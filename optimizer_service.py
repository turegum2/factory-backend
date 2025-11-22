# -*- coding: utf-8 -*-
"""
Production Optimizer (CP-SAT exact)
-----------------------------------
API не менялся:
  POST /optimize         -> JSON (таблица расписания + метрики + предупреждения)
  POST /optimize/excel   -> Excel (Schedule, Summary, Validation)
  POST /optimize/html    -> HTML-диаграмма Ганта + отчёт по загрузке

Ключевые свойства:
- Станочный цикл: машина удерживается непрерывно с LOAD.start до UNLOAD.end.
- Оператор свободен между PROCESS и UNLOAD; обед 13:00–14:00 как жёсткий календарь.
- UNLOAD может задерживаться (и переноситься через обед), если это улучшает цель.
"""
from typing import List, Dict, Tuple, Optional
from dataclasses import dataclass, field
from collections import defaultdict
import re
import os
import math
import io
import time
import mimetypes
import uuid
import boto3
import json
import hmac
import hashlib
import base64
import datetime as dt
from botocore.exceptions import ClientError
import jwt  # PyJWT

from fastapi import FastAPI, Body, Depends, HTTPException, status
from fastapi.security import HTTPBearer, HTTPAuthorizationCredentials
from fastapi.middleware.cors import CORSMiddleware
from fastapi.responses import JSONResponse, HTMLResponse

import pandas as pd

# --- OR-Tools ---
from ortools.sat.python import cp_model

# --------- Всякие S3 штуки -----------------
S3_ENDPOINT = os.getenv("S3_ENDPOINT", "https://storage.yandexcloud.net")
S3_REGION = os.getenv("S3_REGION", "ru-central1")
S3_BUCKET = os.getenv("S3_BUCKET", "optimizer-ui")
S3_PREFIX = os.getenv("S3_PREFIX", "prod/")
PRESIGN_TTL = int(os.getenv("S3_PRESIGN_TTL", "86400"))

# --------- Доступ -----------------
JWT_ALG = "HS256"
JWT_TTL_MIN = int(os.getenv("JWT_TTL_MIN", "480"))
JWT_SECRET = os.getenv("JWT_SECRET")
if not JWT_SECRET:
    raise RuntimeError("JWT_SECRET env var JWT_SECRET is not set")

USERS_S3_KEY = os.getenv("USERS_S3_KEY", f"{S3_PREFIX}auth/users.json")
AUTH_BOOTSTRAP_ADMIN_LOGIN = os.getenv("AUTH_BOOTSTRAP_ADMIN_LOGIN", "admin")
AUTH_BOOTSTRAP_ADMIN_PASSWORD = os.getenv("AUTH_BOOTSTRAP_ADMIN_PASSWORD", "admin")

auth_scheme = HTTPBearer(auto_error=False)

_s3 = boto3.client(
    "s3",
    endpoint_url=S3_ENDPOINT,
    region_name=S3_REGION,
    aws_access_key_id=os.getenv("AWS_ACCESS_KEY_ID"),
    aws_secret_access_key=os.getenv("AWS_SECRET_ACCESS_KEY"),
)

def _s3_put(key: str, data: bytes, ctype: str, cache="no-store"):
    _s3.put_object(Bucket=S3_BUCKET, Key=key, Body=data,
                   ContentType=ctype, CacheControl=cache)

def _s3_presigned(key: str, filename: str | None = None) -> str:
    params = {"Bucket": S3_BUCKET, "Key": key}
    if filename:
        params["ResponseContentDisposition"] = f'attachment; filename="{filename}"'
    return _s3.generate_presigned_url("get_object", Params=params, ExpiresIn=PRESIGN_TTL)

# --------- Хелперы для работы с доступами и паролями ---------
def hash_password(password: str, iterations: int = 100_000) -> str:
    salt = os.urandom(16)
    dk = hashlib.pbkdf2_hmac("sha256", password.encode("utf-8"), salt, iterations)
    return f"{iterations}${base64.b64encode(salt).decode()}${base64.b64encode(dk).decode()}"

def verify_password(password: str, stored: str) -> bool:
    try:
        iterations_str, salt_b64, hash_b64 = stored.split("$", 2)
        iterations = int(iterations_str)
        salt = base64.b64decode(salt_b64)
        expected = base64.b64decode(hash_b64)
    except Exception:
        return False
    dk = hashlib.pbkdf2_hmac("sha256", password.encode("utf-8"), salt, iterations)
    return hmac.compare_digest(dk, expected)

def _ensure_bootstrap_users():
    """Если файла пользователей нет — создать с одним админом."""
    try:
        _s3.head_object(Bucket=S3_BUCKET, Key=USERS_S3_KEY)
        return
    except ClientError as e:
        if e.response["Error"]["Code"] not in ("404", "NoSuchKey"):
            raise

    admin_user = {
        "username": AUTH_BOOTSTRAP_ADMIN_LOGIN,
        "password_hash": hash_password(AUTH_BOOTSTRAP_ADMIN_PASSWORD),
        "role": "admin",
        "is_active": True,
        "must_change_password": True,   # ← новый флаг
        "created_at": dt.datetime.utcnow().isoformat() + "Z",
    }
    data = {"version": 1, "users": [admin_user]}
    _s3_put(USERS_S3_KEY, json.dumps(data).encode("utf-8"), "application/json")


def _load_users() -> dict[str, dict]:
    _ensure_bootstrap_users()
    try:
        obj = _s3.get_object(Bucket=S3_BUCKET, Key=USERS_S3_KEY)
        raw = obj["Body"].read().decode("utf-8")
        payload = json.loads(raw) or {}
        users_list = payload.get("users", [])
        return {u["username"]: u for u in users_list}
    except ClientError as e:
        if e.response["Error"]["Code"] in ("404", "NoSuchKey"):
            return {}
        raise

def _save_users(users: dict[str, dict]):
    data = {
        "version": 1,
        "users": list(users.values()),
    }
    _s3_put(USERS_S3_KEY, json.dumps(data).encode("utf-8"), "application/json")

def create_access_token(username: str, role: str) -> tuple[str, int]:
    now = int(time.time())
    exp = now + JWT_TTL_MIN * 60
    payload = {
        "sub": username,
        "role": role,
        "iat": now,
        "exp": exp,
    }
    token = jwt.encode(payload, JWT_SECRET, algorithm=JWT_ALG)
    return token, exp

def get_current_user(credentials: HTTPAuthorizationCredentials = Depends(auth_scheme)) -> dict:
    if credentials is None:
        raise HTTPException(status_code=status.HTTP_401_UNAUTHORIZED, detail="Не авторизован")
    token = credentials.credentials
    try:
        payload = jwt.decode(token, JWT_SECRET, algorithms=[JWT_ALG])
    except jwt.ExpiredSignatureError:
        raise HTTPException(status_code=status.HTTP_401_UNAUTHORIZED, detail="Сессия истекла")
    except jwt.InvalidTokenError:
        raise HTTPException(status_code=status.HTTP_401_UNAUTHORIZED, detail="Неверный токен")

    username = payload.get("sub")
    role = payload.get("role")
    if not username or not role:
        raise HTTPException(status_code=status.HTTP_401_UNAUTHORIZED, detail="Неверное содержимое токена")

    users = _load_users()
    user = users.get(username)
    if not user or not user.get("is_active", True):
        raise HTTPException(status_code=status.HTTP_401_UNAUTHORIZED, detail="Пользователь деактивирован")
    return {
        "username": username,
        "role": role,
        "must_change_password": bool(user.get("must_change_password", False)),
    }

def require_active_user(user: dict = Depends(get_current_user)) -> dict:
    if user.get("must_change_password"):
        raise HTTPException(status_code=status.HTTP_403_FORBIDDEN,
                            detail="Необходимо сменить пароль")
    return user

def require_admin(user: dict = Depends(require_active_user)) -> dict:
    if user["role"] != "admin":
        raise HTTPException(status_code=status.HTTP_403_FORBIDDEN, detail="Может сделать только admin")
    return user

 # --------- Константы ресурсов и смен ---------
OP = "Оператор"
SAW = "Пила"
EDGE_MACHINE = "Кромка"

DAY = 1440

# Оператор: 09:00–21:00
DAY_BEG = 9 * 60
DAY_END = 21 * 60
CAL_OP = [(DAY_BEG, DAY_END)]

# Станки: 09:00–23:00 (могут заканчивать программу после того, как оператор уйдет со смены)
MACHINE_BEG = 9 * 60
MACHINE_END = 23 * 60
CAL_MACHINE = [(MACHINE_BEG, MACHINE_END)]

# Гибкие перерывы оператора (старт внутри окна, длительность фикс.)
OP_FLEX_BREAKS = [
    (10 * 60, 11 * 60, 15),
    (13 * 60, 14 * 60, 30),
    (15 * 60, 16 * 60, 15),
]

# --------- Модель задачи ---------
@dataclass
class Task:
    uid: str
    order_id: str
    ref_id: str
    label: str
    resources: Tuple[str, ...]
    duration: int
    preds: List[str] = field(default_factory=list)
    start: Optional[int] = None
    end: Optional[int] = None

# --------- Построение runtime-структур из JSON ---------
def build_runtime(obj: dict):
    orders = {str(o["order_id"]): {"id": str(o["order_id"]), "priority": int(o.get("priority", 0))}
              for o in obj.get("orders", [])}

    deliveries: Dict[str, dict] = {}
    for d in obj.get("deliveries", []):
        did = str(d["delivery_id"])
        deliveries[did] = {"id": did, "duration": int(d.get("duration_min", 0)), "stoneIds": []}

    stones: Dict[str, dict] = {}
    for s in obj.get("stones", []):
        sid = str(s["stone_id"])
        oid = str(s["order_id"])
        did = str(s.get("delivery_id") or "")
        stones[sid] = {"id": sid, "orderId": oid, "deliveryId": did, "sawPrograms": []}
        if did and did in deliveries:
            deliveries[did]["stoneIds"].append(sid)

    sawPrograms: Dict[str, dict] = {}
    for sp in obj.get("sawPrograms", []):
        pid = str(sp["prog_id"])
        sid = str(sp["stone_id"])
        sawPrograms[pid] = {
            "id": pid, "stoneId": sid,
            "load": int(sp.get("load_C_min", 0)),
            "process": int(sp.get("process_D_min", 0)),
            "unload": int(sp.get("unload_E_min", 0)),
            "details": []
        }
        if sid in stones:
            stones[sid]["sawPrograms"].append(pid)

    details: Dict[str, dict] = {}
    for d in obj.get("details", []):
        did = str(d["detail_id"])
        details[did] = {
            "id": did,
            "orderId": str(d.get("order_id", "")),
            "stoneId": str(d["stone_id"]),
            "sourceProgId": str(d["source_prog_id"]),
            "edgeNeeded": (d.get("need_edge") in ["Y", "y", True, "True", "true", 1]),
            "edge_load": int(d.get("edge_load_F_min", 0) or 0),
            "edge_process": int(d.get("edge_process_G_min", 0) or 0),
            "edge_unload": int(d.get("edge_unload_H_min", 0) or 0),
            "millingStages": [
                {
                    "id": str(ms["id"]),
                    "machine": str(ms["machine"]),
                    "load": int(ms.get("mill_load_min", 0) or 0),
                    "process": int(ms.get("mill_process_min", 0) or 0),
                    "unload": int(ms.get("mill_unload_min", 0) or 0),
                }
                for ms in d.get("millingStages", [])
            ],
        }
        pid = details[did]["sourceProgId"]
        if pid in sawPrograms:
            sawPrograms[pid]["details"].append(did)

    policy = (obj.get("policy", {}) or {})
    policy["priority_objective"] = "lexicographic"
    return orders, deliveries, stones, sawPrograms, details, policy

# --------- Построение DAG задач ---------
def build_tasks(orders, deliveries, stones, sawPrograms, details):
    tasks_all: Dict[str, Task] = {}
    succs: Dict[str, List[str]] = defaultdict(list)

    def add_task(uid, order_id, ref_id, label, resources, duration):
        t = Task(uid=uid, order_id=order_id, ref_id=ref_id,
                 label=label, resources=tuple(resources), duration=int(duration))
        tasks_all[uid] = t
        return uid

    def link(a: str, b: str):
        tasks_all[b].preds.append(a)
        succs[a].append(b)

    # Доставки (операторные)
    for d in deliveries.values():
        add_task(f"T_DEL_{d['id']}", "MULTI", d["id"], "Доставка", (OP,), d["duration"])

    # Камни → пила → детали → кромка → фрезеры
    for sid, s in stones.items():
        prev_saw_end_uid = None
        for pid in s["sawPrograms"]:
            sp = sawPrograms[pid]
            # Пила: положить/процесс/снять
            t_load = f"T_SAW_LOAD_{pid}"
            t_proc = f"T_SAW_PROC_{pid}"
            t_unld = f"T_SAW_UNLOAD_{pid}"
            add_task(t_load, s["orderId"], sid, "Положить на пилу", (OP, SAW), sp["load"])
            add_task(t_proc, s["orderId"], sid, "Пила распил", (SAW,), sp["process"])
            add_task(t_unld, s["orderId"], sid, "Снять с пилы", (OP, SAW), sp["unload"])
            link(t_load, t_proc)
            link(t_proc, t_unld)

            # Доставка перед распилом
            did = s.get("deliveryId")
            if did:
                del_uid = f"T_DEL_{did}"
                if del_uid in tasks_all:
                    link(del_uid, t_load)

            # Последовательность программ на одном камне
            if prev_saw_end_uid:
                link(prev_saw_end_uid, t_load)
            prev_saw_end_uid = t_unld

            # Детали из этой программы
            for det_id in sawPrograms[pid]["details"]:
                d = details[det_id]
                prev = t_unld

                # Кромка (опционально)
                if d["edgeNeeded"]:
                    e1 = f"T_EDGE_LOAD_{det_id}"
                    e2 = f"T_EDGE_PROC_{det_id}"
                    e3 = f"T_EDGE_UNLOAD_{det_id}"
                    add_task(e1, s["orderId"], det_id, "Положить на кромку", (OP, EDGE_MACHINE), d["edge_load"])
                    add_task(e2, s["orderId"], det_id, "Кромка", (EDGE_MACHINE,), d["edge_process"])
                    add_task(e3, s["orderId"], det_id, "Снять с кромки", (OP, EDGE_MACHINE), d["edge_unload"])
                    link(prev, e1)
                    link(e1, e2)
                    link(e2, e3)
                    prev = e3

                # Фрезеровки (возможно на разных станках)
                for ms in d["millingStages"]:
                    mid = ms["id"]
                    mach = ms["machine"]
                    m1 = f"T_MILL_LOAD_{mid}"
                    m2 = f"T_MILL_PROC_{mid}"
                    m3 = f"T_MILL_UNLOAD_{mid}"
                    add_task(m1, s["orderId"], det_id, f"Положить на {mach}", (OP, mach), ms["load"])
                    add_task(m2, s["orderId"], det_id, f"Фрезеровка ({mach})", (mach,), ms["process"])
                    add_task(m3, s["orderId"], det_id, f"Снять с {mach}", (OP, mach), ms["unload"])
                    link(prev, m1)
                    link(m1, m2)
                    link(m2, m3)
                    prev = m3

    # Ресурсы и календари
    resources = {OP, SAW, EDGE_MACHINE}
    for t in tasks_all.values():
        for r in t.resources:
            resources.add(r)
    res_cal = {r: (CAL_OP if r == OP else CAL_MACHINE) for r in resources}
    return tasks_all, succs, resources, res_cal

# --------- Вспомогалки ---------
def hhmm(abs_min: int) -> str:
    m = abs_min % DAY
    return f"{m//60:02d}:{m%60:02d}"

def available_minutes(cal, start_abs: int, end_abs: int) -> int:
    total = 0
    day0 = start_abs // DAY; day1 = (end_abs + DAY - 1) // DAY
    for dday in range(day0, day1+1):
        for (a,b) in cal:
            s = max(start_abs, dday*DAY + a)
            e = min(end_abs, dday*DAY + b)
            if e > s:
                total += (e - s)
    return total

# ---------- Display helpers ----------
def _is_saw_uid(uid: str) -> bool:
    # UID пилы: T_SAW_LOAD_<prog_id>, T_SAW_PROC_<prog_id>, T_SAW_UNLOAD_<prog_id>
    return uid.startswith(("T_SAW_LOAD_", "T_SAW_PROC_", "T_SAW_UNLOAD_"))

def display_id(t: Task) -> str:
    """
    Что показывать в Excel/Ганте:
      - для задач ПИЛЫ — ID ПРОГРАММЫ (...-P1),
      - иначе — ref_id, как раньше.
    Только визуализация; оптимизацию не трогаем.
    """
    uid = getattr(t, "uid", "")
    if uid and _is_saw_uid(uid):
        parts = uid.split("_", 3)  # ['T','SAW','PROC','<prog_id>']
        if len(parts) == 4 and parts[-1]:
            return parts[-1]
    return getattr(t, "ref_id", "")

# --------- CP-SAT оптимизация ---------
def schedule_cp(orders, deliveries, stones, sawPrograms, details, policy):
    tasks_all, succs, resources, calendars = build_tasks(orders, deliveries, stones, sawPrograms, details)

    # --------- 1) Оценим минимально нужное число дней по загрузке ---------
    # Эффективная дневная мощность: время смены минус обязательные перерывы
    op_day_len       = sum(b - a for (a, b) in CAL_OP)
    breaks_per_day   = sum(d for (_wbeg, _wend, d) in OP_FLEX_BREAKS)
    op_per_day_eff   = max(1, op_day_len - breaks_per_day)  # напр. 600 - 60 = 540 при 19:00
    mach_per_day     = sum(b - a for (a, b) in CAL_MACHINE)

    # минуты оператора = все задачи, где участвует OP (доставки, LOAD/UNLOAD и т.п.)
    op_minutes = sum(t.duration for t in tasks_all.values() if OP in t.resources)

    # минуты по машинам считаем как (LOAD+PROC+UNLOAD) для каждого станочного цикла
    # Для этого временно восстановим тройки (load, proc, unload) и машину M:
    tmp_succs = succs  # читаем уже собранный граф
    machine_demand: Dict[str, int] = defaultdict(int)
    load_of: Dict[str, str] = {}
    unld_of: Dict[str, str] = {}
    proc_of_load: Dict[str, str] = {}
    unld_of_load: Dict[str, str] = {}
    machine_of_load: Dict[str, str] = {}
    for lid, lt in tasks_all.items():
        if OP not in lt.resources or len(lt.resources) != 2:
            continue
        M = [r for r in lt.resources if r != OP][0]
        procs = [pid for pid in tmp_succs.get(lid, []) if tuple(tasks_all[pid].resources) == (M,)]
        if len(procs) != 1:
            continue
        pid = procs[0]
        unlds = [uid for uid in tmp_succs.get(pid, []) if set(tasks_all[uid].resources) == {OP, M} and len(tasks_all[uid].resources) == 2]
        if len(unlds) != 1:
            continue
        uid = unlds[0]
        proc_of_load[lid] = pid
        unld_of_load[lid] = uid
        load_of[pid] = lid
        unld_of[pid] = uid
        machine_of_load[lid] = M
        machine_demand[M] += (tasks_all[lid].duration + tasks_all[pid].duration + tasks_all[uid].duration)

    # Только LOAD'ы пилы → группируем по камню (ref_id у LOAD пилы = stone_id)
    saw_loads_by_stone = defaultdict(list)
    for lid, M in machine_of_load.items():
        if M == SAW:
            sid = tasks_all[lid].ref_id  # это именно stone_id для пилы
            saw_loads_by_stone[sid].append(lid)

    stones_with_megablock = {sid for sid, lids in saw_loads_by_stone.items() if len(lids) >= 2}

    # Минимум дней для оператора с учётом того, что каждый день "съедается" перерывами
    days_by_op   = max(1, math.ceil(op_minutes / op_per_day_eff))
    days_by_mach = max([1] + [math.ceil(d / max(1, mach_per_day)) for d in machine_demand.values()])
    DAYS = max(days_by_op, days_by_mach) + 1

    # --------- 2) Модель CP-SAT с многодневным горизонтом ---------
    model = cp_model.CpModel()
    H_BEG, H_END = 0, DAYS * DAY

    # Переменные времени для всех «примитивных» операций
    starts: Dict[str, cp_model.IntVar] = {}
    ends: Dict[str, cp_model.IntVar] = {}
    ivals: Dict[str, cp_model.IntervalVar] = {}

    # Для операторских (включая LOAD/UNLOAD) запрещаем пересечение обеда:
    def constrain_to_operator_day_multi(model, s: cp_model.IntVar, e: cp_model.IntVar, dur: int, DAYS: int):
        """Операция оператора целиком внутри 09:00–21:00 какого-то дня."""
        lits = []
        for d in range(DAYS):
            b = model.NewBoolVar(f"op_{s.Name()}_{d}")
            model.Add(s >= d * DAY + DAY_BEG).OnlyEnforceIf(b)
            model.Add(e <= d * DAY + DAY_END).OnlyEnforceIf(b)
            lits.append(b)
        model.Add(sum(lits) == 1)
        model.Add(e == s + dur)

    def constrain_to_operator_day_multi_conditional(model, s, e, dur, DAYS, lit):
        """Как constrain_to_operator_day_multi, но действует только при lit=1."""
        day_bits = []
        for d in range(DAYS):
            b = model.NewBoolVar(f"op_{s.Name()}_{d}")
            model.Add(s >= d * DAY + DAY_BEG).OnlyEnforceIf(b)
            model.Add(e <= d * DAY + DAY_END).OnlyEnforceIf(b)
            day_bits.append(b)
        # если lit=0, ни один день не выбран; если lit=1 — выбран ровно один
        model.Add(sum(day_bits) == lit)
        # длительность фиксируем только когда интервал "включён"
        model.Add(e == s + dur).OnlyEnforceIf(lit)

    # Накопим интервалы по ресурсам
    op_intervals: List[cp_model.IntervalVar] = []
    machine_blocks: Dict[str, List[cp_model.IntervalVar]] = defaultdict(list)

    # --- Станочные циклы и операторские задачи ---
    # Для распознавания циклов по структуре:
    # LOAD(OP,M) -> PROC(M) -> UNLOAD(OP,M)
    # Также учтём доставки (OP).
    # Сгруппируем по машинам тройки.
    # Сначала создадим все элементарные переменные.

    # Создание basic переменных для всех задач
    for uid, t in tasks_all.items():
        s = model.NewIntVar(H_BEG, H_END, f"s_{uid}")
        e = model.NewIntVar(H_BEG, H_END, f"e_{uid}")
        starts[uid] = s
        ends[uid] = e
        # интервалы ниже, когда определим тип
        # предшествования (пока без временных лагов)
        for p in t.preds:
            model.Add(s >= ends[p])

    # Найдём бандлы
    # (делаем это через граф задач, как в детекторе)
    # Определим пары (load, proc, unld) и машину M
    for lid, lt in tasks_all.items():
        if OP not in lt.resources or len(lt.resources) != 2:
            continue
        M = [r for r in lt.resources if r != OP][0]
        # поиски proc
        procs = [pid for pid in succs.get(lid, []) if tuple(tasks_all[pid].resources) == (M,)]
        if len(procs) != 1:
            continue
        pid = procs[0]
        unlds = [uid for uid in succs.get(pid, []) if set(tasks_all[uid].resources) == {OP, M} and len(tasks_all[uid].resources) == 2]
        if len(unlds) != 1:
            continue
        uid = unlds[0]
        proc_of_load[lid] = pid
        unld_of_load[lid] = uid
        load_of[pid] = lid
        unld_of[pid] = uid
        machine_of_load[lid] = M

    # Операторские доставки и прочее (OP)
    for uid, t in tasks_all.items():
        if t.resources == (OP,):
            s, e = starts[uid], ends[uid]
            constrain_to_operator_day_multi(model, s, e, t.duration, DAYS)
            iv = model.NewIntervalVar(s, t.duration, e, f"iv_{uid}")
            ivals[uid] = iv
            op_intervals.append(iv)

    # Для каждой станочной тройки создаём:
    #   sL, eL; sP, eP; sU, eU; и единый блок машины block_iv = [sL, eU)
    for lid, M in machine_of_load.items():
        pid = proc_of_load[lid]
        uid = unld_of_load[lid]
        tL, tP, tU = tasks_all[lid], tasks_all[pid], tasks_all[uid]

        sL, eL = starts[lid], ends[lid]
        sP, eP = starts[pid], ends[pid]
        sU, eU = starts[uid], ends[uid]

        if M == SAW:
            # --- ПИЛА: без изменений — "положить" всегда учитываем как задано ---
            # LOAD: операторское окно (фиксированная длительность)
            constrain_to_operator_day_multi(model, sL, eL, tL.duration, DAYS)
            # PROC: только машина, "привязываем" к концу LOAD
            model.Add(sP == eL)
            model.Add(eP == sP + tP.duration)
            # UNLOAD: операторское окно, не раньше конца PROC
            constrain_to_operator_day_multi(model, sU, eU, tU.duration, DAYS)
            model.Add(sU >= eP)

            # Интервалы оператора
            ivL = model.NewIntervalVar(sL, tL.duration, eL, f"iv_{lid}")
            ivU = model.NewIntervalVar(sU, tU.duration, eU, f"iv_{uid}")

        else:
            # --- КРОМКА/ФРЕЗЕРЫ: "положить" опционально (0 мин при мгновенной передаче) ---

            # Конец предшествующей операции (обычно UNLOAD предыдущего станка/пилы)
            preds = tasks_all[lid].preds
            if len(preds) == 1:
                pEnd = ends[preds[0]]
            else:
                pEnd = model.NewIntVar(H_BEG, H_END, f"pEnd_{lid}")
                model.AddMaxEquality(pEnd, [ends[p] for p in preds])

            # Булева: учитывать ли "положить" (1 — была задержка, 0 — мгновенная передача)
            use_load = model.NewBoolVar(f"use_load_{lid}")

            # Окно оператора и фиксирование длительности включаем ТОЛЬКО когда use_load=1
            constrain_to_operator_day_multi_conditional(model, sL, eL, tL.duration, DAYS, use_load)

            # Мгновенная передача: старт ровно в pEnd, длительность 0
            model.Add(sL == pEnd).OnlyEnforceIf(use_load.Not())
            model.Add(eL == sL).OnlyEnforceIf(use_load.Not())

            # Было ожидание (станок был занят): старт позже pEnd, длительность — входная
            model.Add(sL >= pEnd + 1).OnlyEnforceIf(use_load)
            model.Add(eL == sL + tL.duration).OnlyEnforceIf(use_load)

            # PROC: "привязываем" к концу LOAD (работает и при eL == sL)
            model.Add(sP == eL)
            model.Add(eP == sP + tP.duration)

            # UNLOAD: операторское окно, не раньше конца PROC
            constrain_to_operator_day_multi(model, sU, eU, tU.duration, DAYS)
            model.Add(sU >= eP)

            # Интервалы оператора: LOAD только если реально тратили время; UNLOAD — всегда
            ivL = model.NewOptionalIntervalVar(sL, tL.duration, eL, use_load, f"iv_{lid}")
            ivU = model.NewIntervalVar(sU, tU.duration, eU, f"iv_{uid}")

        # Сохраняем интервалы оператора
        ivals[lid] = ivL
        ivals[uid] = ivU
        op_intervals += [ivL, ivU]

        # Машинный блок: непрерывная занятость машины [sL, eU)
        # Нижнюю границу ослабляем до 0 — чтобы допустить "положить = 0"
        block_dur = model.NewIntVar(0, H_END - H_BEG, f"dur_block_{lid}")
        model.Add(block_dur == (eU - sL))
        block = model.NewIntervalVar(sL, block_dur, eU, f"blk_{lid}")

        stone_id = tasks_all[lid].ref_id  # важно брать именно здесь
        if not (M == SAW and stone_id in stones_with_megablock):
            machine_blocks[M].append(block)

    # Мегаблок по камню на ПИЛЕ: непрерывно с первого LOAD до последнего UNLOAD
    for sid, lids in saw_loads_by_stone.items():
        if sid not in stones_with_megablock:
            continue
        s_first = model.NewIntVar(H_BEG, H_END, f"s_sawstone_{sid}")
        e_last  = model.NewIntVar(H_BEG, H_END, f"e_sawstone_{sid}")
        model.AddMinEquality(s_first, [starts[l] for l in lids])
        model.AddMaxEquality(e_last,  [ends[unld_of_load[l]] for l in lids])
        dur = model.NewIntVar(0, H_END - H_BEG, f"d_sawstone_{sid}")
        model.Add(dur == e_last - s_first)
        iv = model.NewIntervalVar(s_first, dur, e_last, f"blk_sawstone_{sid}")
        machine_blocks[SAW].append(iv)  # ← строго в список пилы

        # Небольшая связка, чтобы исключить "дыры" между программами камня на пиле
        lids_sorted = lids[:]  # при необходимости отсортируйте в желаемом порядке
        for a, b in zip(lids_sorted, lids_sorted[1:]):
            model.Add(starts[b] >= ends[unld_of_load[a]])

    # --- гибкие перерывы оператора: интервалы фикс. длительности с перем. стартом в окне ---
    op_break_intervals = []
    op_break_vars = []  # чтобы потом снять решение и нарисовать в Гантте

    for d in range(DAYS):
        for (wbeg, wend, dur) in OP_FLEX_BREAKS:
            s = model.NewIntVar(d * DAY + wbeg, d * DAY + wend - dur, f"brk_s_{d}_{wbeg}")
            e = model.NewIntVar(d * DAY + wbeg + dur, d * DAY + wend, f"brk_e_{d}_{wbeg}")
            model.Add(e == s + dur)
            # Перерыв должен лежать внутри дневного окна оператора (на всякий случай)
            model.Add(s >= d * DAY + DAY_BEG)
            model.Add(e <= d * DAY + DAY_END)

            brk_iv = model.NewIntervalVar(s, dur, e, f"brk_{d}_{wbeg}")
            op_break_intervals.append(brk_iv)
            op_intervals.append(brk_iv)    # <<< ключевое: перерыв тоже «занимает» оператора
            op_break_vars.append((s, e, dur))

    # Ограничения по ресурсам
    # Оператор — одно за раз
    model.AddNoOverlap(op_intervals)
    # Каждая машина — один блок за раз
    for M, blks in machine_blocks.items():
        model.AddNoOverlap(blks)

    # ----- Целевая функция -----
    # Makespan — максимум всех окончаний
    last_end = model.NewIntVar(H_BEG, H_END, "makespan")
    model.AddMaxEquality(last_end, [ends[uid] for uid in tasks_all.keys()])

    # Тай-брейк (сумма окончаний всех задач) — классический secondary
    N = len(tasks_all)
    BIG = (H_END * N) + 1
    secondary = sum(ends[u] for u in tasks_all.keys())

    # --- завершения заказов (по заказам) ---
    order_finish = {}   # oid -> IntVar окончания заказа
    order_ids = sorted({t.order_id for t in tasks_all.values() if t.order_id != "MULTI"})
    for oid in order_ids:
        tids = [uid for uid, t in tasks_all.items() if t.order_id == oid]
        if not tids:
            continue
        cvar = model.NewIntVar(H_BEG, H_END, f"c_{oid}")
        model.AddMaxEquality(cvar, [ends[tid] for tid in tids])
        order_finish[oid] = cvar

    # --- гибридная цель: если есть приоритетные, делаем "взвешенную" лексикографику ---
    pri_terms = []
    urgent_present = False
    for oid, cvar in order_finish.items():
        pr = 1 if int(orders.get(oid, {}).get("priority", 0)) > 0 else 0
        if pr == 1:
            urgent_present = True
        w = 10000 if pr == 1 else 1   # приоритетные очень тяжёлые, остальные с весом 1
        pri_terms.append(w * cvar)

    pri_expr = sum(pri_terms) if pri_terms else 0

    if urgent_present:
        # Лексикографика: первично pri_expr, вторично makespan
        PRI_DOM = (H_END + 1)         # гарантирует приоритет pri_expr над last_end
        model.Minimize(PRI_DOM * pri_expr + last_end)
    else:
        # Чистый makespan (как раньше): первично makespan, вторично "secondary"
        model.Minimize(BIG * last_end + secondary)

    # РЕШЕНИЕ
    # ---------- Фаза 1: детерминированный прогон ----------
    phase2_enable         = bool(policy.get("phase2_enable", True))
    phase1_time_limit_sec = float(policy.get("time_limit_sec", 20))
    phase1_seed           = int(policy.get("random_seed", 123))
    phase2_time_limit_sec = float(policy.get("phase2_time_limit_sec", 20))
    phase2_workers        = int(policy.get("phase2_workers", 8))
    phase2_seed           = int(policy.get("phase2_random_seed", 0))

    solver1 = cp_model.CpSolver()
    solver1.parameters.max_time_in_seconds = phase1_time_limit_sec
    solver1.parameters.num_search_workers  = 1
    solver1.parameters.random_seed         = phase1_seed

    status1 = solver1.Solve(model)
    if status1 not in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        raise RuntimeError("CP-SAT: решение не найдено на фазе 1")

    obj1       = solver1.ObjectiveValue()
    best_bound = solver1.BestObjectiveBound()
    ms1        = solver1.Value(last_end)

    # Подготовим hint для следующей фазы (значения "с первого решения")
    for uid in starts.keys():
        model.AddHint(starts[uid], solver1.Value(starts[uid]))
        model.AddHint(ends[uid],   solver1.Value(ends[uid]))
    for (s, e, _dur) in op_break_vars:
        model.AddHint(s, solver1.Value(s))
        model.AddHint(e, solver1.Value(e))

    # ---------- Фаза 2: портфельный прогон (если включено) ----------
    use2 = False
    solver2 = None
    status2 = None
    if phase2_enable and phase2_time_limit_sec > 0:
        solver2 = cp_model.CpSolver()
        solver2.parameters.max_time_in_seconds = phase2_time_limit_sec
        solver2.parameters.num_search_workers  = phase2_workers
        # seed можно оставить 0 (портфель сам рандомизирует),
        # либо задать явно из policy:
        solver2.parameters.random_seed         = phase2_seed

        # Во 2-й фазе оптимизируем ту же цель (портфель/многопоток + подсказки)
        status2 = solver2.Solve(model)
        if status2 in (cp_model.OPTIMAL, cp_model.FEASIBLE):
            obj2 = solver2.ObjectiveValue()
            # если цель меньше — берём фазу 2 (даже если makespan тот же, улучшение secondary полезно)
            if obj2 + 1e-6 < obj1:
                use2 = True

    # ---------- Выбираем лучшее решение и формируем метрики ----------
    sol     = solver2 if use2 else solver1
    status  = status2 if use2 else status1
    makespan = sol.Value(last_end)

    metrics = {
        "makespan_min":             int(makespan),
        "solver_status":            sol.StatusName(status),
        "best_bound_min":           int(sol.BestObjectiveBound()),
        "gap_min":                  int(sol.ObjectiveValue() - sol.BestObjectiveBound()),
        "workers":                  (phase2_workers if use2 else 1),
        "time_limit_sec":           (phase2_time_limit_sec if use2 else phase1_time_limit_sec),
        "priority_objective":       "lexicographic",
        # диагностика по фазам
        "phase_used":               (2 if use2 else 1),
        "phase1": {
            "status":   solver1.StatusName(status1),
            "workers":  1,
            "t_sec":    phase1_time_limit_sec,
            "obj":      obj1,
            "bound":    best_bound,
            "gap":      obj1 - best_bound,
            "makespan": ms1,
        },
    }
    if solver2 is not None:
        m2 = solver2.Value(last_end) if status2 in (cp_model.OPTIMAL, cp_model.FEASIBLE) else None
        metrics["phase2"] = {
            "status":   solver2.StatusName(status2) if status2 is not None else "NOT_RUN",
            "workers":  phase2_workers,
            "t_sec":    phase2_time_limit_sec,
            "obj":      (solver2.ObjectiveValue() if status2 in (cp_model.OPTIMAL, cp_model.FEASIBLE) else None),
            "bound":    (solver2.BestObjectiveBound() if status2 in (cp_model.OPTIMAL, cp_model.FEASIBLE) else None),
            "gap":      ((solver2.ObjectiveValue() - solver2.BestObjectiveBound()) if status2 in (cp_model.OPTIMAL, cp_model.FEASIBLE) else None),
            "makespan": m2,
            "improved": True if use2 else False,
        }

    # выберем перерывы из финального решения
    chosen_breaks = [(sol.Value(s), sol.Value(e), dur) for (s, e, dur) in op_break_vars]

    # перенесём времена в tasks_all из финального решения
    for uid in tasks_all.keys():
        s = sol.Value(starts[uid])
        e = sol.Value(ends[uid])
        tasks_all[uid].start = s
        tasks_all[uid].end = e

    # ФИЛЬТР: видимые перерывы — только те, что начинаются до makespan
    visible_breaks = [(s_beg, s_end, dur) for (s_beg, s_end, dur) in chosen_breaks if s_beg < makespan]

    # Валидация/предупреждения: чужой LOAD между PROC и UNLOAD на той же машине
    warnings = []
    # соберём бандлы по машинам
    bundles = []
    for lid, M in machine_of_load.items():
        pid = proc_of_load[lid]; uid = unld_of_load[lid]
        bundles.append((M, lid, pid, uid))
    byM = defaultdict(list)
    for M, lid, pid, uid in bundles:
        byM[M].append((lid, pid, uid))
    for M, lst in byM.items():
        lst.sort(key=lambda tup: tasks_all[tup[0]].start)
        for (l, p, u) in lst:
            lt, pt, ut = tasks_all[l], tasks_all[p], tasks_all[u]
            for (l2, p2, u2) in lst:
                if l2 == l: continue
                if pt.end <= tasks_all[l2].start < ut.start:
                    warnings.append({
                        "machine": M,
                        "prev_load": l, "prev_proc": p, "prev_unload": u,
                        "intruder_load": l2,
                        "note": f"На машине {M} между Процессом и Снять цикла {lt.ref_id} вставлен Положить для {tasks_all[l2].ref_id}"
                    })

    # -------- Представленческий порядок: PROC сразу после LOAD --------
    def is_load_uid(uid: str) -> bool:
        return "_LOAD_" in uid

    def paired_proc_uid(uid: str) -> Optional[str]:
        # Универсально для пилы/кромки/фрезеров: меняем _LOAD_ -> _PROC_
        if "_LOAD_" in uid:
            cand = uid.replace("_LOAD_", "_PROC_")
            return cand if cand in tasks_all else None
        return None

    # Базовая сортировка по времени:
    sorted_uids = sorted(tasks_all.keys(), key=lambda u: (tasks_all[u].start, tasks_all[u].end, u))

    # Собираем порядок показа: LOAD, затем сразу его PROC, потом всё остальное
    view_order = []
    emitted = set()
    for uid in sorted_uids:
        if uid in emitted:
            continue
        view_order.append(uid)
        emitted.add(uid)
        if is_load_uid(uid):
            puid = paired_proc_uid(uid)
            if puid and puid not in emitted:
                view_order.append(puid)
                emitted.add(puid)
    # добираем оставшиеся (UNLOAD, доставки, чужие операции) в хрон.порядке
    for uid in sorted_uids:
        if uid not in emitted:
            view_order.append(uid); emitted.add(uid)

    # --- строки по ОПЕРАЦИЯМ ---
    rows_ops = []
    seq = 0
    for uid in view_order:
        t = tasks_all[uid]
        actor = "Оператор" if (len(t.resources) == 1 and t.resources[0] == OP) else (t.resources[0] if t.resources else "")
        order_for_row = t.order_id
        if t.order_id == "MULTI":
            d = deliveries.get(t.ref_id, {}); stoneIds = d.get("stoneIds", [])
            order_for_row = stones[stoneIds[0]]["orderId"] if stoneIds else ""
        day_no = (t.start // DAY) - (min(x.start for x in tasks_all.values()) // DAY) + 1
        rows_ops.append({
            "__seq": seq,                          # сохраняем внутренний порядок операций
            "День": int(day_no),
            "Время начала": hhmm(t.start),
            "Время окончания": hhmm(t.end),
            "Длительность (мин)": int(max(0, t.end - t.start)),
            "Номер заказа": order_for_row,
            "ID": display_id(t),
            "Элемент": "доставка" if t.label == "Доставка"
                    else ("камень" if t.label.startswith(("Положить на пилу","Пила","Снять с пилы")) else "деталь"),
            "Операция": t.label,
            "Исполнитель": actor,
            "_abs_start": int(t.start),
            "_abs_end": int(t.end),
            "_is_break": 0
        })
        seq += 1

    # --- строки по ПЕРЕРЫВАМ (уже отфильтрованным по makespan) ---
    rows_br = []
    for (s_beg, s_end, dur) in visible_breaks:
        day_no = (s_beg // DAY) - (min(x.start for x in tasks_all.values()) // DAY) + 1
        rows_br.append({
            "__seq": 10**9,                        # чтобы не мешать относительному порядку операций
            "День": int(day_no),
            "Время начала": hhmm(s_beg),
            "Время окончания": hhmm(s_end),
            "Длительность (мин)": int(dur),
            "Номер заказа": "",
            "ID": "",
            "Элемент": "",
            "Операция": "Перерыв",
            "Исполнитель": "Оператор",
            "_abs_start": int(s_beg),
            "_abs_end": int(s_end),
            "_is_break": 1
        })

    # --- слияние и сортировка по времени (хронология), при равном времени — сначала операции, потом перерывы ---
    rows_all = sorted(rows_ops + rows_br, key=lambda r: (r["_abs_start"], r["_is_break"], r["__seq"]))

    # DataFrame без служебных полей
    df = pd.DataFrame(rows_all)[
        ["День","Время начала","Время окончания","Длительность (мин)",
        "Номер заказа","ID","Элемент","Операция","Исполнитель"]
    ]

    # Итоговый порядок колонок: "День" — первой, тех.колонки — убрать
    cols = ["День", "Время начала", "Время окончания", "Длительность (мин)",
            "Номер заказа", "ID", "Элемент", "Операция", "Исполнитель"]
    df = df[cols]

    return df, metrics, tasks_all, resources, calendars, warnings, visible_breaks

# --------- HTML-Гантт ---------
def build_gantt_html(tasks_all: Dict[str, Task], resources, calendars, warnings=None, breaks=None, excel_url: Optional[str]=None, base_url: Optional[str]=None) -> str:
    breaks = breaks or []
    # Базовые границы реального расписания
    start_min = min(t.start for t in tasks_all.values())
    end_min = max(t.end for t in tasks_all.values())

    # Визуализируем только рабочую часть дня
    VISIBLE_BEG = min(DAY_BEG, MACHINE_BEG)
    VISIBLE_END = max(DAY_END, MACHINE_END)
    visible_per_day = VISIBLE_END - VISIBLE_BEG
    start_day = start_min // DAY
    end_day = (end_min - 1) // DAY

    # Конвертер "реальное время -> видимые минуты" (сжимает ночи)
    def vis_offset(t: int) -> int:
        d = t // DAY
        acc_days = max(0, d - start_day)
        base = acc_days * visible_per_day
        d_beg = d * DAY + VISIBLE_BEG
        d_end = d * DAY + VISIBLE_END
        if t <= d_beg:
            return base
        return base + max(0, min(t, d_end) - d_beg)

    base_vis = vis_offset(start_min)
    end_vis = vis_offset(end_min)

    # Масштаб и ширины
    px_per_min = 3
    total_vis_min = max(1, end_vis - base_vis)
    width = max(1200, total_vis_min * px_per_min + 200)

    # Динамическая ширина колонки "Операция": 8 px * длина + 20
    longest = max(len(f"{display_id(t)} {t.label}") for t in tasks_all.values()) if tasks_all else 20
    label_w = max(320, min(900, longest * 8 + 20))

    # Меняем порядок отображения
    def is_load_uid(uid: str) -> bool:
        return "_LOAD_" in uid

    def paired_proc_uid(uid: str) -> Optional[str]:
        if "_LOAD_" in uid:
            cand = uid.replace("_LOAD_", "_PROC_")
            return cand if cand in tasks_all else None
        return None

    sorted_uids = sorted(tasks_all.keys(), key=lambda u: (tasks_all[u].start, tasks_all[u].end, u))
    view_order = []
    emitted = set()
    for uid in sorted_uids:
        if uid in emitted:
            continue
        view_order.append(uid)
        emitted.add(uid)
        if is_load_uid(uid):
            puid = paired_proc_uid(uid)
            if puid and puid not in emitted:
                view_order.append(puid)
                emitted.add(puid)
    for uid in sorted_uids:
        if uid not in emitted:
            view_order.append(uid); emitted.add(uid)

    # Ряды подписей и сами бары
    label_rows, track_rows = [], []
    for uid in view_order:
        t = tasks_all[uid]
        left = int((vis_offset(t.start) - base_vis) * px_per_min)
        actual = max(0, t.end - t.start)
        w = max(2, int(actual * px_per_min))
        color = "#3d85c6" if t.resources[0] == OP else "#6aa84f"
        label_text = f"{display_id(t)} {t.label}"
        label_rows.append(f'<div class="label-row" title="{label_text}">{label_text}</div>')
        track_rows.append(
            f'<div class="track-row"><div class="bar" style="left:{left}px;width:{w}px;background:{color}" '
            f'title="{label_text} ({actual} мин, {t.resources[0]})"></div></div>'
        )

    # Часовые метки (09–18), грид-линии, обед и ярлыки дней
    line_divs = []     # вертикальные линии в шапке (ось)
    grid_lines = []    # такие же вертикальные линии в полотне графика
    hour_labels = []   # подписи «10:00», «11:00» ...
    day_tags = []      # «День N, 09:00»
    breaks_axis = []
    breaks_tracks = []

    for (s_beg, s_end, _dur) in breaks:
        lx = int((vis_offset(s_beg) - base_vis) * px_per_min)
        lw = max(1, int((vis_offset(s_end) - base_vis) * px_per_min) - lx)
        breaks_axis.append(f'<div class="breakband" style="left:{lx}px;width:{lw}px"></div>')
        breaks_tracks.append(f'<div class="breakband" style="left:{lx}px;width:{lw}px"></div>')

    day_idx = 1
    start_h = VISIBLE_BEG // 60
    end_h   = VISIBLE_END // 60

    for d in range(start_day, end_day + 1):
        for h in range(start_h, end_h + 1):
            tm = d * DAY + h * 60
            x = int((vis_offset(tm) - base_vis) * px_per_min)

            # вертикальная линия (шапка + тело)
            line_divs.append(f'<div class="gridline" style="left:{x}px"></div>')
            grid_lines.append(f'<div class="gridline" style="left:{x}px"></div>')

            if h == start_h:
                # Ярлык дня «День N, 09:00»
                day_tags.append(f'<div class="daytag" style="left:{x}px">День {day_idx}, 09:00</div>')
            elif h < end_h:
                # Подписи часов ставим в НАЧАЛЕ часа, чуть правее линии (не на разрыве)
                hour_labels.append(f'<div class="tick-label" style="left:{x+6}px">{h:02d}:00</div>')
        day_idx += 1

    # Загрузка ресурсов (как раньше)
    busy = {r: 0 for r in resources}
    for t in tasks_all.values():
        actual = max(0, t.end - t.start)
        for r in t.resources:
            busy[r] += actual
    util_rows = []
    for r in sorted(resources):
        avail = available_minutes(calendars[r], start_min, end_min)
        util = (busy[r] / avail * 100.0) if avail > 0 else 0.0
        util_rows.append((r, int(busy[r]), int(avail), round(util, 1)))
    util_html = ''.join(f"<tr><td>{r}</td><td>{b}</td><td>{a}</td><td>{u}</td></tr>"
                        for r, b, a, u in util_rows)

    warn_html = ""
    if warnings:
        items = "".join([f"<li>{w['note']}</li>" for w in warnings])
        warn_html = f'<div class="warn"><b>Предупреждения валидации:</b><ul>{items}</ul></div>'

    footer_html = (f'''
      <div style="margin-top:16px">
        <a id="dl-excel" href="{excel_url}" download="schedule.xlsx" rel="noopener">Скачать Excel</a>
        <div class="small">Будьте внимательны - здесь ссылка на последний расчёт (файл перезаписывается).</div>
      </div>
    ''' if excel_url else '')

    # HTML
    html = f"""
<!doctype html>
<html lang="ru"><head><meta charset="utf-8"/>
{f'<base href="{base_url}/">' if base_url else ''}
<title>Производственный план</title>
<style>
:root {{ --label-w: {label_w}px; }}
body {{ font-family: Arial, sans-serif; margin:20px; }}
.small {{ color:#666; font-size:12px; margin-bottom:10px; }}
.legend span {{ display:inline-block; width:12px; height:12px; margin-right:6px; border-radius:3px; vertical-align: middle; }}

.gantt {{ border:1px solid #ddd; box-shadow: 0 1px 2px rgba(0,0,0,.05); }}

.head {{ display:grid; grid-template-columns: var(--label-w) 1fr; background:#fafafa; border-bottom:1px solid #eee; }}
.label-head {{ padding:6px 8px; font-weight:600; border-right:1px solid #eee; }}
.axis-scroll {{ overflow-x:auto; }}
.axis {{ position:relative; height:28px; min-width:{width}px; }}

/* Слои в шапке */
.axis-lines, .axis-labels, .axis-days {{ position:absolute; top:0; left:0; right:0; bottom:0; pointer-events:none; }}

/* Вертикальные линии (сквозные — используется и в шапке, и в треках) */
.gridline {{ position:absolute; top:0; bottom:0; border-left:1px solid #eee; z-index:1; }}

/* Подписи часов — поверх линий, по центру линии; не переносятся */
.tick-label {{
  position:absolute;
  top:4px;
  transform:none;
  font-size:11px;
  color:#555;
  white-space:nowrap;
  z-index:3;
}}

/* Ярлык дня у 09:00 — чуть тяжелее по шрифту, с фоном */
.daytag {{
  position:absolute; top:4px; transform:translateX(0);
  font-size:11px; color:#555; white-space:nowrap;
  background:#fafafa; padding:0 2px; z-index:4;
}}

/* Плашка обеда в шапке */
.axis .breakband {{ position:absolute; top:0; bottom:0; background:rgba(220,38,38,0.10); z-index:0; }}

.body {{ display:grid; grid-template-columns: var(--label-w) 1fr; }}
.labels {{ background:#fcfcfc; border-right:1px solid #eee; }}
.label-row {{ height:28px; line-height:28px; padding:0 8px; border-bottom:1px solid #f1f1f1; white-space:nowrap; overflow:hidden; text-overflow:ellipsis; }}

.body-scroll {{ overflow-x:auto; }}
.tracks {{ position:relative; min-width:{width}px; }}
.track-row {{ position:relative; height:28px; border-bottom:1px solid #f1f1f1; }}
.bar {{ position:absolute; top:6px; height:16px; border-radius:4px; box-shadow: inset 0 -1px 0 rgba(0,0,0,.15); z-index:2; }}
.tracks .breakband {{ position:absolute; top:0; bottom:0; background:rgba(220,38,38,0.10); z-index:0; }}

table {{ border-collapse: collapse; margin-top:20px; }}
th, td {{ border:1px solid #ddd; padding:6px 8px; font-size:13px; text-align:left; }}
th {{ background:#fafafa; }}

.warn {{ background:#fff7ed; border:1px solid #fed7aa; padding:8px 10px; margin:10px 0; }}
.warn b {{ color:#c2410c; }}
.warn ul {{ margin:6px 0 0 18px; }}
</style>
</head>
<body>
  <h1>Производственный план</h1>
  <div class="small">Допустимые интервалы: оператор 09:00–21:00, перерывы гибкие, в заданных окнах; станки 09:00–23:00.</div>
  <div class="legend">
    <span style="background:#3d85c6"></span> Действия оператора &nbsp;&nbsp;
    <span style="background:#6aa84f"></span> Работа станка &nbsp;&nbsp;
    <span style="background:rgba(220,38,38,0.10);border:1px solid rgba(220,38,38,0.35)"></span> Перерыв
  </div>
  {warn_html}

  <div class="gantt">
    <div class="head">
      <div class="label-head">Операция</div>
      <div class="axis-scroll"><div class="axis">
        {''.join(breaks_axis)}
        <div class="axis-lines">{''.join(line_divs)}</div>
        <div class="axis-labels">{''.join(hour_labels)}</div>
        <div class="axis-days">{''.join(day_tags)}</div>
      </div></div>
    </div>
    <div class="body">
      <div class="labels">{''.join(label_rows)}</div>
      <div class="body-scroll">
        <div class="tracks">
          {''.join(breaks_tracks)}
          {''.join(grid_lines)}
          {''.join(track_rows)}
        </div>
      </div>
    </div>
  </div>

  <h2>Загрузка ресурсов</h2>
  <table>
    <thead><tr><th>Ресурс</th><th>Занято (мин)</th><th>Доступно (мин)</th><th>Загрузка (%)</th></tr></thead>
    <tbody>{util_html}</tbody>
  </table>

  {footer_html}
  <script>
    // синхронная прокрутка оси и полотна
    const head = document.querySelector('.axis-scroll');
    const body = document.querySelector('.body-scroll');
    let lock = false;
    function sync(from, to){{ if (lock) return; lock = true; to.scrollLeft = from.scrollLeft; lock = false; }}
    head.addEventListener('scroll', ()=>sync(head, body));
    body.addEventListener('scroll', ()=>sync(body, head));
  </script>
  <script>
    (function () {{
        try {{
          var u = new URL(window.location.href);
          var want = u.searchParams.get('dl') === '1' || (window.location.hash || '').indexOf('dl=1') >= 0;
          if (want) {{
            var link = document.getElementById('dl-excel');
            if (link) setTimeout(function(){{ link.click(); }}, 0);
          }}
        }} catch(e) {{}}
    }})();
  </script>
</body></html>
"""
    return html

# --------- FastAPI ---------
app = FastAPI(title="Production Optimizer (CP-SAT)", version="2.0.0")

mimetypes.add_type("application/vnd.openxmlformats-officedocument.spreadsheetml.sheet", ".xlsx")

from pydantic import BaseModel

class LoginRequest(BaseModel):
    username: str
    password: str

class LoginResponse(BaseModel):
    access_token: str
    token_type: str
    username: str
    role: str
    exp: int
    must_change_password: bool = False

class UserOut(BaseModel):
    username: str
    role: str
    is_active: bool
    must_change_password: bool | None = None
    created_at: str | None = None

class UserCreate(BaseModel):
    username: str
    password: str

class UserUpdate(BaseModel):
    password: str | None = None
    role: str | None = None
    is_active: bool | None = None

class PasswordChange(BaseModel):
    old_password: str
    new_password: str

app.add_middleware(
    CORSMiddleware,
    allow_origins=["*"],  # сузить в проде
    allow_credentials=True,
    allow_methods=["*"],
    allow_headers=["*"],
)

@app.get("/ping")
def ping():
    return {"ok": True}

def schedule(orders, deliveries, stones, sawPrograms, details, policy):
    """Совместимость со старым API — теперь вызывает CP-SAT оптимизатор."""
    return schedule_cp(orders, deliveries, stones, sawPrograms, details, policy)

@app.post("/optimize")
def optimize(payload: dict = Body(...), user=Depends(require_active_user)):
    orders, deliveries, stones, sawPrograms, details, policy = build_runtime(payload)
    df, metrics, tasks_all, resources, calendars, warnings, chosen_breaks = schedule(orders, deliveries, stones, sawPrograms, details, policy)
    result = {"schedule": df.to_dict(orient="records"), "metrics": metrics, "warnings": warnings}
    return JSONResponse(result)

@app.post("/optimize/html")
def optimize_html(payload: dict = Body(...), user=Depends(require_active_user)):
    orders, deliveries, stones, sawPrograms, details, policy = build_runtime(payload)
    df, metrics, tasks_all, resources, calendars, warnings, chosen_breaks = schedule(orders, deliveries, stones, sawPrograms, details, policy)
    html = build_gantt_html(tasks_all, resources, calendars, warnings, breaks=chosen_breaks)
    return HTMLResponse(html)

@app.post("/optimize/html-file")
def optimize_html_file(payload: dict = Body(...), user=Depends(require_active_user)):
    # 1) расчет
    orders, deliveries, stones, sawPrograms, details, policy = build_runtime(payload)
    df, metrics, tasks_all, resources, calendars, warnings, chosen_breaks = schedule(
        orders, deliveries, stones, sawPrograms, details, policy
    )

    # 2) Excel -> bytes
    out = io.BytesIO()
    with pd.ExcelWriter(out, engine="openpyxl") as w:
        df.to_excel(w, index=False, sheet_name="Schedule")
        if warnings:
            pd.DataFrame(warnings).to_excel(w, index=False, sheet_name="Validation")
    out.seek(0)
    xlsx_bytes = out.getvalue()

    # 3) ключи в бакете
    calc_id  = f"{int(time.time()*1000)}-{uuid.uuid4().hex[:8]}"
    xlsx_key = f"{S3_PREFIX}schedules/{calc_id}.xlsx"
    html_key = f"{S3_PREFIX}reports/{calc_id}.html"

    # 4) загрузка в S3
    _s3_put(xlsx_key, xlsx_bytes,
            "application/vnd.openxmlformats-officedocument.spreadsheetml.sheet")
    excel_url = _s3_presigned(xlsx_key, filename="schedule.xlsx")

    html = build_gantt_html(tasks_all, resources, calendars, warnings,
                            breaks=chosen_breaks, excel_url=excel_url, base_url=None)
    _s3_put(html_key, html.encode("utf-8"), "text/html; charset=utf-8")

    html_url = _s3_presigned(html_key)

    # 5) отдаем ссылки (html_html оставляем для дебага/резерва)
    return JSONResponse({"ok": True, "html_url": html_url, "excel_url": excel_url, "html": html})

@app.post("/auth/login", response_model=LoginResponse)
def login(req: LoginRequest):
    users = _load_users()
    user = users.get(req.username)
    if not user or not user.get("is_active", True):
        raise HTTPException(status_code=401, detail="Неверное имя пользователя или пароль")
    if not verify_password(req.password, user["password_hash"]):
        raise HTTPException(status_code=401, detail="Неверное имя пользователя или пароль")

    token, exp = create_access_token(user["username"], user["role"])
    return LoginResponse(
        access_token=token,
        token_type="bearer",
        username=user["username"],
        role=user["role"],
        exp=exp,
        must_change_password=bool(user.get("must_change_password", False)),
    )

@app.get("/auth/me", response_model=UserOut)
def auth_me(user=Depends(get_current_user)):
    users = _load_users()
    u = users.get(user["username"], {})
    return UserOut(
        username=user["username"],
        role=user["role"],
        is_active=u.get("is_active", True),
        must_change_password=u.get("must_change_password"),
        created_at=u.get("created_at"),
    )

@app.get("/users", response_model=list[UserOut])
def list_users(_: dict = Depends(require_admin)):
    users = _load_users()
    return [
        UserOut(
            username=u["username"],
            role=u.get("role", "user"),
            is_active=u.get("is_active", True),
            must_change_password=u.get("must_change_password"),
            created_at=u.get("created_at"),
        )
        for u in users.values()
    ]

USERNAME_RE = re.compile(r"^[A-Za-z0-9_.-]+$")
CYRILLIC_RE = re.compile(r"[А-Яа-яЁё]")

@app.post("/users", response_model=UserOut)
def create_user(payload: UserCreate, _: dict = Depends(require_admin)):
    users = _load_users()

    username = payload.username.strip()
    if not username:
        raise HTTPException(status_code=400, detail="Требуется указать имя пользователя")

    if not USERNAME_RE.match(username):
        raise HTTPException(
            status_code=400,
            detail="Имя пользователя может содержать только латинские буквы и символы ._-",
        )

    if username in users:
        raise HTTPException(status_code=400, detail="Такое имя пользователя уже существует")

    if CYRILLIC_RE.search(payload.password):
        raise HTTPException(
            status_code=400,
            detail="Пароль не может содержать русские буквы",
        )

    users[username] = {
        "username": username,
        "password_hash": hash_password(payload.password),
        "role": "user",                    # админ создаёт только обычных пользователей
        "is_active": True,
        "must_change_password": True,      # при первом входе заставим сменить
        "created_at": dt.datetime.utcnow().isoformat() + "Z",
    }
    _save_users(users)
    return UserOut(
        username=username,
        role="user",
        is_active=True,
        created_at=users[username]["created_at"],
    )

@app.put("/users/{username}", response_model=UserOut)
def update_user(username: str, payload: UserUpdate, admin=Depends(require_admin)):
    users = _load_users()
    if username not in users:
        raise HTTPException(status_code=404, detail="Пользователь не найдет")

    # Базового admin нельзя понизить или выключить
    if username == AUTH_BOOTSTRAP_ADMIN_LOGIN:
        if payload.role is not None and payload.role != "admin":
            raise HTTPException(status_code=400, detail="Нельзя поменнять роль учетной записи admin")
        if payload.is_active is False:
            raise HTTPException(status_code=400, detail="Нельзя деактивировать учетную запись admin")

    user = users[username]

    # Защита от потери последнего админа
    if payload.role == "user" or payload.is_active is False:
        if user["role"] == "admin":
            other_admins = [u for u in users.values()
                            if u["username"] != username and u["role"] == "admin" and u.get("is_active", True)]
            if not other_admins:
                raise HTTPException(status_code=400, detail="Нельзя деактивировать последнего admin")

    if payload.password:
        user["password_hash"] = hash_password(payload.password)
        user["must_change_password"] = True  # ← при сбросе пароля заставляем сменить
    if payload.role:
        if payload.role not in ("admin", "user"):
            raise HTTPException(status_code=400, detail="Неверная роль")
        user["role"] = payload.role
    if payload.is_active is not None:
        user["is_active"] = payload.is_active

    users[username] = user
    _save_users(users)
    return UserOut(
        username=user["username"],
        role=user["role"],
        is_active=user.get("is_active", True),
        created_at=user.get("created_at"),
    )

@app.delete("/users/{username}")
def delete_user(username: str, admin=Depends(require_admin)):
    users = _load_users()
    if username not in users:
        raise HTTPException(status_code=404, detail="Пользователь не найден")

    # Нельзя удалять встроенного админа
    if username == AUTH_BOOTSTRAP_ADMIN_LOGIN:
        raise HTTPException(status_code=400, detail="Учетная запись admin не может быть удалена")

    user = users[username]
    if user["role"] == "admin":
        other_admins = [u for u in users.values()
                        if u["username"] != username and u["role"] == "admin" and u.get("is_active", True)]
        if not other_admins:
            raise HTTPException(status_code=400, detail="Нельзя удалить последнюю учетную запись admin")

    del users[username]
    _save_users(users)
    return {"ok": True}

@app.post("/auth/change-password", response_model=LoginResponse)
def change_password(payload: PasswordChange, current=Depends(get_current_user)):
    users = _load_users()
    user = users.get(current["username"])
    if not user or not user.get("is_active", True):
        raise HTTPException(status_code=401, detail="Пользователь не найден, либо неактивен")

    if not verify_password(payload.old_password, user["password_hash"]):
        raise HTTPException(status_code=400, detail="Неверный пароль")

    if len(payload.new_password) < 8:
        raise HTTPException(status_code=400, detail="Пароль слишком короткий (нужно от 8 символов)")

    user["password_hash"] = hash_password(payload.new_password)
    user["must_change_password"] = False
    users[user["username"]] = user
    _save_users(users)

    token, exp = create_access_token(user["username"], user["role"])
    return LoginResponse(
        access_token=token,
        token_type="bearer",
        username=user["username"],
        role=user["role"],
        exp=exp,
        must_change_password=False,
    )