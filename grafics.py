import ezdxf
import math
import re
from typing import List, Dict, Any, Tuple
from collections import Counter

# ---------- утилиты ----------

def is_number(text: str) -> bool:
    """Проверяем, что строка – число (допускаем запятую и единицы измерения)."""
    s = text.strip().replace(",", ".")
    # выкидываем всё, кроме цифр, точки, знаков и e/E
    s = re.sub(r"[^\d.\-+eE]", "", s)
    if not s:
        return False
    try:
        float(s)
        return True
    except ValueError:
        return False


def parse_float(text: str) -> float:
    s = text.strip().replace(",", ".")
    s = re.sub(r"[^\d.\-+eE]", "", s)
    return float(s)


def distance(p1: Tuple[float, float], p2: Tuple[float, float]) -> float:
    return math.hypot(p1[0] - p2[0], p1[1] - p2[1])

# ---------- ищем стрелочки/лидеры ----------

def extract_leaders(msp, max_length=300.0) -> List[Dict[str, Any]]:
    """
    Ищем стрелки как LEADER или короткие LWPOLYLINE.
    Возвращаем список с набором вершин.
    """
    leaders = []

    # 1) явные LEADER
    for e in msp.query("LEADER"):
        pts = [(p[0], p[1]) for p in e.vertices]  # проверь, как у тебя ezdxf отдаёт вершины
        if len(pts) < 2:
            continue
        length = sum(math.hypot(pts[i+1][0] - pts[i][0],
                                pts[i+1][1] - pts[i][1])
                     for i in range(len(pts) - 1))
        if length <= max_length:
            leaders.append({"points": pts, "entity": e})

    # 2) короткие LWPOLYLINE (если стрелки сделаны так)
    for e in msp.query("LWPOLYLINE"):
        pts = [(vx[0], vx[1]) for vx in e]
        if len(pts) < 2:
            continue
        length = sum(math.hypot(pts[i+1][0] - pts[i][0],
                                pts[i+1][1] - pts[i][1])
                     for i in range(len(pts) - 1))
        if length <= max_length:
            leaders.append({"points": pts, "entity": e})

    return leaders

def find_leader_for_label(label, leaders, max_dist=200.0):
    """Находим лидер, привязанный к надписи (по ближайшей вершине)."""
    lx, ly = label["x"], label["y"]

    best = None
    best_d = max_dist

    for L in leaders:
        pts = L["points"]
        # вершина, ближайшая к тексту
        start = min(pts, key=lambda p: distance((lx, ly), p))
        d = distance((lx, ly), start)
        if d < best_d:
            # кончик стрелки — вершина, наиболее удалённая от старта
            tip = max(pts, key=lambda p: distance(start, p))
            best = {"start": start, "tip": tip, "entity": L["entity"]}
            best_d = d

    return best  # либо None

def angle_between(v1, v2):
    x1, y1 = v1
    x2, y2 = v2
    n1 = math.hypot(x1, y1)
    n2 = math.hypot(x2, y2)
    if n1 == 0 or n2 == 0:
        return 180.0
    cos_a = max(-1.0, min(1.0, (x1*x2 + y1*y2) / (n1*n2)))
    return math.degrees(math.acos(cos_a))


def find_dim_for_label_with_leader(label, leader, numeric_texts,
                                   angle_tol=30.0, dist_tol=800.0):
    """
    Ищем размер для метки, используя направление стрелки.
    numeric_texts — это dim_texts из DIMENSION + числовые TEXT/MTEXT.
    """
    lx, ly = label["x"], label["y"]
    tipx, tipy = leader["tip"]

    v_lt = (tipx - lx, tipy - ly)

    best = None
    best_angle = None
    best_dist = None

    for num in numeric_texts:
        vx = num["x"] - lx
        vy = num["y"] - ly
        v_ld = (vx, vy)
        ang = angle_between(v_lt, v_ld)
        d = math.hypot(vx, vy)

        if ang <= angle_tol and d <= dist_tol:
            if best is None or ang < best_angle or (ang == best_angle and d < best_dist):
                best = num
                best_angle = ang
                best_dist = d

    return best  # либо None

def nearest_dim_to_point(
    point: Tuple[float, float],
    numeric_texts: List[Dict[str, Any]],
    dist_tol: float = 400.0,
) -> Dict[str, Any] | None:
    """
    Ищем ближайший размер (numeric_text) к заданной точке.
    Возвращаем словарь из numeric_texts или None, если все дальше dist_tol.
    """
    px, py = point
    best = None
    best_d = dist_tol

    for num in numeric_texts:
        d = distance((px, py), (num["x"], num["y"]))
        if d < best_d:
            best = num
            best_d = d

    return best


def canonical_value(values: List[float]) -> float | None:
    """
    Из набора значений для ТС или ЦС берём "каноническое":
    - группируем по округлению до 0.1 мм,
    - берём кластер с наибольшей частотой,
    - возвращаем одно из исходных значений из этого кластера.
    """
    if not values:
        return None
    cnt = Counter(round(v, 1) for v in values)
    main_round, _ = cnt.most_common(1)[0]
    for v in values:
        if abs(round(v, 1) - main_round) < 0.11:
            return v
    return values[0]

# ---------- чтение TEXT / MTEXT ----------

def extract_texts(msp) -> List[Dict[str, Any]]:
    """TEXT и MTEXT из modelspace."""
    texts = []
    for e in msp:
        dxftype = e.dxftype()
        if dxftype == "TEXT":
            content = e.dxf.text or ""
            insert = e.dxf.insert
            height = e.dxf.height
        elif dxftype == "MTEXT":
            try:
                content = e.plain_text()
            except AttributeError:
                content = e.text
            insert = e.dxf.insert
            # у MTEXT высота немного иначе задаётся, но для наших задач не критично
            height = getattr(e.dxf, "char_height", 0.0)
        else:
            continue

        content = content.strip()
        if not content:
            continue

        texts.append(
            {
                "text": content,
                "x": float(insert.x),
                "y": float(insert.y),
                "height": float(height) if height else 0.0,
            }
        )

    return texts

# ---------- чтение размеров DIMENSION ----------

def extract_dimension_texts(msp) -> List[Dict[str, Any]]:
    """
    Берём все DIMENSION, вытаскиваем их числовое значение и
    координаты середины размерного текста.
    """
    dim_texts: List[Dict[str, Any]] = []

    for dim in msp.query("DIMENSION"):
        # 1. текст, который реально отображается
        txt = dim.dxf.text

        if not txt or txt == "<>":  # "<>" или "" — значит надо брать измерение
            try:
                meas = dim.get_measurement()  # float для линейных размеров
            except Exception:
                continue

            if not isinstance(meas, (int, float)):
                # углы / вектора сейчас не обрабатываем
                continue

            # форматируем примерно как в чертеже: либо целое, либо 1 знак после запятой
            if abs(meas - round(meas)) < 1e-4:
                txt = str(int(round(meas)))
            else:
                txt = f"{meas:.1f}".rstrip("0").rstrip(".")
        else:
            txt = txt.strip()

        # 2. координаты текстового блока
        try:
            tp = dim.dxf.text_midpoint  # OCS
            # переводим в WCS (на всякий случай, вдруг там не плоский чертёж)
            ocs = dim.ocs()
            p_wcs = ocs.to_wcs(tp)
            x, y = float(p_wcs.x), float(p_wcs.y)
        except Exception:
            # запасной вариант — дефпоинт
            p = dim.dxf.defpoint
            x, y = float(p[0]), float(p[1])

        dim_texts.append(
            {
                "text": txt,
                "x": x,
                "y": y,
                "height": 0.0,
                "dim": dim,
            }
        )

    return dim_texts

# ---------- парсинг блоков "Кромка ..." / "Подворот ..." ----------

def parse_header_block(text: str, prefix: str) -> Tuple[float, List[float]]:
    """
    "Кромка 16\\n2525\\n955\\n..." -> (16.0, [2525, 955, ...])
    """
    lines = [ln.strip() for ln in text.splitlines() if ln.strip()]
    if not lines:
        return None, []

    header = lines[0]
    # параметр (16, 45 и т.п.)
    m = re.search(rf"{re.escape(prefix)}\s+([\d.,]+)", header)
    param = float(m.group(1).replace(",", ".")) if m else None

    # остальные строки — длины
    lengths = [parse_float(ln) for ln in lines[1:] if is_number(ln)]

    return param, lengths

# ---------- привязка размеров к ТС / ЦС ----------

def extract_label_sizes(
    texts: List[Dict[str, Any]],
    labels: List[str],
    numeric_texts: List[Dict[str, Any]],
    max_dist: float = 800.0,
) -> Dict[str, List[float]]:
    """
    Для каждой надписи (ТС / ЦС) ищем ближайший числовой размер в радиусе max_dist.
    """
    label_texts = [
        t for t in texts
        if t["text"].strip().upper() in labels
    ]

    result: Dict[str, List[float]] = {lab: [] for lab in labels}

    for lab in label_texts:
        lab_name = lab["text"].strip().upper()
        lab_pos = (lab["x"], lab["y"])

        best_val = None
        best_dist = None

        for num in numeric_texts:
            d = distance(lab_pos, (num["x"], num["y"]))
            if d <= max_dist and (best_dist is None or d < best_dist):
                best_dist = d
                best_val = parse_float(num["text"])

        if best_val is not None:
            result[lab_name].append(best_val)

    # убираем дубли и сортируем
    for k in result:
        result[k] = sorted(set(result[k]))

    return result

# ---------- основная функция ----------

def analyze_cutting_sheet(dxf_path: str) -> Dict[str, Any]:
    """
    Разбор карты раскроя:
      - Кромка: параметр и список длин
      - Подворот: параметр и список длин
      - ТС / ЦС: итоговое значение длины и сырые значения
    """
    doc = ezdxf.readfile(dxf_path)
    msp = doc.modelspace()

    # --- TEXT / MTEXT и размерные подписи DIMENSION ---
    texts = extract_texts(msp)
    dim_texts = extract_dimension_texts(msp)

    # ------------------------------------------------------------------
    # 1. Кромка и Подворот — берём из многострочных MTEXT
    # ------------------------------------------------------------------
    kromka_param = None
    kromka_lengths: List[float] = []
    podv_param = None
    podv_lengths: List[float] = []

    for t in texts:
        txt = t["text"]

        if txt.startswith("Кромка") and "\n" in txt:
            param, lens = parse_header_block(txt, "Кромка")
            if param is not None and lens:
                kromka_param, kromka_lengths = param, lens

        elif txt.startswith("Подворот") and "\n" in txt:
            param, lens = parse_header_block(txt, "Подворот")
            if param is not None and lens:
                podv_param, podv_lengths = param, lens

    # ------------------------------------------------------------------
    # 2. Числовые подписи для размеров:
    #    - из DIMENSION
    #    - плюс любые числовые TEXT/MTEXT
    # ------------------------------------------------------------------
    numeric_texts: List[Dict[str, Any]] = []

    for t in dim_texts:
        if is_number(t["text"]):
            numeric_texts.append(t)

    for t in texts:
        if is_number(t["text"]):
            numeric_texts.append(t)

    # ------------------------------------------------------------------
    # 3. Лидеры (стрелки)
    # ------------------------------------------------------------------
    leaders = extract_leaders(msp)

    # ------------------------------------------------------------------
    # 4. ТС и ЦС:
    #    - сначала пробуем найти размер по направлению стрелки (как раньше);
    #    - если не нашли для какой-то метки, пробуем взять ближайший размер к кончику стрелки;
    #    - по группе берём мажоритарное значение.
    # ------------------------------------------------------------------
    label_values: Dict[str, List[float]] = {"ТС": [], "ЦС": []}

    for lab in texts:
        name = lab["text"].strip().upper()
        if name not in ("ТС", "ЦС"):
            continue

        # ищем стрелку для этой надписи
        leader = find_leader_for_label(lab, leaders, max_dist=200.0)
        if not leader:
            # у конкретной надписи нет стрелки — пропустим её,
            # значение подтянем по группе
            continue

        # --- основной способ: по направлению стрелки ---
        dim_candidate = find_dim_for_label_with_leader(
            label=lab,
            leader=leader,
            numeric_texts=numeric_texts,
            angle_tol=30.0,
            dist_tol=800.0,
        )

        # --- фолбэк: ближайший размер к кончику стрелки ---
        if dim_candidate is None:
            tip = leader["tip"]
            dim_candidate = nearest_dim_to_point(
                point=tip,
                numeric_texts=numeric_texts,
                dist_tol=400.0,  # можно подстроить при необходимости
            )

        if dim_candidate and is_number(dim_candidate["text"]):
            val = parse_float(dim_candidate["text"])
            label_values[name].append(val)

    # итоговые значения по группам
    ts_canon = canonical_value(label_values["ТС"])
    cs_canon = canonical_value(label_values["ЦС"])

    result: Dict[str, Any] = {
        "kromka": {
            "param": kromka_param,
            "lengths": kromka_lengths,
        },
        "podvorot": {
            "param": podv_param,
            "lengths": podv_lengths,
        },
        "ts": [ts_canon] if ts_canon is not None else [],
        "cs": [cs_canon] if cs_canon is not None else [],
        "ts_raw": label_values["ТС"],
        "cs_raw": label_values["ЦС"],
    }

    return result

if __name__ == "__main__":
    path = "6114 раскрой.dxf"  # твой путь к файлу
    res = analyze_cutting_sheet(path)
    print(res)