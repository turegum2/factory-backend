FROM python:3.12-slim
ENV PYTHONDONTWRITEBYTECODE=1 PYTHONUNBUFFERED=1
WORKDIR /app

# 1) Сначала код — чтобы chown зацепил всё
COPY . .

# 2) Зависимости + пользователь + папки и права
RUN pip install --no-cache-dir -r requirements.txt \
    && adduser --disabled-password --gecos "" app \
    && mkdir -p /app/frontend \
    && chown -R app:app /app

USER app

# 3) Uvicorn на 8080
CMD ["uvicorn", "optimizer_service:app", "--host", "0.0.0.0", "--port", "8080"]