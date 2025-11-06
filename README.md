python -m venv .venv && source .venv/bin/activate  # (Windows: .venv\Scripts\activate)
pip install -r requirements.txt
uvicorn optimizer_service:app --reload --host 0.0.0.0 --port 8088