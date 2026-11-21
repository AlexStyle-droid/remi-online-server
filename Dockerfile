# Remi Online — imagine server de joc
FROM python:3.12-slim
WORKDIR /app
COPY server/remi_server.py /app/server/remi_server.py
COPY server/table_engine.py /app/server/table_engine.py
COPY app/assets /app/app/assets
EXPOSE 8080
ENV PORT=8080
CMD ["sh","-c","python3 /app/server/remi_server.py --port ${PORT:-8080} --host 0.0.0.0"]
