# ── Basis-Image ───────────────────────────────────────────────────────────────
FROM python:3.11-slim

# System-Abhängigkeiten für Geodaten-Bibliotheken
RUN apt-get update && apt-get install -y \
    gcc \
    g++ \
    gdal-bin \
    libgdal-dev \
    libproj-dev \
    proj-bin \
    && rm -rf /var/lib/apt/lists/*

# Arbeitsverzeichnis im Container
WORKDIR /app

# Python-Bibliotheken installieren
COPY requirements.txt ./requirements.txt
RUN pip install --no-cache-dir --upgrade pip \
    && pip install --no-cache-dir -r requirements.txt

# Download-Script kopieren
COPY api_download.py ./api_download.py

# Datenpfad als Volume – wird vom Blender-Add-on gemountet:
#   docker run -v /pfad/zu/Abgabeordner/Daten:/app/data ...
VOLUME ["/app/data"]

# Einstiegspunkt: das Script liest Umgebungsvariablen (EGRID, OUTPUT_DIR, …)
CMD ["python", "api_download.py"]
