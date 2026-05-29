#!/usr/bin/env bash
PORT=${1:-8080}
echo ""
echo "  ⬡  Grenzcheck Web-App"
echo "  → http://localhost:$PORT"
echo ""
echo "  Zum Beenden: Ctrl+C"
echo ""
cd "$(dirname "$0")"
python3 -m http.server $PORT
