# Building Permit Boundary Check – Blender Add-on

**Autoren:** Jonas Halter, Kay Schürmann, Oliver Hasler, Felix Egger  
**Version:** 1.0.0  
**Blender:** 3.6 oder neuer  
**Speicherort:** `View3D › Sidebar › Grenzcheck`

---

## Beschreibung

Dieses Blender-Add-on prüft automatisch den Grenzabstand zwischen einem IFC-Gebäude und den Nachbarparzellen anhand von Schweizer Geodaten (Swisstopo). Es kombiniert Parzellenimport, OEREB-Abfrage, Grenzabstandsberechnung und PDF-Export in einem einheitlichen Workflow direkt in Blender.

---

## Funktionen

- **Parzellenabfrage** per EGRID oder Adresse über die Swisstopo-API (WFS/GeoJSON/GeoPackage)
- **IFC-Import** mit automatischer Georeferenzierung (LV95 / EPSG:2056)
- **Grenzabstandsprüfung** mit konfigurierbaren Abständen (grosser/kleiner Grenzabstand)
- **OEREB-Abfrage** für alle Schweizer Kantone (automatische Kantonsermittlung per EGRID)
- **Nutzungszonenauswahl** aus dem OEREB-Extrakt mit Flächenangabe
- **3D-Visualisierung** der Grenzabstandsverletzungen direkt in der Blender-Szene
- **SwissContext-Import** (Swisstopo-Gelände, Gebäude, Satellitenbilder)
- **SwissBuildings3D-Import** (3D-Gebäudemodelle der Umgebung)
- **Docker-basiertes Backend** für die Geodatenverarbeitung
- **PDF-Export** des Grenzabstandsberichts mit Kamera-Renderings
- **Vollständiger Reset** der Szene und heruntergeladener Daten

---

## Voraussetzungen

- Blender 3.6+
- Docker (für das Geodaten-Backend)
- Python-Paket `pyproj` (optional, für Koordinatentransformationen)
- `ifcopenshell` (wird automatisch aus einem mitgelieferten `.whl`-Wheel geladen)
- Projektordner mit der erwarteten Struktur (Abgabeordner oder Entwicklungsstruktur)

---

## Installation

1. `.py`-Datei in Blender unter `Edit › Preferences › Add-ons › Install` auswählen
2. Add-on aktivieren
3. Im `Grenzcheck`-Panel den Projektordner angeben (oder automatische Erkennung abwarten)
4. Docker muss auf dem System installiert und erreichbar sein

---

## Verwendung

1. EGRID oder Adresse eingeben und Parzelle laden
2. IFC-Datei importieren
3. Grenzabstandsparameter setzen (Standard: 6 m / 3 m)
4. Grenzcheck ausführen – Ergebnis erscheint im Panel und wird in der 3D-Szene visualisiert
5. Optional: OEREB-Daten abfragen, Umgebung laden, PDF-Bericht exportieren

---

## Projektstruktur (erwartet)

```
<Projektordner>/
├── Abgabeordner/
│   ├── Docker-Container/   ← Dockerfile und Backend
│   └── Daten/              ← GeoPackage, GeoJSON, temporäre Dateien
```

Alternativ wird auch die ältere Entwicklungsstruktur (`CodeJonas/Docker`) erkannt.

---

## Hinweise

- Die OEREB-Abfrage erfolgt parallel über alle konfigurierten Kantonsendpoints.
- PDFs und heruntergeladene Geodaten werden getrennt verwaltet; beim Reset bleiben PDFs erhalten.
- Das Add-on setzt `SRID`, `crs x/y`, `latitude`, `longitude` und `scale` als Szenen-Metadaten für die Georeferenzierung.
