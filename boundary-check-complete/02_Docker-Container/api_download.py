from __future__ import annotations

import argparse
import json
import os
import re
import shutil
import sys
import xml.etree.ElementTree as ET
import zipfile
from concurrent.futures import ThreadPoolExecutor, as_completed
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable

import geopandas as gpd
import requests
from shapely.geometry import MultiPolygon
from shapely.geometry.base import BaseGeometry


# ── OEREB ──────────────────────────────────────────────────────────────────────

OEREB_NS = {
    "extract": "http://schemas.geo.admin.ch/V_D/OeREB/2.0/Extract",
    "data": "http://schemas.geo.admin.ch/V_D/OeREB/2.0/ExtractData",
}
OEREB_SERVICE_ENDPOINTS: dict[str, str] = {
    "AG": "https://api.geo.ag.ch/v2/oereb",
    "AI": "https://oereb.ai.ch/ktai/wsgi/oereb",
    "AR": "https://oereb.ar.ch/ktar/wsgi/oereb",
    "BE": "https://www.oereb2.apps.be.ch",
    "BL": "https://oereb.geo.bl.ch",
    "BS": "https://api.oereb.bs.ch",
    "FR": "https://maps.fr.ch/RDPPF_ws/RdppfSVC.svc",
    "GE": "https://ge.ch/terecadastrews/RdppfSVC.svc",
    "GL": "https://map.geo.gl.ch/oereb",
    "GR": "https://oereb.geo.gr.ch/oereb",
    "JU": "https://geo.jura.ch/crdppf_server",
    "LU": "https://svc.geo.lu.ch/oereb",
    "NE": "https://oereb.gis-daten.ch/oereb",
    "SG": "https://oereb.geo.sg.ch/ktsg/wsgi/oereb",
    "SH": "https://oereb.geo.sh.ch",
    "SO": "https://geo.so.ch/api/oereb",
    "SZ": "https://map.geo.sz.ch/oereb",
    "TG": "https://map.geo.tg.ch/services/oereb",
    "TI": "https://crdpp.geo.ti.ch/oereb2",
    "UR": "https://prozessor-oereb.ur.ch/oereb",
    "VD": "https://www.rdppf.vd.ch/ws/RdppfSVC.svc",
    "VS": "https://rdppf.apps.vs.ch",
    "ZG": "https://oereb.zg.ch/ors",
    "ZH": "https://maps.zh.ch/oereb/v2",
}


def _oereb_text(element: ET.Element | None, xpath: str) -> str | None:
    if element is None:
        return None
    node = element.find(xpath, OEREB_NS)
    return node.text.strip() if node is not None and node.text else None


def _fetch_oereb_from_endpoint(base_url: str, egrid: str) -> dict | None:
    url = f"{base_url.rstrip('/')}/extract/xml/?EGRID={egrid}"
    try:
        resp = requests.get(url, timeout=20, headers={"Accept": "application/xml,text/xml"})
        resp.raise_for_status()
        if "GetExtractByIdResponse" not in resp.text:
            return None
    except Exception:
        return None

    try:
        root = ET.fromstring(resp.text)
    except ET.ParseError:
        return None

    # Alle Restrictions aggregieren (kein Theme-Filter) — kantonale Theme-Codes
    # wie ch.SZ.NutzungsplanungGemeinden würden sonst gefiltert.
    aggregated: dict[tuple, dict] = {}
    for r in root.findall(".//data:RestrictionOnLandownership", OEREB_NS):
        theme_code = _oereb_text(r, "data:Theme/data:Code") or ""
        theme_text = _oereb_text(r, "data:Theme/data:Text/data:LocalisedText/data:Text") or ""
        legend_text = _oereb_text(r, "data:LegendText/data:LocalisedText/data:Text") or ""
        if not legend_text:
            continue
        type_code = _oereb_text(r, "data:TypeCode")
        law_status = _oereb_text(r, "data:Lawstatus/data:Code")
        raw_area = _oereb_text(r, "data:AreaShare")
        raw_pct = _oereb_text(r, "data:PartInPercent")
        area = int(raw_area) if raw_area and raw_area.isdigit() else None
        pct: float | None
        try:
            pct = float(raw_pct) if raw_pct else None
        except ValueError:
            pct = None

        key = (theme_code, legend_text, law_status, type_code)
        if key in aggregated:
            if area is not None:
                aggregated[key]["area_share"] = (aggregated[key]["area_share"] or 0) + area
            if pct is not None:
                aggregated[key]["part_in_percent"] = (aggregated[key]["part_in_percent"] or 0.0) + pct
        else:
            aggregated[key] = {
                "legend_text": legend_text,
                "theme_code": theme_code,
                "theme_text": theme_text,
                "type_code": type_code,
                "law_status": law_status,
                "area_share": area,
                "part_in_percent": pct,
            }

    re_elem = root.find(".//data:RealEstate", OEREB_NS)
    municipality = _oereb_text(re_elem, "data:Municipality/data:Name/data:LocalisedText/data:Text")

    # Nur Zonen die die Parzelle tatsächlich berühren — Einträge ohne Fläche sind
    # Gemeindeweite Legendeneinträge die nicht auf der Parzelle liegen.
    def _has_area(z: dict) -> bool:
        return (z.get("area_share") or 0) > 0 or (z.get("part_in_percent") or 0.0) > 0.0

    def _sort_key(z: dict) -> tuple:
        is_nutzung = "nutzungsplanung" in (z.get("theme_code") or "").lower()
        return (not is_nutzung, -(z.get("area_share") or 0), -(z.get("part_in_percent") or 0.0))

    zones = sorted([z for z in aggregated.values() if _has_area(z)], key=_sort_key)
    return {"zones": list(zones), "municipality": municipality}


def fetch_oereb_zones(egrid: str, canton: str | None = None) -> dict | None:
    if canton and canton in OEREB_SERVICE_ENDPOINTS:
        result = _fetch_oereb_from_endpoint(OEREB_SERVICE_ENDPOINTS[canton], egrid)
        if result is not None:
            return result

    remaining = [(c, u) for c, u in OEREB_SERVICE_ENDPOINTS.items() if c != canton]
    with ThreadPoolExecutor(max_workers=8) as executor:
        futures = {executor.submit(_fetch_oereb_from_endpoint, url, egrid): c for c, url in remaining}
        for future in as_completed(futures):
            result = future.result()
            if result is not None:
                return result
    return None


# DATA_DIR: Im Container ist /app/data das gemountete Host-Verzeichnis
# (docker run -v /host/Abgabeordner/Daten:/app/data)
# Env-Variable DATA_OUTPUT_DIR erlaubt Überschreiben (optional)
import os as _os
BASE_DIR = Path(__file__).resolve().parent          # /app
DATA_DIR = Path(_os.environ.get("DATA_OUTPUT_DIR", str(BASE_DIR / "data")))
GEOPACKAGE_DIR = DATA_DIR / "geopackage"            # Abgabeordner/Daten/geopackage
PARCEL_DB_DIR  = DATA_DIR / "geopackage"            # GeoPackages in geopackage/
TEMP_DIR       = DATA_DIR / "tmp"

EGRID_PATTERN = re.compile(r"^CH\d{12}$")


def canton_download_url(canton: str) -> str:
    return f"https://geodienste.ch/downloads/geopackage/av/{canton}/deu/av_{canton}_gpkg_lv95.zip"


SUPPORTED_CANTONS = {
    code: {"name": name, "download_url": canton_download_url(code)}
    for code, name in {
        "AG": "Aargau",
        "AI": "Appenzell Innerrhoden",
        "AR": "Appenzell Ausserrhoden",
        "BE": "Bern",
        "BL": "Basel-Landschaft",
        "BS": "Basel-Stadt",
        "FL": "Liechtenstein",
        "FR": "Fribourg",
        "GE": "Geneve",
        "GL": "Glarus",
        "GR": "Graubuenden",
        "JU": "Jura",
        "LU": "Luzern",
        "NE": "Neuchatel",
        "NW": "Nidwalden",
        "OW": "Obwalden",
        "SG": "St. Gallen",
        "SH": "Schaffhausen",
        "SO": "Solothurn",
        "SZ": "Schwyz",
        "TG": "Thurgau",
        "TI": "Ticino",
        "UR": "Uri",
        "VD": "Vaud",
        "VS": "Valais",
        "ZG": "Zug",
        "ZH": "Zuerich",
    }.items()
}

PREFERRED_PARCEL_LAYERS = [
    "resf",
    "dprsf",
    "resfproj",
    "dprsfproj",
]

EGRID_FIELD_CANDIDATES = [
    "EGRIS_EGRID",
    "EGRID",
    "egrid",
    "egris_egrid",
]


class UserFacingError(Exception):
    pass


@dataclass
class ParcelMatch:
    layer_name: str
    feature_index: int
    egrid_field: str
    parcel_geometry: BaseGeometry
    attributes: dict[str, object]
    parcel_layer_gdf: gpd.GeoDataFrame


@dataclass
class LayerFeatures:
    layer_name: str
    geometry_type: str
    gdf: gpd.GeoDataFrame
    intersecting: gpd.GeoDataFrame


def ensure_directories() -> None:
    for path in (GEOPACKAGE_DIR, PARCEL_DB_DIR, TEMP_DIR):
        path.mkdir(parents=True, exist_ok=True)


def prompt_for_canton() -> str:
    print("Verfuegbare Kantone:")
    print(", ".join(sorted(SUPPORTED_CANTONS)))
    canton = input("Bitte Kantonskuerzel eingeben (z.B. ZH): ").strip().upper()
    if canton not in SUPPORTED_CANTONS:
        supported = ", ".join(sorted(SUPPORTED_CANTONS))
        raise UserFacingError(
            f"Fehler: Der Kanton '{canton or '?'}' wird aktuell nicht unterstuetzt. "
            f"Unterstuetzte Kantone: {supported}"
        )
    return canton


def prompt_for_egrid() -> str:
    egrid = input("Bitte E-GRID der Parzelle eingeben (z.B. CH735977412691): ").strip().upper()
    if not EGRID_PATTERN.match(egrid):
        raise UserFacingError("Fehler: Ungueltige E-GRID. Erwartet wird das Format 'CH' gefolgt von 12 Ziffern.")
    return egrid


def validate_canton(canton: str) -> str:
    canton = canton.strip().upper()
    if canton not in SUPPORTED_CANTONS:
        supported = ", ".join(sorted(SUPPORTED_CANTONS))
        raise UserFacingError(
            f"Fehler: Der Kanton '{canton or '?'}' wird aktuell nicht unterstuetzt. "
            f"Unterstuetzte Kantone: {supported}"
        )
    return canton


def validate_egrid(egrid: str) -> str:
    egrid = egrid.strip().upper()
    if not EGRID_PATTERN.match(egrid):
        raise UserFacingError("Fehler: Ungueltige E-GRID. Erwartet wird das Format 'CH' gefolgt von 12 Ziffern.")
    return egrid


def geopackage_cache_path(canton: str) -> Path:
    return GEOPACKAGE_DIR / canton / f"av_{canton}_2056.gpkg"


def download_zip_path(canton: str) -> Path:
    return TEMP_DIR / f"av_{canton}_gpkg_lv95.zip"


def download_geopackage(canton: str) -> Path:
    cached_path = geopackage_cache_path(canton)
    if cached_path.exists():
        print(f"GeoPackage-Cache gefunden: {cached_path}")
        return cached_path

    canton_config = SUPPORTED_CANTONS[canton]
    download_url = canton_config["download_url"]
    zip_path = download_zip_path(canton)
    extract_dir = GEOPACKAGE_DIR / canton

    extract_dir.mkdir(parents=True, exist_ok=True)
    print(f"Lade GeoPackage fuer {canton} von geodienste.ch herunter ...")

    try:
        with requests.get(download_url, stream=True, timeout=(10, 180)) as response:
            if response.status_code == 404:
                raise UserFacingError(
                    f"Fehler: Fuer den Kanton {canton} wurde auf geodienste.ch kein GeoPackage gefunden."
                )
            response.raise_for_status()
            content_length = int(response.headers.get("content-length", "0"))
            bytes_written = 0
            with zip_path.open("wb") as file_handle:
                for chunk in response.iter_content(chunk_size=1024 * 1024):
                    if not chunk:
                        continue
                    file_handle.write(chunk)
                    bytes_written += len(chunk)
                    if content_length:
                        progress = bytes_written / content_length * 100
                        print(f"  Download: {progress:5.1f}% ({bytes_written / 1024 / 1024:.1f} MB)", end="\r")
            if content_length:
                print()
    except requests.RequestException as exc:
        raise UserFacingError(f"Fehler beim Download des GeoPackage fuer {canton}: {exc}") from exc

    if not zip_path.exists() or zip_path.stat().st_size == 0:
        raise UserFacingError(f"Fehler: Download fuer {canton} war leer oder wurde nicht gespeichert.")

    print(f"Entpacke {zip_path.name} ...")
    try:
        with zipfile.ZipFile(zip_path) as archive:
            archive.extractall(extract_dir)
    except zipfile.BadZipFile as exc:
        raise UserFacingError(f"Fehler: Die heruntergeladene ZIP-Datei fuer {canton} ist ungueltig.") from exc
    finally:
        if zip_path.exists():
            zip_path.unlink()

    gpkg_candidates = sorted(extract_dir.rglob("*.gpkg"))
    if not gpkg_candidates:
        raise UserFacingError(f"Fehler: Nach dem Entpacken wurde fuer {canton} kein GeoPackage gefunden.")

    gpkg_path = gpkg_candidates[0]
    if gpkg_path != cached_path:
        cached_path.parent.mkdir(parents=True, exist_ok=True)
        shutil.move(str(gpkg_path), str(cached_path))

    print(f"GeoPackage gespeichert unter: {cached_path}")
    return cached_path


def load_layers(gpkg_path: Path) -> list[dict[str, str]]:
    try:
        layers_df = gpd.list_layers(gpkg_path)
    except Exception as exc:
        raise UserFacingError(f"Fehler: GeoPackage konnte nicht gelesen werden: {exc}") from exc

    layers: list[dict[str, str]] = []
    for _, row in layers_df.iterrows():
        layers.append(
            {
                "name": str(row["name"]),
                "geometry_type": str(row.get("geometry_type") or "Unknown"),
            }
        )
    if not layers:
        raise UserFacingError("Fehler: Das GeoPackage enthaelt keine Layer.")
    return layers


def find_egrid_field(columns: Iterable[str]) -> str | None:
    lowered = {column.lower(): column for column in columns}
    for candidate in EGRID_FIELD_CANDIDATES:
        if candidate.lower() in lowered:
            return lowered[candidate.lower()]
    for column in columns:
        if "egrid" in column.lower():
            return column
    return None


def read_layer(gpkg_path: Path, layer_name: str) -> gpd.GeoDataFrame:
    try:
        gdf = gpd.read_file(gpkg_path, layer=layer_name)
    except Exception as exc:
        raise UserFacingError(f"Fehler beim Lesen des Layers '{layer_name}': {exc}") from exc
    if gdf.crs is None:
        gdf = gdf.set_crs("EPSG:2056", allow_override=True)
    return gdf


def candidate_parcel_layers(layers: list[dict[str, str]]) -> list[str]:
    layer_names = [layer["name"] for layer in layers]
    polygon_layers = [layer["name"] for layer in layers if "Polygon" in layer["geometry_type"]]
    priority = [name for name in PREFERRED_PARCEL_LAYERS if name in layer_names]
    remainder = [name for name in polygon_layers if name not in priority]
    return priority + remainder


def find_parcel_by_egrid(gpkg_path: Path, layers: list[dict[str, str]], egrid: str) -> ParcelMatch:
    searched_layers: list[str] = []

    for layer_name in candidate_parcel_layers(layers):
        gdf = read_layer(gpkg_path, layer_name)
        if gdf.empty:
            continue

        egrid_field = find_egrid_field(gdf.columns)
        if not egrid_field:
            continue

        searched_layers.append(layer_name)
        matches = gdf[gdf[egrid_field].astype(str).str.upper() == egrid]
        matches = matches[matches.geometry.notnull()]
        if matches.empty:
            continue

        first = matches.iloc[0]
        attributes = {column: first[column] for column in matches.columns if column != "geometry"}
        return ParcelMatch(
            layer_name=layer_name,
            feature_index=int(matches.index[0]),
            egrid_field=egrid_field,
            parcel_geometry=first.geometry,
            attributes=attributes,
            parcel_layer_gdf=gdf,
        )

    searched = ", ".join(searched_layers) if searched_layers else "keine E-GRID-faehigen Polygon-Layer"
    raise UserFacingError(f"Fehler: E-GRID {egrid} wurde im GeoPackage nicht gefunden. Gepruefte Layer: {searched}")


def geometry_intersects(geometry: BaseGeometry | None, parcel_geometry: BaseGeometry) -> bool:
    if geometry is None or geometry.is_empty:
        return False
    try:
        return geometry.intersects(parcel_geometry)
    except Exception:
        return False


def geometry_touches(geometry: BaseGeometry | None, parcel_geometry: BaseGeometry) -> bool:
    if geometry is None or geometry.is_empty:
        return False
    try:
        return geometry.touches(parcel_geometry)
    except Exception:
        return False


def collect_neighboring_parcels(parcel_match: ParcelMatch) -> gpd.GeoDataFrame:
    parcel_layer_gdf = parcel_match.parcel_layer_gdf
    if parcel_layer_gdf.empty or "geometry" not in parcel_layer_gdf.columns:
        return build_parcel_record(parcel_match)

    parcel_layer_gdf = parcel_layer_gdf[parcel_layer_gdf.geometry.notnull()].copy()
    if parcel_layer_gdf.empty:
        return build_parcel_record(parcel_match)

    target_index = parcel_match.feature_index
    selected = parcel_layer_gdf.index == target_index
    touching = parcel_layer_gdf.geometry.apply(
        lambda geom: geometry_touches(geom, parcel_match.parcel_geometry)
    )
    export_gdf = parcel_layer_gdf[selected | touching].copy()
    if export_gdf.empty:
        return build_parcel_record(parcel_match)

    export_gdf["is_target_parcel"] = export_gdf.index == target_index
    export_gdf["source_layer"] = parcel_match.layer_name
    export_gdf["source_feature_index"] = export_gdf.index.astype(int)
    if export_gdf.crs is None:
        export_gdf = export_gdf.set_crs("EPSG:2056", allow_override=True)
    return export_gdf


def collect_features_for_parcel(
    gpkg_path: Path,
    layers: list[dict[str, str]],
    parcel_match: ParcelMatch,
) -> list[LayerFeatures]:
    collected: list[LayerFeatures] = []
    parcel_geometry = parcel_match.parcel_geometry

    for layer in layers:
        layer_name = layer["name"]
        geometry_type = layer["geometry_type"]
        if geometry_type == "Unknown":
            continue

        gdf = read_layer(gpkg_path, layer_name)
        if gdf.empty or "geometry" not in gdf.columns:
            continue

        gdf = gdf[gdf.geometry.notnull()].copy()
        if gdf.empty:
            continue

        intersects_mask = gdf.geometry.apply(lambda geom: geometry_intersects(geom, parcel_geometry))
        intersecting = gdf[intersects_mask].copy()

        if not intersecting.empty:
            collected.append(
                LayerFeatures(
                    layer_name=layer_name,
                    geometry_type=geometry_type,
                    gdf=gdf,
                    intersecting=intersecting,
                )
            )

    if not collected:
        raise UserFacingError("Fehler: Parzelle gefunden, aber keine exportierbaren GeoPackage-Objekte im Perimeter.")

    return collected


def sanitize_layer_name(name: str) -> str:
    sanitized = re.sub(r"[^A-Za-z0-9_]", "_", name)
    return sanitized[:31] or "LAYER"


def build_parcel_record(parcel_match: ParcelMatch) -> gpd.GeoDataFrame:
    parcel_data = dict(parcel_match.attributes)
    parcel_data["is_target_parcel"] = True
    parcel_data["source_layer"] = parcel_match.layer_name
    parcel_data["source_feature_index"] = parcel_match.feature_index
    return gpd.GeoDataFrame([parcel_data], geometry=[parcel_match.parcel_geometry], crs="EPSG:2056")


def export_parcel_database(
    parcel_match: ParcelMatch,
    neighboring_parcels: gpd.GeoDataFrame,
    collected_layers: list[LayerFeatures],
    canton: str,
    egrid: str,
) -> tuple[Path, list[str]]:
    output_dir = PARCEL_DB_DIR / canton
    output_dir.mkdir(parents=True, exist_ok=True)
    output_path = output_dir / f"{egrid}.gpkg"
    if output_path.exists():
        output_path.unlink()

    written_layers: list[str] = []
    parcel_layer_name = sanitize_layer_name(parcel_match.layer_name)
    neighboring_parcels.to_file(output_path, layer=parcel_layer_name, driver="GPKG")
    written_layers.append(parcel_layer_name)

    for layer in collected_layers:
        layer_name = sanitize_layer_name(layer.layer_name)
        if layer_name == parcel_layer_name:
            continue
        layer.intersecting.to_file(output_path, layer=layer_name, driver="GPKG")
        written_layers.append(layer_name)

    return output_path, written_layers


def print_summary(
    parcel_match: ParcelMatch,
    neighboring_parcels: gpd.GeoDataFrame,
    collected_layers: list[LayerFeatures],
    output_path: Path,
    written_layers: list[str],
) -> None:
    print("\nExport abgeschlossen.")
    print(f"Parzellen-Layer: {parcel_match.layer_name}")
    print(f"E-GRID-Feld: {parcel_match.egrid_field}")
    if parcel_match.attributes:
        nummer = parcel_match.attributes.get("Nummer")
        nbident = parcel_match.attributes.get("NBIdent")
        if nummer:
            print(f"Parzellennummer: {nummer}")
        if nbident:
            print(f"NBIdent: {nbident}")
    neighbor_count = max(len(neighboring_parcels) - 1, 0)
    print(f"Angrenzende Parzellen im Export: {neighbor_count}")
    print(f"Betroffene Layer: {len(collected_layers)}")
    print(f"Gespeicherte Layer in der Datenbank: {len(written_layers)}")
    print(f"GeoPackage-Datenbank: {output_path}")


def parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="AV GeoPackage -> E-GRID Datenbank Export")
    parser.add_argument("--canton", help="Kantonskuerzel, z.B. TG")
    parser.add_argument("--egrid", help="E-GRID, z.B. CH735977412691")
    parser.add_argument(
        "--json-output",
        action="store_true",
        help="Gibt am Ende eine maschinenlesbare JSON-Zusammenfassung aus.",
    )
    return parser.parse_args(argv)


def resolve_user_inputs(args: argparse.Namespace) -> tuple[str, str]:
    raw_canton = args.canton or os.environ.get("API_LV95_CANTON")
    raw_egrid = args.egrid or os.environ.get("API_LV95_EGRID")

    canton = validate_canton(raw_canton) if raw_canton else prompt_for_canton()
    egrid = validate_egrid(raw_egrid) if raw_egrid else prompt_for_egrid()
    return canton, egrid


def run_export(canton: str, egrid: str) -> dict[str, object]:
    gpkg_path = download_geopackage(canton)
    layers = load_layers(gpkg_path)
    print(f"GeoPackage geladen: {gpkg_path}")
    print(f"Anzahl Layer: {len(layers)}")

    parcel_match = find_parcel_by_egrid(gpkg_path, layers, egrid)
    print(f"Parzelle gefunden im Layer '{parcel_match.layer_name}'.")

    neighboring_parcels = collect_neighboring_parcels(parcel_match)
    collected_layers = collect_features_for_parcel(gpkg_path, layers, parcel_match)
    output_path, written_layers = export_parcel_database(
        parcel_match,
        neighboring_parcels,
        collected_layers,
        canton,
        egrid,
    )
    print_summary(parcel_match, neighboring_parcels, collected_layers, output_path, written_layers)

    # OEREB Zonen holen und als JSON speichern
    oereb_json_path: str | None = None
    print(f"Hole OEREB-Zonen fuer {egrid} ...")
    oereb_result = fetch_oereb_zones(egrid, canton)
    if oereb_result and oereb_result.get("zones"):
        zones = oereb_result["zones"]
        oereb_data = {
            "egrid": egrid,
            "canton": canton,
            "municipality": oereb_result.get("municipality"),
            "primary_zone": zones[0]["legend_text"] if zones else None,
            "zones": zones,
        }
        oereb_path = output_path.with_name(f"{egrid}_oereb.json")
        oereb_path.write_text(json.dumps(oereb_data, ensure_ascii=False, indent=2), encoding="utf-8")
        oereb_json_path = str(oereb_path)
        print(f"OEREB-Zonen gespeichert ({len(zones)} Zonen): {oereb_path}")
    else:
        print("OEREB-Zonen konnten nicht geladen werden (wird im Add-on nachgeholt).")

    return {
        "canton": canton,
        "egrid": egrid,
        "source_gpkg": str(gpkg_path),
        "parcel_gpkg": str(output_path),
        "parcel_layer": parcel_match.layer_name,
        "written_layers": written_layers,
        "oereb_json": oereb_json_path,
    }


def main() -> int:
    ensure_directories()
    print("AV GeoPackage -> E-GRID Datenbank Export")
    print("--------------------------------")
    args = parse_args(sys.argv[1:])

    try:
        canton, egrid = resolve_user_inputs(args)
        result = run_export(canton, egrid)
        if args.json_output:
            print(f"RESULT_JSON={json.dumps(result, ensure_ascii=False)}")
        return 0
    except KeyboardInterrupt:
        print("\nAbgebrochen.")
        return 130
    except UserFacingError as exc:
        print(str(exc), file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
