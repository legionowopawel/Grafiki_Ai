#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
aktualizacja_html.py  —  program z oknem do aktualizacji galerii.

Co robi (kolejno):
  1. Skanuje foldery PUBLICZNE (domyślnie images, pdf, video, audio) — widoczne dla wszystkich.
     Rozpoznaje typ pliku (po rozszerzeniu, a bez rozszerzenia — po zawartości) i dostosowuje go
     do przeglądarki/telefonu:
       obrazy : jpg jpeg jfif jif png webp gif avif bmp svg  (+ tif, heic, ico… → zamiana na JPEG)
       filmy  : mp4 m4v webm ogv                             (+ avi, mpg, mov, mkv, wmv… → mp4)
       audio  : mp3 m4a aac wav ogg opus flac                (+ wma, aiff… → mp3)
       pdf    : pdf
     Konwersja filmów/audio wymaga programu ffmpeg (patrz niżej). Przekonwertowane kopie
     trafiają do folderu converted/, oryginały zostają nietknięte.
  2. (pytając Cię o zgodę) szyfruje PRYWATNE pliki z haslo_git_ignore/<podfolder>/
     hasłem (AES-256-GCM) do folderu haslo/ — tylko ta zaszyfrowana wersja idzie na GitHub.
     Prywatne mogą być obrazy (dowolny obsługiwany format) i PDF.
  3. Zbiera strony HTML z folderu html/ (tytuł i opis bierze z <title> i meta description),
     żeby strona główna mogła je pokazać jako dołączone podstrony.
  4. Zapisuje galeria.json i wstawia te same dane do index.html (między znacznikami
     DATA_START / DATA_END).

Uruchomienie z oknem:   python aktualizacja_html.py
Uruchomienie bez okna:  python aktualizacja_html.py --cli
Wymaga:                 pip install -r requirements.txt   (pillow, cryptography)
Opcjonalnie:            pip install pillow-heif           (zdjęcia .heic z iPhone'a)
                        ffmpeg w PATH                     (konwersja i miniatury filmów, konwersja audio;
                                                           Windows: winget install ffmpeg)
"""

import base64
import codecs
import hashlib
import io
import json
import mimetypes
import os
import queue
import re
import shutil
import subprocess
import sys
import threading
from datetime import datetime
from html.parser import HTMLParser
from pathlib import Path

BASE = Path(__file__).resolve().parent
THUMB_DIR = BASE / "thumbs"
CONVERTED_DIR = BASE / "converted"           # kopie przekonwertowane do formatów przyjaznych przeglądarce
PAGES_DIR = BASE / "html"                    # gotowe strony HTML dołączane do strony głównej
JSON_FILE = BASE / "galeria.json"
HTML_FILE = BASE / "index.html"
CONFIG_FILE = BASE / "aktualizacja_config.json"
GITIGNORE_FILE = BASE / ".gitignore"

PRIVATE_DIR = BASE / "haslo_git_ignore"      # oryginały — NIGDY na GitHub
VAULT_DIR = BASE / "haslo"                   # zaszyfrowane — idzie na GitHub
VAULT_META = VAULT_DIR / "vault.json"
STATE_FILE = PRIVATE_DIR / ".stan_szyfrowania.json"
PBKDF2_ITER = 600_000

DEFAULT_FOLDERS = ["images", "pdf", "video", "audio"]
CONFIG_VERSION = 2                           # 2 = doszły domyślne foldery video i audio
THUMB_SIZE = 640  # najdłuższy bok miniatury w px
TOTAL_STEPS = 4
GITHUB_WARN_MB = 50                          # GitHub ostrzega powyżej 50 MB i odrzuca powyżej 100 MB
GITHUB_MAX_MB = 100

# --- obsługiwane formaty -----------------------------------------------------------------
# "native"      — przeglądarka pokazuje to sama, plik idzie na stronę bez zmian
# "jpeg_alias"  — to po prostu JPEG pod inną nazwą (jfif, jif…) → kopia .jpg bez utraty jakości
# "convert"     — przeglądarka tego nie zna → konwersja do JPEG / mp4 / mp3
IMG_NATIVE = {".jpg", ".jpeg", ".png", ".webp", ".gif", ".avif", ".bmp", ".svg"}
IMG_JPEG_ALIAS = {".jfif", ".jif", ".jpe", ".pjpeg", ".pjp"}
IMG_CONVERT = {".tif", ".tiff", ".heic", ".heif", ".ico", ".tga", ".jp2"}
VIDEO_NATIVE = {".mp4", ".m4v", ".webm", ".ogv"}
VIDEO_CONVERT = {".mov", ".avi", ".mpg", ".mpeg", ".mpe", ".mkv", ".wmv", ".flv", ".3gp", ".3g2",
                 ".mts", ".m2ts", ".vob", ".divx", ".asf"}
AUDIO_NATIVE = {".mp3", ".m4a", ".aac", ".wav", ".ogg", ".oga", ".opus", ".flac"}
AUDIO_CONVERT = {".wma", ".aif", ".aiff", ".amr", ".mka", ".ape", ".mp2", ".ac3", ".wv"}
PDF_EXT = {".pdf"}
PAGE_EXT = {".html", ".htm"}

WEB_VIDEO_CODECS = {"h264", "vp8", "vp9", "av1", "theora"}     # tyle zagra każdy telefon/przeglądarka
WEB_IMAGE_FORMATS = {"JPEG", "MPO", "PNG", "GIF", "WEBP", "BMP", "AVIF"}   # co Pillow zgłasza dla natywnych

MIME = {
    ".jpg": "image/jpeg", ".jpeg": "image/jpeg", ".png": "image/png", ".webp": "image/webp",
    ".gif": "image/gif", ".avif": "image/avif", ".bmp": "image/bmp", ".svg": "image/svg+xml",
    ".pdf": "application/pdf",
    ".mp4": "video/mp4", ".m4v": "video/mp4", ".webm": "video/webm", ".ogv": "video/ogg",
    ".mp3": "audio/mpeg", ".m4a": "audio/mp4", ".aac": "audio/aac", ".wav": "audio/wav",
    ".ogg": "audio/ogg", ".oga": "audio/ogg", ".opus": "audio/ogg", ".flac": "audio/flac",
}

EXT_TABLE = {}                               # rozszerzenie → (rodzaj, akcja)
for _exts, _kind, _action in (
        (IMG_NATIVE, "image", "native"), (IMG_JPEG_ALIAS, "image", "jpeg_alias"),
        (IMG_CONVERT, "image", "convert"), (VIDEO_NATIVE, "video", "native"),
        (VIDEO_CONVERT, "video", "convert"), (AUDIO_NATIVE, "audio", "native"),
        (AUDIO_CONVERT, "audio", "convert"), (PDF_EXT, "pdf", "native")):
    for _e in _exts:
        EXT_TABLE[_e] = (_kind, _action)

KINDS = ("image", "video", "audio", "pdf")
KIND_KEY = {"image": "images", "video": "video", "audio": "audio", "pdf": "pdf"}
KIND_NAME = {"image": "Obrazy", "video": "Filmy", "audio": "Audio", "pdf": "PDF"}

try:
    from PIL import Image, ImageOps
except ImportError:
    Image = None

HEIF_OK = False
try:
    import pillow_heif
    pillow_heif.register_heif_opener()
    HEIF_OK = True
except Exception:
    pass

try:
    from cryptography.hazmat.primitives import hashes
    from cryptography.hazmat.primitives.ciphers.aead import AESGCM
    from cryptography.hazmat.primitives.kdf.pbkdf2 import PBKDF2HMAC
    CRYPTO_OK = True
except ImportError:
    CRYPTO_OK = False


# ----------------------------------------------------------------- pomocnicze
def natural_key(text):
    """Sortowanie naturalne: strona2 < strona10."""
    return [int(t) if t.isdigit() else t.lower() for t in re.split(r"(\d+)", text)]


def pretty_label(rel_folder):
    if not rel_folder:
        return "Inne"
    parts = [p.replace("_", " ").replace("-", " ").strip() for p in rel_folder.split("/")]
    text = " / ".join(parts)
    return text[:1].upper() + text[1:]


def pretty_title(filename):
    stem = Path(filename).stem.replace("_", " ").replace("-", " ").strip()
    return stem or filename


def step(log, n, title, desc):
    log(f"### Krok {n}/{TOTAL_STEPS}: {title}")
    log(desc)


def thumb_image(src: Path):
    """Zwraca miniaturę jako obraz RGB (Pillow)."""
    with Image.open(src) as im:
        im = ImageOps.exif_transpose(im)
        im.thumbnail((THUMB_SIZE, THUMB_SIZE))
        if im.mode in ("RGBA", "LA", "P"):
            im = im.convert("RGBA")
            bg = Image.new("RGB", im.size, (255, 255, 255))
            bg.paste(im, mask=im.split()[3])
            return bg
        return im.convert("RGB")


def jpeg_bytes(src: Path, quality=90) -> bytes:
    """Cały obraz (bez zmniejszania) jako JPEG — dla formatów, których przeglądarka nie zna."""
    if Image is None:
        raise RuntimeError("do zamiany formatu obrazów potrzebny jest Pillow (pip install pillow)")
    with Image.open(src) as im:
        im = ImageOps.exif_transpose(im)
        if im.mode in ("RGBA", "LA", "P"):
            im = im.convert("RGBA")
            bg = Image.new("RGB", im.size, (255, 255, 255))
            bg.paste(im, mask=im.split()[3])
            im = bg
        else:
            im = im.convert("RGB")
        buf = io.BytesIO()
        im.save(buf, "JPEG", quality=quality, optimize=True)
        return buf.getvalue()


def make_thumb(src: Path, log):
    """Publiczna miniatura na dysku. Zwraca ścieżkę względną (z /) albo None."""
    if Image is None:
        return None
    rel = src.relative_to(BASE)
    out = THUMB_DIR / rel.parent / (rel.name + ".jpg")
    try:
        if not (out.exists() and out.stat().st_mtime >= src.stat().st_mtime):
            out.parent.mkdir(parents=True, exist_ok=True)
            thumb_image(src).save(out, "JPEG", quality=80, optimize=True)
        return out.relative_to(BASE).as_posix()
    except Exception as exc:  # uszkodzony plik itp. — nie przerywamy całości
        log(f"! miniatura nieudana dla {src.name}: {exc}")
        return None


def thumb_ar(thumb_rel):
    """Proporcje miniatury (szerokość / wysokość) — strona dzięki temu nie obcina miniatur."""
    try:
        with Image.open(BASE / thumb_rel) as t:
            return round(t.width / t.height, 4)
    except Exception:
        return None


# ------------------------------------------------- rozpoznawanie formatu i konwersja
_warned = set()


def warn_once(log, key, msg):
    if key not in _warned:
        _warned.add(key)
        log(msg)


def sniff_ext(path: Path):
    """Rozpoznaje typ po zawartości (pierwsze bajty). Zwraca rozszerzenie albo None."""
    try:
        with open(path, "rb") as f:
            h = f.read(32)
    except OSError:
        return None
    if h[:3] == b"\xff\xd8\xff":
        return ".jpg"
    if h[:8] == b"\x89PNG\r\n\x1a\n":
        return ".png"
    if h[:6] in (b"GIF87a", b"GIF89a"):
        return ".gif"
    if h[:4] == b"RIFF" and h[8:12] == b"WEBP":
        return ".webp"
    if h[:4] == b"RIFF" and h[8:12] == b"AVI ":
        return ".avi"
    if h[:4] == b"RIFF" and h[8:12] == b"WAVE":
        return ".wav"
    if h[:4] == b"%PDF":
        return ".pdf"
    if h[:2] == b"BM":
        return ".bmp"
    if h[:4] in (b"II*\x00", b"MM\x00*"):
        return ".tif"
    if h[4:8] == b"ftyp":
        brand = h[8:12]
        if brand in (b"heic", b"heix", b"heim", b"heis", b"hevc", b"hevx", b"mif1", b"msf1"):
            return ".heic"
        if brand in (b"avif", b"avis"):
            return ".avif"
        if brand == b"qt  ":
            return ".mov"
        if brand in (b"M4A ", b"M4B "):
            return ".m4a"
        if brand[:3] == b"3gp":
            return ".3gp"
        return ".mp4"
    if h[:4] == b"OggS":
        return ".ogg"
    if h[:4] == b"fLaC":
        return ".flac"
    if h[:3] == b"ID3":
        return ".mp3"
    if h[:4] == b"\x1a\x45\xdf\xa3":
        return ".mkv"
    if h[:4] in (b"\x00\x00\x01\xba", b"\x00\x00\x01\xb3"):
        return ".mpg"
    return None


def classify(path: Path):
    """Rozpoznaje plik. Zwraca (rodzaj, akcja, rozszerzenie) albo None, jeśli to nie nasz format.
    Po rozszerzeniu; plik BEZ rozszerzenia — po zawartości (wtedy powstaje kopia z poprawną nazwą)."""
    ext = path.suffix.lower()
    if ext in EXT_TABLE:
        kind, action = EXT_TABLE[ext]
        return kind, action, ext
    if ext == "":
        real = sniff_ext(path)
        if real in EXT_TABLE:
            kind, action = EXT_TABLE[real]
            return kind, ("rename" if action == "native" else action), real
    return None


def is_jpeg(path: Path) -> bool:
    try:
        with open(path, "rb") as f:
            return f.read(3) == b"\xff\xd8\xff"
    except OSError:
        return False


def image_needs_reencode(path: Path) -> bool:
    """Rozszerzenie mówi np. „jpg”, a w środku jest HEIC/TIFF (iPhone potrafi tak zapisać)?"""
    if Image is None:
        return False
    try:
        with Image.open(path) as im:
            return (im.format or "") not in WEB_IMAGE_FORMATS
    except Exception:
        return False


def converted_path(src: Path, new_ext: str) -> Path:
    rel = src.relative_to(BASE)
    return CONVERTED_DIR / rel.parent / (rel.name + new_ext)


def is_fresh(out: Path, src: Path) -> bool:
    try:
        return out.stat().st_size > 0 and out.stat().st_mtime >= src.stat().st_mtime
    except OSError:
        return False


def relp(path: Path) -> str:
    return path.relative_to(BASE).as_posix()


def check_size(path: Path, log):
    try:
        mb = path.stat().st_size / 1_048_576
    except OSError:
        return
    if mb > GITHUB_MAX_MB:
        log(f"! {relp(path)} ma {mb:.0f} MB — GitHub odrzuci taki plik (limit {GITHUB_MAX_MB} MB). "
            "Zmniejsz go albo użyj Git LFS.")
    elif mb > GITHUB_WARN_MB:
        log(f"! {relp(path)} ma {mb:.0f} MB — GitHub ostrzega przy plikach powyżej {GITHUB_WARN_MB} MB "
            f"(twardy limit: {GITHUB_MAX_MB} MB).")


def run_tool(cmd):
    kw = {}
    if sys.platform.startswith("win"):
        kw["creationflags"] = 0x08000000  # bez migającego okna konsoli
    return subprocess.run(cmd, stdin=subprocess.DEVNULL, capture_output=True, text=True,
                          encoding="utf-8", errors="replace", **kw)


def no_ffmpeg(log):
    warn_once(log, "ffmpeg",
              "! Brak programu ffmpeg (ffmpeg.org; Windows: winget install ffmpeg). Bez niego filmy nie dostaną "
              "miniatur, a avi / mpg / mov / mkv / wma itp. nie zostaną przekonwertowane.")


def probe_codecs(path: Path):
    """Kodeki pliku wg ffprobe, np. {'video': 'h264', 'audio': 'aac'}; pusty słownik, gdy brak ffprobe."""
    exe = shutil.which("ffprobe")
    if not exe:
        return {}
    try:
        r = run_tool([exe, "-v", "error", "-show_entries", "stream=codec_type,codec_name",
                      "-of", "json", str(path)])
        found = {}
        for st in json.loads(r.stdout or "{}").get("streams", []):
            found.setdefault(st.get("codec_type"), st.get("codec_name"))
        return found
    except Exception:
        return {}


def ffmpeg_convert(kind, src: Path, out: Path, log):
    """Film → mp4 (H.264 + AAC, gotowy do strumieniowania), audio → mp3. True, gdy się udało."""
    exe = shutil.which("ffmpeg")
    if not exe:
        return False
    out.parent.mkdir(parents=True, exist_ok=True)
    tmp = out.with_name("~" + out.name)
    if kind == "video":
        args = ["-map", "0:v:0", "-map", "0:a:0?", "-c:v", "libx264", "-preset", "veryfast", "-crf", "23",
                "-pix_fmt", "yuv420p", "-vf", "scale=trunc(iw/2)*2:trunc(ih/2)*2",
                "-c:a", "aac", "-b:a", "128k", "-movflags", "+faststart"]
    else:
        args = ["-vn", "-map", "0:a:0", "-c:a", "libmp3lame", "-q:a", "2"]
    try:
        r = run_tool([exe, "-y", "-v", "error", "-i", str(src), *args, str(tmp)])
        if r.returncode != 0 or not tmp.exists() or tmp.stat().st_size == 0:
            log(f"! konwersja nieudana dla {src.name}: {(r.stderr or '').strip()[-300:]}")
            return False
        os.replace(tmp, out)
        return True
    except Exception as exc:
        log(f"! konwersja nieudana dla {src.name}: {exc}")
        return False
    finally:
        try:
            tmp.unlink()
        except OSError:
            pass


def make_video_thumb(src: Path, log):
    """Klatka z filmu jako miniatura (thumbs/…). Zwraca ścieżkę względną albo None."""
    exe = shutil.which("ffmpeg")
    if not exe:
        no_ffmpeg(log)
        return None
    out = THUMB_DIR / src.relative_to(BASE).parent / (src.name + ".jpg")
    if is_fresh(out, src):
        return relp(out)
    out.parent.mkdir(parents=True, exist_ok=True)
    for ss in ("1", "0"):  # film krótszy niż sekunda → klatka z początku
        try:
            run_tool([exe, "-y", "-v", "error", "-ss", ss, "-i", str(src), "-frames:v", "1",
                      "-vf", f"scale='min({THUMB_SIZE},iw)':-2", "-q:v", "4", str(out)])
        except Exception as exc:
            log(f"! miniatura filmu nieudana dla {src.name}: {exc}")
            return None
        if out.exists() and out.stat().st_size > 0:
            return relp(out)
    log(f"! miniatura filmu nieudana dla {src.name}")
    return None


def prepare_image(src: Path, action, ext, log, used):
    """Zwraca (plik dla strony, mime) albo None."""
    if action == "native" and ext != ".svg" and image_needs_reencode(src):
        log(f"  {src.name}: w środku inny format niż sugeruje rozszerzenie — zamieniam na JPEG")
        action = "convert"
    if action == "native":
        return src, MIME[ext]
    if action == "jpeg_alias" and not is_jpeg(src):
        action = "convert"
    if action in ("jpeg_alias", "rename"):
        new_ext = ".jpg" if action == "jpeg_alias" else ext
        out = converted_path(src, new_ext)
        if not is_fresh(out, src):
            out.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(src, out)
            log(f"  kopia z poprawnym rozszerzeniem: {src.name} → {new_ext}")
        used.add(out)
        return out, MIME[new_ext]
    # action == "convert": zamiana na JPEG
    out = converted_path(src, ".jpg")
    if not is_fresh(out, src):
        if ext in (".heic", ".heif") and not HEIF_OK:
            warn_once(log, "heif", "! Pomijam pliki .heic/.heif — zainstaluj obsługę: pip install pillow-heif")
            return None
        out.parent.mkdir(parents=True, exist_ok=True)
        out.write_bytes(jpeg_bytes(src))
        log(f"  zamieniono na JPEG: {src.name}")
    used.add(out)
    return out, "image/jpeg"


def prepare_av(kind, src: Path, action, ext, log, used):
    """Film lub audio. Zwraca (plik dla strony, mime, czy_zagra_w_przeglądarce)."""
    target = ".mp4" if kind == "video" else ".mp3"
    fallback_native = None
    if action == "native":
        fallback_native = (src, MIME[ext], True)
        if kind == "video":
            vcodec = probe_codecs(src).get("video")
            if vcodec and vcodec not in WEB_VIDEO_CODECS:
                if not is_fresh(converted_path(src, target), src):
                    log(f"  {src.name}: kodek {vcodec} nie zagra wszędzie — konwertuję do H.264")
                action = "convert"
        if action == "native":
            return fallback_native
    if action == "rename":
        out = converted_path(src, ext)
        if not is_fresh(out, src):
            out.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(src, out)
            log(f"  kopia z poprawnym rozszerzeniem: {src.name} → {ext}")
        used.add(out)
        return out, MIME[ext], True

    out = converted_path(src, target)
    if is_fresh(out, src):
        used.add(out)
        return out, MIME[target], True
    guessed = mimetypes.guess_type(src.name)[0] or "application/octet-stream"
    if not shutil.which("ffmpeg"):
        no_ffmpeg(log)
        return fallback_native or (src, guessed, False)
    log(f"  konwertuję {src.name} → {target[1:]} (przy dużych plikach to może potrwać)…")
    if ffmpeg_convert(kind, src, out, log):
        used.add(out)
        return out, MIME[target], True
    return fallback_native or (src, guessed, False)


def process_file(full: Path, kind, action, ext, log, used):
    """Jeden plik publiczny → element do galeria.json (albo None, gdy się nie da)."""
    check_size(full, log)
    title = pretty_title(full.name)

    if kind == "pdf":
        web = full
        if action == "rename":  # PDF bez rozszerzenia → kopia z .pdf
            web = converted_path(full, ".pdf")
            if not is_fresh(web, full):
                web.parent.mkdir(parents=True, exist_ok=True)
                shutil.copy2(full, web)
            used.add(web)
        return {"kind": "pdf", "src": relp(web), "title": title}

    if kind == "image":
        res = prepare_image(full, action, ext, log, used)
        if not res:
            return None
        web, mime = res
        if web != full:
            check_size(web, log)
        item = {"kind": "image", "src": relp(web), "title": title, "mime": mime}
        if web.suffix.lower() != ".svg":
            thumb = make_thumb(web, log)
            if thumb:
                item["thumb"] = thumb
                ar = thumb_ar(thumb)
                if ar:
                    item["ar"] = ar
        return item

    web, mime, playable = prepare_av(kind, full, action, ext, log, used)
    if web != full:
        check_size(web, log)
    item = {"kind": kind, "src": relp(web), "title": title, "mime": mime}
    if not playable:
        item["playable"] = False  # strona może pokazać tylko link „pobierz”
        log(f"! {full.name}: nie udało się przygotować wersji dla przeglądarki — na stronie będzie tylko link do pobrania.")
    if kind == "video":
        thumb = make_video_thumb(web if playable else full, log)
        if thumb:
            item["thumb"] = thumb
            ar = thumb_ar(thumb)
            if ar:
                item["ar"] = ar
    return item


# ------------------------------------------------------------ foldery publiczne
DEFAULT_ROOTS = tuple(BASE / f for f in DEFAULT_FOLDERS)


def scan(root: Path, log, used):
    """Jeden przebieg po folderze. Zwraca {rodzaj: [grupy]}, grupa = {name, label, items}."""
    result = {k: [] for k in KINDS}
    if not root.is_dir():
        if root in DEFAULT_ROOTS:
            log(f"  (brak folderu {root.name} — pomijam)")
        else:
            log(f"! Brak folderu: {root.name}")
        return result

    # foldery domyślne (images, pdf, video, audio) nie dokładają swojej nazwy do nazw grup;
    # foldery dodane przez użytkownika — tak
    prefix = "" if root in DEFAULT_ROOTS else root.relative_to(BASE).as_posix()
    skip_dirs = {THUMB_DIR, CONVERTED_DIR}

    for folder, dirs, files in os.walk(root):
        dirs[:] = sorted(
            (d for d in dirs if not d.startswith(".") and (Path(folder) / d) not in skip_dirs),
            key=natural_key,
        )
        folder_path = Path(folder)
        rel = folder_path.relative_to(root).as_posix()
        rel = "" if rel == "." else rel
        name = "/".join(p for p in (prefix, rel) if p)

        per_kind = {k: [] for k in KINDS}
        for fname in sorted(files, key=natural_key):
            if fname.startswith("."):
                continue
            full = folder_path / fname
            info = classify(full)
            if not info:
                continue
            kind, action, ext = info
            try:
                item = process_file(full, kind, action, ext, log, used)
            except Exception as exc:  # jeden zły plik nie zatrzymuje całości
                log(f"! pomijam {fname}: {exc}")
                continue
            if item:
                per_kind[kind].append(item)

        for k in KINDS:
            if per_kind[k]:
                result[k].append({"name": name, "label": pretty_label(name), "items": per_kind[k]})
    return result


def merge_groups(groups):
    """Łączy grupy o tej samej nazwie i sortuje (luzem leżące pliki na końcu)."""
    merged = {}
    for g in groups:
        if g["name"] in merged:
            merged[g["name"]]["items"].extend(g["items"])
        else:
            merged[g["name"]] = g
    return sorted(merged.values(), key=lambda g: (g["name"] == "", natural_key(g["name"])))


def normalize_roots(folders, log):
    roots = []
    for f in folders:
        p = Path(f)
        p = (p if p.is_absolute() else BASE / p).resolve()
        if p == BASE or BASE not in p.parents:
            log(f"! Pomijam „{f}”: folder musi leżeć wewnątrz folderu projektu.")
            continue
        if p in (PRIVATE_DIR, VAULT_DIR) or PRIVATE_DIR in p.parents or VAULT_DIR in p.parents:
            log(f"! Pomijam „{f}”: to folder prywatny/zaszyfrowany, nie może być publiczny.")
            continue
        if p in (THUMB_DIR, CONVERTED_DIR) or THUMB_DIR in p.parents or CONVERTED_DIR in p.parents:
            log(f"! Pomijam „{f}”: to folder techniczny (miniatury / konwersje), program tworzy go sam.")
            continue
        if p not in roots:
            roots.append(p)
    # jeśli wybrano folder i jego podfolder, liczy się tylko folder nadrzędny
    return [r for r in roots if not any(o != r and o in r.parents for o in roots)]


def prune_converted(used, log):
    """Usuwa z converted/ kopie, których oryginałów już nie ma na stronie."""
    if not CONVERTED_DIR.is_dir():
        return
    removed = 0
    for p in list(CONVERTED_DIR.rglob("*")):
        if p.is_file() and p not in used:
            p.unlink()
            removed += 1
    for d in sorted((d for d in CONVERTED_DIR.rglob("*") if d.is_dir()), reverse=True):
        try:
            d.rmdir()
        except OSError:
            pass
    if removed:
        log(f"Usunięto {removed} nieaktualnych kopii z converted/.")


# ------------------------------------------------- strony HTML dołączane do strony głównej
class _MetaParser(HTMLParser):
    """Wyciąga <title> i <meta name="description"> z nagłówka strony."""

    def __init__(self):
        super().__init__(convert_charrefs=True)
        self.title = ""
        self.desc = ""
        self._in_title = False

    def handle_starttag(self, tag, attrs):
        if tag == "title":
            self._in_title = True
        elif tag == "meta":
            a = {k.lower(): (v or "") for k, v in attrs}
            if a.get("name", "").lower() == "description" and not self.desc:
                self.desc = a.get("content", "")

    def handle_endtag(self, tag):
        if tag == "title":
            self._in_title = False

    def handle_data(self, data):
        if self._in_title:
            self.title += data


def html_meta(path: Path):
    """(tytuł, opis) strony HTML; puste napisy, gdy ich nie ma."""
    try:
        with open(path, "rb") as f:
            raw = f.read(65536)
    except OSError:
        return "", ""
    try:
        text = codecs.getincrementaldecoder("utf-8")().decode(raw, final=False)
    except UnicodeDecodeError:  # starsze strony po polsku bywają w Windows-1250
        text = raw.decode("cp1250", errors="replace")
    parser = _MetaParser()
    try:
        parser.feed(text)
    except Exception:
        pass
    return " ".join(parser.title.split()), " ".join(parser.desc.split())


def scan_pages(log):
    """Strony z folderu html/ → grupy [{name, label, items:[{kind:'page', src, title, desc?}]}]."""
    groups = []
    if not PAGES_DIR.is_dir():
        log("  (brak folderu html — pomijam strony HTML)")
        return groups
    log("Skanuję: html (strony do dołączenia)")
    for folder, dirs, files in os.walk(PAGES_DIR):
        dirs[:] = sorted((d for d in dirs if not d.startswith(".")), key=natural_key)
        folder_path = Path(folder)
        rel = folder_path.relative_to(PAGES_DIR).as_posix()
        rel = "" if rel == "." else rel
        items = []
        for fname in sorted(files, key=natural_key):
            if fname.startswith(".") or Path(fname).suffix.lower() not in PAGE_EXT:
                continue
            full = folder_path / fname
            title, desc = html_meta(full)
            item = {"kind": "page", "src": relp(full), "title": title or pretty_title(fname)}
            if desc:
                item["desc"] = desc
            items.append(item)
        if items:
            groups.append({"name": rel, "label": pretty_label(rel) if rel else "Strony", "items": items})
    return sorted(groups, key=lambda g: (g["name"] != "", natural_key(g["name"])))


# ------------------------------------------------------------------ szyfrowanie
def b64e(data: bytes) -> str:
    return base64.b64encode(data).decode("ascii")


def b64d(text: str) -> bytes:
    return base64.b64decode(text)


def derive_key(password: str, salt: bytes, iterations: int) -> bytes:
    kdf = PBKDF2HMAC(algorithm=hashes.SHA256(), length=32, salt=salt, iterations=iterations)
    return kdf.derive(password.encode("utf-8"))


def encrypt_bytes(key: bytes, data: bytes) -> bytes:
    """Format pliku: 12 bajtów IV + szyfrogram z tagiem (AES-256-GCM) — czyta to przeglądarka."""
    iv = os.urandom(12)
    return iv + AESGCM(key).encrypt(iv, data, None)


def decrypt_bytes(key: bytes, blob: bytes) -> bytes:
    return AESGCM(key).decrypt(blob[:12], blob[12:], None)


def load_vault_meta():
    try:
        return json.loads(VAULT_META.read_text(encoding="utf-8"))
    except Exception:
        return None


def password_mode(password: str) -> str:
    """'new' — seif jeszcze nie istnieje; 'same' — hasło pasuje; 'different' — inne niż poprzednio."""
    meta = load_vault_meta()
    if not meta:
        return "new"
    try:
        key = derive_key(password, b64d(meta["salt"]), int(meta["iterations"]))
        decrypt_bytes(key, b64d(meta["check"]))
        return "same"
    except Exception:
        return "different"


def list_private_files(skipped=None):
    """[(ścieżka względna w haslo_git_ignore (z /), Path)] — obrazy (każdy obsługiwany format) i PDF.
    Filmy i audio nie mogą być prywatne (przeglądarka musiałaby rozszyfrować cały plik w pamięci) —
    trafiają na listę `skipped`, jeśli ją podano."""
    out = []
    if not PRIVATE_DIR.is_dir():
        return out
    for folder, dirs, files in os.walk(PRIVATE_DIR):
        dirs[:] = sorted((d for d in dirs if not d.startswith(".")), key=natural_key)
        for fname in sorted(files, key=natural_key):
            if fname.startswith("."):
                continue
            p = Path(folder) / fname
            info = classify(p)
            if not info:
                continue
            if info[0] not in ("image", "pdf"):
                if skipped is not None:
                    skipped.append(p.relative_to(PRIVATE_DIR).as_posix())
                continue
            out.append((p.relative_to(PRIVATE_DIR).as_posix(), p))
    return out


def private_payload(path: Path, kind, action, ext):
    """(bajty do zaszyfrowania, mime) — obrazy w formatach nieznanych przeglądarce zamieniamy na JPEG."""
    if kind == "pdf":
        return path.read_bytes(), MIME[".pdf"]
    if action in ("native", "rename") and not (ext != ".svg" and image_needs_reencode(path)):
        return path.read_bytes(), MIME[ext]
    if action == "jpeg_alias" and is_jpeg(path):
        return path.read_bytes(), "image/jpeg"
    if ext in (".heic", ".heif") and not HEIF_OK:
        raise RuntimeError("pliki .heic wymagają: pip install pillow-heif")
    return jpeg_bytes(path), "image/jpeg"


def private_summary():
    files = list_private_files()
    dirs = {rel.rsplit("/", 1)[0] if "/" in rel else "" for rel, _ in files}
    return len(files), len(dirs)


def ensure_gitignore(log):
    """Pilnuje, by haslo_git_ignore/ było w .gitignore (oryginały nie mogą trafić na GitHub)."""
    try:
        text = GITIGNORE_FILE.read_text(encoding="utf-8") if GITIGNORE_FILE.exists() else ""
        lines = {l.strip().rstrip("/") for l in text.splitlines()}
        if "haslo_git_ignore" in lines or "/haslo_git_ignore" in lines:
            return
        with open(GITIGNORE_FILE, "a", encoding="utf-8") as f:
            if text and not text.endswith("\n"):
                f.write("\n")
            f.write("\n# Prywatne oryginały (nie wysyłać na GitHub!)\nhaslo_git_ignore/\n")
        log("Dopisałem haslo_git_ignore/ do .gitignore (oryginały nie trafią na GitHub).")
    except Exception as exc:
        log(f"! Nie udało się zaktualizować .gitignore: {exc}")


def load_state(salt_b64):
    try:
        st = json.loads(STATE_FILE.read_text(encoding="utf-8"))
        if st.get("salt") == salt_b64:
            return st
    except Exception:
        pass
    return {"salt": salt_b64, "files": {}}


def encrypt_private(password, new_salt, log):
    """Szyfruje pliki z haslo_git_ignore/ do haslo/. Zwraca meta (dla galeria.json) albo None."""
    if not CRYPTO_OK:
        raise RuntimeError("Brak biblioteki cryptography. Zainstaluj: pip install cryptography")

    skipped = []
    files = list_private_files(skipped)
    if skipped:
        log(f"! Pomijam {len(skipped)} plików audio/wideo w haslo_git_ignore/ — prywatne mogą być tylko obrazy i PDF "
            "(telefon musiałby rozszyfrować cały film w pamięci). Filmy i audio dodaj do folderów publicznych.")
    if not files:
        log("W haslo_git_ignore/ nie ma plików — usuwam zaszyfrowaną część ze strony.")
        if VAULT_DIR.is_dir():
            for p in VAULT_DIR.glob("*.enc"):
                p.unlink()
            if VAULT_META.exists():
                VAULT_META.unlink()
        return None

    ensure_gitignore(log)
    VAULT_DIR.mkdir(exist_ok=True)

    meta = load_vault_meta()
    fresh = meta is None or new_salt
    salt = os.urandom(16) if fresh else b64d(meta["salt"])
    iterations = PBKDF2_ITER if fresh else int(meta["iterations"])
    if new_salt and meta is not None:
        log("Zmiana hasła: wszystkie pliki zostaną zaszyfrowane od nowa.")

    log("Wyprowadzam klucz z hasła (celowo trwa chwilę — to chroni przed zgadywaniem)…")
    key = derive_key(password, salt, iterations)
    salt_b64 = b64e(salt)
    state = {"salt": salt_b64, "files": {}} if fresh else load_state(salt_b64)

    wanted, groups_map = set(), {}
    done = skipped = 0
    for rel, path in files:
        kind, action, ext = classify(path)
        fid = hashlib.sha256(salt + rel.encode("utf-8")).hexdigest()[:24]
        src_name, thumb_name = f"{fid}.enc", f"{fid}_t.enc"
        st = path.stat()
        prev = state["files"].get(rel)

        reuse = (
            prev and prev.get("size") == st.st_size and prev.get("mtime") == st.st_mtime_ns
            and (VAULT_DIR / src_name).exists()
            and (kind == "pdf" or ext == ".svg" or Image is None or (VAULT_DIR / thumb_name).exists())
        )
        if reuse:
            info = prev
            skipped += 1
        else:
            try:
                payload, mime = private_payload(path, kind, action, ext)
            except Exception as exc:
                log(f"! pomijam {rel}: {exc}")
                continue
            (VAULT_DIR / src_name).write_bytes(encrypt_bytes(key, payload))
            info = {"size": st.st_size, "mtime": st.st_mtime_ns, "mime": mime}
            if kind == "image" and ext != ".svg" and Image is not None:
                try:
                    im = thumb_image(path)
                    buf = io.BytesIO()
                    im.save(buf, "JPEG", quality=80, optimize=True)
                    (VAULT_DIR / thumb_name).write_bytes(encrypt_bytes(key, buf.getvalue()))
                    info["ar"] = round(im.width / im.height, 4)
                except Exception as exc:
                    log(f"! miniatura nieudana dla {path.name}: {exc}")
            log(f"  zaszyfrowano: {rel}")
            done += 1
        state["files"][rel] = info

        wanted.add(src_name)
        item = {"kind": kind, "src": f"haslo/{src_name}", "title": pretty_title(path.name),
                "mime": info.get("mime") or MIME.get(ext, "application/octet-stream")}
        if "ar" in info:
            item["thumb"] = f"haslo/{thumb_name}"
            item["ar"] = info["ar"]
            wanted.add(thumb_name)
        gname = rel.rsplit("/", 1)[0] if "/" in rel else ""
        groups_map.setdefault(gname, {"name": gname, "label": pretty_label(gname), "items": []})["items"].append(item)

    # usuń zaszyfrowane pliki, których oryginałów już nie ma
    removed = 0
    for p in VAULT_DIR.glob("*.enc"):
        if p.name not in wanted and p.name != "index.enc":
            p.unlink()
            removed += 1
    state["files"] = {k: v for k, v in state["files"].items() if k in {r for r, _ in files}}

    groups = sorted(groups_map.values(), key=lambda g: (g["name"] == "", natural_key(g["name"])))
    index_bytes = json.dumps({"groups": groups}, ensure_ascii=False, separators=(",", ":")).encode("utf-8")
    index_sha = hashlib.sha256(index_bytes).hexdigest()
    if not ((VAULT_DIR / "index.enc").exists() and state.get("index_sha") == index_sha):
        (VAULT_DIR / "index.enc").write_bytes(encrypt_bytes(key, index_bytes))
    state["index_sha"] = index_sha

    if fresh or not meta or not meta.get("check"):
        check = b64e(encrypt_bytes(key, b"galeria-ok"))
    else:
        check = meta["check"]
    new_meta = {"v": 1, "kdf": "PBKDF2-SHA256", "iterations": iterations, "salt": salt_b64,
                "check": check, "index": "haslo/index.enc"}
    VAULT_META.write_text(json.dumps(new_meta, indent=2), encoding="utf-8")
    STATE_FILE.write_text(json.dumps(state, indent=2), encoding="utf-8")

    log(f"Prywatne pliki: {len(files)} (nowe/zmienione: {done}, bez zmian: {skipped}, usunięte: {removed}).")
    log("Nazwy plików i folderów są ukryte — siedzą w zaszyfrowanym indeksie haslo/index.enc.")
    return new_meta


# ----------------------------------------------------------- HTML i główna akcja
def inject_into_html(payload, log):
    if not HTML_FILE.exists():
        log(f"! Nie znaleziono {HTML_FILE.name} — pomijam aktualizację HTML.")
        return False
    html = HTML_FILE.read_text(encoding="utf-8")
    pattern = re.compile(r"/\*DATA_START\*/.*?/\*DATA_END\*/", re.DOTALL)
    if not pattern.search(html):
        log("! W index.html brak znaczników /*DATA_START*/ ... /*DATA_END*/ — pomijam.")
        return False
    safe = payload.replace("</", "<\\/")  # bezpiecznie wewnątrz <script>
    new_html = pattern.sub(lambda m: f"/*DATA_START*/{safe}/*DATA_END*/", html, count=1)
    HTML_FILE.write_text(new_html, encoding="utf-8")
    return True


def run_update(folders, log=print, encrypt=False, password=None, new_salt=False):
    """Cała aktualizacja, krok po kroku, z komentarzem w logu."""
    log(f"Folder projektu: {BASE}")
    _warned.clear()
    if Image is None:
        log("! Pillow niezainstalowane — bez miniatur i bez zamiany formatów obrazów (pip install pillow).")

    # --- 1 ---
    step(log, 1, "Foldery publiczne i strony HTML",
         "Przeglądam wybrane foldery i zbieram obrazy, filmy, pliki audio i PDF-y. Rozpoznaję format każdego pliku;\n"
         "jeśli przeglądarka lub telefon by go nie odtworzył (np. avi, mpg, mov, heic, wma), robię kopię w folderze\n"
         "converted/ w formacie uniwersalnym (JPEG / mp4 / mp3). Do obrazów i filmów robię małą miniaturę (thumbs/).\n"
         "Na koniec zbieram strony HTML z folderu html/, żeby strona główna mogła je pokazać.")
    roots = normalize_roots(folders, log)
    found = {k: [] for k in KINDS}
    used = set()  # pliki w converted/, które są nadal potrzebne
    for root in roots:
        log(f"Skanuję: {root.relative_to(BASE).as_posix()}")
        got = scan(root, log, used)
        for k in KINDS:
            found[k] += got[k]
    pages = scan_pages(log)
    prune_converted(used, log)

    # --- 2 ---
    if encrypt:
        step(log, 2, "Szyfrowanie prywatnych plików",
             "Biorę oryginały z haslo_git_ignore/ (ten folder NIE idzie na GitHub) i szyfruję je Twoim hasłem\n"
             "(AES-256). Zaszyfrowane kopie trafiają do folderu haslo/ — tylko one zostaną opublikowane.\n"
             "Pliki bez zmian pomijam, żeby nie zaśmiecać historii gita.")
        vault = encrypt_private(password, new_salt, log)
    else:
        step(log, 2, "Szyfrowanie prywatnych plików — pominięte",
             "Nie szyfruję niczego w tym uruchomieniu. Prywatna część strony zostaje taka, jak była.")
        vault = load_vault_meta()

    data = {
        "generated": datetime.now().isoformat(timespec="seconds"),
        "images": merge_groups(found["image"]),
        "pdf": merge_groups(found["pdf"]),
        "video": merge_groups(found["video"]),
        "audio": merge_groups(found["audio"]),
        "pages": pages,
        "vault": vault,
    }

    # --- 3 ---
    step(log, 3, "Zapis galeria.json",
         "Zapisuję listę wszystkich publicznych plików i stron (oraz dane potrzebne do odblokowania prywatnych) w galeria.json.")
    JSON_FILE.write_text(json.dumps(data, ensure_ascii=False, indent=2), encoding="utf-8")

    # --- 4 ---
    step(log, 4, "Aktualizacja index.html",
         "Wstawiam te same dane do index.html, dzięki czemu strona działa od razu, bez dodatkowego pobierania.")
    html_ok = inject_into_html(json.dumps(data, ensure_ascii=False, separators=(",", ":")), log)

    log("### Podsumowanie")
    counts = {}
    for kind in KINDS:
        key = KIND_KEY[kind]
        counts[key] = sum(len(g["items"]) for g in data[key])
        log(f"{KIND_NAME[kind]}: {counts[key]} w {len(data[key])} folderach")
        for g in data[key]:
            log(f"   {g['label']}: {len(g['items'])}")
    counts["pages"] = sum(len(g["items"]) for g in pages)
    log(f"Strony HTML: {counts['pages']}")
    for g in pages:
        log(f"   {g['label']}: {len(g['items'])}")
    log("Część prywatna: " + ("aktywna (zakładka „Prywatne”)" if vault else "brak"))
    if used:
        log(f"! W converted/ jest {len(used)} kopii w formatach przyjaznych przeglądarce. Oryginały (np. avi, mov, heic) "
            "zostają w swoich folderach i git add . wyśle je razem z kopiami — jeśli nie chcesz, przenieś oryginały "
            "poza folder projektu albo dopisz je do .gitignore.")
    log(f"Zapisano {JSON_FILE.name}" + (f" i {HTML_FILE.name}." if html_ok else "."))
    return {**counts, "html_ok": html_ok}


# --------------------------------------------------------------- konfiguracja
def load_config():
    try:
        data = json.loads(CONFIG_FILE.read_text(encoding="utf-8"))
        folders = [str(f) for f in data.get("folders", [])]
        if folders:
            if int(data.get("v", 1)) < CONFIG_VERSION:  # stary plik konfiguracji — dokładam nowe domyślne foldery
                folders += [f for f in DEFAULT_FOLDERS if f not in folders]
            return folders
    except Exception:
        pass
    return list(DEFAULT_FOLDERS)


def save_config(folders):
    try:
        CONFIG_FILE.write_text(json.dumps({"v": CONFIG_VERSION, "folders": folders}, ensure_ascii=False, indent=2), encoding="utf-8")
    except Exception:
        pass


# ------------------------------------------------------------ podgląd lokalny
_server = None


def start_preview():
    """Uruchamia lokalny serwer (tylko ten komputer) i otwiera stronę w przeglądarce."""
    global _server
    import functools
    import http.server
    import webbrowser

    class Handler(http.server.SimpleHTTPRequestHandler):
        def end_headers(self):
            self.send_header("Cache-Control", "no-store")
            super().end_headers()

        def log_message(self, *args):
            pass

    if _server is None:
        for port in range(8000, 8011):
            try:
                _server = http.server.ThreadingHTTPServer(
                    ("127.0.0.1", port), functools.partial(Handler, directory=str(BASE)))
                break
            except OSError:
                continue
        if _server is None:
            raise RuntimeError("Nie udało się uruchomić lokalnego serwera (porty 8000–8010 zajęte).")
        threading.Thread(target=_server.serve_forever, daemon=True).start()
    url = f"http://127.0.0.1:{_server.server_address[1]}/"
    webbrowser.open(url)
    return url


def open_folder(path: Path):
    path.mkdir(exist_ok=True)
    try:
        if sys.platform.startswith("win"):
            os.startfile(str(path))  # type: ignore[attr-defined]
        elif sys.platform == "darwin":
            os.system(f'open "{path}"')
        else:
            os.system(f'xdg-open "{path}"')
    except Exception:
        pass


# ------------------------------------------------------------------- interfejs
INTRO = (
    "Ten program przygotowuje galerię do wysłania na GitHub. Robi to w 4 krokach: (1) zbiera obrazy, filmy, audio i PDF "
    "z folderów publicznych (rozpoznaje format i w razie potrzeby zamienia go na taki, który zagra w telefonie) oraz "
    "strony z folderu html, (2) — jeśli się zgodzisz — szyfruje prywatne pliki hasłem, (3) zapisuje galeria.json, "
    "(4) aktualizuje index.html. Po każdym kliknięciu zielonego przycisku zobaczysz na dole, co dokładnie się dzieje."
)

PRIVATE_INFO = (
    "Oryginały prywatnych grafik i PDF trzymaj w folderze haslo_git_ignore/<podfolder>/. Ten folder jest w .gitignore, "
    "więc nigdy nie trafia na GitHub. Program zaszyfruje je do folderu haslo/ — tylko ta wersja jest publikowana. "
    "Na stronie zobaczysz je w zakładce „Prywatne” po wpisaniu hasła."
)

PASSWORD_INFO = (
    "Hasło nie jest nigdzie zapisywane — wpisuj to samo przy każdej aktualizacji. Użyj długiego (np. 4 losowe słowa): "
    "zaszyfrowane pliki są publiczne, więc ktoś mógłby próbować zgadywać hasło."
)


def launch_gui():
    import tkinter as tk
    from tkinter import filedialog, messagebox, scrolledtext, ttk

    win = tk.Tk()
    win.title("Aktualizacja galerii")
    win.geometry("780x860")
    win.minsize(640, 640)

    folders = load_config()
    PRIVATE_DIR.mkdir(exist_ok=True)

    frm = ttk.Frame(win, padding=12)
    frm.pack(fill="both", expand=True)

    ttk.Label(frm, text=INTRO, wraplength=730, justify="left").pack(anchor="w", pady=(0, 8))

    # ---------- blok 1: foldery publiczne
    pub = ttk.LabelFrame(frm, text=" 1. Foldery publiczne — widoczne dla wszystkich ", padding=8)
    pub.pack(fill="x")
    ttk.Label(pub, text="Program przeszuka te foldery (razem z podfolderami) w poszukiwaniu obrazów, filmów, plików audio i PDF. "
                        "Możesz dodać dowolnie wiele folderów, byle leżały w folderze projektu.",
              wraplength=710, justify="left").pack(anchor="w", pady=(0, 6))
    list_row = ttk.Frame(pub)
    list_row.pack(fill="x")
    box = tk.Listbox(list_row, height=4, selectmode="extended", activestyle="none", font=("Segoe UI", 10))
    box.pack(side="left", fill="x", expand=True)
    side = ttk.Frame(list_row)
    side.pack(side="left", padx=(10, 0), anchor="n")

    def refresh():
        box.delete(0, "end")
        for f in folders:
            box.insert("end", f)

    def add_folder():
        d = filedialog.askdirectory(initialdir=str(BASE), title="Wybierz katalog z grafikami, filmami, audio lub PDF")
        if not d:
            return
        try:
            rel = Path(d).resolve().relative_to(BASE).as_posix()
        except ValueError:
            messagebox.showwarning("Zły folder", "Wybierz folder znajdujący się wewnątrz folderu projektu,\n"
                                   "inaczej strona go nie zobaczy.")
            return
        if rel == ".":
            messagebox.showwarning("Zły folder", "Wybierz podfolder projektu, a nie sam folder projektu.")
            return
        if rel in ("haslo", "haslo_git_ignore") or rel.startswith(("haslo/", "haslo_git_ignore/")):
            messagebox.showwarning("Zły folder", "Foldery haslo i haslo_git_ignore obsługuje część prywatna (blok 2).")
            return
        if rel in ("thumbs", "converted") or rel.startswith(("thumbs/", "converted/")):
            messagebox.showwarning("Zły folder", "Foldery thumbs i converted program tworzy sam — nie dodawaj ich.")
            return
        if rel not in folders:
            folders.append(rel)
            refresh()
            save_config(folders)

    def remove_selected():
        for i in reversed(box.curselection()):
            del folders[i]
        refresh()
        save_config(folders)

    def reset_defaults():
        folders[:] = DEFAULT_FOLDERS
        refresh()
        save_config(folders)

    ttk.Button(side, text="Dodaj katalog…", command=add_folder).pack(fill="x", pady=(0, 3))
    ttk.Button(side, text="Usuń zaznaczony", command=remove_selected).pack(fill="x", pady=3)
    ttk.Button(side, text="Domyślne", command=reset_defaults).pack(fill="x", pady=3)

    # ---------- blok 2: prywatne
    priv = ttk.LabelFrame(frm, text=" 2. Prywatne pliki — zaszyfrowane hasłem ", padding=8)
    priv.pack(fill="x", pady=(10, 0))
    ttk.Label(priv, text=PRIVATE_INFO, wraplength=710, justify="left").pack(anchor="w")

    status_row = ttk.Frame(priv)
    status_row.pack(fill="x", pady=(6, 4))
    priv_status = tk.StringVar()
    ttk.Label(status_row, textvariable=priv_status, font=("Segoe UI", 10, "bold")).pack(side="left")
    ttk.Button(status_row, text="Otwórz folder haslo_git_ignore", command=lambda: open_folder(PRIVATE_DIR)).pack(side="right")

    def refresh_private():
        n, d = private_summary()
        priv_status.set(f"Znaleziono w haslo_git_ignore: {n} plików w {d} folderach." if n
                        else "W haslo_git_ignore nie ma jeszcze plików.")

    pw_row = ttk.Frame(priv)
    pw_row.pack(fill="x")
    ttk.Label(pw_row, text="Hasło:", width=16).grid(row=0, column=0, sticky="w", pady=2)
    pw1 = ttk.Entry(pw_row, show="•", width=34)
    pw1.grid(row=0, column=1, sticky="w")
    ttk.Label(pw_row, text="Powtórz hasło:", width=16).grid(row=1, column=0, sticky="w", pady=2)
    pw2 = ttk.Entry(pw_row, show="•", width=34)
    pw2.grid(row=1, column=1, sticky="w")
    show_var = tk.BooleanVar(value=False)

    def toggle_show():
        ch = "" if show_var.get() else "•"
        pw1.config(show=ch)
        pw2.config(show=ch)

    ttk.Checkbutton(pw_row, text="Pokaż hasło", variable=show_var, command=toggle_show).grid(row=0, column=2, padx=10)
    ttk.Label(priv, text=PASSWORD_INFO, wraplength=710, justify="left", foreground="#555555").pack(anchor="w", pady=(4, 0))

    # ---------- przyciski akcji
    run_btn = tk.Button(
        frm, text="Aktualizuj HTML i JSON", font=("Segoe UI", 13, "bold"),
        bg="#2e9e4f", fg="white", activebackground="#268a43", activeforeground="white",
        relief="flat", pady=10, cursor="hand2",
    )
    run_btn.pack(fill="x", pady=(12, 4))

    def preview():
        try:
            url = start_preview()
            write(f"Podgląd otwarty: {url}  (działa tylko na tym komputerze; odblokowanie hasłem też tu działa)")
        except Exception as exc:
            messagebox.showerror("Podgląd", str(exc))

    ttk.Button(frm, text="Otwórz podgląd strony w przeglądarce (lokalnie)", command=preview).pack(fill="x")

    # ---------- przebieg
    ttk.Label(frm, text="Przebieg", font=("Segoe UI", 10, "bold")).pack(anchor="w", pady=(10, 0))
    step_var = tk.StringVar(value="Gotowy.")
    ttk.Label(frm, textvariable=step_var, foreground="#1b5e20").pack(anchor="w")
    log_box = scrolledtext.ScrolledText(frm, height=10, state="disabled", font=("Consolas", 10), wrap="word")
    log_box.pack(fill="both", expand=True)
    log_box.tag_configure("h", font=("Segoe UI", 10, "bold"), foreground="#1b5e20", spacing1=8)
    log_box.tag_configure("warn", foreground="#b45309")

    def write(msg):
        log_box.config(state="normal")
        if msg.startswith("### "):
            log_box.insert("end", msg[4:] + "\n", "h")
            step_var.set(msg[4:])
        elif msg.startswith("!"):
            log_box.insert("end", msg + "\n", "warn")
        else:
            log_box.insert("end", msg + "\n")
        log_box.see("end")
        log_box.config(state="disabled")

    q = queue.Queue()

    def poll():
        finished = False
        try:
            while True:
                msg = q.get_nowait()
                if isinstance(msg, tuple):
                    kind, payload = msg
                    finished = True
                    if kind == "done":
                        write("### Gotowe")
                        write("Teraz wyślij zmiany na GitHub (w wierszu poleceń w folderze projektu):\n"
                              "  git add .\n  git commit -m \"nowe grafiki\"\n  git push")
                        step_var.set("Gotowe.")
                    else:
                        write(f"! BŁĄD: {payload}")
                        step_var.set("Błąd.")
                        messagebox.showerror("Błąd", str(payload))
                else:
                    write(msg)
        except queue.Empty:
            pass
        if finished:
            run_btn.config(state="normal", text="Aktualizuj HTML i JSON")
            refresh_private()
        else:
            win.after(100, poll)

    def start():
        if not folders:
            messagebox.showinfo("Brak folderów", "Dodaj przynajmniej jeden folder publiczny.")
            return
        save_config(folders)

        encrypt, password, new_salt = False, None, False
        n, d = private_summary()
        refresh_private()
        if n:
            ans = messagebox.askyesno(
                "Zaszyfrować prywatne pliki?",
                f"W haslo_git_ignore znaleziono {n} plików w {d} folderach.\n\n"
                "Czy zaszyfrować je hasłem z okienka i zapisać w folderze haslo/ (to trafi na GitHub)?\n\n"
                "Tak — szyfruję (zmienione pliki; reszta zostaje jak była).\n"
                "Nie — pomijam ten krok; prywatna część strony zostaje bez zmian.")
            if ans:
                if not CRYPTO_OK:
                    messagebox.showerror("Brak biblioteki", "Zainstaluj bibliotekę szyfrującą:\n\npip install cryptography")
                    return
                password = pw1.get()
                if not password:
                    messagebox.showwarning("Brak hasła", "Wpisz hasło w bloku 2 i kliknij ponownie.")
                    pw1.focus_set()
                    return
                mode = password_mode(password)
                if mode == "different":
                    if not messagebox.askyesno(
                            "Inne hasło niż poprzednio",
                            "To hasło różni się od tego, którym zaszyfrowano prywatne pliki wcześniej.\n\n"
                            "Jeśli to literówka — kliknij Nie i spróbuj ponownie.\n"
                            "Jeśli chcesz ZMIENIĆ hasło — kliknij Tak: wszystko zostanie zaszyfrowane od nowa, "
                            "a stare hasło przestanie działać."):
                        return
                if mode != "same" and password != pw2.get():
                    messagebox.showwarning("Hasła się różnią", "Pola „Hasło” i „Powtórz hasło” muszą być takie same.")
                    return
                if len(password) < 12 and not messagebox.askyesno(
                        "Krótkie hasło",
                        "Hasło ma mniej niż 12 znaków. Zaszyfrowane pliki będą publiczne, więc krótkie hasło "
                        "da się złamać próbami.\n\nUżyć mimo to?"):
                    return
                encrypt, new_salt = True, mode != "same"

        log_box.config(state="normal")
        log_box.delete("1.0", "end")
        log_box.config(state="disabled")
        run_btn.config(state="disabled", text="Trwa aktualizacja…")

        def work():
            try:
                run_update(list(folders), q.put, encrypt=encrypt, password=password, new_salt=new_salt)
                q.put(("done", None))
            except Exception as exc:
                q.put(("error", exc))

        threading.Thread(target=work, daemon=True).start()
        win.after(100, poll)

    run_btn.config(command=start)
    refresh()
    refresh_private()
    win.mainloop()


def cli():
    import getpass
    folders = load_config()
    n, d = private_summary()
    encrypt, password, new_salt = False, None, False
    if n and input(f"Znaleziono {n} prywatnych plików w {d} folderach. Zaszyfrować hasłem? [t/N] ").strip().lower().startswith("t"):
        password = getpass.getpass("Hasło: ")
        mode = password_mode(password)
        if mode != "same" and password != getpass.getpass("Powtórz hasło: "):
            print("Hasła się różnią.")
            return
        encrypt, new_salt = True, mode != "same"
    run_update(folders, encrypt=encrypt, password=password, new_salt=new_salt)


def main():
    if "--cli" in sys.argv:
        cli()
        return
    try:
        import tkinter  # noqa: F401
    except ImportError:
        print("Brak biblioteki tkinter — uruchamiam bez okna.")
        cli()
        return
    launch_gui()


if __name__ == "__main__":
    main()
