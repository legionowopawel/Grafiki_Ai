#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
aktualizacja_html.py  —  program z oknem do aktualizacji galerii.

Co robi (kolejno):
  1. Skanuje foldery PUBLICZNE (domyślnie images i pdf) — widoczne dla wszystkich.
  2. (pytając Cię o zgodę) szyfruje PRYWATNE pliki z haslo_git_ignore/<podfolder>/
     hasłem (AES-256-GCM) do folderu haslo/ — tylko ta zaszyfrowana wersja idzie na GitHub.
  3. Zapisuje galeria.json.
  4. Wstawia dane do index.html (między znacznikami DATA_START / DATA_END).

Uruchomienie z oknem:   python aktualizacja_html.py
Uruchomienie bez okna:  python aktualizacja_html.py --cli
Wymaga:                 pip install -r requirements.txt   (pillow, cryptography)
"""

import base64
import hashlib
import io
import json
import os
import queue
import re
import sys
import threading
from datetime import datetime
from pathlib import Path

BASE = Path(__file__).resolve().parent
THUMB_DIR = BASE / "thumbs"
JSON_FILE = BASE / "galeria.json"
HTML_FILE = BASE / "index.html"
CONFIG_FILE = BASE / "aktualizacja_config.json"
GITIGNORE_FILE = BASE / ".gitignore"

PRIVATE_DIR = BASE / "haslo_git_ignore"      # oryginały — NIGDY na GitHub
VAULT_DIR = BASE / "haslo"                   # zaszyfrowane — idzie na GitHub
VAULT_META = VAULT_DIR / "vault.json"
STATE_FILE = PRIVATE_DIR / ".stan_szyfrowania.json"
PBKDF2_ITER = 600_000

DEFAULT_FOLDERS = ["images", "pdf"]
IMG_EXT = {".jpg", ".jpeg", ".png", ".webp", ".gif", ".avif", ".bmp"}
PDF_EXT = {".pdf"}
MIME = {".jpg": "image/jpeg", ".jpeg": "image/jpeg", ".png": "image/png", ".webp": "image/webp",
        ".gif": "image/gif", ".avif": "image/avif", ".bmp": "image/bmp", ".pdf": "application/pdf"}
THUMB_SIZE = 640  # najdłuższy bok miniatury w px
TOTAL_STEPS = 4

try:
    from PIL import Image, ImageOps
except ImportError:
    Image = None

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


# ------------------------------------------------------------ foldery publiczne
def scan(root: Path, exts, with_thumbs, log):
    """Zwraca listę grup: [{name, label, items:[{src, title, thumb?, ar?}]}]"""
    groups = []
    if not root.is_dir():
        log(f"! Brak folderu: {root.name}")
        return groups

    # foldery domyślne (images, pdf) nie dokładają swojej nazwy do nazw grup;
    # foldery dodane przez użytkownika — tak
    prefix = "" if root in (BASE / "images", BASE / "pdf") else root.relative_to(BASE).as_posix()

    for folder, dirs, files in os.walk(root):
        dirs[:] = sorted(
            (d for d in dirs if not d.startswith(".") and (Path(folder) / d) != THUMB_DIR),
            key=natural_key,
        )
        folder_path = Path(folder)
        rel = folder_path.relative_to(root).as_posix()
        rel = "" if rel == "." else rel
        name = "/".join(p for p in (prefix, rel) if p)

        items = []
        for fname in sorted(files, key=natural_key):
            if fname.startswith(".") or Path(fname).suffix.lower() not in exts:
                continue
            full = folder_path / fname
            item = {"src": full.relative_to(BASE).as_posix(), "title": pretty_title(fname)}
            if with_thumbs:
                thumb = make_thumb(full, log)
                if thumb:
                    item["thumb"] = thumb
                    try:  # proporcje obrazka — strona dzięki temu nie obcina miniatur
                        with Image.open(BASE / thumb) as t:
                            item["ar"] = round(t.width / t.height, 4)
                    except Exception:
                        pass
            items.append(item)

        if items:
            groups.append({"name": name, "label": pretty_label(name), "items": items})
    return groups


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
        if p not in roots:
            roots.append(p)
    # jeśli wybrano folder i jego podfolder, liczy się tylko folder nadrzędny
    return [r for r in roots if not any(o != r and o in r.parents for o in roots)]


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


def list_private_files():
    """[(ścieżka względna w haslo_git_ignore (z /), Path)] — tylko obrazki i PDF."""
    out = []
    if not PRIVATE_DIR.is_dir():
        return out
    for folder, dirs, files in os.walk(PRIVATE_DIR):
        dirs[:] = sorted((d for d in dirs if not d.startswith(".")), key=natural_key)
        for fname in sorted(files, key=natural_key):
            if fname.startswith(".") or Path(fname).suffix.lower() not in (IMG_EXT | PDF_EXT):
                continue
            p = Path(folder) / fname
            out.append((p.relative_to(PRIVATE_DIR).as_posix(), p))
    return out


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

    files = list_private_files()
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
        ext = path.suffix.lower()
        kind = "pdf" if ext in PDF_EXT else "image"
        fid = hashlib.sha256(salt + rel.encode("utf-8")).hexdigest()[:24]
        src_name, thumb_name = f"{fid}.enc", f"{fid}_t.enc"
        st = path.stat()
        prev = state["files"].get(rel)

        reuse = (
            prev and prev.get("size") == st.st_size and prev.get("mtime") == st.st_mtime_ns
            and (VAULT_DIR / src_name).exists()
            and (kind == "pdf" or Image is None or (VAULT_DIR / thumb_name).exists())
        )
        if reuse:
            info = prev
            skipped += 1
        else:
            (VAULT_DIR / src_name).write_bytes(encrypt_bytes(key, path.read_bytes()))
            info = {"size": st.st_size, "mtime": st.st_mtime_ns}
            if kind == "image" and Image is not None:
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
        item = {"kind": kind, "src": f"haslo/{src_name}", "title": pretty_title(path.name), "mime": MIME[ext]}
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
    if Image is None:
        log("! Pillow niezainstalowane — bez miniatur (pip install pillow).")

    # --- 1 ---
    step(log, 1, "Foldery publiczne",
         "Przeglądam wybrane foldery i zbieram listę obrazków oraz PDF-ów. Te pliki będą widoczne dla wszystkich.\n"
         "Do każdego obrazka robię małą miniaturę (folder thumbs/), żeby strona szybko działała na telefonie.")
    roots = normalize_roots(folders, log)
    images, pdfs = [], []
    for root in roots:
        log(f"Skanuję: {root.relative_to(BASE).as_posix()}")
        images += scan(root, IMG_EXT, True, log)
        pdfs += scan(root, PDF_EXT, False, log)

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
        "images": merge_groups(images),
        "pdf": merge_groups(pdfs),
        "vault": vault,
    }

    # --- 3 ---
    step(log, 3, "Zapis galeria.json",
         "Zapisuję listę wszystkich publicznych plików (i dane potrzebne do odblokowania prywatnych) w galeria.json.")
    JSON_FILE.write_text(json.dumps(data, ensure_ascii=False, indent=2), encoding="utf-8")

    # --- 4 ---
    step(log, 4, "Aktualizacja index.html",
         "Wstawiam te same dane do index.html, dzięki czemu strona działa od razu, bez dodatkowego pobierania.")
    html_ok = inject_into_html(json.dumps(data, ensure_ascii=False, separators=(",", ":")), log)

    n_img = sum(len(g["items"]) for g in data["images"])
    n_pdf = sum(len(g["items"]) for g in data["pdf"])
    log("### Podsumowanie")
    log(f"Obrazy publiczne: {n_img} w {len(data['images'])} folderach")
    for g in data["images"]:
        log(f"   {g['label']}: {len(g['items'])}")
    log(f"PDF publiczne: {n_pdf} w {len(data['pdf'])} folderach")
    log("Część prywatna: " + ("aktywna (zakładka „Prywatne”)" if vault else "brak"))
    log(f"Zapisano {JSON_FILE.name}" + (f" i {HTML_FILE.name}." if html_ok else "."))
    return {"images": n_img, "pdf": n_pdf, "html_ok": html_ok}


# --------------------------------------------------------------- konfiguracja
def load_config():
    try:
        data = json.loads(CONFIG_FILE.read_text(encoding="utf-8"))
        folders = [str(f) for f in data.get("folders", [])]
        if folders:
            return folders
    except Exception:
        pass
    return list(DEFAULT_FOLDERS)


def save_config(folders):
    try:
        CONFIG_FILE.write_text(json.dumps({"folders": folders}, ensure_ascii=False, indent=2), encoding="utf-8")
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
    "Ten program przygotowuje galerię do wysłania na GitHub. Robi to w 4 krokach: (1) zbiera pliki z folderów "
    "publicznych, (2) — jeśli się zgodzisz — szyfruje prywatne pliki hasłem, (3) zapisuje galeria.json, "
    "(4) aktualizuje index.html. Po każdym kliknięciu zielonego przycisku zobaczysz na dole, co dokładnie się dzieje."
)

PRIVATE_INFO = (
    "Oryginały prywatnych grafik trzymaj w folderze haslo_git_ignore/<podfolder>/. Ten folder jest w .gitignore, "
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
    ttk.Label(pub, text="Program przeszuka te foldery (razem z podfolderami) w poszukiwaniu obrazków i plików PDF. "
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
        d = filedialog.askdirectory(initialdir=str(BASE), title="Wybierz katalog z grafikami lub PDF")
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
