#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
mirror_webgame.py — Mirror a browser-hosted web game (e.g., itch.io WebGL build)

Features
- Recursively downloads assets referenced by the entry HTML (scripts, styles, images, audio/video,
  Unity WebGL files like *.data.unityweb / *.framework.js.unityweb / *.wasm.unityweb / *.json).
- Constrains crawl to the same path subtree by default to avoid wandering off.
- Saves files to an output directory, preserving relative paths.
- Rewrites downloaded absolute URLs inside HTML/JS/CSS to local paths for offline use.
- Sends browser-like headers and same-origin Referer/Origin to avoid CDN 403s.
- Works best when served locally:
    cd OUTPUT_DIR && python -m http.server 8000
    open http://localhost:8000/index.html

Only use for personal offline use; respect the game’s license/itch.io Terms.
"""

import argparse
import os
import re
import sys
import time
import threading
from urllib.parse import urlsplit, urlunsplit, urljoin

import pathlib
import queue
import mimetypes

try:
    import requests
except ImportError:
    print("This script requires the 'requests' package. Install via: pip install requests")
    sys.exit(1)

# Browser-like defaults (Referer/Origin are set per-request)
HEADERS = {
    "User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120 Safari/537.36",
    "Accept": "*/*",
    "Accept-Language": "en-US,en;q=0.9",
    "Accept-Encoding": "gzip, deflate, br",
    "Connection": "keep-alive",
    # These two are harmless hints; some CDNs look at them
    "Sec-Fetch-Dest": "empty",
    "Sec-Fetch-Site": "same-origin",
}
REQUEST_TIMEOUT = 30
MAX_WORKERS = 8

# File types we consider "assets" and will try to fetch if referenced
ASSET_EXT_RE = re.compile(
    r"""(?ix)
    \.(?:                     # common web & Unity WebGL assets
        js|mjs|css|json|
        png|jpe?g|gif|webp|svg|ico|
        mp3|ogg|wav|mp4|webm|
        ttf|otf|woff2?|txt|
        data\.unityweb|
        framework\.js\.unityweb|
        wasm(?:\.unityweb)?   # .wasm or .wasm.unityweb
    )
    (?:\?[^"'\s)]*)?          # optional query
    $"""
)

# Extractors for URLs in various text types
HTML_URL_RE = re.compile(
    r'''(?ix)
    (?:src|href|data-src|data-url)\s*=\s*(?:"([^"]+)"|'([^']+)')
    ''')
CSS_URL_RE = re.compile(
    r'''(?ix)
    url\(\s*(?:"([^"]+)"|'([^']+)'|([^"')]+))\s*\)
    ''')
# General string literals respecting their quote type (allows apostrophes in ")
STRING_LITERAL_RE = re.compile(
    r'''(?sx)
    (?:"(?P<dq>(?:[^"\\]|\\.)*)"|'(?P<sq>(?:[^'\\]|\\.)*)')
    ''')

# Unity loader patterns
BUILDURL_RE = re.compile(r'''(?ix)\b(buildUrl|buildURL)\s*=\s*(?:"([^"]+)"|'([^']+)')''')
BUILDURL_CONCAT_RE = re.compile(r'''(?ix)\bbuildUrl\s*\+\s*(?:"([^"]+)"|'([^']+)')''')

# Unity loader json/vars: dataUrl, frameworkUrl, codeUrl, streamingAssetsUrl
UNITY_KEYS_RE = re.compile(
    r'''(?ix)
    (?:"|\')(dataUrl|frameworkUrl|codeUrl|streamingAssetsUrl)(?:"|\')\s*:\s*(?:"([^"]+)"|'([^']+)')
    '''
)

def discover_unity_loader_links(base_url: str, text: str) -> set:
    """Find Unity WebGL loader asset URLs reliably."""
    links = set()
    for m in UNITY_KEYS_RE.finditer(text):
        rel = m.group(2) or m.group(3)
        links.add(normalize_url(base_url, rel))
    # Older loaders define variables:
    for m in re.finditer(
        r'\b(?:var|let|const)\s+(?:dataUrl|frameworkUrl|codeUrl|streamingAssetsUrl)\s*=\s*(?:"([^"]+)"|'"'([^']+)'"')',
        text
    ):
        rel = m.group(1) or m.group(2)
        links.add(normalize_url(base_url, rel))
    return links


def normalize_url(base_url: str, found: str) -> str:
    """Make absolute without re-encoding parts; strip fragments only."""
    absu = urljoin(base_url, found)
    parts = urlsplit(absu)
    return urlunsplit((parts.scheme, parts.netloc, parts.path, parts.query, ""))  # no fragment


def within_subtree(root_url: str, candidate: str) -> bool:
    """Keep downloads within the same scheme+host and the same path prefix as the root page."""
    r = urlsplit(root_url)
    c = urlsplit(candidate)
    if (r.scheme, r.netloc) != (c.scheme, c.netloc):
        return False
    # Subtree = directory containing the root page's index
    root_dir = r.path.rsplit("/", 1)[0] + "/"
    cand_path = c.path
    return cand_path.startswith(root_dir)


def url_to_local_paths(entry_url: str, url: str, outdir: str):
    """
    Map a URL to a local path under outdir, preserving the subtree structure.

    - Files under the same subtree end up relative to outdir/.
    - Anything outside that subtree is placed under _external/<host>/...
    - Handles directory URLs by appending index.html.
    - Strips ?query from the filename on disk (safe for Unity assets).
    """
    e = urlsplit(entry_url)
    u = urlsplit(url)
    same_host = (e.scheme, e.netloc) == (u.scheme, u.netloc)
    root_dir = e.path.rsplit("/", 1)[0] + "/"

    path = u.path
    if path.endswith("/"):
        path = path + "index.html"

    path = path.lstrip("/")

    if (not same_host) or (not u.path.startswith(root_dir)):
        save_path = os.path.join(outdir, "_external", u.netloc, path)
        rel_path = os.path.join("_external", u.netloc, path)
    else:
        # store relative to subtree root
        # e.g., if entry is /html/14287485/Peggy's Post/index.html,
        # keep files under that folder layout
        if u.path == e.path:
            rel_sub = "index.html"
        else:
            # compute relative to root_dir
            rel_sub = u.path[len(root_dir):].lstrip("/")
            if rel_sub == "":
                rel_sub = "index.html"
        save_path = os.path.join(outdir, rel_sub)
        rel_path = rel_sub

    if "?" in save_path:
        save_path = save_path.split("?", 1)[0]
    if rel_path and "?" in rel_path:
        rel_path = rel_path.split("?", 1)[0]

    return save_path, rel_path


def ensure_dir_for(path: str):
    pathlib.Path(os.path.dirname(path)).mkdir(parents=True, exist_ok=True)


def is_asset_like(url: str) -> bool:
    path = urlsplit(url).path
    return ASSET_EXT_RE.search(path) is not None


def discover_links(base_url: str, content: bytes, ctype: str) -> set:
    """Return a set of absolute URLs discovered inside the content."""
    text = None
    try:
        if content is not None:
            text = content.decode("utf-8", errors="ignore")
    except Exception:
        return set()

    found = set()

    def add_relatives(matches):
        for m in matches:
            candidate = m.strip()
            if not candidate:
                continue
            if candidate.startswith(("data:", "about:", "javascript:", "#")):
                continue
            absu = normalize_url(base_url, candidate)
            if is_asset_like(absu) or absu.endswith("/") or absu.endswith("index.html"):
                found.add(absu)

    if ctype.startswith("text/html"):
        for m in HTML_URL_RE.finditer(text):
            s = m.group(1) or m.group(2)
            add_relatives([s])
        for m in CSS_URL_RE.finditer(text):  # style tags inline
            s = m.group(1) or m.group(2) or m.group(3)
            add_relatives([s])

        # Unity loader keys inside inline <script> blocks
        for u2 in discover_unity_loader_links(base_url, text):
            found.add(u2)

        # Handle buildUrl concatenations present in inline scripts
        build_base = None
        mm = BUILDURL_RE.search(text)
        if mm:
            build_base = normalize_url(base_url, (mm.group(2) or mm.group(3)))
            base_dir = build_base if build_base.endswith("/") else build_base + "/"
            found.add(base_dir)
        if build_base:
            for cm in BUILDURL_CONCAT_RE.finditer(text):
                s = cm.group(1) or cm.group(2)
                found.add(normalize_url(base_url, build_base + ("/" if not build_base.endswith("/") else "") + s))

        # generic strings (rarely needed for HTML)
        for m in STRING_LITERAL_RE.finditer(text):
            s = m.group('dq') or m.group('sq')
            if s and ASSET_EXT_RE.search(s):
                found.add(normalize_url(base_url, s))

    elif ctype.startswith(("text/css", "application/json")):
        for m in CSS_URL_RE.finditer(text):
            s = m.group(1) or m.group(2) or m.group(3)
            add_relatives([s])
        for m in STRING_LITERAL_RE.finditer(text):
            s = m.group('dq') or m.group('sq')
            if s and ASSET_EXT_RE.search(s):
                found.add(normalize_url(base_url, s))

    elif ctype.startswith(("application/javascript", "text/javascript")):
        # Unity loader keys (most reliable)
        for u2 in discover_unity_loader_links(base_url, text):
            found.add(u2)

        # Fallbacks: older buildUrl concatenations and generic strings
        build_base = None
        mm = BUILDURL_RE.search(text)
        if mm:
            build_base = normalize_url(base_url, (mm.group(2) or mm.group(3)))
        if build_base:
            for cm in BUILDURL_CONCAT_RE.finditer(text):
                s = cm.group(1) or cm.group(2)
                # join with exactly one slash
                bb = build_base if build_base.endswith("/") else (build_base + "/")
                found.add(normalize_url(base_url, bb + s))

        for m in STRING_LITERAL_RE.finditer(text):
            s = m.group('dq') or m.group('sq')
            if s and ASSET_EXT_RE.search(s):
                found.add(normalize_url(base_url, s))

    return found


def guess_content_type(path: str, server_ct: str) -> str:
    if server_ct:
        return server_ct.split(";")[0].strip().lower()
    guessed, _ = mimetypes.guess_type(path)
    return guessed or "application/octet-stream"


def rewrite_local_refs(file_path: str, url_to_relpath: dict):
    """
    For text files (html/js/css/json), rewrite occurrences of downloaded absolute URLs
    to their local relative paths for offline use.
    """
    try:
        with open(file_path, "rb") as f:
            raw = f.read()
        text = raw.decode("utf-8", errors="ignore")
    except Exception:
        return

    replaced = text
    # Replace longer URLs first to avoid partial overlaps
    for u in sorted(url_to_relpath.keys(), key=len, reverse=True):
        local_rel = url_to_relpath[u].replace("\\", "/")
        replaced = replaced.replace(u, local_rel)

    if replaced != text:
        with open(file_path, "wb") as f:
            f.write(replaced.encode("utf-8", errors="ignore"))


def main():
    ap = argparse.ArgumentParser(description="Mirror a browser-hosted web game for offline use.")
    ap.add_argument("url", help="Entry page URL (e.g., the game's index.html)")
    ap.add_argument("-o", "--outdir", default="webgame_mirror", help="Output directory")
    ap.add_argument("--include-external", action="store_true",
                    help="Also download assets from outside the entry page's path subtree")
    ap.add_argument("--workers", type=int, default=MAX_WORKERS, help="Max concurrent downloads (default: 8)")
    args = ap.parse_args()

    entry_url = args.url
    # Precompute origin for Referer/Origin headers
    entry_parts = urlsplit(entry_url)
    origin_of_entry_url = f"{entry_parts.scheme}://{entry_parts.netloc}"

    outdir = args.outdir
    max_workers = max(1, args.workers)

    os.makedirs(outdir, exist_ok=True)

    session = requests.Session()
    session.headers.update(HEADERS)

    # Queues and sets
    to_visit = queue.Queue()
    to_visit.put(entry_url)

    seen = set()
    downloaded = set()
    discovered_all = set([entry_url])
    url_to_savepath = {}
    url_to_relpath = {}

    lock = threading.Lock()

    def fetch_one(u: str):
        nonlocal url_to_savepath, url_to_relpath
        try:
            # Per-request headers so the CDN accepts us (anti-hotlink)
            h = dict(session.headers)
           # Always send the actual page URL as Referer, just like the browser in your screenshot
            h["Referer"] = entry_url
            h["Origin"]  = origin_of_entry_url

            r = session.get(u, timeout=REQUEST_TIMEOUT, stream=True, headers=h)
            r.raise_for_status()
        except Exception as e:
            print(f"[!] Failed: {u} ({e})")
            return None, None, None

        save_path, rel_path = url_to_local_paths(entry_url, u, outdir)
        ensure_dir_for(save_path)

        try:
            with open(save_path, "wb") as f:
                for chunk in r.iter_content(chunk_size=65536):
                    if chunk:
                        f.write(chunk)
                # tiny delay can help avoid rate limits on some CDNs
                time.sleep(0.05)
        except Exception as e:
            print(f"[!] Write error: {save_path} ({e})")
            return None, None, None

        ctype = guess_content_type(save_path, r.headers.get("Content-Type", ""))
        with lock:
            url_to_savepath[u] = save_path
            url_to_relpath[u] = rel_path
            downloaded.add(u)

        return save_path, rel_path, ctype

    def worker():
        while True:
            try:
                u = to_visit.get_nowait()
            except queue.Empty:
                break
            if u in seen:
                to_visit.task_done()
                continue
            seen.add(u)

            # scope filter unless include-external
            if not args.include_external and not within_subtree(entry_url, u):
                to_visit.task_done()
                continue

            sp, rp, ct = fetch_one(u)
            if sp and ct and ct.startswith(("text/", "application/javascript", "application/json")):
                try:
                    with open(sp, "rb") as f:
                        data = f.read()
                    new_links = discover_links(u, data, ct)
                    for nl in new_links:
                        if nl not in discovered_all:
                            discovered_all.add(nl)
                            to_visit.put(nl)
                except Exception as e:
                    print(f"[!] Parse error: {sp} ({e})")

            to_visit.task_done()

    # Kick off worker threads
    threads = [threading.Thread(target=worker, daemon=True) for _ in range(max_workers)]
    t0 = time.time()
    for t in threads:
        t.start()
    for t in threads:
        t.join()
    t1 = time.time()

    # Second pass: rewrite references inside text files to local paths
    text_like_exts = (".html", ".htm", ".css", ".js", ".mjs", ".json")
    for u, sp in list(url_to_savepath.items()):
        if any(sp.lower().endswith(ext) for ext in text_like_exts):
            rewrite_local_refs(sp, url_to_relpath)

    print("\n=== Mirror complete ===")
    print(f"Time: {t1 - t0:.1f}s")
    print(f"Discovered: {len(discovered_all)} | Downloaded: {len(downloaded)}")
    entry_local = url_to_savepath.get(entry_url)
    if entry_local:
        rel = os.path.relpath(entry_local, outdir)
        print(f"Open (via local server): {rel}")
    else:
        print("Entry page failed to download; check the URL or try --include-external.")

if __name__ == "__main__":
    main()
