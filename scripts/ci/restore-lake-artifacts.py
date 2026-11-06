#!/usr/bin/env python3
"""Materialize fetched Lake artifacts into .lake/build (CI, H91).

With `enableArtifactCache`, Lake 4.24 leaves a module it *fetched* from the cache
out of `.lake/build`: its trace names the content hashes, and Lake reads the
files from the cache. Tools that run Lean themselves (`lake env lean`, the
replay-timing script, the CLI tests) look in `.lake/build` and miss them. This
hard-links (or copies) each traced output back to where a local build puts it:
`lib/lean/X.olean`/`.ilean` (and any extra olean parts) and `ir/X.c`.
Never overwrites an existing file. Usage: restore-lake-artifacts.py [ROOT]
"""
import json, os, pathlib, shutil, sys
root = pathlib.Path(sys.argv[1] if len(sys.argv) > 1 else '.').resolve()
build = root/'.lake/build'
import subprocess
cache = os.environ.get('LAKE_CACHE_DIR') or str(pathlib.Path(subprocess.check_output(
    ['elan', 'which', 'lean'], text=True).strip()).parent.parent/'lake/cache')
art = pathlib.Path(cache)/'artifacts'
names = {}
for n in os.listdir(art):
    names.setdefault(n.split('.', 1)[0], []).append(n)
placed = missing = 0
def put(src, dst):
    global placed
    if dst.exists(): return
    dst.parent.mkdir(parents=True, exist_ok=True)
    try: os.link(src, dst)
    except OSError: shutil.copy2(src, dst)
    placed += 1
for t in (build/'lib/lean').rglob('*.trace'):
    try: o = json.loads(t.read_text()).get('outputs')
    except Exception: continue
    if not isinstance(o, dict): continue
    stem = t.with_suffix('')                       # lib/lean/A/B
    rel = stem.relative_to(build/'lib/lean')
    for key, hs in o.items():
        for h in (hs if isinstance(hs, list) else [hs]):
            for n in names.get(str(h), []):
                ext = n.split('.', 1)[1]           # olean, olean.server, ilean, c, ...
                dst = (build/'ir'/rel).with_suffix('.' + ext) if ext == 'c' else stem.with_suffix('.' + ext)
                put(art/n, dst)
            if str(h) not in names: missing += 1
print(f'restore-lake-artifacts: placed {placed} files, {missing} hashes not in cache')
