#!/usr/bin/env bash
# ship-cache.sh [--dry-run] CHECKOUT: relay master's Lake artifacts to the lane VMs.
#
# Run by the coordinator after a scheduled merge, on the integration checkout
# whose gates (`run-lean.sh`, and `--bridge` when Bridge/ was built) just
# passed at origin/master. It collects every module's outputs from the
# checkout's Lake traces (`.lake/build/**/*.trace`: `depHash` is the input hash,
# `outputs` the artifact hashes) and the matching lines of the host cache's
# `inputs/<package>.jsonl`, packs the artifacts the previous shipment did not
# carry (the delta), and for each active lane VM sends exactly the artifacts
# that VM lacks, then appends the input-to-output lines it lacks. Lake's cache
# is content-addressed and keyed by input hash on the same toolchain (4.24.0
# everywhere), so a VM whose sources match master at a module fetches it
# instead of rebuilding it (`docs/parallelism.md`, P5).
#
# Never overwrites: artifacts are extracted with --skip-old-files (a name is
# its content hash), and a mapping line is appended only for an input hash the
# VM's file does not hold, under the same flock Lake takes. Every pack is
# sha256-checked after upload and every extracted artifact against the
# manifest. A VM without the free disk for pack + contents + SHIP_RESERVE is
# skipped and reported. Mathlib: a VM with the Bridge's Mathlib checkout at
# the host's pin gets the `lake exe cache` files of SHIP_MATHLIB_SUMS it lacks.
#
# Environment:
#   SHIP_STATE         shipments and receipts (~/.local/state/cloudvm-coord/cache-ship)
#   SHIP_LANES         file of "BATCH SLUG" lines (default: poll-state.json lanes
#                      with offline == false)
#   SHIP_RESERVE       bytes left free on a VM after unpacking (2 GiB)
#   SHIP_MATHLIB_SUMS  sha256sum list of Mathlib cache files the Bridge needs
#                      (~/.local/state/cloudvm-coord/xfer-mathlib-ae/SHA256SUMS.all)
#   SHIP_ALLOW_HEAD=1  ship a checkout that is not at origin/master
#   VMEXEC             ~/.local/share/cloudvm-coord/vmexec.py
#
# Exit 0 = every reachable VM is up to date or skipped for a recorded reason,
# 1 = a transfer or verification failed on some VM, 2 = usage or setup error.
set -euo pipefail
dry=0
if [[ ${1-} == --dry-run ]]; then dry=1; shift; fi
[[ $# -eq 1 && -d $1 ]] || { echo "usage: ship-cache.sh [--dry-run] CHECKOUT" >&2; exit 2; }
exec python3 - "$dry" "$(cd "$1" && pwd)" <<'PY'
import hashlib, json, os, pathlib, shlex, subprocess, sys, tempfile, time
from datetime import datetime, timezone

dry = sys.argv[1] == '1'; co = pathlib.Path(sys.argv[2])
H = pathlib.Path.home()
STATE = pathlib.Path(os.environ.get('SHIP_STATE', H/'.local/state/cloudvm-coord/cache-ship'))
VMEXEC = os.environ.get('VMEXEC', str(H/'.local/share/cloudvm-coord/vmexec.py'))
RESERVE = int(os.environ.get('SHIP_RESERVE', 2*1024**3))
MSUMS = pathlib.Path(os.environ.get('SHIP_MATHLIB_SUMS', H/'.local/state/cloudvm-coord/xfer-mathlib-ae/SHA256SUMS.all'))
PKGS = [('solidity-lean', co/'.lake/build'), ('solidity-bridge', co/'Bridge/.lake/build')]

def die(msg, code=2): print('ship-cache: '+msg, file=sys.stderr); sys.exit(code)
def git(*a): return subprocess.check_output(['git', '-C', str(co), *a], text=True).strip()

head = git('rev-parse', 'HEAD')
master = subprocess.run(['git', '-C', str(co), 'rev-parse', 'origin/master'], capture_output=True, text=True).stdout.strip()
if head != master and os.environ.get('SHIP_ALLOW_HEAD') != '1':
    die(f'{co} is at {head[:12]}, origin/master is {master[:12]}; ship master only (SHIP_ALLOW_HEAD=1 overrides)')
tc = (co/'lean-toolchain').read_text().strip()
cache = pathlib.Path(os.environ.get('LAKE_CACHE_DIR') or H/'.elan/toolchains'/tc.replace('/', '--').replace(':', '---')/'lake/cache')
art = cache/'artifacts'
if not art.is_dir(): die(f'no Lake artifact cache at {cache}')

# 1. The shipment: master's mapping lines and artifacts.
names = {}
for p in art.iterdir(): names.setdefault(p.name.split('.', 1)[0], []).append(p.name)
entries = {}; arts = set(); unresolved = 0
for pkg, build in PKGS:
    if not build.is_dir(): continue
    lines = {}
    jf = cache/'inputs'/(pkg+'.jsonl')
    if jf.is_file():
        for l in jf.read_text().splitlines():
            try: lines[json.loads(l)[0]] = l
            except Exception: pass
    out = entries.setdefault(pkg, {})
    for t in build.rglob('*.trace'):
        try: d = json.loads(t.read_text())
        except Exception: continue
        k = d.get('depHash'); o = d.get('outputs')
        if k not in lines or o is None: continue
        hs = [o] if isinstance(o, str) else [x for v in o.values() for x in (v if isinstance(v, list) else [v])] if isinstance(o, dict) else []
        if not hs or any(str(h) not in names for h in hs): unresolved += 1; continue
        out[k] = lines[k]; arts.update(n for h in hs for n in names[str(h)])
if not arts: die(f'no cached outputs found under {co}/.lake/build; run the gates there first')
STATE.mkdir(parents=True, exist_ok=True)
shacache = STATE/'sha256.tsv'; known = {}
if shacache.is_file():
    for l in shacache.read_text().splitlines():
        n, s = l.split('\t'); known[n] = s
def sha(path):
    h = hashlib.sha256()
    with open(path, 'rb') as f:
        for b in iter(lambda: f.read(1 << 20), b''): h.update(b)
    return h.hexdigest()
new = {n: sha(art/n) for n in sorted(arts) if n not in known}
if new:
    with open(shacache, 'a') as f:
        for n, s in new.items(): f.write(f'{n}\t{s}\n')
    known.update(new)
stamp = datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%SZ')
prev = sorted(d for d in STATE.glob('*-*') if (d/'artifacts.tsv').is_file() and (d/'shipped').is_file())
prev = prev[-1] if prev else None
ship = STATE/f'{stamp}-{head[:8]}'; ship.mkdir(exist_ok=True)
size = {n: (art/n).stat().st_size for n in arts}
(ship/'artifacts.tsv').write_text(''.join(f'{n}\t{size[n]}\t{known[n]}\n' for n in sorted(arts)))
for pkg, es in entries.items(): (ship/f'inputs.{pkg}.jsonl').write_text(''.join(l+'\n' for l in es.values()))
prevset = set(l.split('\t')[0] for l in (prev/'artifacts.tsv').read_text().splitlines()) if prev else set()
delta = sorted(arts - prevset)
(ship/'delta.txt').write_text(''.join(n+'\n' for n in delta))
(ship/'HEAD').write_text(head+'\n')
print(f'shipment {ship.name}: {len(arts)} artifacts ({sum(size.values())/1e9:.2f} GB), '
      f'{sum(len(e) for e in entries.values())} mappings, delta vs {prev.name if prev else "nothing"}: '
      f'{len(delta)} ({sum(size[n] for n in delta)/1e9:.2f} GB); {unresolved} traces without cached outputs skipped')

packs = {}
def pack(members):
    key = hashlib.sha256('\n'.join(members).encode()).hexdigest()[:16]
    if key in packs: return packs[key]
    p = ship/f'pack-{key}.tar.zst'
    if not p.is_file():
        lst = ship/f'pack-{key}.list'; lst.write_text(''.join(n+'\n' for n in members))
        subprocess.run(f'tar -C {shlex.quote(str(art))} -cf - -T {shlex.quote(str(lst))} | zstd -T0 -3 -q -o {shlex.quote(str(p))}', shell=True, check=True)
    packs[key] = (p, sha(p), p.stat().st_size)
    return packs[key]
if delta and not dry: pack(delta)

# 2. The lanes.
def lanes():
    f = os.environ.get('SHIP_LANES')
    if f: return [tuple(l.split()[:2]) for l in pathlib.Path(f).read_text().splitlines() if l.strip() and not l.startswith('#')]
    ps = json.loads((H/'.local/state/cloudvm-coord/poll-state.json').read_text())
    return [tuple(k.split('/', 1)) for k, v in ps.items() if v.get('offline') is False]
def env_of(batch, slug):
    c = json.loads((H/f'.local/share/cloudvm/batches/{batch}/catalog.json').read_text())
    return next(t['environmentId'] for t in c['tasks'] if t['slug'] == slug)
def vm(env, cmd, timeout=600):
    r = subprocess.run([sys.executable, VMEXEC, env, cmd, str(timeout)], capture_output=True, text=True)
    first, _, rest = r.stdout.partition('\n')
    if r.returncode != 0 or first.strip() != 'exit 0':
        raise RuntimeError(f'{first.strip() or r.returncode}: {cmd[:120]}: {(r.stderr or rest)[-400:]}')
    return rest
def put(env, local, remote):
    r = subprocess.run([sys.executable, VMEXEC, env, '--put', str(local), remote], capture_output=True, text=True)
    if r.returncode != 0: raise RuntimeError(f'put {local.name}: {r.stdout[-200:]} {r.stderr[-400:]}')
def get(env, remote, local):
    r = subprocess.run([sys.executable, VMEXEC, env, '--get', remote, str(local)], capture_output=True, text=True)
    if r.returncode != 0: raise RuntimeError(f'get {remote}: {r.stderr[-400:]}')

PROBE = r'''source /workspace/.setup/activate.sh 2>/dev/null || true
c=${LAKE_CACHE_DIR:-}; if [ -z "$c" ]; then if command -v elan >/dev/null; then c=$(elan which lean | sed 's#/bin/lean$##')/lake/cache; else c=${XDG_CACHE_HOME:-$HOME/.cache}/lake; fi; fi
mkdir -p "$c/artifacts" "$c/inputs" "$c/.ship"; echo "cache=$c"
echo "avail=$(df -B1 --output=avail "$c" | tail -1 | tr -d ' ')"
echo "lean=$(lean --version 2>/dev/null | head -1)"
m=/workspace/solidity-lean/Bridge/.lake/packages/mathlib; [ -d "$m/.git" ] && echo "mathlib=$(git -C $m rev-parse HEAD)" || echo mathlib=
[ -f "$m/.lake/build/lib/lean/Mathlib.olean" ] && echo mathlib_built=1 || echo mathlib_built=0
echo "mlcache=${XDG_CACHE_HOME:-$HOME/.cache}/mathlib"'''
APPEND = r'''import fcntl,json,os,sys
jf,new,art=sys.argv[1:4]
present={n.split('.',1)[0] for n in os.listdir(art)}
open(jf,'a').close()
with open(jf,'r+') as f:
    fcntl.flock(f,fcntl.LOCK_EX)  # the lock Lake's CacheMap.save takes
    have=set()
    for l in f:
        try: have.add(json.loads(l)[0])
        except Exception: pass
    add=[]
    for l in open(new):
        k,v=json.loads(l)
        if k in have: continue
        hs=[v] if isinstance(v,str) else [x for y in v.values() for x in (y if isinstance(y,list) else [y])]
        if all(str(h) in present for h in hs): add.append(l.rstrip('\n')+'\n')
    f.seek(0,2); f.write(''.join(add)); f.flush(); os.fsync(f.fileno())
print(len(add),len(have))'''
mhost = ''
mf = co/'Bridge/lake-manifest.json'
if mf.is_file():
    mhost = next((p.get('rev', '') for p in json.loads(mf.read_text()).get('packages', []) if p.get('name') == 'mathlib'), '')
msums = [l.split() for l in MSUMS.read_text().splitlines()] if MSUMS.is_file() else []
mlocal = H/'.cache/mathlib'

failed = 0; receipts = []
for batch, slug in lanes():
    tag = f'{batch}/{slug}'
    try:
        env = c = None
        env = env_of(batch, slug)
        info = dict(l.split('=', 1) for l in vm(env, PROBE, 120).splitlines() if '=' in l)
        c = info['cache']; avail = int(info['avail'])
        if '4.24.0' not in info.get('lean', ''):
            receipts.append((tag, 'skipped', f"toolchain {info.get('lean')!r}")); continue
        with tempfile.TemporaryDirectory() as td:
            td = pathlib.Path(td)
            (td/'names').write_text(''.join(n+'\n' for n in sorted(arts)))
            put(env, td/'names', f'{c}/.ship/names')
            vm(env, f'export LC_ALL=C; cd {shlex.quote(c)} && comm -23 .ship/names <(ls artifacts | LC_ALL=C sort) > .ship/missing; wc -l < .ship/missing', 300)
            get(env, f'{c}/.ship/missing', td/'missing')
            missing = sorted(l for l in (td/'missing').read_text().split() if l in arts)
            need = sum(size[n] for n in missing)
            note = f'{len(missing)} artifacts missing ({need/1e9:.2f} GB)'
            if missing:
                members = delta if missing == delta else missing
                if dry:
                    receipts.append((tag, 'dry-run', note)); continue
                p, psha, psize = pack(members)
                if avail < psize + need + RESERVE:
                    receipts.append((tag, 'skipped', f'{note}; free {avail/1e9:.2f} GB < pack {psize/1e9:.2f} + {need/1e9:.2f} + reserve')); continue
                sums = td/'sums'; sums.write_text(''.join(f'{known[n]}  {n}\n' for n in missing))
                put(env, p, f'{c}/.ship/{p.name}'); put(env, sums, f'{c}/.ship/sums')
                vm(env, f'cd {shlex.quote(c)} && echo "{psha}  .ship/{p.name}" | sha256sum -c --quiet && '
                        f'rm -rf .ship/stage && mkdir .ship/stage && tar --zstd -xf .ship/{p.name} -C .ship/stage && '
                        f'(cd .ship/stage && sha256sum -c --quiet ../sums) && '
                        f'for f in .ship/stage/*; do mv -n "$f" artifacts/; done && rm -rf .ship/stage .ship/{p.name}', 1800)
                note += f'; sent {p.name} {psize/1e6:.0f} MB sha256 {psha[:12]}'
            elif dry:
                receipts.append((tag, 'dry-run', note)); continue
            (td/'append.py').write_text(APPEND); put(env, td/'append.py', f'{c}/.ship/append.py')
            for pkg in entries:
                put(env, ship/f'inputs.{pkg}.jsonl', f'{c}/.ship/inputs.{pkg}.jsonl')
                out = vm(env, f'cd {shlex.quote(c)} && python3 .ship/append.py inputs/{pkg}.jsonl .ship/inputs.{pkg}.jsonl artifacts', 300).split()
                note += f'; {pkg}: +{out[0]} mappings'
            if msums and info.get('mathlib') and info['mathlib'] == mhost and info.get('mathlib_built') == '0':
                (td/'mnames').write_text(''.join(n+'\n' for _, n in msums))
                put(env, td/'mnames', f'{shlex.quote(c)}/.ship/mnames')
                ml = info['mlcache']
                vm(env, f'export LC_ALL=C; mkdir -p {shlex.quote(ml)} && comm -23 <(LC_ALL=C sort {shlex.quote(c)}/.ship/mnames) <(ls {shlex.quote(ml)} | LC_ALL=C sort) > {shlex.quote(c)}/.ship/mmissing', 120)
                get(env, f'{c}/.ship/mmissing', td/'mmissing')
                mm = [n for n in (td/'mmissing').read_text().split() if (mlocal/n).is_file()]
                if mm:
                    mp = td/'mathlib.tar'
                    subprocess.run(['tar', '-C', str(mlocal), '-cf', str(mp), *mm], check=True)
                    msha = sha(mp)
                    if avail < 2*mp.stat().st_size + RESERVE: raise RuntimeError('no disk for the Mathlib files')
                    put(env, mp, f'{c}/.ship/mathlib.tar')
                    (td/'msums').write_text(''.join(f'{s}  {n}\n' for s, n in msums if n in set(mm)))
                    put(env, td/'msums', f'{c}/.ship/msums')
                    vm(env, f'cd {shlex.quote(ml)} && echo "{msha}  "{shlex.quote(c)}/.ship/mathlib.tar | sha256sum -c --quiet && '
                            f'tar -xf {shlex.quote(c)}/.ship/mathlib.tar --skip-old-files && sha256sum -c --quiet {shlex.quote(c)}/.ship/msums && rm -f {shlex.quote(c)}/.ship/mathlib.tar', 900)
                    note += f'; Mathlib: {len(mm)} cache files'
            vm(env, f'rm -rf {shlex.quote(c)}/.ship', 60)
            receipts.append((tag, 'ok', note))
    except Exception as e:
        failed = 1; receipts.append((tag, 'FAILED', str(e)[:300]))
        try: vm(env, f'rm -rf {shlex.quote(c)}/.ship', 60)
        except Exception: pass
if not dry and any(r[1] == 'ok' for r in receipts): (ship/'shipped').write_text('')
(ship/'receipts.tsv').write_text(''.join('\t'.join(r)+'\n' for r in receipts))
print(''.join('\t'.join(r)+'\n' for r in receipts), end='')
print(f'receipts: {ship}/receipts.tsv')
sys.exit(failed)
PY
