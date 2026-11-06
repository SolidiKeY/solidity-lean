#!/usr/bin/env python3
"""Topological, one-process-at-a-time Lean checks in an isolated artifact tree.
This is a per-file proof gate, not a Lake/full repository build verdict.
"""
import hashlib,json,os,pathlib,subprocess,sys
if len(sys.argv) < 3:
    raise SystemExit('usage: serial_check.py EVIDENCE_DIR MODULE [MODULE...]')
root=pathlib.Path(__file__).resolve().parents[3]
os.chdir(root)
evidence=pathlib.Path(sys.argv[1]).resolve()
cache=root/'.lake/refactor-cache/h55-h82/lib/lean'
evidence.mkdir(parents=True,exist_ok=True)
cache.mkdir(parents=True,exist_ok=True)
seen=set(); order=[]
def visit(module):
    if module in seen: return
    seen.add(module)
    source=root/(module.replace('.','/')+'.lean')
    if not source.is_file():
        if module.startswith('Solidity.'): raise SystemExit('missing source '+module)
        return
    imports=[]
    for line in source.read_text().splitlines():
        if line.startswith('import '):
            imports.extend(line.split()[1:])
    for dep in imports: visit(dep)
    order.append((module,source,imports))
for target in sys.argv[2:]:
    if not (root/(target.replace('.','/')+'.lean')).is_file():
        raise SystemExit('missing target source '+target)
    visit(target)
version=subprocess.check_output(['lean','--version'],text=True)
keys={}
for index,(module,source,imports) in enumerate(order,1):
    key=hashlib.sha256(source.read_bytes()+version.encode()+b'-j1 --tstack=131072'+''.join(keys.get(dep,dep) for dep in imports).encode()).hexdigest()
    keys[module]=key
    output=cache/(module.replace('.','/')+'.olean')
    stamp=output.with_suffix('.checked.json')
    # Retired checkpoint: never trust historical stamps as a proof receipt.
    # All requested modules are checked anew; only imported artifacts are reused.
    output.parent.mkdir(parents=True,exist_ok=True)
    env=dict(os.environ,LEAN_NUM_THREADS='1',LEAN_PATH=str(cache),PYTHONDONTWRITEBYTECODE='1')
    prefix=evidence.joinpath(*module.split('.'))/'check'
    command=['lean','-j1','--tstack=131072','-o',str(output),'-i',str(output.with_suffix('.ilean')),str(source.relative_to(root))]
    run=subprocess.run([sys.executable,str(root/'scripts/h55/yul-artifact/bounded.py'),str(prefix),'--',*command],env=env)
    record=json.loads(prefix.with_suffix('.json').read_text())
    record.update(key=key,module=module,source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),toolchain=version.strip(),executor='ccarenv_9a11f3436b048191a66249de9ed39b16',cache_state='warm-imports')
    prefix.with_suffix('.json').write_text(json.dumps(record,indent=2)+'\n')
    if run.returncode: raise SystemExit(run.returncode)
    stamp.write_text(json.dumps(dict(key=key,source=str(source)))+'\n')
    print(f'PASS {index}/{len(order)} {module}',flush=True)
print('SERIAL_PER_FILE_GATE_PASS',flush=True)
