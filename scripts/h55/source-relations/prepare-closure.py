#!/usr/bin/env python3
"""Emit a serial, source-only dependency build; never edits producer sources."""
import pathlib,shlex,sys
from lean_imports import header_imports
root=pathlib.Path(__file__).resolve().parents[3];seen=set();order=[]
def visit(mod):
    if mod in seen:return
    seen.add(mod);p=root/(mod.replace('.','/')+'.lean')
    if not p.exists():
        if mod.startswith(('Init','Std','Lean')):return
        raise SystemExit('Unresolved local import '+mod)
    for dep in header_imports(p.read_text()):visit(dep)
    order.append(mod)
for name in sys.argv[1:]:visit(name)
print('set -eu')
print('export LEAN_PATH=.lake/build/lib/lean')
for mod in order:
    source=mod.replace('.','/')+'.lean';obj='.lake/build/lib/lean/'+mod.replace('.','/')+'.olean'
    print('mkdir -p '+shlex.quote(str(pathlib.Path(obj).parent)))
    print('echo H55_MODULE='+shlex.quote(mod))
    print('timeout 300 lean -j1 --tstack=131072 -o '+shlex.quote(obj)+' '+shlex.quote(source))
print('echo H55_CLOSURE_PASS')
