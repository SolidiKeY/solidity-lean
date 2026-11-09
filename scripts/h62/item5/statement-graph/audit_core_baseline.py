#!/usr/bin/env python3
"""Guard H107's 95-edge audit baseline against accidental regeneration from drift.

Reproduce the immutable audit bytes from exact Git objects, never today's graph.
This is the audit's line-import census, not elaboration or a Lean semantic proof.
"""
import hashlib, io, json, re, subprocess, sys, tarfile
REF='fa5acebd43214bbe642258d862f903bcf08d3f89'
def git(*args):return subprocess.check_output(['git','--no-replace-objects',*args])
source=git('show',REF+':scripts/check-layers.mjs').decode()
def patterns(name):
    block=source[source.index('const '+name+' = ['):]
    return [re.compile(x) for x in re.findall(r'^\s*/(.+)/,',block[:block.index('];')],re.M)]
core,elab=patterns('CORE'),patterns('ELABORATOR')
def is_core(m):return any(p.search(m) for p in core) and not any(p.search(m) for p in elab)
graph={}
with tarfile.open(fileobj=io.BytesIO(git('archive',REF,'Solidity'))) as archive:
    for entry in archive:
        if entry.isfile() and entry.name.endswith('.lean') and not entry.name.startswith('Solidity/Scratch/'):
            graph[entry.name[:-5].replace('/','.')]=re.findall(r'^import\s+(\S+)',archive.extractfile(entry).read().decode(),re.M)
edges=sorted(set((m,n) for m,imports in graph.items() if is_core(m) for n in imports if n in graph and not is_core(n)))
raw=(json.dumps(edges,indent=2)+'\n').encode()
assert len(edges)==95 and hashlib.sha256(raw).hexdigest()=='d202b21ddde800b40237b9c4a95482c17b8d5ea8d2c78c1b42e4bad7344ac80b'
sys.stdout.buffer.write(raw)
