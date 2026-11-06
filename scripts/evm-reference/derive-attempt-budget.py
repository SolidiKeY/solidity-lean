#!/usr/bin/env python3
"""Derive an exact audited CJS copy; never patch the original dependency tree."""
from pathlib import Path
import hashlib,json,shutil,subprocess,sys
root=Path(__file__).resolve().parent
base,out=map(lambda x:Path(x).resolve(),sys.argv[1:])
assert base!=out and base not in out.parents and not out.exists(), 'new output outside original tree required'
sha=lambda b:hashlib.sha256(b).hexdigest()
pins=json.loads((root/'attempt-budget-pins.json').read_text())
files=sorted(f for f in base.rglob('*') if f.is_file())
manifest=''.join(sha(f.read_bytes())+'  '+f.relative_to(base).as_posix()+'\n' for f in files)
assert len(files)==pins['baseTreeFiles'] and sha(manifest.encode())==pins['baseTreeManifestSHA256'], 'base tree drift'
patch=root/'attempt-budget-engine.patch';assert sha(patch.read_bytes())==pins['patchSHA256']
for x in pins['files']:assert sha((base/x['path']).read_bytes())==x['originalSHA256']
shutil.copytree(base,out,symlinks=True)
subprocess.run(['git','apply','--unsafe-paths','--directory',str(out),str(patch)],check=True)
changed={x['path']:x for x in pins['files']}
for f in files:
 rel=f.relative_to(base).as_posix();expected=changed[rel]['patchedSHA256'] if rel in changed else sha(f.read_bytes())
 assert sha((out/rel).read_bytes())==expected,rel

after=sorted(f for f in base.rglob('*') if f.is_file())
assert len(after)==pins['baseTreeFiles'] and sha(''.join(sha(f.read_bytes())+'  '+f.relative_to(base).as_posix()+'\n' for f in after).encode())==pins['baseTreeManifestSHA256'], 'base changed during derivation'
(out.parent/'attempt-budget-derivation.json').write_text(json.dumps({'base':str(base),'derived':str(out),'pins':pins,'allOtherFilesIdentical':True},indent=2)+'\n')
print('derived exact pinned artifact; original tree unchanged')
