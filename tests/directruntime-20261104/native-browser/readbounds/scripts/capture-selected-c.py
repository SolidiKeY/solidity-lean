"""Guard reviewable closure provenance: retain all selected compiled C bytes.

Reconstructs the already audited selection and checks every body against both
fresh build manifests and the independent object inventory. No checking request,
compiler, Lean frontend or benchmark is executed.
"""
from pathlib import Path
import hashlib, json, re, subprocess, tarfile, types
if not __debug__:raise RuntimeError("provenance validation requires Python assertions enabled")
root = Path.cwd()
base = root / '.lake/native-browser-readbounds-6513'
out = Path('/workspace/scratch/browser-chain/readbounds-6513')
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
n = json.loads((base/'native/build.json').read_text())
w = json.loads((base/'direct/build.json').read_text())
assert sha(base/'native/direct-check') == n['executable']
assert sha(base/'direct/direct.wasm') == w['wasm']
helper_path = root/'scripts/direct-runtime-closure.py'
assert sha(helper_path) == n['closureScriptSha256'] == w['closureScriptSha256']
helper = types.ModuleType('closure'); helper.__file__ = str(helper_path)
exec(compile(helper_path.read_bytes(), str(helper_path), 'exec'), helper.__dict__)
inputs, stats = helper.extract(root, base/'native/runtime', native_roots=set(n['closure']['nativeRoots']))
assert stats == n['closure'] == w['closure']
records = {x['module']: x for x in json.loads((out/'closure/selected-C-objects.json').read_text())}
wasm = {x['module']: x for x in w['modules']}
assert set(records) == set(wasm) == {x[0] for x in inputs}
folder = out/'selected-C'; folder.mkdir()
manifest = []
for module, text, original, expected in inputs:
    assert re.fullmatch(r'[A-Za-z_][A-Za-z_0-9.]*', module)
    data = text.encode(); digest = hashlib.sha256(data).hexdigest()
    assert sha(original) == expected == records[module]['originalCSha256']
    assert digest == records[module]['compiledCSha256'] == wasm[module]['compiledCSha256']
    path = folder/(module+'.c')
    with path.open('xb') as f: f.write(data)
    manifest.append({'module': module, 'path': path.name, 'sha256': digest, 'bytes': len(data)})
for e in n['sourceFiles']:
    assert sha(root/(e['module'].replace('.', '/')+'.lean')) == e['sourceSha256']
(folder/'manifest.json').write_text(json.dumps(manifest, indent=2)+'\n')
archive = base/'selected-C.tar.gz'
with tarfile.open(archive, 'x:gz') as tf: tf.add(folder, arcname='selected-C')
with tarfile.open(archive, 'r:gz') as tf:
    for e in manifest:
        assert hashlib.sha256(tf.extractfile('selected-C/'+e['path']).read()).hexdigest() == e['sha256']
print(json.dumps({'modules': len(manifest), 'archive': str(archive), 'sha256': sha(archive),
                 'boundary': 'Exact selected compiled C capture; not source/compiler/native semantic preservation.'}))
