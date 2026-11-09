"""Guards H77 sourceBuild1e8 archive identity against current-reader freshness claims.
Reads archives only; never extracts or executes delivered code or stopped benchmarks.
"""
import argparse, hashlib, json, tarfile
from pathlib import Path, PurePosixPath
ROOT = Path(__file__).resolve().parent
DEFAULT = Path('/workspace/h62-coordinator-inputs/router-20261107T003952Z/sourceBuild1e8')
PINS = {
 'evidence.tar.gz': '786fa58c55792dc2c41cbbf54f7fcf739df9bf844c0306a590be00b1cda5a8eb',
 'runtime-artifacts.tar.gz': 'eaf07aed1360852ec02e142ea35c64bcb5320541c31810c76158cd392900f863',
 'files.json': 'd5e0b176ca61e57fdf8ecb1f67c9f7ca43c33255a0a7303b6f0afd2703f2fe07'}
def digest(data): return hashlib.sha256(data).hexdigest()
def require(condition, message):
 if not condition: raise ValueError(message)
def members(tar):
 entries = tar.getmembers()
 names = [m.name for m in entries]
 require(len(names) == len(set(names)), 'duplicate archive member')
 for m in entries:
  p = PurePosixPath(m.name)
  require(m.isfile() and not p.is_absolute() and '..' not in p.parts and
          str(p) == m.name and m.name not in ('', '.'), 'unsafe archive member')
 return {m.name:m for m in entries}
def verify(directory):
 for name, sha in PINS.items():
  with (directory/name).open('rb') as stream:
   actual = hashlib.file_digest(stream, 'sha256').hexdigest()
  require(actual == sha, 'outer archive/manifest hash: ' + name)
 manifest_raw = (directory/'files.json').read_bytes()
 records = json.loads(manifest_raw)
 require(len(records) == 505, 'evidence denominator')
 # Producer absolute paths are archive lookup keys only, never extraction targets.
 expected = {r['path'].lstrip('/'):r for r in records}
 require(len(expected) == len(records), 'duplicate manifest path')
 with tarfile.open(directory/'evidence.tar.gz', 'r:gz') as tar:
  entries = members(tar)
  require(set(entries) == set(expected) | {'files.json'}, 'evidence member set')
  require(tar.extractfile('files.json').read() == manifest_raw, 'embedded manifest')
  for name,r in expected.items():
   require(entries[name].size == r['bytes'], 'evidence member size: ' + name)
   with tar.extractfile(name) as stream:
    require(hashlib.file_digest(stream, 'sha256').hexdigest() == r['sha256'],
            'evidence member hash: ' + name)
 with tarfile.open(directory/'runtime-artifacts.tar.gz', 'r:gz') as tar:
  entries = members(tar)
  require(set(entries) == {'native/direct-check','native/build.json','direct/direct.wasm',
                          'direct/direct.js','direct/build.json'}, 'runtime member set')
  native = json.load(tar.extractfile('native/build.json'))
  wasm = json.load(tar.extractfile('direct/build.json'))
  require(native['sourceFiles'] == wasm['sourceFiles'] and
          len(native['sourceFiles']) == 343 and
          len({r['module'] for r in native['sourceFiles']}) == 343,
          'recorded source array parity/unique modules')
  binaries = {}
  for name,sha in [('native/direct-check',native['executable']),
                   ('direct/direct.wasm',wasm['wasm']),('direct/direct.js',wasm['javascript'])]:
   with tar.extractfile(name) as stream:
    require(hashlib.file_digest(stream,'sha256').hexdigest() == sha, 'runtime hash: ' + name)
   binaries[name] = {'sha256':sha,'bytes':entries[name].size}
 return {'guardedRegression':'Historical sourceBuild1e8 intake is not current H90 qualification',
         'inputDirectory':str(directory),'inputs':PINS,'evidenceFiles':505,
         'recordedSourceModules':343,'recordedSourceArraysEqual':True,'binaries':binaries,
         'gitSourceIdentityVerified':False,'execution':False,'extraction':False,
         'boundary':'Archive/member/build-manifest consistency only. No Git source verification, '
                    'fresh-reader qualification, runtime closure, compiler preservation, '
                    'performance acceptance or whole-goal completion.'}
if __name__ == '__main__':
 parser = argparse.ArgumentParser()
 parser.add_argument('--directory', type=Path, default=DEFAULT)
 parser.add_argument('--report', type=Path)
 args = parser.parse_args()
 result = verify(args.directory)
 raw = json.dumps(result,indent=2)+'\n'
 if args.report: args.report.write_text(raw)
 else: print(raw,end='')
