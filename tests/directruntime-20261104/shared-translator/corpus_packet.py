"""Integrity gate for the external frozen census packet; no translation code."""
from pathlib import Path
import hashlib,json
OWNED=Path(__file__).resolve().parent;ROOT=OWNED.parents[2]
def sha(path):
 h=hashlib.sha256()
 with path.open('rb') as f:
  for block in iter(lambda:f.read(1048576),b''):h.update(block)
 return h.hexdigest()
def verified_packet(manifestName,directory):
 packet=json.loads((OWNED/manifestName).read_text())
 source=OWNED/'artifacts'/directory;archive=ROOT/packet['archiveRelative']
 assert archive.resolve().is_relative_to((OWNED/'artifacts').resolve()) and not source.is_symlink()
 assert archive.stat().st_size==packet['archiveBytes'] and sha(archive)==packet['archiveSha256'], 'packet archive integrity mismatch'
 index=source/'files.json';assert sha(index)==packet['filesManifestSha256'], 'packet files manifest integrity mismatch'
 expected=set();totalBytes=0
 for row in json.loads(index.read_text())['files']:
  totalBytes+=row['bytes']
  path=source/row['path'];assert row['path'] not in expected;expected.add(row['path'])
  assert not path.is_symlink() and path.resolve().is_relative_to(source.resolve())
  assert path.stat().st_size==row['bytes'] and sha(path)==row['sha256']
 assert expected=={str(p.relative_to(source)) for p in source.rglob('*') if p.is_file() and p!=index}
 assert len(expected)==packet['dataFiles'] and totalBytes==packet['dataBytes']
 return source,packet

def verified_corpus():
 return verified_packet('corpus-inventory-manifest.json','corpus-inventory')
def verified_readers():
 return verified_packet('corpus-readers-manifest.json','corpus-readers')
