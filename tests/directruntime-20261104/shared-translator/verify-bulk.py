"""Verify the H44 archive and every extracted data file before using controls.
Extract the recorded archive at the recorded repository-relative packet root.
No download or implicit fallback to historical tracked fixtures is performed.
"""
from pathlib import Path
import hashlib,json
owned=Path(__file__).resolve().parent;root=owned.parents[2]
record=json.loads((owned/'bulk-manifest.json').read_text())
bulk=owned/'artifacts/h68-bulk'
def sha(path):
 h=hashlib.sha256()
 with path.open('rb') as f:
  for block in iter(lambda:f.read(1048576),b''):h.update(block)
 return h.hexdigest()
archive=root/record['archiveRelative']
assert archive.resolve().is_relative_to((owned/'artifacts').resolve())
assert archive.stat().st_size==record['archiveBytes'] and sha(archive)==record['archiveSha256'], 'archive hash/size mismatch'
index=bulk/'files.json'
assert sha(index)==record['filesManifestSha256'], 'extracted file inventory mismatch'
entries=json.loads(index.read_text())['files'];seen=set()
for row in entries:
 path=bulk/row['path']
 assert not path.is_symlink() and path.resolve().is_relative_to(bulk.resolve()), 'unsafe packet path'
 assert row['path'] not in seen;seen.add(row['path'])
 assert path.stat().st_size==row['bytes'] and sha(path)==row['sha256'], 'extracted data mismatch: '+row['path']
actual={str(x.relative_to(bulk)) for x in bulk.rglob('*') if x.is_file() and x!=index}
assert actual==seen and sum(row['bytes'] for row in entries)==record['dataBytes']
print(json.dumps({'status':'pass','files':len(entries),'dataBytes':record['dataBytes'],'archiveBytes':record['archiveBytes'],'archiveSha256':record['archiveSha256'],'boundary':'External control data integrity; not proof closure or source/backend preservation.'}))
