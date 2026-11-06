#!/usr/bin/env python3
"""Test H44 storage binding after the compact commit; restore every mutation."""
import copy,hashlib,json,os,pathlib,runpy,tempfile
from unittest.mock import patch
ROOT=pathlib.Path(__file__).resolve().parents[3]
F=pathlib.Path(__file__).resolve().parent
nl=runpy.run_path(str(ROOT/'scripts/check-sol-numeric-literals.py'))
lib=runpy.run_path(str(ROOT/'tests/sol-numeric-literals/packetlib.py'))
def reject(action,text):
 try:action()
 except ValueError as error:assert text in str(error),str(error)
 else:raise AssertionError('storage mutation accepted: '+text)
def main():
 nl['validate_committed_inputs']();bindings=lib['h44_bulk_bindings']();assert bindings
 path=F/'h44-bulk-manifest.json';original=path.read_bytes();manifest=json.loads(original)
 try:
  path.write_bytes(original+b'\n');reject(lib['h44_bulk_bindings'],'uncommitted H44 manifest')
 finally:path.write_bytes(original)
 directory=pathlib.Path(os.environ.get('SOL_NL_BULK_DIR',manifest['directory']))
 index=json.loads((directory/'files.json').read_text())
 with tempfile.TemporaryDirectory(prefix='h44-storage-') as td:
  temporary=pathlib.Path(td)
  absent=temporary/'absent'
  missing=copy.deepcopy(manifest);missing['directory']=str(absent)
  exists=pathlib.Path.exists
  with patch.dict(os.environ,clear=False):
   os.environ.pop('SOL_NL_BULK_DIR',None)
   with patch.object(pathlib.Path,'exists',lambda p:False if str(p)=='/workspace/.setup/activate.sh' else exists(p)):
    assert lib['verify_h44_bulk'](missing)=={}
   reject(lambda:lib['verify_h44_bulk'](missing),'H44 VM bulk directory missing')
   os.environ['SOL_NL_BULK_DIR']=str(absent)
   with patch.object(pathlib.Path,'exists',lambda p:False if str(p)=='/workspace/.setup/activate.sh' else exists(p)):
    reject(lambda:lib['verify_h44_bulk'](missing),'H44 VM bulk directory missing')
  saved=os.environ.get('SOL_NL_BULK_DIR');os.environ['SOL_NL_BULK_DIR']=td
  try:
   for kind in ['digest','duplicate','parent','code']:
    candidate=copy.deepcopy(index);m=copy.deepcopy(manifest)
    if kind=='duplicate':candidate['files'].append(dict(candidate['files'][0]))
    elif kind=='parent':candidate['files'][0]['logical_path']='tests/sol-numeric-literals/evidence/../../outside.json'
    elif kind=='code':candidate['files'][0]['logical_path']='scripts/check-sol-numeric-literals.py'
    data=(json.dumps(candidate,indent=2)+'\n').encode();(temporary/'files.json').write_bytes(data)
    m['file_manifest']=dict(bytes=len(data),sha256=hashlib.sha256(data).hexdigest())
    if kind=='digest':m['file_manifest']['sha256']='0'*64
    message={'digest':'digest differs','duplicate':'duplicate data path','parent':'non-data path','code':'non-data path'}[kind]
    reject(lambda:lib['verify_h44_bulk'](m),message)
  finally:
   if saved is None:os.environ.pop('SOL_NL_BULK_DIR',None)
   else:os.environ['SOL_NL_BULK_DIR']=saved
 path=F/'registration-current.patch';original=path.read_bytes();relative=str(path.relative_to(ROOT))
 try:
  path.write_bytes(original+b'\n');reject(nl['validate_committed_inputs'],'H44 required data differs '+relative)
 finally:path.write_bytes(original)
 nl['validate_committed_inputs']()
 print('PASS: off-VM absence reported, VM absence refused; committed bulk bindings; uncommitted manifest, digest, duplicate, traversal, code-path and direct-input mutations refused; all files restored')
if __name__=='__main__':main()
