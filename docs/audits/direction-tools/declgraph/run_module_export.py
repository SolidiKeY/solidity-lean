#!/usr/bin/env python3
"""Export per-module native constants and bind outputs to producer inputs.
Requires the external writer lock, pinned lean on PATH, and a resolved cache view.
Imports compiled initializers/extensions; no project source commands are elaborated.
"""
import argparse,hashlib,json,os,pathlib,subprocess
HERE=pathlib.Path(__file__).resolve().parent

def sha(path):
 h=hashlib.sha256()
 with path.open('rb') as f:
  for block in iter(lambda:f.read(1048576),b''):h.update(block)
 return h.hexdigest()

def main():
 p=argparse.ArgumentParser();p.add_argument('--modules',type=pathlib.Path,required=True);p.add_argument('--view',type=pathlib.Path,required=True);p.add_argument('--output',type=pathlib.Path,required=True);a=p.parse_args()
 producer=HERE/'ModuleExport.lean';inputs=dict(producer_sha256=sha(producer),modules_sha256=sha(a.modules))
 env=dict(os.environ,LEAN_PATH=str(a.view.resolve()),LEAN_NUM_THREADS='1')
 version=subprocess.check_output(['lean','--version'],text=True).strip()
 assert 'version 4.24.0,' in version and '797c613' in version,'Pinned native import model requires Lean 4.24.0 / 797c613'
 subprocess.run(['lean','--tstack=131072','-M10000','-j1','--run',str(producer),str(a.modules.resolve()),str(a.output.resolve())],env=env,check=True)
 assert inputs==dict(producer_sha256=sha(producer),modules_sha256=sha(a.modules)),'Inputs changed while parsing'
 receipt=dict(inputs,lean=version,reference_view=str(a.view.resolve()),index_sha256=sha(a.output))
 pathlib.Path(str(a.output)+'.receipt.json').write_text(json.dumps(receipt,indent=2,sort_keys=True)+'\n')
 print('MODULE_EXPORT_RECEIPT_PASS')
if __name__=='__main__':main()
