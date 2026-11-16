#!/usr/bin/env python3
"""Run the source-syntax census serially and bind outputs to producer inputs.
Requires the external writer lock, pinned lean on PATH, and a resolved cache view.
Recognized top-level checks are not replayed. Scope/grammar replay may invoke
term elaborators. Does not assert complete semantic root coverage.
"""
import argparse,hashlib,json,os,pathlib,subprocess
HERE=pathlib.Path(__file__).resolve().parent

def sha(path):
 h=hashlib.sha256()
 with path.open('rb') as f:
  for block in iter(lambda:f.read(1048576),b''):h.update(block)
 return h.hexdigest()

def main():
 p=argparse.ArgumentParser();p.add_argument('--modules',type=pathlib.Path,required=True);p.add_argument('--paths',type=pathlib.Path,required=True);p.add_argument('--view',type=pathlib.Path,required=True);p.add_argument('--output',type=pathlib.Path,required=True);a=p.parse_args()
 producer=HERE/'Commands.lean';inputs=dict(producer_sha256=sha(producer),modules_sha256=sha(a.modules),paths_sha256=sha(a.paths))
 env=dict(os.environ,LEAN_PATH=str(a.view.resolve()),LEAN_NUM_THREADS='1')
 version=subprocess.check_output(['lean','--version'],text=True).strip()
 subprocess.run(['lean','--tstack=131072','-j1','--run',str(producer),str(a.modules.resolve()),str(a.paths.resolve()),str(a.output.resolve())],env=env,check=True)
 assert inputs==dict(producer_sha256=sha(producer),modules_sha256=sha(a.modules),paths_sha256=sha(a.paths)),'Inputs changed while parsing'
 receipt=dict(inputs,lean=version,reference_view=str(a.view.resolve()),index_sha256=sha(a.output),compiler_sha256=sha(pathlib.Path(str(a.output)+'.compiler.json')))
 pathlib.Path(str(a.output)+'.receipt.json').write_text(json.dumps(receipt,indent=2,sort_keys=True)+'\n')
 print('COMMAND_INDEX_RECEIPT_PASS')
if __name__=='__main__':main()
