#!/usr/bin/env python3
"""Check real recovery receipts and reject tampered identities/unsafe paths.
No proof execution or artifact mutation; use the repository writer lock.
"""
import argparse,json,pathlib,runpy,subprocess,sys,tempfile,types
HERE=pathlib.Path(__file__).resolve().parent

def main():
 p=argparse.ArgumentParser();p.add_argument('--receipt',type=pathlib.Path,required=True);p.add_argument('--producer-commit',required=True);p.add_argument('--summary',type=pathlib.Path,default=HERE/'warm-check-summary.json');args=p.parse_args()
 warm=runpy.run_path(str(HERE/'warm_checks.py'));api=runpy.run_path(str(HERE/'audit.py'));receipt=json.loads(args.receipt.read_text());data=json.loads(args.summary.read_text())
 a=types.SimpleNamespace(producer_commit=args.producer_commit,verify_receipt=args.receipt,source_root=pathlib.Path(receipt['source_root']).resolve(),view=pathlib.Path(receipt['input_view']).resolve(),out_view=pathlib.Path(receipt['output_view']).resolve(),summary=args.summary,logs=args.receipt.parent)
 api['assert_sources'](a.source_root);warm['verify_recovery'](a,api,data['lean'])
 with tempfile.TemporaryDirectory(prefix='declgraph-warm-guards-',dir=HERE.parents[3]/'.lake/refactor-cache') as directory:
  d=pathlib.Path(directory);bad=d/'receipt.json'
  def reject(expected):
   try:warm['verify_recovery'](a,api,data['lean'])
   except AssertionError as e:assert expected in str(e),str(e)
   else:raise AssertionError('Tampered receipt accepted')
  changed=json.loads(args.receipt.read_text());changed['producer_sha256']='0'*64;bad.write_text(json.dumps(changed));a.verify_receipt=bad;reject('Original producer differs')
  changed=json.loads(args.receipt.read_text());changed['builds'][0]['olean_sha256']='0'*64;bad.write_text(json.dumps(changed));reject('Recovered artifact differs')
  input_view=d/'input';input_view.mkdir();nested=input_view/'nested'
  command=[sys.executable,'-I',str(HERE/'warm_checks.py'),'--source-root',str(a.source_root),'--view',str(input_view),'--out-view',str(nested),'--logs',str(d/'logs'),'--summary',str(d/'summary.json')]
  result=subprocess.run(command,text=True,capture_output=True,timeout=60)
  assert result.returncode!=0 and 'Output view must be outside input view' in result.stderr,result.stdout+result.stderr
  assert not nested.exists(),'Unsafe output was created before rejection'
 print('WARM_RECEIPT_GUARDS_PASS immutable_producer artifact_integrity nested_output_rejection')
if __name__=='__main__':main()
