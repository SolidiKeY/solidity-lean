#!/usr/bin/env python3
"""Install the repository's frozen optional reference packages outside Git.
Caller holds the writer lock. This is external-test provisioning, not a proof.
"""
import argparse, hashlib, json, pathlib, subprocess
p=argparse.ArgumentParser();p.add_argument('--runtime',required=True);a=p.parse_args()
root=pathlib.Path(__file__).resolve().parents[4];dest=pathlib.Path(a.runtime).resolve();dest.mkdir(parents=True,exist_ok=True)
base='c6f550e281a7e5affa9a99bc2cdaed556dec00e4';receipts=[]
for name in ['package.json','package-lock.json']:
 data=subprocess.check_output(['git','show',base+':scripts/evm-vectors/'+name],cwd=root)
 (dest/name).write_bytes(data);receipts.append(dict(file=name,source='scripts/evm-vectors/'+name,base=base,sha256=hashlib.sha256(data).hexdigest()))
subprocess.run(['npm','ci','--ignore-scripts','--no-audit','--no-fund'],cwd=dest,check=True)
(dest/'provenance.json').write_text(json.dumps(receipts,indent=2)+'\n')
print(json.dumps(dict(runtime=str(dest),packages='frozen optional EthereumJS reference dependencies',proof=False)))
