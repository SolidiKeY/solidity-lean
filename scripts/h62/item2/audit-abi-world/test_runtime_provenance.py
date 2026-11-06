#!/usr/bin/env python3
"""Mutation controls for the external replay's provenance chain; no Lean."""
import json,subprocess,tempfile
from pathlib import Path
root=Path(__file__).resolve().parents[4];e=Path('/workspace/audit-abi-world-evidence')
script=root/'scripts/h62/item2/audit-abi-world/replay.mjs'
with tempfile.TemporaryDirectory(prefix='runtime-negative-',dir=e) as directory:
 folder=Path(directory)
 vectors=json.loads((e/'runtime-vectors.json').read_text());vectors[0]['code'][0]=0
 changed=folder/'vectors.json';changed.write_text(json.dumps(vectors))
 run=subprocess.run(['node','--max-old-space-size=512',str(script),str(changed),str(e/'reference'),str(e/'runtime-vectors-provenance.json')],capture_output=True,text=True)
 assert run.returncode!=0 and not run.stdout.strip(),'altered vectors accepted'
 print('altered vectors: rejected')
 provenance=json.loads((e/'runtime-vectors-provenance.json').read_text())
 key='tests/h62/item2/audit-abi-world/H62AbiWorld/SuccessContracts.lean';provenance['local_sources'][key]='0'*64
 changed=folder/'provenance.json';changed.write_text(json.dumps(provenance))
 run=subprocess.run(['node','--max-old-space-size=512',str(script),str(e/'runtime-vectors.json'),str(e/'reference'),str(changed)],capture_output=True,text=True)
 assert run.returncode!=0 and not run.stdout.strip(),'stale dependency accepted'
 print('stale imported source: rejected')
