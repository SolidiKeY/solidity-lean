#!/usr/bin/env python3
"""Accept current formal-success and external frame tests, keeping their boundary."""
import argparse,hashlib,json,subprocess,sys
from pathlib import Path
sys.dont_write_bytecode=True
from receipts import checked_receipt
root=Path(__file__).resolve().parents[4];e=Path('/workspace/audit-abi-world-evidence')
parser=argparse.ArgumentParser();parser.add_argument('--report',type=Path,default=e/'reference-replay.json');args=parser.parse_args()
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
folder=root/'tests/h62/item2/audit-abi-world/H62AbiWorld'
success,_=checked_receipt(folder/'SuccessContracts.lean',e)
checked_receipt(folder/'RuntimeVectors.lean',e)
required={'return_total','supported_nonempty','reject_all_fails','always_revert_fails','checked_add_assembly_total','panic_handler_total','zero_receiver_fails'}
actual={x['message'].split("'")[1].removeprefix('H62.AbiWorld.Success.') for x in success['items'] if x['severity']=='info' and 'axioms' in x['message']}
assert actual==required
provenance=json.loads((e/'runtime-vectors-provenance.json').read_text())
assert provenance['vectors_sha256']==sha(e/'runtime-vectors.json')
for pathkey,hashkey in [('source','source_sha256'),('diagnostic','diagnostic_sha256'),('resource','resource_sha256')]:assert sha(Path(provenance[pathkey]))==provenance[hashkey]
for name,digest in {**provenance['local_sources'],**provenance['support']}.items():assert sha(root/name)==digest
report=json.loads(args.report.read_text())
assert report['status']=='pass' and report['fork']=='osaka'
assert report['runnerSha256']==sha(root/'scripts/h62/item2/audit-abi-world/replay.mjs')
assert report['vectorsSha256']==sha(e/'runtime-vectors.json')
assert report['provenanceSha256']==sha(e/'runtime-vectors-provenance.json')
assert report['lockSha256']==sha(e/'reference/package-lock.json')
assert report['versions']=={'@ethereumjs/evm':'10.1.3','@ethereumjs/common':'10.1.2','@ethereumjs/util':'10.1.2'}
vectors={v['name']:v for v in json.loads((e/'runtime-vectors.json').read_text())}
assert len(report['rows'])==len(vectors)==10
assert {r['name'] for r in report['rows']}==set(vectors)
for row in report['rows']:
 assert row['codeSha256']==hashlib.sha256(bytes(vectors[row['name']]['code'])).hexdigest()
 assert int(row['exactGas'])>0 and row['oneBelowKind']=='out of gas' and row['zeroGasKind']=='out of gas'
assert all(report['controls'].values())
resource=json.loads((e/'reference-replay-resource.json').read_text())
assert resource['guard_sha256']==sha(root/'scripts/h62/item2/audit-abi-world/bounded.py')
assert resource['reason'] is None and resource['exit_code']==0 and resource['cleanup_complete'] is True
assert resource['minimum_available_bytes']>=4*1024**3 and resource['swap_active_seen'] is False
assert resource['stdout_sha256']==sha(args.report) and resource['stdout_file']==str(args.report.resolve())
assert resource['command']==['node','--max-old-space-size=512','scripts/h62/item2/audit-abi-world/replay.mjs',str(e/'runtime-vectors.json'),str(e/'reference'),str(e/'runtime-vectors-provenance.json')]
print(json.dumps(dict(success_gate_complete=True,formal_success_theorems=7,external_programs=10,
 boundary='Formal Slice/typed-run success plus external isolated-frame gas/fork tests; no general compiler or gas/fork bridge claim')))
