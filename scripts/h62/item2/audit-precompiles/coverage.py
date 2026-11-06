#!/usr/bin/env python3
"""Exactly-once statement ledger. Passing partial checks never promote full status."""
import argparse, hashlib, json, pathlib
from census import census, ROOT
p=argparse.ArgumentParser();p.add_argument('--evidence',type=pathlib.Path,required=True)
a=p.parse_args(); c=census(); rows=[]
covered={
 'Solidity.Precompiles.words_mono':('words_mono_witness','BasicWitnesses','basic-final'),
 'Solidity.Precompiles.sha256Gas_mono':('sha256Gas_mono_witness','BasicWitnesses','basic-final'),
 'Solidity.Precompiles.ripemd160Gas_mono':('ripemd160Gas_mono_witness','BasicWitnesses','basic-final'),
 'Solidity.Precompiles.identityGas_mono':('identityGas_mono_witness','BasicWitnesses','basic-final'),
 'Solidity.Precompiles.Modexp.modexp_length':('modexp_length_witness','CoreWitnesses','core-final'),
 'Solidity.Precompiles.Modexp.gas_ge':('modexp_gas_ge_witness','CoreWitnesses','core-final'),
 'Solidity.Precompiles.Blake2f.blake2f_length':('blake2f_length_witness','CoreWitnesses','core-final')}
for f in c['files']:
 for d in f['declarations']:
  row=dict(name=d['name'],file=f['path'],owner=f['owner'],signature=d['signature'],signature_sha256=d['signature_sha256'],status='pending',witness=None)
  if d['name'] in covered:
   name,src,gate=covered[d['name']]
   proof=ROOT/'tests/h62/item2/audit-precompiles'/f'{src}.lean'
   meta=json.loads((a.evidence/f'{gate}.json').read_text());log=(a.evidence/f'{gate}.log').read_text()
   assert all(pathlib.Path(path).is_file() and hashlib.sha256(pathlib.Path(path).read_bytes()).hexdigest()==digest for path,digest in meta['input_sha256'].items())
   assert meta['input_sha256'][str(proof)]==hashlib.sha256(proof.read_bytes()).hexdigest() and meta['inputs_unchanged']
   assert meta['exit']==0 and not meta.get('resource_stop') and not meta['timeout']
   assert meta['cwd']==str(ROOT) and meta['command'][-1]==str(proof.relative_to(ROOT))
   assert f"H62.AuditPrecompiles.{name}'" in log and 'sorryAx' not in log
   row.update(status='witness-checked',witness='H62.AuditPrecompiles.'+name,proof_source_sha256=hashlib.sha256(proof.read_bytes()).hexdigest(),gate=gate)
  rows.append(row)
assert len(rows)==138 and len({r['name'] for r in rows})==138
assert len(covered)==sum(r['status']=='witness-checked' for r in rows)
value=dict(status='blocked',statements=138,witness_checked=7,pending=131,rows=rows,
 boundary='Source ledger and seven checked simultaneous witnesses only; no overall audit or compiler correctness pass.')
(a.evidence/'statement-coverage.json').write_text(json.dumps(value,indent=2)+'\n')
print('PARTIAL_LEDGER statements=138 witness_checked=7 pending=131; full gate BLOCKED')
