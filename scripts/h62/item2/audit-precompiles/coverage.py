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
data_covered={
 'Solidity.Precompiles.readPad_length':'readPad_length_data',
 'Solidity.Precompiles.toBE_length':'toBE_length_data',
 'Solidity.Precompiles.mapM_eq_none_iff':'mapM_eq_none_iff_data',
 'Solidity.Precompiles.ecrecover_isSome':'ecrecover_isSome_data',
 'Solidity.Precompiles.sha256_isSome':'sha256_isSome_data',
 'Solidity.Precompiles.ripemd160_isSome':'ripemd160_isSome_data',
 'Solidity.Precompiles.identity_eq':'identity_eq_data',
 'Solidity.Precompiles.Modexp.modexp_eq_none_iff':'modexp_eq_none_iff_data',
 'Solidity.Precompiles.Bn254.add_eq_none_iff':'bn_add_eq_none_iff_data',
 'Solidity.Precompiles.Bn254.mul_eq_none_iff':'bn_mul_eq_none_iff_data',
 'Solidity.Precompiles.Bn254.onCurve_aff':'bn_onCurve_aff_data',
 'Solidity.Precompiles.Bn254.decodeG1_eq_none_iff':'bn_decodeG1_eq_none_iff_data',
 'Solidity.Precompiles.Bn254.pairing_eq_none_iff':'bn_pairing_eq_none_iff_data',
 'Solidity.Precompiles.Blake2f.compress_size':'blake_compress_size_data',
 'Solidity.Precompiles.Blake2f.flatMap_length':'blake_flatMap_length_data',
 'Solidity.Precompiles.Blake2f.blake2f_eq_none_iff':'blake_eq_none_iff_data',
 'Solidity.Precompiles.P256.p256Verify_isSome':'p256_isSome_data'}
assert not (set(covered) & set(data_covered))
for name,witness in data_covered.items(): covered[name]=(witness,'DataWitnesses','data-final')
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
   row.update(status=('data-input-checked' if d['name'] in data_covered else 'witness-checked'),hypothesis_kind=('no proof hypotheses; concrete joint data domain' if d['name'] in data_covered else 'per-input proof hypotheses jointly witnessed'),witness='H62.AuditPrecompiles.'+name,proof_source_sha256=hashlib.sha256(proof.read_bytes()).hexdigest(),gate=gate)
  rows.append(row)
assert len(rows)==138 and len({r['name'] for r in rows})==138
assert len(covered)==sum(r['status']!='pending' for r in rows)==24
assert sum(r['status']=='witness-checked' for r in rows)==7
assert sum(r['status']=='data-input-checked' for r in rows)==17
value=dict(status='blocked',statements=138,applicability_checked=24,witness_checked=7,data_input_checked=17,pending=114,rows=rows,
 boundary='Exactly-once source ledger: seven proof-premise witnesses and seventeen unconditional data-domain samples, kept distinct. No owner compiler-success or full audit pass.')
(a.evidence/'statement-coverage.json').write_text(json.dumps(value,indent=2)+'\n')
print('PARTIAL_LEDGER statements=138 applicability_checked=24 proof_premises=7 data_inputs=17 pending=114; full gate BLOCKED')
