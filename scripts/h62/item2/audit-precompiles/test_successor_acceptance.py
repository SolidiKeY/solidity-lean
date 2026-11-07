#!/usr/bin/env python3
"""Reject failed, stale, wrong-package and incomplete private-type receipts; no Lean jobs."""
import hashlib,json,pathlib,shutil,tempfile,unittest
import successor_acceptance as audit
E=audit.ROOT/'tests/h62/item2/audit-precompiles/successor-evidence'
class ReceiptTests(unittest.TestCase):
 def setUp(self):
  self.temp=tempfile.TemporaryDirectory(prefix='acceptance-',dir=E);self.e=pathlib.Path(self.temp.name)
  for stem in ['basic-final','core-final','data-final','type-fidelity-final','identity-final424','bridge-fidelity-final424','stipend-control424','keysort424','imported-bridge-axioms424','bytes-gas-final424','header-short-zero424','osaka-ledger-final424','bls-ledger-final424','point-ledger-final424','stipend-ledger424','remaining-fidelity-final424','point-success-final424']:
   for ext in ['.json','.log']:shutil.copyfile(E/(stem+ext),self.e/(stem+ext))
 def tearDown(self):self.temp.cleanup()
 def alter(self,fn):
  p=self.e/'identity-final424.json';m=json.loads(p.read_text());fn(m);p.write_text(json.dumps(m))
 def rejected(self):
  with self.assertRaises(AssertionError):audit.generate(self.e)
 def test_valid_partial_boundary(self):
  r=audit.generate(self.e);self.assertEqual(r['counts']['case_accounted'],138);self.assertEqual(r['pending'],0);self.assertFalse(r['owner_compiler_success_supplied'])
 def test_failed_job(self):self.alter(lambda m:m.update(exit=1));self.rejected()
 def test_timeout(self):self.alter(lambda m:m.update(timeout=True));self.rejected()
 def test_resource_stop(self):self.alter(lambda m:m.update(resource_stop='cap'));self.rejected()
 def test_wrong_package(self):self.alter(lambda m:m.update(cwd=str(audit.ROOT)));self.rejected()
 def test_stale_proof(self):
  self.alter(lambda m:m['input_sha256'].update({str(audit.ROOT/'tests/h62/item2/audit-precompiles/BridgeIdentityWitnesses.lean'):'0'*64}));self.rejected()
 def test_stale_frozen_input(self):
  def change(m):m['frozen_input_sha256'][next(iter(m['frozen_input_sha256']))]='0'*64
  self.alter(change);self.rejected()
 def test_missing_private_constant(self):
  p=self.e/'bridge-fidelity-final424.log';s=p.read_text();p.write_text('\n'.join(x for x in s.splitlines() if 'PRIVATE_CONSTANT SolidityBridge.PrecompileAgreement.list_loop:' not in x));m=self.e/'bridge-fidelity-final424.json';x=json.loads(m.read_text());x['log_sha256']=hashlib.sha256(p.read_bytes()).hexdigest();m.write_text(json.dumps(x));self.rejected()
 def test_omitted_frozen_closure(self):
  def change(m):m.pop('frozen_input_sha256');m.pop('frozen_inputs_unchanged')
  self.alter(change);self.rejected()
 def test_same_count_wrong_frozen_paths(self):
  def change(m):
   m['frozen_input_sha256'].pop(next(iter(m['frozen_input_sha256'])))
   p=audit.ROOT/'tests/h62/item2/audit-precompiles/BridgeIdentityWitnesses.lean';m['frozen_input_sha256'][str(p)]=audit.sha(p)
  self.alter(change);self.rejected()
 def test_wrong_executable(self):self.alter(lambda m:m['command'].__setitem__(0,'/bin/true'));self.rejected()
 def test_query_instead_of_elaboration(self):self.alter(lambda m:m['command'].insert(-1,'--version'));self.rejected()
 def test_rebound_empty_identity_log(self):
  p=self.e/'identity-final424.log';p.write_text('');self.alter(lambda m:m.update(log_sha256=hashlib.sha256(b'').hexdigest()));self.rejected()
 def test_changed_log_digest(self):
  p=self.e/'identity-final424.log';p.write_text(p.read_text()+'changed');self.rejected()
 def test_wrong_tool_identity(self):self.alter(lambda m:m['toolchain']['lean'].update(sha256='0'*64));self.rejected()
 def test_excessive_measured_rss(self):self.alter(lambda m:m.update(aggregate_peak_rss_bytes=12*1024**3+1));self.rejected()
 def test_insufficient_measured_headroom(self):self.alter(lambda m:m.update(minimum_available_bytes=4*1024**3-1));self.rejected()
 def test_missing_resource_measurement(self):self.alter(lambda m:m.pop('aggregate_peak_rss_bytes'));self.rejected()
 def test_elapsed_limit(self):self.alter(lambda m:m.update(wall_seconds=301));self.rejected()
 def test_missing_core_input_closure(self):
  p=self.e/'basic-final.json';m=json.loads(p.read_text());src=str(audit.ROOT/'tests/h62/item2/audit-precompiles/BasicWitnesses.lean');m['input_sha256']={src:m['input_sha256'][src]};p.write_text(json.dumps(m));self.rejected()
 def test_nonstandard_printed_axiom(self):
  p=self.e/'identity-final424.log';p.write_text(p.read_text()+"\n'H62.AuditPrecompiles.fake' depends on axioms: [unapprovedAxiom]\n")
  self.alter(lambda m:m.update(log_sha256=hashlib.sha256(p.read_bytes()).hexdigest()));self.rejected()
 def test_missing_bytes_gas_receipt(self):
  (self.e/'bytes-gas-final424.json').unlink()
  with self.assertRaises(FileNotFoundError):audit.generate(self.e)
 def test_query_bytes_gas_command(self):
  p=self.e/'bytes-gas-final424.json';m=json.loads(p.read_text());m['command'].insert(-1,'--version');p.write_text(json.dumps(m));self.rejected()
 def test_missing_header_receipt(self):
  (self.e/'header-short-zero424.json').unlink()
  with self.assertRaises(FileNotFoundError):audit.generate(self.e)
 def test_stale_header(self):
  p=self.e/'header-short-zero424.json';m=json.loads(p.read_text());src=str(audit.ROOT/'tests/h62/item2/audit-precompiles/BridgeHeaderWitnesses.lean');m['input_sha256'][src]='0'*64;p.write_text(json.dumps(m));self.rejected()

 def test_new_core_receipt_mutations(self):
  for stem in ['osaka-ledger-final424','bls-ledger-final424','point-ledger-final424','stipend-ledger424','remaining-fidelity-final424','point-success-final424']:
   p=self.e/(stem+'.json');original=p.read_text()
   for mutation in ['failed','query','stale','missing']:
    with self.subTest(stem=stem,mutation=mutation):
     m=json.loads(original)
     if mutation=='failed':m['exit']=1
     if mutation=='query':m['command'].insert(-1,'--version')
     if mutation=='stale':m['input_sha256'][next(iter(m['input_sha256']))]='0'*64
     if mutation=='missing':p.unlink()
     else:p.write_text(json.dumps(m))
     with self.assertRaises((AssertionError,FileNotFoundError)):audit.generate(self.e)
     p.write_text(original)

if __name__=='__main__':unittest.main()
