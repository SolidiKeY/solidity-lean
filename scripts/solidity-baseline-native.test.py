#!/usr/bin/env python3
"""Integrity/cache negative controls; no Lean/server/build."""
import copy,importlib.util,json,unittest
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1];HERE=ROOT/'tests/upstream/baseline-20261028/native-cache'
def module(name,path):
 s=importlib.util.spec_from_file_location(name,path);m=importlib.util.module_from_spec(s);s.loader.exec_module(m);return m
cache=module('cache_audit',ROOT/'scripts/solidity-baseline-cache-audit.py');native=module('native_index',ROOT/'scripts/solidity-baseline-native-index.py')
class CacheIntegrity(unittest.TestCase):
 @classmethod
 def setUpClass(cls):
  _,files=native.archived_files(ROOT)
  cls.audit=json.loads(files['audit.json']);cls.hashes=json.loads(files['file-hashes.json'])
 def check_mutation(self,fn,reason):
  a=copy.deepcopy(self.audit);fn(a['modules']['Solidity.Tools.Upstream']);r=cache.verify(a,self.hashes);self.assertFalse(r['narrowClosureSourceAndOleanChecksPass']);self.assertTrue(any(reason in s for _,s in r['failures']))
 def test_real_narrow_cache_passes(self):self.assertTrue(cache.verify(self.audit,self.hashes)['narrowClosureSourceAndOleanChecksPass'])
 def test_missing_setup_refused(self):self.check_mutation(lambda r:r['setup'].update(exists=False),'setup missing')
 def test_missing_direct_import_refused(self):self.check_mutation(lambda r:r.update(directImports=r['directImports']+['Solidity.FakeMissingImport']),'direct imports absent')
 def test_wrong_toolchain_refused(self):self.check_mutation(lambda r:r.update(traceToolchain=[['Lean wrong','0']]),'toolchain')
 def test_source_hash_drift_refused(self):self.check_mutation(lambda r:r.update(traceSourceHash='wrong'),'source hash')
 def test_olean_output_drift_refused(self):self.check_mutation(lambda r:r.update(traceOutputs={'o':['wrong']}),'olean hash')
 def test_cached_import_drift_refused(self):self.check_mutation(lambda r:r['importArtifactChecks'][0].update(byteIdenticalToLocal=False),'imports differ')
class NativeIntegrity(unittest.TestCase):
 @classmethod
 def setUpClass(cls):cls.x=native.derive(ROOT)
 def test_all40_ids_preserved(self):
  old=json.loads((ROOT/'tests/upstream/baseline-20261028/probes/matrix.json').read_text());self.assertEqual([r['id'] for r in old['features']],[r['id'] for r in self.x['features']])
 def test_modes_observations_and_negative_controls(self):
  self.assertEqual(self.x['statistics'],{'typedImportModes':40,'replayModes':38,'replayStatuses':{'broken':12,'working':26},'matchingRuntimeObservations':122,'wrongExpectedValueControls':2,'productionProvenanceRefusals':4,'internalAbiEntryRefusals':2,'typedOnlyModes':2})
 def test_native_refusal_rows_precise(self):
  self.assertEqual({r['id'] for r in self.x['features'] if r['classification']=='observed-native-import-refusal'},{'increments','valueTypeDeclarations','valueTypes','doWhileStatement','continueStatement'})
 def test_compound_receiver_observations_credit_support(self):
  r=next(r for r in self.x['features'] if r['id']=='compoundAssignment');self.assertEqual(r['classification'],'inventory-documentation-discrepancy');self.assertIn('107/207',r['assessment'])
 def test_nonzero_value_not_claimed(self):
  self.assertFalse(self.x['nativeValidationComplete']);self.assertTrue(self.x['nativeImportAndReplayAvailable']);self.assertIn('Nonzero msg.value',self.x['remainingNativeValidation'])
 def test_original_variants_not_inferred_from_same_message(self):
  a=self.x['originalVariantAttributionAudit'];self.assertFalse(a['associated']);self.assertEqual(len(a['considered']),4);self.assertTrue(all('struct S { C c;'in s['source'] for s in a['consideredSources']))
 def test_original_counts_unchanged(self):self.assertEqual(self.x['originalCounts'],{'working':4135,'broken':196,'blocked':5329})
 def test_outputs_reproduce(self):
  expected=json.loads((HERE/'matrix.json').read_text())
  # The portability repair changes the executing generator's identity only.
  # Every retained observation and historical claim must still reproduce.
  self.assertEqual(self.x['generatorSha256'],native.sha((ROOT/'scripts/solidity-baseline-native-index.py').read_bytes()))
  native.historical_observations(self.x,expected)
  self.assertEqual((HERE/'README.md').read_text(),native.render(self.x))
 def test_archived_log_paths_cannot_escape_the_recorded_checkout(self):
  for path in ['/other/native.log','/workspace/solidity-lean/tests/upstream/baseline-20261028/native-cache/../native.log']:
   with self.assertRaises(ValueError):native.archived_log_name(path)
 def test_historical_observation_or_generator_drift_is_refused(self):
  expected=json.loads((HERE/'matrix.json').read_text())
  for mutated in [{**expected,'generatorSha256':'wrong'}, {**expected,'questions':39}]:
   with self.assertRaises(ValueError):native.historical_observations(self.x,mutated)
if __name__=='__main__':unittest.main()
