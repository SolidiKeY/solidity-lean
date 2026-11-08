"""Guard lost original helpers and erased continuation effects in statement credit."""
import importlib.util
from pathlib import Path
import subprocess
import unittest
spec=importlib.util.spec_from_file_location('read_statement_controls',Path(__file__).with_name('read_statement_coverage.py'))
m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);g=m.module.gate
class ReadStatementControls(unittest.TestCase):
    def test_complete_extension_and_prior_body_preservation(self):
        old=subprocess.check_output(['git','show','abcf292e41410f0ba4eb379dd554c4269f1ec735:'+g.SOURCE],cwd=g.ROOT).decode()
        raw=(g.ROOT/g.SOURCE).read_bytes();new=raw.decode();ns='namespace Solidity.H62.ReadonlyAudit.PrimitiveReadWitnesses'
        before=old.split(ns,1)[1].rsplit('end Solidity.H62.ReadonlyAudit.PrimitiveReadWitnesses',1)[0]
        self.assertTrue(new.split(ns,1)[1].startswith(before))
        self.assertEqual(len(g.inventory(raw)),19)
        for bad in [b'import Extra.Module\n'+raw,raw+b'\nnamespace Extra\ntheorem extra : True := True.intro\nend Extra\n']:
            with self.assertRaises(ValueError):g.inventory(bad)
    def test_explicit_six_mapping_and_fresh_verifier(self):
        self.assertEqual(len(g.INTERFACES),2);self.assertEqual(m.collector.CREDIT_PROOFS,m.module.NEW_NAMES)
        self.assertEqual(len(set(m.collector.CREDIT_PROOFS)),2)
        self.assertEqual(m.collector.verifier.gate,g)
        self.assertNotIn('cache_module',g.__dict__)
        self.assertEqual(m.collector.CANONICAL_SHA,'532234a73caefaadee0ef39a75108d9392b6de99e05fcbd763ce9634642c9077')
    def test_held_workload_still_refused(self):
        import tempfile
        with tempfile.TemporaryDirectory() as temp:
            with self.assertRaisesRegex(ValueError,'held workload'):g.original.snapshot(lambda _:b'import Solidity.Backend.WorldCalls.Premises\n',g.TARGET,Path(temp))
if __name__=='__main__':unittest.main()
