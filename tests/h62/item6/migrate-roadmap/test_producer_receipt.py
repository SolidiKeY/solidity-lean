"""Prevent publication of an unchanged partial head as a trust-guard fix."""
import importlib.util,pathlib,sys,unittest
from unittest.mock import patch
sys.dont_write_bytecode=True
ROOT=pathlib.Path(__file__).resolve().parents[4]
s=importlib.util.spec_from_file_location("receipt",ROOT/"scripts/h62/item6/migrate-roadmap/producer_receipt.py")
m=importlib.util.module_from_spec(s);s.loader.exec_module(m)
class Controls(unittest.TestCase):
    def source(self):return (ROOT/m.REL).read_bytes()
    def test_exact_empty_guard_is_preserved(self):
        current=self.source();self.assertEqual(m.validate_source(current,current,current),1104)
    def test_unreviewed_worktree_change_rejected(self):
        current=self.source()
        with self.assertRaises(ValueError):m.validate_source(current+b"\n",current,current)
    def test_changed_published_source_not_called_unchanged(self):
        current=self.source()
        with self.assertRaises(ValueError):m.validate_source(current+b"\n",current+b"\n",current)
    def test_guard_cannot_relax_even_with_updated_identity_constants(self):
        current=self.source().replace(b"does not depend on any axioms",b"depends on axioms: [propext]")
        with patch.object(m,"SOURCE_SHA256",m.sha(current)),patch.object(m,"SOURCE_BLOB",m.blob(current)):
            with self.assertRaises(ValueError):m.validate_source(current,current,current)
    def test_duplicate_target_guard_rejected(self):
        current=self.source()+b"\n#guard_msgs in #print axioms Solidity.Roadmap.PublicCorrectness.transfer\n"
        with patch.object(m,"SOURCE_SHA256",m.sha(current)),patch.object(m,"SOURCE_BLOB",m.blob(current)):
            with self.assertRaises(ValueError):m.validate_source(current,current,current)
if __name__=="__main__":unittest.main()
