"""Exact-byte relay and original-file protection controls; no Lean run."""
import importlib.util,pathlib,sys,tempfile,unittest
from unittest.mock import patch
sys.dont_write_bytecode=True
ROOT=pathlib.Path(__file__).resolve().parents[4]
p=ROOT/"scripts/h62/item6/migrate-roadmap/stage_h70_hash.py"
s=importlib.util.spec_from_file_location("h70_hash",p);m=importlib.util.module_from_spec(s);s.loader.exec_module(m)
class Controls(unittest.TestCase):
    def original(self):return (ROOT/m.REL).read_bytes()
    def test_exact_full_owner_target(self):
        original=self.original();result=m.apply_relay(original)
        self.assertEqual(m.blob(result),"092971eda8c7d6997276a92ba19b25b7ce05844e")
        self.assertEqual(self.original(),original)
    def test_modified_base_rejected(self):
        with self.assertRaises(ValueError):m.apply_relay(self.original()+b"\n")
    def test_duplicate_application_rejected(self):
        with self.assertRaises(ValueError):m.apply_relay(m.apply_relay(self.original()))
    def test_same_prefix_wrong_full_hash_rejected(self):
        with patch.object(m,"EXPECTED_TARGET_BLOB",m.EXPECTED_TARGET_BLOB[:-1]+"0"):
            with self.assertRaises(ValueError):m.apply_relay(self.original())
    def test_unexpected_private_work_preserved(self):
        parent=pathlib.Path("/workspace/migrate-roadmap-evidence/h70")
        with tempfile.TemporaryDirectory(dir=parent) as name:
            directory=pathlib.Path(name);target=directory/m.REL;target.parent.mkdir(parents=True);target.write_bytes(b"unexpected owned work")
            with patch.object(sys,"argv",["stage_h70_hash.py",name]):
                with self.assertRaises(ValueError):m.main()
            self.assertEqual(target.read_bytes(),b"unexpected owned work")
if __name__=="__main__":unittest.main()
