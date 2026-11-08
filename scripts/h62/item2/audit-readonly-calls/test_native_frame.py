"""Guard stale transitive object reuse and dropped child-frame proof cases."""
import importlib.util
from pathlib import Path
import unittest
spec=importlib.util.spec_from_file_location('native_frame_controls',Path(__file__).with_name('check_native_frame.py'))
m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
class NativeFrameControls(unittest.TestCase):
    def test_source_change_rebuilds_entire_consumer_chain(self):
        order=['A.lean','B.lean','C.lean','Independent.lean']
        old={f:{'source_sha256':'old','imports':[]} for f in order}
        old['B.lean']['imports']=['A'];old['C.lean']['imports']=['B']
        import copy
        new=copy.deepcopy(old);new['A.lean']['source_sha256']='changed'
        self.assertEqual(m.dirty_modules(order,new,old),{'A.lean','B.lean','C.lean'})
    def test_import_change_invalidates_consumers(self):
        old={'A.lean':{'source_sha256':'a','imports':[]},'B.lean':{'source_sha256':'b','imports':[]},'C.lean':{'source_sha256':'c','imports':['B']}}
        import copy
        new=copy.deepcopy(old);new['B.lean']['imports']=['A']
        self.assertEqual(m.dirty_modules(list(old),new,old),{'B.lean','C.lean'})
    def test_missing_prior_module_cannot_reuse(self):
        pins={'New.lean':{'source_sha256':'new','imports':[]},'Consumer.lean':{'source_sha256':'same','imports':['New']}}
        self.assertEqual(m.dirty_modules(list(pins),pins,{'Consumer.lean':pins['Consumer.lean']}),set(pins))
    def test_receipt_parses_only_admitted_buffer(self):
        from unittest.mock import Mock
        path=Mock();raw=b'{"value":7}'
        path.read_bytes.return_value=raw
        self.assertEqual(m.load_pinned(path,m.digest(raw)),{'value':7})
        path.read_bytes.assert_called_once();path.read_text.assert_not_called()
        with self.assertRaises(ValueError):m.load_pinned(path,m.digest(b'{"value":8}'))
    def test_source_substitution_refused(self):
        from unittest.mock import Mock
        path=Mock();path.read_bytes.return_value=b'changed'
        with self.assertRaises(ValueError):m.source_bytes(path,m.digest(b'admitted'))
    def test_closure_includes_native_bytes_and_framed_compiler(self):
        from unittest.mock import patch
        with patch.object(m.m.profile,'closure',return_value=([],{})) as closure:
            self.assertEqual(m.current_closure(),([],{}))
            self.assertEqual(closure.call_args.args[1],[m.m.TARGET,m.legacy.CHECKED_TARGET])
        with patch.object(m.m.profile,'closure',return_value=([m.legacy.HELD],{})):
            with self.assertRaises(ValueError):m.current_closure()
    def test_exact_theorems_and_imports(self):
        raw=(m.ROOT/m.SOURCE).read_bytes()
        self.assertEqual(len(m.inventory(raw)),3)
        for bad in [b'import Lean\n'+raw,raw.replace(b'theorem lift_returned',b'theorem wrong'),raw+b'\nnamespace Extra\ntheorem padding : True := True.intro\nend Extra\n']:
            with self.assertRaises(ValueError):m.inventory(bad)
if __name__=='__main__':unittest.main()
