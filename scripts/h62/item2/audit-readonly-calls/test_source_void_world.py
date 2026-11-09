"""Guard world-mode self-import staging and lost Source-selection prerequisites."""
import importlib.util
from pathlib import Path
import unittest
from unittest.mock import patch
spec=importlib.util.spec_from_file_location('source_world_controls',Path(__file__).with_name('check_source_void.py'))
m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);m.configure_world()
class WorldModeControls(unittest.TestCase):
    def test_world_inventory(self):
        raw=(m.ROOT/m.SOURCE).read_bytes()
        self.assertEqual(len(m.inventory(raw)),12)
        for bad in [b'import Lean\n'+raw,raw.replace(b'theorem reached_image',b'theorem renamed_image')]:
            with self.assertRaises(ValueError):m.inventory(bad)
    def test_source_prerequisite_and_distinct_module(self):
        self.assertEqual(m.LOCAL[-1],('SourceVoidSelection','tests/h62/item2/audit-readonly-calls/SourceVoidSelection.lean'))
        self.assertEqual(Path(m.SOURCE).stem,'SourceVoidWorld')
        plan=m.local_plan()
        self.assertEqual(plan[-1],('SourceVoidWorld',m.SOURCE))
        self.assertEqual(len({name for name,_ in plan}),len(plan))
        self.assertLess([name for name,_ in plan].index('SourceVoidSelection'),len(plan)-1)
        with self.assertRaises(ValueError):m.configure_world()
    def test_staging_collision_refused(self):
        with patch.object(m,'SOURCE','tests/h62/item2/audit-readonly-calls/SourceVoidSelection.lean'):
            with self.assertRaises(ValueError):m.local_plan()
        with patch.object(m,'LOCAL',[('wrong_module',m.LOCAL[0][1])]):
            with self.assertRaises(ValueError):m.local_plan()
    def test_world_closure_and_hold(self):
        with patch.object(m.m.profile,'closure',return_value=([],{})) as closure:
            self.assertEqual(m.closure(),([],{}))
            self.assertEqual(closure.call_args.args[1][-1],'Solidity.Lowering.V08.WorldCatalogueTransport')
        with patch.object(m.m.profile,'closure',return_value=([m.frame.legacy.HELD],{})):
            with self.assertRaises(ValueError):m.closure()
if __name__=='__main__':unittest.main()
