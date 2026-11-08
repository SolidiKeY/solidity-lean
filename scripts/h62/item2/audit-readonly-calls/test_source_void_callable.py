"""Guard callable-mode staging, prerequisite order and conflicting modes."""
import importlib.util
from pathlib import Path
import contextlib
import io
import sys
import unittest
from unittest.mock import patch
spec=importlib.util.spec_from_file_location('callable_controls',Path(__file__).with_name('check_source_void.py'))
m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);m.configure_callable()
class CallableControls(unittest.TestCase):
    def test_inventory_and_import_refusal(self):
        raw=(m.ROOT/m.SOURCE).read_bytes();self.assertEqual(len(m.inventory(raw)),11)
        for bad in [b'import Lean\n'+raw,raw.replace(b'theorem phase_complete',b'theorem replaced_phase')]:
            with self.assertRaises(ValueError):m.inventory(bad)
    def test_prerequisite_order_and_collision(self):
        plan=m.local_plan();names=[name for name,_ in plan]
        self.assertEqual(names[-3:],['SourceVoidSelection','SourceVoidWorld','SourceVoidCallable'])
        with patch.object(m,'SOURCE',m.LOCAL[-1][1]):
            with self.assertRaises(ValueError):m.local_plan()
        with self.assertRaises(ValueError):m.configure_callable()
    def test_closure_and_hold(self):
        with patch.object(m.m.profile,'closure',return_value=([],{})) as closure:
            self.assertEqual(m.closure(),([],{}))
            self.assertEqual(closure.call_args.args[1][-1:],['Solidity.Lowering.V08.CallableBodyPremises'])
        with patch.object(m.m.profile,'closure',return_value=([m.frame.legacy.HELD],{})):
            with self.assertRaises(ValueError):m.closure()
    def test_conflicting_cli_modes_rejected(self):
        args=['check','--world','--callable','--native','/tmp/none','--source','/tmp/none','--output','/tmp/none']
        with patch.object(sys,'argv',args),contextlib.redirect_stderr(io.StringIO()):
            with self.assertRaises(SystemExit) as result:m.main()
        self.assertEqual(result.exception.code,2)
if __name__=='__main__':unittest.main()
