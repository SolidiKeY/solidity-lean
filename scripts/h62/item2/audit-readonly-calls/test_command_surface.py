"""Guard alternate SDKs, helper races and partial ranges being accepted as binding."""
import importlib.util
from pathlib import Path
import tempfile
import unittest
from unittest import mock
spec=importlib.util.spec_from_file_location('surface_driver',Path(__file__).with_name('command_surface.py'))
m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)

class SurfaceControls(unittest.TestCase):
    def test_sdk_overrides_removed(self):
        env=m.isolated_environment({'LEAN_SYSROOT':'bad','LEAN_PATH':'bad','LEAN_OTHER':'bad','ELAN_TOOLCHAIN':'bad','KEEP':'yes'},Path('/private'))
        self.assertEqual(env['LEAN_SYSROOT'],str(m.LEAN.resolve().parent.parent));self.assertEqual(env['LEAN_PATH'],'/private')
        self.assertEqual(env['LEAN_NUM_THREADS'],'1');self.assertEqual(env['KEEP'],'yes');self.assertNotIn('ELAN_TOOLCHAIN',env);self.assertNotIn('LEAN_OTHER',env)

    def test_captured_helper_changed_before_compile_refused(self):
        with tempfile.TemporaryDirectory() as temp:
            source=Path(temp)/'tool';staged=Path(temp)/'staged';raw=b'import Lean';pin=m.digest(raw);source.write_bytes(raw)
            m.stage_helper(source,staged,raw,pin);self.assertEqual(staged.read_bytes(),raw)
            source.write_bytes(b'changed')
            with self.assertRaises(ValueError):m.stage_helper(source,staged,raw,pin)
            source.write_bytes(raw)
            with mock.patch.object(Path,'write_bytes',side_effect=lambda value:None):
                staged.unlink()
                with self.assertRaises(OSError):m.stage_helper(source,staged,raw,pin)

    def test_utf8_byte_ranges_and_bad_indices(self):
        raw='αβ'.encode();self.assertEqual(m.slice_span(raw,{'start':0,'end':2}),'α')
        for span in [{'start':True,'end':2},{'start':-1,'end':2},{'start':0,'end':9},{'start':2,'end':1}]:
            with self.assertRaises(ValueError):m.slice_span(raw,span)
        with self.assertRaises(UnicodeDecodeError):m.slice_span(raw,{'start':1,'end':2})

    def test_partial_or_executed_records_never_promoted(self):
        base={'project_imports_loaded':False,'commands_elaborated':False,'kernel_binding':False,'status':'parser-error','diagnostics':['bad'],'records':[{'name':'forged'}]}
        self.assertEqual(m.surface(b'',base)['rows'],[])
        bad=dict(base,commands_elaborated=True)
        with self.assertRaises(ValueError):m.surface(b'',bad)
        bad=dict(base,status='parsed-standard-syntax',terminal='Lean.Parser.Command.exit')
        with self.assertRaises(ValueError):m.surface(b'',bad)

    def test_runtime_guards_not_assertions(self):
        with self.assertRaises(ValueError):m.require(False,'guard')
        self.assertTrue(m.require(True,'guard') is None)

if __name__=='__main__':unittest.main()
