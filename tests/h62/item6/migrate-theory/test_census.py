"""Scanner negative controls; no claim of proof or elaborated API auditing."""
import importlib.util, pathlib, unittest, runpy, sys, tempfile
from unittest import mock
ROOT=pathlib.Path(__file__).resolve().parents[4]
spec=importlib.util.spec_from_file_location('census',ROOT/'scripts/h62/item6/migrate-theory/census.py')
m=importlib.util.module_from_spec(spec); spec.loader.exec_module(m)
class ScannerControls(unittest.TestCase):
    def test_nested_comments_strings_and_multiple_imports(self):
        self.assertEqual(m.imports('/- import Fake /- nested -/ -/\nimport Solidity.AST Solidity.Scope -- no\ndef text := "import Fake"\npublic import Lean\n'),['Solidity.AST','Solidity.Scope','Lean'])
    def test_anonymous_instances(self):
        ds=m.declaration_candidates('instance (T : Ty) : X T where\ninstance : X where\ntheorem valid : True := by trivial\n/- theorem fake -/\n')
        self.assertEqual([(d['kind'],d['name']) for d in ds],[('instance',None),('instance',None),('theorem','valid')])
    def test_missing_project_import_rejected(self):
        with self.assertRaises(FileNotFoundError): m.source_path('Solidity.MissingH62NegativeControl')
    def test_vendor_layout(self):
        self.assertTrue(str(m.source_path('LeanTeX.Defs')).endswith('vendor/LeanTeX/LeanTeX/Defs.lean'))
    def test_report_drift_exits_nonzero(self):
        c=m.census(); c['files'][0]['unchanged']=False
        with tempfile.TemporaryDirectory() as tmp:
            argv=['report.py','--inputs','/workspace/h62-coordinator-inputs','--output',str(pathlib.Path(tmp)/'report.json')]
            with mock.patch.dict(sys.modules,{'census':m}), mock.patch.object(m,'census',return_value=c), mock.patch.object(sys,'argv',argv):
                with self.assertRaises(SystemExit) as result:
                    runpy.run_path(str(ROOT/'scripts/h62/item6/migrate-theory/report.py'),run_name='__main__')
                self.assertEqual(result.exception.code,1)
    def test_complete_frozen_sources(self):
        c=m.census(); self.assertEqual(c['assigned_count'],25)
        self.assertTrue(all(x['unchanged'] for x in c['files']))
        self.assertEqual(c,m.census())
        paths=next(x for x in c['files'] if x['path'].endswith('Obs/Paths.lean'))
        self.assertIn(232,[d['line'] for d in paths['declaration_candidates'] if d['kind']=='instance' and d['name'] is None])
        self.assertIn(429,[d['line'] for d in paths['declaration_candidates'] if d['kind']=='instance' and d['name'] is None])
if __name__=='__main__': unittest.main()
