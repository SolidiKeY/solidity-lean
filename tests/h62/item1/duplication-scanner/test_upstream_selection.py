"""Guard rebasing away alias accounting, invalid inputs or traversal-failure deltas."""
import contextlib
import hashlib
import importlib.util
import io
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest import mock

ROOT=Path(__file__).resolve().parents[4];SCRIPT=ROOT/"scripts/h62/item1/duplication-scanner/scan.py"
spec=importlib.util.spec_from_file_location("reconciled_scan",SCRIPT);scanner=importlib.util.module_from_spec(spec);spec.loader.exec_module(scanner)


class UpstreamSelectionControls(unittest.TestCase):
    def invoke(self,root,pattern,*extra):
        return subprocess.run([sys.executable,"-B",str(SCRIPT),str(root),pattern,*extra],capture_output=True,text=True,timeout=15)

    def test_safe_alias_preserved_broken_alias_suppresses_removals(self):
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp);(root/'A.lean').write_text('def a := 0\n');(root/'B.lean').write_text('def b := 1\n')
            baseline=self.invoke(root,'*.lean');self.assertEqual(baseline.returncode,0)
            previous=root/'old.json';previous.write_text(baseline.stdout)
            (root/'B.lean').unlink();(root/'B.lean').symlink_to('A.lean');(root/'Missing.lean').symlink_to('gone')
            result=self.invoke(root,'*.lean','--previous',str(previous),'--previous-sha256',hashlib.sha256(previous.read_bytes()).hexdigest())
            self.assertNotEqual(result.returncode,0);value=json.loads(result.stdout)
            self.assertEqual([r['path'] for r in value['inputs']],['A.lean','B.lean'])
            self.assertTrue(any(Path(r['path']).name=='Missing.lean' for r in value['errors']))
            self.assertEqual(value['input_aliases'],[{'path':'B.lean','resolved_path':'A.lean'}])
            self.assertIsNone(value['incremental']['removed']);self.assertIsNone(value['incremental']['candidate_groups'])

    def test_recursive_and_finite_alias_globs_nonregular_and_escape(self):
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp);(root/'actual').mkdir();(root/'actual/A.lean').write_text('def a := 0\n');(root/'alias').symlink_to('actual',target_is_directory=True)
            result=self.invoke(root,'**/*.lean');self.assertNotEqual(result.returncode,0)
            recursive=json.loads(result.stdout)
            self.assertEqual([r['path'] for r in recursive['inputs']],['actual/A.lean'])
            self.assertTrue(any('skips directory symlink' in r['reason'] for r in recursive['errors']))
            self.assertEqual(recursive['incremental']['comparison_status'],'current-incomplete')
            finite=self.invoke(root,'alias/*.lean');self.assertEqual(finite.returncode,0)
            self.assertEqual(json.loads(finite.stdout)['input_aliases'],[{'path':'alias/A.lean','resolved_path':'actual/A.lean'}])
            (root/'alias').unlink();(root/'dangling-directory').symlink_to('gone',target_is_directory=True)
            broken=self.invoke(root,'dangling-directory/*.lean');self.assertNotEqual(broken.returncode,0)
            self.assertEqual(json.loads(broken.stdout)['unmatched_patterns'],['dangling-directory/*.lean'])
            os.mkfifo(root/'Pipe.lean');fifo=self.invoke(root,'**/*.lean');self.assertNotEqual(fifo.returncode,0)
            self.assertTrue(json.loads(fifo.stdout)['errors'])
            escape=self.invoke(root,'../*.lean');self.assertNotEqual(escape.returncode,0);self.assertIn('patterns must stay within the root',escape.stderr)

    def test_nonrecursive_literal_target_failure_suppresses_deltas(self):
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp)
            for folder in ['readable','denied']:(root/folder).mkdir();(root/folder/'Target.lean').write_text('def a := 0\n')
            result=self.invoke(root,'*/Target.lean');self.assertEqual(result.returncode,0)
            previous=root/'old.json';previous.write_text(result.stdout);actual=Path.lstat
            def fail(path,*args,**kwargs):
                if path==root/'denied/Target.lean':raise PermissionError(13,'permission denied',str(path))
                return actual(path,*args,**kwargs)
            output=io.StringIO()
            with mock.patch.object(Path,'lstat',fail),mock.patch.object(sys,'argv',[str(SCRIPT),str(root),'*/Target.lean','--previous',str(previous),'--previous-sha256',hashlib.sha256(previous.read_bytes()).hexdigest()]),contextlib.redirect_stdout(output):
                self.assertTrue(scanner.main())
            value=json.loads(output.getvalue());self.assertTrue(any('permission denied' in r['reason'] for r in value['errors']))
            self.assertIsNone(value['incremental']['removed']);self.assertIsNone(value['incremental']['candidate_groups'])


if __name__=='__main__':unittest.main()
