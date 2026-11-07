"""Exercise successful and failing external-process receipts without Lean."""
import pathlib, subprocess, tempfile, unittest, json, sys
SCRIPT=pathlib.Path(__file__).resolve().parents[4]/'scripts/h62/item6/migrate-automation/measure.py'
class MeasureTests(unittest.TestCase):
    def run_case(self,code,timeout='5'):
        with tempfile.TemporaryDirectory() as d:
            out=pathlib.Path(d)/'receipt'
            p=subprocess.run([sys.executable,str(SCRIPT),'--cwd',d,'--output',str(out),'--timeout',timeout,'--',sys.executable,'-c',code],capture_output=True,text=True)
            return p,json.loads((out/'result.json').read_text())
    def test_exit_zero(self):
        p,r=self.run_case('print("ok")');self.assertEqual(p.returncode,0);self.assertEqual(r['exit'],0);self.assertIsNone(r['guard_stop'])
    def test_nonzero_is_not_pass(self):
        p,r=self.run_case('raise SystemExit(7)');self.assertEqual(p.returncode,1);self.assertEqual(r['exit'],7)
    def test_timeout_is_not_pass(self):
        p,r=self.run_case('import time; time.sleep(10)','.1');self.assertEqual(p.returncode,1);self.assertEqual(r['guard_stop'],'timeout')
if __name__=='__main__':unittest.main()
