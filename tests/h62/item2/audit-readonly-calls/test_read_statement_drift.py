"""Guard private drift evidence from direct or symlinked checkout output paths."""
from pathlib import Path
import subprocess
import tempfile
import unittest
ROOT=Path(__file__).resolve().parents[4]
SCRIPT=ROOT/'scripts/h62/item2/audit-readonly-calls/read_statement_drift.py'
class PrivateOutputTests(unittest.TestCase):
    def check_rejected(self,output):
        result=subprocess.run(['python3',str(SCRIPT),'--proof-root','/nonexistent/probe','--ledger','/nonexistent/ledger','--output',str(output)],capture_output=True,text=True)
        self.assertNotEqual(result.returncode,0)
        self.assertIn('evidence output must remain outside public checkout',result.stderr)
        self.assertFalse(output.exists())
    def test_direct_checkout_output(self):
        self.check_rejected(ROOT/'tests/h62/item2/audit-readonly-calls/rejected-private-output')
    def test_symlinked_checkout_output(self):
        with tempfile.TemporaryDirectory() as tmp:
            alias=Path(tmp)/'checkout';alias.symlink_to(ROOT,target_is_directory=True)
            self.check_rejected(alias/'rejected-private-output')
if __name__=='__main__':unittest.main()
