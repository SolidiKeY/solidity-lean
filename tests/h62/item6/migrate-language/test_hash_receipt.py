"""Negative receipt control: mismatched owner bytes cannot create a fixture."""
import pathlib,subprocess,sys,tempfile,unittest
ROOT=pathlib.Path(__file__).resolve().parents[4]
class ReceiptControl(unittest.TestCase):
    def test_reject_mismatched_receipt_before_writes(self):
        with tempfile.TemporaryDirectory() as d:
            root=pathlib.Path(d);bad=root/'wrong.patch';bad.write_text('not the routed owner receipt\n')
            dest=root/'fixture'
            r=subprocess.run([sys.executable,str(ROOT/'scripts/h62/item6/migrate-language/prepare-hash-fixture.py'),str(bad),str(dest)],stdout=subprocess.PIPE,stderr=subprocess.PIPE,text=True)
            self.assertNotEqual(r.returncode,0)
            self.assertIn('Unverified receipt: STOP',r.stderr)
            self.assertFalse(dest.exists())
if __name__=='__main__':unittest.main()
