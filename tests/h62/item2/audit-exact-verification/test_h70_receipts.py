"""Negative replay checks after the performance stop; never runs Lean."""
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile
import unittest

ROOT=Path(__file__).resolve().parents[4]
EVIDENCE=Path("/workspace/h62-audit-h70-evidence")
CHECK=ROOT/"scripts/h62/item2/audit-exact-verification/h70-check.py"

class H70ReceiptControls(unittest.TestCase):
    def reject(self, mutate=None, optimize=False):
        with tempfile.TemporaryDirectory() as directory:
            path=Path(directory)
            receipt=json.loads((EVIDENCE/"h70-receipt.json").read_text())
            (path/"toolchain").symlink_to(EVIDENCE/"toolchain",target_is_directory=True)
            for phase in receipt["phases"].values():
                name=phase["log"];shutil.copyfile(EVIDENCE/name,path/name)
                exit_name=Path(name).stem+".exit";shutil.copyfile(EVIDENCE/exit_name,path/exit_name)
            if mutate:mutate(receipt,path)
            (path/"h70-receipt.json").write_text(json.dumps(receipt))
            command=[sys.executable]+(["-O"] if optimize else [])+[str(CHECK),"--evidence",str(path)]
            result=subprocess.run(command,cwd=ROOT,capture_output=True,text=True,
                env={**os.environ,"PYTHONDONTWRITEBYTECODE":"1"})
            self.assertNotEqual(result.returncode,0,result.stdout+result.stderr)
            return result.stdout+result.stderr

    def test_missing_keysort_rejected(self):
        self.assertIn("missing/unexpected required phase",self.reject(lambda r,p:r["phases"].pop("keysort")))

    def test_stale_proof_rejected(self):
        def mutate(r,p):r["hashes"]["tests/h62/item2/audit-exact-verification/LinearDecisionAudit.lean"]="0"*64
        self.assertIn("stale source receipt",self.reject(mutate))

    def test_omitted_control_workload_rejected(self):
        def mutate(r,p):
            phase=r["phases"]["proof"];log=p/phase["log"]
            rows=[line for line in log.read_text().splitlines() if not
                  (line.startswith(("CHECK ","PASS ")) and "JointWitnessControls" in line)]
            log.write_text("\n".join(rows)+"\n");phase["log_sha256"]=hashlib.sha256(log.read_bytes()).hexdigest()
        self.assertIn("missing/unexpected workload",self.reject(mutate))

    def test_nonfinite_timing_rejected(self):
        def mutate(r,p):
            phase=r["phases"]["after"];log=p/phase["log"]
            text=re.sub(r"^(PASS \S+) \S+",r"\1 nan",log.read_text(),count=1,flags=re.M)
            log.write_text(text);phase["log_sha256"]=hashlib.sha256(log.read_bytes()).hexdigest()
        self.assertIn("invalid timing duration",self.reject(mutate))

    def test_optimized_python_rejected(self):
        self.assertIn("optimized Python refused",self.reject(optimize=True))

if __name__=="__main__":unittest.main()
