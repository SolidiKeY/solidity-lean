"""Negative acceptance controls: stale/failed/partial proof evidence must reject."""
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[4]
EVIDENCE = Path(os.environ.get("H62_AUDIT_EVIDENCE", "/workspace/h62-audit-evidence"))
VERIFY = ROOT/"scripts/h62/item2/audit-exact-verification/verify.py"


class ReceiptControls(unittest.TestCase):
    def reject(self, mutate=None, optimize=False, complete=False):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory)
            for name in ("source-census.json", "bounded-audit.log", "bounded-audit.exit", "bounded-audit.receipt.json"):
                shutil.copyfile(EVIDENCE/name, path/name)
            if mutate: mutate(path)
            args = [sys.executable] + (["-O"] if optimize else []) + [str(VERIFY), "--evidence", str(path)]
            if complete: args.append("--require-complete")
            result = subprocess.run(args, cwd=ROOT, capture_output=True, text=True,
                                    env={**os.environ, "PYTHONDONTWRITEBYTECODE":"1"})
            self.assertNotEqual(result.returncode, 0, result.stdout+result.stderr)
            return result.stdout+result.stderr

    def test_stale_proof_hash_rejected(self):
        def mutate(path):
            p=path/"bounded-audit.receipt.json"; x=json.loads(p.read_text())
            x["proof_sha256"]="0"*64; p.write_text(json.dumps(x))
        self.assertIn("stale proof evidence", self.reject(mutate))

    def test_missing_completion_rejected_even_with_matching_log_hash(self):
        def mutate(path):
            log=path/"bounded-audit.log"
            log.write_text(log.read_text().replace("COMPLETED audit\n", ""))
            p=path/"bounded-audit.receipt.json"; x=json.loads(p.read_text())
            x["log_sha256"]=hashlib.sha256(log.read_bytes()).hexdigest();p.write_text(json.dumps(x))
        self.assertIn("incomplete proof run", self.reject(mutate))

    def test_failed_compiler_exit_rejected(self):
        self.reject(lambda path: (path/"bounded-audit.exit").write_text("1\n"))

    def test_optimized_python_rejected(self):
        self.assertIn("optimized Python", self.reject(optimize=True))

    def test_incomplete_assignment_never_passes(self):
        self.assertIn("FULL_AUDIT_GATE_FAIL", self.reject(complete=True))


if __name__ == "__main__": unittest.main()
