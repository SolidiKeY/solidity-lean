"""Reject tampering through the actual frozen executable in sparse local clones."""
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[3]
REL = "tests/terra-20261103/gate"

class FrozenContract(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix="tf_contract_")
        self.addCleanup(self.temp.cleanup)
        self.clone = Path(self.temp.name) / "repo"
        self.env = {k: v for k, v in os.environ.items()
                    if not k.startswith(("GIT_", "GATE_", "TF_GATE_")) and k not in ("BASH_ENV", "ENV")}
        home = Path(self.temp.name) / "home"
        home.mkdir()
        self.env.update(HOME=str(home), GIT_CONFIG_GLOBAL=os.devnull, GIT_CONFIG_NOSYSTEM="1",
                        GIT_AUTHOR_NAME="Contract Fixture", GIT_AUTHOR_EMAIL="fixture@example.invalid",
                        GIT_COMMITTER_NAME="Contract Fixture", GIT_COMMITTER_EMAIL="fixture@example.invalid",
                        PYTHONDONTWRITEBYTECODE="1")
        self.head = subprocess.check_output(["git", "-c", "safe.directory=" + str(ROOT), "-C", str(ROOT), "rev-parse", "HEAD"], env=self.env, text=True).strip()
        self.command(["git", "clone", "--shared", "--no-checkout", "-q", str(ROOT), str(self.clone)])
        self.command(["git", "-C", str(self.clone), "sparse-checkout", "set", "--no-cone", "/scripts/", "/run-lean.sh", "/" + REL + "/"])
        self.command(["git", "-C", str(self.clone), "checkout", "--detach", "-q", self.head])

    def command(self, command):
        result = subprocess.run(command, env=self.env, text=True, capture_output=True, timeout=20)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        return result.stdout.strip()

    def reject(self, message, head=None, omit_head=False):
        command = [sys.executable, str(self.clone / REL / "accept_repaired.py")]
        if not omit_head:
            command += ["--head", head or self.head]
        result = subprocess.run(command, cwd=self.clone, env=self.env, text=True, capture_output=True, timeout=20)
        self.assertEqual(result.returncode, 2 if omit_head else 1, result.stdout + result.stderr)
        self.assertIn(message, result.stderr)
        self.assertNotIn('"status": "PASS"', result.stdout)

    def test_wrong_head(self):
        self.reject("exact head mismatch", "0" * 40)

    def test_extra_artifact(self):
        (self.clone / REL / "unexpected.txt").write_text("unreviewed")
        self.reject("artifact inventory mismatch")

    def test_missing_artifact(self):
        (self.clone / REL / "test_targets.py").unlink()
        self.reject("artifact inventory mismatch")

    def test_changed_artifact(self):
        with (self.clone / REL / "README.md").open("a") as stream:
            stream.write("changed")
        self.reject("artifact hash mismatch")

    def test_changed_dependency(self):
        with (self.clone / "scripts/check-trust.mjs").open("a") as stream:
            stream.write("changed")
        self.reject("dependency hash mismatch")

    def test_changed_snapshot(self):
        with (self.clone / REL / "snapshot.json").open("a") as stream:
            stream.write(" ")
        self.reject("snapshot commit mismatch")

    def test_source_drift(self):
        with (self.clone / "scripts/coord-tools/gate.sh").open("a") as stream:
            stream.write("# changed\n")
        self.reject("source hash mismatch")

    def test_missing_head_argument(self):
        self.reject("--head", omit_head=True)

    def test_unexpected_commit(self):
        self.command(["git", "-C", str(self.clone), "commit", "--allow-empty", "-qm", "unexpected"])
        head = self.command(["git", "-C", str(self.clone), "rev-parse", "HEAD"])
        self.reject("contract parent mismatch", head)
