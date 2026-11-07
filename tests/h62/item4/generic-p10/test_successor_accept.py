"""Adversarial source-only successor gate tests; no real Lean is invoked."""
import copy
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[4]
sys.path.insert(0, str(ROOT / "scripts/h62/item4/generic-p10"))
import census
import successor_accept as gate


class SuccessorGateTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.repo = Path(self.tmp.name) / "repo"
        self.repo.mkdir()
        self.git("init", "-q", "--initial-branch=" + gate.SUCCESSOR_BRANCH)
        self.path = str(census.FAMILY / "Fixture.lean")
        source = self.repo / self.path
        source.parent.mkdir(parents=True)
        source.write_text("theorem supported (h : True) : True := h\n")
        scanner = self.repo / gate.SCANNER
        scanner.parent.mkdir(parents=True)
        scanner.write_bytes((ROOT / gate.SCANNER).read_bytes())
        self.commit("frozen family")
        self.base = self.git("rev-parse", "HEAD").decode().strip()
        self.base_patch = patch.object(census, "BASE", self.base)
        self.base_patch.start()
        self.addCleanup(self.base_patch.stop)
        gate_base_patch = patch.object(gate, "BASE", self.base)
        gate_base_patch.start()
        self.addCleanup(gate_base_patch.stop)
        scanner.write_bytes(scanner.read_bytes().replace(
            b"c6f550e281a7e5affa9a99bc2cdaed556dec00e4", self.base.encode()))
        self.raw = census.render(census.census(self.repo)).encode()
        self.receipt = {"inventory_sha256": gate.sha(self.raw), "base": self.base,
                        "summary": json.loads(self.raw)["summary"]}
        receipt = self.repo / gate.RECEIPT
        receipt.parent.mkdir(parents=True)
        receipt.write_text(json.dumps(self.receipt))
        self.commit("retired member final")
        self.member = self.git("rev-parse", "HEAD").decode().strip()
        self.member_patch = patch.object(gate, "MEMBER_HEAD", self.member)
        self.member_patch.start()
        self.addCleanup(self.member_patch.stop)
        self.inventory = Path(self.tmp.name) / "inventory.json"
        self.inventory.write_bytes(self.raw)

    def git(self, *args):
        return subprocess.check_output(["git", "-C", str(self.repo), *args], stderr=subprocess.PIPE)

    def commit(self, message):
        self.git("add", ".")
        self.git("-c", "user.name=Fixture", "-c", "user.email=fixture@example.invalid",
                 "commit", "-qm", message)

    def test_exact_frozen_inputs_accept_on_successor(self):
        report = gate.verify(self.repo, self.inventory)
        self.assertEqual(report["source_files_verified"], 1)
        self.assertEqual(report["member_head"], self.member)
        self.assertEqual(report["successor_head"], self.member)
        self.assertIn("no Lean", report["boundary"])

    def test_original_branch_gate_remains_unchanged(self):
        self.assertIn("wrong branch", (ROOT / "scripts/h62/item4/generic-p10/accept.py").read_text())
        self.git("switch", "-qc", "unassigned-branch")
        with self.assertRaisesRegex(ValueError, "wrong successor branch"):
            gate.verify(self.repo, self.inventory)

    def test_missing_final_head_ancestry_refused(self):
        self.git("checkout", "--orphan", "unrelated")
        self.commit("unrelated root")
        self.git("branch", "-D", gate.SUCCESSOR_BRANCH)
        self.git("branch", "-m", gate.SUCCESSOR_BRANCH)
        with self.assertRaises(subprocess.CalledProcessError):
            gate.verify(self.repo, self.inventory)

    def test_tampered_receipt_refused(self):
        (self.repo / gate.RECEIPT).write_text("{}")
        with self.assertRaisesRegex(ValueError, "receipt changed"):
            gate.verify(self.repo, self.inventory)

    def test_tampered_scanner_refused(self):
        marker = Path(self.tmp.name) / "unverified-scanner-executed"
        with (self.repo / gate.SCANNER).open("a") as f:
            f.write("\nfrom pathlib import Path\nPath(" + repr(str(marker)) + ").touch()\n")
        with self.assertRaisesRegex(ValueError, "scanner changed"):
            gate.verify(self.repo, self.inventory)
        self.assertFalse(marker.exists(), "unverified scanner must never execute")

    def test_changed_premise_with_same_counts_refused(self):
        source = self.repo / self.path
        source.write_text(source.read_text().replace("h : True", "h : False"))
        with self.assertRaisesRegex(ValueError, "current source differs"):
            gate.verify(self.repo, self.inventory)

    def test_staged_only_corruption_refused(self):
        source = self.repo / self.path
        original = source.read_bytes()
        source.write_bytes(original.replace(b"h : True", b"h : False"))
        self.git("add", self.path)
        source.write_bytes(original)
        with self.assertRaisesRegex(ValueError, "staged frozen family differs"):
            gate.verify(self.repo, self.inventory)

    def test_extra_untracked_source_refused(self):
        (self.repo / census.FAMILY / "Untracked.lean").write_text("theorem extra : True := True.intro\n")
        with self.assertRaisesRegex(ValueError, "family file set"):
            gate.verify(self.repo, self.inventory)

    def test_missing_source_refused(self):
        (self.repo / self.path).unlink()
        with self.assertRaisesRegex(ValueError, "family file set"):
            gate.verify(self.repo, self.inventory)

    def test_identical_source_symlink_refused(self):
        source = self.repo / self.path
        target = Path(self.tmp.name) / "same-source"
        target.write_bytes(source.read_bytes())
        source.unlink()
        source.symlink_to(target)
        with self.assertRaisesRegex(ValueError, "symlink"):
            gate.verify(self.repo, self.inventory)

    def test_checksum_tamper_refused(self):
        self.inventory.write_bytes(self.raw + b" ")
        with self.assertRaisesRegex(ValueError, "checksum"):
            gate.verify(self.repo, self.inventory)

    def test_rehashed_forged_source_or_statement_refused(self):
        original = json.loads(self.raw)
        frozen = {self.path: (self.repo / self.path).read_bytes()}
        for mutation, reason in [("hash", "unpinned source"), ("statement", "census differs"),
                                 ("remove", "family file set"), ("duplicate", "family file set")]:
            with self.subTest(mutation=mutation):
                forged = copy.deepcopy(original)
                if mutation == "hash": forged["files"][0]["source_sha256"] = "0" * 64
                elif mutation == "statement": forged["files"][0]["declarations"][0]["statement"] = "False"
                elif mutation == "remove": forged["files"] = []
                else: forged["files"] += copy.deepcopy(forged["files"])
                raw = census.render(forged).encode()
                receipt = dict(self.receipt, inventory_sha256=gate.sha(raw))
                with self.assertRaisesRegex(ValueError, reason):
                    gate.verify_inventory(raw, receipt, frozen, frozen, self.raw)


if __name__ == "__main__":
    unittest.main()
