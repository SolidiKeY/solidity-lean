#!/usr/bin/env python3
"""Black-box identity controls for the production handoff executable.

These tests use disposable Git repositories and synthetic gate receipts;
they are not evidence that any Solidity/Lean build passed.
"""
import json
import os
from pathlib import Path
import pwd
import subprocess
import tempfile
import unittest

SCRIPT = Path(__file__).resolve().parents[3] / "scripts/coord-tools/handoff.sh"


class GateIdentity(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(prefix="tf-handoff-")
        self.root = Path(self.tmp.name)
        self.repo = self.root / "repo"
        self.repo.mkdir()
        self.git("init", "-q")
        (self.repo / "tracked").write_text("clean\n")
        self.git("add", "tracked")
        self.git("-c", "user.name=Fixture", "-c", "user.email=fixture@example.invalid",
                 "commit", "-qm", "fixture")
        self.head = self.git("rev-parse", "HEAD").strip()
        self.output = self.root / "output"
        self.output.mkdir()
        self.sentinels = {"HANDOFF.md": b"existing handoff\n",
                          "CLOUDVM-RESULT.json": b"existing result\n"}
        for name, data in self.sentinels.items():
            (self.output / name).write_bytes(data)

    def tearDown(self):
        self.tmp.cleanup()

    def git(self, *args):
        return subprocess.check_output(["git", *args], cwd=self.repo, text=True,
                                       stderr=subprocess.PIPE)

    def gate(self, name="gate", identity=None, row="PASS"):
        p = self.root / name
        p.mkdir()
        (p / "gates.tsv").write_text(f"{row}\tfixture\t0\tfixture.log\ttrue\n")
        if identity is not None:
            (p / "HEAD").write_bytes(identity)
        return p

    def invoke(self, gates, status="done", demote=None, default_output=False, notes=None):
        env = os.environ.copy()
        env.update(HANDOFF_STATUS=status, HANDOFF_BASE=self.head,
                   HANDOFF_GATES=":".join(map(str, gates)), HANDOFF_OUT=str(self.output),
                   HOME=str(self.root), GIT_CONFIG_NOSYSTEM="1", GIT_CONFIG_GLOBAL=os.devnull)
        if default_output:
            env.pop("HANDOFF_OUT")
            env["TMPDIR"] = str(self.root / "defaults")
        if notes is not None:
            env["HANDOFF_CHECKPOINTS"] = "first=done,remaining=blocked"
        command = ["bash", str(SCRIPT)] + ([] if notes is None else [str(notes)])
        return subprocess.run(command, cwd=self.repo, env=env,
                              capture_output=True, timeout=10, preexec_fn=demote)

    def refused(self, gates, diagnostic=None, **kwargs):
        result = self.invoke(gates, **kwargs)
        self.assertNotEqual(result.returncode, 0, result.stdout.decode(errors="replace"))
        if diagnostic is not None:
            self.assertIn(diagnostic, result.stderr.decode(errors="replace"))
        for name, data in self.sentinels.items():
            self.assertEqual((self.output / name).read_bytes(), data)

    def test_missing_identity_rejected(self):
        self.refused([self.gate()], diagnostic="done refused: missing or invalid gate HEAD:")

    def test_empty_identity_rejected(self):
        self.refused([self.gate(identity=b"")],
                     diagnostic="done refused: gates ran on another commit:")

    def test_malformed_identities_rejected(self):
        for i, raw in enumerate([b"HEAD\n", self.head[:12].encode(), b"z" * 40,
                                 self.head.encode() + b"\nextra", b"\xff\xfe"]):
            with self.subTest(identity=raw):
                diagnostic = ("done refused: unreadable gate HEAD:" if raw == b"\xff\xfe"
                              else "done refused: gates ran on another commit:")
                self.refused([self.gate(str(i), raw)], diagnostic=diagnostic)

    def test_stale_commit_rejected(self):
        gate = self.gate(identity=(self.head + "\n").encode())
        self.git("-c", "user.name=Fixture", "-c", "user.email=fixture@example.invalid",
                 "commit", "--allow-empty", "-qm", "new commit")
        self.head = self.git("rev-parse", "HEAD").strip()
        self.refused([gate], diagnostic="done refused: gates ran on another commit:")

    def test_mixed_current_and_missing_rejected_in_both_orders(self):
        current = self.gate("current", (self.head + "\n").encode())
        missing = self.gate("missing")
        self.refused([current, missing], diagnostic="done refused: missing or invalid gate HEAD:")
        self.refused([missing, current], diagnostic="done refused: missing or invalid gate HEAD:")

    def test_nonfile_identity_rejected(self):
        gate = self.gate()
        (gate / "HEAD").mkdir()
        self.refused([gate], diagnostic="done refused: missing or invalid gate HEAD:")

    def test_unreadable_identity_rejected(self):
        gate = self.gate(identity=(self.head + "\n").encode())
        demote = None
        if os.geteuid() == 0:
            account = pwd.getpwnam("nobody")
            for directory, dirs, files in os.walk(self.root):
                os.chown(directory, account.pw_uid, account.pw_gid)
                for name in files:
                    os.chown(Path(directory) / name, account.pw_uid, account.pw_gid)
            def demote():
                os.setgroups([])
                os.setgid(account.pw_gid)
                os.setuid(account.pw_uid)
        (gate / "HEAD").chmod(0)
        try:
            self.refused([gate], demote=demote, diagnostic="done refused: unreadable gate HEAD:")
        finally:
            (gate / "HEAD").chmod(0o600)

    def test_current_identities_preserve_done_success(self):
        gates = [self.gate("one", (self.head + "\n").encode()),
                 self.gate("with spaces", (" \n" + self.head + "\n\t").encode())]
        result = self.invoke(gates)
        self.assertEqual(result.returncode, 0, result.stderr.decode())
        saved = json.loads((self.output / "CLOUDVM-RESULT.json").read_text())
        self.assertEqual(saved["head"], self.head)
        self.assertEqual(saved["status"], "done")
        self.assertEqual(len(saved["gates"]), 2)

    def test_failed_gate_still_rejected(self):
        self.refused([self.gate(identity=self.head.encode(), row="FAIL")],
                     diagnostic="done requires passing gates and a clean tracked tree")

    def test_dirty_worktree_still_rejected(self):
        gate = self.gate(identity=self.head.encode())
        (self.repo / "tracked").write_text("dirty\n")
        self.refused([gate], diagnostic="done requires passing gates and a clean tracked tree")

    def test_default_output_observed_outside_checkout_with_complete_artifacts(self):
        gate = self.gate(identity=(self.head + "\n").encode())
        notes = self.root / "notes.txt"
        notes.write_text("exact notes\nsecond line λ\n")
        result = self.invoke([gate], default_output=True, notes=notes)
        self.assertEqual(result.returncode, 0, result.stderr.decode())
        observed = json.loads(result.stdout.decode().split("CLOUDVM-RESULT\n", 1)[1]
                              .rsplit("END-CLOUDVM-RESULT", 1)[0])
        handoff = Path(observed["artifacts"]["handoff"])
        expected = self.root / "defaults" / ("coord-handoff-" + self.head[:12])
        self.assertEqual(handoff, expected / "HANDOFF.md")
        self.assertNotEqual(handoff, self.output / "HANDOFF.md")
        self.assertFalse(handoff.is_relative_to(self.repo))
        self.assertEqual({p.name for p in handoff.parent.iterdir()},
                         {"HANDOFF.md", "CLOUDVM-RESULT.json"})
        saved = json.loads((handoff.parent / "CLOUDVM-RESULT.json").read_text())
        self.assertEqual(saved, observed)
        self.assertEqual(saved["base"], self.head)
        self.assertEqual(saved["head"], self.head)
        self.assertEqual(saved["repository"], str(self.repo))
        self.assertEqual(saved["notes"], notes.read_text())
        self.assertEqual(saved["checkpoints"],
                         [{"name": "first", "status": "done"},
                          {"name": "remaining", "status": "blocked"}])
        self.assertIn(notes.read_text(), handoff.read_text())

    def test_no_gates_still_rejected(self):
        self.refused([], diagnostic="done requires passing gates and a clean tracked tree")

    def test_partial_and_blocked_keep_existing_semantics(self):
        missing = self.gate("missing", row="FAIL")
        stale = self.gate("stale", b"0" * 40)
        for status in ["partial", "blocked"]:
            with self.subTest(status=status):
                result = self.invoke([missing, stale], status=status)
                self.assertEqual(result.returncode, 0, result.stderr.decode())
                saved = json.loads((self.output / "CLOUDVM-RESULT.json").read_text())
                self.assertEqual(saved["status"], status)


if __name__ == "__main__":
    unittest.main()
