import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest

TOOL = Path(__file__).resolve().parents[3] / "scripts/coord-tools/handoff.sh"

class HandoffCases(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(prefix="terra handoff ")
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.repo = self.root / "repo"
        self.repo.mkdir()
        self.git("init", "-q")
        self.git("config", "user.name", "Fixture")
        self.git("config", "user.email", "fixture@example.invalid")
        (self.repo / "Old.lean").write_text("old\n")
        (self.repo / "tracked").write_text("base\n")
        self.git("add", ".")
        self.git("commit", "-qm", "base")
        self.base = self.git("rev-parse", "HEAD")
        (self.repo / "Old.lean").unlink()
        (self.repo / "New.lean").write_text("new\n")
        self.git("add", "-A")
        self.git("commit", "-qm", "change modules")
        self.head = self.git("rev-parse", "HEAD")
        self.branch = self.git("branch", "--show-current")
        self.out = self.root / "out"
        self.env = {k:v for k,v in os.environ.items() if not k.startswith("HANDOFF_")}
        self.env.update(HANDOFF_BASE=self.base, HANDOFF_BATCH="batch", HANDOFF_SLUG="slug", TMPDIR=str(self.root))

    def git(self, *args):
        return subprocess.check_output(["git", *map(str, args)], cwd=self.repo, text=True).strip()

    def invoke(self, *args, **updates):
        env = dict(self.env, **updates)
        return subprocess.run(["bash", str(TOOL), *map(str, args)], cwd=self.repo, env=env, text=True, capture_output=True)

    def gate(self, status="PASS", head=True):
        d = self.root / "gate"
        d.mkdir(exist_ok=True)
        (d / "gates.tsv").write_text(status + "\tcheck\t1\tfixture.log\tcheck --flag\n")
        if head is True:
            (d / "HEAD").write_text(self.head + "\n")
        elif head:
            (d / "HEAD").write_text(head + "\n")
        return d

    def expected(self, out, status="partial", gates=None, checkpoints=None, notes=""):
        return dict(batch="batch", slug="slug", status=status, branch=self.branch,
                    base=self.base, head=self.head, repository=str(self.repo),
                    commits=[dict(sha=self.head, subject="change modules")],
                    modules_changed=["New"], modules_deleted=["Old"],
                    checkpoints=checkpoints or [], gates=gates or [], notes=notes,
                    questions=[], artifacts=dict(handoff=str(out / "HANDOFF.md")))

    def passing_gate(self):
        return [dict(gate="check", command="check --flag", status="pass", seconds=1.0, evidence="fixture.log")]

    def assert_artifacts(self, result, expected, out):
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual({p.name for p in out.iterdir()}, {"HANDOFF.md", "CLOUDVM-RESULT.json"})
        body = json.dumps(expected, indent=2, ensure_ascii=False) + "\n"
        self.assertEqual(json.loads((out / "CLOUDVM-RESULT.json").read_text()), expected)
        self.assertEqual((out / "CLOUDVM-RESULT.json").read_text(), body)
        self.assertEqual((out / "HANDOFF.md").read_bytes().decode(), "# Handoff\n\n" + self.head + " change modules\n\n```json\n" + body + "```\n\n" + expected["notes"])
        self.assertEqual(result.stdout, "CLOUDVM-RESULT\n" + body + "END-CLOUDVM-RESULT\n")

    def assert_refused(self, result):
        self.assertNotEqual(result.returncode, 0, result.stdout)
        self.assertIn("handoff:", result.stderr)
        self.assertFalse(self.out.exists())

    def test_partial_default(self):
        result = self.invoke(HANDOFF_OUT=str(self.out))
        self.assert_artifacts(result, self.expected(self.out), self.out)

    def test_done_passing(self):
        gate = self.gate()
        result = self.invoke(HANDOFF_OUT=str(self.out), HANDOFF_STATUS="done", HANDOFF_GATES=str(gate))
        self.assert_artifacts(result, self.expected(self.out, status="done", gates=self.passing_gate()), self.out)

    def test_done_failed_gate(self):
        gate = self.gate(status="FAIL")
        result = self.invoke(HANDOFF_OUT=str(self.out), HANDOFF_STATUS="done", HANDOFF_GATES=str(gate))
        self.assert_refused(result)
        self.assertIn("done requires passing gates and a clean tracked tree", result.stderr)

    def test_done_stale_head(self):
        gate = self.gate(head=self.base)
        result = self.invoke(HANDOFF_OUT=str(self.out), HANDOFF_STATUS="done", HANDOFF_GATES=str(gate))
        self.assert_refused(result)
        self.assertIn("another commit", result.stderr)

    def test_done_dirty_tracked(self):
        gate = self.gate()
        (self.repo / "tracked").write_text("dirty\n")
        result = self.invoke(HANDOFF_OUT=str(self.out), HANDOFF_STATUS="done", HANDOFF_GATES=str(gate))
        self.assert_refused(result)
        self.assertIn("done requires passing gates and a clean tracked tree", result.stderr)

    def test_missing_gate_head(self):
        gate = self.gate(head=False)
        self.assertFalse((gate / "HEAD").exists())
        result = self.invoke(HANDOFF_OUT=str(self.out), HANDOFF_STATUS="done", HANDOFF_GATES=str(gate))
        self.assert_refused(result)

    def test_notes_crlf(self):
        notes = self.root / "notes"
        notes.write_bytes(b"first\r\nsecond\r\n")
        result = self.invoke(notes, HANDOFF_OUT=str(self.out))
        self.assert_artifacts(result, self.expected(self.out, notes="first\r\nsecond\r\n"), self.out)

    def test_notes_unicode(self):
        notes = self.root / "notes"
        notes.write_text("proof λ 漢字\n")
        result = self.invoke(notes, HANDOFF_OUT=str(self.out))
        self.assert_artifacts(result, self.expected(self.out, notes="proof λ 漢字\n"), self.out)

    def test_outside_checkout_default(self):
        out = self.root / ("coord-handoff-" + self.head[:12])
        result = self.invoke()
        self.assertEqual(result.returncode, 0, result.stderr)
        observed = json.loads(result.stdout.removeprefix("CLOUDVM-RESULT\n")
                              .removesuffix("END-CLOUDVM-RESULT\n"))
        observed_handoff = Path(observed["artifacts"]["handoff"])
        self.assertTrue(observed_handoff.is_absolute())
        self.assertFalse(observed_handoff.is_relative_to(self.repo))
        self.assertEqual(observed_handoff, out / "HANDOFF.md")
        self.assert_artifacts(result, self.expected(out), out)

    def test_checkpoint_statuses(self):
        checkpoints = [dict(name="one", status="done"), dict(name="two", status="partial"), dict(name="three", status="blocked")]
        result = self.invoke(HANDOFF_OUT=str(self.out), HANDOFF_CHECKPOINTS="one=done,two=partial,three=blocked")
        self.assert_artifacts(result, self.expected(self.out, checkpoints=checkpoints), self.out)

    def test_base_and_head(self):
        result = self.invoke(HANDOFF_OUT=str(self.out))
        self.assert_artifacts(result, self.expected(self.out), self.out)
        self.assertNotEqual(self.base, self.head)
        self.assertEqual(self.git("merge-base", self.base, self.head), self.base)

    def test_malformed_status(self):
        result = self.invoke(HANDOFF_OUT=str(self.out), HANDOFF_STATUS="finished")
        self.assert_refused(result)
        self.assertIn("invalid status", result.stderr)
