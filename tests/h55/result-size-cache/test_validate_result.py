import ast
import importlib.util
import shutil
import subprocess
import tempfile
from types import SimpleNamespace
import json
from pathlib import Path
import unittest

ROOT = Path(__file__).resolve().parents[3]
SPEC = importlib.util.spec_from_file_location("h55_validate", ROOT / "scripts/h55/result-size-cache/validate_result.py")
validator = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(validator)


def valid():
    return dict(batch="batch", slug="slug", status="partial", branch="branch", base="a"*40, head=None,
                repository="/repo", checkpoints=[], gates=[], reviews="pending", limitations="pending", questions=[], waits=[],
                artifacts=dict(original_patch=None, handoff=None, evidence=None, checksums=None))


def wrap(body):
    return "context\nCLOUDVM-RESULT\n" + body + "\nEND-CLOUDVM-RESULT\n"


class ResultValidation(unittest.TestCase):
    def test_valid_report(self):
        self.assertEqual(validator.validate(wrap(json.dumps(valid()))), valid())

    def test_missing_extra_and_bad_enum(self):
        for mutate in (lambda d: d.pop("head"), lambda d: d.update(extra=1), lambda d: d.update(status="complete")):
            value = valid(); mutate(value)
            with self.assertRaises(validator.ResultError): validator.validate(wrap(json.dumps(value)))

    def test_waits_are_required_and_typed(self):
        value = valid(); value["waits"] = [{"lane": "coordinator", "item": "trusted base"}]
        self.assertEqual(validator.validate(wrap(json.dumps(value))), value)
        for bad in ([{"lane":"coordinator"}], [{"lane":"", "item":"base"}], [{"lane":" ", "item":"base"}], [{"lane":"x", "item":"y", "extra":1}]):
            value["waits"] = bad
            with self.assertRaises(validator.ResultError): validator.validate(wrap(json.dumps(value)))
        value.pop("waits")
        with self.assertRaises(validator.ResultError): validator.validate(wrap(json.dumps(value)))

    def test_done_cannot_have_waits(self):
        value = valid(); value.update(status="done", head="b" * 40,
            checkpoints=[{"name":"item", "status":"done"}],
            gates=[{"command":"check", "status":"pass", "evidence":"ok"}],
            artifacts={k:"/artifact" for k in value["artifacts"]})
        self.assertEqual(validator.validate(wrap(json.dumps(value))), value)
        value["waits"] = [{"lane":"coordinator", "item":"integration"}]
        with self.assertRaises(validator.ResultError): validator.validate(wrap(json.dumps(value)))

    def test_duplicate_and_non_json_constants(self):
        for body in ("{\"status\":1,\"status\":2}", "{\"x\":NaN}"):
            with self.assertRaises(validator.ResultError): validator.validate(wrap(body))

    def test_markers_and_trailing_json(self):
        for text in ("CLOUDVM-RESULT\n{}", wrap("{}") + wrap("{}"), wrap("{} {}"), " CLOUDVM-RESULT\n{}\nEND-CLOUDVM-RESULT "):
            with self.assertRaises(validator.ResultError): validator.validate(text)

    def test_nested_constraints_and_done_artifacts(self):
        value = valid(); value["questions"] = [{"id":"Q1", "sources":["size"], "question":"Which?", "options":["one"]}]
        with self.assertRaises(validator.ResultError): validator.validate(wrap(json.dumps(value)))
        value = valid(); value["base"] += "\n"
        with self.assertRaises(validator.ResultError): validator.validate(wrap(json.dumps(value)))
        value = valid(); value["status"] = "done"
        with self.assertRaises(validator.ResultError): validator.validate(wrap(json.dumps(value)))

    def test_exact_error(self):
        with self.assertRaisesRegex(validator.ResultError, "^expected exactly one ordered marker pair on separate lines$"):
            validator.validate("bad")

    def test_legacy_producer_and_strict_turn_association(self):
        original = Path("/workspace/h55-coordinator-inputs/coordinator-originals/poll.py")
        if not original.is_file(): self.skipTest("coordinator snapshot unavailable")
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp); poll = root / "poll.py"; shutil.copyfile(original, poll)
            patch = ROOT / "scripts/h55/result-size-cache/poll.py.patch"
            subprocess.run(["patch", "-p1", "-i", str(patch)], cwd=root, check=True, capture_output=True)
            tree = ast.parse(poll.read_text())
            names = ("result_block", "strict_result_block", "strict_turn_result", "inspect")
            funcs = [n for n in tree.body if isinstance(n, ast.FunctionDef) and n.name in names]
            state = root / "state"; (state / "raw").mkdir(parents=True)
            payload = {"recentTurns": [], "items": [], "goal": {}}
            def run(*args, **kwargs):
                (state / "raw" / "batch__slug.json").write_text(json.dumps(payload))
                return SimpleNamespace(returncode=0)
            ns = {"ResultError": validator.ResultError, "validate": validator.validate, "os": __import__("os"), "json": json,
                  "subprocess": SimpleNamespace(run=run), "sys": __import__("sys"), "re": __import__("re"),
                  "STATE": str(state), "BATCHES": tmp, "SKILL": "unused", "H55_STRICT_BATCHES": set()}
            exec(compile(ast.Module(body=funcs, type_ignores=[]), str(poll), "exec"), ns)
            # Use the real existing producer, with its unchanged legacy keys.
            repo = root / "repo"; repo.mkdir()
            subprocess.run(["git", "init", "-q", str(repo)], check=True)
            subprocess.run(["git", "-C", str(repo), "config", "user.email", "test@example.invalid"], check=True)
            subprocess.run(["git", "-C", str(repo), "config", "user.name", "Test"], check=True)
            subprocess.run(["git", "-C", str(repo), "commit", "--allow-empty", "-qm", "base"], check=True)
            import os
            env = os.environ.copy(); env.update(HANDOFF_BASE="HEAD", HANDOFF_OUT=str(root / "handoff"), HANDOFF_BATCH="batch", HANDOFF_SLUG="slug")
            legacy = subprocess.run(["bash", str(ROOT / "scripts/coord-tools/handoff.sh")], cwd=repo, env=env, check=True, text=True, capture_output=True).stdout
            payload.update(recentTurns=[{"id":"new", "status":"completed"}], items=[{"type":"agentMessage", "text":legacy}])
            self.assertIn("commits", ns["inspect"]("batch", "slug")["result"])
            ns["H55_STRICT_BATCHES"] = {"batch"}
            # An older final and missing association must never satisfy this turn.
            payload["items"] = [{"type":"agentMessage", "turnId":"old", "phase":"final_answer", "text":wrap(json.dumps(valid()))}]
            with self.assertRaisesRegex(RuntimeError, "expected exactly one final message for completed turn"):
                ns["inspect"]("batch", "slug")
            payload["items"].insert(0, {"type":"agentMessage", "text":wrap(json.dumps(valid()))})
            with self.assertRaisesRegex(RuntimeError, "expected exactly one final message for completed turn"):
                ns["inspect"]("batch", "slug")
            current = {"type":"agentMessage", "turnId":"new", "phase":"final_answer", "text":wrap(json.dumps(valid()))}
            payload["items"].insert(0, current)
            self.assertEqual(ns["inspect"]("batch", "slug")["result"], valid())
            payload["items"].insert(0, current.copy())
            with self.assertRaisesRegex(RuntimeError, "expected exactly one final message for completed turn"):
                ns["inspect"]("batch", "slug")
            payload["items"] = [dict(current, text="CLOUDVM-RESULT\n{}")]
            with self.assertRaisesRegex(RuntimeError, "CLOUDVM-RESULT invalid: expected exactly one ordered marker pair"):
                ns["inspect"]("batch", "slug")
            payload["items"] = [dict(current, text=legacy)]
            with self.assertRaisesRegex(RuntimeError, "CLOUDVM-RESULT invalid:"):
                ns["inspect"]("batch", "slug")
            wrong = valid(); wrong["slug"] = "other"
            payload["items"] = [dict(current, text=wrap(json.dumps(wrong)))]
            with self.assertRaisesRegex(RuntimeError, "batch or slug mismatch"):
                ns["inspect"]("batch", "slug")
            payload["items"] = [dict(current, phase="commentary")]
            with self.assertRaisesRegex(RuntimeError, "expected exactly one final message"):
                ns["inspect"]("batch", "slug")
            payload["items"] = [current]; payload["recentTurns"] = [{"id":"new", "status":"inProgress"}]
            self.assertIsNone(ns["inspect"]("batch", "slug")["result"])
            payload["recentTurns"] = [{"status":"completed"}]
            with self.assertRaisesRegex(RuntimeError, "completed turn has no identity"):
                ns["inspect"]("batch", "slug")

    def test_full_poller_reports_exact_validation_error(self):
        original = Path("/workspace/h55-coordinator-inputs/coordinator-originals/poll.py")
        if not original.is_file(): self.skipTest("coordinator snapshot unavailable")
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp); poll = root / "poll.py"; shutil.copyfile(original, poll)
            shutil.copyfile(original, root / "poll.py.bak-h55")
            patch = ROOT / "scripts/h55/result-size-cache/poll.py.patch"
            subprocess.run(["patch", "-p1", "-i", str(patch)], cwd=root, check=True, capture_output=True)
            for name in ("validate_result.py", "result_schema.json"):
                shutil.copyfile(ROOT / "scripts/h55/result-size-cache" / name, root / name)
            state = root / ".local/state/cloudvm-coord"; (state / "msgs").mkdir(parents=True)
            (state / "msgs/v09.txt").write_text("header\n")
            (state / "digest").mkdir()
            (state / "digest/batch__slug.json").write_text(json.dumps({"result": {"status": "done"}}))
            (state / "poll-state.json").write_text(json.dumps({"batch/slug": {"result": {"status": "done"}}}))
            fake = root / "fake_api.py"
            fake.write_text("import json,sys\np=sys.argv[sys.argv.index('--out')+1]\njson.dump({'recentTurns':[{'id':'turn','status':'completed'}], 'items':[{'type':'agentMessage','turnId':'turn','phase':'final_answer','text':'CLOUDVM-RESULT\\n{}'}]},open(p,'w'))\n")
            harness = root / "run.py"
            harness.write_text("import poll,sys\npoll.tasks=lambda: iter([('batch','slug')])\npoll.SKILL=" + repr(str(fake)) + "\npoll.sample_pilot_tokens=lambda _: None\npoll.sync_master=lambda: None\nsys.argv=['poll.py','--once']\npoll.main()\n")
            import os
            env = os.environ.copy(); env.update(HOME=tmp, PYTHONDONTWRITEBYTECODE="1", H55_STRICT_BATCHES="batch")
            result = subprocess.run(["python3", str(harness)], cwd=root, env=env, text=True, capture_output=True, timeout=10)
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertIn("ERROR batch/slug CLOUDVM-RESULT invalid: expected exactly one ordered marker pair on separate lines", result.stdout)
            self.assertEqual((root / "poll.py.bak-h55").read_bytes(), original.read_bytes())
            digest = json.loads((state / "digest/batch__slug.json").read_text())
            self.assertIsNone(digest["result"])
            self.assertIn("CLOUDVM-RESULT invalid:", digest["error"])
            saved = json.loads((state / "poll-state.json").read_text())
            self.assertNotIn("result", saved["batch/slug"])
            (state / "digest/batch__slug.json").write_text(json.dumps({"result": {"status": "done"}}))
            (state / "poll-state.json").write_text(json.dumps({"batch/slug": {"result": {"status": "done"}}}))
            failing = root / "run-failing.py"
            failing.write_text("import tempfile\ndef fail(*a,**kw): raise PermissionError('simulated write refusal')\ntempfile.mkstemp=fail\n" + harness.read_text())
            result = subprocess.run(["python3", str(failing)], cwd=root, env=env, text=True, capture_output=True, timeout=10)
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertIn("digest invalidation failed: simulated write refusal", result.stdout)
            saved = json.loads((state / "poll-state.json").read_text())
            self.assertNotIn("result", saved["batch/slug"])
            self.assertEqual(saved["batch/slug"]["digestError"], "simulated write refusal")
            self.assertIsNotNone(json.loads((state / "digest/batch__slug.json").read_text())["result"])

    def test_legacy_poller_can_start_without_validator_install(self):
        original = Path("/workspace/h55-coordinator-inputs/coordinator-originals/poll.py")
        if not original.is_file(): self.skipTest("coordinator snapshot unavailable")
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp); shutil.copyfile(original, root / "poll.py")
            patch = ROOT / "scripts/h55/result-size-cache/poll.py.patch"
            subprocess.run(["patch", "-p1", "-i", str(patch)], cwd=root, check=True, capture_output=True)
            state = root / ".local/state/cloudvm-coord/msgs"; state.mkdir(parents=True)
            (state / "v09.txt").write_text("header\n")
            import os
            env = os.environ.copy(); env.update(HOME=tmp, PYTHONDONTWRITEBYTECODE="1")
            result = subprocess.run(["python3", "-c", "import poll; print(poll.validate is None)"], cwd=root, env=env, text=True, capture_output=True)
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual(result.stdout.strip(), "True")
            (root / "validate_result.py").write_text("import missing_transitive_dependency\n")
            result = subprocess.run(["python3", "-c", "import poll; print(poll.validate is None)"], cwd=root, env=env, text=True, capture_output=True)
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual(result.stdout.strip(), "True")

    def test_missing_schema_is_prefixed_result_error(self):
        with self.assertRaisesRegex(validator.ResultError, "^schema unavailable or invalid:"):
            validator.validate(wrap(json.dumps(valid())), "/nonexistent/h55-schema.json")

    def test_missing_dependency_fails_closed(self):
        saved = validator.jsonschema
        try:
            validator.jsonschema = None
            with self.assertRaisesRegex(validator.ResultError, "^jsonschema dependency unavailable$"):
                validator.validate(wrap(json.dumps(valid())))
        finally:
            validator.jsonschema = saved


if __name__ == "__main__": unittest.main()
