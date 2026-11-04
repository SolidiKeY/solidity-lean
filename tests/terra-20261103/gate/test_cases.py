import os
import json
import hashlib
import re
import time
import shutil
from pathlib import Path
import subprocess
import tempfile
import unittest

TOOL = Path(__file__).resolve().parents[3] / "scripts/coord-tools/gate.sh"

class GateCases(unittest.TestCase):
    def setUp(self):
        # Integration checkers currently require an unencoded checkout URL.
        # Dedicated per-file/relative-log controls below still exercise spaces.
        self.tmp = tempfile.TemporaryDirectory(prefix="terra_gate_")
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.repo = self.root / "repo"
        self.repo.mkdir()
        self.home = self.root / "home"
        self.home.mkdir()
        self.env = {k: v for k, v in os.environ.items()
                    if not k.startswith(("GIT_", "GATE_")) and k not in ("BASH_ENV", "ENV")}
        self.env.update(HOME=str(self.home), ELAN_HOME=str(self.home / ".elan"),
                        XDG_CACHE_HOME=str(self.home / ".cache"),
                        XDG_CONFIG_HOME=str(self.home / ".config"),
                        GIT_CONFIG_GLOBAL=os.devnull, GIT_CONFIG_NOSYSTEM="1",
                        GIT_AUTHOR_NAME="Fixture", GIT_AUTHOR_EMAIL="fixture@example.invalid",
                        GIT_COMMITTER_NAME="Fixture", GIT_COMMITTER_EMAIL="fixture@example.invalid",
                        LAKE_CACHE_DIR="", LAKE_ARTIFACT_CACHE="false")
        self.git("init", "-q")
        for path, content in {"Solidity/A.lean":"def a := 1\n", "Solidity/B.lean":"import Solidity.A\n", "Solidity/C.lean":"import Solidity.B\n", "Solidity/Z.lean":"def z := 1\n", "Solidity.lean":"import Solidity.C\n"}.items():
            self.write(path, content)
        self.git("add", ".")
        self.git("commit", "-qm", "base")
        self.base = self.git("rev-parse", "HEAD")
        self.branch = self.git("branch", "--show-current")
        self.bin = self.root / "bin"
        self.bin.mkdir()
        self.calls = self.root / "calls"
        lake = self.bin / "lake"
        lake.write_text("#!/bin/sh\nprintf '%s\\n' \"lake $*\" >> \"$CALLS\"\nif [ \"${FAIL_TOOL:-}\" = lake ]; then echo 'fixture backend refused: lake' >&2; exit 23; fi\n")
        lake.chmod(0o755)
        # run-lean and corpus prepend this private path: they cannot escape to
        # the host's installed elan even when one is present.
        elan = self.home / ".elan/bin"
        elan.mkdir(parents=True)
        (elan / "lake").symlink_to(lake)
        self.logs = self.root / "logs"
        self.env.update(PATH=str(self.bin)+os.pathsep+os.environ["PATH"], CALLS=str(self.calls), GATE_BASE=self.base, GATE_LOGS=str(self.logs), TMPDIR=str(self.root))

    def write(self, name, contents):
        path = self.repo / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(contents)

    def git(self, *args):
        return subprocess.check_output(["git", *map(str, args)], cwd=self.repo, env=self.env, text=True).strip()

    def run_gate(self, *args, cwd=None, **updates):
        started = time.monotonic()
        result = subprocess.run(["/bin/bash", str(TOOL), *args], cwd=cwd or self.repo, env=dict(self.env, **updates), text=True, capture_output=True, timeout=30)
        self.record("gate", {"arguments": args, "exit": result.returncode,
                            "seconds": time.monotonic() - started,
                            "stdout": result.stdout, "stderr": result.stderr})
        return result

    def record(self, kind, payload):
        # Optional external receipts; never change expectations from a log.
        directory = os.environ.get("TF_GATE_EVIDENCE")
        if directory:
            target = Path(directory)
            target.mkdir(parents=True, exist_ok=True)
            with (target / (self._testMethodName + ".jsonl")).open("a") as stream:
                stream.write(json.dumps({"kind": kind, **payload}) + "\n")

    def calls_read(self):
        return self.calls.read_text().splitlines() if self.calls.exists() else []

    def inspect(self, result, names, statuses=None, logs=None):
        logs = logs or self.logs
        statuses = statuses or ["PASS"] * len(names)
        self.assertEqual(result.returncode, 0 if all(s == "PASS" for s in statuses) else 1, result.stderr)
        self.assertEqual((logs / "HEAD").read_text().strip(), self.git("rev-parse", "HEAD"))
        rows = [line.split("\t") for line in (logs / "gates.tsv").read_text().splitlines()]
        self.assertEqual(len(rows), len(names))
        self.assertEqual({p.name for p in logs.iterdir()}, {"HEAD", "gates.tsv"} | ({"core"} if "build-touched" in names else set()) | {str(i)+".log" for i in range(1,len(names)+1)})
        for i, (row, name, status) in enumerate(zip(rows, names, statuses), 1):
            self.assertEqual(len(row), 5)
            self.assertEqual(row[:2], [status, name])
            self.assertTrue(row[2].isdigit())
            self.assertEqual(row[3], str(logs / (str(i)+".log")))
            self.assertTrue(row[4])
            self.assertTrue((logs / (str(i)+".log")).is_file())
        self.assertEqual(result.stdout.splitlines(), [f"{row[0]} {row[1]} {row[2]}s {row[3]}" for row in rows])
        self.assertEqual(result.stderr, "")
        self.record("receipts", {"rows": rows, "calls": self.calls_read(),
                                  "logs": {str(i) + ".log": (logs / (str(i) + ".log")).read_text()
                                           for i in range(1, len(names) + 1)}})
        return rows

    def touched(self, expected):
        result = self.run_gate("touched")
        self.inspect(result, ["build-touched"])
        expected = sorted(expected)
        self.assertEqual((self.logs / "1.log").read_text(), "targets: " + (" ".join(expected) if expected else "none") + "\n")
        self.assertEqual(self.calls_read(), ["lake build " + " ".join(expected)] if expected else [])

    def test_usage(self):
        for args in [(), ("per-file",), ("unknown",), ("touched", "extra")]:
            r = self.run_gate(*args)
            self.assertEqual(r.returncode, 2)
            self.assertIn("usage:", r.stderr)
        self.assertFalse(self.logs.exists())
        self.assertEqual(self.calls_read(), [])

    def test_per_file_relative_paths(self):
        spaced = self.root / "repo with spaces"
        self.repo.rename(spaced)
        self.repo = spaced
        r = self.run_gate("per-file", "A.lean", "B.lean", cwd=self.repo / "Solidity")
        self.inspect(r, ["lean:Solidity/A.lean", "lean:Solidity/B.lean"])
        self.assertEqual(self.calls_read(), ["lake env lean --tstack=131072 Solidity/A.lean", "lake env lean --tstack=131072 Solidity/B.lean"])
        self.assertEqual([(self.logs / (str(i)+".log")).read_text() for i in (1,2)], ["", ""])

    def test_relative_logs(self):
        r = self.run_gate("per-file", "A.lean", cwd=self.repo / "Solidity", GATE_LOGS="relative logs")
        logs = self.repo / "Solidity/relative logs"
        self.inspect(r, ["lean:Solidity/A.lean"], logs=logs)
        self.assertEqual(self.calls_read(), ["lake env lean --tstack=131072 Solidity/A.lean"])

    def test_head_stamp(self):
        self.git("commit", "-qm", "next", "--allow-empty")
        r = self.run_gate("per-file", "Solidity/A.lean")
        self.inspect(r, ["lean:Solidity/A.lean"])
        self.assertNotEqual((self.logs / "HEAD").read_text().strip(), self.base)
        self.assertEqual(self.calls_read(), ["lake env lean --tstack=131072 Solidity/A.lean"])

    def test_changed_module(self):
        self.write("Solidity/Z.lean", "def z := 2\n")
        self.touched(["Solidity.Z"])

    def test_reverse_import_closure(self):
        self.write("Solidity/A.lean", "def a := 2\n")
        self.touched(["Solidity.A", "Solidity.B", "Solidity.C"])

    def test_deleted_module_importers(self):
        (self.repo / "Solidity/A.lean").unlink()
        self.touched(["Solidity.B", "Solidity.C"])

    def test_renamed_module_importers(self):
        self.git("mv", "Solidity/A.lean", "Solidity/D.lean")
        self.touched(["Solidity.B", "Solidity.C", "Solidity.D"])

    def test_diverged_base_merge_base(self):
        self.git("checkout", "-qb", "other", self.base)
        self.write("Solidity/Z.lean", "def z := 3\n")
        self.git("commit", "-qam", "other")
        other = self.git("rev-parse", "HEAD")
        self.git("checkout", "-q", self.branch)
        self.write("Solidity/C.lean", "import Solidity.B\ndef c := 1\n")
        self.git("commit", "-qam", "current")
        self.assertEqual(self.git("merge-base", other, "HEAD"), self.base)
        self.env["GATE_BASE"] = other
        self.touched(["Solidity.C"])

    def test_root_module(self):
        self.write("Solidity.lean", "import Solidity.C\n-- root changed\n")
        self.touched(["Solidity"])

    def test_untracked_module(self):
        self.write("Solidity/New.lean", "import Solidity.Z\n")
        self.touched(["Solidity.New"])

    def test_scratch_excluded(self):
        self.write("Solidity/Scratch/Test.lean", "import Solidity.A\n")
        self.touched([])

    def test_failure_exit(self):
        r = self.run_gate("per-file", "Solidity/A.lean", "Solidity/B.lean", FAIL_TOOL="lake")
        self.inspect(r, ["lean:Solidity/A.lean", "lean:Solidity/B.lean"], ["FAIL", "FAIL"])
        self.assertEqual(self.calls_read(), ["lake env lean --tstack=131072 Solidity/A.lean", "lake env lean --tstack=131072 Solidity/B.lean"])

    def audit(self, command, code, fragments, **updates):
        result = subprocess.run(command, cwd=self.repo, env=dict(self.env, **updates),
                                capture_output=True, text=True, timeout=30)
        self.record("audit", {"command": command, "exit": result.returncode,
                              "stdout": result.stdout, "stderr": result.stderr})
        self.assertEqual(result.returncode, code, result.stdout + result.stderr)
        text = result.stdout + result.stderr
        for fragment in fragments:
            self.assertIn(fragment, text)
        for infrastructure in ("ENOENT", "ERR_MODULE_NOT_FOUND", "Traceback", "TypeError"):
            self.assertNotIn(infrastructure, text)
        return result

    def all_gates(self, mode):
        source = TOOL.parents[2]
        # Copy actual wrappers and their import closure, not unrelated tools.
        needed = ["check-trust.sh", "check-trust.mjs", "check-orphans.mjs",
                  "check-layers.mjs", "import-fanout.mjs", "check-doc-paths.sh",
                  "check-axiom-pins.mjs", "check-automatic.mjs",
                  "check-testsuite.sh", "check-corpus.sh", "check-solkey.sh",
                  "solkey-port.mjs", "coord-tools/register.sh"]
        copied = set()
        while needed:
            name = needed.pop()
            if name in copied:
                continue
            copied.add(name)
            src = source / "scripts" / name
            dst = self.repo / "scripts" / name
            dst.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(src, dst)
            if src.suffix == ".mjs":
                for relative in re.findall(r"from [\"'](\.[^\"']+)[\"']", src.read_text()):
                    needed.append(str((Path(name).parent / relative)))
        shutil.copy2(source / "run-lean.sh", self.repo / "run-lean.sh")
        real_node = shutil.which("node")
        self.assertIsNotNone(real_node, "real Node is a fixture prerequisite")
        for name, executable in (("bash", "/bin/bash"), ("node", real_node)):
            wrapper = self.bin / name
            wrapper.write_text("#!/bin/sh\nprintf '%s\\n' \"" + name + " $*\" >> \"$CALLS\"\nexec \"" + executable + "\" \"$@\"\n")
            wrapper.chmod(0o755)
        self.write("lakefile.toml", 'name = "fixture"\ndefaultTargets = ["Solidity"]\n[[lean_lib]]\nname = "Solidity"\n[[lean_lib]]\nname = "SolidityCorpus"\n[[lean_lib]]\nname = "SuiteRoot"\n[[lean_lib]]\nname = "SolidityExamples"\n')
        self.write("Solidity/Examples/Fixture.lean", "import Solidity.A\n")
        self.write("Solidity/Semantics.lean", "def semanticFixture := 1\n")
        self.write("Solidity/Syntax/Elab.lean", "def elaboratorFixture := 1\n")
        self.write("tests/trust-inventory.json", "[]\n")
        self.write("Solidity/Pin.lean", "/-- info: 'Fixture.pin' does not depend on any axioms -/\n#guard_msgs in #print axioms Fixture.pin\n")
        inventory = {"Solidity/Pin.lean:Fixture.pin": []}
        self.write("scripts/g07-axiom-pins.json", json.dumps(inventory))
        report = "/--\ninfo: 1 functions: 1 derived, 0 pending, 0 other\npending:\n\n-/\n#guard_msgs in\n#solkey_obligations Solkey.TestSuite\n"
        self.write("Solidity/TestSuite/Report.lean", report)
        derived = "theorem Solkey.TestSuite.example.proved (x : Nat) : True := by\n  sol_prove\n"
        self.write("Solidity/TestSuite/Derived1.lean", derived)
        self.write("Solidity/Solkey/TestSuite.lean", "/--\ninfo: \n-/\n#guard_msgs in\n#eval IO.println (Solidity.Frontend.ImportRow.summary Solkey.TestSuite.report)\n")
        self.write("SuiteRoot.lean", "import Solidity.TestSuite.Report\nimport Solidity.TestSuite.Derived1\nimport Solidity.Solkey.TestSuite\nimport Solidity.Corpus.Imported\n")
        self.write("FixtureDoc.md", "See `Solidity/A.lean`.\n")
        contracts = ["SolcExpressions", "SolcStructs", "SolcArrays", "SolcMemory", "SolcMappings", "SolcControlFlow"]
        self.write("Solidity/Syntax/Contract.lean", "\n".join("def " + name + " : Contract := contract!{}" for name in contracts) + "\n")
        self.write("Solidity/Corpus/Basic.lean", "def basicFixture := 1\n")
        self.write("Solidity/Corpus/Imported.lean", "def importedFixture := 1\n")
        solkey = self.root / "solkey"
        solkey.mkdir()
        port = (source / "scripts/solkey-port.mjs").read_text()
        for directory in re.findall(r'dir: "([^"\n]+)"', port):
            (solkey / directory).mkdir(parents=True, exist_ok=True)
        (solkey / "solc").mkdir(exist_ok=True)
        for name in contracts:
            (solkey / "solc" / (name + ".sol")).write_text("contract " + name + " {}\n")
        solidity = "contract TestSuite { function example(uint256 x) public {} }\n"
        (solkey / "TestSuite.sol").write_text(solidity)
        ast = {"sourceSha256": hashlib.sha256(solidity.encode()).hexdigest(), "ast": {"nodes": [{"nodeType": "ContractDefinition", "name": "TestSuite", "nodes": [{"nodeType": "FunctionDefinition", "name": "example", "kind": "function", "visibility": "public", "parameters": {"parameters": [{"name": "x", "typeDescriptions": {"typeString": "uint256"}}]}}]}]}}
        self.write("tests/solc/TestSuite.ast.json", json.dumps(ast))
        subprocess.run(["git", "init", "-q", str(solkey)], env=self.env, check=True)
        subprocess.run(["git", "-C", str(solkey), "add", "."], env=self.env, check=True)
        subprocess.run(["git", "-C", str(solkey), "commit", "-qm", "populated input"], env=self.env, check=True)
        self.env["SOLKEY_EXAMPLES"] = str(solkey)
        generated = self.root / "generated"
        self.audit(["node", "scripts/solkey-port.mjs", "--out", str(generated)], 0, ["1 obligations:"])
        for name in ("Solidity/Corpus", "tests/solkey", "docs"):
            shutil.copytree(generated / name, self.repo / name, dirs_exist_ok=True)
        shutil.copy2(generated / "SolidityCorpus.lean", self.repo / "SolidityCorpus.lean")
        self.audit(["bash", "scripts/coord-tools/register.sh"], 0, [])
        self.git("add", "Solidity", "Solidity.lean", "SolidityExamples.lean", "SolidityCorpus.lean",
                 "SuiteRoot.lean", "lakefile.toml", "FixtureDoc.md", "tests/solc", "tests/solkey", "tests/trust-inventory.json")
        # Real positive audits: populated proof pin, source catalogue and corpus.
        self.audit(["bash", "scripts/check-trust.sh"], 0, ["0 findings"])
        self.audit(["node", "scripts/check-orphans.mjs"], 0, ["0 orphaned, 0 not allowed"])
        self.audit(["node", "scripts/check-layers.mjs"], 0, ["0 reach the elaborator"])
        self.audit(["bash", "scripts/coord-tools/register.sh", "--check"], 0, [])
        self.audit(["bash", "scripts/check-doc-paths.sh"], 0, ["OK: every backticked"])
        self.audit(["node", "scripts/check-axiom-pins.mjs"], 0, ["1 pinned theorems", "0 errors, 0 unrecorded changes"])
        self.audit(["node", "scripts/check-automatic.mjs", "--strict"], 0, ["1 automatic", "0 manual", "0 pending", "classification only"])
        self.audit(["bash", "scripts/check-testsuite.sh"], 0, ["parity: 1 testSuiteFunctions = 1 derived", "check-testsuite: ok"])
        self.audit(["bash", "scripts/check-corpus.sh"], 0, ["check-corpus: ok"])
        self.audit(["bash", "run-lean.sh"], 23, ["fixture backend refused: lake"], FAIL_TOOL="lake")
        # Layer negative reaches the actual path-finding audit, then restore it.
        self.write("Solidity/Semantics.lean", "import Solidity.Syntax.Elab\n")
        self.audit(["node", "scripts/check-layers.mjs"], 1, ["LAYER  Semantics → Syntax.Elab", "1 reach the elaborator"])
        self.write("Solidity/Semantics.lean", "def semanticFixture := 1\n")
        # Other specific negatives remain installed for the gate-level run.
        self.write("Solidity/Loose.lean", "theorem rejectedFixture : True := by sorry\n")
        self.write("FixtureDoc.md", "See `Solidity/MissingFixture.lean`.\n")
        self.write("scripts/g07-axiom-pins.json", json.dumps({"Solidity/Pin.lean:Fixture.pin": ["propext"]}))
        self.write("Solidity/TestSuite/Report.lean", report + "unsound fixtureMarker\n")
        self.write("Solidity/TestSuite/Derived1.lean", derived.replace("sol_prove", "rfl"))
        self.git("add", "Solidity", "Solidity.lean", "SolidityExamples.lean", "SolidityCorpus.lean",
                 "SuiteRoot.lean", "lakefile.toml", "FixtureDoc.md", "tests/solc", "tests/solkey", "tests/trust-inventory.json")
        self.git("commit", "-qm", "populated audit negatives")
        self.base = self.git("rev-parse", "HEAD")
        self.env["GATE_BASE"] = self.base
        self.calls.unlink()
        names = ["build-touched", "library" if mode == "checkpoint" else "run-lean", "trust", "orphans", "layers", "roots", "doc-paths", "axiom-pins"]
        if mode == "full":
            names += ["testsuite", "corpus", "automatic-strict"]
        statuses = ["PASS", "FAIL", "FAIL", "FAIL", "PASS", "FAIL", "FAIL", "FAIL"]
        if mode == "full":
            statuses += ["FAIL", "FAIL", "FAIL"]
        result = self.run_gate(mode, FAIL_TOOL="lake")
        rows = self.inspect(result, names, statuses)
        wanted = ["build_touched", "lake build Solidity" if mode == "checkpoint" else "bash run-lean.sh", "bash scripts/check-trust.sh", "node scripts/check-orphans.mjs", "node scripts/check-layers.mjs", "bash scripts/coord-tools/register.sh --check", "bash scripts/check-doc-paths.sh", "node scripts/check-axiom-pins.mjs"]
        if mode == "full":
            wanted += ["bash scripts/check-testsuite.sh", "bash scripts/check-corpus.sh", "node scripts/check-automatic.mjs --strict"]
        self.assertEqual([r[4].strip() for r in rows], wanted)
        diagnostics = {"trust": "forbidden sorry", "orphans": "ORPHAN   Solidity.Loose", "layers": "0 reach the elaborator", "roots": "missing import Solidity.Loose", "doc-paths": "MissingFixture.lean", "axiom-pins": "pin Fixture.pin shrank", "testsuite": "Report.lean pins `unsound fixtureMarker`", "corpus": "fixture backend refused: lake", "automatic-strict": "1 manual"}
        for i, name in enumerate(names, 1):
            text = (self.logs / (str(i) + ".log")).read_text()
            if name in diagnostics:
                self.assertIn(diagnostics[name], text)
            for infrastructure in ("ENOENT", "ERR_MODULE_NOT_FOUND", "Traceback", "TypeError"):
                self.assertNotIn(infrastructure, text)
        calls = self.calls_read()
        expected = (["lake build Solidity"] if mode == "checkpoint" else ["bash run-lean.sh", "node scripts/check-layers.mjs", "bash scripts/coord-tools/register.sh --check"])
        expected += ["bash scripts/check-trust.sh", "node scripts/check-trust.mjs", "node scripts/check-orphans.mjs", "node scripts/check-layers.mjs", "bash scripts/coord-tools/register.sh --check", "bash scripts/check-doc-paths.sh", "node scripts/check-axiom-pins.mjs"]
        if mode == "full":
            self.assertEqual(len(calls), len(expected) + 6)
            self.assertEqual(calls[:len(expected)], expected)
            tail = calls[len(expected):]
            self.assertEqual(tail[0], "bash scripts/check-testsuite.sh")
            port_call = re.fullmatch(r"node scripts/solkey-port\.mjs --solkey " + re.escape(str(solkey)) + r" --out (/[^ ]+)", tail[1])
            self.assertIsNotNone(port_call)
            self.assertEqual(tail[2], "node --input-type=module - " + str(solkey) + " " + port_call.group(1) + " 0")
            self.assertEqual(tail[3:], ["bash scripts/check-corpus.sh", "lake build Solidity.Corpus.Basic", "node scripts/check-automatic.mjs --strict"])
        else:
            self.assertEqual(calls, expected)

    def test_checkpoint_all_gates(self):
        self.all_gates("checkpoint")

    def test_full_extra_gates(self):
        self.all_gates("full")
