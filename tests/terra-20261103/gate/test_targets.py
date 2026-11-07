"""Real Git/production gate, isolated Lake backend; no Lean or elan required."""
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest

TOOL = (Path(__file__).resolve().parents[3] / "scripts/coord-tools/gate.sh").resolve()

class Targets(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix="gate fixture ")
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.repo = self.root / "repo with spaces"
        self.repo.mkdir()
        self.bin = self.root / "mock bin"
        self.bin.mkdir()
        self.calls = self.root / "calls.jsonl"
        self.elan = self.root / "elan-used"
        self.home = self.root / "private home"
        self.home.mkdir()
        self.env = os.environ.copy()
        for key in list(self.env):
            if key.startswith("GIT_"):
                self.env.pop(key)
        self.env.update(GIT_AUTHOR_NAME="Gate Fixture", GIT_AUTHOR_EMAIL="fixture@example.invalid",
                        GIT_COMMITTER_NAME="Gate Fixture", GIT_COMMITTER_EMAIL="fixture@example.invalid",
                        GIT_CONFIG_GLOBAL=os.devnull, GIT_CONFIG_NOSYSTEM="1",
                        HOME=str(self.home), ELAN_HOME=str(self.home / ".elan"),
                        XDG_CACHE_HOME=str(self.home / ".cache"),
                        XDG_CONFIG_HOME=str(self.home / ".config"),
                        LAKE_CACHE_DIR="", LAKE_ARTIFACT_CACHE="false")
        self.env.pop("BASH_ENV", None)
        self.env.pop("ENV", None)
        self.env.pop("GATE_EXAMPLES", None)
        self.git("init", "-q")
        self.put("Solidity/Leaf.lean", "def leaf : Nat := 1\n")
        self.put("Solidity/Importer.lean", "import Solidity.Leaf\n")
        self.put("Solidity/Consumer.lean", "import Solidity.Importer\n")
        self.put("Solidity/Unrelated.lean", "def unrelated : Nat := 3\n")
        self.put("Solidity/Scratch/Probe.lean", "import Solidity.Leaf\n")
        self.put("Solidity/Syntax/Tiny.lean", "def tiny : Nat := 0\n")
        self.put("Solidity/Examples/Demo.lean", "import Solidity.Leaf\nimport Solidity.Syntax.Tiny\n")
        self.put("Solidity/Corpus/Demo.lean", "import Solidity.Leaf\n")
        self.git("add", ".")
        self.git("commit", "-qm", "populated base")
        self.base = self.git("rev-parse", "HEAD").strip()
        # A real installed elan, missing elan, and host toolchain configuration
        # are irrelevant: both lake and elan are private executable backends.
        for name in ("python3", "git", "bash", "date", "rm", "realpath", "mkdir"):
            executable = sys.executable if name == "python3" else shutil.which(name)
            self.assertIsNotNone(executable)
            (self.bin / name).symlink_to(executable)
        self.script("lake", "import json, os, sys\nwith open(os.environ['CALLS'], 'a') as f: f.write(json.dumps({'args': sys.argv[1:], 'threads': os.environ.get('LEAN_NUM_THREADS')})+'\\n')\nsys.exit(int(os.environ.get('MOCK_EXIT','0')))\n")
        self.script("elan", "import os\nopen(os.environ['ELAN_USED'], 'w').write('unexpected')\nraise SystemExit(97)\n")
        self.env.update(PATH=str(self.bin), CALLS=str(self.calls), ELAN_USED=str(self.elan),
                        GATE_BASE=self.base, GATE_LOGS=str(self.root / "gate logs"))

    def put(self, name, text):
        path = self.repo / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text)

    def script(self, name, body):
        path = self.bin / name
        path.write_text("#!" + sys.executable + "\n" + body)
        path.chmod(0o700)

    def git(self, *args):
        return subprocess.check_output(["git", "-C", str(self.repo), *args], env=self.env, text=True)

    def gate(self, expected, exit_code=0):
        result = subprocess.run([str(self.bin / "bash"), str(TOOL), "touched"], cwd=self.repo,
                                env=self.env, capture_output=True, text=True, timeout=15)
        self.assertEqual(result.returncode, exit_code, result.stdout + result.stderr)
        calls = [json.loads(x) for x in self.calls.read_text().splitlines()] if self.calls.exists() else []
        wanted = [{"args": ["build", *sorted(expected)], "threads": "1"}] if expected else []
        self.assertEqual(calls, wanted)
        self.assertFalse(self.elan.exists(), "fixture touched host/toolchain elan")
        self.assertEqual(list(self.home.iterdir()), [], "unexpected toolchain/cache/config write")
        log = Path(self.env["GATE_LOGS"])
        self.assertEqual((log / "HEAD").read_text().strip(), self.base)
        rows = (log / "gates.tsv").read_text().splitlines()
        self.assertEqual(len(rows), 1)
        fields = rows[0].split("\t")
        self.assertEqual(len(fields), 5)
        status = "PASS" if exit_code == 0 else "FAIL"
        self.assertEqual(fields[:2], [status, "build-touched"])
        self.assertTrue(fields[2].isdigit())
        self.assertEqual(fields[3:], [str(log / "1.log"), "build_touched "])
        self.assertEqual(result.stdout, f"{status} build-touched {fields[2]}s {log / '1.log'}\n")
        self.assertEqual(result.stderr, "")
        targets = " ".join(sorted(expected)) if expected else "none"
        self.assertIn("targets: " + targets + "\n", (log / "1.log").read_text())

    def test_tracked_scratch_only(self):
        self.put("Solidity/Scratch/Probe.lean", "-- changed scratch\n")
        self.gate([])

    def test_untracked_scratch_only(self):
        self.put("Solidity/Scratch/New.lean", "-- untracked scratch\n")
        self.gate([])

    def test_mixed_and_transitive_importers(self):
        self.put("Solidity/Leaf.lean", "def leaf : Nat := 2\n")
        self.put("Solidity/Scratch/Probe.lean", "-- changed scratch\n")
        self.gate(["Solidity.Leaf", "Solidity.Importer", "Solidity.Consumer"])

    def test_deleted_production_keeps_importers(self):
        (self.repo / "Solidity/Leaf.lean").unlink()
        self.gate(["Solidity.Importer", "Solidity.Consumer"])

    def test_untracked_production_is_not_ignored(self):
        self.put("Solidity/Fresh.lean", "def fresh : Nat := 5\n")
        self.gate(["Solidity.Fresh"])

    def test_tracked_ignored_production_is_not_ignored(self):
        self.put(".gitignore", "Solidity/Leaf.lean\n")
        self.put("Solidity/Leaf.lean", "def leaf : Nat := 2\n")
        self.gate(["Solidity.Leaf", "Solidity.Importer", "Solidity.Consumer"])

    def test_core_change_retains_example_policy(self):
        self.put("Solidity/Syntax/Tiny.lean", "def tiny : Nat := 1\n")
        self.gate(["Solidity.Syntax.Tiny", "Solidity.Examples.Demo"])

    def test_backend_failure_is_not_hidden(self):
        self.put("Solidity/Leaf.lean", "def leaf : Nat := 2\n")
        self.env["MOCK_EXIT"] = "23"
        self.gate(["Solidity.Leaf", "Solidity.Importer", "Solidity.Consumer"], 1)

if __name__ == "__main__":
    unittest.main(verbosity=2)
