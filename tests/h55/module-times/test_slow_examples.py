"""Guard regression: H109 slow examples leak into regular source roots."""
import os
import pathlib
import re
import subprocess
import tempfile
import unittest

ROOT = pathlib.Path(__file__).resolve().parents[3]


def imports(path):
    return [m.group(1) for line in path.read_text().splitlines()
            if (m := re.match(r"^import\s+(\S+)", line))]


class SlowExamples(unittest.TestCase):
    def test_generator_keeps_descendants_and_handles_sparse_tree(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = pathlib.Path(tmp)
            subprocess.run(["git", "init", "-q", str(root)], check=True)
            script = root / "register.sh"
            script.write_bytes((ROOT / "scripts/coord-tools/register.sh").read_bytes())
            subprocess.run(["bash", str(script)], cwd=root, check=True)
            self.assertFalse((root / "SoliditySlowExamples.lean").exists())
            for name in imports(ROOT / "SoliditySlowExamples.lean"):
                source = root / (name.replace(".", "/") + ".lean")
                source.parent.mkdir(parents=True, exist_ok=True)
                source.write_text("-- fixture\n")
            extra = root / "Solidity/Examples/DecisionGaps/Extra.lean"
            extra.parent.mkdir(parents=True, exist_ok=True)
            extra.write_text("-- fixture\n")
            subprocess.run(["bash", str(script)], cwd=root, check=True)
            self.assertIn("Solidity.Examples.DecisionGaps.Extra", imports(root / "SolidityExamples.lean"))
            self.assertNotIn("Solidity.Examples.DecisionGaps.Extra", imports(root / "SoliditySlowExamples.lean"))

    def test_partial_sparse_examples_are_supported(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = pathlib.Path(tmp)
            subprocess.run(["git", "init", "-q", str(root)], check=True)
            subprocess.run(["git", "config", "core.sparseCheckout", "true"], cwd=root, check=True)
            script = root / "register.sh"
            script.write_bytes((ROOT / "scripts/coord-tools/register.sh").read_bytes())
            source = root / "Solidity/Examples/DecisionGaps.lean"
            source.parent.mkdir(parents=True)
            source.write_text("-- fixture\n")
            subprocess.run(["bash", str(script)], cwd=root, check=True)
            self.assertEqual(["Solidity.Examples.DecisionGaps"], imports(root / "SoliditySlowExamples.lean"))

    def test_checkpoint_defers_transitive_slow_module(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = pathlib.Path(tmp)
            subprocess.run(["git", "init", "-q", str(root)], check=True)
            gate = root / "scripts/coord-tools/gate.sh"
            gate.parent.mkdir(parents=True)
            gate.write_bytes((ROOT / "scripts/coord-tools/gate.sh").read_bytes())
            for name in ("scripts/check-trust.sh", "scripts/check-doc-paths.sh",
                         "scripts/coord-tools/register.sh", "scripts/coord-tools/fragments.sh"):
                file = root / name
                file.parent.mkdir(parents=True, exist_ok=True)
                file.write_text("#!/bin/bash\nexit 0\n")
            core = root / "Solidity/Syntax/Core.lean"
            slow = root / "Solidity/Examples/Tactics/OpenLoops.lean"
            core.parent.mkdir(parents=True)
            slow.parent.mkdir(parents=True)
            core.write_text("-- base\n")
            slow.write_text("import Solidity.Syntax.Core\n")
            (root / "SoliditySlowExamples.lean").write_text("import Solidity.Examples.Tactics.OpenLoops\n")
            subprocess.run(["git", "add", "."], cwd=root, check=True)
            subprocess.run(["git", "-c", "user.name=Fixture", "-c", "user.email=f@example.invalid", "commit", "-qm", "base"], cwd=root, check=True)
            core.write_text("-- changed\n")
            fakebin = root / "fakebin"
            fakebin.mkdir()
            calls = root / "lake-calls"
            lake = fakebin / "lake"
            lake.write_text('#!/bin/bash\nprintf "%s\\n" "$*" >> "$H55_LAKE_CALLS"\n')
            lake.chmod(0o755)
            node = fakebin / "node"
            node.write_text("#!/bin/bash\nexit 0\n")
            node.chmod(0o755)
            env = dict(os.environ, PATH=str(fakebin) + os.pathsep + os.environ["PATH"],
                       GATE_BASE="HEAD", GATE_LOGS=str(root / "logs"), H55_LAKE_CALLS=str(calls))
            result = subprocess.run(["bash", str(gate), "checkpoint"], cwd=root, env=env,
                                    text=True, capture_output=True)
            self.assertEqual(0, result.returncode, result.stdout + result.stderr)
            commands = calls.read_text()
            self.assertIn("Solidity.Syntax.Core", commands)
            self.assertNotIn("Solidity.Examples.Tactics.OpenLoops", commands)
            self.assertNotIn("SoliditySlowExamples", commands)
            result = subprocess.run(["bash", str(gate), "per-file", "Solidity/Syntax/Core.lean"],
                                    cwd=root, env=env, text=True, capture_output=True)
            self.assertEqual(0, result.returncode, result.stdout + result.stderr)
            self.assertEqual("lean Solidity/Syntax/Core.lean -- --tstack=131072", calls.read_text().splitlines()[-1])

    def test_slow_partition_and_reverse_imports(self):
        slow = set(imports(ROOT / "SoliditySlowExamples.lean"))
        regular = set(imports(ROOT / "SolidityExamples.lean"))
        self.assertEqual(14, len(slow))
        self.assertFalse(slow & regular)
        self.assertTrue({"Solidity.Examples.Tactics.OpenLoops", "Solidity.Examples.DecisionGaps",
                         "Solidity.Examples.Tactics.RevertData"} <= slow)
        for file in (ROOT / "Solidity").rglob("*.lean"):
            module = file.relative_to(ROOT).with_suffix("").as_posix().replace("/", ".")
            if module not in slow:
                self.assertFalse(slow.intersection(imports(file)), str(file))
        self.assertIn("import SoliditySlowExamples", (ROOT / "scripts/AxiomAudit.lean").read_text())
        self.assertIn("SoliditySlowExamples", (ROOT / ".github/workflows/lean.yml").read_text())
        self.assertIn("SoliditySlowExamples", (ROOT / "run-lean.sh").read_text())


if __name__ == "__main__":
    unittest.main()
