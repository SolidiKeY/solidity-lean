"""Guard regression: H109 slow examples leak into regular source roots."""
import os
import pathlib
import re
import subprocess
import tempfile
import tomllib
import unittest

ROOT = pathlib.Path(__file__).resolve().parents[3]


def imports(path):
    result = []
    for line in path.read_text().splitlines():
        match = re.match(r"^\s*(?:(?:public|private|meta)\s+)*import(?:\s+all)?\s+(.+)$", line)
        if match:
            result.extend(match.group(1).split("--", 1)[0].split())
    return result


def reachable_slow(roots, slow, load):
    seen, stack, found = set(), list(roots), set()
    while stack:
        module = stack.pop()
        if module in seen:
            continue
        seen.add(module)
        if module in slow:
            found.add(module)
        stack.extend(load(module))
    return found


def default_roots(config):
    entries = {entry["name"]: (kind, entry) for kind in ("lean_lib", "lean_exe")
               for entry in config.get(kind, [])}
    result = []
    for target in config["defaultTargets"]:
        kind, entry = entries[target]
        if (entry.get("srcDir", ".") != "." or (kind == "lean_lib" and "globs" in entry)
                or entry.get("needs") or entry.get("extraDepTargets")):
            raise ValueError("unsupported default target source mapping or dependency")
        roots = entry.get("roots", [entry["name"]]) if kind == "lean_lib" else [entry.get("root", entry["name"])]
        if not isinstance(roots, list) or not roots or any(not isinstance(x, str) or not x for x in roots):
            raise ValueError("invalid target roots")
        result.extend(roots)
    return result


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
                         "scripts/check-private-paths.sh", "scripts/check-evidence-files.sh",
                         "scripts/coord-tools/register.sh", "scripts/coord-tools/fragments.sh",
                         "scripts/ci/checks-fast.sh"):
                file = root / name
                file.parent.mkdir(parents=True, exist_ok=True)
                file.write_text("#!/bin/bash\nexit 0\n")
            p16 = root / "scripts/h62/item1/p16-generator/check.py"
            p16.parent.mkdir(parents=True)
            p16.write_text("raise SystemExit(0)\n")
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

    def test_default_root_config_and_indented_imports(self):
        config = {"defaultTargets": ["App"], "lean_lib": [{"name": "App", "roots": ["A", "B"]}]}
        self.assertEqual(["A", "B"], default_roots(config))
        config["lean_lib"][0]["globs"] = ["A.+"]
        with self.assertRaisesRegex(ValueError, "unsupported"):
            default_roots(config)
        del config["lean_lib"][0]["globs"]
        config["lean_lib"][0]["needs"] = ["SoliditySlowExamples"]
        with self.assertRaisesRegex(ValueError, "unsupported"):
            default_roots(config)
        with tempfile.TemporaryDirectory() as tmp:
            source = pathlib.Path(tmp) / "imports.lean"
            source.write_text("  import A B -- comment\npublic import C\nmeta import all D\n")
            self.assertEqual(["A", "B", "C", "D"], imports(source))

    def test_default_root_traversal_detects_indirect_slow_import(self):
        graph = {"Application": ["Middle"], "Middle": ["Solidity.Examples.Tactics.OpenLoops"]}
        slow = {"Solidity.Examples.Tactics.OpenLoops"}
        self.assertEqual(slow, reachable_slow(["Application"], slow, lambda name: graph.get(name, [])))

    def test_slow_partition_and_reverse_imports(self):
        slow = set(imports(ROOT / "SoliditySlowExamples.lean"))
        regular = set(imports(ROOT / "SolidityExamples.lean"))
        original_slow = {
            "Solidity.Examples.DecisionAPF",
            "Solidity.Examples.DecisionBlocks",
            "Solidity.Examples.DecisionGapCore",
            "Solidity.Examples.DecisionGapHashes",
            "Solidity.Examples.DecisionGapKInt",
            "Solidity.Examples.DecisionGaps",
            "Solidity.Examples.DecisionLedger",
            "Solidity.Examples.DecisionOperators",
            "Solidity.Examples.DecisionRefutations",
            "Solidity.Examples.DecisionResidue",
            "Solidity.Examples.DecisionStorageArrays",
            "Solidity.Examples.DecisionThreeKindCoverage",
            "Solidity.Examples.Tactics.OpenLoops",
            "Solidity.Examples.Tactics.OpenLoops.RowsNine",
            "Solidity.Examples.Tactics.RevertData",
        }
        rowsnine_children = {
            "Solidity.Examples.Tactics.OpenLoops.RowsNine.Checkpoint",
            "Solidity.Examples.Tactics.OpenLoops.RowsNine.Finish",
            "Solidity.Examples.Tactics.OpenLoops.RowsNine.Stage1",
            "Solidity.Examples.Tactics.OpenLoops.RowsNine.Stage2",
            "Solidity.Examples.Tactics.OpenLoops.RowsNine.Stage3",
        }
        self.assertEqual(15, len(slow - rowsnine_children))
        self.assertEqual(original_slow | rowsnine_children, slow)
        self.assertFalse(slow & regular)
        with (ROOT / "lakefile.toml").open("rb") as file:
            roots = default_roots(tomllib.load(file))
        self.assertIn("SolidityLean", roots)
        for module in roots:
            self.assertTrue((ROOT / (module.replace(".", "/") + ".lean")).is_file(), module)
        def load(module):
            relative = module.replace(".", "/") + ".lean"
            source = ROOT / relative
            if module == "LeanTeX" or module.startswith("LeanTeX."):
                source = ROOT / "vendor/LeanTeX" / relative
            if source.is_file():
                return imports(source)
            if module == "Solidity" or module.startswith("Solidity.") or module == "LeanTeX" or module.startswith("LeanTeX."):
                raise ValueError("unresolved local module: " + module)
            return []
        self.assertFalse(reachable_slow(roots, slow, load))
        self.assertTrue({"Solidity.Examples.Tactics.OpenLoops", "Solidity.Examples.DecisionGaps",
                         "Solidity.Examples.Tactics.RevertData",
                         "Solidity.Examples.Tactics.OpenLoops.RowsNine"} <= slow)
        for file in (ROOT / "Solidity").rglob("*.lean"):
            module = file.relative_to(ROOT).with_suffix("").as_posix().replace("/", ".")
            if module not in slow:
                self.assertFalse(slow.intersection(imports(file)), str(file))
        self.assertIn("import SoliditySlowExamples", (ROOT / "scripts/AxiomAudit.lean").read_text())
        self.assertIn("SoliditySlowExamples", (ROOT / ".github/workflows/lean.yml").read_text())
        self.assertIn("SoliditySlowExamples", (ROOT / "run-lean.sh").read_text())


if __name__ == "__main__":
    unittest.main()
