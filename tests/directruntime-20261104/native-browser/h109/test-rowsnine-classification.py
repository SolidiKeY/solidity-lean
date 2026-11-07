"""Guard RowsNine slow-library membership without dropping CI/full validation.

Only synthetic source trees and static hooks are checked; no Lean is run.
"""

import ast
import json
from pathlib import Path
import subprocess
import tempfile
import tomllib
import unittest


ROOT = Path(__file__).resolve().parents[4]
AREA = Path(__file__).parent
CHILD = "Solidity.Examples.Tactics.OpenLoops.RowsNine"
PARENT = "Solidity.Examples.Tactics.OpenLoops"


def imports(path):
    return {line[7:] for line in path.read_text().splitlines() if line.startswith("import ")}


class Classification(unittest.TestCase):
    def test_current_leak_and_exact_central_proposal(self):
        source = (ROOT / "scripts/coord-tools/register.sh").read_text()
        old = next(line for line in source.splitlines() if line.startswith("SLOW_EXAMPLES = "))
        baseline = ast.literal_eval(old.split("=", 1)[1])
        proposal = json.loads((AREA / "rowsnine-registration.json").read_text())
        self.assertEqual(set(proposal["proposedSlowMembers"]), set(baseline) | {CHILD})
        self.assertEqual(len(proposal["proposedSlowMembers"]), 15)
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            subprocess.run(["git", "init", "-q", str(root)], check=True)
            extra = "Solidity.Examples.DecisionGaps.Extra"
            regular = "Solidity.Examples.Regular"
            for module in baseline + [CHILD, extra, regular]:
                path = root / (module.replace(".", "/") + ".lean")
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text("-- source-tree metadata fixture; never elaborated\n")
            script = root / "register.sh"
            script.write_text(source)
            subprocess.run(["bash", str(script)], cwd=root, check=True)
            self.assertIn(CHILD, imports(root / "SolidityExamples.lean"))
            self.assertNotIn(CHILD, imports(root / "SoliditySlowExamples.lean"))
            self.assertNotIn(PARENT, imports(root / "SolidityExamples.lean"))
            # Apply only the proposed exact-list addition, in this fixture.
            new = "SLOW_EXAMPLES = " + repr(baseline + [CHILD])
            script.write_text(source.replace(old, new, 1))
            subprocess.run(["bash", str(script)], cwd=root, check=True)
            slow = imports(root / "SoliditySlowExamples.lean")
            default = imports(root / "SolidityExamples.lean")
            self.assertEqual(slow, set(baseline) | {CHILD})
            self.assertTrue({CHILD, PARENT}.isdisjoint(default))
            self.assertTrue({extra, regular}.issubset(default))
            self.assertEqual({CHILD, PARENT, regular} - slow, {regular})

    def test_retained_validation_hooks(self):
        self.assertNotIn("SoliditySlowExamples", tomllib.loads((ROOT / "lakefile.toml").read_text())["defaultTargets"])
        for name in ["run-lean.sh", ".github/workflows/lean.yml", ".github/workflows/pages.yml",
                     "scripts/AxiomAudit.lean"]:
            self.assertIn("SoliditySlowExamples", (ROOT / name).read_text(), name)
        gate = (ROOT / "scripts/coord-tools/gate.sh").read_text()
        self.assertIn('run_gate run-lean bash run-lean.sh', gate)
        self.assertIn('out.difference_update(slow)', gate)


if __name__ == "__main__":
    unittest.main()
