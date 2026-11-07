"""Guard H109 preparation against source, target and special-file substitution.

Synthetic Git fixtures test metadata only; no Lean, Docker or benchmark runs.
"""

import os
from pathlib import Path
import runpy
import subprocess
import tempfile
import unittest


M = runpy.run_path(str(Path(__file__).with_name("prepare-plan.py")))


class Preparation(unittest.TestCase):
    def test_regular_file_safety(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "plain").write_bytes(b"data")
            self.assertEqual(M["regular_bytes"](root, "plain", 4)[0], b"data")
            os.symlink("plain", root / "link")
            os.mkfifo(root / "pipe")
            (root / "dir").mkdir()
            os.symlink("dir", root / "ancestor")
            for name, size in [("link", 4), ("pipe", 0), ("dir", 0),
                               ("ancestor/missing", 0), ("../escape", 0), ("plain", 5)]:
                with self.subTest(name=name), self.assertRaises((ValueError, OSError)):
                    M["regular_bytes"](root, name, size)

    def test_source_plan_and_refusals(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            def git(*args):
                return subprocess.check_output(["git", "-C", str(root), *args], stderr=subprocess.DEVNULL)
            git("init", "-q")
            git("config", "user.name", "H109 fixture")
            git("config", "user.email", "fixture@invalid")
            (root / "lakefile.toml").write_text('defaultTargets=["Solidity"]\n[[lean_lib]]\nname="SoliditySlowExamples"\n')
            (root / "SoliditySlowExamples.lean").write_text("".join("import " + m + "\n" for m in M["SLOW"]))
            for module in M["SLOW"]:
                path = root / (module.replace(".", "/") + ".lean")
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text("-- metadata fixture; never elaborated\n")
            def commit():
                git("add", ".")
                git("commit", "-qm", "fixture")
                return git("rev-parse", "HEAD").decode().strip()
            head = commit()
            result = M["prepare"](root, head)
            self.assertEqual(len(result["slowModules"]), 14)
            self.assertEqual(result["status"], "prepared-not-executed")
            self.assertEqual(result["measurementDeadlineSeconds"], 300)
            self.assertEqual(result["derived17ReplayDeadlineSeconds"], 300)
            ci = M["prepare"](root, head, "ci")
            self.assertEqual(ci["measurementDeadlineSeconds"], 300)
            self.assertEqual(ci["derived17ReplayDeadlineSeconds"], 600)
            with self.assertRaisesRegex(ValueError, "Unsupported execution context"):
                M["prepare"](root, head, "checkpoint")
            with self.assertRaisesRegex(ValueError, "Unexpected source head"):
                M["prepare"](root, "0" * 40)
            (root / "lakefile.toml").write_text('defaultTargets=["SoliditySlowExamples"]\n[[lean_lib]]\nname="SoliditySlowExamples"\n')
            with self.assertRaisesRegex(ValueError, "Tracked source changes"):
                M["prepare"](root, head)
            head = commit()
            with self.assertRaisesRegex(ValueError, "must remain non-default"):
                M["prepare"](root, head)
            (root / "lakefile.toml").write_text('defaultTargets=["Solidity"]\n[[lean_lib]]\nname="SoliditySlowExamples"\n')
            (root / "SoliditySlowExamples.lean").write_text("import Solidity.Examples.DecisionGaps\n")
            head = commit()
            with self.assertRaisesRegex(ValueError, "target inventory changed"):
                M["prepare"](root, head)
            (root / "SoliditySlowExamples.lean").write_text("".join("import " + m + "\n" for m in M["SLOW"]))
            row = root / "Solidity/Examples/Tactics/OpenLoops/RowsNine.lean"
            row.parent.mkdir(parents=True)
            row.write_text("-- pending source membership fixture, never elaborated\n")
            head = commit()
            with self.assertRaisesRegex(ValueError, "RowsNine requires reviewed central"):
                M["prepare"](root, head)


if __name__ == "__main__":
    unittest.main()
