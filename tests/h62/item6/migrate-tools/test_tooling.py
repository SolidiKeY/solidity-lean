#!/usr/bin/env python3
"""Scanner controls and actual subprocess interruption/reaping regression.
No Lean server; fake executable tests resource-tool behavior, not proofs.
"""
import importlib.util, json, os, signal, sys, tempfile, unittest
from pathlib import Path
ROOT = Path(__file__).resolve().parents[4]
sys.dont_write_bytecode = True
sys.path.insert(0, str(ROOT / "scripts/h62/item6/migrate-tools"))
from census import mask, imports, census
spec = importlib.util.spec_from_file_location("serial_build", ROOT / "scripts/h62/item6/migrate-tools/serial-build.py")
runner = importlib.util.module_from_spec(spec); spec.loader.exec_module(runner)

class ToolingTests(unittest.TestCase):
    def test_mask_comments_strings_and_characters(self):
        text = "import Solidity.A\n/- import False /- nested -/ -/\ndef c := '\"'\ndef x := \"import Hidden\"\nimport Solidity.B\n"
        self.assertEqual(imports(text), ["Solidity.A", "Solidity.B"])
        self.assertEqual(mask(text).count("\n"), text.count("\n"))

    def test_continued_strings_preserve_real_line_numbers(self):
        text = 'def s := "before' + "\\" + "\n" + 'after"\ndef x := 0\n'
        self.assertEqual(mask(text).count("\n"), text.count("\n"))
        for path in (ROOT / "Solidity/Tools").glob("*.lean"):
            raw = path.read_text()
            self.assertEqual(mask(raw).count("\n"), raw.count("\n"), str(path))

    def test_same_line_attributes_are_accounted(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp); (root / "Solidity/Tools").mkdir(parents=True)
            (root / "Solidity/Tools/Fixture.lean").write_text("@[command_elab x] def actual := 0\n@[simp] theorem proof : True := by trivial\n")
            rows = census(root)["modules"][0]["declaration_candidates"]
            self.assertEqual([r["kind"] for r in rows], ["def", "theorem"])
            self.assertEqual([r["line"] for r in rows], [1, 2])

    def test_current_scope_exact_files_and_missed_commands(self):
        data = census(ROOT)
        self.assertEqual(data["module_count"], 30)
        heads = "\n".join(d["source_head"] for r in data["modules"] for d in r["declaration_candidates"])
        for name in ["elabTaclet", "elabRun", "elabDeploy", "elabDiffTest"]:
            self.assertIn(name, heads)

    def test_prebuilt_reuse_cannot_be_a_clean_or_multitarget_build(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            for fixtures in [(), (Path("A.lean"), Path("B.lean"))]:
                with self.assertRaises(SystemExit):
                    runner.build(root, root, root / "output", fixtures, root / "prebuilt")
            self.assertFalse((root / "output").exists())

    def test_monitor_interrupt_reaps_owned_process(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp); (root / "Solidity").mkdir(); (root / "Solidity/KeySort.lean").write_text("")
            tc = root / "toolchain"; (tc / "bin").mkdir(parents=True)
            for name in ["lean", "lake"]:
                p = tc / "bin" / name
                p.write_text("#!/usr/bin/env python3\nimport sys,time\nif '--version' in sys.argv: print('fake test runtime')\nelse: time.sleep(60)\n")
                p.chmod(0o755)
            original = runner.time.sleep
            def interrupt(_):
                runner.time.sleep = original
                raise KeyboardInterrupt()
            runner.time.sleep = interrupt
            try: code = runner.build(root, tc, root / "output")
            finally: runner.time.sleep = original
            result = json.loads((root / "output/result.json").read_text())
            self.assertEqual(code, 1)
            self.assertEqual(result["status"], "failed")
            self.assertEqual(result["modules"][0]["blocker"], "MONITOR_INTERRUPTED:KeyboardInterrupt")
            self.assertLess(result["modules"][0]["exit"], 0)

if __name__ == "__main__": unittest.main()
