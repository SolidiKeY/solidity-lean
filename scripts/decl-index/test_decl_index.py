#!/usr/bin/env python3
"""Tests of decl_index.py's index logic (no Lean): duplicates, ratchet, compare, touched modules."""
import json, os, pathlib, subprocess, sys, tempfile, unittest

sys.dont_write_bytecode = True
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import decl_index as d  # noqa: E402

ENV = dict(os.environ, GIT_AUTHOR_NAME="t", GIT_AUTHOR_EMAIL="t@t", GIT_COMMITTER_NAME="t",
           GIT_COMMITTER_EMAIL="t@t", GIT_CONFIG_GLOBAL=os.devnull, GIT_CONFIG_NOSYSTEM="1")


def row(name, h, module="Solidity.A", kind="theorem", cls=None, **kw):
    r = {"name": name, "module": module, "kind": kind, "typeHash": str(h), "shapeHash": "s" + str(h),
         "typeConsts": 1, "typeClass": cls or f"{h}.0", "aliasOf": None, "deprecated": False, "proj": False}
    r.update(kw)
    return r


class Duplicates(unittest.TestCase):
    def test_groups_skip_aliases_deprecated_projections_and_defs(self):
        rows = [row("a", 1), row("b", 1), row("c", 1, aliasOf="a"), row("e", 1, deprecated=True),
                row("f", 1, proj=True), row("g", 1, kind="def"), row("h", 2), row("i", 3), row("j", 3), row("k", 3)]
        g = d.duplicate_groups(rows)
        self.assertEqual([[r["name"] for r in x] for x in g], [["i", "j", "k"], ["a", "b"]])
        self.assertEqual(d.redundant(g), 3)

    def test_ratchet(self):
        with tempfile.TemporaryDirectory() as t:
            idx, base = pathlib.Path(t) / "i.jsonl", pathlib.Path(t) / "b.json"
            idx.write_text("".join(json.dumps(r) + "\n" for r in [row("a", 1), row("b", 1), row("c", 1)]))
            saved = d.BASELINE; d.BASELINE = base
            try:
                base.write_text('{"duplicate_theorems": 2}'); self.assertEqual(d.ratchet(idx), 0)
                base.write_text('{"duplicate_theorems": 1}'); self.assertEqual(d.ratchet(idx), 1)
                base.write_text('{"duplicate_theorems": 5}'); d.ratchet(idx, update=True)
                self.assertEqual(json.loads(base.read_text())["duplicate_theorems"], 2)
                base.write_text('{"duplicate_theorems": -1}')
                with self.assertRaises(d.SetupError): d.ratchet(idx)
            finally:
                d.BASELINE = saved

    def test_empty_index_is_a_setup_error(self):
        with tempfile.NamedTemporaryFile("w", suffix=".jsonl", delete=False) as f: pass
        try:
            with self.assertRaises(d.SetupError): d.load(f.name)
        finally:
            os.unlink(f.name)


class Compare(unittest.TestCase):
    base = [row("Old.a", 1, "Solidity.X"), row("Lib.b", 2, "Solidity.Y"), row("Lib.c", 3, "Solidity.Y")]

    def run_cmp(self, head, sp=False, waived=frozenset(), touched=("Solidity.X",)):
        return d.compare(self.base, head, list(touched), sp, waived)

    def test_renamed_copy_fails_and_alias_passes(self):
        ok, rep = self.run_cmp(self.base[:1] + [row("New.copy", 2, "Solidity.X")])
        self.assertFalse(ok); self.assertIn("New.copy (Solidity.X) = Lib.b", "\n".join(rep))
        ok, rep = self.run_cmp(self.base[:1] + [row("New.copy", 2, "Solidity.X", aliasOf="Lib.b")])
        self.assertTrue(ok, rep)

    def test_two_new_copies_of_a_new_statement_fail(self):
        ok, rep = self.run_cmp([row("Old.a", 1, "Solidity.X"), row("n1", 9, "Solidity.X", cls="9.0"),
                                row("n2", 9, "Solidity.X", cls="9.0")])
        self.assertFalse(ok); self.assertIn("n2 (Solidity.X) = n1", "\n".join(rep))

    def test_rename_passes(self):
        ok, rep = self.run_cmp([row("Old.renamed", 1, "Solidity.X")])
        self.assertTrue(ok, rep); self.assertIn("rename Old.a -> Old.renamed", "\n".join(rep))

    def test_statement_change_fails_only_when_preserving(self):
        head = [row("Old.a", 7, "Solidity.X")]
        ok, rep = self.run_cmp(head); self.assertTrue(ok, rep); self.assertIn("statement changed: Old.a", "\n".join(rep))
        ok, rep = self.run_cmp(head, sp=True); self.assertFalse(ok)
        ok, rep = self.run_cmp(head, sp=True, waived={"statements"}); self.assertTrue(ok, rep)

    def test_removal_fails_only_when_preserving(self):
        ok, _ = self.run_cmp([]); self.assertTrue(ok)
        ok, rep = self.run_cmp([], sp=True); self.assertFalse(ok); self.assertIn("removed: Old.a", "\n".join(rep))

    def test_duplicate_waiver(self):
        ok, rep = self.run_cmp(self.base[:1] + [row("New.copy", 2, "Solidity.X")], waived={"duplicates"})
        self.assertTrue(ok, rep); self.assertIn("waived", "\n".join(rep))

    def test_untouched_modules_are_not_compared(self):
        ok, rep = self.run_cmp([row("Lib.b", 99, "Solidity.Y"), row("Old.a", 1, "Solidity.X")], sp=True)
        self.assertTrue(ok, rep)

    def test_key_needs_shape_and_constants_too(self):
        other = row("New.same_hash", 2, "Solidity.X"); other["shapeHash"] = "different"
        ok, rep = self.run_cmp(self.base[:1] + [other]); self.assertTrue(ok, rep)


class Git(unittest.TestCase):
    def test_touched_modules_and_waivers(self):
        with tempfile.TemporaryDirectory() as t:
            g = lambda *a: subprocess.run(["git", *a], cwd=t, env=ENV, check=True, capture_output=True, text=True).stdout
            g("init", "-q", "-b", "main")
            os.makedirs(f"{t}/Solidity/Scratch")
            for p in ("Solidity/A.lean", "Solidity/B.lean", "Solidity/Scratch/S.lean"):
                pathlib.Path(t, p).write_text("x\n")
            g("add", "-A"); g("commit", "-qm", "base"); g("branch", "base")
            for p in ("Solidity/A.lean", "Solidity/Scratch/S.lean", "Solidity/C.lean", "notes.md"):
                pathlib.Path(t, p).write_text("y\n")
            os.unlink(f"{t}/Solidity/B.lean")
            g("add", "-A"); g("commit", "-qm", "change\n\nReview-Check: duplicates frozen statement copy")
            cwd = os.getcwd(); os.chdir(t)
            try:
                merge, mods = d.touched_modules("base")
                self.assertEqual(mods, ["Solidity.A", "Solidity.C"])
                self.assertEqual(d.waivers(merge), {"duplicates"})
            finally:
                os.chdir(cwd)


if __name__ == "__main__":
    unittest.main()
