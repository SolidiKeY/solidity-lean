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
    def test_library_boundary_for_changed_and_touched_modules(self):
        with tempfile.TemporaryDirectory() as t:
            g = lambda *a: subprocess.run(["git", *a], cwd=t, env=ENV, check=True, capture_output=True, text=True).stdout.strip()
            g("init", "-q", "-b", "main")
            paths = ["Solidity/A.lean", "Solidity/Deleted.lean", "Solidity/Examples/E.lean",
                     "Solidity/Corpus/C.lean", "Solidity/TestSuite/T.lean",
                     "Solidity/Solkey/TestSuite.lean", "Solidity/Scratch/S.lean",
                     "Solidity/ExamplesExtra.lean"]
            for p in paths:
                f = pathlib.Path(t, p); f.parent.mkdir(parents=True, exist_ok=True); f.write_text("old\n")
            g("add", "-A"); g("commit", "-qm", "base"); g("branch", "base")
            for p in paths: pathlib.Path(t, p).write_text("new\n")
            pathlib.Path(t, "Solidity/Deleted.lean").unlink()
            g("add", "-A"); g("commit", "-qm", "change")
            cwd = os.getcwd(); os.chdir(t)
            try:
                self.assertEqual(d.touched_modules("base")[1], ["Solidity.A", "Solidity.ExamplesExtra"])
                self.assertEqual(d.changed_modules("base", "HEAD"),
                                 (["Solidity.A", "Solidity.ExamplesExtra"],
                                  {"Solidity.A", "Solidity.Deleted", "Solidity.ExamplesExtra"}))
            finally:
                os.chdir(cwd)

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


class LakeImports(unittest.TestCase):
    """dump builds the touched modules with Lake before linking oleans, so a declaration new on
    the lane is indexed even when .lake/build still holds an older olean (b2 pre-gate,
    MemoryStructDefaultPlan). Lake and Lean are faked: lean sees what the linked olean holds."""

    def dump_stale(self, build=True):
        with tempfile.TemporaryDirectory() as t:
            top = pathlib.Path(t); lib = top / ".lake/build/lib/lean/Solidity"; lib.mkdir(parents=True)
            (lib / "M.olean").write_text("Old\n"); (lib / "M.trace").write_text("{}")
            calls = []

            def run(cmd, cwd=None, env=None, **kw):
                calls.append(cmd[:2])
                if cmd[:2] == ["lake", "build"]:
                    (lib / "M.olean").write_text("Old\nMemoryStructDefaultPlan\n")
                elif cmd[:2] == ["lake", "env"]:
                    names = (pathlib.Path(env["DECLINDEX_LIB"]) / "Solidity/M.olean").read_text().split()
                    pathlib.Path(env["DECLINDEX_OUT"]).write_text(
                        "".join(json.dumps(row(n, i, "Solidity.M")) + "\n" for i, n in enumerate(names)))
                    return subprocess.CompletedProcess(cmd, 0, f"decls={len(names)}\n", "")
                return subprocess.CompletedProcess(cmd, 0, "", "")

            saved = d.root, d.artifacts, d.subprocess.run, d.lake_build
            d.root, d.artifacts, d.subprocess.run = (lambda: top), (lambda: None), run
            if not build: d.lake_build = lambda top, modules: None
            try:
                out = top / "i.jsonl"; d.dump(out, ["Solidity.M"])
                return calls, [r["name"] for r in d.load(out)]
            finally:
                d.root, d.artifacts, d.subprocess.run, d.lake_build = saved

    def test_lake_build_runs_first(self):
        calls, names = self.dump_stale()
        self.assertEqual(calls, [["lake", "build"], ["lake", "env"]])
        self.assertIn("MemoryStructDefaultPlan", names)

    def test_old_invocation_misses_the_declaration(self):
        _, names = self.dump_stale(build=False)
        self.assertNotIn("MemoryStructDefaultPlan", names)


class HostCache(unittest.TestCase):
    """Coordinator host (dc3): Lake built MemoryStructDefaultPlan into a cache other than the
    one decl_index guessed (no LAKE_CACHE_DIR, elan toolchain cache absent), .lake/build held
    only its trace, nothing was linked and Lean reported the olean missing."""

    def setUp(self):
        self.t = tempfile.TemporaryDirectory(); t = pathlib.Path(self.t.name)
        self.top, self.lib = t / "top", t / "lib"
        self.build = self.top / ".lake/build/lib/lean/Solidity/Evm"; self.build.mkdir(parents=True)
        (self.build / "MemoryStructDefaultPlan.trace").write_text(json.dumps({"outputs": {"o": "abc123"}}))
        self.xdg = t / "xdg"; (self.xdg / "lake/artifacts").mkdir(parents=True)
        self.env = {k: os.environ.get(k) for k in ("LAKE_CACHE_DIR", "XDG_CACHE_HOME", "HOME")}
        os.environ.pop("LAKE_CACHE_DIR", None); os.environ["XDG_CACHE_HOME"] = str(self.xdg)
        os.environ["HOME"] = str(t / "home")
        self.run_saved = d.subprocess.run
        d.subprocess.run = lambda cmd, **kw: subprocess.CompletedProcess(cmd, 1, "", "")  # no elan

    def tearDown(self):
        d.subprocess.run = self.run_saved
        for k, v in self.env.items():
            if v is None: os.environ.pop(k, None)
            else: os.environ[k] = v
        self.t.cleanup()

    M = "Solidity.Evm.MemoryStructDefaultPlan"

    def test_olean_in_xdg_cache_is_linked(self):
        (self.xdg / "lake/artifacts/abc123.olean").write_text("MemoryStructDefaultPlan")
        d.link_build(self.top, self.lib, [self.M])
        self.assertEqual((self.lib / "Solidity/Evm/MemoryStructDefaultPlan.olean").read_text(),
                         "MemoryStructDefaultPlan")

    def test_unresolved_needed_module_is_a_setup_error(self):
        (self.build / "Other.olean").write_text("x"); (self.build / "Other.trace").write_text("{}")
        os.symlink(self.top / "gone.olean", self.build / "MemoryStructDefaultPlan.olean")
        with self.assertRaises(d.SetupError) as e: d.link_build(self.top, self.lib, [self.M])
        self.assertIn(self.M, str(e.exception))
        self.assertFalse(os.path.lexists(self.lib / "Solidity/Evm/MemoryStructDefaultPlan.olean"))

    def touched_importer(self):
        """Touched Solidity.Evm.User (olean in .lake/build) imports
        MemoryStructDefaultPlan, whose olean is only in a Lake artifact cache."""
        src = self.top / "Solidity/Evm"; src.mkdir(parents=True)
        (src / "User.lean").write_text("import Solidity.Evm.MemoryStructDefaultPlan\n\ndef u := 1\n")
        (src / "MemoryStructDefaultPlan.lean").write_text("def m := 0\n")
        (self.build / "User.olean").write_text("User"); (self.build / "User.trace").write_text("{}")
        return "Solidity.Evm.User"

    def test_transitive_import_olean_from_cache_is_linked(self):
        u = self.touched_importer()
        (self.xdg / "lake/artifacts/abc123.olean").write_text("MemoryStructDefaultPlan")
        d.link_build(self.top, self.lib, [u])
        self.assertEqual((self.lib / "Solidity/Evm/MemoryStructDefaultPlan.olean").read_text(),
                         "MemoryStructDefaultPlan")
        self.assertEqual((self.lib / "Solidity/Evm/User.olean").read_text(), "User")

    def test_unlinked_transitive_import_is_a_setup_error(self):
        u = self.touched_importer()
        with self.assertRaises(d.SetupError) as e: d.link_build(self.top, self.lib, [u])
        self.assertIn(self.M, str(e.exception))

    def test_header_imports_skip_comments(self):
        text = "/- header\n /- nested -/ -/\n-- line\nimport A.B -- why\n/-- doc -/\nimport C\n\ndef import_x := 1\nimport D\n"
        self.assertEqual(d.header_imports(text), ["A.B", "C"])
        self.assertEqual(d.header_imports("module\npublic import X\nimport all Y\n"), ["X", "Y"])

    def test_closure_follows_import_after_header_comment(self):
        src = self.top / "Solidity/Backend"; src.mkdir(parents=True)
        (src / "EvmVectors.lean").write_text("/-\nVectors.\n-/\nimport Solidity.Backend.Assembler\n")
        (src / "Assembler.lean").write_text("def a := 0\n")
        self.assertEqual(d.import_closure(self.top, ["Solidity.Backend.EvmVectors"]),
                         {"Solidity.Backend.EvmVectors", "Solidity.Backend.Assembler"})

    def test_trace_output_shapes(self):
        self.assertEqual(d.trace_hashes({"o": ["a.olean", "b"], "i": "c.ilean"}), ["a", "b", "c"])
        (self.build / "MemoryStructDefaultPlan.trace").write_text(json.dumps({"outputs": {"o": ["abc123.olean"]}}))
        (self.xdg / "lake/artifacts/abc123.olean").write_text("MemoryStructDefaultPlan")
        d.link_build(self.top, self.lib, [self.M])
        self.assertTrue((self.lib / "Solidity/Evm/MemoryStructDefaultPlan.olean").is_file())

    def test_olean_where_lake_fetched_it_is_linked(self):
        """H1071: Lake fetched the module into a cache only `lake env` names; the trace has no
        outputs and the hash is in the `.olean.hash` file Lake wrote next to the build path."""
        u = self.touched_importer()
        (self.build / "MemoryStructDefaultPlan.trace").write_text("{}")
        (self.build / "MemoryStructDefaultPlan.olean.hash").write_text("feedface00000001")
        fetched = self.top.parent / "fetched"; (fetched / "artifacts").mkdir(parents=True)
        (fetched / "artifacts/feedface00000001.olean").write_text("MemoryStructDefaultPlan")
        def run(cmd, **kw):
            if cmd[:2] == ["lake", "env"]:
                return subprocess.CompletedProcess(cmd, 0, "LAKE_CACHE_DIR=%s\nPATH=/x\n" % fetched, "")
            return subprocess.CompletedProcess(cmd, 1, "", "")
        d.subprocess.run = run
        d.link_build(self.top, self.lib, [u])
        self.assertEqual((self.lib / "Solidity/Evm/MemoryStructDefaultPlan.olean").read_text(),
                         "MemoryStructDefaultPlan")
        d.subprocess.run = lambda cmd, **kw: subprocess.CompletedProcess(cmd, 1, "", "")
        with self.assertRaises(d.SetupError): d.link_build(self.top, self.top.parent / "lib2", [u])


if __name__ == "__main__":
    unittest.main()
