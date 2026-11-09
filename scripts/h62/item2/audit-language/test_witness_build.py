"""Guard stale imports, transitive drift and cache fallback in fresh witness credit."""
import os
import hashlib
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest
from unittest.mock import patch
from witness_build import closure, imports, environment, compile_closure, validate_build, toolchain, ROOT


class WitnessBuildTests(unittest.TestCase):
    def test_import_header(self):
        self.assertEqual(imports('/- import Wrong -/\nprelude\nimport Lean A.«b-c»\n-- hi\nimport B\ntheorem x : True := by trivial'),
                         ['Lean', 'A.b-c', 'B'])
        for source in ('public import Lean', 'import "bad"', 'import\n Lean',
                       'theorem x : True := by trivial\nimport Lean'):
            with self.subTest(source=source), self.assertRaises(ValueError):
                imports(source)

    def test_transitive_closure_and_cycles(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            generated = root / 'Audit.lean'
            generated.write_text('import A\n')
            (root / 'A.lean').write_text('import B\n')
            (root / 'B.lean').write_text('theorem ok : True := by trivial\n')
            first = closure(generated, root)
            self.assertEqual(first['modules'], ['B', 'A'])
            (root / 'B.lean').write_text('theorem ok : True := True.intro\n')
            self.assertNotEqual(first, closure(generated, root))
            (root / 'B.lean').write_text('import A\n')
            with self.assertRaises(ValueError):
                closure(generated, root)

    def test_search_path_and_preexisting_build(self):
        with patch.dict(os.environ, {'LEAN_PATH': '/stale', 'LEAN_SYSROOT': '/stale',
                                     'LAKE_HOME': '/stale', 'LD_PRELOAD': '/stale',
                                     'LD_LIBRARY_PATH': '/stale', 'DYLD_INSERT_LIBRARIES': '/stale'}):
            env = environment(Path('/fresh'), '/trusted')
        self.assertEqual(env['LEAN_PATH'], '/fresh:/trusted/lib/lean')
        self.assertNotIn('LEAN_SYSROOT', env)
        self.assertNotIn('LAKE_HOME', env)
        for name in ('LD_PRELOAD', 'LD_LIBRARY_PATH', 'DYLD_INSERT_LIBRARIES'):
            self.assertNotIn(name, env)
        with tempfile.TemporaryDirectory() as tmp:
            with self.assertRaises(ValueError):
                compile_closure(Path(tmp) / 'Audit.lean', Path(tmp), Path(tmp))

    def test_proxy_invocation_is_not_resolved_before_dispatch(self):
        with tempfile.TemporaryDirectory() as tmp:
            prefix = Path(tmp) / "toolchain"
            (prefix / "bin").mkdir(parents=True)
            (prefix / "bin/lean").write_bytes(b"selected")
            proxy = Path(tmp) / "elan"
            proxy.write_bytes(b"proxy")
            invocation = Path(tmp) / "lean"
            invocation.symlink_to(proxy)
            with patch("witness_build.subprocess.check_output", return_value=str(prefix) + "\n") as query:
                result = toolchain(str(invocation))
            self.assertEqual(query.call_args.args[0][0], str(invocation))
            self.assertEqual(result["lean"], str(prefix / "bin/lean"))
            self.assertIn(str(proxy), result["files"])

    def test_artifact_and_command_substitution_refused(self):
        with tempfile.TemporaryDirectory() as tmp:
            build = Path(tmp)
            generated = build / "Audit.lean"
            generated.write_text("import Sample\n")
            artifact = build / "Sample.olean"
            artifact.write_bytes(b"compiled")
            cl = {"modules": ["Sample"], "sources": {"Sample.lean": "source"}}
            compiler = {"lean": "/trusted/bin/lean", "invocation": "/trusted/bin/lean",
                        "prefix": "/trusted", "files": {}}
            command = [compiler["lean"], "--root=" + str(ROOT), "--tstack=131072", "-j1",
                       "-o", str(artifact), str(ROOT / "Sample.lean")]
            record = {"closure": cl, "generated_sha256": hashlib.sha256(generated.read_bytes()).hexdigest(),
                      "compiler": compiler, "artifacts": {str(artifact): hashlib.sha256(b"compiled").hexdigest()},
                      "commands": [command, [compiler["lean"], "--root=" + str(build),
                                               "--tstack=131072", "-j1", str(generated)]],
                      "search_path": environment(build, "/trusted")["LEAN_PATH"]}
            with patch("witness_build.closure", return_value=cl), patch("witness_build.toolchain", return_value=compiler):
                validate_build(record, generated)
                with self.assertRaises(ValueError):
                    validate_build(dict(record, commands=[]), generated)
                artifact.write_bytes(b"substituted")
                with self.assertRaises(ValueError):
                    validate_build(record, generated)

    @unittest.skipUnless(shutil.which('lean'), 'bounded Lean integration required')
    def test_stale_object_cannot_hide_broken_current_source(self):
        with tempfile.TemporaryDirectory() as tmp:
            base = Path(tmp)
            root = base / 'source'
            root.mkdir()
            source = root / 'Sample.lean'
            source.write_text('theorem checked : True := True.intro\n')
            generated = base / 'Audit.lean'
            generated.write_text('import Sample\n#check checked\n')
            fresh = base / 'first'
            record = compile_closure(generated, fresh, root)
            self.assertEqual(set(record['closure']['sources']), {'Sample.lean'})
            stale = root / '.lake/build/lib/lean'
            stale.mkdir(parents=True)
            shutil.copyfile(fresh / 'Sample.olean', stale / 'Sample.olean')
            source.write_text('theorem checked : False := by trivial\n')
            with patch.dict(os.environ, {'LEAN_PATH': str(stale)}):
                with self.assertRaises(subprocess.CalledProcessError):
                    compile_closure(generated, base / 'second', root)
            self.assertTrue((stale / 'Sample.olean').is_file())


if __name__ == '__main__':
    unittest.main()
