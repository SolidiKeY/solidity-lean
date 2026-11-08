"""Guard against accepting a compiled but unauthenticated vector inventory."""
import contextlib
import io
import shutil
import sys
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT / "scripts/h55/vectors-tables"))
import compile_vectors as compiler
import vector_census as census


class CompileInputTests(unittest.TestCase):
    def populate(self, root):
        for name in census.PATHS:
            target = root / name
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(ROOT / name, target)

    def test_authenticated_inventory_reaches_serial_driver(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory) / "generated"
            out = Path(directory) / "objects"
            self.populate(root)
            with patch.object(compiler, "GENERATED", root), patch.object(compiler, "OUT", out):
                with patch.object(compiler, "run") as run, contextlib.redirect_stdout(io.StringIO()):
                    compiler.main()
                    self.assertEqual(run.call_count, len(compiler.DEPS) + len(census.PATHS))
                    self.assertEqual([str(call.args[0].relative_to(root)) for call in
                                      run.call_args_list[len(compiler.DEPS):]], census.PATHS)

    def test_rejected_inputs_have_no_compile_or_output_side_effect(self):
        for mutation in ["missing", "extra", "body", "order", "schema", "symlink", "root_symlink", "parent_symlink"]:
            with self.subTest(mutation=mutation), tempfile.TemporaryDirectory() as directory:
                root = Path(directory) / "generated"
                out = Path(directory) / "objects"
                self.populate(root)
                target = root / census.PATHS[0]
                if mutation == "missing":
                    target.unlink()
                elif mutation == "extra":
                    (root / "Extra.lean").write_text("-- extra source\n")
                elif mutation == "body":
                    target.write_bytes(target.read_bytes() + b"-- changed bytes\n")
                elif mutation == "order":
                    lines = target.read_bytes().splitlines(keepends=True)
                    rows = [i for i, line in enumerate(lines) if line.startswith(b"theorem ")]
                    lines[rows[0]], lines[rows[1]] = lines[rows[1]], lines[rows[0]]
                    target.write_bytes(b"".join(lines))
                elif mutation == "schema":
                    target.write_bytes(target.read_bytes().replace(b"decide +kernel", b"rfl", 1))
                elif mutation == "symlink":
                    target.unlink()
                    target.symlink_to(ROOT / census.PATHS[0])
                elif mutation == "root_symlink":
                    alias = Path(directory) / "alias"
                    alias.symlink_to(root, target_is_directory=True)
                    root = alias
                else:
                    alias = Path(directory) / "alias"
                    alias.symlink_to(root.parent, target_is_directory=True)
                    root = alias / root.name
                with patch.object(compiler, "GENERATED", root), patch.object(compiler, "OUT", out):
                    with patch.object(compiler, "run") as run:
                        with self.assertRaises((RuntimeError, ValueError, OSError)):
                            compiler.main()
                        run.assert_not_called()
                        self.assertFalse(out.exists())


if __name__ == "__main__":
    unittest.main()
