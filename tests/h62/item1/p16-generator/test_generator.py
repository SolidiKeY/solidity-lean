#!/usr/bin/env python3
"""Black-box drift controls against a disposable miniature checkout."""
import hashlib
import json
import pathlib
import shutil
import subprocess
import sys
import tempfile
import unittest

ROOT = pathlib.Path(__file__).resolve().parents[4]
LANE = pathlib.Path("scripts/h62/item1/p16-generator")
TARGET = pathlib.Path("Solidity/Yul/Interfaces/P16.lean")


class GeneratorControls(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.root = pathlib.Path(self.tmp.name)
        shutil.copytree(ROOT / LANE, self.root / LANE)
        (self.root / TARGET).parent.mkdir(parents=True)
        shutil.copyfile(ROOT / TARGET, self.root / TARGET)
        for p in (self.root / LANE / "imports").glob("*.txt"):
            source = self.root / (p.read_text().strip().replace(".", "/") + ".lean")
            source.parent.mkdir(parents=True, exist_ok=True)
            source.touch()
        self.original = (self.root / TARGET).read_text()
        git_dir = subprocess.run(["git", "rev-parse", "--absolute-git-dir"], cwd=ROOT, text=True, capture_output=True, check=True).stdout.strip()
        (self.root / ".git").write_text("gitdir: " + git_dir + "\n")

    def tearDown(self):
        self.tmp.cleanup()

    def run_gen(self, arg):
        return subprocess.run([sys.executable, str(self.root / LANE / "generate.py"), arg], text=True, capture_output=True)

    def check_drift(self, text, message):
        (self.root / TARGET).write_text(text)
        result = self.run_gen("--check")
        self.assertEqual(result.returncode, 1, result.stderr)
        self.assertIn(message, result.stdout)

    def test_exact(self):
        self.assertEqual(self.run_gen("--check").returncode, 0)
        self.assertEqual(self.run_gen("--render").stdout, self.original)

    def test_missing_and_extra(self):
        line = self.original.splitlines(keepends=True)[0]
        self.check_drift(self.original.removeprefix(line), "missing import")
        self.check_drift(self.original + "\nimport Solidity.Yul.Extra\n", "extra import")

    def test_duplicate_order_and_body(self):
        lines = self.original.splitlines(keepends=True)
        self.check_drift(lines[0] + self.original, "non-generated")
        lines[0], lines[1] = lines[1], lines[0]
        self.check_drift("".join(lines), "non-generated")
        self.check_drift(self.original + "-- drift\n", "non-generated")

    def test_missing_target_render_and_migration_patch(self):
        target = self.root / TARGET
        patch = self.run_gen("--patch").stdout
        self.assertEqual(patch, "")
        command = [sys.executable, str(self.root / LANE / "generate.py"), "--migration"]
        migration = subprocess.run(command + ["--render"], text=True, capture_output=True, check=True).stdout
        diff = subprocess.run(command + ["--patch"], text=True, capture_output=True, check=True).stdout
        applied = subprocess.run(["patch", "-p1"], cwd=self.root, input=diff, text=True, capture_output=True)
        self.assertEqual(applied.returncode, 0, applied.stderr)
        self.assertEqual(target.read_text(), migration)
        self.assertEqual(subprocess.run(command + ["--check"], capture_output=True).returncode, 0)
        self.assertEqual(self.run_gen("--check").returncode, 1)
        target.unlink()
        self.assertEqual(self.run_gen("--render").stdout, self.original)

    def test_fragment_and_source_drift(self):
        entries = sorted((self.root / LANE / "imports").glob("*.txt"))
        source = self.root / (entries[0].read_text().strip().replace(".", "/") + ".lean")
        source.unlink()
        self.assertEqual(self.run_gen("--check").returncode, 2)
        source.touch()
        extra = self.root / LANE / "imports" / "999-Extra.txt"
        extra.write_text("Solidity.Yul.Extra\n")
        (self.root / "Solidity/Yul/Extra.lean").touch()
        result = self.run_gen("--check")
        self.assertEqual(result.returncode, 2)
        self.assertIn("extra=", result.stderr)
        extra.unlink()
        entries[0].unlink()
        self.assertEqual(self.run_gen("--check").returncode, 2)
        self.assertEqual(self.run_gen("--render").returncode, 2)
        body = next((self.root / LANE / "body").glob("*.txt"))
        body.unlink()
        self.assertEqual(self.run_gen("--check").returncode, 2)

    def add_extension(self, owner, name, module=None, doc=None):
        ident = owner + "-" + name
        lane = self.root / LANE
        (lane / "registrations" / (ident + ".json")).write_text(json.dumps({"module": module, "documentation": doc is not None}))
        if module is not None:
            (lane / "imports" / ("ext-" + ident + ".txt")).write_text(module + "\n")
            source = self.root / (module.replace(".", "/") + ".lean")
            source.parent.mkdir(parents=True, exist_ok=True)
            source.touch()
        if doc is not None:
            (lane / "body" / ("ext-" + ident + ".txt")).write_text(doc)

    def test_concurrent_extensions_are_order_independent(self):
        self.add_extension("VY3", "Beta", "Solidity.Yul.Beta", "/-! Beta -/\n")
        self.add_extension("VY1", "Alpha", "Solidity.Yul.Alpha", "/-! Alpha -/\n")
        first = self.run_gen("--render")
        self.assertEqual(first.returncode, 0, first.stderr)
        self.assertLess(first.stdout.index("import Solidity.Yul.Alpha"), first.stdout.index("import Solidity.Yul.Beta"))
        self.assertLess(first.stdout.index("/-! Alpha -/"), first.stdout.index("/-! Beta -/"))
        lane = self.root / LANE
        paths = [p for directory in ("registrations", "imports", "body") for p in (lane / directory).glob("*VY[13]-*")]
        contents = [(p, p.read_bytes()) for p in paths]
        for path, _ in contents:
            path.unlink()
        for path, content in reversed(contents):
            path.write_bytes(content)
        self.assertEqual(self.run_gen("--render").stdout, first.stdout)
        (self.root / TARGET).write_text(first.stdout)
        self.assertEqual(self.run_gen("--check").returncode, 0)

    def test_extension_conflicts_and_registration(self):
        self.add_extension("VY1", "Alpha", "Solidity.Yul.Alpha", "/-! Alpha -/\n")
        self.add_extension("VY3", "Alpha", "Solidity.Yul.Alpha", "/-! Other -/\n")
        self.assertEqual(self.run_gen("--render").returncode, 2)
        lane = self.root / LANE
        (lane / "registrations/VY3-Alpha.json").unlink()
        (lane / "imports/ext-VY3-Alpha.txt").unlink()
        (lane / "body/ext-VY3-Alpha.txt").unlink()
        (lane / "body/ext-VY1-Alpha.txt").unlink()
        self.assertEqual(self.run_gen("--render").returncode, 2)
        (lane / "body/ext-VY1-Alpha.txt").write_text("/-! Alpha -/\n")
        registration = lane / "registrations/VY1-Alpha.json"
        registration.rename(lane / "registrations/OTHER-Alpha.json")
        self.assertEqual(self.run_gen("--render").returncode, 2)

    def test_census_missing_extra_and_order(self):
        command = [sys.executable, "-B", str(self.root / LANE / "census.py")]
        result = subprocess.run(command, text=True, capture_output=True)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn("imports=39 documentation_blocks=33", result.stdout)
        target = self.root / TARGET
        lines = self.original.splitlines(keepends=True)
        target.write_text("".join(lines[1:]))
        result = subprocess.run(command, text=True, capture_output=True)
        self.assertEqual(result.returncode, 1)
        self.assertIn("missing import Solidity.Yul.RawFrameLogic", result.stdout)
        target.write_text(self.original + "\n/-! extra documentation -/\n")
        result = subprocess.run(command, text=True, capture_output=True)
        self.assertEqual(result.returncode, 1)
        self.assertIn("extra documentation sha256:", result.stdout)
        lines[0], lines[1] = lines[1], lines[0]
        target.write_text("".join(lines))
        self.assertIn("import order differs", subprocess.run(command, text=True, capture_output=True).stdout)

    def test_baseline_content_and_joint_inventory_tamper(self):
        lane = self.root / LANE
        baseline = lane / "baseline-inventory.json"
        manifest = json.loads(baseline.read_text())
        fragment = lane / "body" / sorted(manifest["body"])[0]
        changed = fragment.read_text().replace("# Syntax", "# Changed syntax", 1)
        fragment.write_text(changed)
        self.assertEqual(self.run_gen("--render").returncode, 2)
        manifest["body"][fragment.name] = hashlib.sha256(fragment.read_bytes()).hexdigest()
        baseline.write_text(json.dumps(manifest))
        self.assertEqual(self.run_gen("--render").returncode, 0)
        result = subprocess.run([sys.executable, "-B", str(lane / "census.py"), "--baseline"], text=True, capture_output=True)
        self.assertEqual(result.returncode, 1, result.stderr)
        self.assertIn("documentation sha256:", result.stdout)

    def test_reject_injected_documentation_and_unexpected_files(self):
        self.add_extension("VY1", "Alpha", "Solidity.Yul.Alpha", "/-! Alpha -/\n")
        lane = self.root / LANE
        doc = lane / "body/ext-VY1-Alpha.txt"
        for value in ("", "/-! -/\n", "/-! hi -/\ndef injected : Nat := 1\n/-! hi -/\n", "/-! unclosed /- nested -/\n"):
            doc.write_text(value)
            self.assertEqual(self.run_gen("--render").returncode, 2, repr(value))
        doc.write_text("/-! Alpha -/\n")
        for path in (lane / "imports/stray.md", lane / "registrations/VY1-Oops.txt"):
            path.write_text("bad")
            self.assertEqual(self.run_gen("--render").returncode, 2, str(path))
            path.unlink()
        unexpected = lane / "body/nested"
        unexpected.mkdir()
        self.assertEqual(self.run_gen("--render").returncode, 2)

    def test_git_merge_concurrent_and_colliding_registrations(self):
        repo = self.root / "merge-fixture"
        repo.mkdir()
        def git(*args, check=True):
            return subprocess.run(["git", "-c", "user.name=Fixture", "-c", "user.email=fixture@example.invalid", *args], cwd=repo, text=True, capture_output=True, check=check)
        git("init", "-q")
        (repo / "seed").write_text("seed\n")
        git("add", "seed")
        git("commit", "-qm", "base")
        base = git("rev-parse", "HEAD").stdout.strip()
        def branch(name, files):
            git("checkout", "-q", "-B", name, base)
            for path, contents in files.items():
                dest = repo / path
                dest.parent.mkdir(parents=True, exist_ok=True)
                dest.write_text(contents)
                git("add", path)
            git("commit", "-qm", name)
            return git("rev-parse", "HEAD").stdout.strip()
        def addition(owner, name):
            ident = owner + "-" + name
            module = "Solidity.Yul." + name
            return {"registrations/" + ident + ".json": json.dumps({"module": module, "documentation": True}),
                    "imports/ext-" + ident + ".txt": module + "\n",
                    "body/ext-" + ident + ".txt": "/-! " + name + " -/\n"}
        a = branch("owner-a", addition("VY1", "Alpha"))
        b = branch("owner-b", addition("VY3", "Beta"))
        merged_ab = git("merge-tree", "--write-tree", a, b).stdout.splitlines()[0]
        merged_ba = git("merge-tree", "--write-tree", b, a).stdout.splitlines()[0]
        self.assertEqual(merged_ab, merged_ba)
        archive = subprocess.run(["git", "archive", merged_ab], cwd=repo, capture_output=True, check=True).stdout
        subprocess.run(["tar", "-xf", "-", "-C", str(self.root / LANE)], input=archive, check=True)
        for name in ("Alpha", "Beta"):
            (self.root / "Solidity/Yul" / (name + ".lean")).touch()
        result = self.run_gen("--render")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn("import Solidity.Yul.Alpha", result.stdout)
        self.assertIn("import Solidity.Yul.Beta", result.stdout)
        a = branch("collision-a", {"registrations/VY1-Shared.json": "left\n"})
        b = branch("collision-b", {"registrations/VY1-Shared.json": "right\n"})
        self.assertNotEqual(git("merge-tree", "--write-tree", a, b, check=False).returncode, 0)

    def test_whitespace_only_baseline_tamper_and_nested_documentation(self):
        lane = self.root / LANE
        manifest_path = lane / "baseline-inventory.json"
        manifest = json.loads(manifest_path.read_text())
        name = sorted(manifest["body"])[0]
        fragment = lane / "body" / name
        fragment.write_text(fragment.read_text() + "\n")
        manifest["body"][name] = hashlib.sha256(fragment.read_bytes()).hexdigest()
        manifest_path.write_text(json.dumps(manifest))
        result = subprocess.run([sys.executable, "-B", str(lane / "census.py"), "--baseline"], text=True, capture_output=True)
        self.assertEqual(result.returncode, 2, result.stderr)
        self.assertIn("invalid documentation fragment", result.stderr)
        fragment.write_text(fragment.read_text()[:-1])
        manifest["body"][name] = hashlib.sha256(fragment.read_bytes()).hexdigest()
        manifest_path.write_text(json.dumps(manifest))
        (self.root / TARGET).write_text(self.original + "\n")
        result = subprocess.run([sys.executable, "-B", str(lane / "census.py")], text=True, capture_output=True)
        self.assertEqual(result.returncode, 1, result.stderr)
        self.assertIn("byte-level text differs", result.stdout)
        self.add_extension("VY1", "Nested", None, "/-! outer\n/-! inner -/\nend -/\n")
        rendered = self.run_gen("--render")
        self.assertEqual(rendered.returncode, 0, rendered.stderr)
        (self.root / TARGET).write_text(rendered.stdout)
        result = subprocess.run([sys.executable, "-B", str(lane / "census.py")], text=True, capture_output=True)
        self.assertEqual(result.returncode, 0, result.stderr)

    def test_crlf_is_not_byte_reproduction(self):
        target = self.root / TARGET
        target.write_bytes(self.original.replace("\n", "\r\n").encode())
        self.assertNotEqual(self.run_gen("--check").returncode, 0)
        result = subprocess.run([sys.executable, "-B", str(self.root / LANE / "census.py")], text=True, capture_output=True)
        self.assertNotEqual(result.returncode, 0)
        target.write_bytes(self.original.encode())
        lane = self.root / LANE
        manifest_path = lane / "baseline-inventory.json"
        manifest = json.loads(manifest_path.read_text())
        name = sorted(manifest["body"])[0]
        fragment = lane / "body" / name
        fragment.write_bytes(fragment.read_bytes().replace(b"\n", b"\r\n"))
        manifest["body"][name] = hashlib.sha256(fragment.read_bytes()).hexdigest()
        manifest_path.write_text(json.dumps(manifest))
        self.assertEqual(self.run_gen("--render").returncode, 2)

    def test_bad_input(self):
        entries = sorted((self.root / LANE / "imports").glob("*.txt"))
        entries[1].write_text(entries[0].read_text())
        self.assertEqual(self.run_gen("--check").returncode, 2)
        entries[1].write_text("not a module\n")
        self.assertEqual(self.run_gen("--check").returncode, 2)
        entries[1].write_text("Solidity.Yul.Missing\n")
        self.assertEqual(self.run_gen("--check").returncode, 2)


if __name__ == "__main__":
    unittest.main()
