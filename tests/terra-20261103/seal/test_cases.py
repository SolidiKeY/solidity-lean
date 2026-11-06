import hashlib
import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest

TOOL = Path(__file__).resolve().parents[3] / "scripts/coord-tools/seal.sh"

class SealCases(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(prefix="terra seal ")
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.repo = self.root / "repository with spaces"
        self.repo.mkdir()
        self.git("init", "-q")
        self.git("config", "user.name", "Fixture")
        self.git("config", "user.email", "fixture@example.invalid")
        (self.repo / "tracked").write_text("base\n")
        self.git("add", "tracked")
        self.git("commit", "-qm", "base")
        self.base = self.git("rev-parse", "HEAD")
        self.branch = self.git("branch", "--show-current")
        (self.repo / "tracked").write_text("tip\n")
        self.git("commit", "-qam", "tip")
        self.head = self.git("rev-parse", "HEAD")
        self.out = self.root / "seal output"
        self.env = dict(os.environ, TMPDIR=str(self.root))

    def git(self, *args):
        return subprocess.check_output(["git", *map(str, args)], cwd=self.repo, text=True).strip()

    def run_seal(self, *args):
        return subprocess.run(["bash", str(TOOL), *map(str, args)], cwd=self.repo,
                              env=self.env, text=True, capture_output=True)

    def create(self, base=None):
        result = self.run_seal(self.out, base or self.base)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn("seal verified", result.stdout)
        return self.inventory()

    def inventory(self):
        self.assertEqual({p.relative_to(self.out).as_posix() for p in self.out.rglob("*") if p.is_file()},
                         {"checkpoint.bundle", "manifest.json", "SHA256SUMS"})
        manifest = json.loads((self.out / "manifest.json").read_text())
        bundle = self.out / "checkpoint.bundle"
        digest = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
        self.assertEqual(manifest, {"head": self.head, "base": self.base,
                                  "files": [{"path": "checkpoint.bundle", "size": bundle.stat().st_size,
                                             "sha256": digest(bundle)}]})
        self.assertEqual((self.out / "SHA256SUMS").read_text().splitlines(),
                         [digest(bundle) + "  checkpoint.bundle", digest(self.out / "manifest.json") + "  manifest.json"])
        self.assertEqual(self.git("bundle", "list-heads", bundle).split()[0], self.head)
        return manifest

    def rewrite_manifest(self, **updates):
        path = self.out / "manifest.json"
        data = json.loads(path.read_text())
        data.update(updates)
        path.write_text(json.dumps(data, indent=2) + "\n")
        self.rewrite_sums()

    def rewrite_sums(self):
        paths = sorted(p for p in self.out.rglob("*") if p.is_file() and p.name != "SHA256SUMS")
        (self.out / "SHA256SUMS").write_text("".join(hashlib.sha256(p.read_bytes()).hexdigest() + "  " + p.relative_to(self.out).as_posix() + "\n" for p in paths))

    def rejected(self):
        result = self.run_seal("--verify", self.out)
        self.assertNotEqual(result.returncode, 0, result.stdout)
        self.assertNotIn("seal verified", result.stdout)

    def test_usage(self):
        for args in [(), ("a", "b", "c"), ("--verify", self.root / "missing")]:
            result = self.run_seal(*args)
            self.assertNotEqual(result.returncode, 0, (args, result.stdout))
            self.assertIn("seal:", result.stderr)
        self.assertFalse(self.out.exists())

    def test_clean_roundtrip(self):
        self.create()
        result = self.run_seal("--verify", self.out)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn("seal verified", result.stdout)
        self.inventory()

    def test_base_merge_base(self):
        self.git("checkout", "-qb", "diverged", self.base)
        (self.repo / "other").write_text("other\n")
        self.git("add", "other")
        self.git("commit", "-qm", "other")
        other = self.git("rev-parse", "HEAD")
        self.git("checkout", "-q", self.branch)
        self.assertEqual(self.git("merge-base", other, self.head), self.base)
        self.create(other)
        self.assertEqual(self.run_seal("--verify", self.out).returncode, 0)

    def test_manifest_tip(self):
        self.create()
        self.rewrite_manifest(head=self.base)
        self.rejected()

    def test_manifest_base(self):
        self.create()
        self.rewrite_manifest(base=self.head)
        self.rejected()

    def test_bundle_prerequisites(self):
        self.create()
        data = (self.out / "checkpoint.bundle").read_bytes().split(b"\n\n", 1)[0].splitlines()
        prerequisites = [line[1:].split()[0].decode() for line in data if line.startswith(b"-")]
        self.assertEqual(prerequisites, [self.base])
        self.git("bundle", "verify", self.out / "checkpoint.bundle")
        self.rewrite_manifest(base=self.head)
        self.rejected()

    def test_missing_file(self):
        self.create()
        for name in ("checkpoint.bundle", "manifest.json", "SHA256SUMS"):
            path = self.out / name
            contents = path.read_bytes()
            path.unlink()
            self.rejected()
            path.write_bytes(contents)

    def test_extra_file(self):
        self.create()
        (self.out / "extra").write_text("unlisted\n")
        self.rejected()
        self.rewrite_sums()
        self.rejected()

    def test_corrupt_bundle(self):
        self.create()
        path = self.out / "checkpoint.bundle"
        path.write_bytes(path.read_bytes()[:-20] + b"corrupt")
        self.rejected()
        manifest = json.loads((self.out / "manifest.json").read_text())
        manifest["files"][0].update(size=path.stat().st_size, sha256=hashlib.sha256(path.read_bytes()).hexdigest())
        (self.out / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
        self.rewrite_sums()
        self.rejected()

    def test_corrupt_checksum(self):
        self.create()
        path = self.out / "SHA256SUMS"
        path.write_text("0" * 64 + path.read_text()[64:])
        self.rejected()

    def test_empty_range(self):
        result = self.run_seal(self.out, self.head)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("empty base..HEAD", result.stderr)
        self.assertEqual(list(self.out.iterdir()), [])

    def test_paths_with_spaces(self):
        self.create()
        result = self.run_seal("--verify", self.out)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.inventory()
