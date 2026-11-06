#!/usr/bin/env python3
"""End-to-end owner revision test; all Git operations stay in a scratch repo."""
import json
import os
import re
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest

SOURCE_ROOT = Path(__file__).resolve().parents[4]
SCRATCH = Path("/workspace/scratch").resolve()
LANE = Path("scripts/h62/item1/p16-generator")
TARGET = Path("Solidity/Yul/Interfaces/P16.lean")
ORIGINAL_BASE = "c6f550e281a7e5affa9a99bc2cdaed556dec00e4"


class IsolatedOwnerCommit(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix="p16-owner-test-", dir=SCRATCH)
        self.repo = Path(self.temp.name).resolve()
        self.addCleanup(self.cleanup_fixture)
        if self.repo.parent != SCRATCH or self.repo == SOURCE_ROOT:
            raise RuntimeError("fixture is not an isolated direct child of /workspace/scratch")
        self.environment = {key: value for key, value in os.environ.items() if not key.startswith("GIT_")}
        self.environment.update(GIT_CONFIG_NOSYSTEM="1", GIT_CONFIG_GLOBAL="/dev/null", GIT_TERMINAL_PROMPT="0")
        self.template = self.repo / "empty-template"
        self.template.mkdir()
        self.git("init", "-q", "--template=" + str(self.template))
        actual_root = Path(self.git("rev-parse", "--show-toplevel").stdout.strip()).resolve()
        self.assertEqual(actual_root, self.repo)
        self.assertEqual(self.git("remote").stdout, "")
        shutil.copytree(SOURCE_ROOT / LANE, self.repo / LANE)
        (self.repo / TARGET).parent.mkdir(parents=True)
        shutil.copyfile(SOURCE_ROOT / TARGET, self.repo / TARGET)
        for fragment in (self.repo / LANE / "imports").glob("*.txt"):
            module = fragment.read_text().strip()
            if not re.fullmatch(r"Solidity(?:\.[A-Za-z_][A-Za-z_0-9]*)+", module):
                raise ValueError("invalid source module in fixture input")
            source = self.repo / (module.replace(".", "/") + ".lean")
            if not source.resolve().is_relative_to(self.repo):
                raise ValueError("source path escapes fixture")
            source.parent.mkdir(parents=True, exist_ok=True)
            source.write_text("-- synthetic source fixture\n")
        self.git("add", "--", "Solidity")
        self.git("commit", "-qm", "synthetic baseline")
        self.base = self.git("rev-parse", "HEAD").stdout.strip()
        copied = self.repo / LANE / "conservation.py"
        text = copied.read_text()
        self.assertEqual(text.count(ORIGINAL_BASE), 1)
        copied.write_text(text.replace(ORIGINAL_BASE, self.base))

    def cleanup_fixture(self):
        self.temp.cleanup()
        if self.repo.exists():
            raise AssertionError("scratch fixture was not removed: " + str(self.repo))
        print("fixture_removed=" + str(self.repo), flush=True)

    def git(self, *args):
        return subprocess.run(["git", "-c", "user.name=Fixture", "-c", "user.email=fixture@example.invalid",
                               "-c", "core.hooksPath=/dev/null", *args], cwd=self.repo,
                              env=self.environment, text=True, capture_output=True, check=True)

    def run_script(self, name, *args):
        return subprocess.run([sys.executable, "-B", str(self.repo / LANE / name), *args],
                              cwd=self.repo, env=self.environment, text=True, capture_output=True)

    def test_owner_commit_and_invalid_tree_entries(self):
        lane = self.repo / LANE
        registration = {"module": "Solidity.Yul.Alpha", "documentation": True}
        (lane / "registrations/VY1-Alpha.json").write_text(json.dumps(registration))
        (lane / "imports/ext-VY1-Alpha.txt").write_text("Solidity.Yul.Alpha\n")
        (lane / "body/ext-VY1-Alpha.txt").write_text("/-! Alpha -/\n")
        source = self.repo / "Solidity/Yul/Alpha.lean"
        source.write_text("-- synthetic owner source\n")
        rendered = self.run_script("generate.py", "--render")
        self.assertEqual(rendered.returncode, 0, rendered.stderr)
        (self.repo / TARGET).write_text(rendered.stdout)
        self.git("add", "--", str(TARGET), "Solidity/Yul/Alpha.lean")
        self.git("commit", "-qm", "synthetic owner addition")
        owner_head = self.git("rev-parse", "HEAD").stdout.strip()
        source.unlink()
        matched = self.run_script("conservation.py", "--owner", "VY1", "--after-rev", owner_head)
        self.assertEqual(matched.returncode, 0, matched.stderr + matched.stdout)
        result = json.loads(matched.stdout)
        self.assertEqual(result["status"], "interface_delta_match")
        self.assertEqual(result["source_module_check"], "git_tree_verified")
        self.assertEqual(result["owner_completeness"], "unverified")
        self.git("rm", "--cached", "--", "Solidity/Yul/Alpha.lean")
        self.git("commit", "-qm", "synthetic missing source")
        missing_head = self.git("rev-parse", "HEAD").stdout.strip()
        source.write_text("-- local file does not repair the committed tree\n")
        missing = self.run_script("conservation.py", "--owner", "VY1", "--after-rev", missing_head)
        self.assertEqual(missing.returncode, 2, missing.stdout + missing.stderr)
        source.unlink()
        source.symlink_to("Words.lean")
        self.git("add", "--", "Solidity/Yul/Alpha.lean")
        self.git("commit", "-qm", "synthetic symlink source")
        symlink_head = self.git("rev-parse", "HEAD").stdout.strip()
        invalid = self.run_script("conservation.py", "--owner", "VY1", "--after-rev", symlink_head)
        self.assertEqual(invalid.returncode, 2, invalid.stdout + invalid.stderr)
        self.assertEqual(self.git("remote").stdout, "")


if __name__ == "__main__":
    unittest.main(verbosity=2)
