"""Guard fixed H127 recipes against target, budget and executable substitution.

Synthetic source-plan bytes only; no gate, compiler, tool or worker is executed.
"""
import copy
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import tempfile
import unittest
from unittest import mock

spec = importlib.util.spec_from_file_location("worker_recipe", Path(__file__).with_name("worker-recipe.py"))
m = importlib.util.module_from_spec(spec)
spec.loader.exec_module(m)


class RecipeControls(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.path = Path(self.tmp.name) / "plan.json"
        names = {m.GATE, "lakefile.toml", "lake-manifest.json", "lean-toolchain"}
        names.update(target.replace(".", "/") + ".lean" for target in m.timing.TARGETS)
        names.update(row[2] for row in m.AUDITS)
        self.plan = {"schemaVersion": 1, "status": "prepared-not-executed", "head": "a"*40,
                     "tree": "b"*40, "slowModules": list(m.inputs.plan_module.SLOW),
                     "rootGate": "SoliditySlowExamples", "executionContext": "lane-end",
                     "slowLibraryDeadlineSeconds": 300,
                     "sourceInventory": [{"path": name, "mode": "100644", "bytes": 0,
                                          "sha256": hashlib.sha256(b"").hexdigest()}
                                         for name in sorted(names)]}

    def write(self):
        raw = json.dumps(self.plan).encode()
        self.path.write_bytes(raw)
        return hashlib.sha256(raw).hexdigest()

    def derive(self):
        return m.derive(self.path, self.write())

    def test_exact_serial_denominator_and_retained_audits(self):
        result = self.derive()
        self.assertEqual([row["target"] for row in result["checks"]], list(m.timing.TARGETS))
        self.assertEqual(len(result["checks"]), 16)
        for row in result["checks"]:
            self.assertEqual(row["argv"], ["/bin/bash", m.GATE, "per-file", row["target"].replace(".", "/")+".lean"])
            self.assertIs(row["cachedVerdictAllowed"], False)
        self.assertEqual([row["name"] for row in result["audits"]], [row[0] for row in m.AUDITS])
        for field in ("ciBudgetAuthorized", "sourceSemanticsAuthenticated", "imageToolsAuthenticated", "cacheMappingAuthenticated", "compilerSerializationEnforced", "resourcesAuthenticated", "workerExecutionAuthorized"):
            self.assertIs(result[field], False)

    def test_ambient_and_plan_argv_cannot_become_commands(self):
        before = self.derive()
        self.plan.update({"argv": ["/bin/sh", "-c", "injected"], "environment": {"LD_PRELOAD": "injected"}})
        with mock.patch.dict(os.environ, {"PATH": "/injected", "LEAN_PATH": "/injected", "GITHUB_ACTIONS": "true"}):
            result = self.derive()
        # The pin changes, but all operational recipe data stays fixed.
        before.pop("planSha256"); result.pop("planSha256")
        self.assertEqual(result, before)
        result["environment"]["HOME"] = "changed"
        self.assertNotEqual(m.inputs.ENVIRONMENT["HOME"], "changed")

    def test_exact_external_pin_and_required_source_inventory(self):
        self.write()
        with self.assertRaises(ValueError): m.derive(self.path, "0"*64)
        original = copy.deepcopy(self.plan)
        for kind in ("missing", "duplicate", "path", "pin"):
            self.plan = copy.deepcopy(original)
            if kind == "missing": self.plan["sourceInventory"].pop()
            elif kind == "duplicate": self.plan["sourceInventory"].append(self.plan["sourceInventory"][0])
            elif kind == "path": self.plan["sourceInventory"][0]["path"] = "../injected"
            else: self.plan["sourceInventory"][0]["sha256"] = "not-a-pin"
            with self.subTest(kind=kind), self.assertRaises(ValueError): self.derive()

    def test_target_root_and_declared_budget_mutations_refused(self):
        original = copy.deepcopy(self.plan)
        for kind in ("target", "root", "budget", "bool", "context"):
            self.plan = copy.deepcopy(original)
            if kind == "target": self.plan["slowModules"].reverse()
            elif kind == "root": self.plan["rootGate"] = "Solidity"
            elif kind == "budget": self.plan["slowLibraryDeadlineSeconds"] = 600
            elif kind == "bool": self.plan["slowLibraryDeadlineSeconds"] = True
            else: self.plan["executionContext"] = "ci-injected"
            with self.subTest(kind=kind), self.assertRaises(ValueError): self.derive()

    def test_ci_budget_is_one_library_declaration_not_execution_grant(self):
        self.plan["executionContext"] = "ci"
        self.plan["slowLibraryDeadlineSeconds"] = 600
        result = self.derive()
        self.assertEqual(result["wholeLibraryBudgetNs"], 600_000_000_000)
        self.assertEqual(result["auditInvocationMaximumNs"], 300_000_000_000)
        self.assertEqual(result["timingContext"], "ci-slow-library")
        self.assertIs(result["ciBudgetAuthorized"], False)
        self.assertTrue(all("budget" not in row for row in result["checks"]))


if __name__ == "__main__":
    unittest.main()
