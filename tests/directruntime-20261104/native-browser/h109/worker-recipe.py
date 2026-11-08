"""Guard H127 worker recipes against caller-selected commands or missing slow checks.

Derives data only from an externally pinned source plan. No command is run and
no ambient environment is inherited. The controller must still authenticate the
sealed source/image/tools, private cache, compiler serialization, resource and
lifecycle admission before any execution. CI is a declaration, not a grant.
"""
import sys
sys.dont_write_bytecode = True
import importlib.util
from pathlib import Path
import re


def load(name, file):
    spec = importlib.util.spec_from_file_location(name, Path(__file__).with_name(file))
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


inputs = load("recipe_inputs", "input-set.py")
timing = load("recipe_timing", "stage-timing.py")
GATE = "scripts/coord-tools/gate.sh"
# Existing checkpoint trust/inventory checks are retained, with no --write or
# target/caller argv channel. Full TestSuite/corpus gates remain separate jobs.
AUDITS = (
    ("layers", "/usr/bin/node", "scripts/check-layers.mjs"),
    ("trust", "/bin/bash", "scripts/check-trust.sh"),
    ("orphans", "/usr/bin/node", "scripts/check-orphans.mjs"),
    ("roots", "/bin/bash", "scripts/coord-tools/register.sh", "--check"),
    ("fragments", "/bin/bash", "scripts/coord-tools/fragments.sh", "--check"),
    ("doc-paths", "/bin/bash", "scripts/check-doc-paths.sh"),
    ("axiom-pins", "/usr/bin/node", "scripts/check-axiom-pins.mjs"),
    ("private-paths", "/bin/bash", "scripts/check-private-paths.sh"),
    ("evidence-files", "/bin/bash", "scripts/check-evidence-files.sh"),
)


def derive(plan_path, plan_sha256):
    plan = inputs.copy.receipt(plan_path, plan_sha256)
    if (not isinstance(plan, dict) or type(plan.get("schemaVersion")) is not int or
            plan["schemaVersion"] != 1 or plan.get("status") != "prepared-not-executed" or
            plan.get("slowModules") != list(inputs.plan_module.SLOW) or
            plan.get("rootGate") != "SoliditySlowExamples"):
        raise ValueError("exact prepared slow-source plan required")
    for key in ("head", "tree"):
        if not isinstance(plan.get(key), str) or not re.fullmatch("[0-9a-f]{40}", plan[key]):
            raise ValueError("full source head/tree required")
    context = plan.get("executionContext")
    if context not in ("lane-end", "ci"):
        raise ValueError("fixed declared execution context required")
    expected_budget = 600 if context == "ci" else 300
    if (type(plan.get("slowLibraryDeadlineSeconds")) is not int or
            plan["slowLibraryDeadlineSeconds"] != expected_budget):
        raise ValueError("whole-library declared deadline differs from policy")
    entries = plan.get("sourceInventory")
    if not isinstance(entries, list) or not entries:
        raise ValueError("complete source inventory required")
    table = {}
    for entry in entries:
        if not isinstance(entry, dict):
            raise ValueError("invalid source entry")
        name = entry.get("path")
        inputs.safe_name(name)
        if name in table:
            raise ValueError("duplicate source entry")
        if (entry.get("mode") not in ("100644", "100755") or
                type(entry.get("bytes")) is not int or entry["bytes"] < 0 or
                not isinstance(entry.get("sha256"), str) or
                not re.fullmatch("[0-9a-f]{64}", entry["sha256"])):
            raise ValueError("invalid source content pin")
        table[name] = entry
    checks = []
    required = {GATE, "lakefile.toml", "lake-manifest.json", "lean-toolchain"}
    for index, target in enumerate(timing.TARGETS):
        source = target.replace(".", "/") + ".lean"
        required.add(source)
        checks.append({"index": index, "target": target,
                       "argv": ["/bin/bash", GATE, "per-file", source],
                       "logDirectory": "/output/checks/" + str(index),
                       "cachedVerdictAllowed": False})
    audits = []
    for entry in AUDITS:
        name, executable, script, *args = entry
        required.add(script)
        audits.append({"name": name, "argv": [executable, script, *args],
                       "logDirectory": "/output/audits/" + name})
    if not required.issubset(table):
        raise ValueError("required recipe source missing from pinned plan")
    # Derive every argv from reviewed constants. Supplied plan extensions never
    # become options, shell fragments, target names or environment variables.
    return {"status": "fixed-worker-recipe-not-executed", "planSha256": plan_sha256,
            "head": plan["head"], "tree": plan["tree"], "cwd": "/input/source",
            "environment": dict(inputs.ENVIRONMENT), "checks": checks, "audits": audits,
            "directEntryPins": [{"path": name, "sha256": table[name]["sha256"]}
                                for name in sorted(required)],
            "timingContext": "ci-slow-library" if context == "ci" else "lane-end",
            "wholeLibraryBudgetNs": expected_budget * 1_000_000_000,
            "auditInvocationMaximumNs": 300_000_000_000,
            "executionOrder": "Serial slow members then root, followed by serial retained audits; stop on any failure. Dependency preparation and cleanup are separate timed stages.",
            "ciBudgetAuthorized": False, "sourceSemanticsAuthenticated": False,
            "imageToolsAuthenticated": False, "cacheMappingAuthenticated": False,
            "compilerSerializationEnforced": False, "resourcesAuthenticated": False,
            "workerExecutionAuthorized": False,
            "boundary": "Fixed command data and source-plan pins only. Entire source closure and system executables still require authentication. No timer, process, cache mutation, gate, CI identity, cleanup or measurement acceptance."}
