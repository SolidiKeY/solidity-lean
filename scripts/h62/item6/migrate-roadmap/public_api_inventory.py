#!/usr/bin/env python3
"""Consolidate existing H78 API exports; no Lean run or compatibility acceptance.
Usage: public_api_inventory.py /workspace/migrate-roadmap-evidence/NEW_DIRECTORY
All original declarations remain visible, including private/generated names.
"""
import collections
import hashlib
import importlib.util
import json
import re
import subprocess
import sys
from pathlib import Path
sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[4]
EVIDENCE = Path("/workspace/migrate-roadmap-evidence")
BASE = "c6f550e281a7e5affa9a99bc2cdaed556dec00e4"
OLD_CANON = EVIDENCE / "h70/h62-roadmap-old-classify-1793978165171900399/result.json"
NEW_CANON = EVIDENCE / "h70/h62-roadmap-new-classify-1793978204527825213/result.json"
OLD_EXPORT_RESULT = EVIDENCE / "h62-roadmap-old-api-1793975052419846724/result.json"
FIXTURE_RESULT = EVIDENCE / "h62-roadmap-new-fixtures-1793974979117587979/result.json"


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def unique(rows):
    result = {row["name"]: row for row in rows}
    if len(result) != len(rows):
        raise ValueError("duplicate API declaration")
    return result


def binders(expr):
    """Ordered outer forall binders; exact domains retain de Bruijn indices."""
    result = []
    while isinstance(expr, list) and expr and expr[0] == "forall":
        if len(expr) != 4 or expr[1] not in ("explicit", "implicit", "strictImplicit", "instance"):
            raise ValueError("unsupported binder representation")
        result.append(dict(position=len(result), binder_kind=expr[1], domain=expr[2]))
        expr = expr[3]
    return result


def signature(row, canonical=None):
    if row is None:
        return None
    return dict(type_debug=row["type_debug"], universe_parameters=row["universe_parameters"],
                kind="theorem" if row["is_theorem"] else "non_theorem_subkind_not_captured",
                kind_provenance="archived exporter info.isTheorem; full ConstantInfo kind was not captured",
                is_unsafe=row["is_unsafe"],
                normalized_expr=canonical["alpha"] if canonical else None,
                ordered_binders=binders(canonical["alpha"]) if canonical else None,
                binder_provenance="existing canonical Expr export" if canonical else "debug type only; structured binder metadata not exported")


def visibility(name):
    return dict(private_name_encoding=name.startswith("_private."),
                evidence="exported constant name spelling only",
                public_visibility=None, protected_status=None,
                disposition="visibility attributes were not exported; retain declaration without exemption")


def family(name):
    if "noConfusion" in name: return "noConfusion"
    if name.endswith(".recOn"): return "recOn"
    if name.endswith(".casesOn") or "_sparseCasesOn_" in name: return "casesOn"
    if ".match_" in name: return "matcher"
    if "._proof_" in name: return "generated_proof"
    return "other_original_declaration"


def exported_rows(path):
    run = json.loads(path.read_text())
    script = Path(run["command"][-1])
    if (run["exit"] != 0 or run["guard"] is not None or run["inputs_before"] != run["inputs_after"]
        or sha(script) != run["script_sha256"]):
        raise ValueError("unsuccessful or unstable archived API export")
    rows = [json.loads(line.split("ROADMAP_API ", 1)[1])
            for line in path.with_name("build.log").read_text().splitlines()
            if "ROADMAP_API {" in line]
    return run, unique(rows)


def candidate_coverage(block, expected):
    # Lexical coverage only, paired with a successful exact-source run hash below.
    names = set(re.findall(r"^(?:protected +)?(?:abbrev|theorem) +([A-Za-z0-9_.]+)", block, re.MULTILINE))
    actual = {"Solidity.Roadmap.Evm." + name for name in names}
    if actual != set(expected):
        raise ValueError("exact qualified candidate coverage mismatch")


def verify_fixture(run, fixture):
    key = str(fixture.relative_to(ROOT))
    if (run["exit"] != 0 or run["guard"] is not None or
        run["inputs_before"] != run["inputs_after"] or
        run["inputs_after"].get(key) != sha(fixture)):
        raise ValueError("candidate bytes are not bound to a successful fixture run")


def main():
    if len(sys.argv) != 2: raise SystemExit(__doc__)
    out = Path(sys.argv[1]).resolve()
    if not out.is_relative_to(EVIDENCE) or out == EVIDENCE or out.exists():
        raise ValueError("new evidence subdirectory required; never overwrite prior seals")
    spec = importlib.util.spec_from_file_location("classification", Path(__file__).with_name("classify_api.py"))
    classifier = importlib.util.module_from_spec(spec); spec.loader.exec_module(classifier)
    old_run, ca = classifier.load(OLD_CANON); new_run, cb = classifier.load(NEW_CANON)
    old = unique(json.loads((EVIDENCE / "old-api.json").read_text()))
    new = unique(json.loads((EVIDENCE / "new-evm-api.json").read_text()))
    export_run, bound_old = exported_rows(OLD_EXPORT_RESULT)
    _, bound_new = exported_rows(FIXTURE_RESULT)
    if old != bound_old or new != bound_new:
        raise ValueError("saved declaration rows differ from successful export logs")
    delta = json.loads((EVIDENCE / "h70/classification/classification.json").read_text())
    changes = unique(delta["rows"])
    evm = {n for n, row in old.items() if row["module"] == "Solidity.Roadmap.Evm"}
    if len(old) != 2077 or len(new) != 391 or set(ca) != evm or set(cb) != set(new):
        raise ValueError("incomplete or unexpected original export population")
    for canonical_rows, population in ((ca, old), (cb, new)):
        for n, canonical in canonical_rows.items():
            row = population[n]
            if canonical["type_debug"] != row["type_debug"] or canonical["universe_count"] != len(row["universe_parameters"]):
                raise ValueError("signature export mismatch")
    current = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT).decode().strip()
    source_hashes = {}
    for module in {row["module"] for row in old.values()}:
        rel = module.replace(".", "/") + ".lean"
        original = subprocess.check_output(["git", "show", BASE + ":" + rel], cwd=ROOT)
        if (ROOT / rel).read_bytes() != original:
            raise ValueError("original assigned source changed; historical export cannot describe current source")
        source_hashes[rel] = hashlib.sha256(original).hexdigest()
    fixture = ROOT / "tests/h62/item6/migrate-roadmap/HashContainsFixture.lean"
    text = fixture.read_text()
    candidate_names = sorted(evm - set(new))
    candidate_block = text[text.index('@[deprecated Fork.ctorIdx'):text.index('\ntheorem legacy_fork_index')]
    proposal = EVIDENCE / "evm-compatibility-proposal.patch"
    candidate_coverage(candidate_block, candidate_names)
    fixture_run = json.loads(FIXTURE_RESULT.read_text())
    verify_fixture(fixture_run, fixture)
    fixture_script = Path(fixture_run["command"][-1])
    if sha(fixture_script) != fixture_run["script_sha256"]:
        raise ValueError("historical fixture workload script changed")
    records = []
    for n, row in sorted(old.items()):
        observed_new = new.get(n)
        if row["module"] != "Solidity.Roadmap.Evm": status = "new_module_not_exported"
        elif observed_new is None: status = "missing_in_new_evm"
        elif n in changes: status = changes[n]["category"]
        else: status = "debug_type_unchanged"
        records.append(dict(name=n, module=row["module"], family=family(n), visibility=visibility(n),
            old_signature=signature(row, ca.get(n)), new_signature=signature(observed_new, cb.get(n)),
            status=status, shim_signature=None, production_shim_implemented=False,
            candidate=dict(source_block=candidate_block, source=str(fixture), source_sha256=sha(fixture),
                proposed_required_signature=signature(row, ca.get(n)),
                compiled_shim_signature=None,
                boundary="existing fixture compiled under4.35; exact compiled shim signature/visibility not exported; no production shim") if n in candidate_names else None))
    if len(changes) != 64 or {r["name"] for r in records if r["status"] in ("alpha_only", "binder_visibility_only", "structural")} != set(changes):
        raise ValueError("per-name delta accounting mismatch")
    changed = [r for r in records if r["name"] in changes]
    summary = dict(schema=1, original_base=BASE, inspected_head=current,
        declarations=len(records), old_modules=len({r["module"] for r in records}),
        old_evm=len(ca), new_evm=len(cb), new_modules_not_exported=14,
        status_counts=dict(sorted(collections.Counter(r["status"] for r in records).items())),
        family_counts=dict(sorted(collections.Counter(r["family"] for r in records).items())),
        removed_names=candidate_names, added_names=sorted(set(new)-evm),
        changed_names=[r["name"] for r in changed], visibility_complete=False,
        implemented_shims=[], compatibility_accepted=False,
        source_hashes=source_hashes, current_tree_compiled=False,
        export_provenance="export-provenance.json",
        boundary="All2077 original exports retained, including33 private-encoded names. No public/generated/private exemption. Visibility/subkind metadata gaps explicit; no semantic or defeq proof. Missing14newmodule exports are not declaration removals.")
    inputs = [OLD_EXPORT_RESULT, OLD_EXPORT_RESULT.with_name("build.log"), Path(export_run["command"][-1]), FIXTURE_RESULT, FIXTURE_RESULT.with_name("build.log"), fixture_script,
        EVIDENCE / "old-api.json", EVIDENCE / "new-evm-api.json", OLD_CANON, NEW_CANON,
        OLD_CANON.with_name("build.log"), NEW_CANON.with_name("build.log"),
        EVIDENCE / "h70/classification/classification.json", fixture, proposal,
        ROOT / "scripts/h62/item6/migrate-roadmap/classify_api.py", Path(__file__)]
    provenance = {}
    for path, run in ((OLD_CANON, old_run), (NEW_CANON, new_run), (OLD_EXPORT_RESULT, export_run), (FIXTURE_RESULT, fixture_run)):
        provenance[str(path)] = dict(result_sha256=sha(path), compiled_head=run["head"],
            command=run["command"], script_sha256=run["script_sha256"], executed_modules=run["modules"],
            captured_inputs=run["inputs_after"], source_hashes=run["source_hashes"],
            current_input_differences=[k for k, v in run["inputs_after"].items()
                if not (ROOT/k).is_file() or sha(ROOT/k) != v],
            boundary="Historical compiler run. Captured inputs can include unused closure files; exact command/script records actual workload. Not a current-tree compile or closure validation.")
    out.mkdir()
    for name, obj in [("all-original-declarations.json", records), ("evm-64-deltas.json", changed),
                      ("summary.json", summary), ("export-provenance.json", provenance), ("inputs.json", {str(p):sha(p) for p in inputs})]:
        (out / name).write_text(json.dumps(obj, indent=2, sort_keys=True) + "\n")
    (out / "SHA256SUMS").write_text("".join(sha(p)+"  "+str(p)+"\n" for p in sorted(out.iterdir()) if p.is_file()))
    print(json.dumps(summary, indent=2))


if __name__ == "__main__": main()
