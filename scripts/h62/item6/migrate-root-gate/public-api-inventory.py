#!/usr/bin/env python3
"""Inventory H78 records without treating references, missing bytes or failed controls as API acceptance.

Regression guarded: a partial lane census or an off-VM signature pointer must
never become a complete public generated-API verdict. No Lean or member tool runs.
"""
import argparse
import ast
import hashlib
import io
import difflib
import json
from pathlib import Path
import re
import subprocess
import tarfile
import sys
sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[4]
BASE = "c6f550e281a7e5affa9a99bc2cdaed556dec00e4"
NAME = re.compile(r"(?:Solidity\.|H78Compat\.|_private\.).+")
SIGNATURE_KEYS = {"old_signature", "new_signature", "legacy_signature", "shim_signature", "old_type_repr", "new_type_repr", "replacement_signature"}
KEYWORDS = re.compile(r"H78|generated|public.API|shim|axiom|failed|failure|STOP|timeout", re.I)


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def require(value, message):
    if not value:
        raise ValueError(message)


def validate_members(ledger):
    members = ledger["members"]
    require(len(members) == 28 and len({r["lane"] for r in members}) == 28, "need all28 unique lanes")
    require(all(r.get("integrated") and r.get("commit_available") for r in members), "all28 exact member inputs required")
    return sorted(members, key=lambda r: r["lane"])


def records(value, pointer=""):
    """Retain exact names, including proof/private/debug spelling; infer no visibility."""
    if isinstance(value, dict):
        name = value.get("name")
        if isinstance(name, str) and NAME.fullmatch(name) and SIGNATURE_KEYS.intersection(value):
            yield name, pointer, value
        for key, child in value.items():
            if isinstance(key, str) and NAME.fullmatch(key) and isinstance(child, dict) and SIGNATURE_KEYS.intersection(child):
                yield key, pointer+"/"+key, child
            yield from records(child, pointer+"/"+str(key))
    elif isinstance(value, list):
        for index, child in enumerate(value):
            yield from records(child, pointer+"/"+str(index))


def signature_kind(value):
    if value is None:
        return "not supplied"
    if isinstance(value, dict):
        return "reference or structured record; no literal type inferred"
    if isinstance(value, str):
        return "source-level text; not independently elaborated"
    return "unclassified retained value"


def notes(value, pointer=""):
    if isinstance(value, str) and KEYWORDS.search(value):
        yield {"pointer": pointer, "text": value}
    elif isinstance(value, dict):
        for key, child in value.items():
            yield from notes(child, pointer+"/"+str(key))
    elif isinstance(value, list):
        for index, child in enumerate(value):
            yield from notes(child, pointer+"/"+str(index))


def code_only(text):
    """Root-owned comment/string mask; preserve raw offsets for literal/default checks."""
    out = list(text)
    depth = 0
    string = False
    i = 0
    while i < len(text):
        pair = text[i:i+2]
        if depth:
            if pair == "/-":
                depth += 1; out[i:i+2] = "  "; i += 2; continue
            if pair == "-/":
                depth -= 1; out[i:i+2] = "  "; i += 2; continue
            if text[i] != "\n": out[i] = " "
        elif string:
            if text[i] == "\\" and i+1 < len(text):
                out[i] = " "; out[i+1] = "\n" if text[i+1] == "\n" else " "; i += 2; continue
            if text[i] == '"': string = False
            out[i] = "\n" if text[i] == "\n" else " "
        elif pair == "/-":
            depth = 1; out[i:i+2] = "  "; i += 2; continue
        elif pair == "--":
            stop = text.find("\n", i)
            if stop < 0: stop = len(text)
            out[i:stop] = " "*(stop-i); i = stop; continue
        elif text[i] == '"':
            string = True; out[i] = " "
        i += 1
    require(not depth and not string, "unterminated comment/string")
    return "".join(out)


def source_notes(text):
    """Retain matching prose/template lines, including historical failed controls."""
    return [{"line": i, "text": line} for i, line in enumerate(text.splitlines(), 1) if KEYWORDS.search(line)]


def header_changes(before, after):
    """Keep additive/private headers visible; reject deletion or changed originals."""
    added, missing = [], []
    for tag, a, b, c, d in difflib.SequenceMatcher(a=before, b=after, autojunk=False).get_opcodes():
        if tag in ("delete", "replace"): missing.extend(before[a:b])
        if tag in ("insert", "replace"): added.extend(after[c:d])
    return {"original_headers_preserved": not missing, "missing_or_changed_original_headers": missing,
            "added_headers": added, "entire_header_list_equal": before == after}


def headers(text):
    """Lexical authored headers only; keep raw literals/defaults, not an API exporter."""
    code = code_only(text)
    pattern = re.compile(r"^[ \t]*(?:@\[[^\n]*?\][ \t]*)*(?:(?:private|protected|noncomputable|partial|unsafe|local|scoped)[ \t]+)*(?:def|theorem|lemma|abbrev|opaque|instance|example|inductive|structure|class)\b", re.M)
    result = []
    matches = list(pattern.finditer(code))
    for index, match in enumerate(matches):
        depth = 0
        found = False
        for i in range(match.end(), matches[index+1].start() if index+1 < len(matches) else len(code)):
            c = code[i]
            if depth == 0 and (code.startswith(":=", i) or re.match(r"where\b", code[i:]) or (c == "|" and not code[code.rfind("\n", 0, i)+1:i].strip())):
                result.append(text[match.start():i].strip())
                found = True
                break
            if c in "([{⦃":
                depth += 1
            elif c in ")] }⦄".replace(" ", ""):
                depth -= 1
        require(found, "unsupported authored header; refuse silent skipping")
    return result


def producer_rows(revision):
    paths = ["Solidity/Syntax/Raw.lean", "Solidity/Automation/H28/Context.lean", "Solidity/Roadmap/Contracts.lean", "Solidity/Frontend/Checked/Token.lean", "Solidity/Language/FixedPoint.lean", "Solidity/Hash/CollisionBound.lean", "Solidity/Precompiles/Bls12381.lean", "Bridge/SolidityBridge.lean"]
    result = []
    for path in paths:
        original = subprocess.check_output(["git", "show", BASE+":"+path], cwd=ROOT)
        current = subprocess.check_output(["git", "show", revision+":"+path], cwd=ROOT)
        require((ROOT/path).read_bytes() == current, "producer file differs from recorded revision")
        before, after = headers(original.decode()), headers(current.decode())
        delta = header_changes(before, after)
        if path in paths[:3]:
            require(delta["original_headers_preserved"], "authored lexical headers drift: "+path)
        row = {"path": path, "producer_head": revision, "source_last_commit": subprocess.check_output(["git", "log", "-1", "--format=%H", revision, "--", path], cwd=ROOT, text=True).strip(),
               "base_sha256": sha(original), "source_sha256": sha(current), "whole_file_unchanged": current == original,
               "authored_lexical_headers_unchanged": len(before) if delta["original_headers_preserved"] else None,
               "header_delta": delta, "header_evidence_sha256": sha(json.dumps(before, ensure_ascii=False).encode()),
               "generated_API_or_axiom_fidelity_established": False, "Lean_run": False}
        if path.endswith("Contracts.lean"):
            guard = "/-- info: 'Solidity.Roadmap.PublicCorrectness.transfer' does not depend on any axioms -/\n#guard_msgs in #print axioms Solidity.Roadmap.PublicCorrectness.transfer"
            require(guard in current.decode() and current == original, "Contracts exact source/empty guard changed")
            row.update({"expected_transfer_axioms": [], "guard_sha256": sha(guard.encode()), "repair_status": "not repaired; exact original statement/body/empty guard retained"})
        elif path.endswith("Context.lean"):
            require(current == original, "Context original source changed")
            row["audit_status"] = "Classical.choice growth remains unresolved despite unchanged source; original failed ContextControls retained"
        elif path == "Solidity/Syntax/Raw.lean":
            row["audit_status"] = "current pinned-source snapshot; archived v4.35 compatibility and historical637 declaration axiom-growth/generated API audits remain unresolved"
        elif path.endswith("Token.lean"):
            row["audit_status"] = "original source unchanged; Token candidate remains unapplied/unaccepted"
        elif path.startswith("Bridge/"):
            row["audit_status"] = "unchanged import root; prior Bridge resource-stop and compatibility/full gates remain unfinished"
        else:
            row["audit_status"] = "retained scoped producer checks reported; no successor full API/axiom/consumer acceptance"
        result.append(row)
    return result


def link_legacy_names(catalogue):
    """Guard against growing a legacy bucket while traversing that same bucket."""
    snapshot = [row for evidence in catalogue.values() for row in evidence]
    for row in snapshot:
        legacy = row["record"].get("legacy_public_name")
        if legacy:
            catalogue.setdefault(legacy, []).append({**row, "status": "legacy name obligation; separate-namespace candidate is not an installed shim"})


def require_production_inputs(expected, inputs):
    """Guard against a complete-lane label silently omitting assigned production files."""
    require(set(expected) <= set(inputs), "missing assigned production input")


def archived_inputs(root):
    """Read H44 bulk only after archive identity and member counts verify."""
    manifest_path = root/"scripts/h62/item6/migrate-root-gate/bulk-manifest.json"
    manifest = json.loads(manifest_path.read_text())
    archive = Path(manifest["archive"])
    raw = archive.read_bytes()
    require(len(raw) == manifest["size_bytes"] and sha(raw) == manifest["sha256"],
            "H44 bulk archive size/SHA256 mismatch")
    result = {}
    with tarfile.open(fileobj=io.BytesIO(raw), mode="r:gz") as stream:
        for member in stream.getmembers():
            path = Path(member.name)
            require(member.isfile() and not path.is_absolute() and ".." not in path.parts,
                    "unsupported H44 archive member")
            require(member.name not in result, "duplicate H44 archive member")
            result[member.name] = stream.extractfile(member).read()
    require(len(result) == manifest["file_count"] and
            sum(map(len, result.values())) == manifest["uncompressed_bytes"],
            "H44 bulk member count/size mismatch")
    return result


def member_ancestry(root, historical_head, revision):
    """Rebasing need not retain historical member ancestry in the current tree.

    Require the exact authenticated object, but report current ancestry separately
    from the historical intake ledger. This never certifies current source fidelity.
    """
    exists = subprocess.run(["git", "cat-file", "-e", historical_head+"^{commit}"],
                            cwd=root, capture_output=True)
    require(exists.returncode == 0, "missing exact historical member commit: "+historical_head)
    relation = subprocess.run(["git", "merge-base", "--is-ancestor", historical_head, revision],
                              cwd=root, capture_output=True)
    require(relation.returncode in (0, 1), "cannot inspect current member ancestry")
    return {"exact_historical_head_object_available": True,
            "historical_head_is_current_ancestor": relation.returncode == 0,
            "provenance_boundary": "Historical integration ledger retained; current source bytes indexed independently. Ancestry or object availability is not current API/axiom acceptance."}


def reconcile_source_shims(historical, source):
    """Historical installed aliases may disappear after a toolchain restoration.

    Observe explicit source only; generated legacy names require compiler exports.
    Comments/strings cannot establish that an alias is currently installed.
    """
    code = " ".join(code_only(source).split())
    rows = []
    for record in historical:
        short = record["name"].split(".")[-2]
        expected = f"protected abbrev {short}.toCtorIdx : type_of% {short}.ctorIdx := {short}.ctorIdx"
        present = expected in code
        rows.append({"name": record["name"], "historical_record": record,
                     "explicit_source_alias_present": present,
                     "status": ("explicit source alias observed; exported API fidelity pending" if present else
                                "historical alias absent from current source; generated API availability unverified"),
                     "API_axiom_acceptance": False})
    return rows


def build(root, ledger, revision, bulk=None):
    bulk = archived_inputs(root) if bulk is None else bulk
    members = validate_members(ledger)
    lane_rows, names = [], {}
    ownership_path = Path("/workspace/h62-coordinator-inputs/ownership.json")
    ownership = json.loads(ownership_path.read_text())
    owners = {r["owner"]: r for r in ownership["items"] if "owner" in r}
    for member in members:
        ancestry = member_ancestry(root, member["head"], revision)
        lane = member["lane"].split("/")[-1]
        patterns = [s.strip() for s in owners[member["lane"]]["writeScope"].split(";")]
        production_patterns = [s for s in patterns if s.startswith(("Solidity/", "Bridge/"))]
        production = subprocess.check_output(["git", "ls-tree", "-r", "--name-only", BASE, "--", *production_patterns], cwd=root, text=True).splitlines()
        require(production, "missing frozen production scope: "+lane)
        paths = subprocess.check_output(["git", "ls-files", "--", "tests/h62/item6/"+lane, "scripts/h62/item6/"+lane, "docs/feature-work/h62-6-"+lane+".md", *production_patterns], cwd=root, text=True).splitlines()
        require(paths, "missing lane source inputs: "+lane)
        require_production_inputs(production, paths)
        tracked_paths = set(paths)
        archived_paths = {p for p in bulk if p.startswith(("tests/h62/item6/"+lane+"/", "scripts/h62/item6/"+lane+"/"))}
        inputs, lane_notes, references = [], [], set()
        for path in sorted(tracked_paths | archived_paths):
            raw = (root/path).read_bytes() if path in tracked_paths else bulk[path]
            api_related = bool(re.search(r"api|interface|shim|retirement|handoff", path, re.I)) or path.startswith("docs/")
            inputs.append({"path": path, "sha256": sha(raw), "api_related": api_related, "production_source": path in production, "tracked_current_source": path in tracked_paths, "verified_H44_archived_input": path not in tracked_paths})
            if not api_related or re.search(r"original-(?:assignment|frozen|rendered|scope)|scope-manifest|exact-scope|ORIGINAL-", path, re.I):
                continue
            value = None
            if path.endswith(".json"):
                value = json.loads(raw)
            elif path.endswith(".py"):
                # Read literal record dictionaries, never execute candidate generators.
                for node in ast.walk(ast.parse(raw.decode())):
                    if isinstance(node, ast.Dict):
                        row = {k.value: v.value for k, v in zip(node.keys, node.values) if isinstance(k, ast.Constant) and isinstance(k.value, str) and isinstance(v, ast.Constant)}
                        if isinstance(row.get("name"), str) and SIGNATURE_KEYS.intersection(row):
                            for name, pointer, record in records(row):
                                names.setdefault(name, []).append({"lane": lane, "path": path, "pointer": "AST literal", "record": record, "signature_kinds": {k: signature_kind(record[k]) for k in SIGNATURE_KEYS.intersection(record)}, "status": "candidate generator literal; not an installed shim"})
            if value is not None:
                for name, pointer, record in records(value):
                    names.setdefault(name, []).append({"lane": lane, "path": path, "pointer": pointer, "record": record, "signature_kinds": {k: signature_kind(record[k]) for k in SIGNATURE_KEYS.intersection(record)}, "status": "retained source record; fidelity not accepted"})
                lane_notes.extend({"path": path, **n} for n in notes(value))
            text = raw.decode(errors="strict")
            if not path.endswith(".json"):
                lane_notes.extend({"path": path, "kind": "source/prose/template line; not a runtime verdict", **n} for n in source_notes(text))
            for match in re.finditer(r"/workspace/[^\s\"'<>]+", text):
                reference = match.group(0).rstrip(",;.)")
                if re.search(r"api|interface|signature|axiom|shim", reference, re.I):
                    references.add(reference)
        lane_rows.append({"lane": member["lane"], "final_member_head": member["head"], **ancestry, "source_inputs": inputs,
                          "frozen_production_paths_indexed": len(production),
                          "retained_API_failure_and_hold_notes": lane_notes,
                          "referenced_export_paths": [{"path": p, "exists_on_successor": Path(p).exists(), "bytes_or_elaboration_verified": False} for p in sorted(references)],
                          "complete_public_generated_API_fidelity": False,
                          "record_extraction_limits": "JSON signature rows and constant Python dictionaries only; dynamic name loops, prose signatures and compiler exports are not synthesized. All tracked input hashes retained; failure notes cover selected API-related JSON/prose/template inputs only.",
                          "remaining": "Exact old/new exports, visibility, universe/binder/attribute provenance, all public generated families and successful controls require reconciliation; no absent bytes regenerated or accepted here."})
    requirements_path = root/"scripts/h62/item6/migrate-root-gate/h78-public-api-requirements.json"
    requirements_raw = bulk[str(requirements_path.relative_to(root))]
    requirements = json.loads(requirements_raw)
    for record in requirements["known_obligations"]:
        names.setdefault(record["name"], []).append({"lane": "migrate-root-gate", "path": str(requirements_path.relative_to(root)), "record": record, "status": "existing explicit obligation; null signatures remain unresolved"})
    # A separate-namespace prototype does not restore its legacy public name.
    link_legacy_names(names)
    shim_source_path = "Solidity/SortCheck/Annotations.lean"
    shim_source = (root/shim_source_path).read_text()
    shim_rows = reconcile_source_shims(ledger["inherited_implemented_shims"], shim_source)
    for row in shim_rows:
        names.setdefault(row["name"], []).append({"lane": "migrate-sortcheck", "path": shim_source_path,
                                                "record": row["historical_record"], "status": row["status"]})
    for lane_row in lane_rows:
        short = lane_row["lane"].split("/")[-1]
        lane_row["named_signature_record_names"] = sorted(n for n, rows in names.items() if any(row["lane"] == short for row in rows))
        lane_row["historical_failure_or_STOP_notes"] = sum(bool(re.search(r"failed|failure|STOP|timeout", n["text"], re.I)) for n in lane_row["retained_API_failure_and_hold_notes"])
    installed = [row for row in shim_rows if row["explicit_source_alias_present"]]
    return {"schema_version": 1, "base": BASE, "producer_head": revision, "generator_sha256": sha(Path(__file__).read_bytes()),
            "requirements_source_sha256": sha(requirements_raw),
            "bulk_manifest_sha256": sha((root/"scripts/h62/item6/migrate-root-gate/bulk-manifest.json").read_bytes()),
            "frozen_ownership_source_sha256": sha(ownership_path.read_bytes()),
            "integrated_lane_input_index_complete": True, "lane_count": len(lane_rows), "lanes": lane_rows,
            "named_signature_records": [{"name": n, "visibility": "not inferred; exact exported visibility still required", "evidence": rows} for n, rows in sorted(names.items())],
            "installed_source_shims": installed, "historical_source_shims": shim_rows,
            "shim_source_sha256": sha(shim_source.encode()),
            "shim_source_toolchain": (root/"lean-toolchain").read_text().strip(),
            "producer_files": producer_rows(revision),
            "generated_public_API_inventory_complete": False, "API_axiom_acceptance": False,
            "missing_raw_bytes": "No missing old export is synthesized or accepted; H86 regeneration limitation retained. No Lean or unchanged known-STOP rerun.",
            "boundary": "Complete current production/tracked-input and verified H44 archived-input index with structured-record and prose-note extraction, not a complete elaborated public API census. Do not infer absence, visibility or fidelity from names, source headers, old unions, record counts, missing raw bytes or historical failed controls."}


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    revision = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip()
    bulk = archived_inputs(ROOT)
    ledger = json.loads(bulk["scripts/h62/item6/migrate-root-gate/h82b-final-intake.json"])
    result = build(ROOT, ledger, revision, bulk)
    with args.output.open("x") as stream:
        json.dump(result, stream, indent=2, sort_keys=True)
        stream.write("\n")
    print(json.dumps({"lanes": result["lane_count"], "named_records": len(result["named_signature_records"]), "installed_source_shims": len(result["installed_source_shims"]), "fidelity_accepted": False}))
