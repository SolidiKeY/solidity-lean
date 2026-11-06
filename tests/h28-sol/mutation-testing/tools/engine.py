"""Committed-manifest mutation engine. Assignment acceptance is separate."""
import fcntl
import hashlib
import io
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import tarfile
import tempfile
import bulk_inputs
import bounded
import checked
from runner import mutate, relative, digest

BASE = "6f3eedf0788ee1f8a3bcf230558c712ecdca04d5"
# Published origin/master 6cf853ae is included in the owned integration head.
# Only the delivery/write-scope boundary advances; BASE remains the immutable
# semantic/cache trust pin. No input hash, theorem or proof budget changes.
DELIVERY_BASE = "6cf853aea0417155aca29ddb91f1767d3f3a3cc4"
BRANCH = "codex/solidity-h28-sol-20261104/mutation-testing"
PREFIX = "tests/h28-sol/mutation-testing/"
KINDS = {"mutant", "negative-control", "known-kill", "equivalent-control", "invalid-control", "runner-survivor-control"}
SCORED = {"mutant", "negative-control"}


class CaseStop(Exception):
    def __init__(self, status, reason):
        self.status = status
        super().__init__(reason)


def sha(path): return digest(path.read_bytes())

def valid_id(value):
    return isinstance(value, str) and re.fullmatch(r"[a-z0-9][a-z0-9.-]*", value) is not None


def save(path, value):
    temp = path.with_suffix(path.suffix + ".tmp")
    temp.write_text(json.dumps(value, indent=2) + "\n")
    temp.replace(path)


def artifact_path(source):
    path = relative(source)
    if path.suffix != ".lean":
        raise ValueError("compiled source must be Lean")
    return ".lake/build/lib/lean/" + str(path.with_suffix(".olean"))


def retain_artifact(tree, source, evidence, phase):
    """Retain only a fresh, successful compile; never use this as a proof gate."""
    origin = tree / artifact_path(source)
    if origin.is_symlink() or not origin.is_file() or origin.stat().st_size == 0:
        raise ValueError("successful check lacks a regular nonempty compiled artifact")
    destination = evidence / "compiled-artifacts" / phase / Path(source).with_suffix(".olean")
    destination.parent.mkdir(parents=True, exist_ok=True)
    if destination.exists():
        raise ValueError("refuse to overwrite retained compiled artifact")
    shutil.copyfile(origin, destination)
    return {"path": str(destination.relative_to(evidence)), "sha256": sha(destination),
            "bytes": destination.stat().st_size, "source": source,
            "source_sha256": sha(tree / source), "phase": phase,
            "boundary": "Compiled Lean output, isolated by normal/mutant phase; not a Lake transport receipt"}


def snapshot(tree):
    result = {}
    for directory, dirs, files in os.walk(tree):
        if Path(directory) == tree:
            dirs[:] = [name for name in dirs if name != ".lake"]
        for name in files:
            path = Path(directory) / name
            result[str(path.relative_to(tree))] = "symlink:" + os.readlink(path) if path.is_symlink() else sha(path)
    return result


def graph_of(repo, cache):
    modules = set(cache["ordered_modules"])
    return {m: {dep for line in (repo / (m.replace(".", "/") + ".lean")).read_text().splitlines()
                if line.startswith("import ") for dep in line.split()[1:] if dep in modules} for m in modules}


def forbidden_modules(graph, target):
    blocked = {target}
    while True:
        more = {m for m, deps in graph.items() if deps & blocked}
        if more <= blocked: return blocked
        blocked |= more


def committed_source(repo, path):
    return bulk_inputs.read(repo, path)


def validate_write_scope(repo):
    # The coordinator explicitly authorized this delivery integration. It does not
    # change BASE, the immutable semantic/cache inputs checked below.
    subprocess.run(["git", "merge-base", "--is-ancestor", BASE, DELIVERY_BASE], cwd=repo, check=True)
    subprocess.run(["git", "merge-base", "--is-ancestor", DELIVERY_BASE, "HEAD"], cwd=repo, check=True)
    changed = subprocess.check_output(["git", "diff", "--name-only", "--no-renames", DELIVERY_BASE, "HEAD"], cwd=repo, text=True).splitlines()
    if any(not p.startswith(PREFIX) and p != "docs/feature-work/h28-mutation-testing.md" for p in changed):
        raise ValueError("branch writes outside exclusive scope after authorized delivery base")


def validate(repo, manifest, path):
    if manifest.get("schema") != 2 or manifest.get("state") != "frozen" or manifest.get("base") != BASE:
        raise ValueError("schema-2 frozen manifest at the exact assigned base required")
    if manifest.get("scope") not in ("pilot", "full"):
        raise ValueError("manifest scope must be explicit")
    path = path.resolve()
    rel = path.relative_to(repo)
    if not str(rel).startswith(PREFIX): raise ValueError("manifest outside owned scope")
    if subprocess.check_output(["git", "status", "--porcelain"], cwd=repo):
        raise ValueError("commit all inputs before executing")
    if subprocess.check_output(["git", "branch", "--show-current"], cwd=repo, text=True).strip() != BRANCH:
        raise ValueError("wrong assigned branch")
    subprocess.run(["git", "merge-base", "--is-ancestor", BASE, "HEAD"], cwd=repo, check=True)
    blob = committed_source(repo, path)
    if json.loads(blob) != manifest:
        raise ValueError("manifest is not the committed input")
    validate_write_scope(repo)
    cases = manifest["cases"]
    ids = [c["id"] for c in cases]
    if not cases or len(set(ids)) != len(ids) or any(not valid_id(ident) for ident in ids):
        raise ValueError("empty/duplicate/unsafe case IDs")
    inventory_path = repo / relative(manifest["inventory"])
    committed_source(repo, inventory_path)
    if sha(inventory_path) != manifest["inventory_sha256"]: raise ValueError("inventory identity mismatch")
    inventory_data = json.loads(inventory_path.read_text())
    if manifest["production_inputs"] != inventory_data["production_inputs"]:
        raise ValueError("production input set differs from pinned inventory")
    inventory = {row["id"]: row for row in inventory_data["inventory"]}
    edits = {}
    for case in cases:
        if case["kind"] not in KINDS: raise ValueError("unknown case role")
        target = relative(case["target"])
        if not str(target).endswith(".lean") or str(target) not in manifest["production_inputs"]:
            raise ValueError("target not a pinned Lean production input")
        original = subprocess.check_output(["git", "show", BASE + ":" + str(target)], cwd=repo)
        if digest(original) != case["target_sha256"] or digest(original) != manifest["production_inputs"][str(target)]:
            raise ValueError("target is not exact frozen source")
        row = inventory[case["constructor_id"]]
        span = "".join(original.decode().splitlines(True)[row["line_start"] - 1:row["line_end"]])
        if row["file"] != str(target) or case["old"] not in span:
            raise ValueError("edit not attributed to declared constructor span")
        old, new = case["old"].encode(), case["new"].encode()
        if not old or old == new or original.count(old) != 1:
            raise ValueError("edit must replace exactly one unique span")
        after = digest(original.replace(old, new, 1))
        if after != case["mutant_sha256"]: raise ValueError("mutant identity mismatch")
        edits[case["id"]] = after
        required = ["oracle"] + (["equivalence"] if case["kind"] == "equivalent-control" else
                                [] if case["kind"] == "invalid-control" else ["witness"])
        if case["kind"] == "runner-survivor-control": required += ["regression"]
        for field in required:
            source = relative(case[field])
            if str(source.parent) != PREFIX.rstrip("/") + "/oracles": raise ValueError("oracle outside owned oracle directory")
            actual_source = repo / source
            if source.suffix != ".lean" or actual_source.is_symlink() or not actual_source.resolve().is_relative_to(repo):
                raise ValueError("oracle must be a regular owned Lean file")
            committed_source(repo, actual_source)
            if sha(repo / source) != case[field + "_sha256"]: raise ValueError("oracle source drift")
            code = checked.oracle_code((repo / source).read_text())
            if re.search(r"\b(axiom|sorry|admit|unsafe|native_decide|maxHeartbeats|elab|macro|run_cmd)\b|#eval", code):
                raise ValueError("oracle trust/execution shortcut")
            declarations = case[field + "_declarations"]
            if len(set(declarations)) != len(declarations) or set(declarations) != set(case[field + "_signature_sha256"]):
                raise ValueError("missing/duplicate signature freeze")
            roles = {d.rsplit(".", 1)[1] for d in declarations}
            needed = {"source_link_all", "equivalence_all", "input_inhabited"} if field == "equivalence" else {"source_link", "input_inhabited", "checked_kill"} if field == "witness" else {"source_link", "input_inhabited"}
            if not needed <= roles: raise ValueError("missing mandatory proof declarations")
    by_id = {c["id"]: c for c in cases}
    for case in cases:
        if case["kind"] == "known-kill" and any(edits[case["id"]] == edits[c["id"]] for c in cases if c["kind"] in SCORED):
            raise ValueError("known-kill control duplicates a scored edit")
        if case["kind"] == "runner-survivor-control":
            parent = by_id[case["control_of"]]
            if parent["kind"] not in SCORED or edits[parent["id"]] != edits[case["id"]]:
                raise ValueError("survivor self-test must transparently duplicate its declared scored edit")
    if not any(c["kind"] == "known-kill" for c in cases): raise ValueError("independent known-kill control required")
    for source, expected in manifest["production_inputs"].items():
        frozen = subprocess.check_output(["git", "show", BASE + ":" + str(relative(source))], cwd=repo)
        if digest(frozen) != expected or sha(repo / source) != expected: raise ValueError("production input drift")
    cache_path = repo / relative(manifest["cache_manifest"])
    committed_source(repo, cache_path)
    if sha(cache_path) != manifest["cache_manifest_sha256"]: raise ValueError("cache manifest drift")
    cache = json.loads(cache_path.read_text())
    if not cache["complete"] or cache["base"] != BASE: raise ValueError("incomplete/wrong-base cache")
    for source, expected in cache["source_sha256"].items():
        frozen = subprocess.check_output(["git", "show", BASE + ":" + source], cwd=repo)
        if digest(frozen) != expected or sha(repo / source) != expected: raise ValueError("cache source provenance mismatch")
    cache_root = Path(manifest["cache_root"]).resolve() / ".lake/build/lib/lean"
    for artifact, expected in cache["artifact_sha256"].items():
        if sha(cache_root / relative(artifact)) != expected: raise ValueError("cache artifact drift")
    if sha(bounded.RUNTIME / "bin/lean") != manifest["runtime_lean_sha256"] or sha(Path("/workspace/h28-runtime/measure")) != manifest["measurement_binary_sha256"]:
        raise ValueError("runtime/instrumentation identity drift")
    return cache, cache_root, graph_of(repo, cache)


def primary_outcome(rejected, witness_verified, equivalence_verified=False):
    if equivalence_verified:
        return "error" if rejected else "equivalent"
    if rejected:
        return "killed" if witness_verified else "error"
    return "surviving"


def summarize(records, cases):
    by_id = {r["id"]: r for r in records}
    if len(by_id) != len(records): raise ValueError("duplicate result ID")
    expected_ids = {c["id"] for c in cases}
    if len(expected_ids) != len(cases) or set(by_id) - expected_ids: raise ValueError("duplicate manifest or undeclared result ID")
    unrun = [c["id"] for c in cases if by_id.get(c["id"], {}).get("status", "unrun") == "unrun"]
    known = [c for c in cases if c["kind"] == "known-kill"]
    control_ok = bool(known) and all(by_id.get(c["id"], {}).get("status") == "killed" and
                                  by_id[c["id"]].get("witness_verified") and by_id[c["id"]].get("baseline_passed") for c in known)
    eligible = [c for c in cases if c["kind"] in SCORED and by_id.get(c["id"], {}).get("baseline_passed") and
                by_id[c["id"]]["status"] in ("killed", "surviving") and
                (by_id[c["id"]]["status"] != "killed" or by_id[c["id"]].get("witness_verified"))]
    denominator = [c["id"] for c in eligible]
    killed = sum(by_id[ident]["status"] == "killed" for ident in denominator)
    def verified(record):
        if not record.get("baseline_passed"): return False
        status = record["status"]
        if status == "killed": return bool(record.get("witness_verified"))
        if status == "equivalent": return bool(record.get("equivalence_verified"))
        if status == "surviving": return bool(record.get("witness_verified") and record.get("regression_verified"))
        if status == "invalid-compilation": return bool(record.get("invalid_compilation_verified"))
        return False
    healthy = not unrun and control_ok and all(verified(by_id.get(c["id"], {})) for c in cases)
    expected_controls = {"known-kill": "killed", "equivalent-control": "equivalent", "invalid-control": "invalid-compilation", "runner-survivor-control": "surviving"}
    controls_match = all(by_id.get(c["id"], {}).get("status") == expected_controls[c["kind"]] for c in cases if c["kind"] in expected_controls)
    return {"unrun": unrun, "known_kill_controls_pass": control_ok, "denominator_ids": denominator,
            "denominator": len(denominator), "killed": killed,
            "score": killed / len(denominator) if healthy and controls_match and denominator else None,
            "excluded_from_score": [{"id": c["id"], "role": c["kind"], "status": by_id.get(c["id"], {}).get("status", "unrun")} for c in cases if c["id"] not in denominator],
            "runner_cases_complete": healthy and controls_match and all(r.get("regression_verified") for r in records if r["status"] == "surviving"),
            "scope_complete": False}


def run_frozen(repo, manifest, out, manifest_path):
    repo, out = repo.resolve(), out.resolve()
    if out.is_relative_to(repo): raise ValueError("run evidence must be outside checkout to preserve clean input provenance")
    lock_path = Path("/tmp/solidity-lean-feature-groups-20261025/writer.lock")
    lock_path.parent.mkdir(parents=True, exist_ok=True)
    with lock_path.open("a") as lock:
        fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        cache_data, cache, graph = validate(repo, manifest, manifest_path)
        head = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=repo, text=True).strip()
        archive = subprocess.check_output(["git", "archive", head], cwd=repo)
        out.mkdir(parents=True, exist_ok=False)
        (out / "manifest.json").write_bytes(manifest_path.read_bytes())
        result = {"run_head": head, "base": BASE, "scope": manifest["scope"], "archive_sha256": digest(archive),
                  "manifest_sha256": sha(manifest_path), "records": [{"id": c["id"], "kind": c["kind"], "status": "unrun", "checks": {}, "validation": {}} for c in manifest["cases"]]}
        def persist(record):
            save(out / record["id"] / "result.json", record)
            save(out / "result.json", {**result, **summarize(result["records"], manifest["cases"])})
        for case, record in zip(manifest["cases"], result["records"], strict=True):
            ev = out / case["id"]
            ev.mkdir()
            record.update(baseline_passed=False, witness_verified=False, regression_verified=False)
            persist(record)
            target_module = case["target"][:-5].replace("/", ".")
            blocked = forbidden_modules(graph, target_module)
            record["cache_excluded_modules"] = sorted(blocked)
            try:
                if target_module not in graph: raise CaseStop("error", "target dependency cache is not prepared")
                for phase in ("baseline", "mutant"):
                    with tempfile.TemporaryDirectory(prefix="h28-run-" + phase + "-", dir="/workspace/h28-runtime") as scratch:
                        tree = Path(scratch)
                        with tarfile.open(fileobj=io.BytesIO(archive)) as tar: tar.extractall(tree, filter="data")
                        expected_sources = snapshot(tree)
                        for module in cache_data["ordered_modules"]:
                            if module in blocked: continue
                            artifact = module.replace(".", "/") + ".olean"
                            dest = tree / ".lake/build/lib/lean" / artifact
                            dest.parent.mkdir(parents=True, exist_ok=True)
                            dest.symlink_to(Path("/cache") / artifact)
                        if phase == "mutant":
                            change = mutate(tree, case)
                            (ev / "mutant.patch").write_text(change.pop("diff"))
                            record["mutation"] = change
                            if change["after_sha256"] != case["mutant_sha256"]: raise CaseStop("error", "actual mutant differs from frozen identity")
                            expected_sources[case["target"]] = change["after_sha256"]
                        def check(label, source, artifact=None):
                            record["phase"] = phase + "-" + label
                            persist(record)
                            log = ev / (record["phase"] + ".log")
                            if artifact is None:
                                artifact = artifact_path(source)
                            try:
                                res = bounded.lean(tree, source, log, output=artifact, cache=cache)
                            except bounded.CleanupError as exc:
                                record["checks"][record["phase"]] = exc.record
                                persist(record)
                                raise
                            record["checks"][record["phase"]] = res
                            persist(record)
                            if snapshot(tree) != expected_sources: raise CaseStop("error", "source inventory changed during a check")
                            if res["kind"] == "timeout": raise CaseStop("timeout", record["phase"])
                            if res["kind"] != "exit": raise CaseStop("error", "infrastructure failure at " + record["phase"])
                            if res["runtime_lean_sha256"] != manifest["runtime_lean_sha256"] or res["measurement_binary_sha256"] != manifest["measurement_binary_sha256"]:
                                raise CaseStop("error", "runtime changed during run")
                            return res, log.read_text()
                        def certify(field):
                            res, text = check(field, case[field])
                            cert = checked.success(res, text, case[field + "_declarations"])
                            cert["all_owned_axioms"] = checked.all_owned_axioms(res, text, (tree / case[field]).read_text())
                            actual = {name: digest(sig.encode()) for name, sig in cert["signatures"].items()}
                            if actual != case[field + "_signature_sha256"]: raise CaseStop("error", "proof signature drift")
                            if field == "witness":
                                sig = next(sig for name, sig in cert["signatures"].items() if name.endswith(".checked_kill"))
                                if not re.search(r":\s*¬\s*Solidity\.Premise\.Sound\b", sig): raise CaseStop("error", "witness is not an unconditional semantic counterexample")
                            record["validation"][record["phase"]] = cert
                            record.setdefault("compiled_artifacts", {})[record["phase"]] = retain_artifact(tree, case[field], ev, record["phase"])
                            persist(record)
                            return cert
                        def reject(field):
                            res, text = check(field, case[field])
                            lines = [i for i, line in enumerate((tree / case[field]).read_text().splitlines(), 1) if line.startswith("theorem source_link :")]
                            if len(lines) != 1: raise CaseStop("error", "expected one concrete source-link theorem")
                            cert = checked.source_link_rejection(res, text, case[field], lines[0])
                            record["validation"][record["phase"]] = cert
                            persist(record)
                        artifact = ".lake/build/lib/lean/" + target_module.replace(".", "/") + ".olean"
                        res, text = check("compile", case["target"], artifact)
                        if res["exit"] != 0:
                            errors = [m for m in checked.messages(text) if m["severity"] == "error"]
                            fatal = re.search(r"out of memory|maximum.*heartbeats|maximum.*recursion|timed out|stack overflow", text, re.I)
                            if phase == "mutant" and res["exit"] == 1 and errors and not fatal and all(m["fileName"] == case["target"] for m in errors):
                                record["status"] = "invalid-compilation"
                                record["invalid_compilation_verified"] = True
                                break
                            raise CaseStop("error", "normal compilation or resource/budget failure")
                        checked.success(res, text)
                        record.setdefault("compiled_artifacts", {})[record["phase"]] = retain_artifact(tree, case["target"], ev, record["phase"])
                        persist(record)
                        if phase == "baseline":
                            certify("oracle")
                            if case["kind"] == "runner-survivor-control": certify("regression")
                            if case["kind"] == "equivalent-control": certify("equivalence")
                            elif case["kind"] != "invalid-control": reject("witness")
                            record["baseline_passed"] = True
                            persist(record)
                        else:
                            # Keep the actual primary oracle result. A stronger
                            # regression must never relabel a survivor as killed.
                            oracle_res, oracle_text = check("oracle", case["oracle"])
                            rejected = oracle_res["exit"] != 0
                            if rejected:
                                line = next(i for i, ln in enumerate((tree / case["oracle"]).read_text().splitlines(), 1) if ln.startswith("theorem source_link :"))
                                record["validation"][record["phase"]] = checked.source_link_rejection(oracle_res, oracle_text, case["oracle"], line)
                            else:
                                cert = checked.success(oracle_res, oracle_text, case["oracle_declarations"])
                                cert["all_owned_axioms"] = checked.all_owned_axioms(oracle_res, oracle_text, (tree / case["oracle"]).read_text())
                                if {n: digest(s.encode()) for n, s in cert["signatures"].items()} != case["oracle_signature_sha256"]: raise CaseStop("error", "oracle signature drift")
                                record["validation"][record["phase"]] = cert
                                record.setdefault("compiled_artifacts", {})[record["phase"]] = retain_artifact(tree, case["oracle"], ev, record["phase"])
                            if case["kind"] == "equivalent-control":
                                certify("equivalence")
                                record["equivalence_verified"] = True
                            elif case["kind"] != "invalid-control":
                                certify("witness")
                                record["witness_verified"] = True
                            if not rejected and record["witness_verified"]:
                                record["regression_verified"] = True
                                record["survivor_regression"] = "checked concrete semantic witness; primary outcome remains surviving"
                            if case["kind"] == "runner-survivor-control":
                                reject("regression")
                                record["regression_verified"] = True
                            record["status"] = primary_outcome(rejected, record["witness_verified"], record.get("equivalence_verified", False))
                persist(record)
            except bounded.CleanupError as exc:
                record.update(status="error", error=str(exc))
                persist(record)
                break
            except CaseStop as exc:
                record.update(status=exc.status, error=str(exc))
                persist(record)
            except (ValueError, RuntimeError, OSError, subprocess.SubprocessError) as exc:
                record.update(status="error" if record["checks"] else "unrun", error=type(exc).__name__ + ": " + str(exc))
                persist(record)
            print(record["id"], record["status"], flush=True)
        final = {**result, **summarize(result["records"], manifest["cases"])}
        save(out / "result.json", final)
        (out / "SHA256SUMS").write_text("".join(sha(p) + "  " + str(p.relative_to(out)) + "\n" for p in sorted(out.rglob("*")) if p.is_file() and p.name != "SHA256SUMS"))
        return final
