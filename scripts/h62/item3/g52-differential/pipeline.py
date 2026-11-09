#!/usr/bin/env python3
"""H62 G52 external evidence tooling; no result here is a kernel proof."""
import argparse
import configparser
import hashlib
import json
import re
import subprocess
import tarfile
from collections import Counter
from pathlib import Path

SOLC_SHA = "65c3180a336eabb6bdc4bbd49cc405aeb233976964ae6c11fba2a6c8be8f3243"
SOLC_VERSION = "Version: 0.8.38+commit.1835d247.Linux.g++"
SOLC_BIN_COMMIT = "62f89f31914359ec2e153f1bc0614a1bdf2c8e17"
EEST_COMMIT = "6824474c2ae99e6a67be6093e9a1edc1c82091ea"
EEST_SHA = "5dd08fee0fb41bc2a59bc4ab1dc75b19723fc71fe6af2f855454d3283fba09b9"
FIELDS = ("halt", "output", "storage", "storage_full", "logs", "rollback")
BODIES = {
    "checked_add": "return x + K;",
    "unchecked_add": "unchecked { return x + K; }",
    "division": "return K / x;",
    "storage_log": "value = x; emit E(x); return value;",
    "rollback": "value = x; emit E(x); revert Failure(x);",
    "branch": "if (x < K) { value = x; } else { value = K; } return value;",
}


def sha(data):
    return hashlib.sha256(data).hexdigest()


def file_sha(path):
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def write(path, obj):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(obj, sort_keys=True, indent=2) + "\n")


def generate(root):
    cases = []
    sources = {}
    for seed in range(8):
        k = 1 + int(sha(f"g52-v1:{seed}".encode()), 16) % 31
        xs = [0, 1, k-1, k, 2**255, 2**256-2, 2**256-1,
              int(sha(f"g52-input-v1:{seed}".encode()), 16)]
        xs = list(dict.fromkeys(xs))
        for family, body in BODIES.items():
            name = f"{family}-{seed}.sol"
            source = ("// SPDX-License-Identifier: UNLICENSED\npragma solidity 0.8.38;\n"
                      "contract C { uint256 public value; event E(uint256 x); error Failure(uint256 x); "
                      f"uint256 constant K = {k}; function f(uint256 x) external returns (uint256) {{ {body} }} }}\n")
            sources[name] = source
            for i, x in enumerate(xs):
                cases.append(dict(id=f"{family}:{seed}:{i}", family=family, seed=seed,
                                  source=name, x=str(x), initial_storage={"0": "7"},
                                  gas_limit="1000000", fork="Osaka"))
    for name, source in sources.items():
        p = root / "generated" / "sources" / name
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(source)
    obj = dict(schema=1, generator="g52-v1", fork="Osaka", cases=cases,
               source_sha256={k: sha(v.encode()) for k, v in sources.items()})
    write(root / "generated" / "cases.json", obj)
    return dict(sources=len(sources), cases=len(cases), manifest_sha256=sha((root/"generated/cases.json").read_bytes()))


def verify_solc(binary):
    actual = sha(binary.read_bytes())
    if actual != SOLC_SHA:
        raise ValueError(f"native solc checksum mismatch: {actual}")
    version = subprocess.run([str(binary), "--version"], check=True, capture_output=True, text=True).stdout
    if SOLC_VERSION not in version.splitlines():
        raise ValueError(f"native solc version mismatch: {version!r}")
    return dict(binary_sha256=actual, version=version, upstream_commit=SOLC_BIN_COMMIT)


def compile_cases(root):
    pin = verify_solc(root/"upstream/solc")
    manifest = json.loads((root/"generated/cases.json").read_text())
    counts = Counter()
    artifacts = {}
    for name, expected in manifest["source_sha256"].items():
        source = (root/"generated/sources"/name).read_text()
        if sha(source.encode()) != expected:
            raise ValueError(f"source hash mismatch: {name}")
        for via_ir in [False, True]:
            mode = "via-ir" if via_ir else "legacy"
            request = dict(language="Solidity", sources={name: dict(content=source)},
                           settings=dict(viaIR=via_ir, evmVersion="osaka",
                                         optimizer=dict(enabled=True, runs=200),
                                         metadata=dict(bytecodeHash="none"),
                                         outputSelection={"*": {"": ["ast"], "*": ["abi", "evm.deployedBytecode.object"]}}))
            p = subprocess.run([str(root/"upstream/solc"), "--standard-json"],
                               input=json.dumps(request), text=True, capture_output=True, check=True, timeout=60)
            result = json.loads(p.stdout)
            write(root/"compiled"/mode/(name+".input.json"), request)
            write(root/"compiled"/mode/(name+".json"), result)
            errors = [e for e in result.get("errors", []) if e["severity"] == "error"]
            if errors:
                raise ValueError(f"compilation failed {name}/{mode}: {errors}")
            bytecode = result["contracts"][name]["C"]["evm"]["deployedBytecode"]["object"]
            if not bytecode or not re.fullmatch(r"[0-9a-f]+", bytecode):
                raise ValueError(f"missing or unlinked bytecode {name}/{mode}")
            for artifact in (root/"compiled"/mode/(name+".input.json"), root/"compiled"/mode/(name+".json")):
                artifacts[str(artifact.relative_to(root))] = file_sha(artifact)
            counts[mode] += 1
    receipt = dict(pin=pin, input_sha256=file_sha(root/"generated/cases.json"), artifacts=artifacts, settings=dict(optimizer=dict(enabled=True, runs=200), evmVersion="osaka"), counts=dict(counts))
    write(root/"evidence/compiler.json", receipt)
    return dict(pin=pin, counts=dict(counts), artifacts=len(artifacts), input_sha256=receipt["input_sha256"], settings=receipt["settings"])


def census(root):
    archive = root/"upstream/fixtures_develop-v5.3.0.tar.gz"
    if file_sha(archive) != EEST_SHA:
        raise ValueError("EEST archive checksum mismatch")
    rows = []
    counts = Counter()
    metadata_verified = False
    # Stream; never extract upstream archive paths into the filesystem.
    with tarfile.open(archive, "r|gz") as tar:
        for member in tar:
            if member.name == "fixtures/.meta/fixtures.ini":
                config = configparser.ConfigParser()
                config.read_string(tar.extractfile(member).read().decode())
                if config["fixtures"]["commit"] != EEST_COMMIT or config["fixtures"]["ref"] != "refs/tags/v5.3.0":
                    raise ValueError("EEST embedded provenance mismatch")
                metadata_verified = True
            if not member.isfile() or not member.name.endswith(".json"):
                continue
            data = tar.extractfile(member).read()
            file_hash = sha(data)
            if not member.name.startswith("fixtures/state_tests/"):
                continue
            doc = json.loads(data)
            for name, fixture in doc.items():
                post = fixture.get("post", {})
                if "Osaka" not in post:
                    continue
                fork_keys = list(post)
                status = "pending-execution"
                for variant, expected in enumerate(post["Osaka"]):
                    rows.append(dict(path=member.name, case=name, variant=variant, indexes=expected["indexes"],
                                     sha256=file_hash, forks=fork_keys, status=status,
                                     reason="fixture adapter not yet executed"))
                    counts[status] += 1
    if not metadata_verified:
        raise ValueError("missing EEST fixture build provenance")
    if not rows:
        raise ValueError("no Osaka post-state fixtures in pinned archive; do not report empty success")
    receipt = dict(upstream_commit=EEST_COMMIT, release="v5.3.0", fork="Osaka",
                   archive_sha256=file_sha(archive), counts=dict(counts), cases=rows)
    write(root/"evidence/eest-census.json", receipt)
    return dict(upstream_commit=EEST_COMMIT, counts=dict(counts), fixtures=len(rows), archive_sha256=receipt["archive_sha256"])


def validate_observation(row):
    if row.get("status") != "executed":
        return
    for field in FIELDS:
        if field not in row:
            raise ValueError(f"executed observation lacks {field}")
    if row["halt"] not in ("return", "revert", "exception"):
        raise ValueError("invalid halt")
    if not isinstance(row["output"], str) or not re.fullmatch(r"0x(?:[0-9a-f]{2})*", row["output"]):
        raise ValueError("noncanonical output")
    if not isinstance(row["storage"], dict) or not isinstance(row["logs"], list):
        raise ValueError("invalid state observation")
    word = lambda x: isinstance(x, str) and re.fullmatch(r"0|[1-9][0-9]*", x) and int(x) < 2**256
    if not all(word(k) and word(v) for k, v in row["storage"].items()):
        raise ValueError("noncanonical storage word")
    for log in row["logs"]:
        if not isinstance(log, dict) or set(log) != {"address", "topics", "data"}:
            raise ValueError("invalid log fields")
        if not re.fullmatch(r"0x[0-9a-f]{40}", log["address"]):
            raise ValueError("invalid log address")
        if not isinstance(log["topics"], list) or len(log["topics"]) > 4 or not all(
            isinstance(topic, str) and re.fullmatch(r"0x[0-9a-f]{64}", topic) for topic in log["topics"]):
            raise ValueError("invalid log topics")
        if not isinstance(log["data"], str) or not re.fullmatch(r"0x(?:[0-9a-f]{2})*", log["data"]):
            raise ValueError("invalid log data")
    if not isinstance(row["storage_full"], dict) or not all(
        isinstance(k, str) and re.fullmatch(r"0x[0-9a-f]{64}", k) and
        isinstance(v, str) and re.fullmatch(r"0x(?:[0-9a-f]{2})+", v)
        for k, v in row["storage_full"].items()):
        raise ValueError("invalid full storage trie observation")
    if not isinstance(row["rollback"], bool):
        raise ValueError("invalid rollback observation")


def compare(left, right):
    validate_observation(left)
    validate_observation(right)
    if left.get("status") != "executed" or right.get("status") != "executed":
        return dict(status="unsupported", reason="both real engines must execute", fields=[])
    if left.get("fork") != "Osaka" or right.get("fork") != "Osaka":
        return dict(status="unsupported", reason="both engines must attest Osaka", fields=[])
    different = [field for field in FIELDS if left[field] != right[field]]
    if not left["rollback"] or not right["rollback"]:
        if "rollback" not in different:
            different.append("rollback")

    # Gas comparison is valid only for the same explicitly declared metric.
    gas_applicable = left.get("gas_metric") == right.get("gas_metric") and left.get("gas_metric") is not None
    if gas_applicable:
        if "gas_used" not in left or "gas_used" not in right:
            raise ValueError("gas metric declared without value")
        if left["gas_used"] != right["gas_used"]:
            different.append("gas_used")
    return dict(status="mismatch" if different else "match", fields=different,
                gas_status="compared" if gas_applicable else "unsupported")


def load_results(path, root, role):
    doc = json.loads(path.read_text())
    if doc.get("input_sha256") != file_sha(root/"generated/cases.json") or doc.get("compiler_sha256") != file_sha(root/"evidence/compiler.json"):
        raise ValueError(f"{role} results do not bind current cases/compiler")
    if doc.get("role") != role or not doc.get("producer"):
        raise ValueError(f"{role} missing producer identity")
    return doc["results"]


def compare_results(root):
    manifest = json.loads((root/"generated/cases.json").read_text())
    # Canonical regenerated manifest binds every source, seed and unique input.
    import tempfile
    with tempfile.TemporaryDirectory() as d:
        generate(Path(d))
        canonical = json.loads((Path(d)/"generated/cases.json").read_text())
    if manifest != canonical:
        raise ValueError("case manifest differs from complete canonical generator output")
    cases = manifest["cases"]
    reference = load_results(root/"evidence/reference.json", root, "reference")
    own_path = root/"evidence/semantics.json"
    own = load_results(own_path, root, "semantics") if own_path.exists() else {}
    expected = {f"{mode}:{c['id']}" for mode in ("legacy", "via-ir") for c in cases}
    if not cases or len(expected) != 2 * len(cases):
        raise ValueError("empty or duplicate generated case IDs")
    if set(reference) != expected:
        raise ValueError("reference case coverage differs from exact generated manifest")
    if own_path.exists() and set(own) != expected:
        raise ValueError("semantics case coverage differs from exact generated manifest")
    rows = {key: compare(own.get(key, dict(status="unsupported", reason="real executable semantics adapter unavailable")), reference[key])
            for key in sorted(expected)}
    counts = dict(Counter(row["status"] for row in rows.values()))
    receipt = dict(counts=counts, expected=len(expected), results=rows, scope="generated-only",
                   complete=counts.get("match", 0)==len(expected) and all(row.get("gas_status")=="compared" for row in rows.values()))
    write(root/"evidence/comparison.json", receipt)
    return dict(counts=counts, expected=len(expected), complete=receipt["complete"])


def block_acceptance(root):
    """Guard omitted mismatch transactions and reference/source count conflation.

    Deterministic post-run accounting only, never a source-semantics proof.
    Candidate transactions from mismatched blocks are retained observations,
    separately counted from transactions of accepted blocks.
    """
    evidence = root/"evidence"
    path = evidence/"eest-reference-block-transactions-final.jsonl"
    summary = json.loads((evidence/"eest-reference-block-transactions-final-summary.json").read_text())
    receipt_path = evidence/"blockchain-export.json"
    export = json.loads(receipt_path.read_text())
    if summary["format"] != "blockchain_test" or summary["export_sha256"] != file_sha(receipt_path):
        raise ValueError("block export binding mismatch")
    if export["archive_sha256"] != EEST_SHA or export["stream_sha256"] != file_sha(root/"blockchain-inputs.jsonl.gz"):
        raise ValueError("block archive/input binding mismatch")
    if summary["reference_lock_sha256"] != file_sha(root/"reference/package-lock.json"):
        raise ValueError("reference lock drift")
    for field, name in (("adapter_sha256", "eest_reference.mjs"), ("blockchain_adapter_sha256", "blockchain_adapter.mjs"), ("rejection_adapter_sha256", "eest_rejection.mjs")):
        if summary[field] != file_sha(Path(__file__).parent/name):
            raise ValueError("production adapter drift: " + name)
    counts, outcomes, categories = Counter(), Counter(), Counter()
    indices, mismatches = set(), []
    totals = Counter()
    def transactions(block, scope):
        cumulative = 0
        for index, tx in enumerate(block["transactions"]):
            if tx["index"] != index or tx["receipt_status"] != (0 if tx["execution_exception"] else 1):
                raise ValueError("native transaction identity/status mismatch")
            cumulative += int(tx["total_gas_spent"])
            if cumulative != int(tx["receipt_cumulative_gas_used"]) or not re.fullmatch(r"0x(?:[0-9a-f]{2})*", tx["output"]):
                raise ValueError("native output/gas observation mismatch")
            if tx["execution_exception"] and tx["logs"]:
                raise ValueError("failed transaction retained logs")
            totals[scope] += 1
            totals["retained_transactions"] += 1
            totals["raw_log_count"] += len(tx["logs"])
            totals["nonempty_outputs"] += tx["output"] != "0x"
            totals["positive_native_refund_counters"] += int(tx["native_gas_refund_counter"]) > 0
            outcomes["return" if tx["execution_exception"] is None else ("revert" if tx["execution_exception"] == "revert" else "fault")] += 1
        if cumulative != int(block["gas_used"]):
            raise ValueError("retained transaction/block gas disagreement")
    with path.open() as stream:
        for line in stream:
            row = json.loads(line)
            if row["index"] in indices or row["source_semantics"] != "unsupported-adapter-pending":
                raise ValueError("duplicate case or conflated source result")
            indices.add(row["index"])
            counts[row["status"]] += 1
            if row["status"] == "reference_match" and not all(row.get(key) is True for key in ("header_validation", "block_validation", "block_size_validation")):
                raise ValueError("match without all native validators")
            if row["status"] == "reference_mismatch":
                mismatches.append(row["index"])
            for rejection in row.get("rejections", []):
                if rejection["status"] != "reference_match" or not rejection["matched_categories"] or rejection["before_state_root"] != rejection["after_state_root"] or rejection["before_head"] != rejection["after_head"]:
                    raise ValueError("invalid matched rejection/rollback")
                totals["matched_rejections"] += 1
                categories.update(rejection["matched_categories"])
            for block in row.get("blocks", []):
                totals["validated_accepted_blocks"] += 1
                transactions(block, "accepted_block_transactions")
            if "transactions" in row.get("observed", {}):
                if row["status"] != "reference_mismatch":
                    raise ValueError("unexpected candidate observations")
                totals["mismatch_candidate_blocks"] += 1
                transactions(row["observed"], "mismatch_candidate_transactions")
    if indices != set(range(export["cases"])) or dict(counts) != summary["counts"] or summary["selected"] != export["cases"]:
        raise ValueError("incomplete or inconsistent full-corpus outcome accounting")
    complete = counts["reference_match"] == export["cases"]
    if summary["reference_complete"] != complete or summary["differential_complete"] is not False:
        raise ValueError("incorrect completion flags")
    result = dict(summary=summary, unique_cases=len(indices), counts_verified=dict(counts), **totals,
        outcomes=dict(outcomes), matched_categories=dict(categories), mismatch_indices=mismatches,
        all_source_semantics_unsupported=True, result_sha256=file_sha(path),
        production_adapter_hashes_verified=True, provisional_runs_excluded=True,
        raw_full_process_exit=None,
        exit_capture_limitation="Full PTY session expired before exit retrieval; runner assigns a failure exit for observed mismatches. Exact fixture replay separately captured exit1. No passing conformance gate claimed.",
        new_fixture_matches_from_synthetic_controls=0)
    write(evidence/"block-transactions-acceptance.json", result)
    return result


def manifest(root):
    paths = sorted(p for directory in ("generated", "compiled", "typed-compiled", "boundary-compiled", "lean-build", "pre-merge", "evidence")
                   for p in (root/directory).rglob("*") if p.is_file() and p.name != "sha256.json")
    paths += [root/name for name in ("upstream/solc", "upstream/solc-list.json",
              "upstream/fixtures_develop-v5.3.0.tar.gz",
              "reference/package.json", "reference/package-lock.json")]
    for optional in ("transaction-inputs.jsonl.gz", "engine-inputs.jsonl.gz", "engine-x-inputs.jsonl.gz", "sync-inputs.jsonl.gz", "engine-x-allocations.jsonl", "engine-x-allocations-index.json", "blockchain-inputs.jsonl.gz", "archive-inventory.jsonl.gz", "eest-inputs.jsonl.gz", "upstream/reference-before-kzg-package-lock.json", "upstream/reference-before-blockchain-package-lock.json", "upstream/eip7934-v5.3.0-spec.py", "upstream/fixtures_stable-v5.3.0.tar.gz", "toolchain/lean-4.24.0-linux.tar.zst"):
        if (root/optional).is_file(): paths.append(root/optional)
    obj = {str(p.relative_to(root)): file_sha(p) for p in paths}
    write(root/"sha256.json", obj)
    return dict(files=len(obj), sha256=sha((root/"sha256.json").read_bytes()))


def main():
    parser = argparse.ArgumentParser(__doc__)
    parser.add_argument("action", choices=["generate", "compile", "census", "compare", "manifest", "block-acceptance"])
    parser.add_argument("--bulk", type=Path, required=True)
    args = parser.parse_args()
    root = args.bulk.resolve()
    # Bulk must stay outside this repository, including via symlinks.
    repo = Path(__file__).resolve().parents[4]
    if root == repo or repo in root.parents:
        parser.error("H44 bulk directory must be outside Git checkout")
    fn = {"generate": generate, "compile": compile_cases, "census": census,
          "compare": compare_results, "manifest": manifest, "block-acceptance": block_acceptance}[args.action]
    result = fn(root)
    print(json.dumps(result, sort_keys=True))
    if args.action == "block-acceptance" and not result["summary"]["reference_complete"]:
        raise SystemExit(1 if result["counts_verified"].get("reference_mismatch") or result["counts_verified"].get("engine_error") else 2)

if __name__ == "__main__":
    main()
