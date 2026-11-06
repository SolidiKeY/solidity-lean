"""Freshness checks for audit receipts. These checks do not replace Lean proofs."""
import hashlib
import json
from pathlib import Path

HELPER="tests/h62/item2/audit-calculus/KernelCensus.lean"


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def find_direct_compile(records, file, source_hash, artifact_hash, dependencies, lean_hash):
    """Only an actual schema2 compile can certify a private artifact for reuse."""
    for record in reversed(records):
        if (record.get("schema")==2 and record.get("kind")=="compile" and record.get("exit")==0
            and record.get("file")==file and record.get("source_sha256")==source_hash
            and record.get("artifact_sha256")==artifact_hash
            and record.get("dependency_artifact_hashes")==dependencies
            and record.get("lean_sha256")==lean_hash):
            if record.get("log") and Path(record["log"]).is_file() and sha(record["log"])==record.get("log_sha256"):
                return record
    return None


def validate_dependency_edge(parent, child, expected_hash):
    if child.get("artifact_sha256")!=expected_hash:
        raise RuntimeError("dependency artifact differs from parent's checked input")
    if child.get("lean_sha256")!=parent.get("lean_sha256"):
        raise RuntimeError("mixed Lean binaries across a dependency edge")


def validate_export(record, root, current_compile, current_helper):
    if record.get("schema")!=2 or record.get("kind")!="kernel-census" or record.get("exit")!=0:
        raise RuntimeError("no current successful schema2 kernel export")
    if record["source_sha256"]!=sha(root/record["file"]):raise RuntimeError("stale export source")
    for field in ("log","json","scratch","artifact","helper_artifact"):
        if sha(record[field])!=record[field+"_sha256"]:raise RuntimeError("stale/tampered export "+field)
    if record["helper_source_sha256"]!=sha(root/HELPER):raise RuntimeError("stale helper source")
    if current_compile.get("kind")=="compile-cache" and not current_compile.get("source_compilation_verified"):
        raise RuntimeError("legacy artifact adoption is not a verified source compile")
    if current_compile.get("exit")!=0 or current_compile.get("artifact_sha256")!=record["artifact_sha256"] or current_compile.get("source_sha256")!=record["source_sha256"]:
        raise RuntimeError("export not bound to current successful module artifact")
    if current_helper.get("exit")!=0 or current_helper.get("source_sha256")!=record["helper_source_sha256"] or current_helper.get("artifact_sha256")!=record["helper_artifact_sha256"]:
        raise RuntimeError("export not bound to current successful helper artifact")
    if current_compile.get("lean_sha256")!=record["lean_sha256"] or current_helper.get("lean_sha256")!=record["lean_sha256"]:
        raise RuntimeError("export/compiler toolchain mismatch")
    item=json.loads(Path(record["json"]).read_text())
    if item["module"]!=record["module"]:raise RuntimeError("wrong exported module")
    logged=[line.split("H62_KERNEL_CENSUS ",1)[1] for line in Path(record["log"]).read_text().splitlines() if "H62_KERNEL_CENSUS " in line]
    if len(logged)!=1 or json.loads(logged[0])!=item:raise RuntimeError("export JSON differs from passing log")
    return item
