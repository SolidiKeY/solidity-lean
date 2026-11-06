"""Freshness checks for audit receipts. These checks do not replace Lean proofs."""
import hashlib
import json
from pathlib import Path

HELPER="tests/h62/item2/audit-calculus/KernelCensus.lean"
CHUNK_HELPER="tests/h62/item2/audit-calculus/ChunkCensus.lean"


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


def parse_export_log(log, module, export_format="module-v1"):
    """Rebuild precisely one full census; incomplete/overlapping chunks fail."""
    marker = "H62_KERNEL_CENSUS_CHUNK " if export_format == "chunks-v1" else "H62_KERNEL_CENSUS "
    if export_format not in {"module-v1", "chunks-v1"}:
        raise RuntimeError("unknown export format")
    parts = [json.loads(line.split(marker, 1)[1]) for line in log.splitlines() if marker in line]
    if export_format == "module-v1":
        if len(parts) != 1 or parts[0]["module"] != module:
            raise RuntimeError("not exactly one correct module export")
        return parts[0]
    if not parts:
        raise RuntimeError("no census chunks")
    total, limit = parts[0]["total"], parts[0]["limit"]
    if not isinstance(total, int) or total < 0 or not isinstance(limit, int) or limit <= 0:
        raise RuntimeError("invalid chunk bounds")
    offsets = list(range(0, total, limit)) or [0]
    if [part["offset"] for part in parts] != offsets:
        raise RuntimeError("missing, duplicated or reordered census chunks")
    records = []
    for part in parts:
        if part["module"] != module or part["total"] != total or part["limit"] != limit:
            raise RuntimeError("inconsistent census chunks")
        if len(part["theorems"]) != min(limit, total - part["offset"]):
            raise RuntimeError("incomplete census chunk")
        records.extend(part["theorems"])
    names = [row["name"] for row in records]
    if len(names) != total or len(set(names)) != total or names != sorted(names):
        raise RuntimeError("census names missing, duplicated or unsorted")
    return {"module": module, "theorems": records}


def probe_total_or_tombstone(record, limit, save):
    """A malformed zero-exit probe supersedes any older successful export."""
    try:
        marker="H62_KERNEL_CENSUS_CHUNK "
        parts=[json.loads(line.split(marker,1)[1]) for line in Path(record["log"]).read_text().splitlines() if marker in line]
        if len(parts)!=1:raise RuntimeError("not exactly one chunk probe")
        part=parts[0]
        total=part["total"]
        if (part["module"]!=record["module"] or part["offset"]!=0 or part["limit"]!=limit
            or type(total) is not int or total<0 or len(part["theorems"])!=min(limit,total)):
            raise RuntimeError("invalid chunk probe")
        return total
    except (RuntimeError,ValueError,KeyError,TypeError) as failure:
        save(dict(record,kind="kernel-census",exit=89,assembly_error=str(failure)))
        raise RuntimeError("chunk probe failed; older export superseded") from failure


def validate_export(record, root, current_compile, current_helper):
    if record.get("schema")!=2 or record.get("kind")!="kernel-census" or record.get("exit")!=0:
        raise RuntimeError("no current successful schema2 kernel export")
    if record["source_sha256"]!=sha(root/record["file"]):raise RuntimeError("stale export source")
    for field in ("log","json","scratch","artifact","helper_artifact"):
        if sha(record[field])!=record[field+"_sha256"]:raise RuntimeError("stale/tampered export "+field)
    helper_file=record.get("helper_file",HELPER)
    if helper_file not in {HELPER,CHUNK_HELPER}:raise RuntimeError("unknown census helper")
    if record["helper_source_sha256"]!=sha(root/helper_file):raise RuntimeError("stale helper source")
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
    logged=parse_export_log(Path(record["log"]).read_text(),record["module"],record.get("export_format","module-v1"))
    if logged!=item:raise RuntimeError("export JSON differs from passing log")
    return item
