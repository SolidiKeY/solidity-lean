#!/usr/bin/env python3
"""Export only a stopped, committed retirement handoff; never push or mutate goals."""
import argparse
import gzip
import hashlib
import io
import json
from pathlib import Path
import subprocess
import tarfile

ROOT = Path(__file__).resolve().parents[4]
BASE = "c6f550e281a7e5affa9a99bc2cdaed556dec00e4"
BRANCH = "codex/solidity-h62-2-20261106/audit-language"
INPUTS = ROOT / "tests/h62/item2/audit-language/retirement"

def git(*args):
    return subprocess.check_output(["git", *args], cwd=ROOT)

def digest(path):
    h = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()

def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--increment-base", default=BASE, help="Existing checkout head before this isolated packaging increment")
    p.add_argument("--output", type=Path, required=True)
    p.add_argument("--evidence", type=Path, required=True)
    p.add_argument("--coordinator-inputs", type=Path, required=True)
    a = p.parse_args()
    a.output = a.output.resolve()
    a.evidence = a.evidence.resolve()
    assert not a.output.is_relative_to(ROOT)
    assert not a.output.is_relative_to(a.evidence)
    assert git("branch", "--show-current").decode().strip() == BRANCH
    assert not git("status", "--porcelain"), "commit all handoff work first"
    subprocess.run(["git", "merge-base", "--is-ancestor", BASE, "HEAD"], cwd=ROOT, check=True)
    increment_base = git("rev-parse", "--verify", a.increment_base + "^{commit}").decode().strip()
    subprocess.run(["git", "merge-base", "--is-ancestor", increment_base, "HEAD"], cwd=ROOT, check=True)
    paths = git("diff", "--name-only", increment_base, "HEAD").decode().splitlines()
    for path in paths:
        assert path.startswith(("tests/h62/item2/audit-language/", "scripts/h62/item2/audit-language/")) or path == "docs/feature-work/h62-2-audit-language.md", path
    # Mandatory original scope and prompt bytes must be committed and authenticated.
    for line in (INPUTS / "SHA256SUMS").read_text().splitlines():
        expected, name = line.split("  ", 1)
        assert digest(INPUTS / name) == expected
        assert git("show", "HEAD:" + str((INPUTS / name).relative_to(ROOT))) == (INPUTS / name).read_bytes()
    scope_manifest = json.loads((INPUTS / "scope-manifest.json").read_text())
    bulk = Path(scope_manifest["artifact"]["path"])
    assert bulk.resolve().is_relative_to(a.evidence), "scope bulk must be included in portable evidence"
    assert digest(bulk) == scope_manifest["artifact"]["sha256"]
    assert bulk.stat().st_size == scope_manifest["artifact"]["bytes"]
    state = json.loads((INPUTS / "retirement.json").read_text())
    assert state["execution_state"] == "STOPPED_BY_HUMAN_RETIREMENT"
    a.output.mkdir(parents=True, exist_ok=True)
    patch = a.output / "original.patch"
    owned_paths = ["tests/h62/item2/audit-language/", "scripts/h62/item2/audit-language/", "docs/feature-work/h62-2-audit-language.md"]
    patch.write_bytes(git("diff", "--binary", BASE, "HEAD", "--", *owned_paths))
    (a.output / "increment.patch").write_bytes(git("diff", "--binary", increment_base, "HEAD"))
    bundle = a.output / "audit-language.bundle"
    subprocess.run(["git", "bundle", "create", str(bundle), increment_base + ".." + BRANCH], cwd=ROOT, check=True)
    verify = subprocess.run(["git", "bundle", "verify", str(bundle)], cwd=ROOT, capture_output=True, text=True)
    (a.output / "bundle-verify.log").write_text(verify.stdout + verify.stderr)
    assert verify.returncode == 0
    archive = a.output / "portable-evidence.tar.gz"
    members = []
    excluded = []
    for file in sorted(a.evidence.rglob("*")):
        if not file.is_file():
            continue
        rel = file.relative_to(a.evidence)
        if "lib" in rel.parts or "cache" in rel.parts or rel.parts[0] == "toolchain":
            excluded.append(str(rel))
            continue
        members.append(("evidence/" + str(rel), file))
    for file in sorted(a.coordinator_inputs.rglob("*")):
        if file.is_file():
            members.append(("coordinator-inputs/" + str(file.relative_to(a.coordinator_inputs)), file))
    for file in sorted(INPUTS.iterdir()):
        if file.is_file():
            members.append(("retirement/" + file.name, file))
    # Each archived byte stream has its own internal checksum, independent of
    # the historical manifests whose absolute paths are provenance only.
    internal = "".join(digest(file) + "  " + name + "\n" for name, file in members).encode()
    with archive.open("wb") as raw, gzip.GzipFile(filename="", mode="wb", fileobj=raw, mtime=0, compresslevel=1) as compressed, tarfile.open(fileobj=compressed, mode="w|") as tar:
        for name, file in members:
            info = tar.gettarinfo(str(file), arcname=name)
            info.mtime = info.uid = info.gid = 0
            info.uname = info.gname = ""
            info.mode = 0o644
            with file.open("rb") as stream:
                tar.addfile(info, stream)
        info = tarfile.TarInfo("PORTABLE-SHA256SUMS")
        info.size = len(internal)
        info.mode = 0o644
        tar.addfile(info, io.BytesIO(internal))
    (a.output / "archive-contents.sha256").write_bytes(internal)
    handoff = dict(state, batch="solidity-h62-2-20261106", slug="audit-language", branch=BRANCH,
                   base=BASE, head=git("rev-parse", "HEAD").decode().strip(), repository=str(ROOT),
                   clean=True, changed_paths=paths, bundle_requires_base=increment_base,
                   increment_base=increment_base, cumulative_patch_scope="Only original lane-owned paths relative to frozen base; upstream merges excluded",
                   external_scope_manifest=scope_manifest,
                   packaging_validation="evidence/h44/split-validation.json",
                   packaging_reviews="evidence/h44/split-reviews.json",
                   no_push_merge_publication=True, archived_files=len(members),
                   archive_exclusions="Compiled lib/cache products and toolchain archive/extraction; all remain on original VM. Official pin is included.",
                   portable_path_rule="Original absolute paths are provenance. Extract portable-evidence.tar.gz: evidence/, coordinator-inputs/, retirement/. Verify PORTABLE-SHA256SUMS.",
                   versions=json.loads((a.evidence / "versions.json").read_text()),
                   prior_gate_commands_and_outcomes=["evidence/h70-continuation-validation.json", "evidence/migration-blockers.json", "evidence/final-reviewed/checks.json"],
                   final_retirement_validation="evidence/h82/retirement-validation.json",
                   final_retirement_reviews="evidence/h82/retirement-reviews.json",
                   artifacts={"original_patch": str(patch), "increment_patch": str(a.output / "increment.patch"), "bundle": str(bundle), "handoff": str(a.output / "handoff.json"),
                              "evidence": str(a.evidence), "archive": str(archive), "checksums": str(a.output / "SHA256SUMS")})
    (a.output / "handoff.json").write_text(json.dumps(handoff, indent=2) + "\n")
    files = sorted(x for x in a.output.iterdir() if x.is_file() and x.name != "SHA256SUMS")
    (a.output / "SHA256SUMS").write_text("".join(digest(x) + "  " + x.name + "\n" for x in files))
    print(json.dumps({"head": handoff["head"], "status": "partial", "execution_state": state["execution_state"],
                      "handoff_to": state["handoff_to"], "archived_files": len(members),
                      "artifacts": {x.name: digest(x) for x in files}}), flush=True)

if __name__ == "__main__":
    main()
