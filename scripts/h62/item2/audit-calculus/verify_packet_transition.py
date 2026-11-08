"""Guard regression: packet publication must preserve old classifications/scope.

Read exact immutable Git objects offline; synthetic tests do not substitute
for running this command on the actual private packets. Output is evidence
and must remain outside the code checkout.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
from bulk_inputs import REPO, _git_bytes, _checked


def read_packet(repo, commit, directory):
    manifest = _git_bytes(repo, commit, directory + "/bulk-inputs-manifest.json")
    records = json.loads(manifest)
    if set(records) != {"frozen_scope", "lifetime_roles"}:
        raise ValueError("packet requires exact scope and classification entries")
    blobs = {}
    identities = {}
    member_paths = {"bulk-inputs-manifest.json"}
    for name, row in records.items():
        path = row["path"]
        if not isinstance(path, str) or not re.fullmatch(r"[A-Za-z0-9_-]+\.json", path):
            raise ValueError("unsafe packet member")
        if path in member_paths:
            raise ValueError("reserved or duplicate packet member")
        member_paths.add(path)
        blobs[name] = _checked(_git_bytes(repo, commit, directory + "/" + path), row, name)
        identities[name] = {"path": path, "bytes": len(blobs[name]),
                            "sha256": hashlib.sha256(blobs[name]).hexdigest()}
    return {"dataset": json.loads(blobs["lifetime_roles"]), "scope": blobs["frozen_scope"],
            "manifest": manifest, "blobs": blobs, "identity": {
                "commit": commit, "directory": directory,
                "manifest_sha256": hashlib.sha256(manifest).hexdigest(), "payloads": identities}}


def compare(before, after):
    a, b = before["dataset"], after["dataset"]
    if before["scope"] != after["scope"]:
        raise ValueError("frozen scope bytes changed")
    for key in ("base", "source_census_sha256", "semantic_owner_by_file"):
        if a[key] != b[key]:
            raise ValueError("frozen provenance or owner map changed: " + key)
    if b["declarations"][:len(a["declarations"])] != a["declarations"]:
        raise ValueError("prior classification records changed")
    identities = [r["id"] for r in b["declarations"]]
    if len(identities) != len(set(identities)):
        raise ValueError("duplicate classification identity")
    if b["reviewed_files"][:len(a["reviewed_files"])] != a["reviewed_files"]:
        raise ValueError("prior reviewed file roster changed")
    if len(b["reviewed_files"]) != len(set(b["reviewed_files"])):
        raise ValueError("duplicate reviewed file")
    return {"before_reviewed": len(a["declarations"]), "after_reviewed": len(b["declarations"]),
            "added": len(b["declarations"]) - len(a["declarations"]),
            "prior_records_equal": True, "owners_equal": True, "scope_equal": True,
            "provenance_equal": True, "fresh_witness_credit": 0}


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--repo", type=Path, required=True)
    for side in ("before", "after"):
        p.add_argument("--" + side + "-commit", required=True)
        p.add_argument("--" + side + "-directory", required=True)
    p.add_argument("--out", type=Path, required=True)
    args = p.parse_args()
    if not args.out.is_absolute() or args.out.resolve().is_relative_to(REPO) or args.out.is_symlink():
        p.error("evidence output must be absolute and outside code checkout")
    packets = [read_packet(args.repo, getattr(args, side + "_commit"),
                           getattr(args, side + "_directory")) for side in ("before", "after")]
    result = compare(*packets)
    args.out.mkdir(parents=True, exist_ok=False)
    for side, packet in zip(("before", "after"), packets):
        root = args.out / side
        root.mkdir()
        (root / "bulk-inputs-manifest.json").write_bytes(packet["manifest"])
        for key, data in packet["blobs"].items():
            (root / packet["identity"]["payloads"][key]["path"]).write_bytes(data)
    result.update(before=packets[0]["identity"], after=packets[1]["identity"],
                  boundary="Exact packet/transition integrity only; no semantic, witness or kernel acceptance")
    (args.out / "validation.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, sort_keys=True))


if __name__ == "__main__":
    main()
