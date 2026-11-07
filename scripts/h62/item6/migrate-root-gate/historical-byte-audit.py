#!/usr/bin/env python3
"""Guard against accepting missing historical API bytes from path hints or regeneration.

Regression guarded: a present same-name file, a Markdown-normalized locator or a
current metadata hash must not become proof of exact historical artifact identity.
No compiler invocation, artifact regeneration, network lookup or source edits.
"""
import hashlib
import json
from pathlib import Path
import sys
sys.dont_write_bytecode = True


def classify(raw_locator):
    literal = Path(raw_locator)
    # This is a lookup hint only; preserve the original exact text separately.
    candidate_text = raw_locator.rstrip("`:,.")
    candidate = Path(candidate_text)
    selected = literal if literal.exists() else candidate
    row = {"raw_locator": raw_locator, "looked_up_path": str(selected), "literal_exists": literal.exists(),
           "normalized_candidate": candidate_text,
           "normalization_is_identity_evidence": False,
           "candidate_exists": candidate.exists(),
           "historical_exact_bytes": "UNVERIFIABLE",
           "historical_digest_verified": False,
           "API_axiom_acceptance": False}
    if selected.is_file():
        row.update(current_candidate_kind="file",
                   current_candidate_sha256=hashlib.sha256(selected.read_bytes()).hexdigest(),
                   boundary="Current bytes only; no authenticated historical digest is bound by this input. Not certified raw compiler exports.")
    elif selected.is_dir():
        row.update(current_candidate_kind="directory",
                   boundary="Directory existence does not supply referenced raw export files or historical identity.")
    else:
        row.update(current_candidate_kind="missing",
                   boundary="Referenced bytes absent at literal/candidate locator; UNVERIFIABLE under H30/H86. Do not reconstruct or treat regenerated/transcribed bytes as identical.")
    return row


def main():
    if len(sys.argv) != 3:
        raise SystemExit("usage: historical-byte-audit.py INVENTORY.json NEW_OUTPUT.json")
    source, output = map(Path, sys.argv[1:])
    if output.exists():
        raise ValueError("preserve earlier evidence: output must be new")
    raw = source.read_bytes(); inventory = json.loads(raw)
    rows = []
    for lane in inventory["lanes"]:
        for reference in lane["referenced_export_paths"]:
            rows.append({"lane": lane["lane"], "final_member_head": lane["final_member_head"],
                         **classify(reference["path"])})
    result = {"schema_version":1, "inventory_source":str(source),
              "inventory_sha256":hashlib.sha256(raw).hexdigest(),
              "generator_sha256":hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
              "reference_records":len(rows), "rows":rows,
              "historical_byte_identity_accepted":False, "API_axiom_acceptance":False,
              "Lean_runs":0, "artifacts_regenerated":0,
              "boundary":"Only existing selected API-reference records are audited, not an exhaustive search or missing-artifact recovery. H82b authenticated handoff metadata and integrated Git heads remain verified separately. Same-name copies, transcriptions and regenerated results do not establish historical byte identity."}
    with output.open("x") as f:
        json.dump(result,f,indent=2); f.write("\n")
    print(json.dumps({"reference_records":len(rows),"missing":sum(r["current_candidate_kind"]=="missing" for r in rows),"historical_identity":"UNVERIFIABLE; no historical digest binding in these references"}))


if __name__ == "__main__":
    main()
