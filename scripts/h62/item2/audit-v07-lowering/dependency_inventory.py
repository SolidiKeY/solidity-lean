#!/usr/bin/env python3
"""Read-only imported premise-contract source inventory, not scope registration.

Captures exact source definitions required by the 15 producer-bearing mapped
signatures. No fabricated producer, reference, success premise or Lean claim.
"""
import argparse
import hashlib
import json
import pathlib
import re
from census import masked
from source_inventory import terminator, binders, classification

SELECTED = {
    "Solidity/Lowering/P8/FrozenInterface.lean": ("Solidity.Lowering.P8.P8a", [
        ("abbrev", "Spec"), ("structure", "OperationalReference"),
        ("structure", "SourceOrigins"), ("structure", "RootModel"),
        ("structure", "Extraction"), ("structure", "Extractor"),
        ("structure", "FailureProjection"), ("structure", "SourceRealization"),
        ("structure", "Producer")]),
    "Solidity/Roadmap/Contracts.lean": ("Solidity.Roadmap", [
        ("structure", "SourceSpec"), ("def", "SourceSpec.Admitted"),
        ("def", "SourceSpec.Unambiguous"), ("def", "SourceSpec.AllPipelines"),
        ("def", "SourceSpec.Approved"), ("def", "SourceSpec.NonVacuous"),
        ("structure", "Admission"), ("structure", "CheckedFrontend")])
}


def sha(text):
    return hashlib.sha256(text.encode()).hexdigest()


def inventory(repo):
    records = []
    for path, (namespace, selected) in SELECTED.items():
        raw = (repo/path).read_bytes()
        source = raw.decode()
        code = masked(source)
        for kind, name in selected:
            matches = list(re.finditer(r"^"+kind+r"\s+"+re.escape(name)+r"(?=\s|:|\{|\()", code, re.M))
            if len(matches) != 1:
                raise ValueError(f"expected one {path}:{name}, got {len(matches)}")
            match = matches[0]
            start = match.start()
            sep, term = terminator(code, match.end(), kind == "structure")
            body = sep+len(term)
            nxt = re.search(r"^\S", code[body:], re.M)
            end = body+nxt.start() if nxt else len(code)
            tokens = list(re.finditer(r"\S", code[start:end]))
            end = start+tokens[-1].end()
            record = dict(path=path, name=namespace+"."+name, kind=kind,
                start=start, end=end, line=source.count("\n", 0, start)+1,
                source=source[start:end], sha256=sha(source[start:end]),
                module_sha256=hashlib.sha256(raw).hexdigest(),
                header_source=source[start:sep], header_end=sep,
                binder_evidence=binders(source[start:sep], match.end()-start),
                scope="supplemental imported contract; no module-map registration or proof-lane expansion",
                inhabitation="unproved", statement_fidelity="pending-elaboration")
            if kind == "structure":
                fields = list(re.finditer(r"^  ([A-Za-z_][A-Za-z0-9_']*)\s*:", code[body:end], re.M))
                record["fields"] = []
                for i, field in enumerate(fields):
                    fs = body+field.start()
                    fe = body+fields[i+1].start() if i+1 < len(fields) else end
                    tokens = list(re.finditer(r"\S", code[fs:fe]))
                    fe = fs+tokens[-1].end()
                    category, reason = classification(source[body+field.end():fe])
                    record["fields"].append(dict(name=field[1], start=fs,end=fe,
                        source=source[fs:fe],sha256=sha(source[fs:fe]),category=category,reason=reason,
                        boundary="field declaration including any default; not an elaborated field type"))
                if not fields:
                    raise ValueError("no fields for "+name)
            records.append(record)
    return dict(schema=1, boundary="Exact source definitions, not a transitive dependency closure, proof, or simultaneous witness.",
                contracts=records, count=len(records), fields=sum(len(r.get("fields", [])) for r in records))


if __name__ == "__main__":
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--repo", type=pathlib.Path, required=True)
    p.add_argument("--output", type=pathlib.Path, required=True)
    a = p.parse_args()
    result = inventory(a.repo)
    a.output.write_text(json.dumps(result, indent=2, sort_keys=True)+"\n")
    print(f"{result['count']} imported definitions; {result['fields']} field declarations; all inhabitation unproved")
