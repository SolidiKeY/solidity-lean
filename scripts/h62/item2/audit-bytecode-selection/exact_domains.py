#!/usr/bin/env python3
"""Guard against replacing joint kernel-binder domains with copied signatures.

Render proof-specific witnesses using the existing pinned hypothesis elaborator.
This is not a census, an inspection-acceptance gate or a witness-ledger linker.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess

from census import BASE, MAP, mask, mapped_references

MACRO_PATH = "tests/h62/item2/audit-bytecode-selection/HypothesisDomains.lean"
FIXTURE_PATH = "tests/h62/item2/audit-bytecode-selection/exact-gate-domains.txt"
NAMESPACE = "Solidity.H62.BytecodeSelection.HypothesisAudit"
MACRO_SHA256 = "27ba183e9fc5db42bf9e4733d31ce7f988cbc564db4a5b7ded7405b239a1ebe6"
TARGETS = {
    "head_certificate_executed_domain": "Solidity.Backend.AbiEntry.Interface.HeadGateCertificate.executed",
    "word_certificate_executed_domain": "Solidity.Backend.AbiEntry.Interface.WordGateCertificate.executed",
    "word_correspondence_domain": "Solidity.Backend.AbiEntry.WordGate.correspondence",
    "head_semantic_rejection_domain": "Solidity.Backend.AbiEntry.HeadGate.semantic_rejection",
}
# Explicit public-method slice; private helpers and other modules remain out of this renderer.
for gate, prefix in (("HeadGate", "head"), ("WordGate", "word")):
    for method in ("admitted", "selected", "run_program", "executed", "rejected_iff"):
        TARGETS[prefix + "_" + method + "_domain"] = "Solidity.Backend.AbiEntry." + gate + "." + method
    TARGETS[prefix + "_certificate_selected_domain"] = "Solidity.Backend.AbiEntry.Interface." + gate + "Certificate.selected"

for method in ("admitted", "selected", "run_program", "executed", "entry_form",
               "entry_rejection", "entry_success", "short_before_word", "insufficient_fuel"):
    TARGETS["single_" + method + "_domain"] = "Solidity.Backend.AbiEntry.SingleWordGate." + method
for field in ("selected", "executed", "entry_rejection"):
    TARGETS["single_certificate_" + field + "_domain"] = "Solidity.Backend.AbiEntry.Interface.SingleWordGateCertificate." + field

for method in ("admitted", "selected", "code", "run_program", "executed", "entry_rejection",
               "validated_word", "decoded_and_bound", "short_before_word"):
    TARGETS["binding_" + method + "_domain"] = "Solidity.Backend.AbiEntry.BoolBinding." + method
for field in ("selected", "executed", "entry_rejection"):
    TARGETS["binding_certificate_" + field + "_domain"] = "Solidity.Backend.AbiEntry.Interface.BoolBindingCertificate." + field

for gate, prefix, methods in (
    ("UnsignedGate", "unsigned", ("admitted", "selected", "condition_code", "run_program", "executed", "rejected_iff", "enum_rejection", "uint_rejection", "bool_rejection", "enum_correspondence", "uint_correspondence", "bool_correspondence")),
    ("SignedGate", "signed", ("admitted", "selected", "run_program", "executed", "rejected_iff", "correspondence")),
    ("BytesGate", "bytes", ("admitted", "selected", "run_program", "executed"))):
    for method in methods:
        TARGETS[prefix + "_" + method + "_domain"] = "Solidity.Backend.AbiEntry." + gate + "." + method
    for field in ("selected", "executed"):
        TARGETS[prefix + "_certificate_" + field + "_domain"] = "Solidity.Backend.AbiEntry.Interface." + gate + "Certificate." + field

for field in ("correct", "capacity"):
    TARGETS["tail_inherited_" + field + "_domain"] = "Solidity.Backend.AbiEntry.Interface.TailGuardCertificate." + field

for field in ("raw", "reference"):
    TARGETS["raw_tail_" + field + "_domain"] = "Solidity.Backend.AbiEntry.Interface.RawTailGuardCertificate." + field

for method in ("correct", "capacity", "reference"):
    TARGETS["tail_method_" + method + "_domain"] = "Solidity.Backend.AbiEntry.TailGuard." + method
for method in ("raw", "reference"):
    TARGETS["raw_tail_method_" + method + "_domain"] = "Solidity.Backend.AbiEntry.RawTailGuard." + method

for method in ("correct", "capacity", "lazy_revert", "eager_bytes_panic", "eager_array_panic"):
    TARGETS["length_method_" + method + "_domain"] = "Solidity.Backend.AbiEntry.LengthCheck." + method
for field in ("correct", "capacity", "lazy_revert"):
    TARGETS["length_certificate_" + field + "_domain"] = "Solidity.Backend.AbiEntry.Interface.LengthCheckCertificate." + field

for method in ("tail_raw", "region_raw", "tail_correct", "region_correct", "tail_capacity", "region_capacity"):
    TARGETS["offset_method_" + method + "_domain"] = "Solidity.Backend.AbiEntry.OffsetChecks." + method
for field in ("tail_correct", "region_correct", "tail_capacity", "region_capacity"):
    TARGETS["offset_certificate_" + field + "_domain"] = "Solidity.Backend.AbiEntry.Interface.OffsetChecksCertificate." + field


PRODUCERS = ["Solidity/Backend/AbiEntry/" + name + ".lean" for name in
             ("HeadGate", "HeadGateInterface", "WordGate", "WordGateInterface", "SingleWordGate", "SingleWordGateInterface", "BoolBinding", "BoolBindingInterface", "UnsignedGate", "UnsignedGateInterface", "SignedGate", "SignedGateInterface", "BytesGate", "BytesGateInterface", "TailGuard", "TailGuardInterface", "RawTailGuard", "RawTailGuardInterface", "TailGuardControls", "LengthCheck", "LengthCheckInterface", "LengthCheckControls", "OffsetChecks", "OffsetChecksInterface", "OffsetChecksControls")]


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def macro_fragment(source):
    start = "namespace " + NAMESPACE + "\n"
    end = "\nprivate theorem dependentToy"
    if source.count(start) != 1 or source.count(end) != 1:
        raise ValueError("ambiguous existing elaborator boundaries")
    fragment = source[source.index(start):source.index(end)]
    if sha(fragment.encode()) != MACRO_SHA256:
        raise ValueError("existing elaborator implementation changed; review required")
    return fragment


def render(macro_source, fixture):
    found = re.findall(r"(?m)^theorem\s+(\w+)\s*:\s*hypotheses_of%\s+(\S+)\s*:=", mask(fixture))
    if len(found) != len(TARGETS) or dict(found) != TARGETS:
        raise ValueError("exact domain targets differ")
    if re.search(r"\b(?:sorry|admit|axiom|native_decide|unsafe|implemented_by)\b", mask(fixture)):
        raise ValueError("forbidden fixture mechanism")
    fragment = macro_fragment(macro_source)
    return ("import Lean\nimport Solidity.Backend.AbiEntry.HeadGate\n"
            "import Solidity.Backend.AbiEntry.WordGate\nimport Solidity.Backend.AbiEntry.SingleWordGate\nimport Solidity.Backend.AbiEntry.BoolBinding\nimport Solidity.Backend.AbiEntry.RawTailGuard\nimport Solidity.Backend.AbiEntry.TailGuardControls\nimport Solidity.Backend.AbiEntry.LengthCheckControls\nimport Solidity.Backend.AbiEntry.OffsetChecksControls\n\n"
            "/-! Guards omission of implicit/self/proof binders from joint hypotheses.\n"
            "Only the original conclusion is replaced by True; no census acceptance follows. -/\n"
            + fragment + "\n" + fixture + "\nend " + NAMESPACE + "\n")


def build(repo):
    repo = repo.resolve()
    macro_raw = (repo / MACRO_PATH).read_bytes()
    fixture_raw = (repo / FIXTURE_PATH).read_bytes()
    frozen_map = subprocess.check_output(["git", "show", BASE + ":" + MAP], cwd=repo)
    allowed, _ = mapped_references(frozen_map.decode())
    if set(PRODUCERS) - set(allowed):
        raise ValueError("explicit producer outside frozen mapped census: " + ", ".join(sorted(set(PRODUCERS) - set(allowed))))
    producers = {}
    for path in PRODUCERS:
        raw = (repo / path).read_bytes()
        frozen = subprocess.check_output(["git", "show", BASE + ":" + path], cwd=repo)
        if raw != frozen:
            raise ValueError("frozen producer source changed: " + path)
        producers[path] = sha(raw)
    program = render(macro_raw.decode(), fixture_raw.decode())
    manifest = {
        "schema_version": 1, "base": BASE, "targets": TARGETS,
        "scope_map_path": MAP, "scope_map_sha256": sha(frozen_map),
        "producer_scope": "All explicit producer leaves mapped; transitive imports are not assigned targets.",
        "generator_sha256": sha(Path(__file__).read_bytes()),
        "macro_source_path": MACRO_PATH, "macro_source_sha256": sha(macro_raw),
        "macro_fragment_sha256": MACRO_SHA256, "fixture_path": FIXTURE_PATH,
        "fixture_sha256": sha(fixture_raw), "producer_source_sha256": producers,
        "generated_lean_sha256": sha(program.encode()),
        "boundary": "Proof-specific binder domains only; not original conclusions, census or metadata-join acceptance.",
        "inspection_accepted": False, "witness_ledger_links_established": False,
    }
    return program, manifest


def export(repo, output):
    output = output.absolute()
    owner = Path(__file__).resolve().parents[4]
    if any(output.resolve().is_relative_to(root.resolve()) for root in (repo, owner)):
        raise ValueError("H44: generated proofs must remain outside repositories")
    if any(p.is_symlink() for p in (output, *output.parents)):
        raise ValueError("symlink output refused")
    manifest_path = output.with_suffix(".manifest.json")
    if output.exists() or manifest_path.exists():
        raise ValueError("existing output refused")
    program, manifest = build(repo)
    with output.open("x") as stream:
        stream.write(program)
    with manifest_path.open("x") as stream:
        stream.write(json.dumps(manifest, sort_keys=True, indent=2) + "\n")
    return manifest


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", required=True, type=Path)
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args()
    result = export(args.repo, args.output)
    print(json.dumps({"targets": result["targets"], "inspection_accepted": False}, sort_keys=True))


if __name__ == "__main__":
    main()
