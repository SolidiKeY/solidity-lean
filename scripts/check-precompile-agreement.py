#!/usr/bin/env python3
"""Bounded B16 row/fixture/evidence gate; never a crypto or full-B16 claim.

--inventory-only checks source, theorem and fixture coverage without trusting
saved kernel receipts. Default also checks fresh-source-bound kernel evidence.
Run tests/precompile-agreement/verify.py in Bridge to regenerate that evidence.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import sys
import subprocess
import shlex

ROOT = Path(__file__).resolve().parents[1]
INVENTORY = ROOT / "Bridge/tests/precompile-agreement/inventory.json"
TESTS = ROOT / "Bridge/tests/precompile-agreement"
PROOFS = ROOT / "Bridge/SolidityBridge/PrecompileAgreement"
NAMESPACE = "SolidityBridge.PrecompileAgreement."
COVERAGE = json.loads((TESTS / "required-coverage.json").read_text())
COVERAGE_SHA256 = "4dc87074a98874b3370dc85b63f95a60a5e47838a10a8da0c9fb2cabed79c791"
BASE = "b6ba0696102a7a038afe2ed333c09dff397cc5b2"
CLASSIFICATIONS = {
    "common-gas-external-output", "identity-candidate", "fork-mismatch",
    "header-domain-mismatch", "unsupported-vendor",
}


def validate(data):
    errors = []
    if data.get("schema") != 2 or data.get("base") != BASE:
        errors.append("wrong schema or base")
    if hashlib.sha256((TESTS / "required-coverage.json").read_bytes()).hexdigest() != COVERAGE_SHA256:
        errors.append("reviewed theorem/fixture mapping changed")
    source = (ROOT / "Solidity/Roadmap/Evm.lean").read_text()
    address_part = source.split("def Precompile.address", 1)[1].split("def Precompile.all", 1)[0]
    actual = {name: int(address, 16) for name, address in
              re.findall(r"\| \.(\w+) => (0x[0-9a-f]+)", address_part)}
    rows = data.get("rows", [])
    if len(actual) != 18 or len(rows) != 18:
        errors.append("expected exactly 18 addresses")
    if len({r["name"] for r in rows}) != len(rows) or len({r["address"] for r in rows}) != len(rows):
        errors.append("duplicate name/address")
    if {r["name"]: r["address"] for r in rows} != actual:
        errors.append("source address coverage mismatch")
    required_pins = {"Solidity/Roadmap/Evm.lean", "Bridge/lake-manifest.json",
                     "Bridge/vendor/EvmYul/EVM/PrecompiledContracts.lean",
                     "Bridge/vendor/EvmYul/EVM/Semantics.lean",
                     "Bridge/vendor/EvmYul/FFI/ffi.lean", "Bridge/lean-toolchain"}
    required_pins.update(str(p.relative_to(ROOT)) for p in
                         (ROOT / "Solidity/Precompiles").glob("*.lean"))
    for directory in ("Bridge/vendor/EvmYul", "Bridge/vendor/Conform"):
        required_pins.update(str(p.relative_to(ROOT)) for p in
                             (ROOT / directory).rglob("*.lean"))
    required_pins.update("Bridge/vendor/EvmYul/" + name for name in
                         ("VENDOR.md", "SHA256SUMS", "UPSTREAM_SHA256SUMS",
                          "h7-bounded-scanner-padding-pin.json"))
    core_seen = set()
    def visit_core(name):
        if name in core_seen: return
        core_seen.add(name)
        path = name.replace(".", "/") + ".lean"
        required_pins.add(path)
        for line in (ROOT / path).read_text().splitlines():
            if line.startswith("import "):
                for dependency in line.split()[1:]:
                    if dependency.startswith("Solidity."): visit_core(dependency)
    visit_core("Solidity.Precompiles.Osaka")
    pins = data.get("pins", {})
    if not required_pins <= pins.keys():
        errors.append("missing required input pins")
    for name, expected in pins.items():
        path = ROOT / name
        if not path.is_file() or hashlib.sha256(path.read_bytes()).hexdigest() != expected:
            errors.append("hash mismatch: " + name)
    vendor = (ROOT / "Bridge/vendor/EvmYul/EVM/PrecompiledContracts.lean").read_text()
    dispatch = (ROOT / "Bridge/vendor/EvmYul/EVM/Semantics.lean").read_text()
    dispatch_pairs = {int(address): definition for address, definition in re.findall(
        r"\| (\d+)\s*=> \.ok <\| \(∅, (Ξ_\w+)", dispatch)}
    if set(dispatch_pairs) != set(range(1, 11)):
        errors.append("vendor dispatch coverage changed")
    modules = {1: "Basic", 2: "Basic", 3: "Basic", 4: "Basic", 5: "Modexp",
               6: "Bn254", 7: "Bn254", 8: "Bn254", 9: "Blake2f", 10: "PointEval",
               **{address: "Bls12381" for address in range(11, 18)}, 256: "P256"}
    classes = {**{address: "common-gas-external-output" for address in (1, 2, 3, 6, 7, 8, 10)},
               4: "identity-candidate", 5: "fork-mismatch", 9: "header-domain-mismatch",
               **{address: "unsupported-vendor" for address in (*range(11, 18), 256)}}
    for row in rows:
        expected_module = "Solidity/Precompiles/" + modules.get(row["address"], "MISSING") + ".lean"
        if row.get("core_module") != expected_module or expected_module not in pins:
            errors.append(row["name"] + ": wrong/unpinned core module")
        if row.get("classification") != classes.get(row["address"]):
            errors.append(row["name"] + ": changed source classification")
        for field in ("core_module", "core_gas", "length", "malformed", "vendor_behavior", "controls"):
            if not row.get(field):
                errors.append(row["name"] + ": missing " + field)
        if row.get("classification") not in CLASSIFICATIONS:
            errors.append(row["name"] + ": bad classification")
        if row["address"] <= 10:
            definition = row.get("vendor_definition")
            if (definition != dispatch_pairs.get(row["address"]) or not definition or
                    "def " + definition + "\n" not in vendor or not row.get("vendor_gas")):
                errors.append(row["name"] + ": missing actual vendor definition")
        elif row.get("vendor_definition") is not None or row["classification"] != "unsupported-vendor":
            errors.append(row["name"] + ": unsupported row misclassified")
        required = COVERAGE.get(str(row["address"]), {})
        for field in ("proof_status", "proofs", "fixture_theorems"):
            if row.get(field) != required.get(field):
                errors.append(row["name"] + ": required theorem/fixture/status mismatch: " + field)
        address = row["address"]
        charge = ("unavailable-vendor" if address > 10 else "fork-mismatch" if address == 5 else
                  "actual-success-flag-common-header-domain" if address == 9 else
                  "actual-success-flag" if address in (6,7,8,10) else "affordability-branch")
        domain = ("no-vendor" if address > 10 else "no-universal-agreement" if address == 5 else
                  "size>=4-or-zero-header" if address == 9 else "all-inputs")
        if row.get("charge_model") != charge or row.get("agreement_domain") != domain:
            errors.append(row["name"] + ": malformed-input charge/domain boundary changed")
        output = ("kernel-arbitrary-bytes" if row["address"] == 4 else
                  "open-unsupported" if row["address"] > 10 else
                  "fork-mismatch" if row["address"] == 5 else "open-crypto-or-ffi")
        if row.get("output_agreement") != output:
            errors.append(row["name"] + ": output boundary changed")
        if row.get("boundary_suite") != "Bridge/tests/precompile-agreement/BoundaryVectors.lean":
            errors.append(row["name"] + ": boundary suite missing")
        funcs = {1:"ecrecover",2:"sha256",3:"ripemd160",4:"identity",5:"modexp",6:"add",7:"mul",8:"pairing",9:"blake2f",10:"pointEval",11:"g1Add",12:"g1Msm",13:"g2Add",14:"g2Msm",15:"pairing",16:"mapFpToG1",17:"mapFp2ToG2",256:"p256Verify"}
        func = funcs.get(row["address"], "__invalid_address__")
        prefixes = [func, func+"Gas"] + (["gas"] if row["address"] in (5,9,10,256) else [])
        vector_source = ROOT / row["core_module"]
        vector_lines = vector_source.read_text().splitlines() if vector_source.is_file() else []
        expected_refs = [{"path": row["core_module"], "line": j,
                          "sha256": hashlib.sha256(line.encode()).hexdigest()}
                         for j, line in enumerate(vector_lines, 1)
                         if any(re.match(r"^#guard " + f + r"\b", line) for f in prefixes)]
        if row.get("core_vector_refs") != expected_refs:
            errors.append(row["name"] + ": incomplete core vector mapping")
        refs = row.get("core_vector_refs", [])
        if not refs:
            errors.append(row["name"] + ": core vector references missing")
        for ref in refs:
            path = ROOT / ref["path"]
            lines = path.read_text().splitlines() if path.is_file() else []
            line = lines[ref["line"]-1] if 0 < ref["line"] <= len(lines) else ""
            if (ref["path"] != row["core_module"] or not line.startswith("#guard ") or
                    hashlib.sha256(line.encode()).hexdigest() != ref["sha256"]):
                errors.append(row["name"] + ": invalid source vector reference")
    if data.get("status") != "bounded-kernel-agreement":
        errors.append("wrong bounded acceptance status")
    if data.get("vendor_commit") != "047f63070309f436b66c61e276ab3b6d1169265a" or data.get("mathlib_commit") != "f897ebcf72cd16f89ab4577d0c826cd14afaafc7":
        errors.append("vendor/Mathlib revision changed")
    declarations = public_declarations()
    recorded = json.loads((TESTS / "declarations.json").read_text())
    if set(recorded) != set(declarations) or len(recorded) != len(declarations):
        errors.append("public declaration inventory mismatch")
    for row in rows:
        for name in row.get("proofs", []) + row.get("fixture_theorems", []):
            if name not in declarations:
                errors.append("unknown theorem: " + name)
    for name in ("address_table", "address_complete"):
        if NAMESPACE + name not in declarations:
            errors.append("address completeness theorem missing")
    # Compare pins to the published assignment base, not merely editable hashes.
    for name, digest in pins.items():
        blob = subprocess.run(["git", "show", BASE + ":" + name], cwd=ROOT,
                              stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        if blob.returncode or hashlib.sha256(blob.stdout).hexdigest() != digest:
            errors.append("input differs from pinned published base: " + name)
    return errors


def public_declarations():
    result = {}
    for path in sorted(PROOFS.glob("*.lean")):
        prefix = NAMESPACE + ("Controls." if path.stem == "Controls" else "")
        for name in re.findall(r"^(?:theorem|def) (\w+)", path.read_text(), re.M):
            result[prefix + name] = str(path.relative_to(ROOT))
    return result


def logical_input_closure():
    seen, order = set(), []
    def visit(name):
        if name in seen: return
        seen.add(name)
        if name.startswith("Solidity."):
            path = name.replace(".", "/") + ".lean"
        elif name.startswith(("EvmYul.", "Conform.")):
            path = "Bridge/vendor/" + name.replace(".", "/") + ".lean"
        else:
            return  # external package cache; exact revisions stay manifest-pinned
        for line in (ROOT / path).read_text().splitlines():
            if line.startswith("import "):
                for dep in line.split()[1:]: visit(dep)
        order.append(path)
    visit("Solidity.Precompiles.Osaka")
    visit("EvmYul.EVM.PrecompiledContracts")
    return order


def kernel_log_errors(name, content):
    stem = name.removesuffix("-kernel.log")
    module = (PROOFS / (stem + ".lean")).is_file()
    source = ("SolidityBridge/PrecompileAgreement/" if module else "tests/precompile-agreement/") + stem + ".lean"
    expected = ["env", "lean", "-j1", "-M11264", "--tstack=131072"]
    if module: expected += ["-o", ".lake/build/lib/lean/" + source.removesuffix(".lean") + ".olean"]
    expected += [source]
    commands = re.findall(r"^COMMAND: (.+)$", content, re.M)
    if len(commands) != 1 or Path(shlex.split(commands[0])[0]).name != "lake" or shlex.split(commands[0])[1:] != expected:
        return ["kernel log/source command mismatch: " + name]
    if re.findall(r"^CWD: (.+)$", content, re.M) != [str(ROOT / "Bridge")]:
        return ["kernel log working-directory mismatch: " + name]
    if len(re.findall(r"^EXIT=.*$", content, re.M)) != 1:
        return ["kernel log has missing/duplicate outcomes: " + name]
    footer = re.search(r"\nEXIT=0 SECONDS=([0-9.]+) PEAK_RSS=(\d+) MIN_AVAILABLE=(\d+) RESOURCE_STOP=False\n\Z", content)
    if (not footer or float(footer[1]) <= 0 or not 0 < int(footer[2]) <= 12*1024**3 or
            int(footer[3]) < 4*1024**3 or "error:" in content or "warning:" in content):
        return ["kernel log failed/resource-invalid: " + name]
    return []


def input_build_errors(data, build):
    expected = logical_input_closure()
    headers = list(re.finditer(r"^(\d+)/(\d+) SHA256=(\w+) CWD=(\S+) COMMAND=([^\n]+)$", build, re.M))
    if len(headers) != len(expected):
        return ["pinned input build does not contain the exact logical closure"]
    errors, paths = [], []
    for i, h in enumerate(headers):
        command = shlex.split(h[5])
        if Path(h[4]) != (ROOT / "Bridge" if command[-1].startswith("vendor/") else ROOT):
            errors.append("pinned input build working-directory mismatch")
        source = command[-1]
        path = "Bridge/" + source if source.startswith("vendor/") else source
        paths.append(path)
        if (int(h[1]) != i+1 or int(h[2]) != len(expected) or
                data["pins"].get(path) != h[3] or path != expected[i]):
            errors.append("pinned input build ordinal/source/hash mismatch: " + path)
        flags = ["-j1", "-M11264", "--tstack=131072"]
        if source.startswith("vendor/"): flags += ["--root=vendor"]
        module_source = source.removeprefix("vendor/")
        output = str(Path(h[4]) / ".lake/build/lib/lean" / (module_source.removesuffix(".lean") + ".olean"))
        if Path(command[0]).name != "lean" or command[1:] != flags + ["-o", output, source]:
            errors.append("pinned input build flags mismatch: " + path)
        block = build[h.end():headers[i+1].start() if i+1 < len(headers) else len(build)]
        footers = re.findall(r"^EXIT=(\d+) SECONDS=([0-9.]+) PEAK_RSS=(\d+) MIN_AVAILABLE=(\d+)$", block, re.M)
        if (len(re.findall(r"^EXIT=.*$", block, re.M)) != 1 or len(footers) != 1 or footers[0][0] != "0" or float(footers[0][1]) <= 0 or
                not 0 < int(footers[0][2]) <= 12*1024**3 or int(footers[0][3]) < 4*1024**3):
            errors.append("pinned input build outcome/resource mismatch: " + path)
    if paths != expected or len(set(paths)) != len(expected) or "RESOURCE_GUARD_STOP" in build:
        errors.append("pinned input build omitted/duplicated a required module")
    return errors


def evidence_errors(data, receipt):
    errors = []
    if receipt.get("status") != "pass":
        errors.append("kernel receipt is not a pass")
    if receipt.get("inputs") != data["pins"]:
        errors.append("kernel input receipt mismatch")
    required = {str(p.relative_to(ROOT)) for p in PROOFS.glob("*.lean")}
    required |= {"scripts/check-precompile-agreement.py"}
    required |= {"Bridge/tests/precompile-agreement/" + p for p in
                 ("Acceptance.lean", "Axioms.lean", "AllDeclarations.lean", "BoundaryVectors.lean",
                  "ActualAxioms.lean", "required-coverage.json", "declarations.json", "axiom-pins.json",
                  "inventory.json", "run-file.py", "verify.py")}
    hashes = receipt.get("sources", {})
    if set(hashes) != required:
        errors.append("kernel source receipt coverage mismatch")
    for name in required:
        path = ROOT / name
        if not path.is_file() or hashlib.sha256(path.read_bytes()).hexdigest() != hashes.get(name):
            errors.append("stale kernel source receipt: " + name)
    expected_logs = {p.stem + "-kernel.log" for p in PROOFS.glob("*.lean")}
    expected_logs |= {n + "-kernel.log" for n in ("Acceptance", "Axioms", "BoundaryVectors", "AllDeclarations", "ActualAxioms")}
    if set(receipt.get("logs", {})) != expected_logs:
        errors.append("kernel log coverage mismatch")
    for name, digest in receipt.get("logs", {}).items():
        path = TESTS / "evidence" / name
        content = path.read_text() if path.is_file() else ""
        if hashlib.sha256(content.encode()).hexdigest() != digest:
            errors.append("stale kernel gate: " + name)
        errors.extend(kernel_log_errors(name, content))
    pins = json.loads((TESTS / "axiom-pins.json").read_text())
    if set(pins) != set(public_declarations()):
        errors.append("axiom pin coverage mismatch")
    if any(not set(value) <= {"propext", "Classical.choice", "Quot.sound"} for value in pins.values()):
        errors.append("nonstandard axiom pin")
    audit = (TESTS / "evidence/AllDeclarations-kernel.log").read_text()
    if not re.search(r"ALL_DECLARATIONS_PASS count=[1-9][0-9]*", audit):
        errors.append("all-declaration axiom audit missing")
    build = (TESTS / "evidence/pinned-input-build.log").read_text()
    errors.extend(input_build_errors(data, build))
    if receipt.get("input_build_sha256") != hashlib.sha256(build.encode()).hexdigest():
        errors.append("pinned input build receipt mismatch")
    return errors




def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--inventory-only", action="store_true")
    args = parser.parse_args()
    errors = validate(json.loads(INVENTORY.read_text()))
    if errors:
        print("FAIL: " + "\nFAIL: ".join(errors))
        return 1
    print("PASS scope map: 18 addresses, actual vendor definitions, fixed input hashes and required theorems/fixtures")
    if args.inventory_only:
        print("Mapping only; no saved kernel receipt or native/cryptographic equality claim")
        return 0
    path = TESTS / "evidence/kernel-receipt.json"
    if not path.is_file():
        print("FAIL: kernel receipt absent; run the serial verify.py gate")
        return 1
    errors = evidence_errors(json.loads(INVENTORY.read_text()), json.loads(path.read_text()))
    if errors:
        print("FAIL: " + "\nFAIL: ".join(errors))
        return 1
    print("PASS bounded kernel evidence: IDENTITY, common gas rows, header domains, mismatch/negative controls, standard axiom pins")
    print("OPEN: native crypto/FFI output equality, MODEXP fork, unsupported addresses, central registration/full repository gate")
    return 0


if __name__ == "__main__":
    sys.exit(main())
