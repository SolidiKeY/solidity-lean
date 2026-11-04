#!/usr/bin/env python3
"""SOL-EU audit. --inventory is static; --checkpoint validates partial proof evidence.
Default full acceptance stays closed while the original uniqueness target is open.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

BASE = "6f3eedf0788ee1f8a3bcf230558c712ecdca04d5"
ROOT = Path(__file__).resolve().parents[1]
DATA = ROOT / "tests/sol-expression-uniqueness"
AREA = ROOT / "Solidity/Frontend/ExpressionUniqueness"
STANDARD = {"propext", "Classical.choice", "Quot.sound"}


def read(name):
    return json.loads((DATA / name).read_text())


def require(ok, message):
    if not ok:
        raise ValueError(message)


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def declarations():
    rows = []
    for path in sorted(AREA.glob("*.lean")):
        source = path.read_text()
        matches = list(re.finditer(r"^(def|theorem|inductive)\s+(\w+)", source, re.M))
        for i, match in enumerate(matches):
            segment = source[match.start():matches[i+1].start() if i+1 < len(matches) else len(source)]
            rows.append(dict(module=path.relative_to(ROOT).with_suffix("").as_posix().replace("/", "."),
                             kind=match[1], name="Solidity.Frontend.ExpressionUniqueness."+match[2],
                             source_signature=segment.split(":=", 1)[0].strip()))
    return rows


def audit_runs():
    runs = read("audit-runs.json")
    require(set(runs) == {"proof_stem", "proof_gate_dir", "signature_stem", "signature_gate_dir"} and
            all(re.fullmatch(r"[a-z][a-z0-9-]*", value) for value in runs.values()), "invalid audit run references")
    return runs


def actual_axiom_report():
    runs = audit_runs()
    path = DATA/"evidence"/runs["signature_gate_dir"]/"1.log"
    require(path.is_file(), "actual axiom report missing")
    pattern = r"^'([^'\n]+)' (?:does not depend on any axioms|depends on axioms: \[([^\]]*)\])$"
    reported, messages = {}, {}
    for match in re.finditer(pattern, path.read_text(), re.M):
        require(match[1] not in reported, "duplicate actual axiom report")
        messages[match[1]] = match[0]
        reported[match[1]] = [x.strip() for x in match[2].split(",") if x.strip()] if match[2] else []
    return reported, messages


def audit_checkpoint(modules, decls, axioms):
    runs = audit_runs()
    proof = read("evidence/"+runs["proof_stem"]+".inside.json")
    outer = read("evidence/"+runs["proof_stem"]+".outer.json")
    current = {name: digest(ROOT/name) for name in modules}
    require(proof["exit"] == outer["exit"] == 0 and not outer["resource_stop"], "proof gate failed")
    require(proof["source_hashes"] == current, "proof evidence is stale for current modules")
    require(proof["memory_max"] == 12884901888 and proof["memory_swap_max"] == 0 and
            proof["lean_num_threads"] == 1, "runtime bounds mismatch")
    require(outer["minimum_parent_headroom_bytes"] >= 4294967296, "H1 reserve failed")
    log = (DATA/"evidence"/(runs["proof_stem"]+".log")).read_text()
    require("RUNTIME_GATE_PASS" in log and "377 taclets, 131 read-bearing" in log and
            "diag: 0 errors" in log, "runtime/KeySort/MCP evidence missing")
    gate = (DATA/"evidence"/runs["proof_gate_dir"]/"gates.tsv").read_text().splitlines()
    require(len(gate) == 1 and gate[0].startswith("PASS\tlean:Solidity/Frontend/ExpressionUniqueness/AxiomPins.lean\t"),
            "axiom pin kernel gate missing")
    signature = read("evidence/"+runs["signature_stem"]+".inside.json")
    signature_outer = read("evidence/"+runs["signature_stem"]+".outer.json")
    require(signature["exit"] == signature_outer["exit"] == 0 and not signature_outer["resource_stop"],
            "signature build/audit command failed")
    require(signature["memory_max"] == 12884901888 and signature["memory_swap_max"] == 0 and
            signature["lean_num_threads"] == 1 and
            signature_outer["minimum_parent_headroom_bytes"] >= 4294967296,
            "signature runtime/reserve mismatch")
    signature_gate = (DATA/"evidence"/runs["signature_gate_dir"]/"gates.tsv").read_text().splitlines()
    require(len(signature_gate) == 1 and signature_gate[0].startswith(
        "PASS\tlean:tests/sol-expression-uniqueness/signatures.lean\t"), "signature kernel gate missing")
    pin_path = "Solidity/Frontend/ExpressionUniqueness/AxiomPins.lean"
    require({k:v for k,v in signature["source_hashes"].items() if k != pin_path} ==
            {k:v for k,v in current.items() if k != pin_path}, "signature evidence is stale")
    reported, _ = actual_axiom_report()
    require(reported == axioms, "actual axiom report differs from pins")
    compiler = read("evidence/compiler-0.8.38.json")
    require(compiler["pin"]["sha256"] == "6c74ffba0ea4cf9521e78b16052a98208770bb7677616de08ced239f4312d390" and
            compiler["pin"]["version"] == "0.8.38+commit.1835d247.Emscripten.clang", "compiler pin mismatch")
    observations = compiler["observations"]
    ops = ["||", "&&", "==", "<", "|", "^", "&", "<<", "+", "*", "**"]
    expected_ids = {"association-"+op for op in ops}
    expected_ids |= {f"precedence-{lo}-{hi}-{side}" for i,lo in enumerate(ops)
                     for hi in ops[i+1:] for side in ("left", "right")}
    expected_ids |= {"assignment-association", "conditional-association", "prefix-postfix-solc-reading",
                     "conditional-assignment-solc-reading", "postfix-member-refused", "postfix-postfix-refused",
                     "group-prefix-postfix", "group-conditional-assignment", "group-postfix-member"}
    require(len(observations) == len({r["id"] for r in observations}) == 130 and
            {r["id"] for r in observations} == expected_ids, "compiler case inventory mismatch")
    for row in observations:
        require(hashlib.sha256(row["source"].encode()).hexdigest() == row["sourceSha256"], "compiler source hash mismatch")
        require(row["actual"] == row["expected"], "compiler observation differs")
        require(not row["errors"] if row["expected"] is not None else
                any(e["type"] == "ParserError" for e in row["errors"]), "compiler refusal stage differs")
    require(read("evidence/compiler-pinned.inside.json")["exit"] == 0, "external compiler command failed")
    print("CHECKPOINT_PASS: exact current proof sources, standard axiom pins, runtime and 130 external parsing controls")
    print("Partial checkpoint only: expression root reconstruction and global uniqueness remain OPEN.")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    modes = parser.add_mutually_exclusive_group()
    modes.add_argument("--inventory", action="store_true")
    modes.add_argument("--checkpoint", action="store_true")
    args = parser.parse_args()
    pins = read("source-pins.json")
    required = {"Solidity/Frontend/Checked/"+n+".lean" for n in
                ("Print", "Prec", "Parser", "Check", "Token", "ExprExamples")}
    required |= {"Solidity/Source/Syntax.lean", "tests/upstream/grammar-0.8.38/SolidityParser.g4"}
    require(set(pins) == required, "source pin inventory differs from mandatory inputs")
    for name, expected in pins.items():
        frozen = subprocess.check_output(["git", "show", BASE+":"+name], cwd=ROOT)
        require(digest(ROOT/name) == hashlib.sha256(frozen).hexdigest() == expected, "source pin mismatch: "+name)
    block = (ROOT/"Solidity/Source/Syntax.lean").read_text().split(
        "  -- Expressions, one constructor per labelled alternative.")[1].split("  -- Simple statements.")[0]
    constructors = re.findall(r"^  \| (\w+)", block, re.M)
    ledger = read("constructors.json")
    require([r["constructor"] for r in ledger] == constructors, "intrinsic constructor inventory differs")
    for row in ledger:
        require(all(row[k] for k in ("boundary", "precNode", "layout", "root_reconstruction", "uniqueness", "controls")),
                "missing constructor obligation")
        require(0 <= row["level"] <= 16, "invalid precedence level")
    obligations = read("obligations.json")
    require([r["id"] for r in obligations] == [f"EU-{i:02}" for i in range(1, 15)], "obligation inventory differs")
    require(all(r["status"] == "open" for r in obligations if r["id"] in {"EU-04", "EU-07", "EU-08", "EU-14"}),
            "open target changed: extend actual proof acceptance before closing obligations")
    modules = sorted(p.relative_to(ROOT).as_posix() for p in AREA.glob("*.lean"))
    manifest = read("registration-manifest.json")
    decls = declarations()
    require(manifest["base"] == BASE and manifest["modules"] == modules, "module registration inventory differs")
    require(read("declarations.json") == decls and manifest["declarations"] == [d["name"] for d in decls],
            "declaration/signature inventory differs")
    require([r["module"] for r in manifest["module_map_rows"]] == [m[9:] for m in modules], "module-map proposals differ")
    central = manifest["central_axiom_registration"]
    require(central["file"] == "scripts/g07-axiom-pins.json" and
            central["source"] == "tests/sol-expression-uniqueness/axioms.json" and
            central["count"] == len(decls), "central axiom registration proposal differs")
    names = [d["name"] for d in decls]
    controls = read("constructor-controls.json")
    require([r["constructor"] for r in controls] == constructors and
            all(r["theorem"] in names and r["input"] for r in controls), "constructor fixtures incomplete")
    by_name = {d["name"]: d for d in decls}
    for row in controls:
        ctor = row["constructor"]
        name = "Solidity.Frontend.ExpressionUniqueness.constructor_"+ctor
        expected_signature = "theorem constructor_"+ctor+" : expressionCtor "+json.dumps(row["input"])+" = some ."+ctor
        require(row["theorem"] == name and by_name[name]["kind"] == "theorem" and
                by_name[name]["source_signature"] == expected_signature,
                "constructor fixture statement/input linkage differs: "+ctor)
    axioms = read("axioms.json")
    require(set(axioms) == set(names) and all(set(a) <= STANDARD for a in axioms.values()), "axiom inventory differs")
    imports = sorted({d["module"] for d in decls})
    expected = "\n".join("import "+m for m in imports)+"\n\n/-! Exact kernel-reported axiom pins for every source declaration in this lane. -/\n\n"
    reported, messages = actual_axiom_report()
    require(reported == axioms, "actual axiom report differs from pins")
    for name in names:
        msg = messages[name]
        expected += f"/-- info: {msg} -/\n#guard_msgs in #print axioms {name}\n\n"
    require((AREA/"AxiomPins.lean").read_text() == expected.rstrip()+"\n", "axiom guards differ from full declaration inventory")
    signature_source = "\n".join("import "+m for m in imports)+"\n\n"+"".join(
        "#check "+n+"\n#print axioms "+n+"\n" for n in names)
    require((DATA/"signatures.lean").read_text() == signature_source, "kernel signature audit omits declarations")
    print(f"INVENTORY_PASS: {len(constructors)} constructors; {len(modules)} modules; {len(decls)} source declarations; {len(pins)} source pins")
    for row in obligations:
        print(f'{row["id"]}: {row["status"]}: {row["obligation"]}')
    if args.checkpoint:
        audit_checkpoint(modules, decls, axioms)
        return 0
    if args.inventory:
        print("Static inventory only; no full task acceptance claimed.")
        return 0
    print("ACCEPTANCE_OPEN: original certified expression uniqueness, root reconstruction, accepted-tree corollary and full final gates remain open.", file=sys.stderr)
    return 1


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (ValueError, KeyError, IndexError, OSError, subprocess.CalledProcessError) as error:
        print("AUDIT_FAIL: "+str(error), file=sys.stderr)
        sys.exit(2)
