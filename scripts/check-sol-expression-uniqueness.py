#!/usr/bin/env python3
"""SOL-EU audit. All modes run the static inventory and proof-scope checks
(unchanged target, constructor/operator/boundary ledgers, exact pin text).
--checkpoint --build-log LOG adds the kernel evidence: a full ./run-lean.sh at
the current sources (tests/sol-expression-uniqueness/gate.sh writes LOG).
--proof is the static proof-scope check alone. --external-evidence re-checks the
H44 Codex-VM evidence when tests/sol-expression-uniqueness/evidence/ and the
kernel-*.json dumps are restored. The default mode is full acceptance.
"""
import argparse
import hashlib
import gzip
from collections import Counter
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
    for path in sorted(AREA.rglob("*.lean")):
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


PIN_PATTERN = r"^/-- info: ('([^'\n]+)' (?:does not depend on any axioms|depends on axioms: \[([^\]]*)\])) -/$"


def actual_axiom_report():
    """The kernel's axiom report, as pinned by `#guard_msgs` in AxiomPins.lean.

    Lean re-checks every pinned message when it builds that module (part of
    `lake build Solidity`), so a passing library build is the kernel evidence
    that each message below is exactly what `#print axioms` reports.  The
    Codex-VM log this function used to read was externalized under H44.
    """
    path = AREA/"AxiomPins.lean"
    require(path.is_file(), "AxiomPins.lean missing")
    reported, messages = {}, {}
    for match in re.finditer(PIN_PATTERN, path.read_text(), re.M):
        require(match[2] not in reported, "duplicate actual axiom report")
        messages[match[2]] = match[1]
        reported[match[2]] = [x.strip() for x in match[3].split(",") if x.strip()] if match[3] else []
    return reported, messages


_ENVIRONMENT_AUDIT_CACHE = {}


def stream_environment_emissions(archive, compression, declared):
    compressed = digest(archive)
    require(compressed == compression["compressed_sha256"] and
            archive.stat().st_size == compression["compressed_bytes"], "compressed actual Lean output differs")
    counts = Counter(name for module in declared for name in module["constants"])
    key = (str(archive), compressed, compression["uncompressed_sha256"], compression["uncompressed_bytes"],
           tuple(sorted(counts.items())))
    if key in _ENVIRONMENT_AUDIT_CACHE:
        return _ENVIRONMENT_AUDIT_CACHE[key]
    raw_hash, raw_size = hashlib.sha256(), 0
    remaining = counts.copy()
    duplicate_types, rows = {}, []
    prefix = b"OWNED_KERNEL_DECL "
    with gzip.open(archive, "rb") as source:
        for line in source:
            raw_hash.update(line)
            raw_size += len(line)
            if not line.startswith(prefix):
                continue
            row = json.loads(line[len(prefix):])
            typ = row.pop("type_expr")
            require(isinstance(typ, str) and typ, "missing actual full kernel type")
            name = row["name"]
            require(name in counts and remaining[name] > 0, "unexpected/duplicate kernel emission name")
            if counts[name] > 1:
                if name in duplicate_types:
                    require(duplicate_types[name] == typ, "re-emitted full kernel types differ")
                else:
                    duplicate_types[name] = typ
            remaining[name] -= 1
            if remaining[name] == 0:
                duplicate_types.pop(name, None)
            encoded = typ.encode()
            row["type_expr_sha256"] = hashlib.sha256(encoded).hexdigest()
            row["type_expr_bytes"] = len(encoded)
            rows.append(row)
    require(raw_size == compression["uncompressed_bytes"] and
            raw_hash.hexdigest() == compression["uncompressed_sha256"], "lossless actual Lean output digest differs")
    require(all(count == 0 for count in remaining.values()) and not duplicate_types,
            "actual kernel emission stream is incomplete")
    _ENVIRONMENT_AUDIT_CACHE[key] = rows
    return rows


def audit_kernel_environment(modules, decls, axioms):
    summary = read("environment-summary.json")
    current = {name: digest(ROOT/name) for name in modules}
    role_sources = {"names": "tests/sol-expression-uniqueness/environment-names.lean",
                    "audit": "tests/sol-expression-uniqueness/environment-audit.lean"}
    outputs = {}
    for role, source in role_sources.items():
        run = summary[role]
        require(run["source"] == source and run["source_sha256"] == digest(ROOT/source),
                "environment verifier source hash differs: "+role)
        require(re.fullmatch(r"[a-z][a-z0-9-]*", run["stem"]) and
                re.fullmatch(r"[a-z][a-z0-9-]*", run["gate_dir"]), "invalid environment run reference")
        inside = read("evidence/"+run["stem"]+".inside.json")
        outer = read("evidence/"+run["stem"]+".outer.json")
        require(inside["exit"] == outer["exit"] == 0 and not outer["resource_stop"],
                "environment audit command failed: "+role)
        require(inside["memory_max"] == 12884901888 and inside["memory_swap_max"] == 0 and
                inside["lean_num_threads"] == 1 and outer["minimum_parent_headroom_bytes"] >= 4294967296,
                "environment runtime/reserve differs: "+role)
        require(inside["source_hashes"] == current and
                inside["verification_hashes"][source] == run["source_sha256"],
                "environment audit library or executed-tool snapshot is stale: "+role)
        gate = (DATA/"evidence"/run["gate_dir"]/"gates.tsv").read_text().splitlines()
        require(len(gate) == 1 and gate[0].startswith("PASS\tlean:"+source+"\t"),
                "environment kernel/tool gate missing: "+role)
        if role == "names":
            outputs[role] = (DATA/"evidence"/run["gate_dir"]/"1.log").read_text()
    def records(role, prefix):
        return [json.loads(line[len(prefix):]) for line in outputs[role].splitlines() if line.startswith(prefix)]
    declared = records("names", "OWNED_KERNEL_MODULE ")
    require(summary["compression_catalog_sha256"] == digest(DATA/"environment-compression.json"),
            "lossless output archive catalog differs")
    original = "tests/sol-expression-uniqueness/evidence/"+summary["audit"]["gate_dir"]+"/1.log"
    archives = [row for row in read("environment-compression.json") if row["original"] == original]
    require(len(archives) == 1 and archives[0]["archive"] == original+".gz" and
            summary["audit"]["log_archive"] == archives[0]["archive"], "actual full type trace archive missing")
    emissions = stream_environment_emissions(ROOT/archives[0]["archive"], archives[0], declared)
    require(declared == read("kernel-module-declarations.json") and emissions == read("kernel-emissions.json"),
            "kernel declaration inventories differ from actual Lean output")
    for key, path in (("module_inventory_sha256", "kernel-module-declarations.json"),
                      ("emission_inventory_sha256", "kernel-emissions.json"),
                      ("kernel_inventory_sha256", "kernel-declarations.json")):
        require(summary[key] == digest(DATA/path), "kernel inventory digest differs: "+path)
    expected_modules = {name[:-5].replace("/", ".") for name in modules}
    require(len(declared) == len(expected_modules) and {row["module"] for row in declared} == expected_modules,
            "environment module coverage differs")
    expected = [(row["module"], name) for row in declared for name in row["constants"]]
    actual = [(row["module"], row["name"]) for row in emissions]
    require(len(expected) == len(set(expected)) == len(actual) == len(set(actual)) and set(expected) == set(actual),
            "kernel emission audit missing/duplicate rows")
    owners = {}
    for module in declared:
        require([row["name"] for row in module["ownership"]] == module["constants"],
                "kernel ownership coverage differs")
        for row in module["ownership"]:
            require(row["owner"] in expected_modules and
                    (row["name"] not in owners or owners[row["name"]] == row["owner"]),
                    "actual kernel ownership differs across metadata emissions")
            owners[row["name"]] = row["owner"]
    groups = {}
    for row in emissions:
        groups.setdefault(row["name"], []).append(row)
    canonical = []
    for name, copies in sorted(groups.items()):
        require(len({(row["kind"], row["type_expr_sha256"], row["type_expr_bytes"], tuple(row["axioms"])) for row in copies}) == 1,
                "repeated kernel metadata has inconsistent type/axioms: "+name)
        require((owners[name], name) in set(actual), "kernel defining-module entry missing")
        row = copies[0]
        canonical.append(dict(module=owners[name], name=name, kind=row["kind"], type_expr_sha256=row["type_expr_sha256"], type_expr_bytes=row["type_expr_bytes"],
                              axioms=row["axioms"], emitting_modules=sorted(copy["module"] for copy in copies)))
    require(canonical == read("kernel-declarations.json"), "unique owned kernel declarations differ")
    by_name = {row["name"]: row for row in canonical}
    require(all(row["name"] in by_name and by_name[row["name"]]["module"] == row["module"] for row in decls),
            "explicit source declaration is missing or assigned to the wrong kernel owner")
    for row in canonical:
        require(row["kind"] in {"definition", "theorem", "opaque", "quotient", "constructor", "recursor", "inductive"} and
                re.fullmatch(r"[0-9a-f]{64}", row["type_expr_sha256"]) and row["type_expr_bytes"] > 0 and
                len(row["axioms"]) == len(set(row["axioms"])) and set(row["axioms"]) <= STANDARD,
                "kernel type/kind/actual standard axiom set invalid: "+row["name"])
    require(all(set(by_name[name]["axioms"]) == set(value) for name, value in axioms.items()),
            "explicit source axiom pins differ from complete kernel audit")
    extra = [name for row in declared for name in row["codegen_extra"]]
    require(len(extra) == len(set(extra)), "duplicate compiler metadata name")
    overlap = set(extra) & set(by_name)
    counts = dict(modules=len(declared), kernel_declarations=len(canonical), kernel_emissions=len(emissions),
                  repeated_emissions=len(emissions)-len(canonical), explicit_source_declarations=len(decls),
                  extra_names=len(extra), extra_names_also_kernel=len(overlap), compiler_only_names=len(set(extra)-set(by_name)))
    require(all(summary[key] == value for key, value in counts.items()), "kernel/compiler metadata counts differ")
    print(f"KERNEL_ENVIRONMENT_PASS: {len(declared)} modules; {len(canonical)} unique owned logical declarations; "
          f"{len(emissions)} audited emissions; {len(extra)} compiler metadata names "
          f"({len(overlap)} also logical, {len(set(extra)-set(by_name))} compiler-only)")


def source_digest():
    """One sha256 over every area module, the library root and the mandatory inputs."""
    names = {p.relative_to(ROOT).as_posix() for p in AREA.rglob("*.lean")}
    pending = list(names)
    while pending:
        path = pending.pop()
        for module in re.findall(r"^import\s+([\w.]+)", (ROOT/path).read_text(), re.M):
            dependency = module.replace(".", "/")+".lean"
            if (ROOT/dependency).is_file() and dependency not in names:
                names.add(dependency)
                pending.append(dependency)
    names.update(read("source-pins.json"))
    names.update(["Solidity.lean", "lean-toolchain", "lakefile.toml", "run-lean.sh",
                  "tests/sol-expression-uniqueness/gate.sh",
                  "scripts/check-sol-expression-uniqueness.py"])
    names = sorted(names)
    lines = "".join(f"{digest(ROOT/name)}  {name}\n" for name in names)
    return hashlib.sha256(lines.encode()).hexdigest()


def audit_checkpoint(modules, decls, axioms, build_log):
    """Fresh evidence from this checkout: a `tests/sol-expression-uniqueness/gate.sh` log.

    The log must name the current source digest (so it is neither stale nor from
    another checkout), end with exit 0 of the full `./run-lean.sh` (whose
    `lake build Solidity` re-checks every `#guard_msgs` pin in AxiomPins.lean),
    and report no error. The H44 Codex-VM evidence (bounded-runtime JSON, kernel
    environment dumps, external solc observations) runs only with
    `--external-evidence`, once that directory is restored.
    """
    require(build_log is not None and build_log.is_file(), "--checkpoint needs --build-log <gate.sh log>")
    log = build_log.read_text(errors="replace")
    require(re.search(r"^SOL_EU_SOURCES "+source_digest()+"$", log, re.M) is not None,
            "build log is stale: its source digest differs from the checkout")
    require(re.search(r"^SOL_EU_EXIT 0$", log, re.M) is not None, "run-lean.sh did not exit 0")
    require(re.search(r"^SOL_EU_FULL_GATE ./run-lean.sh$", log, re.M) is not None, "build log is not the full gate")
    require(re.search(r"(^error|: error:|^✖)", log, re.M) is None, "build log reports an error")
    require("Build completed successfully" in log, "build log is not a completed build")
    reported, _ = actual_axiom_report()
    require(len(reported) == len(decls), "kernel axiom guards do not cover every declaration")
    print("CHECKPOINT_PASS: full run-lean.sh at the current sources re-checked the exact kernel axiom guards "
          f"of {len(reported)} declarations in {len(modules)} modules")


def observed_axiom_report():
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




def audit_external(modules, decls, axioms):
    audit_kernel_environment(modules, decls, axioms)
    observed, _ = observed_axiom_report()
    require(observed == axioms, "observed external axioms differ from pins")
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
    require("Lean (version 4.24.0" in log and "Lake version 5.0.0-src+797c613" in log and
            log.index("377 taclets, 131 read-bearing") < log.index("RUNTIME_GATE_PASS"),
            "actual versions or KeySort-before-marker ordering differs")
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
    print("Kernel proof scope is complete; registration-dependent full task gates remain OPEN.")



# Fixed reviewed proof contracts, independent of mutable acceptance metadata.
EXPRESSION_IDENTITY_STEPS = {'index': 'index_word_unique', 'slice': 'slice_word_unique', 'member': 'member_word_unique', 'callOptions': 'callOptions_word_unique', 'call': 'call_word_unique', 'payableConv': 'payableConv_word_unique', 'metaType': 'metaType_word_unique', 'unaryPrefix': 'unaryPrefix_word_unique', 'unarySuffix': 'unarySuffix_word_unique', 'exp': 'exp_word_unique', 'mulDivMod': 'mulDivMod_word_unique', 'addSub': 'addSub_word_unique', 'shift': 'shift_word_unique', 'bitAnd': 'bitAnd_word_unique', 'bitXor': 'bitXor_word_unique', 'bitOr': 'bitOr_word_unique', 'order': 'order_word_unique', 'equality': 'equality_word_unique', 'and': 'and_word_unique', 'or': 'or_word_unique', 'cond': 'cond_word_unique', 'assign': 'assign_word_unique', 'new': 'new_word_unique', 'tuple': 'tuple_word_unique', 'inlineArray': 'inlineArray_word_unique', 'ident': 'ident_word_unique', 'lit': 'literal_word_unique', 'litUnit': 'unit_word_unique', 'elemType': 'elementary_expr_word_unique'}
OPERATOR_CONTRACTS = {'PrefixOp': ('unaryPrefix_word_unique', 'prefix_suffix_refused'), 'SuffixOp': ('unarySuffix_word_unique', 'suffix_prefix_refused'), 'MulOp': ('mulDivMod_word_unique', 'mulDivMod_right_nested_refused'), 'AddOp': ('addSub_word_unique', 'addSub_right_nested_refused'), 'ShiftOp': ('shift_word_unique', 'shift_right_nested_refused'), 'OrderOp': ('order_word_unique', 'order_right_nested_refused'), 'EqOp': ('equality_word_unique', 'equality_right_nested_refused'), 'AssignOp': ('assign_word_unique', 'assignment_left_nested_refused')}
BOUNDARY_NEGATIVES = ['assignment_left_nested_refused', 'conditional_left_nested_refused', 'or_right_nested_refused', 'and_right_nested_refused', 'equality_right_nested_refused', 'order_right_nested_refused', 'bitOr_right_nested_refused', 'bitXor_right_nested_refused', 'bitAnd_right_nested_refused', 'shift_right_nested_refused', 'addSub_right_nested_refused', 'mulDivMod_right_nested_refused', 'exp_left_nested_refused', 'prefix_suffix_refused', 'suffix_prefix_refused', 'postfix_bases_refused', 'new_bases_refused']
PUBLIC_PROOF_SIGNATURES = {'Solidity.Frontend.ExpressionUniqueness.parseCat_expression_accepted_unique': 'theorem parseCat_expression_accepted_unique {p : Nat → P (Syn .expr)} {src : Bytes} {tree : Syn .expr} {layout : List Choice} (accepted : parseCat p src = .ok (tree, layout)) : ∃ ps, lex src = .ok ps ∧ tree.toks layout = some (tokensOf ps) ∧ tree.prec = true ∧ ∀ other : Syn .expr, other.Derives (tokensOf ps) → other.prec = true → tree = other', 'Solidity.Frontend.ExpressionUniqueness.parseCat_expression_same_source': "theorem parseCat_expression_same_source {p q : Nat → P (Syn .expr)} {src : Bytes} {a b : Syn .expr} {la lb : List Choice} (accepted : parseCat p src = .ok (a, la)) (accepted' : parseCat q src = .ok (b, lb)) : a = b", 'Solidity.Frontend.ExpressionUniqueness.recursive_yield_property': 'theorem recursive_yield_property {c : Cat} (e : Syn c) : RecursiveYieldProperty e', 'Solidity.Frontend.ExpressionUniqueness.expression_yield_word_unique': 'theorem expression_yield_word_unique (e : Syn .expr) : WordUnique e', 'Solidity.Frontend.ExpressionUniqueness.certified_expression_yield_unique': 'theorem certified_expression_yield_unique (a b : Syn .expr) (ts : List Tok) (da : a.Derives ts) (ha : a.prec = true) (db : b.Derives ts) (hb : b.prec = true) : a = b', 'Solidity.Frontend.ExpressionUniqueness.certifiedYieldUnique': 'theorem certifiedYieldUnique : CertifiedYieldUnique'}
RECURSIVE_CASE_CONTRACTS = [{'constructor': 'nil', 'theorem': 'Solidity.Frontend.ExpressionUniqueness.nil_vector_unique', 'categories': ['list.expr', 'list.param', 'list.namedArg', 'list(opt.expr)']}, {'constructor': 'cons', 'theorem': 'Solidity.Frontend.ExpressionUniqueness.cons_vector_unique', 'categories': ['list.expr', 'list.param', 'list.namedArg', 'list(opt.expr)']}, {'constructor': 'none', 'theorem': 'Solidity.Frontend.ExpressionUniqueness.none_expr_word_unique', 'categories': ['opt.expr']}, {'constructor': 'some', 'theorem': 'Solidity.Frontend.ExpressionUniqueness.some_expr_word_unique', 'categories': ['opt.expr']}, {'constructor': 'positional', 'theorem': 'Solidity.Frontend.ExpressionUniqueness.positional_word_unique', 'categories': ['callArgs']}, {'constructor': 'named', 'theorem': 'Solidity.Frontend.ExpressionUniqueness.named_word_unique', 'categories': ['callArgs']}, {'constructor': 'namedArg', 'theorem': 'Solidity.Frontend.ExpressionUniqueness.namedArg_word_unique', 'categories': ['namedArg']}, {'constructor': 'param', 'theorem': 'Solidity.Frontend.ExpressionUniqueness.parameter_word_unique', 'categories': ['param']}, {'constructor': 'elem', 'theorem': 'Solidity.Frontend.ExpressionUniqueness.elementary_type_word_unique', 'categories': ['typeName']}, {'constructor': 'userType', 'theorem': 'Solidity.Frontend.ExpressionUniqueness.user_type_word_unique', 'categories': ['typeName']}, {'constructor': 'mapping', 'theorem': 'Solidity.Frontend.ExpressionUniqueness.mapping_type_word_unique', 'categories': ['typeName']}, {'constructor': 'fnType', 'theorem': 'Solidity.Frontend.ExpressionUniqueness.fn_type_word_unique', 'categories': ['typeName']}, {'constructor': 'array', 'theorem': 'Solidity.Frontend.ExpressionUniqueness.array_type_word_unique', 'categories': ['typeName']}]
ORIGINAL_TARGET = "∀ (a b : Syn .expr) (ts : List Tok), a.Derives ts → a.prec = true → b.Derives ts → b.prec = true → a = b"


def original_target_text():
    source = (AREA / "Statement.lean").read_text()
    return " ".join(source.split("def CertifiedYieldUnique : Prop :=", 1)[1].split("end Solidity.Frontend.ExpressionUniqueness", 1)[0].split())


def audit_complete_proof(by_name, constructors, ledger):
    require(original_target_text() == ORIGINAL_TARGET, "original certified uniqueness target changed")
    for name, signature in PUBLIC_PROOF_SIGNATURES.items():
        require(name in by_name and by_name[name]["kind"] == "theorem" and
                " ".join(by_name[name]["source_signature"].split()) == signature,
                "public proof signature changed or missing: " + name)
    identity = read("constructor-identity.json")
    expected = [dict(constructor=c, theorem="Solidity.Frontend.ExpressionUniqueness."+EXPRESSION_IDENTITY_STEPS[c],
                     assembly="Solidity.Frontend.ExpressionUniqueness.recursive_yield_property") for c in constructors]
    require(identity == expected, "constructor identity/assembly ledger differs")
    for row in identity:
        name = row["theorem"]
        require(name in by_name and by_name[name]["kind"] == "theorem" and
                "WordUnique (Syn."+row["constructor"]+" " in by_name[name]["source_signature"],
                "constructor identity theorem does not bind its intrinsic root: "+row["constructor"])
    source = (AREA / "Certified.lean").read_text()
    cases = re.findall(r"^  \| @?(\w+)\b", source, re.M)
    require(all(cases.count(c) == 1 for c in constructors), "exhaustive expression induction case coverage differs")
    require(read("recursive-cases.json") == RECURSIVE_CASE_CONTRACTS,
            "recursive category/case-family inventory differs")
    for row in RECURSIVE_CASE_CONTRACTS:
        require(cases.count(row["constructor"]) == 1 and row["theorem"] in by_name and
                by_name[row["theorem"]]["kind"] == "theorem", "recursive induction case/identity step missing")
    syntax = (ROOT / "Solidity/Source/Syntax.lean").read_text()
    expected_ops = []
    for enum, (step, negative) in OPERATOR_CONTRACTS.items():
        block = syntax.split("inductive "+enum+" where", 1)[1].split("  deriving", 1)[0]
        expected_ops.append(dict(enum=enum, constructors=re.findall(r"\|\s*(\w+)", block),
            identity="Solidity.Frontend.ExpressionUniqueness."+step,
            negative="Solidity.Frontend.ExpressionUniqueness."+negative))
    require(read("operators.json") == expected_ops, "intrinsic operator constructor coverage differs")
    expected_boundaries = [dict(level=i, constructors=[r["constructor"] for r in ledger if r["level"] == i],
        classification="Solidity.Frontend.ExpressionUniqueness.certified_root_levels_equal",
        negative="Solidity.Frontend.ExpressionUniqueness."+BOUNDARY_NEGATIVES[i]) for i in range(17)]
    require(read("boundaries.json") == expected_boundaries, "precedence/association boundary coverage differs")
    for row in expected_ops:
        for key in ("identity", "negative"):
            require(row[key] in by_name and by_name[row[key]]["kind"] == "theorem", "operator proof missing")
    for row in expected_boundaries:
        for key in ("classification", "negative"):
            require(row[key] in by_name and by_name[row[key]]["kind"] == "theorem", "boundary proof missing")
    controls = ["wrappedFunctionExpr_certified", "wrappedFunctionExpr_any_competitor", "direct_function_meta_refused",
        "attribute_orders_distinct", "holeTuple_certified", "holeTuple_any_competitor", "arrayTypeFamily_word_unique",
        "optionalHoles_actual_vector_identity", "postfixTower_certified", "prefixChain_certified", "suffixChain_certified",
        "middleAssignment_certified", "groupFamily_certified", "mixedAddPrefix_certified"]
    for name in controls:
        full = "Solidity.Frontend.ExpressionUniqueness."+name
        require(full in by_name and by_name[full]["kind"] == "theorem", "arbitrary inhabited/negative control missing: "+name)
    print("PROOF_SCOPE_PASS: unchanged certified target, exhaustive 29 expression cases, all 17 levels, all intrinsic operators, accepted-tree corollaries and arbitrary-family controls")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    modes = parser.add_mutually_exclusive_group()
    modes.add_argument("--inventory", action="store_true")
    modes.add_argument("--checkpoint", action="store_true")
    modes.add_argument("--proof", action="store_true")
    parser.add_argument("--build-log", type=Path)
    parser.add_argument("--source-digest", action="store_true")
    parser.add_argument("--external-evidence", action="store_true",
                        help="also re-check the H44 Codex-VM evidence (needs evidence/ and the kernel-*.json dumps restored)")
    args = parser.parse_args()
    if args.source_digest:
        print(source_digest())
        return 0
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
    require(all(r["status"] == "proved" for r in obligations if r["id"] in
                {"EU-02", "EU-03", "EU-04", "EU-05", "EU-06", "EU-07", "EU-08", "EU-10"}) and
            all(r["status"] in {"partial", "open", "pass"} for r in obligations if r["id"] in {"EU-12", "EU-14"}),
            "proof versus required-global-gate obligation status differs")
    modules = sorted(p.relative_to(ROOT).as_posix() for p in AREA.rglob("*.lean"))
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
    audit_complete_proof(by_name, constructors, ledger)
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
    if args.external_evidence:
        audit_external(modules, decls, axioms)
    if args.checkpoint:
        audit_checkpoint(modules, decls, axioms, args.build_log)
        return 0
    if args.proof:
        return 0
    if args.inventory:
        print("Static inventory only; no full task acceptance claimed.")
        return 0
    audit_checkpoint(modules, decls, axioms, args.build_log)
    open_rows = [r["id"] for r in obligations if r["status"] not in {"proved", "proved-inventory", "pass"}]
    if open_rows:
        print("ACCEPTANCE_OPEN: kernel proof scope and full gate pass; open obligations: "+", ".join(open_rows), file=sys.stderr)
        return 1
    print("ACCEPTANCE_PASS: every obligation closed at the current sources")
    return 0

if __name__ == "__main__":
    try:
        sys.exit(main())
    except (ValueError, KeyError, IndexError, OSError, subprocess.CalledProcessError) as error:
        print("AUDIT_FAIL: "+str(error), file=sys.stderr)
        sys.exit(2)
