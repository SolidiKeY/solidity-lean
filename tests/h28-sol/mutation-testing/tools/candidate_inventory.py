"""Pinned, lossless source census and kernel-checkable finite operator tables.

This records every constructor/helper and textual premise clause. It does not
assert that every possible mutation is selected or every semantic oracle exists.
"""
import hashlib
import json
import bulk_inputs
import checked
import re
import subprocess
from pathlib import Path

BASE = "6f3eedf0788ee1f8a3bcf230558c712ecdca04d5"
OWNERS = {"Taclet", "LeanTaclet", "Rule", "CallbackTaclet"}
INPUTS = ["Solidity/Calculus/Rules.lean", "Solidity/Calculus/CallbackRules.lean",
          "Solidity/Calculus/RuleShapes.lean", "Solidity/TestSuite/Refuted.lean",
          "tests/upstream/README.md", "Solidity/Calculus/RuleSyntax/Schemas.lean",
          "Solidity/AST.lean"]


def digest(data):
    return hashlib.sha256(data).hexdigest()


def mask(source):
    """Hide nested comments and quoted literals, preserving offsets/newlines."""
    result = list(source); i = 0; depth = 0
    def hide(a, b):
        for j in range(a, b):
            if result[j] != "\n": result[j] = " "
    while i < len(source):
        if depth:
            if source.startswith("/-", i): hide(i, i + 2); depth += 1; i += 2
            elif source.startswith("-/", i): hide(i, i + 2); depth -= 1; i += 2
            else: hide(i, i + 1); i += 1
        elif source.startswith("/-", i): hide(i, i + 2); depth = 1; i += 2
        elif source.startswith("--", i):
            end = source.find("\n", i); end = len(source) if end < 0 else end
            hide(i, end); i = end
        elif source[i] == '"':
            start = i; i += 1
            while i < len(source) and source[i] != '"':
                i += 2 if source[i] == "\\" else 1
            if i >= len(source): raise ValueError("unterminated string")
            i += 1; hide(start, i)
        elif source[i] == "'" and re.match(r"'(?:\\.|[^'\\\n])'", source[i:]):
            end = i + len(re.match(r"'(?:\\.|[^'\\\n])'", source[i:])[0]); hide(i, end); i = end
        else: i += 1
    if depth: raise ValueError("unterminated comment")
    return "".join(result)


def span(source, start, stop):
    if not 0 <= start < stop <= len(source): raise ValueError("invalid span")
    return {"start": start, "stop": stop, "byte_start": len(source[:start].encode()),
            "byte_stop": len(source[:stop].encode()), "line_start": source.count("\n", 0, start) + 1,
            "line_end": source.count("\n", 0, stop - 1) + 1,
            "sha256": digest(source[start:stop].encode())}


def command_stop(clean, start):
    # All continuation lines in these pinned declarations are indented.
    match = re.search(r"\n(?=\S)", clean[start:])
    return len(clean) if match is None else start + match.start() + 1


def declarations(source, file):
    clean = mask(source); rows = []
    for owner_match in re.finditer(r"^inductive (\w+)\b", clean, re.M):
        owner = owner_match[1]
        if owner not in OWNERS: continue
        stop = command_stop(clean, owner_match.start())
        starts = list(re.finditer(r"^  \| (\w+)\b", clean[owner_match.start():stop], re.M))
        if not starts: raise ValueError("empty constructor declaration: " + owner)
        for n, match in enumerate(starts):
            a = owner_match.start() + match.start()
            b = owner_match.start() + starts[n + 1].start() if n + 1 < len(starts) else stop
            rows.append({"id": owner + "." + match[1], "kind": "constructor", "file": file,
                         "span": span(source, a, b)})
    scope = []; offset = 0
    for line in clean.splitlines(keepends=True):
        opened = re.match(r"^(namespace|section)\s+([\w.]+)", line)
        ended = re.match(r"^end(?:\s+(\w+))?\s*$", line)
        if opened: scope.append((opened[1], opened[2]))
        elif ended:
            if not scope or (ended[1] and scope[-1][1] != ended[1]): raise ValueError("scope mismatch")
            scope.pop()
        match = re.match(r"^(?:@\[[^\n]*\]\s*)?(?:(?:private|partial|noncomputable|protected)\s+)*(def|abbrev|theorem)\s+([\w.]+[!?]?)", line)
        if match:
            namespace = [name for kind, name in scope if kind == "namespace"]
            if not namespace or namespace[0] != "Solidity": raise ValueError("unexpected declaration namespace")
            name = ".".join(namespace[1:] + [match[2]])
            stop = command_stop(clean, offset)
            kind = "existing-theorem" if match[1] == "theorem" else "term-helper" if name.startswith("Tms.") else "side-condition-helper"
            rows.append({"id": name, "kind": kind, "file": file, "span": span(source, offset, stop)})
        offset += len(line)
    if scope: raise ValueError("unclosed scope")
    if len({r["id"] for r in rows}) != len(rows): raise ValueError("duplicate declaration")
    return rows


def premise_clauses(source, row):
    """Every top-level DSL RHS branch; typed declarations retain their full type."""
    a, b = row["span"]["start"], row["span"]["stop"]
    clean = mask(source); quote = re.search(r"\bdl(?:\[[^\]]+\])?\s*\{", clean[a:b])
    if quote is None:
        return [{"kind": "typed-declaration-body", **span(source, a, b)}]
    opening = a + quote.end() - 1; stack = ["{"]; rhs = None; boundaries = []
    pairs = {"(": ")", "[": "]", "{": "}", "⟨": "⟩"}
    closing = set(pairs.values()); i = opening + 1
    while i < b and stack:
        ch = clean[i]
        if ch in pairs: stack.append(ch)
        elif ch in closing:
            if pairs[stack[-1]] != ch: raise ValueError("unbalanced DSL delimiter")
            stack.pop()
            if not stack:
                if rhs is None: raise ValueError("DSL rule lacks premise separator")
                boundaries.append(i); break
        elif ch == "⇝" and len(stack) == 1:
            if rhs is not None: raise ValueError("multiple outer premise separators")
            rhs = i + 1; boundaries.append(rhs)
        elif ch == ";" and len(stack) == 1 and rhs is not None: boundaries.append(i + 1)
        i += 1
    if stack: raise ValueError("unterminated DSL rule")
    return [{"kind": "dsl-premise-branch", **span(source, x, y)} for x, y in zip(boundaries, boundaries[1:])]


def enum_names(source, owner):
    clean = mask(source); match = re.search(r"^inductive " + re.escape(owner) + r"\b", clean, re.M)
    if match is None: raise ValueError("missing enum: " + owner)
    end = command_stop(clean, match.start())
    body = clean[match.start():end].split("deriving", 1)[0]
    names = re.findall(r"\|\s*(\w+)", body)
    if not names or len(set(names)) != len(names): raise ValueError("invalid enum census")
    return names


def accepts(op, prim):
    if op in {"and", "or"}: return prim == "bool"
    if op in {"eqB", "neB"}: return True
    if op in {"pow", "shl", "addW", "subW", "mulW", "powW"}: return prim == "uint"
    return prim in {"uint", "int"}


def build(repo):
    sources = {}
    for file in INPUTS:
        data = subprocess.check_output(["git", "show", BASE + ":" + file], cwd=repo)
        if (repo / file).read_bytes() != data: raise ValueError("pinned input drift: " + file)
        sources[file] = data.decode()
    rows = []
    for file in INPUTS[:2]: rows += declarations(sources[file], file)
    for row in rows:
        source = sources[row["file"]]; a, b = row["span"]["start"], row["span"]["stop"]
        row["clauses"] = premise_clauses(source, row)
        row["fat_arrow_sites"] = [span(source, a + m.start(), a + m.end()) for m in re.finditer("=>", mask(source[a:b]))]
        row["semantic_oracle_status"] = "not-established-by-declaration-census"
    helper_names = {r["id"] for r in rows if r["kind"] in {"term-helper", "side-condition-helper"}}
    for row in rows:
        if row["kind"] in {"term-helper", "side-condition-helper"}:
            body = mask(sources[row["file"]][row["span"]["start"]:row["span"]["stop"]])
            names = re.findall(r"(?<![\w.])(?:Solidity\.)?([A-Z]\w*(?:\.\w+)+[!?]?)", body)
            refs = {name for name in names if name in helper_names} | {"Tms." + name for name in names if "Tms." + name in helper_names}
            # These exact unqualified global references were reviewed in the
            # immutable Rules source. This is an explicit supplement, not a
            # claim to implement Lean name resolution for arbitrary binders.
            supplements = {"kernelSummary?": {"fewNodes", "summaryNodes", "kernelNF"}, "kernelNF": {"summaryNodes"}}
            for name in supplements.get(row["id"], set()):
                if name not in helper_names or re.search(r"(?<![\w.])" + re.escape(name) + r"(?![\w.!?])", body) is None:
                    raise ValueError("reviewed unqualified helper edge disappeared")
                refs.add(name)
            row["source_helper_references"] = sorted((refs & helper_names) - {row["id"]})
    enums = {name: enum_names(sources["Solidity/AST.lean"], name) for name in ["PrimTy", "BinOp", "IncDec"]}
    if set(enums["PrimTy"]) != {"bool", "uint", "int"}: raise ValueError("operator table needs review for new primitive type")
    if set(enums["BinOp"]) != {"add", "sub", "mul", "pow", "div", "mod", "lt", "gt", "le", "ge", "eqB", "neB", "and", "or", "band", "bor", "bxor", "shl", "shr", "addW", "subW", "mulW", "powW"}: raise ValueError("operator table needs review for new binary operator")
    if set(enums["IncDec"]) != {"preInc", "preDec", "postInc", "postDec"}: raise ValueError("increment table needs review")
    fixture_paths = subprocess.check_output(["git", "ls-files", "tests/h28-sol/mutation-testing/oracles"], cwd=repo, text=True).splitlines()
    fixtures = []
    for file in fixture_paths:
        data = bulk_inputs.read(repo, repo / file)
        code = checked.oracle_code(data.decode())
        fixtures.append({"file": file, "sha256": digest(data),
                         "theorems": re.findall(r"^theorem (\w+)", code, re.M),
                         "proof_status": "requires-original-VM-proof-receipt; not established by this census"})
    manifests = []; variants = {}; by_id = {row["id"]: row for row in rows}
    for file in subprocess.check_output(["git", "ls-files", "tests/h28-sol/mutation-testing/manifests"], cwd=repo, text=True).splitlines():
        data = bulk_inputs.read(repo, repo / file); manifest = json.loads(data)
        manifests.append({"file": file, "sha256": digest(data), "scope": manifest["scope"], "case_ids": [c["id"] for c in manifest["cases"]]})
        for case in manifest["cases"]:
            key = digest(json.dumps(case, sort_keys=True).encode())
            if key in variants:
                variants[key]["manifests"].append(file); continue
            row = by_id[case["constructor_id"]]; text = sources[row["file"]]
            if case["target"] != row["file"] or case["old"] not in text[row["span"]["start"]:row["span"]["stop"]]:
                raise ValueError("case is not attributed to its declaration: " + case["id"])
            references = []
            for role in ["oracle", "witness", "equivalence", "regression"]:
                if role not in case: continue
                path = case[role]; actual = bulk_inputs.read(repo, repo / path)
                if digest(actual) != case[role + "_sha256"]: raise ValueError("fixture hash mismatch")
                references.append({"role": role, "file": path, "sha256": digest(actual)})
            variants[key] = {"id": case["id"], "variant_sha256": key, "kind": case["kind"],
                             "declaration": case["constructor_id"], "family": case.get("family"),
                             "fixtures": references, "manifests": [file], "score": None}
    return {"schema": 1, "base": BASE, "state": "candidate-source-census",
            "production_inputs": {p: digest(s.encode()) for p, s in sources.items()},
            "declarations": rows, "enums": enums, "fixtures": fixtures, "frozen_manifests": manifests, "case_variants": list(variants.values()),
            "binop_acceptance": [{"op": op, "prim": prim, "accepts": accepts(op, prim)} for op in enums["BinOp"] for prim in enums["PrimTy"]],
            "compound_assign": {op: op in {"add", "sub", "mul", "div", "mod"} for op in enums["BinOp"]},
            "numeric_types": {p: p in {"uint", "int"} for p in enums["PrimTy"]},
            "increment_operator": {op: "add" if op in {"preInc", "postInc"} else "sub" for op in enums["IncDec"]},
            "reference_boundary": "Printed type constants, explicit qualified source calls and reviewed pinned unqualified edges; not arbitrary Lean name resolution.",
            "score": None, "scope_complete": False,
            "outstanding": ["Semantic candidate selection and exhaustive oracle attribution remain separate obligations.", "This census does not prove production rule soundness or assignment acceptance."]}


def lean_source(catalog, corrupt=False):
    text = "import Solidity.Calculus.Rules\nimport Solidity.Calculus.CallbackRules\nset_option pp.fullNames true\nset_option pp.sol.dl false\nnamespace H28.CandidateInventoryAudit\nopen Solidity\n"
    text += "def acceptsTable : BinOp → PrimTy → Bool\n"
    for row in catalog["binop_acceptance"]:
        value = not row["accepts"] if corrupt and row["op"] == "add" and row["prim"] == "uint" else row["accepts"]
        text += "  | ." + row["op"] + ", ." + row["prim"] + " => " + str(value).lower() + "\n"
    text += "def compoundTable : BinOp → Bool\n" + "".join("  | ." + op + " => " + str(value).lower() + "\n" for op, value in catalog["compound_assign"].items())
    text += "def numericTable : PrimTy → Bool\n" + "".join("  | ." + prim + " => " + str(value).lower() + "\n" for prim, value in catalog["numeric_types"].items())
    text += "def incrementTable : IncDec → BinOp\n" + "".join("  | ." + op + " => ." + value + "\n" for op, value in catalog["increment_operator"].items())
    facts = {"accepts_all": "∀ op prim, acceptsTable op prim = op.accepts prim", "compound_all": "∀ op, compoundTable op = op.hasCompoundAssign", "numeric_all": "∀ prim, numericTable prim = prim.isNumeric", "increment_all": "∀ op, incrementTable op = op.binOp"}
    for name, statement in facts.items():
        proof = "by intro op prim; cases op <;> cases prim <;> rfl" if name == "accepts_all" else "by intro x; cases x <;> rfl"
        text += "theorem " + name + " : " + statement + " := " + proof + "\n"
    text += "end H28.CandidateInventoryAudit\n"
    declarations = ["Solidity." + r["id"] for r in catalog["declarations"]] + ["H28.CandidateInventoryAudit." + name for name in facts]
    for name in declarations: text += "#print axioms " + name + "\n#check @" + name + "\n"
    for owner in sorted(OWNERS) + list(catalog["enums"]): text += "#print Solidity." + owner + "\n"
    return text, declarations


def attach_kernel_references(catalog, signatures):
    helpers = {row["id"] for row in catalog["declarations"] if row["kind"] in {"term-helper", "side-condition-helper"}}
    direct = {}
    for row in catalog["declarations"]:
        signature = signatures["Solidity." + row["id"]]
        names = set(re.findall(r"Solidity\.([\w.]+[!?]?)", signature)) & helpers
        row["printed_type_helper_references"] = sorted(names)
        direct[row["id"]] = set(names)
    # A helper type does not expose its implementation. Read only the exact
    # pinned definition bytes to add its explicit helper calls, not name guesses.
    for row in catalog["declarations"]:
        if row["kind"] not in {"term-helper", "side-condition-helper"}: continue
        # Source bytes are separately pinned in the catalog; caller supplies
        # the actual source slices below when recording source helper edges.
        direct[row["id"]].update(row.get("source_helper_references", []))
    def closure(name, active):
        if name in active: return set()
        result = set(direct[name])
        for child in direct[name]: result |= closure(child, active | {name})
        return result
    for row in catalog["declarations"]:
        row["transitive_helper_references"] = sorted(closure(row["id"], set()))
    return {helper: sorted(row["id"] for row in catalog["declarations"] if row["kind"] == "constructor" and helper in row["transitive_helper_references"]) for helper in sorted(helpers)}
