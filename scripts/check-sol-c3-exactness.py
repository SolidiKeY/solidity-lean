#!/usr/bin/env python3
"""Check exact proofs, external fixtures, and mandatory final gate evidence."""
import argparse, copy, hashlib, json, re, subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
AREA = ROOT / "tests/sol-c3-exactness"
BASE = "6f3eedf0788ee1f8a3bcf230558c712ecdca04d5"
ADOPTED_UPSTREAM = "e6849d3bdf516099d20c33d3581d523449764018"
PREFIX = "Solidity.Frontend.C3Exactness."
ALLOWED = ("Solidity/Frontend/C3Exactness/", "tests/sol-c3-exactness/",
           "scripts/check-sol-c3-exactness.py", "docs/feature-work/c3-exactness.md")
REQUIRED = {"Solidity/Source/Resolve.lean", "Solidity/Source/Inheritance.lean",
            "Solidity/Frontend/Static/C3.lean", "Solidity/Frontend/Static/Inheritance.lean",
            "Solidity/Source/Decls.lean", "Solidity/Source/WellFormed.lean"}
TOOLING = {"scripts/check-sol-c3-exactness.py", "tests/sol-c3-exactness/run-bounded.py",
           "tests/sol-c3-exactness/lakefile.worker.toml", "tests/sol-c3-exactness/bin/lake",
           "tests/sol-c3-exactness/manifest.json"}
TOOLING |= {"tests/sol-c3-exactness/check-fixtures.mjs", "tests/sol-c3-exactness/final-checks.py", "tests/sol-c3-exactness/axiom-registration.json", "tests/sol-c3-exactness/release-owned-file-cache.py"}
TOOLING |= {str(p.relative_to(ROOT)) for p in (AREA / "fixtures").rglob("*") if p.is_file()}
FIXTURE_MANIFEST_SHA = "9a2ab74a8040178026a74a04929116ce6d7d9ce064b315c5ba5c0678b342190f"
STANDARD = {"propext", "Classical.choice", "Quot.sound"}

EXPECTED_CASE_FAMILIES = {'Solidity.Frontend.C3Exactness.Trace.done': ['Solidity.Frontend.C3Exactness.Controls.empty_trace'],
 'Solidity.Frontend.C3Exactness.Trace.step': ['Solidity.Frontend.C3Exactness.Controls.independent_heads',
                                              'Solidity.Frontend.C3Exactness.Controls.diamond_merge'],
 'Solidity.Frontend.C3Exactness.Stuck.here': ['Solidity.Frontend.C3Exactness.Controls.cycle_stuck'],
 'Solidity.Frontend.C3Exactness.Stuck.step': ['Solidity.Frontend.C3Exactness.graphBad_merge_stuck'],
 'Solidity.Frontend.C3Exactness.ExactLin.mk': ['Solidity.Frontend.C3Exactness.graphDiamond_exact',
                                               'Solidity.Frontend.C3Exactness.graphShared_exact'],
 'Solidity.Frontend.C3Exactness.Reaches.refl': ['Solidity.Frontend.C3Exactness.graphDiamond_refl'],
 'Solidity.Frontend.C3Exactness.Reaches.step': ['Solidity.Frontend.C3Exactness.graphDiamond_reaches'],
 'Solidity.Frontend.C3Exactness.GraphBlocked.merge': ['Solidity.Frontend.C3Exactness.graphBad_certificate'],
 'Solidity.Frontend.C3Exactness.GraphBlocked.base': ['Solidity.Frontend.C3Exactness.graphBad_inherited_certificate'],
 'Solidity.Frontend.C3Exactness.CyclePath.direct': ['Solidity.Frontend.C3Exactness.graphSelfCycle_path'],
 'Solidity.Frontend.C3Exactness.CyclePath.step': ['Solidity.Frontend.C3Exactness.graphMutualCycle_path'],
 'Solidity.Frontend.C3Exactness.IdentityLin.mk': ['Solidity.Frontend.C3Exactness.graphDiamond_identities',
                                                  'Solidity.Frontend.C3Exactness.graphInterfaceDiamond_identities',
                                                  'Solidity.Frontend.C3Exactness.graphResolution_identities']}
EXPECTED_SYNTAX_CONTROLS = {'Syn.unit': ['Solidity.Frontend.C3Exactness.graphUnit', 'Solidity.Frontend.C3Exactness.graphInterfaceUnit'],
 'Syn.cons': ['Solidity.Frontend.C3Exactness.graphSpecs',
              'Solidity.Frontend.C3Exactness.graphUnit',
              'Solidity.Frontend.C3Exactness.graphInterfaceUnit'],
 'Syn.nil': ['Solidity.Frontend.C3Exactness.graphSpecs',
             'Solidity.Frontend.C3Exactness.graphUnit',
             'Solidity.Frontend.C3Exactness.graphInterfaceUnit'],
 'Syn.contract': ['Solidity.Frontend.C3Exactness.graphUnit',
                  'Solidity.Frontend.C3Exactness.graphMixed',
                  'Solidity.Frontend.C3Exactness.graphBadInterface'],
 'Syn.interface': ['Solidity.Frontend.C3Exactness.graphInterfaceUnit',
                   'Solidity.Frontend.C3Exactness.graphMixed',
                   'Solidity.Frontend.C3Exactness.graphBadInterface'],
 'Syn.inherit': ['Solidity.Frontend.C3Exactness.graphSpecs'],
 'Syn.none': ['Solidity.Frontend.C3Exactness.graphSpecs', 'Solidity.Frontend.C3Exactness.graphUnit']}
EXPECTED_TYPED_WITNESSES = {'Solidity.Frontend.C3Exactness.Controls.empty_trace': 'Trace ([] : List (List String)) []',
 'Solidity.Frontend.C3Exactness.Controls.identity_trace': 'Trace ([[1], [2, 1]] : List (List Nat)) [2, 1]',
 'Solidity.Frontend.C3Exactness.Controls.independent_heads': 'Trace [["a"], ["b"]] ["a", "b"]',
 'Solidity.Frontend.C3Exactness.Controls.diamond_merge': 'Trace [["B", "A"], ["C", "A"], ["B", "C"]] ["B", '
                                                         '"C", "A"]',
 'Solidity.Frontend.C3Exactness.Controls.cycle_stuck': 'Stuck [["a", "b"], ["b", "a"]]',
 'Solidity.Frontend.C3Exactness.graphBad_merge_stuck': 'Stuck [["Y", "A", "B"], ["X", "B", "A"], ["Y", "X"]]',
 'Solidity.Frontend.C3Exactness.graphDiamond_exact': 'ExactLin graphDiamond.env "D" ["D", "C", "B", "A"]',
 'Solidity.Frontend.C3Exactness.graphShared_exact': 'ExactLin graphShared.env "F" ["F", "E", "D", "C", "B", '
                                                    '"A"]',
 'Solidity.Frontend.C3Exactness.graphDiamond_refl': 'Reaches graphDiamond.env "D" "D"',
 'Solidity.Frontend.C3Exactness.graphDiamond_reaches': 'Reaches graphDiamond.env "D" "A"',
 'Solidity.Frontend.C3Exactness.graphBad_certificate': 'GraphBlocked graphBad.env "Z"',
 'Solidity.Frontend.C3Exactness.graphBad_inherited_certificate': 'GraphBlocked graphBad.env "W"',
 'Solidity.Frontend.C3Exactness.graphSelfCycle_path': 'CyclePath graphSelfCycle.env "S" "S"',
 'Solidity.Frontend.C3Exactness.graphMutualCycle_path': 'CyclePath graphMutualCycle.env "P" "P"',
 'Solidity.Frontend.C3Exactness.graphDiamond_identities': 'IdentityLin graphDiamond.env 3 [3, 2, 1, 0]',
 'Solidity.Frontend.C3Exactness.graphInterfaceDiamond_identities': 'IdentityLin graphInterfaceDiamond.env 3 '
                                                                   '[3, 2, 1, 0]',
 'Solidity.Frontend.C3Exactness.graphResolution_identities': 'IdentityLin graphResolution.env 3 [3, 2, 1, 0]',
 'Solidity.Frontend.C3Exactness.Controls.alternative_common_order': 'CommonOrder ([[0], [1]] : List (List '
                                                                    'Nat)) [1, 0]',
 'Solidity.Frontend.C3Exactness.Controls.alternative_not_trace': '¬ Trace ([[0], [1]] : List (List Nat)) [1, '
                                                                 '0]',
 'Solidity.Frontend.C3Exactness.graphBad_merge_no_order': '∀ out, ¬ CommonOrder [["Y", "A", "B"], ["X", "B", '
                                                          '"A"], ["Y", "X"]] out',
 'Solidity.Frontend.C3Exactness.graphBad_identity_no_order': '∀ out, ¬ CommonOrder ([[3, 0, 1], [2, 1, 0], '
                                                             '[3, 2]] : List (List Nat)) out'}
EXPECTED_TYPED_INTERFACES = {'Solidity.Frontend.C3Exactness.merge_iff': '∀ {n : Nat} {ls : List (List String)} {out : List String}, '
                                            'Env.merge n ls = some out ↔ Trace ls out ∧ out.length < n',
 'Solidity.Frontend.C3Exactness.Trace.unique': '∀ {α : Type} [DecidableEq α] {ls : List (List α)} {a b : '
                                               'List α}, Trace ls a → Trace ls b → a = b',
 'Solidity.Frontend.C3Exactness.linearize_exact_iff': '∀ {E : Env}, E.basesOK = true → ∀ (c : String) (L : '
                                                      'List String), E.linearize c = some L ↔ ExactLin E c L',
 'Solidity.Frontend.C3Exactness.linearize_none_iff_blocked': '∀ {E : Env}, E.basesOK = true → ∀ c : String, '
                                                             'E.linearize c = none ↔ GraphBlocked E c',
 'Solidity.Frontend.C3Exactness.CyclePath.linearizeF_none': '∀ {E : Env} {c : String}, CyclePath E c c → ∀ n '
                                                            ': Nat, E.linearizeF n c = none',
 'Solidity.Frontend.C3Exactness.IdentityLin.unique': '∀ {E : Env} {i : Nat} {a b : List Nat}, IdentityLin E '
                                                     'i a → IdentityLin E i b → E.basesOK = true → a = b',
 'Solidity.Frontend.C3Exactness.unit_identity_iff': '∀ (u : Syn .unit), u.env.basesOK = true → ∀ c : String, '
                                                    'c ∈ u.env.contractNames → ∀ I : List Nat, '
                                                    '(u.env.linearize c).map (List.map (rank u.env)) = some '
                                                    'I ↔ IdentityLin u.env (rank u.env c) I',
 'Solidity.Frontend.C3Exactness.resolved_identity_iff': '∀ {s : Settings} {u : Syn .unit} {r : Resolution}, '
                                                        "Resolves' s u r → r.env.basesOK = true → ∀ c : "
                                                        'String, c ∈ r.env.contractNames → ∀ I : List Nat, '
                                                        '(r.env.linearize c).map (List.map (rank r.env)) = '
                                                        'some I ↔ IdentityLin r.env (rank r.env c) I',
 'Solidity.Frontend.C3Exactness.ctor_monotone': '∀ {E : Env} {c b : String} {L Lb : List String}, '
                                                'E.linearize c = some L → b ∈ E.bases c → E.linearize b = '
                                                'some Lb → (E.ctorOrder b).Sublist (E.ctorOrder c).dropLast',
 'Solidity.Frontend.C3Exactness.ctor_nodup': '∀ {E : Env} {c : String} {L : List String}, E.basesOK = true → '
                                             'E.linearize c = some L → (E.ctorOrder c).Nodup',
 'Solidity.Frontend.C3Exactness.Trace.common_order': '∀ {α : Type} [DecidableEq α] {ls : List (List α)} {out '
                                                     ': List α}, Trace ls out → CommonOrder ls out',
 'Solidity.Frontend.C3Exactness.Obstruction.not_common_order': '∀ {α : Type} [DecidableEq α] {ls : List '
                                                               '(List α)}, Obstruction ls → ∀ out, ¬ '
                                                               'CommonOrder ls out',
 'Solidity.Frontend.C3Exactness.Stuck.not_common_order': '∀ {α : Type} [DecidableEq α] {ls : List (List α)}, '
                                                         'Stuck ls → ∀ out, ¬ CommonOrder ls out',
 'Solidity.Frontend.C3Exactness.stuck_iff_no_common_order': '∀ {α : Type} [DecidableEq α] (ls : List (List '
                                                            'α)), Stuck ls ↔ ¬ ∃ out, CommonOrder ls out',
 'Solidity.Frontend.C3Exactness.trace_exists_iff_common_order': '∀ {α : Type} [DecidableEq α] (ls : List '
                                                                '(List α)), (∃ out, Trace ls out) ↔ ∃ out, '
                                                                'CommonOrder ls out',
 'Solidity.Frontend.C3Exactness.merge_bound_none_iff_no_common_order': '∀ ls : List (List String), Env.merge '
                                                                       '(fuelBound ls) ls = none ↔ ¬ ∃ out, '
                                                                       'CommonOrder ls out',
 'Solidity.Frontend.C3Exactness.merge_bound_exists_iff_common_order': '∀ ls : List (List String), (∃ out, '
                                                                      'Env.merge (fuelBound ls) ls = some '
                                                                      'out) ↔ ∃ out, CommonOrder ls out',
 'Solidity.Frontend.C3Exactness.merge_none_iff_order_or_fuel': '∀ (n : Nat) (ls : List (List String)), '
                                                               'Env.merge n ls = none ↔ (¬ ∃ out, '
                                                               'CommonOrder ls out) ∨ ∃ out, Trace ls out ∧ '
                                                               'n ≤ out.length',
 'Solidity.Frontend.C3Exactness.Controls.cycle_not_common_order': '∀ {α : Type} [DecidableEq α] (a b : α), ∀ '
                                                                  'out, ¬ CommonOrder [[a, b], [b, a]] out'}
EXPECTED_SYNTAX_PROOFS = ['#check (show graphUnit [] = Syn.unit Syn.nil from rfl)',
 '#check (show graphSpecs ["A"] = Syn.cons (Syn.inherit ⟨"A", []⟩ Syn.none) Syn.nil from rfl)',
 '#check (show graphUnit [("A", [])] = Syn.unit (Syn.cons (Syn.contract false "A" Syn.none Syn.nil Syn.nil) '
 'Syn.nil) from rfl)',
 '#check (show graphInterfaceUnit [("I", [])] = Syn.unit (Syn.cons (Syn.interface "I" Syn.nil Syn.nil) '
 'Syn.nil) from rfl)',
 '#check (show (fun {α : Type} (ls : List (List α)) (out : List α) => CommonOrder ls out) = (fun {α : Type} '
 '(ls : List (List α)) (out : List α) => out.Nodup ∧ ∀ l ∈ ls, l.Sublist out) from rfl)']
EXPECTED_ARBITRARY_FAMILIES = ['Solidity.Frontend.C3Exactness.merge_iff',
 'Solidity.Frontend.C3Exactness.merge_bound_iff',
 'Solidity.Frontend.C3Exactness.trace_or_stuck',
 'Solidity.Frontend.C3Exactness.Trace.unique',
 'Solidity.Frontend.C3Exactness.Trace.mem_iff',
 'Solidity.Frontend.C3Exactness.Trace.nodup',
 'Solidity.Frontend.C3Exactness.Trace.local_order',
 'Solidity.Frontend.C3Exactness.Controls.every_head_position',
 'Solidity.Frontend.C3Exactness.Controls.delayed_obstruction',
 'Solidity.Frontend.C3Exactness.linearize_exact_iff',
 'Solidity.Frontend.C3Exactness.graph_trace_or_blocked',
 'Solidity.Frontend.C3Exactness.linearize_none_iff_blocked',
 'Solidity.Frontend.C3Exactness.CyclePath.not_exact',
 'Solidity.Frontend.C3Exactness.CyclePath.linearizeF_none',
 'Solidity.Frontend.C3Exactness.IdentityLin.decode',
 'Solidity.Frontend.C3Exactness.IdentityLin.roundtrip',
 'Solidity.Frontend.C3Exactness.unit_identity_iff',
 'Solidity.Frontend.C3Exactness.resolved_identity_iff',
 'Solidity.Frontend.C3Exactness.ctor_direct_order',
 'Solidity.Frontend.C3Exactness.ctor_monotone',
 'Solidity.Frontend.C3Exactness.ctor_nodup',
 'Solidity.Frontend.C3Exactness.Trace.common_order',
 'Solidity.Frontend.C3Exactness.Obstruction.not_common_order',
 'Solidity.Frontend.C3Exactness.Stuck.not_common_order',
 'Solidity.Frontend.C3Exactness.stuck_iff_no_common_order',
 'Solidity.Frontend.C3Exactness.trace_exists_iff_common_order',
 'Solidity.Frontend.C3Exactness.merge_bound_none_iff_no_common_order',
 'Solidity.Frontend.C3Exactness.merge_bound_exists_iff_common_order',
 'Solidity.Frontend.C3Exactness.merge_none_iff_order_or_fuel',
 'Solidity.Frontend.C3Exactness.Controls.cycle_not_common_order',
 'Solidity.Frontend.C3Exactness.graphBad_merge_no_order',
 'Solidity.Frontend.C3Exactness.graphBad_identity_no_order']

def sha(data):
    return hashlib.sha256(data).hexdigest()


def lean_code(text):
    """Remove nested Lean comments while preserving strings and line locations."""
    out, i, depth, quoted = [], 0, 0, False
    while i < len(text):
        if depth:
            if text.startswith("/-", i):
                depth += 1; out.extend("  "); i += 2
            elif text.startswith("-/", i):
                depth -= 1; out.extend("  "); i += 2
            else:
                out.append("\n" if text[i] == "\n" else " "); i += 1
        elif quoted:
            if text[i] == "\\" and i + 1 < len(text):
                out.extend(text[i:i+2]); i += 2
            else:
                quoted = text[i] != '"'; out.append(text[i]); i += 1
        elif text.startswith("/-", i):
            depth = 1; out.extend("  "); i += 2
        elif text.startswith("--", i):
            while i < len(text) and text[i] != "\n":
                out.append(" "); i += 1
        else:
            quoted = text[i] == '"'; out.append(text[i]); i += 1
    if depth or quoted:
        raise ValueError("unterminated Lean comment/string")
    return "".join(out)

def lean_commands(code):
    """Only active command lines, excluding strings that span physical lines."""
    commands, quoted = [], False
    for line in code.splitlines():
        if not quoted and line.lstrip().startswith(("#check ", "#guard_msgs ")):
            commands.append(line.strip())
        i = 0
        while i < len(line):
            if quoted and line[i] == "\\":
                i += 2
            else:
                if line[i] == '"': quoted = not quoted
                i += 1
    return "\n".join(commands)

def write_scope_errors(paths, adopted_is_ancestor):
    errors = []
    if not adopted_is_ancestor:
        errors.append("authorized adopted upstream is not an ancestor")
    if not all(p.startswith(ALLOWED[:2]) or p in ALLOWED[2:] for p in paths):
        errors.append("tracked/untracked write scope violation")
    return errors


def validate(m, overlays=None, receipt_override=None):
    overlays = overlays or {}
    def read(path):
        return overlays[path] if path in overlays else (ROOT / path).read_bytes()
    errors = []
    def require(ok, text):
        if not ok:
            errors.append(text)
    require(m["base"] == BASE, "base drift")
    request = json.loads(read("tests/sol-c3-exactness/axiom-registration.json"))
    require(request == {"Solidity/Frontend/C3Exactness/Audit.lean:"+k:sorted(v) for k,v in m["axiom_sets"].items()}, "axiom registration request drift")
    expected_modules = sorted(str(p.relative_to(ROOT)) for p in
                              (ROOT / "Solidity/Frontend/C3Exactness").rglob("*.lean"))
    expected_modules = sorted(set(expected_modules) | {p for p in overlays if p.endswith(".lean")})
    require(sorted(m["modules"]) == expected_modules, "module inventory drift")
    require(set(m["lean_sources"]) == set(expected_modules), "Lean hash inventory drift")
    require(set(m["source_pins"]) == REQUIRED, "producer pin inventory drift")
    actual = []
    for path in expected_modules:
        data = read(path)
        require(m["lean_sources"].get(path) == sha(data), "Lean source hash drift: " + path)
        text = data.decode()
        code = lean_code(text)
        require(not re.search(r"\b(sorry|admit|unsafe|native_decide)\b|^\s*axiom\s", code, re.M),
                "forbidden proof escape: " + path)
        require(not re.search(r"\bset_option\s+maxHeartbeats\b", code), "proof budget override: " + path)
        namespaces = re.findall(r"^namespace ([\w.]+)$", code, re.M)
        prefix = namespaces[0] + "." if len(namespaces) == 1 else PREFIX
        # This lane permits only these simple explicit forms; fail closed otherwise.
        starts = re.findall(r"(?m)^([ \t]*(?:(?:private|protected|noncomputable|partial)\s+)*(?:def|inductive|theorem|abbrev|structure|class|instance|opaque|axiom|example)\b[^\n]*)", code)
        require(not starts or (len(namespaces) == 1 and
                (namespaces[0] == PREFIX[:-1] or namespaces[0].startswith(PREFIX))),
                "declaration namespace drift: " + path)
        require(all(re.match(r"^(def|inductive|theorem)\s+[\w.]+", line) for line in starts)
                and not re.search(r"(?m)^\s*@\[", code), "unsupported declaration syntax: " + path)
        for kind, name in re.findall(r"^(def|inductive|theorem)\s+([\w.]+)", code, re.M):
            actual.append({"module": path, "kind": kind, "name": prefix + name})
        for match in re.finditer(r"(?ms)^inductive ([\w.]+).*?(?=^(?:def|theorem|inductive|end)\b|\Z)", code):
            for constructor in re.findall(r"^  \| ([\w]+)\b", match.group(), re.M):
                actual.append({"module": path, "kind": "constructor",
                               "name": prefix + match[1] + "." + constructor})
    require(sorted(actual, key=lambda d: d["name"]) == sorted(m["declarations"], key=lambda d: d["name"]), "declaration/constructor inventory drift")
    audit = read("Solidity/Frontend/C3Exactness/Audit.lean").decode()
    audit_code = lean_code(audit)
    audit_commands = lean_commands(audit_code)
    names = {x["name"] for x in actual}
    require(set(m["axiom_sets"]) == names, "axiom inventory drift")
    require(set(re.findall(r"^#check ([\w.]+)$", audit_commands, re.M)) == names,
            "signature audit coverage drift")
    require(set(re.findall(r"^#guard_msgs in #print axioms (\S+)", audit_commands, re.M)) == names,
            "guarded axiom audit coverage drift")
    for name, axioms in m["axiom_sets"].items():
        require(set(axioms) <= STANDARD, "unapproved axiom: " + name)
        msg = (f"'{name}' depends on axioms: [{', '.join(axioms)}]" if axioms else
               f"'{name}' does not depend on any axioms")
        require(" ".join(("/-- info: " + msg + " -/").split()) in " ".join(audit.split()),
                "axiom pin drift: " + name)
    require(m.get("case_families") == EXPECTED_CASE_FAMILIES, "fixed constructor witness drift")
    require(m.get("syntax_controls") == EXPECTED_SYNTAX_CONTROLS, "fixed syntax witness drift")
    require(m.get("typed_witnesses") == EXPECTED_TYPED_WITNESSES, "typed witness inventory drift")
    require(m.get("typed_interfaces") == EXPECTED_TYPED_INTERFACES, "typed API inventory drift")
    require(m.get("syntax_proofs") == EXPECTED_SYNTAX_PROOFS, "typed syntax proof inventory drift")
    require(m.get("arbitrary_families") == EXPECTED_ARBITRARY_FAMILIES, "fixed arbitrary proof inventory drift")
    normalized = " ".join(audit_commands.split())
    for name, ty in (EXPECTED_TYPED_WITNESSES | EXPECTED_TYPED_INTERFACES).items():
        require(" ".join(("#check (" + name + " : " + ty + ")").split()) in normalized,
                "typed witness/API guard missing: " + name)
    for guard in EXPECTED_SYNTAX_PROOFS:
        require(" ".join(guard.split()) in normalized, "typed syntax guard missing")
    constructors = {d["name"] for d in actual if d["kind"] == "constructor"}
    require(set(m.get("case_families", {})) == constructors, "constructor family coverage drift")
    for family, controls in m.get("case_families", {}).items():
        require(bool(controls) and all(c in names for c in controls),
                "constructor witness coverage drift: " + family)
    syntax = {"Syn.unit", "Syn.cons", "Syn.nil", "Syn.contract", "Syn.interface", "Syn.inherit", "Syn.none"}
    require(set(m.get("syntax_controls", {})) == syntax, "syntax usage inventory drift")
    require(all(v and all(c in names for c in v) for v in m.get("syntax_controls", {}).values()),
            "syntax witness coverage drift")
    critical = {PREFIX + n for n in ["merge_iff", "merge_bound_iff", "Trace.unique",
        "linearize_exact_iff", "linearize_none_iff_blocked", "CyclePath.linearizeF_none",
        "IdentityLin.decode", "IdentityLin.roundtrip", "unit_identity_iff", "resolved_identity_iff",
        "ctor_direct_order", "ctor_monotone", "ctor_nodup"]}
    require(critical <= set(m.get("arbitrary_families", [])) <= names,
            "arbitrary-family proof coverage drift")
    for path, expected in m["source_pins"].items():
        require(sha(read(path)) == expected, "producer source drift: " + path)
        pinned = subprocess.check_output(["git", "show", BASE + ":" + path], cwd=ROOT)
        require(sha(pinned) == expected, "producer base pin drift: " + path)
    # The user explicitly authorized adopting this exact published upstream.
    # Its files remain read-only: only the owned delta may differ from it.
    ancestry = subprocess.run(["git", "merge-base", "--is-ancestor", ADOPTED_UPSTREAM, "HEAD"], cwd=ROOT).returncode == 0
    changed = subprocess.check_output(["git", "diff", "--name-only", ADOPTED_UPSTREAM], cwd=ROOT,
                                      text=True).splitlines()
    changed += subprocess.check_output(["git", "ls-files", "--others", "--exclude-standard"],
                                       cwd=ROOT, text=True).splitlines()
    errors.extend(write_scope_errors(changed, ancestry))
    log_path = AREA / "evidence/audit-confirmation.log"
    receipt_path = log_path.with_suffix(".log.json")
    require(receipt_path.exists(), "missing bounded audit receipt")
    receipt = receipt_override if receipt_override is not None else (
        json.loads(receipt_path.read_text()) if receipt_path.exists() else {})
    expected_snapshot = {p: sha(read(p)) for p in REQUIRED | TOOLING | set(expected_modules)}
    require(receipt.get("input_hashes") == expected_snapshot, "audit receipt source snapshot drift")
    require(receipt.get("command") == ["lake", "build", "+Solidity.Frontend.C3Exactness.Audit"],
            "audit command drift")
    require(receipt.get("exit") == 0 and not receipt.get("pressure_stop") and
            not receipt.get("interrupted"), "guarded kernel audit has not passed")
    require(receipt.get("memory_limit_bytes") == 12884901888 and
            receipt.get("swap_limit_bytes") == 0 and
            receipt.get("minimum_parent_available_bytes", 0) >= 4*1024**3,
            "audit resource envelope drift")
    require(receipt.get("lean_version", "").startswith("Lean (version 4.24.0,") and
            receipt.get("lake_version", "").startswith("Lake version 5.0.0-src+797c613"),
            "audit toolchain drift")
    log_bytes = log_path.read_bytes()
    require(receipt.get("log_sha256") == sha(log_bytes), "audit log hash drift")
    log = log_bytes.decode()
    require("Build completed successfully" in log and "Exit status: 0" in log and
            not re.search(r"^error:", log, re.M), "guarded kernel audit has not passed")
    require(m["open_obligations"] or m.get("checkpoints", {}).get("final") == "done", "unfinished final obligations were erased")
    return errors

def fixture_errors(overlays=None, receipt_override=None):
    overlays = overlays or {}
    errors = []
    def read(path):
        return overlays[path] if path in overlays else (ROOT / path).read_bytes()
    def require(ok, text):
        if not ok: errors.append(text)
    manifest_path = "tests/sol-c3-exactness/fixtures/manifest.json"
    manifest_bytes = read(manifest_path)
    require(sha(manifest_bytes) == FIXTURE_MANIFEST_SHA, "fixed fixture ledger drift")
    fm = json.loads(manifest_bytes)
    packet_path = "tests/sol-c3-exactness/evidence/compiler-fixtures.json"
    packet_bytes = read(packet_path)
    packet = json.loads(packet_bytes)
    require(packet.get("compiler") == fm["compiler"], "compiler packet pin drift")
    require(packet.get("manifest_sha256") == sha(manifest_bytes), "fixture manifest packet drift")
    checker_path = "tests/sol-c3-exactness/check-fixtures.mjs"
    require(packet.get("checker_sha256") == sha(read(checker_path)), "fixture checker packet drift")
    require(packet.get("negative_controls") == 6, "compiler negative controls missing")
    discovered = {str(p.relative_to(ROOT)) for p in (AREA / "fixtures").rglob("*.sol")}
    discovered |= {p for p in overlays if p.startswith("tests/sol-c3-exactness/fixtures/") and p.endswith(".sol")}
    require(discovered == {f["source"] for f in fm["fixtures"]}, "fixture source inventory drift")
    rows = packet.get("results", [])
    require([r.get("name") for r in rows] == [f["name"] for f in fm["fixtures"]], "fixture result coverage drift")
    audit = " ".join(lean_commands(lean_code(read("Solidity/Frontend/C3Exactness/Audit.lean").decode())).split())
    for f, row in zip(fm["fixtures"], rows):
        require(sha(read(f["source"])) == f["source_sha256"] == row.get("source_sha256"), "fixture source drift: " + f["name"])
        require(row.get("source") == f["source"], "fixture source path drift")
        require(row.get("kernel_observations") == f["kernel_observations"], "fixture kernel link drift")
        for o in f["kernel_observations"]:
            require(" ".join(("#check (" + o["name"] + " : " + o["type"] + ")").split()) in audit, "fixture kernel type guard missing")
        observed = [{k:e.get(k) for k in ("errorCode", "type", "message")} for e in row.get("errors", [])]
        require(observed == f["expected_errors"], "exact compiler diagnostics drift: " + f["name"])
        if f["linearizations"] is not None:
            require(row.get("linearizations") == f["linearizations"], "compiler order drift: " + f["name"])
            reverse = {k:list(reversed(v)) for k,v in f["linearizations"].items()}
            require(row.get("reverse_name_sequences") == reverse, "compiler static sequence drift")
        else:
            require(bool(observed), "negative fixture accepted")
        require(row.get("comparison_limit") == f.get("comparison_limit"), "fixture comparison boundary drift")
    log_path = "tests/sol-c3-exactness/evidence/compiler-fixtures-final.log"
    receipt = receipt_override if receipt_override is not None else json.loads(read(log_path + ".json"))
    cmd = ["node", checker_path, str(AREA / ".artifacts/compiler" / fm["compiler"]["file"]), packet_path]
    require(receipt.get("command") == cmd, "fixture command drift")
    require(receipt.get("exit") == 0 and not receipt.get("interrupted") and not receipt.get("pressure_stop"), "fixture run did not pass")
    inputs = REQUIRED | TOOLING | {str(p.relative_to(ROOT)) for p in (ROOT / "Solidity/Frontend/C3Exactness").rglob("*.lean")}
    require(receipt.get("input_hashes") == {p:sha(read(p)) for p in inputs}, "fixture receipt snapshot drift")
    require(receipt.get("memory_limit_bytes") == 12884901888 and receipt.get("swap_limit_bytes") == 0 and receipt.get("minimum_parent_available_bytes",0) >= 4*1024**3, "fixture resource envelope drift")
    log = read(log_path)
    require(receipt.get("log_sha256") == sha(log), "fixture log digest drift")
    require(("FIXTURE_PACKET_SHA256 " + sha(packet_bytes)).encode() in log and b"SOL_C3_COMPILER_FIXTURES_PASS 9" in log, "fixture output not bound to passed run")
    return errors


def final_errors(m):
    errors = []
    if not m.get("checkpoints") or any(v != "done" for v in m["checkpoints"].values()):
        errors.append("final checkpoint not done")
    if m.get("open_obligations"):
        errors.append("open obligations remain: " + "; ".join(m["open_obligations"]))
    required = {
        "run-lean-final": ["bash", "run-lean.sh"],
        "keysort-final": ["bash", "scripts/check-solkey.sh", "--key", "/workspace/.setup/solkey/keyext.solidity.core/src/main/resources/org/key_project/solidity/proof/rules/solidityProgramRules.key"],
        "final-source-gates": [".venv/bin/python", "tests/sol-c3-exactness/final-checks.py"],
        "corpus-final": ["bash", "scripts/check-corpus.sh", "--solkey", "/workspace/solidity-lean/tests/migration/solkey/keyext.solidity.examples"],
    }
    inputs = REQUIRED | TOOLING | set(m["modules"])
    snapshot = {p:sha((ROOT/p).read_bytes()) for p in inputs}
    for name, cmd in required.items():
        p = AREA / "evidence" / (name + ".log")
        r = p.with_suffix(".log.json")
        if not r.exists() or not p.exists():
            errors.append("missing final gate receipt: " + name); continue
        r = json.loads(r.read_text())
        if r.get("command") != cmd or r.get("exit") != 0 or r.get("interrupted") or r.get("pressure_stop"):
            errors.append("final gate not passed: " + name)
        decisive = {"run-lean-final":["Build completed successfully", "solkeycheck: OK"], "keysort-final":["parsed 377 taclets, 131 read-bearing, table covers 131", "solkeycheck: OK"], "corpus-final":["check-corpus: ok"]}
        if any(t not in p.read_text() for t in decisive.get(name, [])):
            errors.append("missing decisive final output: " + name)
        if r.get("input_hashes") != snapshot or r.get("log_sha256") != sha(p.read_bytes()):
            errors.append("stale final gate evidence: " + name)
        if r.get("memory_limit_bytes") != 12884901888 or r.get("swap_limit_bytes") != 0 or r.get("minimum_parent_available_bytes",0) < 4*1024**3:
            errors.append("final gate resource drift: " + name)
    source_packet = AREA / "evidence/final-source-gates.json"
    if not source_packet.exists():
        errors.append("missing source gate packet")
    else:
        rows = json.loads(source_packet.read_text())
        commands = [["bash","scripts/check-trust.sh"],["node","scripts/check-orphans.mjs"],["node","scripts/check-layers.mjs"],["bash","scripts/coord-tools/register.sh","--check"],["bash","scripts/check-doc-paths.sh"],["node","scripts/check-axiom-pins.mjs"],["bash","scripts/check-testsuite.sh"],["node","scripts/check-automatic.mjs","--strict"]]
        if [r.get("command") for r in rows] != commands: errors.append("source gate coverage drift")
        for row in rows:
            p = ROOT / row["log"]
            if row.get("exit") != 0 or not p.exists() or row.get("log_sha256") != sha(p.read_bytes()): errors.append("source gate not passed: " + " ".join(row["command"]))
        log = AREA / "evidence/final-source-gates.log"
        if not log.exists() or ("SOURCE_GATE_PACKET_SHA256 " + sha(source_packet.read_bytes())) not in log.read_text(): errors.append("source gate packet digest drift")
    reviews = AREA / "evidence/final-reviews.json"
    if not reviews.exists():
        errors.append("missing final independent reviews")
    else:
        reviews = json.loads(reviews.read_text())
        if reviews.get("input_hashes") != snapshot:
            errors.append("final review snapshot drift")
        for role in ("finder", "skeptic"):
            r = reviews.get(role, {})
            p = ROOT / r.get("evidence", "missing-final-review")
            if r.get("verdict") != "pass" or not p.is_file() or r.get("sha256") != sha(p.read_bytes()): errors.append("final review not passed: " + role)
    return errors

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--checkpoint", choices=["merge", "graph", "fixtures", "full"], default="full")
    ap.add_argument("--self-test", action="store_true")
    args = ap.parse_args()
    m = json.loads((AREA / "manifest.json").read_text())
    errors = validate(m)
    if args.checkpoint in ("fixtures", "full"):
        errors += fixture_errors()
    if errors:
        raise SystemExit("FAIL: " + "; ".join(errors))
    if args.self_test:
        assert not write_scope_errors(["Solidity/Frontend/C3Exactness/Trace.lean"], True)
        for path in ["Solidity/Source/Inheritance.lean", "Solidity.lean", "scripts/g07-axiom-pins.json"]:
            assert "tracked/untracked write scope violation" in write_scope_errors([path], True)
        assert "authorized adopted upstream is not an ancestor" in write_scope_errors([], False)
        print("ADOPTION_SCOPE_NEGATIVE_CONTROLS_PASS: 4 rejected unauthorized states")
        mutations = []
        bad = copy.deepcopy(m); bad["declarations"].pop(); mutations.append(bad)
        bad = copy.deepcopy(m); bad["modules"].pop(); mutations.append(bad)
        bad = copy.deepcopy(m); bad["source_pins"][next(iter(bad["source_pins"]))] = "0" * 64; mutations.append(bad)
        bad = copy.deepcopy(m); bad["axiom_sets"][next(iter(bad["axiom_sets"]))] = ["sorryAx"]; mutations.append(bad)
        bad = copy.deepcopy(m); bad["open_obligations"] = []; bad["checkpoints"]["final"] = "pending"; mutations.append(bad)
        bad = copy.deepcopy(m); bad["source_pins"].pop(next(iter(bad["source_pins"]))); mutations.append(bad)
        bad = copy.deepcopy(m); bad["case_families"].pop(next(iter(bad["case_families"]))); mutations.append(bad)
        bad = copy.deepcopy(m); bad["case_families"][next(iter(bad["case_families"]))] = []; mutations.append(bad)
        bad = copy.deepcopy(m); bad["syntax_controls"].pop("Syn.interface"); mutations.append(bad)
        bad = copy.deepcopy(m); bad["arbitrary_families"].remove(PREFIX + "resolved_identity_iff"); mutations.append(bad)
        bad = copy.deepcopy(m); bad["case_families"][PREFIX + "GraphBlocked.merge"] = [PREFIX + "Controls.empty_zero_fuel"]; mutations.append(bad)
        bad = copy.deepcopy(m); bad["syntax_controls"]["Syn.interface"] = [PREFIX + "Controls.empty_zero_fuel"]; mutations.append(bad)
        bad = copy.deepcopy(m); bad["typed_witnesses"][PREFIX + "graphBad_certificate"] = "True"; mutations.append(bad)
        bad = copy.deepcopy(m); bad["typed_interfaces"][PREFIX + "resolved_identity_iff"] = "True"; mutations.append(bad)
        bad = copy.deepcopy(m); bad["syntax_proofs"].pop(); mutations.append(bad)
        assert all(validate(bad) for bad in mutations)
        assert "module inventory drift" in validate(m, {"Solidity/Frontend/C3Exactness/Nested/Hidden.lean": b""})
        base_path = "Solidity/Frontend/C3Exactness/Trace.lean"
        hidden = (ROOT / base_path).read_bytes() + b"\nprivate theorem hidden : True := True.intro\n"
        assert any("unsupported declaration syntax" in e for e in validate(m, {base_path: hidden}))
        extra = (ROOT / base_path).read_bytes().replace(b"  | done {ls}", b"  | ghost {ls} : Trace ls []\n  | done {ls}")
        assert "declaration/constructor inventory drift" in validate(m, {base_path: extra})
        stale = json.loads((AREA / "evidence/audit-confirmation.log.json").read_text())
        stale["input_hashes"][base_path] = "0" * 64
        assert "audit receipt source snapshot drift" in validate(m, receipt_override=stale)
        audit_path = "Solidity/Frontend/C3Exactness/Audit.lean"
        audit_bytes = (ROOT / audit_path).read_bytes()
        name = PREFIX + "graphBad_certificate"
        typed = ("#check (" + name + " : " + EXPECTED_TYPED_WITNESSES[name] + ")").encode()
        commented = audit_bytes.replace(typed, b"/- outer /- nested -/\n" + typed + b"\n-/")
        assert any("typed witness/API guard missing" in e for e in validate(m, {audit_path: commented}))
        ax = ("#guard_msgs in #print axioms " + name).encode()
        commented_ax = audit_bytes.replace(ax, b"/- " + ax + b" -/")
        assert "guarded axiom audit coverage drift" in validate(m, {audit_path: commented_ax})
        if args.checkpoint in ("fixtures", "full"):
            packet_path = "tests/sol-c3-exactness/evidence/compiler-fixtures.json"
            packet = json.loads((ROOT/packet_path).read_text())
            bad = copy.deepcopy(packet); bad["results"][0]["linearizations"]["D"] = ["D","B","C","A"]
            assert any("compiler order drift" in e for e in fixture_errors({packet_path:json.dumps(bad).encode()}))
            bad = copy.deepcopy(packet); bad["results"][5]["errors"][0]["errorCode"] = "2449"
            assert any("exact compiler diagnostics drift" in e for e in fixture_errors({packet_path:json.dumps(bad).encode()}))
            bad = copy.deepcopy(packet); bad["results"].pop()
            assert "fixture result coverage drift" in fixture_errors({packet_path:json.dumps(bad).encode()})
            bad = copy.deepcopy(packet); bad["results"][0]["kernel_observations"] = []
            assert "fixture kernel link drift" in fixture_errors({packet_path:json.dumps(bad).encode()})
            fpath = "tests/sol-c3-exactness/fixtures/manifest.json"
            bad = json.loads((ROOT/fpath).read_text()); bad["fixtures"][5]["expected_errors"][0]["message"] = ""
            assert "fixed fixture ledger drift" in fixture_errors({fpath:json.dumps(bad).encode()})
            guard = b'#check (Solidity.Frontend.C3Exactness.graphMixed_public : graphMixed.env.linearize "C" = some ["C", "IB", "IA"])'
            assert "fixture kernel type guard missing" in fixture_errors({audit_path:audit_bytes.replace(guard,b"/- "+guard+b" -/")})
            r = json.loads((AREA/"evidence/compiler-fixtures-final.log.json").read_text());r["input_hashes"]["tests/sol-c3-exactness/check-fixtures.mjs"] = "0"*64
            assert "fixture receipt snapshot drift" in fixture_errors(receipt_override=r)
            fake = copy.deepcopy(m);fake["checkpoints"]["final"]="done";fake["open_obligations"]=[];fake["modules"]=[]
            assert final_errors(fake), "fake final completion accepted"
            assert "fixture source inventory drift" in fixture_errors({"tests/sol-c3-exactness/fixtures/uncovered.sol":b"contract X {}"})
            print("FIXTURE_ACCEPTANCE_NEGATIVE_CONTROLS_PASS: 9 rejected mutations")
        print("ACCEPTANCE_NEGATIVE_CONTROLS_PASS: 21 rejected mutations")
    if args.checkpoint == "full":
        errors = final_errors(m)
        if errors:
            raise SystemExit("FULL_ACCEPTANCE_PENDING: " + "; ".join(errors))
    print(args.checkpoint.upper() + "_CHECKPOINT_PASS: " + str(len(m["declarations"])) +
          " explicit declarations/constructors; " + str(len(m["case_families"])) +
          " constructor families; exact sources, axiom pins and kernel controls")
    print("OPEN: " + "; ".join(m["open_obligations"]))

if __name__ == "__main__":
    main()
