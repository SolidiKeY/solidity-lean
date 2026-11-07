#!/usr/bin/env python3
"""Exhaustive, mechanical H28 family-site enumeration.

Every constructor of Taclet, LeanTaclet, CallbackTaclet and Rule is read from
the production sources (read-only); each family operator below is applied at
every match inside the constructor's premise text (after its rewrite arrow).
One match is one mutant: a unique one-change edit whose `old` is the whole
constructor span, so the replacement is attributable to exactly one
constructor.  Term-helper operators edit `Tms` definitions in the same way.
Nothing here judges a mutant: the runner checks each one in Lean.
"""
import hashlib
import json
from pathlib import Path
import re
import sys

TABLES = {"Solidity/Calculus/Rules.lean": ("Taclet", "LeanTaclet", "Rule"),
          "Solidity/Calculus/CallbackRules.lean": ("CallbackTaclet",)}
READ_ONLY = ["Solidity/Calculus/Rules.lean", "Solidity/Calculus/RuleShapes.lean",
             "Solidity/TestSuite/Refuted.lean", "tests/upstream/README.md",
             "Solidity/Calculus/CallbackRules.lean"]

# (operator id, family, pattern, replacement).  Patterns are literal unless
# they start with "re:".  A family name ending in "*" is resolved per site by
# `site_family` (the constructor decides); "other:" families are outside the
# nine H28 families and kept only so no matched clause is silently dropped.
OPERATORS = [
    ("guard-true-to-false", "guard-polarity", "= true ⟹", "= false ⟹"),
    ("guard-false-to-true", "guard-polarity", "= false ⟹", "= true ⟹"),
    ("loop-guard-TRUE-to-FALSE", "guard-polarity", "b = TRUE", "b = FALSE"),
    ("loop-guard-FALSE-to-TRUE", "guard-polarity", "b = FALSE", "b = TRUE"),
    ("invariant-TRUE-to-FALSE", "other:loop-invariant", "inv = TRUE", "inv = FALSE"),
    ("assert-check-true-to-false", "guard-polarity", "re:se = true \\}$", "se = false }"),
    ("break-negation-dropped", "other:loop-invariant", "¬broke", "broke"),
    ("close-true-to-false", "close*", "re:⇝ true \\}$", "⇝ false }"),
    ("close-false-to-true", "close*", "re:⇝ false \\}$", "⇝ true }"),
    ("send-flag-true-to-false", "rollback-payment", "pv := true", "pv := false"),
    ("send-flag-false-to-true", "rollback-payment", "pv := false", "pv := true"),
    ("payment-amount-zeroed", "rollback-payment", "pay(sadr, se)", "pay(sadr, 0)"),
    ("send-amount-strict", "rollback-payment", "0 <= se", "0 < se"),
    ("push-arith-plus-one-to-minus", "overflow", ") + 1)", ") - 1)"),
    ("push-arith-minus-one-to-plus", "overflow", ") - 1)", ") + 1)"),
    ("push-arith-add-to-sub", "overflow", ") + se)", ") - se)"),
    ("push-arith-sub-to-add", "overflow", ") - se)", ") + se)"),
    ("push-arith-mul-to-add", "overflow", ") * se)", ") + se)"),
    ("increment-step-dropped", "overflow", " ± 1", ""),
    ("division-div-to-mul", "division-minimum", ") / se)", ") * se)"),
    ("division-mod-to-div", "division-minimum", ") % se)", ") / se)"),
    ("division-zero-guard-negated", "division-minimum", "if se != 0 then", "if se == 0 then"),
    ("push-length-advanced-twice", "push-tail-length", "re:(\\w+)\\.length \\+ 1\\)", "\\1.length + 2)"),
    ("push-slot-is-last-old", "push-tail-length", "re:(\\w+)\\[\\1\\.length\\]", "\\1[\\1.length - 1]"),
    ("last-slot-is-length", "slot*", "re:(\\w+)\\[\\1\\.length - 1\\]", "\\1[\\1.length]"),
    ("pop-length-reduced-twice", "pop-delete", "re:(\\w+)\\.length - 1\\) \\}", "\\1.length - 2) }"),
    ("delete-dropped", "pop-delete", "re:delAt\\(storage, [^()]*(?:\\([^()]*\\))?[^()]*\\)", "storage"),
    ("memory-delete-dropped", "pop-delete",
     "re:\\{ memory := write\\((?:addM\\(memory\\)|memory), \\w+(?:\\.\\w+|\\[ie\\]), (?:defVal\\(T\\)|freshId\\(addM\\(memory\\)\\))\\) \\}",
     "{ memory := memory }"),
    ("index-constant-zero", "index-bounds", "re:\\b(arr|darr|marr|mv|pmv|rmv|mv₂)\\[ie\\]", "\\1[0]"),
]


def site_family(family, constructor):
    """Resolve a per-site family: closings and last-slot edits name what they
    close or address."""
    name = constructor.split(".")[1]
    if family == "close*":
        if re.match(r"revert|transfer|tryCall|send", name):
            return "rollback-payment"
        return "other:closing"
    if family == "slot*":
        return "pop-delete" if "Pop" in name else "push-tail-length"
    return family


HELPERS = [  # (operator id, family, helper, old, new)
    ("helper-compound-operands-swapped", "overflow", "Tms.Term.binopC",
     ".app2 (.binop op (BinOp.compound_accepts hop hp)) a b",
     ".app2 (.binop op (BinOp.compound_accepts hop hp)) b a"),
    ("helper-incdec-swapped", "overflow", "Tms.Term.binopI",
     "Term.binopC op.binOp (IncDec.binOp_compound op) hp a b",
     "Term.binopC op.binOp (IncDec.binOp_compound op) hp b a"),
    ("helper-binop-args-swapped", "division-minimum", "Tms.Term.binop",
     ".app2 (.binop op h) a b", ".app2 (.binop op h) b a"),
    ("helper-push-slot-cleared", "push-tail-length", "Tms.STerm.pushSlot",
     ".app2 .pushSlot s q", ".app2 .delAt (.app2 .pushSlot s q) (.app1 .next q)"),
]


def sha(data):
    return hashlib.sha256(data.encode() if isinstance(data, str) else data).hexdigest()


def constructors(source, owners):
    lines = source.splitlines(keepends=True)
    owner, out = None, []
    for i, line in enumerate(lines):
        m = re.match(r"inductive (\w+)", line)
        if m:
            owner = m[1]
        m = re.match(r"  \| (\w+)", line)
        if not m or owner not in owners:
            continue
        end = i + 1
        while end < len(lines) and not re.match(r"  \| |  /--|  --|\S|\s*$", lines[end]):
            end += 1
        out.append((owner + "." + m[1], i + 1, "".join(lines[i:end])))
    return out


RECEIVER = re.compile(r"(T storage sp = nsp|T memory mv = nmp|aliasType storage sp = fc); (.*?)\]⟩", re.S)
ALIAS = {"T storage sp = nsp": ("sp", "nsp"), "T memory mv = nmp": ("mv", "nmp"),
         "aliasType storage sp = fc": ("sp", "fc")}


def receiver_reevaluated(span, arrow):
    """Every receiver capture in the premise, anywhere in it: the uses of the
    captured alias after the capture read the receiver expression again
    (evaluated twice), while the capture itself stays.  One site per capture."""
    out = []
    for m in RECEIVER.finditer(span, arrow):
        alias, recv = ALIAS[m[1]]
        rest = re.sub(r"\b" + alias + r"\b(?!')", recv, m[2])
        if rest != m[2]:
            out.append((m.start(2), m.end(2), rest))
    return out


def apply(pattern, repl, text, start):
    if pattern.startswith("re:"):
        rx = re.compile(pattern[3:], re.M)
        for m in rx.finditer(text, start):
            yield m.start(), m.end(), m.expand(repl)
    else:
        i = text.find(pattern, start)
        while i != -1:
            yield i, i + len(pattern), repl
            i = text.find(pattern, i + 1)


def enumerate_sites(root):
    mutants, rows, duplicates = [], [], []
    for target, owners in TABLES.items():
        source = (root / target).read_text()
        for cid, line, span in constructors(source, owners):
            assert source.count(span) == 1, cid
            arrow = span.find("⇝")
            hits = []
            if arrow != -1:
                for op, family, pat, repl in OPERATORS:
                    for k, (a, b, new) in enumerate(apply(pat, repl, span, arrow)):
                        hits.append((op, family, a, b, new))
            if arrow != -1:
                for a, b, new in receiver_reevaluated(span, arrow):
                    hits.append(("receiver-reevaluated", "alias-capture-once", a, b, new))
            rows.append({"id": cid, "file": target, "line": line, "span_sha256": sha(span),
                         "premise_written": arrow != -1, "sites": len(hits)})
            seen, made = {}, {}
            for op, family, a, b, new in sorted(hits, key=lambda h: (h[0], h[2])):
                seen[op] = seen.get(op, 0) + 1
                mutated = span[:a] + new + span[b:]
                if mutated == span or mutated in made:
                    duplicates.append({"constructor": cid, "operator": op, "same_as": made.get(mutated, "original")})
                    continue
                made[mutated] = f"{cid.split('.')[1]}.{op}.{seen[op]}"
                mutants.append({"id": f"{cid.split('.')[1]}.{op}.{seen[op]}", "constructor": cid,
                                "operator": op,
                                "family": "callback-frames" if owners == ("CallbackTaclet",) else site_family(family, cid), "target": target,
                                "offset_in_span": a, "old": span, "new": mutated,
                                "affected": [cid]})
    rules = (root / "Solidity/Calculus/Rules.lean").read_text()
    for op, family, helper, old, new in HELPERS:
        assert rules.count(old) == 1, helper
        mutants.append({"id": f"{helper.split('.')[-1]}.{op}.1", "constructor": helper,
                        "operator": op, "family": family,
                        "target": "Solidity/Calculus/Rules.lean", "old": old, "new": new,
                        "affected": helper_uses(rules, helper)})
    return rows, mutants, duplicates


def helper_uses(rules, helper):
    """Constructors whose elaborated premise reaches the helper: the schema
    lowering is not textual, so this is the declared candidate set; the
    runner checks the toStep row of every constructor of the tables."""
    return ["*"]


def manifest(root):
    rows, mutants, duplicates = enumerate_sites(root)
    ids = [m["id"] for m in mutants]
    assert len(ids) == len(set(ids))
    return {"schema": 3, "generator": "tests/h28-sol/mutation-testing/tools/sites.py",
            "production_inputs": {p: sha((root / p).read_bytes()) for p in READ_ONLY},
            "constructors": rows,
            "operators": [{"id": o[0], "family": o[1], "pattern": o[2], "replacement": o[3]} for o in OPERATORS],
            "helper_operators": [{"id": h[0], "family": h[1], "helper": h[2]} for h in HELPERS],
            "duplicates_not_run": duplicates, "mutants": mutants}


if __name__ == "__main__":
    root = Path(__file__).resolve().parents[4]
    data = manifest(root)
    if "--summary" in sys.argv:
        from collections import Counter
        print(len(data["constructors"]), "constructors;", len(data["mutants"]), "mutants")
        print(Counter(m["family"] for m in data["mutants"]))
        print(Counter(m["operator"] for m in data["mutants"]))
    else:
        print(json.dumps(data, indent=1, ensure_ascii=False))
