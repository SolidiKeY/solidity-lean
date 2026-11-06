#!/usr/bin/env python3
"""Clause-level inventory of the constructors the 30-operator census misses.

`sites.py` finds no operator site in 98 of the 215 constructors: 85 whose
written premise matches no family operator (`no-family-site`) and 13 whose
premise is a Lean term or which wrap another table (`no-premise-text`).  This
tool lists every clause of those 98 premises and gives each clause a family
and a one-change fixture: a mutant attributed to exactly one constructor (its
`old` is the whole constructor span, as in `sites.py`), which the runner then
checks with the proof oracle.  A clause without a fixture carries a reason.

Clause kinds, read off the premise text after `⇝` (or the premise term):

* capture   `T x = E; … x …`: the later uses of `x` read `E` again
              (alias-capture-once; generalises the census receiver operator
              to value, index, condition and argument captures);
* binding   `{ … lhs := rhs … }`: one binding made the identity
              (`lhs := lhs`, `storage := storage`, `memory := memory`);
* branch    `if (c) { A } else { B }`: branches swapped; a one-armed
              `if (c)` negated (guard-polarity);
* arith     `a ⊕ b`: operands swapped; `op(e₁, e₂, e₃)`: modulus swapped;
              `⊖se`: operator dropped (division-minimum / overflow);
* constant  short-circuit results `&& true`, `|| false`, `v = false`, `v = true`
              flipped (guard-polarity);
* side      a Boolean side condition `(h : c = true)`: polarity flipped;
              a computed one (`= some …`, `= none`, `= []`) is listed with a
              reason;
* term      a premise built by a Lean term: a hand fixture (closing flipped,
              modality swapped, a flag negated, the premise closed).

Production sources are only read.  Nothing here judges a fixture.
"""
import json
from pathlib import Path
import re
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
import sites  # noqa: E402

LANE = "tests/h28-sol/mutation-testing"

# Constructors the census does reach are those with at least one site; the
# rest are the scope of this inventory (recomputed, not read from a run).
POP_DELETE = {"Taclet.memoryRootDeleteFreshRebind", "Taclet.storageIndexDeleteNonSimpleIndexCapture"}
PAYMENT = {"Taclet.transfer_unfold_leftFstReceiver", "Taclet.transfer_unfold_rightSndArgument",
           "Taclet.send_unfold_leftFstReceiver", "Taclet.send_unfold_rightSndArgument"}

# Hand fixtures: (clause, family, old substring of the span, new).  The old
# substring must occur exactly once in the constructor span.
HAND = {
    "Taclet.blockEmpty": [
        ("term: the block's statements unfolded", "other:block",
         "(.unfold body body.ext)", "(.done true)")],
    "Taclet.functionBodyExpand": [
        ("expansion of the call body", "callback-frames",
         "⟨[ expand_function_body(fbs); ]⟩ }", "true }")],
    "Taclet.internalCallExpand": [
        ("expansion of the call body", "callback-frames",
         "⟨[ expand_function_body(ic); ]⟩ }", "true }")],
    "Taclet.tryCallNoCallbackBox": [
        ("branch: Error caught runs errorBody", "rollback-payment",
         "\"Error caught\": [ errorBody ]", "\"Error caught\": [ otherBody ]"),
        ("branch: call succeeded binds rets", "rollback-payment",
         "\"call succeeded\": ∀ rets. [ body ]", "\"call succeeded\": ∀ rets. [ ]"),
        ("branch: Panic caught binds code", "rollback-payment",
         "\"Panic caught\": ∀ code. [ panicBody ]", "\"Panic caught\": ∀ code. [ ]"),
        ("branch: other failure caught runs otherBody", "rollback-payment",
         "\"other failure caught\": [ otherBody ]", "\"other failure caught\": [ errorBody ]")],
    "CallbackTaclet.tryCallWithCallbackBox": [
        ("branch: Error caught runs errorBody", "callback-frames",
         "\"Error caught\": [ errorBody ]", "\"Error caught\": [ otherBody ]"),
        ("branch: call succeeded binds rets", "callback-frames",
         "\"call succeeded\": ∀ rets. [ body ]", "\"call succeeded\": ∀ rets. [ ]"),
        ("branch: Panic caught binds code", "callback-frames",
         "\"Panic caught\": ∀ code. [ panicBody ]", "\"Panic caught\": ∀ code. [ ]"),
        ("branch: other failure caught runs otherBody", "callback-frames",
         "\"other failure caught\": [ otherBody ]", "\"other failure caught\": [ errorBody ]")],
    "Taclet.whileUnwind": [
        ("branch: one-armed if (cond)", "guard-polarity",
         "⟨[ if (cond) {", "⟨[ if (!cond) {"),
        ("continuation: the loop again after the body", "other:loop",
         "{ body; while (cond) body; }", "{ body; }")],
    "LeanTaclet.ifElseJoin": [
        ("side condition: join of then/else", "guard-polarity",
         "Upd.ifJoin? se.lower thenStm elseStm", "Upd.ifJoin? se.lower elseStm thenStm")],
    "LeanTaclet.ifElseJoinSequence": [
        ("side condition: join of then/else", "guard-polarity",
         "Upd.ifJoin? se.lower thenStm elseStm", "Upd.ifJoin? se.lower elseStm thenStm")],
    "LeanTaclet.whileInvariantLexDiamond": [
        ("clause: invariant initially valid", "other:loop-invariant",
         "\"invariant initially valid\": inv,", "\"invariant initially valid\": true,"),
        ("clause: the loop condition", "guard-polarity", "‹metrics›, cond,", "‹metrics›, !cond,"),
        ("clause: invariant preserved and used runs body", "other:loop-invariant",
         "\"invariant preserved and used\": body)", "\"invariant preserved and used\": )")],
    "LeanTaclet.tryCallSelfBox": [
        ("term: trySelfStep (five goals)", "rollback-payment",
         "(trySelfStep call rets body errorBody code panicBody otherBody selfArgs selfBody)",
         "(.done true)")],
    "LeanTaclet.tryCallSelfDiamond": [
        ("closing: false", "rollback-payment", "        (.done false)\n", "        (.done true)\n")],
    "LeanTaclet.revertDataBox": [
        ("closing: true", "rollback-payment", "(.done true)", "(.done false)")],
    "LeanTaclet.revertDataDiamond": [
        ("closing: false", "rollback-payment", "(.done false)", "(.done true)")],
    "LeanTaclet.catchDataBox": [
        ("term: catchDataStep at the box", "rollback-payment",
         "(catchDataStep .box call", "(catchDataStep .diamond call")],
    "LeanTaclet.catchDataDiamond": [
        ("closing: false", "rollback-payment", "(.done false)", "(.done true)")],
    "LeanTaclet.recursiveCallUnfold": [
        ("term: one unrolled call frame", "callback-frames",
         "(.unfold (.cons (.call f args ret (body ())) .nil) .refl)", "(.done true)")],
    "LeanTaclet.loopLexErase": [
        ("term: the loop with its plain invariant (break flag kept)", "other:loop-invariant",
         "(.loop (.inv inv none brk qs) cond body)", "(.loop (.inv inv none (!brk) qs) cond body)")],
    "LeanTaclet.functionCallArgCapture": [
        ("term: the first non-simple argument captured", "alias-capture-once",
         "(Premise.argCapture k f p v as' ret body)", "(.done true)")],
    "LeanTaclet.internalCallSummary": [
        ("term: the callee's summary update", "callback-frames",
         "(.update u)", "(.done true)")],
    "LeanTaclet.addmodAssignment": [
        ("arith: modulus", "division-minimum",
         "{ v := addmod(e₁, e₂, e₃) }", "{ v := addmod(e₁, e₃, e₂) }")],
    "LeanTaclet.mulmodAssignment": [
        ("arith: modulus", "division-minimum",
         "{ v := mulmod(e₁, e₂, e₃) }", "{ v := mulmod(e₁, e₃, e₂) }")],
    "Taclet.localValueDeclInitDrop": [
        ("continuation: the initialising write", "other:declaration", "⇝ ⟨[ v = e; ]⟩", "⇝ ⟨[ ]⟩")],
    "Taclet.storageLocalDeclInitDrop": [
        ("continuation: the initialising bind", "other:declaration", "⇝ ⟨[ lsv = rhs; ]⟩", "⇝ ⟨[ ]⟩")],
    "Taclet.memoryLocalDeclInitDrop": [
        ("continuation: the initialising bind", "other:declaration", "⇝ ⟨[ mv = mrhs; ]⟩", "⇝ ⟨[ ]⟩")],
}

# Clauses with no type-correct one-change fixture in the rule language.
NO_FIXTURE = {
    "Rule.key": [("wrapper: a Taclet's premise", "wrapper",
        "no premise of its own: `Rule.key d` has `d`'s premise, so every Taclet clause and fixture covers it")],
    "Rule.lean": [("wrapper: a LeanTaclet's premise", "wrapper",
        "no premise of its own: `Rule.lean d` has `d`'s premise, so every LeanTaclet clause and fixture covers it")],
}

# The declaration only is consumed, the rest read by lookahead: a capture
# followed by more captures yields one match each.
CAPTURE = re.compile(r"(?:T|bool|uint|aliasType)(?: storage| memory)? (\w+'?) = ([^;]+?); (?=(.*?)\]⟩)", re.S)
# a side condition stated as a Boolean equation: its polarity flipped
SIDE = re.compile(r"\((h\w*) : ([^()]*?) = (true|false)( := by side_cond)?\)")
UPDATE = re.compile(r"\{ ((?:[^{}]|\{[^{}]*\})*?) \}\s*⟨\[")
IFELSE = re.compile(r"if \((\w+)\) \{ (.*?) \} else \{ (.*?) \}")
IFSTM = re.compile(r"if \((\w+)\) thenStm else elseStm")
BINOP = re.compile(r"([\w.\[\]₁₂']+) ⊕ ([\w.\[\]₁₂']+)")
UNOP = re.compile(r"⊖(se)\b")
SHORT = [("&& true", "&& false"), ("|| false", "|| true"), ("v = false;", "v = true;"), ("v = true;", "v = false;")]


def mechanical(cid, span):
    """(clause, family, operator, a, b, new) over the premise text."""
    arrow = span.find("⇝")
    out = []
    for m in SIDE.finditer(span, 0, arrow if arrow != -1 else len(span)):
        flip = "false" if m[3] == "true" else "true"
        out.append((f"side condition: {m[1]} : {m[2]} = {m[3]}", "side-condition", "side-condition-flipped",
                    m.start(3), m.end(3), flip))
    if arrow == -1:
        return out
    for m in CAPTURE.finditer(span, arrow):
        name, expr, rest = m[1], m[2], m[3]
        new = re.sub(r"\b" + re.escape(name) + r"(?![\w'])", lambda _: expr, rest)
        if new != rest:
            fam = "alias-capture-once"
            out.append((f"capture: {name} = {expr}", fam, "capture-use-reevaluated", m.start(3), m.end(3), new))
        else:
            # the captured local is used only inside a spliced schema
            # statement: listed, with no textual use to re-read
            out.append((f"capture: {name} = {expr}", "alias-capture-once", None, 0, 0, None))
    for m in UPDATE.finditer(span, arrow):
        body, off = m[1], m.start(1)
        # bindings are separated by `‖`, with any whitespace (also a newline)
        for part in re.finditer(r"[^‖]+", body):
            text = part[0]
            lead = len(text) - len(text.lstrip())
            text = text.strip()
            lhs, sep, rhs = text.partition(" := ")
            if sep and rhs.strip() != lhs.strip():
                ident = lhs.strip()
                fam = "pop-delete" if cid in POP_DELETE else "other:access"
                a = off + part.start() + lead
                out.append((f"binding: {' '.join(text.split())}", fam, "binding-identity",
                            a, a + len(text), f"{ident} := {ident}"))
    for m in IFELSE.finditer(span, arrow):
        new = f"if ({m[1]}) {{ {m[3]} }} else {{ {m[2]} }}"
        out.append((f"branch: if ({m[1]})", "guard-polarity", "branches-swapped", m.start(), m.end(), new))
    for m in IFSTM.finditer(span, arrow):
        out.append((f"branch: if ({m[1]})", "guard-polarity", "branches-swapped", m.start(), m.end(),
                    f"if ({m[1]}) elseStm else thenStm"))
    for m in BINOP.finditer(span, arrow):
        out.append((f"arith: {m[0]}", "division-minimum", "operands-swapped", m.start(), m.end(),
                    f"{m[2]} ⊕ {m[1]}"))
    for m in UNOP.finditer(span, arrow):
        out.append((f"arith: ⊖{m[1]}", "overflow", "unop-dropped", m.start(), m.end(), m[1]))
    for old, new in SHORT:
        i = span.find(old, arrow)
        while i != -1:
            out.append((f"constant: {old}", "guard-polarity", "short-circuit-flipped", i, i + len(old), new))
            i = span.find(old, i + 1)
    return out


def inventory(root):
    rows, census, _ = sites.enumerate_sites(root)
    reached = {r["id"] for r in rows if r["sites"] > 0}
    spans = {}
    for target, owners in sites.TABLES.items():
        for cid, line, span in sites.constructors((root / target).read_text(), owners):
            spans[cid] = (target, line, span)
    out_rows, mutants = [], []
    for r in rows:
        cid = r["id"]
        if cid in reached:
            continue
        target, line, span = spans[cid]
        short = cid.split(".")[1]
        clauses, made, n = [], {}, {}
        mech = mechanical(cid, span)
        for c, f, op, a, b, new in mech:
            if op is None:
                clauses.append({"clause": c, "family": f, "operator": None, "fixture": None,
                                "reason": "the captured local is read only inside a spliced schema statement "
                                          "(`body`), so no written use can be made to re-read the expression"})
        found = [(c, f, op, span[:a] + new + span[b:]) for c, f, op, a, b, new in mech if op is not None]
        for c, f, old, new in HAND.get(cid, []):
            if span.count(old) != 1:
                raise SystemExit(f"hand fixture not unique in {cid}: {old!r}")
            found.append((c, f, "hand", span.replace(old, new, 1)))
        for clause, fam, op, mutated in found:
            if mutated == span or mutated in made:
                clauses.append({"clause": clause, "family": fam, "operator": op,
                                "fixture": None, "reason": "same text as " + made.get(mutated, "the original")})
                continue
            n[op] = n.get(op, 0) + 1
            mid = f"clause.{short}.{op}.{n[op]}"
            made[mutated] = mid
            mutants.append({"id": mid, "constructor": cid, "operator": "clause:" + op, "family": fam,
                            "target": target, "old": span, "new": mutated, "affected": [cid],
                            "clause": clause})
            clauses.append({"clause": clause, "family": fam, "operator": op, "fixture": mid})
        arrow = span.find("⇝") if "⇝" in span else len(span)
        for h in re.finditer(r"\((h\w*) : ([^()]*(?:\([^()]*\)[^()]*)*?)\)", span[:arrow] if "⇝" in span else span):
            if SIDE.fullmatch(h[0]) or any(old in h[0] for _, _, old, _ in HAND.get(cid, [])):
                continue
            stmt = " ".join(h[2].split(" := ")[0].split())
            clauses.append({"clause": f"side condition: {h[1]} : {stmt}", "family": "side-condition",
                            "operator": None, "fixture": None,
                            "reason": "a computed side condition (an equation to `some …`, `none` or `[]`, or a "
                                      "shape): no one-change edit names another inhabited value; the premise "
                                      "term it fixes is covered by the constructor's other clauses"})
        for clause, fam, reason in NO_FIXTURE.get(cid, []):
            clauses.append({"clause": clause, "family": fam, "operator": None, "fixture": None, "reason": reason})
        if cid in PAYMENT:
            for c in clauses:
                c["also"] = ["rollback-payment"]
        out_rows.append({"constructor": cid, "file": target, "line": line,
                         "census": "no-premise-text" if not r["premise_written"] else "no-family-site",
                         "clauses": clauses})
    return out_rows, mutants


def check(rows):
    """Every constructor has at least one clause; every clause a fixture or a reason."""
    bad = [r["constructor"] for r in rows if not r["clauses"] or
           any(c["fixture"] is None and not c.get("reason") for c in r["clauses"])]
    if bad:
        raise SystemExit("clauses without fixture or reason: " + ", ".join(bad))


if __name__ == "__main__":
    root = Path(__file__).resolve().parents[4]
    rows, mutants = inventory(root)
    check(rows)
    if "--summary" in sys.argv:
        from collections import Counter
        print(len(rows), "constructors;", len(mutants), "fixtures")
        print(Counter(m["family"] for m in mutants))
        print(Counter(m["operator"] for m in mutants))
        for r in rows:
            print(r["constructor"], [c["fixture"] or ("-" + c["reason"][:30]) for c in r["clauses"]])
    else:
        print(json.dumps({"rows": rows, "mutants": mutants}, indent=1, ensure_ascii=False))
