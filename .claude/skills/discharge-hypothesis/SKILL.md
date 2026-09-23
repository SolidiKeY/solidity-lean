---
name: discharge-hypothesis
description: Remove, weaken or classify a hypothesis of the unfold-rule soundness theorems in Calculus/RuleSoundness.lean. Use when asked to drop a hypothesis, to make a `_sound` theorem unconditional, to work through the soundness debt, or to pick what to prove next there.
---

# Discharging a soundness hypothesis

Work on one hypothesis **family** per session, not one rule. Families share
their template lemma, so removing a hypothesis there frees every rule that uses
the lemma. The session ends with a commit even if nothing was removed.

## 1. Pick

- The count: the pinned `#soundness_ledger` output at the bottom of
  `Solidity/Calculus/SoundnessLedger.lean`. Do not re-derive it.
- The history: `docs/soundness-hypotheses.md`. Read the family's
  **Attempts** before trying anything, and do not repeat one that is
  recorded there unless you are changing what made it stick.

Prefer, in order:

1. `residue`
2. `unclassified`, where the first job is to classify
3. `typing`

A `semantic` hypothesis is not a proof task. It waits on the design change
its section names.

## 2. Free wins

Run `lean_minimal_hypotheses` on each `_sound` theorem that carries the
family, and on its template lemma. Delete every hypothesis it reports as
unused, together with the argument at every call site, then re-check.

## 3. Delete and look

Remove the hypothesis from the template lemma, not from the rules. Then run
`lean_diagnostic_messages` on `Calculus/RuleSoundness.lean`, and for each
failure `lean_goal` at the failing line. The file is 12k lines, so use
`lean_file_outline` and ranged reads.

## 4. Is the stuck goal true?

The interpreter is executable, so check before proving. Build the smallest
concrete state and statement that violates the deleted hypothesis, and
compare `execStmt` against `execBlock` of the residual with `lean_run_code`
(the files in `Counterexamples/` show the shape).

- **They disagree.** The hypothesis is semantic. Turn the probe into
  `Counterexamples/<Name>.lean`, ending in a theorem
  `¬ ResultsAgree aliasNames (execStmt …) (execBlock …)`. Then:
  - point the name's `hypKind` at that theorem;
  - add a row to `docs/module-map.md` and an import to `Solidity.lean`;
  - restore the hypothesis. Stop there.
- **They agree, and you cannot find a counterexample.** Split with
  `by_cases` on the old hypothesis. The positive branch is the old proof,
  so all the new work is in the negative branch. If only some rules go
  through, *weaken* the hypothesis instead of removing it: for example the
  `hsafe` that replaced `hnm` in the `execAssign*_storageRhsErr` helpers.
  A weakened hypothesis gets a new binder name, which the ledger records.
- **Missing lemma.** Prove it, or state it and record it as the blocker.
  Never leave a `sorry` in `RuleSoundness.lean` that is not documented at
  its site.

## 5. Record, re-pin, commit

1. Add a dated **Attempts** entry to the family's section in
   `docs/soundness-hypotheses.md`: the approach, and either what came off or
   the exact stuck goal or missing lemma. If the family's kind changed,
   update its section and `hypKind`.
2. Rebuild the ledger's imports with
   `lake build Solidity.Calculus.SoundnessLedger` (in the background).
   `RuleSoundness` has to be recompiled before the ledger sees the change.
3. Re-pin: `lean_diagnostic_messages` on `SoundnessLedger.lean` shows the
   `#guard_msgs` diff. Take the new text, or the "Update #guard_msgs" action
   from `lean_code_actions`. Read the diff before accepting it:
   - it should shrink;
   - a line that *grew* means a hypothesis came back under a new name, which
     has to be justified in the Attempts entry.

A commit whose ledger diff is empty but whose Attempts entry is new is a
normal outcome.

## Running families in parallel

Families that share no template lemma are independent, so they can be
worked in parallel. Give one worktree agent per family this skill and the
family's name. Each agent returns its Attempts entry and a diff. Merge them
one at a time, re-pinning the ledger after each merge, because the pin is one
block and the diffs will conflict there.
