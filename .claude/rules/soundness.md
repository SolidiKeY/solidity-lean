---
paths:
  - "Solidity/RuleSoundness.lean"
  - "Solidity/RewriteSoundness.lean"
  - "Solidity/Wp/**/*.lean"
  - "Solidity/Counterexamples/*.lean"
---

# Soundness conventions

**The contract**: every rule in `ruleNames` with a non-empty residual has a
`<rule>_sound` theorem — the residual agrees with the original statement under
the interpreter, modulo the scratch alias bindings. Adding an unfold rule
without one silently weakens the file's claim.

## Hypothesis shapes

The module docstring of `RuleSoundness.lean` classifies the theorems by
hypothesis shape. What to know before adding or weakening one:

- **Alias freshness** is stated as `RuleSoundness.usesVar` /
  `stmtUsesVar … = false`, decidable on a concrete program.
- **`hprim : rhs.ty.isPrimitive = true`** is about the *interpreter*, not the
  rule. On a reference source with an impure index, rule and interpreter
  disagree and the real EVM sides with the **rule** — solc is right-hand-side
  first only for a primitive source. `Semantics.execAssignNested` is uniformly
  value-first and unfaithful there, so `hprim` is what stops the theorem
  asserting the interpreter's answer. See
  `Counterexamples/RefSourceOrder.lean` and `docs/solc-alignment.md`
  § "Known divergence". Dropping it needs assignment to become target-first
  for reference sources.
- **`hev`/`hstable` are gone.** `freezeRhs` binds the value into `rv` before
  any target capture, so the whole `*WriteUnfoldLeft*` family needs no
  semantic side condition on a primitive value operand. The programs those
  hypotheses used to exclude are now *inside* the theorems.
- **The freeze cannot be made conditional** on the path being impure: a simple
  right-hand side can get stuck while a pure path can revert, so the two
  orders differ even inside the rule's condition. `Counterexamples/ErrorOrder.lean`
  is the refutation, and shows what `hev` was hiding — assuming the
  right-hand side *succeeds* deletes exactly the states where the unfrozen
  residual is wrong.
- Some side conditions are **proof-technique residue, not semantic
  restriction**, and the docstring says which. Those are the ones worth
  weakening.

## The terminal side

`Wp/Terminal/*`'s `<rule>_update` theorems state
`execStmt s stmt = terminalUpdate r stmt s` **under the rule's guard**. The
guard is what fixes the shapes; a theorem that did not use it would be an
interpreter fact, not a rule fact. `Wp/TerminalUpdate.lean` writes updates in
the interpreter's *state* vocabulary and never through its evaluators — the
one exception is `storagePlaceAliasUpd`.

`Update/TacletTable.lean` bridges a rule's *stated* update to the one the
interpreter performs. Bridges needing a KeY sort the Lean condition does not
express carry it as a syntactic hypothesis (`hprim`, `hvar`, `hpure`).
`bridges_account` checks `bridgedRules` and `openBridges` together are exactly
the rules with an update, so moving a rule between them is checked.

## Open `sorry`s here

`functionCallArgCapture_sound_inlined`; the storage/memory-alias argument case
of `storagePushValueUnfoldRightSndArgument_sound`; the memory-kind right-hand
side of `memoryWriteUnfoldRightSndResult_sound`. Each is documented at the
site. Do not add an undocumented one.
