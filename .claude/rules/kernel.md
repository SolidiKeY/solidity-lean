---
paths:
  - "Solidity/Kernel/**"
  - "docs/kernel-port.md"
---

# The typed kernel

`Solidity/Kernel/` is mini-solkey's calculus at full scale. The plan and the
tracker are `docs/kernel-port.md`; tick its **Progress** line in the commit
that makes it true. mini-solkey (`~/projects/side-projects/lean/mini-solkey`)
is the reference: copy the shape of the declaration the plan names.

## Invariants (mini-solkey's, stricter than the rest of this package)

- No `sorry`, no `native_decide`, no `axiom` under `Kernel/`.
  `rg -n 'sorry|native_decide|^axiom' Solidity/Kernel` prints nothing.
- **Types, not predicates.** A statement no rule can run is a typing
  problem: change the syntax so it cannot be written. Never add a
  `wf`/`stmtWt` hypothesis to a `Kernel/` theorem.
- One rule, one `Taclet` constructor, named by its solkey taclet (the
  `KeyTaclet` constructor); a Lean-only rule keeps its `RuleName`. The
  modality is a parameter, not a box/diamond twin.
- Example contracts are **named** `Contract` constants: the quoters and the
  kernel re-check rely on it. A new syntax constructor needs an arm in every
  quoter.
- Every theorem has a docstring with a small Solidity example; headline
  theorems are followed by a checked `example`.
- `Kernel/` imports the old layer, never the reverse, until phase 7. Do not
  touch `Calculus/Rules.lean` or `Calculus/KeyTaclets.lean` before then.

## Porting one rule

1. The `RuleName` it bridges to (existing).
2. A row in `RuleName.accepts`. If `rules_disjoint` fails it overlaps an old
   row; if `rules_complete` fails a shape has no rule.
3. A `Taclet` constructor, in the notation, and its case of `Taclet.sound`,
   from the rule's `*_sound` through erasure.
4. An arm in `Stmt.step`. If `smaller_tac` fails, fix the rule or the measure;
   do not add a hypothesis.
5. The bridge theorem to `ruleEffect` (until phase 7).
6. The tracker line, and `docs/lean-key-rule-map.md` if a name moved.
