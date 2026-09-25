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

## Sharp edges

- A function over `Stmt C Γ Γ'` must match each constructor with variables
  only: a pattern that fixes a field (`.declStorage true …`, `.declLocal p x
  none`) makes Lean fail to generate the equation lemmas ("failed to
  generate splitter"). Branch inside the arm instead.
- A `match` in a denotation must not capture a subterm the proofs weaken
  (`Val.eval`'s unary arm goes through `unopCheck` for that reason).
- `tyHasMapping` and other well-founded definitions do not reduce in the
  kernel, so a proof of them cannot be `Eq.refl`; carry a structural twin
  (`Ty.mapFree`) and prove it equal.
- The MCP server is slow on this package; `lake env lean --tstack=131072
  file.lean` checks a scratch file (`#print axioms`) in under a second.

## Porting one rule

1. The `RuleName` it bridges to (existing).
2. A row in `RuleName.accepts`. If `rules_disjoint` fails it overlaps an old
   row; if `rules_complete` fails a shape has no rule.
3. A `Taclet` constructor and its case of `Taclet.sound`, over the
   denotation (`Stmt.run`): case on the atoms the premise evaluates, in its
   order; move later atoms past the fresh bindings with the `*_setEnv`
   lemmas; close with `SameOk.save`/`agree_tac`.
4. An arm in `Stmt.step`. If `smaller_tac` fails, fix the rule or the measure;
   do not add a hypothesis.
5. The bridge theorem to `ruleEffect` (until phase 7).
6. The tracker line, and `docs/lean-key-rule-map.md` if a name moved.
