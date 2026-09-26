---
paths:
  - "Solidity/Calculus/Rules.lean"
  - "Solidity/Calculus/RuleSyntax.lean"
  - "Solidity/Calculus/Completeness.lean"
  - "Solidity/Calculus/RuleShapes.lean"
  - "Solidity/Calculus/PrintedRules.lean"
  - "Solidity/Calculus/KeyTaclets.lean"
  - "Solidity/SortCheck/*.lean"
---

# The rule table

A taclet is one constructor of `Taclet C k m s p` (`Calculus/Rules.lean`),
named as solkey names it, its type written in `dl{ ⟨[ s; ]⟩ ⇝ p }`. Schema
variables are bound implicitly and their kind is read off their name
(`RuleSyntax.lean`'s table: `sp`/`nsp`, `se`/`nse`, `fld`, `lhs`, …). There is
no generated table and no condition to keep disjoint: which rule fires is
`Stmt.step` (`Completeness.lean`), a total function over the typed syntax.

## Invariants

- No `sorry`, `native_decide` or `axiom` under `Solidity/Calculus/`.
- **Types, not predicates.** A statement no rule can run is a typing problem:
  change the syntax (`Syntax.lean`) so it cannot be written. Never add a
  well-formedness hypothesis.
- One rule, one constructor; the modality is a parameter (`⟨[ ]⟩`), not a
  box/diamond twin. Only `revertBox`/`revertDiamond` tell them apart.
- Every theorem has a docstring with a small Solidity example.
- Example contracts are **named** `Contract` constants: the quoters and the
  kernel re-check rely on it. A new syntax constructor needs an arm in every
  quoter (`Syntax.lean`, `Calculus/Notation.lean`).

## Adding or changing a rule

1. The constructor, in its section of `Rules.lean`, in `dl{ … }`.
2. Its arm in `Stmt.step` (`Completeness.lean`). Exhaustiveness is the
   coverage proof, so a statement form without an arm fails the build.
3. Its case of `Taclet.sound`: `Calculus/SoundUpdate.lean` for an update
   premise, `Calculus/SoundUnfold.lean` for statements,
   `Calculus/RuleSoundness.lean` for a branch or a closed goal
   (`.claude/rules/soundness.md`).
4. Its row in `RuleShapes.tacletOrigins` (the solkey taclets it transcribes)
   and in `PrintedRules.printedOrigins`. `#check_constructor_table` fails the
   build on a missing or extra row; `taclets_partitioned` and
   `printed_rules_partitioned` move with it.
5. A taclet that reads storage or memory: its row in
   `SortCheck/Annotations.lean`, then `lake exe solkeycheck`.

`docs/lean-key-rule-map.md` is the authority for the correspondence to
solkey's taclet names. Do not restate it in a docstring or a banner.

## Sharp edges

- A function over `Stmt C` must match each constructor with variables only: a
  pattern that fixes a field (`.declLocal p x none`) makes Lean fail to
  generate the equation lemmas ("failed to generate splitter"). Branch inside
  the arm instead.
- `tyHasMapping` and other well-founded definitions do not reduce in the
  kernel, so a proof of them cannot be `Eq.refl`; carry a structural twin
  (`Ty.mapFree`) and prove it equal.
- `lake env lean --tstack=131072 file.lean` checks a scratch file in
  seconds; the MCP server is slow on this package.
