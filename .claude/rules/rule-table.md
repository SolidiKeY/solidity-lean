---
paths:
  - "Solidity/Calculus/Rules.lean"
  - "Solidity/Calculus/RuleSyntax.lean"
  - "Solidity/Calculus/Arms.lean"
  - "Solidity/Calculus/Blocks.lean"
  - "Solidity/Calculus/Step.lean"
  - "Solidity/Calculus/Taclet.lean"
  - "Solidity/Calculus/Completeness.lean"
  - "Solidity/Calculus/RuleShapes.lean"
  - "Solidity/Calculus/PrintedRules.lean"
  - "Solidity/Calculus/KeyTaclets.lean"
  - "Solidity/SortCheck/*.lean"
---

# The rule table

A taclet is one constructor of `Taclet C k m s p` (`Calculus/Rules.lean`),
named as solkey names it, its type written in `dl{ ⟨[ s; ]⟩ ⇝ p }` and read,
under `open scoped Solidity.Schema`, at a scoped statement `s : Stmt C Γ Γ'`
(`RuleSyntax.schemaTacletCore` inserts the shifts under a fresh local, its
`pop .capture` and the hidden binder of a declaration). Schema
variables are bound implicitly and their kind is read off their name
(`RuleSyntax.lean`'s table: `sp`/`nsp`, `se`/`nse`, `fld`, `lhs`, …), and so
are the rule's side conditions (`RuleSyntax.sideConds`: `nsp` is not simple,
`sp` is, a value written to storage is not a conditional, …), hidden
`autoParam` hypotheses. Which rule fires is `Stmt.step` (`Calculus/Step.lean`,
its arms in `Arms.lean` and `Blocks.lean`), a total function over the scoped
syntax, and every constructor's premise is the one it builds:
`Taclet.toStep` (alias `step_eq`, `Calculus/Taclet.lean`). The converse is
`Stmt.rule_exists` (`Calculus/RuleExists.lean`); `ruleOf?`
(`Completeness.lean`) names the rule fired.

## Invariants

- No `sorry`, `native_decide` or `axiom` under `Solidity/Calculus/`.
- **Types, not predicates.** A statement no rule can run is a typing problem:
  change the syntax (`Syntax.lean`) so it cannot be written. Never add a
  well-formedness hypothesis.
- One rule, one constructor; the modality is a parameter (`⟨[ ]⟩`), not a
  box/diamond twin. Only `revertBox`/`revertDiamond` tell them apart (and
  the loop invariant rules). `sol_chain` relies on it: it runs a line under a
  modality `m` as the diamond and as the box and keeps the lines they share
  (`Chains.runChain`), so a rule that cases on `m` must give premises that
  differ elsewhere than in the modality (as revert's `true`/`false` do);
  otherwise `sol_chain` writes a line under `m` the kernel rejects.
  `CallbackTaclet` (the other `transferSemantics`, sound for `holdsC`, not
  for `holds`) is a separate inductive and keeps solkey's box/diamond pair.
- Every theorem has a docstring with a small Solidity example.
- Example contracts are **named** `Contract` constants: the quoters and the
  kernel re-check rely on it. A new syntax constructor needs an arm in every
  quoter (`Syntax/Quote.lean`, `Calculus/Quote.lean`, and the erased side's
  in `Syntax.lean`, `Calculus/SurfaceNotation.lean`), and an arm in
  `Syntax/Resolve.lean`'s `resolve`/`erase`.

## Adding or changing a rule

1. The constructor, in its section of `Calculus/Rules.lean`, in `dl{ … }`. Spell its
   schema variables so that the side conditions they give it
   (`RuleSyntax.sideConds`) are **exactly** what its `Stmt.step` arm knows:
   `nsp`/`nse` where the arm has found the part not simple, `sp` where it
   has found it simple, `path`/`e` where it does not look. Check with
   `set_option pp.sol.dl false in #check @Taclet.r`.  Two variables of one
   kind are numbered with subscripts (`mv₁`/`mv₂`, `se₁`/`se₂`), the
   spelling the existing rules use; `sp1`/`sp2` in the storage copy rules
   (`storageFieldWriteCopySource`, `storageIndexWrite*CopySource`) are the
   ASCII exception, KeY's own spelling there.  Write labels as solkey does
   (`"Holds": …`) and keep `Taclet.branchLabels` equal to them
   (`Examples/ProofTree.lean` checks it).
2. Its arm in `Stmt.step` (`Calculus/Arms.lean`, `Blocks.lean`; the
   dispatcher in `Calculus/Step.lean`, one `casesOn`, Gate G0's condition 1).
   Exhaustiveness is the coverage proof, so a statement form without an arm
   fails the build. Its lemma `Taclet.<rule>.toStep` (`Calculus/Taclet.lean`:
   a `#replay_toStep` row from `#derive_toStep?`, or by hand) fails if a side
   condition is weaker than the arm (two rules for one statement), and
   `Stmt.<c>.ruleExists` (`RuleExists.lean`, `#replay_ruleExists`) if it is
   stronger (no rule).
3. Its arm's soundness, `Stmt.StepSound` of the arm (`…_sound` in
   `Calculus/SoundArms.lean` for an update premise, `SoundStore`,
   `SoundMem`, `SoundLocal`, `SoundControl`, `SoundCapture`; `SoundCalls`,
   `SoundLoops` for the blocks), dispatched by `SoundStep.lean` into
   `Stmt.sound` (`.claude/rules/soundness.md`). There is no proof per
   taclet: `toStep` makes it `Stmt.sound`'s.
4. Its row in `RuleShapes.tacletOrigins` (the solkey taclets it transcribes)
   and in `PrintedRules.printedOrigins`. `#check_constructor_table` fails the
   build on a missing or extra row; `taclets_partitioned` and
   `printed_rules_partitioned` move with it.
5. A taclet that reads storage or memory: its row in
   `SortCheck/Annotations.lean`, then `lake exe solkeycheck`.

`docs/lean-key-rule-map.md` is the authority for the correspondence to
solkey's taclet names. Do not restate it in a docstring or a banner.

## Sharp edges

- Kernel-evaluated code takes a context-indexed family (`Stmt`, `Prog`,
  `Frames`, `Fml`, `Args`) apart by `casesOn` with a motive over its indices,
  never by `match` (Gate G0, `docs/intrinsic.md`); a `match` is fine on the
  expression families, whose context is a parameter, and at elaboration
  time.
- `tyHasMapping` and other well-founded definitions do not reduce in the
  kernel, so a proof of them cannot be `Eq.refl`; carry a structural twin
  (`Ty.mapFree`) and prove it equal.
- `lake env lean --tstack=131072 file.lean` checks a scratch file in
  seconds; the MCP server is slow on this package.
