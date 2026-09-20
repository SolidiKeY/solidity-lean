---
paths:
  - "Solidity/Calculus/Rules.lean"
  - "Solidity/Calculus/RuleSyntax.lean"
  - "Solidity/Calculus/RuleShapes.lean"
  - "Solidity/Calculus/RuleValidation.lean"
  - "Solidity/Calculus/Uniqueness.lean"
  - "Solidity/Calculus/Coverage.lean"
  - "Solidity/Calculus/Completeness.lean"
  - "Solidity/Calculus/KeyTaclets.lean"
  - "Solidity/Calculus/PaperRules.lean"
  - "Solidity/SortCheck/*.lean"
---

# The rule table

`RuleName`, `ruleEffect`, `ruleNames` and `twinPairs` are **generated** from
the `sol_rule` declarations by `sol_assemble_rules`. Do not hand-edit them.

**Declaration order is the order of all four.** Put a new rule under the
section its banner names, and write a box twin before its diamond twin
(`twins` does both at once and fills `twinPairs`; `CandidateStep.twins_box_first`
checks it). `FirstStepCase` takes the first applicable rule under `.both`, so
the order decides which name a `⇝[.rule]` derivation pins.

## Adding or changing a rule

1. One `sol_rule` declaration, in the right section.
2. The condition is generated from the schema variables' *names*
   (`RuleSyntax.schemaVar`): `sp.fld = se` already says
   `isSimple sp ∧ isSe se`. `where` appends conjuncts no name carries;
   `where cond := …` replaces the conjunction outright, for the handful
   whose applicability is a bespoke predicate. A residual that has to be
   *computed* from the condition proof is written `⟦ b ⟧`, with the proof in
   scope as `h` — five rules. There is no other form: the declaration is how
   a rule is written.
3. **Keep the condition disjoint from every other rule.** Then add the
   `candidate` dispatch branch and the `applicable_eq_candidate` case in
   `Calculus/Uniqueness.lean`. A failing uniqueness build signals an overlap.
4. Non-empty residual ⇒ add a `Calculus/RuleValidation.lean` entry.
5. The taclet reads storage/memory (`find`/`read`/`selectSt`/`valAt`/
   `defaultValue`) ⇒ add or extend its `TacletReadAnn` row in
   `SortCheck/Annotations.lean`, keep `sortFaithful_all` closing (extend
   `ruleNumericTarget`/`ruleRefTarget` for new `fixed`-sorted value reads),
   then run `lake exe solkeycheck`.
6. Give the rule its paper origin in `Calculus/PaperRules.lean`
   (`paperOrigin`): the paper rule it is, the rules it merges, or
   `leanOnly` with its reason (`keyTier` — solkey has it, the paper does not;
   `plumbing` — this syntax's own normalisation; `calculus` — theory the
   paper is to gain).  `paper_rules_partitioned` and the count theorems
   move with it; `./scripts/check-paper-rules.mjs` checks the enumeration
   against `rules/*.tex`.

**Names are the paper's.** A rule is spelled as the paper spells it where the
paper has it (`storageFieldWrite_unfold_leftFst` → `storageFieldWriteUnfoldLeftFst`),
and as solkey spells it otherwise.  A residual binds four fixed scratch names,
the paper's kind-names: `se` (a value), `ie` (an index), `sp` (a storage
path), `mv` (a memory path).  KeY mints fresh names instead, so a capture
whose source already is `se` is not repeated (`Rules.freezeRhs`); write the
matched value `se1` and the generated one `se`, as the paper numbers them.

## Three traps

**A generated `ruleEffect` arm never has a catch-all `| _ => []`.** `block` is
dependent on the condition proof, so the generator passes that proof as a
second match discriminant and lists only the arms the `cond` admits — the
match compiler refutes the rest, because the proof's type reduces to `False`
there. An empty residual therefore means *terminal rule* and nothing else. A
`(lhs : WrappedExpr)` scrutinee is destructured as
`match lhs, h with | ⟨PAT, _⟩, _ => …`, because the condition reaches `block`
as an unreduced beta-redex.

**A parameterized family** (`(op : BinOp)` and friends) expands to every
instance in `ruleNames` on its own — classification requires them all, so
give a KeY-absent instance an unsatisfiable conjunct, which is what the
binder guard `(op : BinOp | op.isArith = true)` writes.

**A new `*Effect` builder has to be declared twice more.** `Tactics/Derivation.lean`
lists every builder under `attribute [reducible]` and under
`attribute [rule_simp_set]`; a builder missing from either makes `single_step`
fail to synthesise `Decidable` for that rule's condition, with no hint that
the list is where to look.

## Facts about the table

There is no catch-all tier: a statement no rule matches is stuck, and
`Calculus/Coverage.lean` proves the stuck set is exactly the documented `ResidueShape`s.
Membership proofs over `ruleNames` use `decide` (`simp [ruleNames]` exceeds
the recursion limit).

`docs/lean-key-rule-map.md` is the authority for the correspondence to
solkey's taclet names. Do not restate it in a docstring or a banner.
