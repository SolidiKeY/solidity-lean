---
paths:
  - "Solidity/Rules.lean"
  - "Solidity/RuleSyntax.lean"
  - "Solidity/Uniqueness.lean"
  - "Solidity/RuleValidation.lean"
  - "Solidity/RuleShapes.lean"
  - "Solidity/TacletAnnotations.lean"
  - "Solidity/KeyTaclets.lean"
  - "Solidity/Coverage.lean"
  - "Solidity/Completeness.lean"
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
   `where cond := …` replaces the conjunction outright. Reach for
   `sol_rule NAME … := <term>` only when the goals consume the condition
   proof or the condition is bespoke — about ten rules.
3. **Keep the condition disjoint from every other rule.** Then add the
   `candidate` dispatch branch and the `applicable_eq_candidate` case in
   `Uniqueness.lean`. A failing uniqueness build signals an overlap.
4. Non-empty residual ⇒ add a `RuleValidation.lean` entry.
5. The taclet reads storage/memory (`find`/`read`/`selectSt`/`valAt`/
   `defaultValue`) ⇒ add or extend its `TacletReadAnn` row in
   `TacletAnnotations.lean`, keep `sortFaithful_all` closing (extend
   `ruleNumericTarget`/`ruleRefTarget` for new `fixed`-sorted value reads),
   then run `lake exe solkeycheck`.

## Two traps

**A generated `ruleEffect` arm never has a catch-all `| _ => []`.** `block` is
dependent on the condition proof, so pass that proof as a second match
discriminant and list only the arms the `cond` admits — the match compiler
refutes the rest, because the proof's type reduces to `False` there. An empty
residual therefore means *terminal rule* and nothing else. A `(lhs :
WrappedExpr)` scrutinee has to destructure the place,
`match lhs, h with | ⟨PAT, _⟩, _ => …`, because the condition reaches `block`
as an unreduced beta-redex.

**A parameterized family** (`(op : BinOp)` and friends) expands to every
instance in `ruleNames` on its own — classification requires them all, so
give a KeY-absent instance an unsatisfiable guard conjunct.

## Facts about the table

There is no catch-all tier: a statement no rule matches is stuck, and
`Coverage.lean` proves the stuck set is exactly the documented `ResidueShape`s.
Membership proofs over `ruleNames` use `decide` (`simp [ruleNames]` exceeds
the recursion limit).

`docs/lean-key-rule-map.md` is the authority for the correspondence to
solkey's taclet names. Do not restate it in a docstring or a banner.
