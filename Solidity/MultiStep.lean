import Solidity.Completeness

namespace Solidity

/-- One execution step of a block: rewrite the head statement with a rule. -/
inductive BlockStep : SolidityBlock → SolidityBlock → Prop where
  | head {sm : SolidityModality} {lhs : Stmt} {cond : Prop}
      {rhs rest : Block} :
      RuleStep sm lhs cond rhs →
      BlockStep ⟨sm, lhs :: rest⟩ ⟨sm, rhs ++ rest⟩

/-- One execution step of a block by a **named** rule.

`BlockStep` goes through `RuleStep`, which hides the `StepCase` behind an
existential (`Completeness.lean`), so the rule that fired is not visible in the
type.  Here the rule name is an index, exactly as in `TerminalRuleStep`
(`Wp/TerminalRules.lean`) -- generalized to a nonempty residual.  That is
what lets a derivation write the rule on the arrow (`b ⇝[.rule] b'`) and have
Lean check the claim.

The successor is a free index constrained by an equation rather than the
positional `⟨sm, rhs ++ rest⟩` of `BlockStep.head`: against a written-out
successor the unifier cannot invert `?rhs ++ rest =?= literal`, which is why
`named_step` had to be an elaborator.  With the equation, the residual check is
an ordinary `rfl` *after* the `FirstStepCase` proof has determined `rhs`. -/
inductive NamedBlockStep (r : RuleName) : SolidityBlock → SolidityBlock → Prop where
  | head {sm : SolidityModality} {lhs : Stmt} {cond : Prop}
      {rhs rest : Block} {after : SolidityBlock} :
      FirstStepCase sm lhs Rules.stepCases (Rules.stepCase r) cond rhs →
      after = ⟨sm, rhs ++ rest⟩ →
      NamedBlockStep r ⟨sm, lhs :: rest⟩ after

/-- One or more steps: the transitive closure of `BlockStep`,
reused from the core library. -/
abbrev BlockMultiStep : SolidityBlock → SolidityBlock → Prop :=
  Relation.TransGen BlockStep

/-- Zero or more steps: the reflexive-transitive closure of `BlockStep`. -/
inductive BlockReflMultiStep : SolidityBlock → SolidityBlock → Prop where
  | refl {block : SolidityBlock} :
      BlockReflMultiStep block block
  | step {before middle after : SolidityBlock} :
      BlockStep before middle →
      BlockReflMultiStep middle after →
      BlockReflMultiStep before after

/-! ## Notation

The calculus writes symbolic execution as a chain of `⇝` lines,
with `⇝*` standing for a run of several steps
.  The Lean spellings mirror that:
`⇝` is one step, `⇝*` several (possibly zero), `⇝[.rule]` one step by a named
rule -- where the calculus attributes the rule in prose, Lean puts it in the type.
-/

@[inherit_doc] scoped infix:50 " ⇝ "  => BlockStep
@[inherit_doc] scoped infix:50 " ⇝⁺ " => BlockMultiStep
@[inherit_doc] scoped infix:50 " ⇝* " => BlockReflMultiStep
-- `notation` placeholders carry a precedence, not a syntax category, so the
-- rule sits at precedence 0: the closing `]` is what terminates it, which is
-- what lets an applied constructor (`⇝[.storageRootIncDec .postInc]`) be
-- written without parentheses.
@[inherit_doc] scoped notation:50 before:51 " ⇝[" rule:0 "] " after:51 =>
  NamedBlockStep rule before after

/-! The `—→`/`—→⁺`/`—↠` arrows this file used to define.  Input-only sugar: a
second `infix` for the same constant would give a second unexpander and make
goal display order-dependent, so these parse but never print -- every goal and
error message shows `⇝`. Delete them once the remaining `Examples/` files and
`Progress.lean` have moved over. -/
syntax:50 term:51 " —→ "  term:51 : term
syntax:50 term:51 " —→⁺ " term:51 : term
syntax:50 term:51 " —↠ "  term:51 : term

macro_rules
  | `($a —→ $b)  => `(BlockStep $a $b)
  | `($a —→⁺ $b) => `(BlockMultiStep $a $b)
  | `($a —↠ $b)  => `(BlockReflMultiStep $a $b)

/-! ### ASCII input forms

`⇝` and `⇝*` are the glyphs the calculus draws, so they stay the ones goals print.
But a `⇝` has to be typed, and on a keyboard without an input method the whole
derivation vocabulary is out of reach.  `~>`, `~>*` and `~>[r]` are the ASCII
twins, and -- exactly like the `—→` family above -- they are *input only*: a
second `infix` for the same constant would give a second unexpander and make
goal display depend on which one was parsed last, so these are `syntax` +
`macro_rules` and every goal, error message and `#check` still shows `⇝`. -/

syntax:50 term:51 " ~> "  term:51 : term
syntax:50 term:51 " ~>⁺ " term:51 : term
syntax:50 term:51 " ~>* " term:51 : term
-- Precedence 0 for the rule, as in the `⇝[...]` notation: the closing `]` is
-- what terminates it, so an applied constructor needs no parentheses.
syntax:50 term:51 " ~>[" term:0 "] " term:51 : term

macro_rules
  | `($a ~> $b)  => `(BlockStep $a $b)
  | `($a ~>⁺ $b) => `(BlockMultiStep $a $b)
  | `($a ~>* $b) => `(BlockReflMultiStep $a $b)
  | `($a ~>[$r] $b) => `(NamedBlockStep $r $a $b)

namespace BlockReflMultiStep

theorem trans {a b c : SolidityBlock} :
    a ⇝* b → b ⇝* c → a ⇝* c := by
  intro hab hbc
  induction hab with
  | refl => exact hbc
  | step h _ ih => exact step h (ih hbc)

theorem single {a b : SolidityBlock} (h : a ⇝ b) : a ⇝* b :=
  step h refl

end BlockReflMultiStep

instance : Trans BlockStep BlockReflMultiStep BlockReflMultiStep :=
  ⟨BlockReflMultiStep.step⟩

instance : Trans BlockReflMultiStep BlockReflMultiStep BlockReflMultiStep :=
  ⟨BlockReflMultiStep.trans⟩

instance : Trans BlockStep BlockStep BlockReflMultiStep :=
  ⟨fun hab hbc => .step hab (.single hbc)⟩

instance : Trans BlockReflMultiStep BlockStep BlockReflMultiStep :=
  ⟨fun hab hbc => hab.trans (.single hbc)⟩

namespace NamedBlockStep

/-- Forget which rule fired. -/
theorem toBlockStep {r : RuleName} {a b : SolidityBlock}
    (h : NamedBlockStep r a b) : a ⇝ b := by
  cases h with
  | head hfirst heq => subst heq; exact BlockStep.head (RuleStep.ofStepCase hfirst)

theorem toReflMultiStep {r : RuleName} {a b : SolidityBlock}
    (h : NamedBlockStep r a b) : a ⇝* b :=
  BlockReflMultiStep.single h.toBlockStep

end NamedBlockStep

/-! `Trans` instances mixing named steps into a `⇝*` chain.  `calc` reads the
relation as everything before the last two explicit arguments, so the relation
of `a ⇝[r] b` is the partial application `NamedBlockStep r` -- the same shape as
`Relation.ReflTransGen r`, and these instances resolve for it. -/

instance {r₁ r₂ : RuleName} :
    Trans (NamedBlockStep r₁) (NamedBlockStep r₂) BlockReflMultiStep :=
  ⟨fun hab hbc => .step hab.toBlockStep (.single hbc.toBlockStep)⟩

instance {r : RuleName} :
    Trans (NamedBlockStep r) BlockReflMultiStep BlockReflMultiStep :=
  ⟨fun hab hbc => .step hab.toBlockStep hbc⟩

instance {r : RuleName} :
    Trans BlockReflMultiStep (NamedBlockStep r) BlockReflMultiStep :=
  ⟨fun hab hbc => hab.trans hbc.toReflMultiStep⟩

instance {r : RuleName} :
    Trans (NamedBlockStep r) BlockStep BlockReflMultiStep :=
  ⟨fun hab hbc => .step hab.toBlockStep (.single hbc)⟩

instance {r : RuleName} :
    Trans BlockStep (NamedBlockStep r) BlockReflMultiStep :=
  ⟨fun hab hbc => .step hab (.single hbc.toBlockStep)⟩

/-! ## The judgment layer

The same rewriting, on a full dynamic-logic judgment `⟨[ program ]⟩ post`
instead of a bare block: one taclet application rewrites the program inside
the modality and leaves the postcondition untouched, which is how the calculus
draws every one of its chains (73 of them -- the
postcondition `φ` is on every line).

These live here, beside `BlockStep`, rather than in
`Examples/Derivations/DynamicLogic.lean` where they started: they depend on
nothing but the AST and the rules, and `sol_derivation` has to be able to
build either layer from the same source syntax. `DynamicLogic.lean` keeps the
worked examples and the `ite_split` material. -/

/-- One dynamic-logic step: rewrite the head statement of the program
with a taclet, keeping modality and postcondition. -/
inductive JudgmentStep : SolidityJudgment → SolidityJudgment → Prop where
  | prog {before after : SolidityBlock} {post : WrappedExpr} :
      BlockStep before after →
      JudgmentStep (SolidityJudgment.mk before post)
        (SolidityJudgment.mk after post)

/-- One dynamic-logic step by a *named* taclet: the judgment-level twin of
`NamedBlockStep`, so the rule can be written on the arrow here too. -/
inductive NamedJudgmentStep (r : RuleName) :
    SolidityJudgment → SolidityJudgment → Prop where
  | prog {before after : SolidityBlock} {post : WrappedExpr} :
      NamedBlockStep r before after →
      NamedJudgmentStep r (SolidityJudgment.mk before post)
        (SolidityJudgment.mk after post)

/-- Zero or more dynamic-logic steps. -/
inductive JudgmentMultiStep : SolidityJudgment → SolidityJudgment → Prop where
  | refl {j : SolidityJudgment} : JudgmentMultiStep j j
  | step {a b c : SolidityJudgment} :
      JudgmentStep a b → JudgmentMultiStep b c → JudgmentMultiStep a c

@[inherit_doc] scoped infix:50 " ⇝ᵈ "  => JudgmentStep
@[inherit_doc] scoped infix:50 " ⇝ᵈ* " => JudgmentMultiStep
@[inherit_doc] scoped notation:50 before:51 " ⇝ᵈ[" rule:0 "] " after:51 =>
  NamedJudgmentStep rule before after

/-- ASCII input forms for the judgment arrows, input-only like `~>`. -/
syntax:50 term:51 " ~>d "  term:51 : term
syntax:50 term:51 " ~>d* " term:51 : term
syntax:50 term:51 " ~>d[" term:0 "] " term:51 : term

macro_rules
  | `($a ~>d $b)  => `(JudgmentStep $a $b)
  | `($a ~>d* $b) => `(JudgmentMultiStep $a $b)
  | `($a ~>d[$r] $b) => `(NamedJudgmentStep $r $a $b)

theorem JudgmentMultiStep.trans {a b c : SolidityJudgment} :
    JudgmentMultiStep a b → JudgmentMultiStep b c → JudgmentMultiStep a c := by
  intro hab hbc
  induction hab with
  | refl => exact hbc
  | step h _ ih => exact .step h (ih hbc)

/-- Lift a whole block-level `⇝*` derivation to the judgment layer: the
postcondition rides along unchanged.  This is what lets a judgment
derivation elide a run of steps without restating the postcondition on
every intermediate line. -/
theorem JudgmentMultiStep.ofBlock {before after : SolidityBlock}
    {post : WrappedExpr} (h : before ⇝* after) :
    JudgmentMultiStep (SolidityJudgment.mk before post)
      (SolidityJudgment.mk after post) := by
  induction h with
  | refl => exact .refl
  | step hstep _ ih => exact .step (.prog hstep) ih

namespace NamedJudgmentStep

theorem toJudgmentStep {r : RuleName} {a b : SolidityJudgment}
    (h : NamedJudgmentStep r a b) : a ⇝ᵈ b := by
  cases h with
  | prog hstep => exact JudgmentStep.prog hstep.toBlockStep

theorem toMultiStep {r : RuleName} {a b : SolidityJudgment}
    (h : NamedJudgmentStep r a b) : a ⇝ᵈ* b :=
  .step h.toJudgmentStep .refl

end NamedJudgmentStep

instance : Trans JudgmentStep JudgmentMultiStep JudgmentMultiStep :=
  ⟨JudgmentMultiStep.step⟩

instance : Trans JudgmentStep JudgmentStep JudgmentMultiStep :=
  ⟨fun h₁ h₂ => .step h₁ (.step h₂ .refl)⟩

instance : Trans JudgmentMultiStep JudgmentStep JudgmentMultiStep :=
  ⟨fun h₁ h₂ => h₁.trans (.step h₂ .refl)⟩

instance : Trans JudgmentMultiStep JudgmentMultiStep JudgmentMultiStep :=
  ⟨JudgmentMultiStep.trans⟩

instance {r₁ r₂ : RuleName} :
    Trans (NamedJudgmentStep r₁) (NamedJudgmentStep r₂) JudgmentMultiStep :=
  ⟨fun h₁ h₂ => .step h₁.toJudgmentStep h₂.toMultiStep⟩

instance {r : RuleName} :
    Trans (NamedJudgmentStep r) JudgmentMultiStep JudgmentMultiStep :=
  ⟨fun h₁ h₂ => .step h₁.toJudgmentStep h₂⟩

instance {r : RuleName} :
    Trans JudgmentMultiStep (NamedJudgmentStep r) JudgmentMultiStep :=
  ⟨fun h₁ h₂ => h₁.trans h₂.toMultiStep⟩

instance {r : RuleName} :
    Trans (NamedJudgmentStep r) JudgmentStep JudgmentMultiStep :=
  ⟨fun h₁ h₂ => .step h₁.toJudgmentStep (.step h₂ .refl)⟩

instance {r : RuleName} :
    Trans JudgmentStep (NamedJudgmentStep r) JudgmentMultiStep :=
  ⟨fun h₁ h₂ => .step h₁ h₂.toMultiStep⟩

namespace MultiStepExamples

example (b1 b2 b3 : SolidityBlock)
    (h1 : b1 ⇝ b2) (h2 : b2 ⇝ b3) :
    b1 ⇝* b3 :=
  calc
    b1 ⇝ b2 := h1
    _  ⇝ b3 := h2

example (b1 b2 b3 b4 : SolidityBlock)
    (h1 : b1 ⇝ b2) (h2 : b2 ⇝ b3) (h3 : b3 ⇝ b4) :
    b1 ⇝* b4 :=
  calc
    b1 ⇝ b2 := h1
    _  ⇝ b3 := h2
    _  ⇝ b4 := h3

/-- `calc` accepts the rule-indexed relation and mixes it with `⇝` and `⇝*`.
Abstract in the rules and the blocks, so this costs nothing to elaborate and
still breaks if a `Trans` instance goes missing. -/
example (r₁ r₂ : RuleName) (b1 b2 b3 b4 b5 : SolidityBlock)
    (h1 : b1 ⇝[r₁] b2) (h2 : b2 ⇝[r₂] b3) (h3 : b3 ⇝* b4) (h4 : b4 ⇝ b5) :
    b1 ⇝* b5 :=
  calc
    b1 ⇝[r₁] b2 := h1
    _  ⇝[r₂] b3 := h2
    _  ⇝*    b4 := h3
    _  ⇝     b5 := h4

/-- The old arrows still parse (input-only sugar). -/
example (b1 b2 : SolidityBlock) (h : b1 —→ b2) : b1 —↠ b2 :=
  BlockReflMultiStep.single h

end MultiStepExamples

end Solidity
