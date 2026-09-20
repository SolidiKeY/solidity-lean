import Solidity.Update.Eval
import Solidity.Calculus.MultiStep

/-!
# Sequents: a derivation line as the calculus writes it

`Calculus/MultiStep.lean` rewrites *programs*: `solbox!{ … } ⇝ solbox!{ … }`, every
chain ending at the empty block.  That is one half of a derivation.  The
calculus writes the other half on the same line -- the accumulated update --
and its chains end not at an empty program but at a formula under an update:

```
   ⟨[alice.account.balance = 10;]⟩φ
⇝  ⟨[uint rv = 10; Account storage sp = alice.account; sp.balance = rv;]⟩φ
⇝* {rv := 10 ‖ sp := alice·account} ⟨[sp.balance = rv;]⟩φ
⇝  {rv := 10 ‖ sp := alice·account ‖ storage := save(storage, alice·account·balance, 10)} φ
```

This module is the line of such a chain, and the step between two lines.

## What a line is

A **`Sequent`** is `Γ ⟹ {U₁}…{Uₙ} goal`: an antecedent, a *sequential* stack
of parallel updates, and either a program under a modality (`SeqGoal.prog`) or
a bare formula (`SeqGoal.obl`, the calculus's `⊤`/`⊥` and its real
obligations).  A **`Frontier`** is a list of them, because a guarded rule
produces a list: the calculus draws the last line of an array access as two
stacked sequents, the in-bounds goal and `⊤`.

The update stack is a `List UpdTerm` and not an `Upd`, deliberately.  A rule
*states* its update as first-order syntax (`Calculus/Rules.lean`), and keeping the
syntax is what lets two spellings of the same update be compared -- which is
what the calculus's last line does.  `Sequent.upd` is the meaning, and
`Sequent.Equiv` the comparison.

## What a step is

`NamedFrontierStep r` rewrites the **first open sequent** (`firstOpen?`: the
first whose goal still has a head statement) into the sequents its goals name,
one per goal whose mode applies.  That is `Update/Wp.lean`'s reading of a
taclet made into a relation: each goal contributes
`guard → {update}⟨residual ++ rest⟩post`, so the guard becomes an antecedent
and the update is pushed onto the stack.

The rule is an index and the successor a free variable pinned by an equation,
exactly as in `NamedBlockStep` -- so a derivation writes the rule on the arrow
and the successor check is `rfl` once `find_pinned_step` has determined the
rule's goals.  The split itself is *computed* (`firstOpen?`), not positional,
so `hsq` is `rfl` too.

## The line that is not a rule application

The last line of almost every chain upstream is the **merge**: two stacked
updates collapse into one parallel update, with the second one's right-hand
side re-read in the first one's result.  That is not a step of the rule set,
so it is not a `FrontierStep`; it is `FrontierMultiStep.equiv` over
`Frontier.Equiv`, whose content is `Sequent.upd a = Sequent.upd b` -- an
equality of state functions, proved from `Upd.Par.seq_single` and the reader
lemmas at the end of this file (the `upd_merge` tactic of
`Tactics/Derivation.lean` is that proof, automated).

What is *not* here: soundness.  `Sequent.check` is the semantics, and each
worked derivation checks its own endpoints against it
(`SolidityPaper.lean`); the general
`FrontierStep a b → (a.Holds s ↔ b.Holds s)` needs the per-rule bridges of
`Update/TacletTable.lean` (21 of the 95 rules with an update) and
`Rules.assertGoals` is deliberately not exhaustive (`Update/Wp.lean`), so it
is a separate result.
-/

namespace Solidity

open Semantics Rules Update

/-! ## The line -/

/-- What is left of a sequent's succedent: a program under a modality, or a
bare formula.  The calculus's `⊤` is `obl (.const true)`. -/
inductive SeqGoal where
  /-- `⟨[ π ω ]⟩φ` -- the modality is the block's, and the postcondition rides
  along here rather than on the sequent: a goal with no program left has no
  postcondition to read, and a rule that turns one into the other (`revertBox`)
  would otherwise have to invent a placeholder. -/
  | prog (b : SolidityBlock) (post : WrappedExpr)
  /-- `{U}ψ` with no program left: `⊤`, `⊥`, `0 ≤ se ≤ selfBalance`, … -/
  | obl (φ : SideFormula)
  deriving Repr

/-- One line of a derivation: `Γ ⟹ {U₁}…{Uₙ} goal`.

`ante` is the calculus's antecedent, each formula paired with the update stack
it is read under (the diamond `transfer`'s funds obligation is read under the
capture that precedes it, `main.tex` § "Example: Symbolic Execution of
`to.transfer(x + 2)`").  `upds` is the *sequential* stack: `{U₁}{U₂}` applied
left to right, each `UpdTerm` itself a parallel update. -/
structure Sequent where
  ante : List (List UpdTerm × SideFormula) := []
  upds : List UpdTerm := []
  goal : SeqGoal
  deriving Repr

/-- A derivation line: the sequents a guarded rule leaves open at once. -/
abbrev Frontier := List Sequent

/-- `{U₁}…{Uₙ}` as one update: applied left to right, which is `Upd.seq`'s
Kleisli composition. -/
def stackUpd : List UpdTerm -> Upd :=
  List.foldr (fun u acc => Upd.seq (UpdTerm.toUpd u) acc) Upd.id

@[simp] theorem stackUpd_nil : stackUpd [] = Upd.id := rfl

@[simp] theorem stackUpd_cons (u : UpdTerm) (us : List UpdTerm) :
    stackUpd (u :: us) = Upd.seq (UpdTerm.toUpd u) (stackUpd us) := rfl

/-- Appending a line to the stack is composing on the right, which is what a
terminal rule does to the accumulated update. -/
theorem stackUpd_append (us vs : List UpdTerm) :
    stackUpd (us ++ vs) = Upd.seq (stackUpd us) (stackUpd vs) := by
  induction us with
  | nil => simp [Upd.id_seq]
  | cons u rest ih => simp only [List.cons_append, stackUpd_cons, ih, Upd.seq_assoc]

namespace Sequent

/-- The update the line has accumulated. -/
def upd (q : Sequent) : Upd := stackUpd q.upds

/-- Read a formula under a stack, in the state the line starts from. -/
def formulaUnder (U : List UpdTerm) (φ : SideFormula) (s0 : State) : Res Bool :=
  stackUpd U s0 >>= fun s => SideFormula.eval s φ

/-- Is some antecedent false?  Then the sequent holds vacuously.  A
*halting* antecedent is not false -- it is a reading that went wrong, and
nothing is validated. -/
def anteVerdict (s0 : State) : List (List UpdTerm × SideFormula) -> Option Bool
  | [] => none
  | (U, φ) :: rest =>
      match formulaUnder U φ s0 with
      | .ok false => some true
      | .ok true => anteVerdict s0 rest
      | .error _ => some false

/-- Run a line, given its four *semantic* components.  Split out of `check`
so that `Sequent.Equiv.check_eq` is one `simp only`: two lines that agree on
these four agree on the verdict, whatever their update stacks look like. -/
def checkOf (ante : List (List UpdTerm × SideFormula)) (u : Upd)
    (goal : SeqGoal) (s0 : State) : Bool :=
  match anteVerdict s0 ante with
  | some v => v
  | none =>
      match u s0 with
      | .ok s =>
          match goal with
          | .prog b post => (SolidityJudgment.mk b post).check s
          | .obl φ => match SideFormula.eval s φ with
                      | .ok b => b
                      | .error _ => false
      | .error .revert =>
          match goal with
          | .prog b _ => b.modality = SolidityModality.box
          | .obl _ => false
      | .error .stuck => false

/-- Run the line.  The verdict shape is `SolidityJudgment.check`'s, which is
also `RuleGoal.check`'s (`Update/Wp.lean`): a stuck run validates nothing, a
`revert` validates a box judgment and refutes a diamond one, and an
obligation with no program left is read as a formula. -/
def check (q : Sequent) (s0 : State := State.exampleStore) : Bool :=
  checkOf q.ante q.upd q.goal s0

/-- Validity of a derivation line. -/
def Holds (q : Sequent) (s0 : State := State.exampleStore) : Prop :=
  q.check s0 = true

instance (q : Sequent) (s0 : State) : Decidable (q.Holds s0) :=
  inferInstanceAs (Decidable (q.check s0 = true))

/-- A line is **open** when its goal still has a statement to execute: those
are the ones a step rewrites. -/
def isOpen : Sequent -> Bool
  | ⟨_, _, .prog ⟨_, _ :: _⟩ _⟩ => true
  | _ => false

end Sequent

namespace Frontier

/-- Every line of the frontier holds. -/
def check (f : Frontier) (s0 : State := State.exampleStore) : Bool :=
  f.all (fun q => q.check s0)

def Holds (f : Frontier) (s0 : State := State.exampleStore) : Prop :=
  f.check s0 = true

instance (f : Frontier) (s0 : State) : Decidable (f.Holds s0) :=
  inferInstanceAs (Decidable (f.check s0 = true))

/-- No line has a statement left to execute.  This is the frontier a KeY
proof ends at: every line is either a formula under the accumulated update or
an empty program under it, and nothing the rule set can fire on remains.

It is what makes "the rules drove this program" a claim rather than a
tautology: `⇝ᵘ*` is reflexive, so a target that is merely *reachable* can be
the start itself. -/
def isClosed (f : Frontier) : Bool :=
  f.all (fun q => !q.isOpen)

@[simp] theorem isClosed_nil : isClosed [] = true := rfl

/-- Split at the first open line: the closed lines before it, that line, and
the rest.  Computed rather than guessed, so a step's `hsq` is `rfl`. -/
def firstOpen? : Frontier -> Option (Frontier × Sequent × Frontier)
  | [] => none
  | q :: rest =>
      if q.isOpen then some ([], q, rest)
      else match firstOpen? rest with
        | some (before, open_, after) => some (q :: before, open_, after)
        | none => none

/-- Closure is exactly "no first open line", which is the form the step
relation and the tactics test. -/
theorem firstOpen?_eq_none_iff (f : Frontier) :
    firstOpen? f = none <-> isClosed f = true := by
  induction f with
  | nil => simp [firstOpen?, isClosed]
  | cons q rest ih =>
      -- Unfold `isClosed` at the head only: unfolding it on the tail as well
      -- replaces the induction hypothesis' right-hand side by a membership
      -- statement `ih` no longer matches.
      rw [show isClosed (q :: rest) = (!q.isOpen && isClosed rest) from rfl]
      cases hq : q.isOpen
      · cases h : firstOpen? rest
        · simpa [firstOpen?, hq, h] using ih.mp h
        · have hne : isClosed rest ≠ true := by
            intro hc
            rw [ih.mpr hc] at h
            exact Option.noConfusion h
          refine iff_of_false ?_ ?_
          · simp [firstOpen?, hq, h]
          · simpa [hq] using hne
      · simp [firstOpen?, hq]

end Frontier

/-! ## The successors of a rule application -/

namespace Update

/-- Push a rule's update onto the stack.  An *unfold* rule's update is empty
and adds no line -- which is why an unfold step in a derivation leaves the
`{…}` prefix exactly as it was. -/
def pushUpd (U : List UpdTerm) : UpdTerm -> List UpdTerm
  | [] => U
  | u => U ++ [u]

/-- Add a goal's guard to the antecedent, under the stack it is read in.  A
trivially true guard adds nothing: that is what keeps an unguarded rule's
successor line as short as the calculus draws it. -/
def addGuard (Γ : List (List UpdTerm × SideFormula)) (U : List UpdTerm) :
    SideFormula -> List (List UpdTerm × SideFormula)
  | .const true => Γ
  | φ => Γ ++ [(U, φ)]

/-- The sequents a rule's goals leave open, one per goal whose mode applies:
`Update/Wp.lean`'s `guard → {update}⟨residual ++ rest⟩post`, as lines.

`match`, not `if`, on the mode test: `dsimp only` reduces a `match` on a
literal by iota, which is what lets the step tactics renormalise a successor
frontier into a literal list. -/
def goalSequents (sm : SolidityModality)
    (Γ : List (List UpdTerm × SideFormula)) (U : List UpdTerm)
    (rest : Block) (post : WrappedExpr) : List RuleGoal -> Frontier
  | [] => []
  | g :: gs =>
      match sm.appliesCaseMode g.mode with
      | false => goalSequents sm Γ U rest post gs
      | true =>
          (match g.residual with
            | .prog upd b =>
                { ante := addGuard Γ U g.guard.formula, upds := pushUpd U upd
                  goal := .prog ⟨sm, b ++ rest⟩ post }
            | .reverting =>
                { ante := addGuard Γ U g.guard.formula, upds := U
                  goal := .prog ⟨sm, Stmt.revert none :: rest⟩ post }
            | .obligation upd φ =>
                { ante := addGuard Γ U g.guard.formula, upds := pushUpd U upd
                  goal := .obl φ }) ::
          goalSequents sm Γ U rest post gs

end Update

/-! ## The step -/

/-- One step of a derivation by a **named** rule: rewrite the first open line
into the lines its goals name.

The shape is `NamedBlockStep`'s (`Calculus/MultiStep.lean`), for the same reason: the
successor is a free index constrained by an equation, so against a
written-out successor the check is `rfl` *after* the `FirstStepCase` proof has
determined the rule's goals -- the unifier cannot invert
`?before ++ ?goals ++ ?after =?= literal`.  `hsq` is `rfl` as well, because
`firstOpen?` computes the split. -/
inductive NamedFrontierStep (r : RuleName) : Frontier -> Frontier -> Prop where
  | head {src next before after : Frontier}
      {Γ : List (List UpdTerm × SideFormula)} {U : List UpdTerm}
      {sm : SolidityModality} {lhs : Stmt} {rest : Block} {post : WrappedExpr}
      {cond : Prop} {rhs : Block} :
      src.firstOpen? = some (before, ⟨Γ, U, .prog ⟨sm, lhs :: rest⟩ post⟩, after) ->
      (hfirst : FirstStepCase sm lhs Rules.stepCases (Rules.stepCase r) cond rhs) ->
      next = before ++ Update.goalSequents sm Γ U rest post
          ((Rules.stepCase r).effect.goals lhs
            (FirstStepCase.effect_cond_holds hfirst)) ++ after ->
      NamedFrontierStep r src next

/-- One step by some rule of the calculus. -/
def FrontierStep (a b : Frontier) : Prop := ∃ r, NamedFrontierStep r a b

theorem FrontierStep.of {r : RuleName} {a b : Frontier}
    (h : NamedFrontierStep r a b) : FrontierStep a b := ⟨r, h⟩

/-! ## The merge

Two lines are the same derivation line when they differ only in how the
accumulated update is *spelled*: `{u}{x := t}` and `{u ‖ x := {u}t}` are one
update, and the calculus's last line is that rewriting. -/

/-- Same antecedent, same goal, and the same update -- the last as an equality
of state functions, which is where `Par.seq_single` does its work. -/
def Sequent.Equiv (x y : Sequent) : Prop :=
  x.ante = y.ante ∧ x.goal = y.goal ∧ x.upd = y.upd

theorem Sequent.Equiv.refl (x : Sequent) : Sequent.Equiv x x :=
  ⟨rfl, rfl, rfl⟩

/-- A merged line validates exactly what the unmerged one does: the merge is
a rewriting of the *spelling*, and `check` only reads the meaning. -/
theorem Sequent.Equiv.check_eq {x y : Sequent} (h : Sequent.Equiv x y)
    (s0 : State) : x.check s0 = y.check s0 := by
  obtain ⟨ha, hg, hu⟩ := h
  simp only [Sequent.check, ha, hg, hu]

/-- Two frontiers are the same derivation line when they have the same lines,
each up to the spelling of its update. -/
def Frontier.Equiv : Frontier -> Frontier -> Prop
  | [], [] => True
  | x :: xs, y :: ys => Sequent.Equiv x y ∧ Frontier.Equiv xs ys
  | _, _ => False

theorem Frontier.Equiv.refl : ∀ f : Frontier, Frontier.Equiv f f
  | [] => trivial
  | _ :: rest => ⟨Sequent.Equiv.refl _, Frontier.Equiv.refl rest⟩

theorem Frontier.Equiv.check_eq :
    ∀ {a b : Frontier}, Frontier.Equiv a b -> ∀ s0 : State, a.check s0 = b.check s0
  | [], [], _, _ => rfl
  | x :: xs, y :: ys, ⟨hx, hrest⟩, s0 => by
      show (x.check s0 && Frontier.check xs s0)
        = (y.check s0 && Frontier.check ys s0)
      rw [hx.check_eq s0, Frontier.Equiv.check_eq hrest s0]

/-- Zero or more steps, with merge lines allowed anywhere in the chain --
the calculus merges mid-derivation too, not only at the end. -/
inductive FrontierMultiStep : Frontier -> Frontier -> Prop where
  | refl {f : Frontier} : FrontierMultiStep f f
  | step {a b c : Frontier} :
      FrontierStep a b -> FrontierMultiStep b c -> FrontierMultiStep a c
  | equiv {a b c : Frontier} :
      Frontier.Equiv a b -> FrontierMultiStep b c -> FrontierMultiStep a c

namespace FrontierMultiStep

theorem trans {a b c : Frontier} :
    FrontierMultiStep a b -> FrontierMultiStep b c -> FrontierMultiStep a c := by
  intro hab hbc
  induction hab with
  | refl => exact hbc
  | step h _ ih => exact .step h (ih hbc)
  | equiv h _ ih => exact .equiv h (ih hbc)

theorem single {a b : Frontier} (h : FrontierStep a b) : FrontierMultiStep a b :=
  .step h .refl

end FrontierMultiStep

theorem NamedFrontierStep.toMultiStep {r : RuleName} {a b : Frontier}
    (h : NamedFrontierStep r a b) : FrontierMultiStep a b :=
  .step (FrontierStep.of h) .refl

/-! ## Notation

`⇝ᵘ` is `⇝` with an update riding along, beside `Calculus/MultiStep.lean`'s `⇝ᵈ` for a
judgment.  As there, the ASCII twins are input-only `macro_rules`, never a
second `infix`: goals print the glyph the calculus draws. -/

@[inherit_doc] scoped infix:50 " ⇝ᵘ "  => FrontierStep
@[inherit_doc] scoped infix:50 " ⇝ᵘ* " => FrontierMultiStep
@[inherit_doc] scoped infix:50 " ≡ᵘ "  => Frontier.Equiv
@[inherit_doc] scoped notation:50 before:51 " ⇝ᵘ[" rule:0 "] " after:51 =>
  NamedFrontierStep rule before after

syntax:50 term:51 " ~>u "  term:51 : term
syntax:50 term:51 " ~>u* " term:51 : term
syntax:50 term:51 " ~>u[" term:0 "] " term:51 : term

macro_rules
  | `($a ~>u $b)  => `(FrontierStep $a $b)
  | `($a ~>u* $b) => `(FrontierMultiStep $a $b)
  | `($a ~>u[$r] $b) => `(NamedFrontierStep $r $a $b)

instance : Trans FrontierStep FrontierMultiStep FrontierMultiStep :=
  ⟨FrontierMultiStep.step⟩

instance : Trans FrontierMultiStep FrontierMultiStep FrontierMultiStep :=
  ⟨FrontierMultiStep.trans⟩

instance : Trans FrontierStep FrontierStep FrontierMultiStep :=
  ⟨fun hab hbc => .step hab (.single hbc)⟩

instance : Trans FrontierMultiStep FrontierStep FrontierMultiStep :=
  ⟨fun hab hbc => hab.trans (.single hbc)⟩

/-- A single sequent is a one-line frontier: what lets a derivation write
`seq!{ … }` on a line and a bracketed list only where a rule actually
branched. -/
instance : CoeTail Sequent Frontier := ⟨fun q => [q]⟩

/-! ## What a proof by the rule table alone is -/

/-- The rule table drives `⟨sm, b⟩post` to a frontier with no statement left,
and that frontier holds at `s0`.

This is KeY's own proof shape, and the reason it is worth stating separately
from `SolidityJudgment.Holds`: the symbolic-execution half is the taclets and
nothing else — no interpreter, no weakest precondition.  What is left at the
end is first-order: the accumulated update applied to `s0`, and one obligation
line per `assert` (`Rules.assertGoals` leaves the violated branch as an
obligation, not a revert).

`isClosed` is what makes it a claim about the rules.  `⇝ᵘ*` is reflexive, so
without that conjunct the start frontier is its own witness and the statement
collapses back to `Frontier.Holds` — the interpreter again, which is exactly
what this is meant to avoid.

**What it is not.**  It does not yet *imply* `SolidityJudgment.Holds`.  That
needs `FrontierStep a b → (a.Holds s ↔ b.Holds s)`, which needs the per-rule
bridges of `Update/TacletTable.lean` (21 of the 95 rules with an update), and
`Rules.assertGoals` is deliberately not exhaustive (`Update/Wp.lean`).  The
two are proved of the same programs side by side instead:
`Corpus/Calculus/` and `Corpus/Wp/`, from one pass of the
porter so they cannot drift. -/
def CalculusHolds (sm : SolidityModality) (b : Block) (post : WrappedExpr)
    (s0 : State) : Prop :=
  ∃ f : Frontier,
    FrontierMultiStep [{ goal := SeqGoal.prog ⟨sm, b⟩ post }] f ∧
      Frontier.isClosed f = true ∧ f.Holds s0

end Solidity
