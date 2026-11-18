import Solidity.Goals.ElabTotal

/-!
# Successful runs of the elaborator monad, and capture predicates (ls2-expressions)

`ElabRan` through `pure` and `>>=`, and the shape of a relation on captures
that the arms preserve.

* `ran_pure`, `ran_bind`: a successful run of `pure a` returns `a` and keeps
  the state; one of `x >>= f` is a run of `x` then a run of `f` from its
  state.
* `Pieces S`: a predicate `S sc st P st'` on captures (scope, state before,
  emitted statements, state after) that holds of no captures and of a
  concatenation of two runs. The case facts of the arms
  (`Sim/Expr/Operand.lean`, `Sim/Expr/Capture.lean`) are stated for any such
  `S`, with the obligations of the callbacks an arm calls as hypotheses.

`Pieces` is the local stand-in for the statement-level relation of the v2 case
interface (`ls1c2-cases-v2`, `Sim/Match/CasesV2.lean`, not landed): the arms'
facts are instantiated at it once it lands. The whole-body site obligations
(`SiteSim`, `SiteSim₂`) are not `Pieces`: they are not closed under
concatenation.
-/
namespace Solidity.Correctness.Lowering.Sim

open Solidity.Goals (ElabRan)

theorem ran_pure {β : Type} {a b : β} {sc : ElabScope} {st st' : ECtx × Nat}
    (ran : ElabRan (pure a) sc st b st') : b = a ∧ st' = st := by
  obtain ⟨m, m', run⟩ := ran
  cases run
  exact ⟨rfl, rfl⟩

theorem ran_bind {α β : Type} {x : ElabM α} {f : α → ElabM β} {sc : ElabScope}
    {st st' : ECtx × Nat} {b : β} (ran : ElabRan (x >>= f) sc st b st') :
    ∃ a st₁, ElabRan x sc st a st₁ ∧ ElabRan (f a) sc st₁ b st' := by
  obtain ⟨m, m', run⟩ := ran
  cases hx : ((x.run sc).run st).run m with
  | error e =>
    have : (((x >>= f).run sc).run st).run m = .error e := by
      show (do let r ← ((x.run sc).run st).run m; _) = _
      rw [hx]; rfl
    rw [this] at run; cases run
  | ok r =>
    obtain ⟨⟨a, st₁⟩, m₁⟩ := r
    have : (((x >>= f).run sc).run st).run m = (((f a).run sc).run st₁).run m₁ := by
      show (do let r ← ((x.run sc).run st).run m; _) = _
      rw [hx]; rfl
    rw [this] at run
    exact ⟨a, st₁, ⟨m, m₁, hx⟩, ⟨m₁, m', run⟩⟩

/-- A predicate on captures closed under the empty captures and under the
concatenation of two consecutive runs in one scope. -/
structure Pieces {C : Contract}
    (S : ElabScope → ECtx × Nat → SProg C → ECtx × Nat → Prop) : Prop where
  nil : ∀ sc st, S sc st [] st
  append : ∀ {sc st st₁ st₂ P Q}, S sc st P st₁ → S sc st₁ Q st₂ → S sc st (P ++ Q) st₂

/-- Every successful run of `f` emits captures in `S`. -/
def Emits {C : Contract} {α β : Type}
    (S : ElabScope → ECtx × Nat → SProg C → ECtx × Nat → Prop)
    (f : α → ElabM (SProg C × β)) : Prop :=
  ∀ a sc st out st', ElabRan (f a) sc st out st' → S sc st out.1 st'

end Solidity.Correctness.Lowering.Sim
