import Solidity.Source.Horizon
import Solidity.Correctness.Lowering.Checker.SourceAssociation

/-!
# Identity conversions in a `while` condition cost one horizon

Source resolution keeps an identity conversion on an assignment's right-hand
side (`Checker.SourceAssociation.resolved_eq`); the G19 Source statements do
not. A `while` whose condition gains such a conversion runs, at one more
horizon, exactly as the bare loop whenever the bare loop completes. Proved for
every body by induction on the horizon, from the interpreter's horizon
monotonicity (`Source.belowAtKnown`); no loop termination is assumed.
-/
namespace Solidity.Correctness.Lowering.Loops.Horizon

open Solidity.Source

/-- A condition `d` is `c` one horizon later. -/
theorem while_below {E : Env} (G : Glob E) (F : Fr) (nps : Nat) (ph : Option (Ph E))
    {R : List STy} {M lp u : Bool} {Γ Γ₁ : RCtx} (c d : RExpr E Γ .bool)
    (s : RStmt E R M ⟨true, u⟩ Γ Γ₁)
    (hcd : ∀ n, Below (evalE G F n c) (evalE G F (n + 1) d)) :
    ∀ (n : Nat) (l : Locals E.layout Γ),
      Below (execS G F n nps ph (.whileLoop (l := lp) c s) l)
        (execS G F (n + 1) nps ph (.whileLoop (l := lp) d s) l)
  | 0, _ => Below.timeout _
  | n + 1, l => by
    have hs : ∀ l', Below (execS G F n nps ph s l') (execS G F (n + 1) nps ph s l') :=
      fun l' => (belowAtKnown G n).execS true F nps ph s l'
    have hw := while_below (lp := lp) G F nps ph c d s hcd n
    rw [execS, execS]
    exact Below.bind (Below.sub l (hcd n)) fun ⟨cv, l1⟩ => by
      dsimp only
      refine Below.bind (Below.refl _) fun v => ?_
      split
      · refine Below.bind (hs l1) fun o => ?_
        cases o with
        | normal l2 => exact Below.bind (Below.refl _) fun l3 => hw l3
        | cont l2 => exact hw l2
        | brk l2 => exact Below.refl _
        | ret l2 => exact Below.refl _
      · exact Below.refl _

/-- The converted-assignment condition is the bare one a horizon later. -/
theorem assign_below {E : Env} (G : Glob E) (F : Fr) {Γ : RCtx} (i a : Source.Idx Γ .bool) :
    ∀ n, Below (evalE G F n (.assign (.local i) (.local a)))
      (evalE G F (n + 1) (.assign (.local i) (.conv (.local a) (.inl rfl)))) := by
  intro n
  match n with
  | 0 => exact Below.timeout _
  | 1 => exact Below.timeout _
  | k + 2 =>
    rw [Checker.SourceAssociation.local_assignment_identity G F k i a (.inl rfl)]
    exact Below.refl _

end Solidity.Correctness.Lowering.Loops.Horizon
