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

/-- A loop whose condition `d` and body `s'` are `c` and `s` one horizon later
is the bare loop one horizon later. -/
theorem while_below {E : Env} (G : Glob E) (F : Fr) (nps : Nat) (ph : Option (Ph E))
    {R : List STy} {M lp u : Bool} {Γ Γ₁ : RCtx} (c d : RExpr E Γ .bool)
    (s s' : RStmt E R M ⟨true, u⟩ Γ Γ₁)
    (hcd : ∀ n, Below (evalE G F n c) (evalE G F (n + 1) d))
    (hs : ∀ n l, Below (execS G F n nps ph s l) (execS G F (n + 1) nps ph s' l)) :
    ∀ (n : Nat) (l : Locals E.layout Γ),
      Below (execS G F n nps ph (.whileLoop (l := lp) c s) l)
        (execS G F (n + 1) nps ph (.whileLoop (l := lp) d s') l)
  | 0, _ => Below.timeout _
  | n + 1, l => by
    have hw := while_below (lp := lp) G F nps ph c d s s' hcd hs n
    rw [execS, execS]
    exact Below.bind (Below.sub l (hcd n)) fun ⟨cv, l1⟩ => by
      dsimp only
      refine Below.bind (Below.refl _) fun v => ?_
      split
      · refine Below.bind (hs n l1) fun o => ?_
        cases o with
        | normal l2 => exact Below.bind (Below.refl _) fun l3 => hw l3
        | cont l2 => exact hw l2
        | brk l2 => exact Below.refl _
        | ret l2 => exact Below.refl _
      · exact Below.refl _

/-- A `do … while` whose body is the bare body a horizon later is the bare
loop a horizon later; the condition is the same on both sides. -/
theorem doWhile_below {E : Env} (G : Glob E) (F : Fr) (nps : Nat) (ph : Option (Ph E))
    {R : List STy} {M lp u : Bool} {Γ Γ₁ : RCtx} (c : RExpr E Γ .bool)
    (s s' : RStmt E R M ⟨true, u⟩ Γ Γ₁)
    (hs : ∀ n l, Below (execS G F n nps ph s l) (execS G F (n + 1) nps ph s' l)) :
    ∀ (n : Nat) (l : Locals E.layout Γ),
      Below (execS G F n nps ph (.doWhile (l := lp) s c) l)
        (execS G F (n + 1) nps ph (.doWhile (l := lp) s' c) l)
  | 0, _ => Below.timeout _
  | n + 1, l => by
    have hw := doWhile_below (lp := lp) G F nps ph c s s' hs n
    have hb := hs n l
    have hc : Below (evalE G F n c) (evalE G F (n + 1) c) :=
      (belowAtKnown G n).evalE true F c
    rw [execS, execS]
    below_go [hb, hw, hc, Below.sub]

/-- Same body on both sides. -/
theorem same_below {E : Env} (G : Glob E) (F : Fr) (nps : Nat) (ph : Option (Ph E))
    {R : List STy} {M : Bool} {k : SCtx} {Γ Γ₁ : RCtx} (s : RStmt E R M k Γ Γ₁) :
    ∀ n l, Below (execS G F n nps ph s l) (execS G F (n + 1) nps ph s l) :=
  fun n l => (belowAtKnown G n).execS true F nps ph s l

/-- An expression statement whose expression is the bare one a horizon later. -/
theorem expr_below {E : Env} (G : Glob E) (F : Fr) (nps : Nat) (ph : Option (Ph E))
    {R : List STy} {M : Bool} {k : SCtx} {Γ : RCtx} {τ : STy} (e e' : RExpr E Γ τ)
    (he : ∀ n, Below (evalE G F n e) (evalE G F (n + 1) e')) :
    ∀ n l, Below (execS G F n nps ph (R := R) (M := M) (k := k) (.expr e) l)
      (execS G F (n + 1) nps ph (R := R) (M := M) (k := k) (.expr e') l)
  | 0, _ => Below.timeout _
  | n + 1, l => by
    rw [execS, execS]
    exact Below.bind (Below.sub l (he n)) fun _ => Below.refl _

/-- A statement list whose head is the bare head a horizon later. -/
theorem items_below {E : Env} (G : Glob E) (F : Fr) (nps : Nat) (ph : Option (Ph E))
    {R : List STy} {M : Bool} {k : SCtx} {Γ Γ₁ Γ₂ : RCtx} (s s' : RStmt E R M k Γ Γ₁)
    (rest : RItems E R M k Γ₁ Γ₂)
    (hs : ∀ n l, Below (execS G F n nps ph s l) (execS G F (n + 1) nps ph s' l)) :
    ∀ n l, Below (execItems G F n nps ph (.stmt s rest) l)
      (execItems G F (n + 1) nps ph (.stmt s' rest) l)
  | 0, _ => Below.timeout _
  | n + 1, l => by
    rw [execItems, execItems]
    refine Below.bind (hs n l) fun o => ?_
    cases o with
    | normal l1 =>
      exact Below.bind ((belowAtKnown G n).execItems true F nps ph rest l1) fun _ => Below.refl _
    | brk l1 => exact Below.refl _
    | cont l1 => exact Below.refl _
    | ret l1 => exact Below.refl _

/-- A block whose items are the bare items a horizon later. -/
theorem block_below {E : Env} (G : Glob E) (F : Fr) (nps : Nat) (ph : Option (Ph E))
    {R : List STy} {M : Bool} {k : SCtx} {Γ Γ₁ : RCtx} (b b' : RItems E R M k Γ Γ₁)
    (hb : ∀ n l, Below (execItems G F n nps ph b l) (execItems G F (n + 1) nps ph b' l)) :
    ∀ n l, Below (execS G F n nps ph (.block b) l) (execS G F (n + 1) nps ph (.block b') l)
  | 0, _ => Below.timeout _
  | n + 1, l => by
    rw [execS, execS]
    exact Below.bind (hb n l) fun _ => Below.refl _

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

/-- A converted-literal assignment is the bare one a horizon later. -/
theorem assign_lit_below {E : Env} (G : Glob E) (F : Fr) {Γ : RCtx} (a : Source.Idx Γ .bool)
    (b : Bool) (h : Conv E.isBase E.mapFree .bool .bool) :
    ∀ n, Below (evalE G F n (.assign (.local a) (.bool b)))
      (evalE G F (n + 1) (.assign (.local a) (.conv (.bool b) h))) := by
  intro n
  match n with
  | 0 => exact Below.timeout _
  | 1 => exact Below.timeout _
  | k + 2 =>
    have eq : evalE G F (k + 3) (.assign (.local a) (.conv (.bool b) h)) =
        evalE G F (k + 2) (.assign (.local a) (.bool b)) := by
      conv => lhs; rw [evalE]
      rw [Checker.SourceAssociation.identity_eval]
      rfl
    rw [eq]
    exact Below.refl _

end Solidity.Correctness.Lowering.Loops.Horizon
