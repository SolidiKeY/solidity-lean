import Solidity.Calculus.Derive

/-!
# A leaf of `sol_prove`'s walk, closed on the scoped form

`sol_prove`'s walk (`Calculus/ProvesDerive.lean`) leaves a leaf `H ⊢ φ`
where no program rule fits.  Here it is closed on its scoped form
(`Seq.leafCheckS`): the sequent put back together (`Hyps.wrap`), no
modality left (`Fml.modalFree`), its updates pushed in by position
(`Fml.toLS`, `Calculus/DecideScoped.lean`) within `closeSize` nodes, the
reads of writes eliminated (`LFml.elim`) within `elimSize`, and the
reduction closed by `LFml.close` (`Calculus/Closer.lean`).  Soundness is
`Valid.of_reduceS` and `LFml.close_valid`, then `Proves.closeHolds`.  A
leaf outside the fragment is not read (`none`); the walk leaves it, a goal
of the scoped calculus.

The parameters stay quantified: the reduction binds each to its position
(`LFml.all`), and a hidden binder of a value reads as the quantifier it is
(`LFml.allB`).  A premise `wt(storage)` is one more premise: the typed
storage is in the shape its contract declares, so the closer needs no
layout.

A split's branch whose condition is ground under the context
(`Hyps.groundS`) is asked of the closer first: `if (v < 0)` after
`int v = -3;` takes one branch only.  KeY applies the update to the
condition in each branch's antecedent, simplifies it, and closes the branch
it became `false` in (`closeFalse`); here a refuted branch is closed by
`Proves.closeFalse` (`Seq.refutes`), not walked.  The test reads only
positions and literals and decides only when to ask; the closer proves what
is closed.

The functions the kernel evaluates are written with their recursors, each
with a `match` twin for compiled code and a link theorem (Gate G0).
`Seq.leafFitsOn` is compiled only: the bounds `sol_prove?` asks before it
tries a step that reduces a leaf.
-/

namespace Solidity

open Solidity (Modality RuleSet)
open Decide

variable {C : Contract}

/-! ## The ground test of a split, by position -/

section Ground

/-- `Idx.toNat`, by the recursor. -/
@[implemented_by Idx.toNat]
def _root_.Solidity.Idx.toNatR {Γ : Ctx} {t : LTy} (i : Idx Γ t) : Nat :=
  Idx.rec (motive := fun _ _ _ => Nat) 0 (fun _ ih => ih + 1) i

theorem _root_.Solidity.Idx.toNatR_eq {Γ : Ctx} {t : LTy} (i : Idx Γ t) : i.toNatR = i.toNat := by
  induction i with
  | here => rfl
  | there i ih => exact congrArg (· + 1) ih

/-- `Idx.wk` on positions: where a local of `Γ` sits in `Δ`. -/
def _root_.Solidity.Thin.posWkM : {Γ Δ : Ctx} → Thin Γ Δ → Nat → Nat
  | _, _, .refl, n => n
  | _, _, .keep _, 0 => 0
  | _, _, .keep h, n + 1 => h.posWkM n + 1
  | _, _, .drop h, n => h.posWkM n + 1

/-- A position of `Γ` read in `Δ` (`Idx.wk`), by the recursor. -/
@[implemented_by Thin.posWkM]
def _root_.Solidity.Thin.posWk {Γ Δ : Ctx} (h : Thin Γ Δ) (n : Nat) : Nat :=
  Thin.rec (motive := fun _ _ _ => Nat → Nat) (fun n => n)
    (fun _ ih n => Nat.casesOn (motive := fun _ => Nat) n 0 (fun n => ih n + 1))
    (fun _ ih n => ih n + 1) h n

theorem _root_.Solidity.Thin.posWk_eq_posWkM {Γ Δ : Ctx} (h : Thin Γ Δ) (n : Nat) :
    h.posWk n = h.posWkM n := by
  induction h generalizing n with
  | refl => rfl
  | keep h ih => cases n <;> simp only [Thin.posWkM, ← ih] <;> rfl
  | drop h ih => simp only [Thin.posWkM, ← ih]; rfl

/-- The positions a value right-hand side reads, when it is built from
literals and value operators alone. -/
def _root_.Solidity.Rhs.litPos {Γ : Ctx} {t : LTy} : Rhs C Γ t → Option (List Nat)
  | .val a => a.litVarsS.map (·.map (·.2.toNatR))
  | _ => none

/-- `Upd.resolveS`'s compiled twin. -/
def _root_.Solidity.Upd.resolveSM {Γ : Ctx} : {Δ : Ctx} → Upd C Γ Δ → Nat → Option (List Nat)
  | _, .nil, n => some [n]
  | _, .snoc U e, n =>
    match e with
    | .local i r => if i.toNatR == n then r.litPos else U.resolveSM n
    | _ => U.resolveSM n
  | _, .decl _ _ r, 0 => r.litPos
  | _, .decl U _ _, n + 1 => U.resolveSM n
  | _, .pop U h, n => U.resolveSM (n + h.depth)
  | _, .drop U h, n => U.resolveSM (h.posWk n)

/-- **What the position `n` after the update reads before it**: the
positions its right-hand side reads, when the update binds it to a term of
literals (the last element that binds it, as the parallel update writes
it); itself, moved past the update's scopes, when the update does not bind
it; `none` when it binds it to anything else.  By the recursor. -/
@[implemented_by Upd.resolveSM]
def _root_.Solidity.Upd.resolveS {Γ Δ : Ctx} (U : Upd C Γ Δ) (n : Nat) : Option (List Nat) :=
  Upd.rec (motive := fun _ _ => Nat → Option (List Nat)) (fun n => some [n])
    (fun _ e ih n =>
      match e with
      | .local i r => if i.toNatR == n then r.litPos else ih n
      | _ => ih n)
    (fun _ _ r ih n => Nat.casesOn (motive := fun _ => Option (List Nat)) n r.litPos ih)
    (fun _ h ih n => ih (n + h.depth)) (fun _ h ih n => ih (h.posWk n)) U n

theorem _root_.Solidity.Upd.resolveS_eq_resolveSM {Γ Δ : Ctx} (U : Upd C Γ Δ) (n : Nat) :
    U.resolveS n = U.resolveSM n := by
  induction U generalizing n with
  | nil => rfl
  | snoc U e ih => cases e <;> simp only [Upd.resolveSM, ← ih] <;> rfl
  | decl U x r ih => cases n <;> simp only [Upd.resolveSM, ← ih] <;> rfl
  | pop U h ih | drop U h ih => simp only [Upd.resolveSM, ← ih]; rfl

/-- The positions `xs` after the update, each replaced by what it reads
before it (`Upd.resolveS`), none listed twice; `none` when one is bound to
something other than a term of literals. -/
def _root_.Solidity.Upd.groundStepS {Γ Δ : Ctx} (U : Upd C Γ Δ) : List Nat → Option (List Nat)
  | [] => some []
  | x :: xs =>
    match U.resolveS x, U.groundStepS xs with
    | some u, some v => some (u.foldr List.insert v)
    | _, _ => none

/-- `Hyps.groundInS`'s compiled twin. -/
def _root_.Solidity.Hyps.groundInSM {Γ₀ : Ctx} : {Γ : Ctx} → Hyps C Γ₀ Γ → List Nat → Bool
  | _, _, [] => true
  | _, .nil, _ :: _ => false
  | _, .pre H _, xs@(_ :: _) | _, .havoc H, xs@(_ :: _) => H.groundInSM xs
  | _, .upd H _ U, xs@(_ :: _) =>
    match U.groundStepS xs with
    | some ys => H.groundInSM ys
    | none => false
  | _, .all H _ _, xs@(_ :: _) | _, .bind H _ _ _, xs@(_ :: _) =>
    !xs.contains 0 && H.groundInSM (xs.map (· - 1))
  | _, .anon H ys, xs@(_ :: _) =>
    !ys.any (fun y => xs.contains y.2.toNatR) && H.groundInSM xs

/-- **Whether every position of `xs` is bound by the context**, its
entries innermost first, to a term of literals, transitively.  A
quantified local, a hidden binder's not yet assigned and one a loop
anonymised are not.  By the recursor. -/
@[implemented_by Hyps.groundInSM]
def _root_.Solidity.Hyps.groundInS {Γ₀ Γ : Ctx} (H : Hyps C Γ₀ Γ) (xs : List Nat) : Bool :=
  Hyps.rec (motive := fun _ _ => List Nat → Bool)
    (fun xs => xs.isEmpty)
    (fun _ _ ih xs => xs.isEmpty || ih xs)
    (fun _ _ U ih xs => xs.isEmpty || match U.groundStepS xs with
      | some ys => ih ys
      | none => false)
    (fun _ ih xs => xs.isEmpty || ih xs)
    (fun _ _ _ ih xs => xs.isEmpty || (!xs.contains 0 && ih (xs.map (· - 1))))
    (fun _ _ _ _ ih xs => xs.isEmpty || (!xs.contains 0 && ih (xs.map (· - 1))))
    (fun _ ys ih xs => xs.isEmpty || (!ys.any (fun y => xs.contains y.2.toNatR) && ih xs)) H xs

theorem _root_.Solidity.Hyps.groundInS_eq_groundInSM {Γ₀ Γ : Ctx} (H : Hyps C Γ₀ Γ)
    (xs : List Nat) : H.groundInS xs = H.groundInSM xs := by
  induction H generalizing xs with
  | nil => cases xs <;> rfl
  | pre H a ih | havoc H ih =>
    cases xs with
    | nil => rfl
    | cons x xs => simp only [Hyps.groundInSM, ← ih]; rfl
  | upd H m U ih =>
    cases xs with
    | nil => rfl
    | cons x xs => simp only [Hyps.groundInSM, ← ih]; rfl
  | all H x p ih | bind H m x t ih =>
    cases xs with
    | nil => rfl
    | cons x xs => simp only [Hyps.groundInSM, ← ih]; rfl
  | anon H ys ih =>
    cases xs with
    | nil => rfl
    | cons x xs => simp only [Hyps.groundInSM, ← ih]; rfl

/-- `Fml.litPos`' compiled twin. -/
def _root_.Solidity.Fml.litPosM : {Γ : Ctx} → Fml C Γ → Option (List Nat)
  | _, .tt => some []
  | _, .eq a b =>
    match a.litVarsS, b.litVarsS with
    | some u, some v => some ((u ++ v).map (·.2.toNatR))
    | _, _ => none
  | _, .defined t => t.litVarsS.map (·.map (·.2.toNatR))
  | _, .not φ => φ.litPosM
  | _, .and φ ψ | _, .imp φ ψ =>
    match φ.litPosM, ψ.litPosM with
    | some u, some v => some (u ++ v)
    | _, _ => none
  | _, _ => none

/-- **The positions a first-order formula reads when its terms are built
from literals and value operators alone**; `none` otherwise.  By the recursor. -/
@[implemented_by Fml.litPosM]
def _root_.Solidity.Fml.litPos {Γ : Ctx} (φ : Fml C Γ) : Option (List Nat) :=
  Fml.rec (motive := fun _ _ => Option (List Nat))
    (some [])
    (fun a b => match a.litVarsS, b.litVarsS with
      | some u, some v => some ((u ++ v).map (·.2.toNatR))
      | _, _ => none)
    (fun t => t.litVarsS.map (·.map (·.2.toNatR)))
    (fun _ ih => ih)
    (fun _ _ ihφ ihψ => match ihφ, ihψ with
      | some u, some v => some (u ++ v)
      | _, _ => none)
    (fun _ _ ihφ ihψ => match ihφ, ihψ with
      | some u, some v => some (u ++ v)
      | _, _ => none)
    (fun _ _ _ _ => none) (fun _ _ _ _ _ => none) (fun _ _ => none) (fun _ _ _ _ => none)
    (fun _ _ _ _ _ => none) (fun _ _ _ => none) φ

theorem _root_.Solidity.Fml.litPos_eq_litPosM {Γ : Ctx} (φ : Fml C Γ) :
    φ.litPos = φ.litPosM := by
  induction φ with
  | not φ ih => simp only [Fml.litPosM, ← ih]; rfl
  | and φ ψ ihφ ihψ | imp φ ψ ihφ ihψ => simp only [Fml.litPosM, ← ihφ, ← ihψ]; rfl
  | _ => rfl

/-- **Whether a split's condition `c` is ground in the context `H`**: it
reads only locals the context binds, through its updates, to terms of
literals and value operators. -/
def _root_.Solidity.Hyps.groundS {Γ : Ctx} (H : Hyps C [] Γ) (c : Fml C Γ) : Bool :=
  match c.litPos with
  | some xs => H.groundInS xs
  | none => false

end Ground

/-! ## The leaf closer -/

namespace Seq

/-- The most nodes the closer takes in a leaf's formula with its updates
pushed in, counted as a tree (`LFml.fits`).  A storage written from a read
of the one before it appears twice in the next, so this tree doubles with
each such write.  It is the cheap first test: computing the reduction of a
leaf far past it would itself be slow. -/
def closeSize : Nat := 2000

/-- The most nodes the closer takes in the reduction (`LFml.elim`), which
is what it walks, counted as a tree. -/
def elimSize : Nat := 40000

/-- **The scoped closer on a leaf `ψ` of no modality**: `none` where the
reduction does not read it; else whether it closes it: within `closeSize`
nodes with its updates pushed in (the cheap bound, tested before the
elimination), within `elimSize` after it, and closed by `LFml.close`. -/
def checkCore (ψ : Fml C []) : Option Bool :=
  (ψ.toLS true SymS.init).map fun l =>
    (l.fits closeSize).isSome && (l.elim.fits elimSize).isSome && l.elim.close

/-- What `checkCore` closes is valid: `Valid.of_reduceS` and
`LFml.close_valid`. -/
theorem checkCore_valid {ψ : Fml C []} (h : checkCore ψ = some true) : Valid ψ := by
  simp only [checkCore, Option.map_eq_some_iff, Bool.and_eq_true] at h
  obtain ⟨l, hl, -, hc⟩ := h
  exact Valid.of_reduceS (by rw [Fml.reduceS, hl]; rfl) (LFml.close_valid hc)

/-- **The scoped closer on a wrapped leaf `ψ`**: none where a modality is
left; else `checkCore` on the leaf. -/
def leafCheckOn (ψ : Fml C []) : Option Bool :=
  bif ψ.modalFree then checkCore ψ else none

/-- **The closer's bounds on a wrapped leaf**, by position, which
`sol_prove?` asks before it tries a step that reduces the leaf (the
reduction, its quoting and its kernel check heed no heartbeats): the
reduction reads it within `closeSize` with its updates pushed in, and
within `elimSize` after the elimination, which is built only within the
first bound. -/
def leafFitsOn (ψ : Fml C []) : Bool :=
  ψ.modalFree &&
    match ψ.toLS true SymS.init with
    | some l => (l.fits closeSize).isSome && (l.elim.fits elimSize).isSome
    | none => false

/-- `leafCheckOn` on the leaf `H ⊢ φ`. -/
def leafCheckS {Γ : Ctx} (H : Hyps C [] Γ) (φ : Fml C Γ) : Option Bool := leafCheckOn (H.wrap φ)

/-- **A leaf the scoped closer closes is proved**: `Proves.closeHolds`. -/
theorem leafCheckS_sound {R : RuleSet} {Γ : Ctx} {H : Hyps C [] Γ} {φ : Fml C Γ}
    (h : leafCheckS H φ = some true) : Proves C R [] H φ := by
  simp only [leafCheckS, leafCheckOn] at h
  cases hm : (H.wrap φ).modalFree
  · simp only [hm, cond_false, reduceCtorEq] at h
  simp only [hm, cond_true] at h
  exact Proves.closeHolds (checkCore_valid h) hm

end Seq

end Solidity
