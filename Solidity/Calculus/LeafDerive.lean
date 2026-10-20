import Solidity.Calculus.Derive

/-!
# A leaf of `sol_prove`'s walk, closed on the scoped form

`sol_prove`'s walk (`Calculus/ProvesDerive.lean`) leaves a leaf `H ⊢ φ`
where no program rule fits.  Here it is closed on its scoped form
(`Seq.leafCheckS`): the sequent put back together (`Hyps.wrap`), no
modality left (`Fml.modalFree`), its updates pushed in by position
(`Fml.toLS`, `Calculus/DecideScoped.lean`) within `closeSize` nodes and
`stackSize` storage updates on the same pushed-in leaf, or the concrete
tier (`LFml.boundsOk`; `Seq.checkCore`,
`Calculus/DecideComplete.lean`), the reads of writes
eliminated under the premises (`LFml.elimF`, `Calculus/ElimFacts.lean`),
memory read as solkey reads it and the reduction closed by the closer
(`LFml.decideMem`, `Calculus/MemRead.lean`, `Calculus/Closer.lean`).
Soundness is `Valid.of_toLS` and `LFml.decideMem_valid`, then
`Proves.closeHolds`.  A
leaf outside the fragment is not read (`none`); the walk leaves it, a goal
of the scoped calculus.

The parameters stay quantified: the reduction binds each to its position
(`LFml.all`), and a hidden binder of a value reads as the quantifier it is
(`LFml.allB`).  A premise `wt(storage)` is one more premise: the typed
storage is in the shape its contract declares, so the closer needs no
layout.

A split's branch is asked of the bounded scoped closer first: `if (v < 0)` after
`int v = -3;` takes one branch only.  KeY applies the update to the
condition in each branch's antecedent, simplifies it, and closes the branch
it became `false` in (`closeFalse`); here a refuted branch is closed by
`Proves.closeFalse` (`Seq.refuteS`, on the premises the condition reaches), not walked. Symbolic hypotheses, including
required storage lengths, may also refute a branch. The closer proves every
branch it closes.

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
  | _, .wellFormed t => t.litVarsS.map (·.map (·.2.toNatR))
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

/-- **The scoped closer on a wrapped leaf `ψ`**: none where a modality is
left; else `checkCore` on the leaf. -/
def leafCheckOn (ψ : Fml C []) : Option Bool :=
  bif ψ.modalFree then checkCore ψ else none

/-- **The closer's bounds on a wrapped leaf**, by position, which
`sol_prove?` asks before it tries a step that reduces the leaf (the
reduction, its quoting and its kernel check heed no heartbeats): the
leaf with its updates pushed in is within `closeSize` nodes and within
`stackSize` storage updates, or the concrete tier (`Seq.fitsCore`,
`LFml.boundsOk`, `Calculus/DecideComplete.lean`), before the elimination.
Pushing in reads storage early only on a concrete history
(`LTm.literalRead`, `LTm.foldable`), within the same tiers. -/
def leafFitsOn (ψ : Fml C []) : Bool :=
  ψ.modalFree && (fitsCore ψ).getD false

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

/-! ## A split refuted on the premises its condition reads

A split's branch is refuted on its wrapped sequent, the condition the last
premise (`Seq.refuteS`).  The premises its condition does not reach, through
the positions they share or through the state, are dropped first
(`LFml.slice`): a loop's guard over locals is then refuted on the locals'
facts alone, not through every storage write the loop made, whose guards
would grow the closer's work with each iteration and soon pass its bounds
(`LFml.boundsOk`).  A refutation that stacks few storage updates
(`sliceDepth`), and one whose slice still reads the state, is read whole, as
the leaf closer reads it.  Dropping a premise only strengthens a formula
(`LFml.dropPrem_holds`), so which premises are kept is a matter of
completeness, not of soundness. -/

namespace Decide

/-- What a term or a formula reads: the positions, and whether it reads
the state (storage, memory, the transaction's values). -/
abbrev Reads := List Nat × Bool

/-- Whether a constant reads the state. -/
def _root_.Solidity.Op0.readsState {s : Srt} (o : Op0 C s) : Bool :=
  @Op0.casesOn C (fun _ _ => Bool) s o (fun _ => false) (fun _ => true) (fun _ _ _ => false)
    true true true (fun _ _ _ _ => false) (fun _ => false)

/-- `LTm.reads`' compiled twin. -/
def LTm.readsM : {s : Srt} → LTm C s → Reads → Reads
  | _, .var j, r => (r.1.insert j, r.2)
  | _, .app0 o, r => (r.1, r.2 || o.readsState)
  | _, .err, r => r
  | _, .app1 _ x, r => x.readsM r
  | _, .app2 _ x y, r => y.readsM (x.readsM r)
  | _, .app3 _ x y z, r => z.readsM (y.readsM (x.readsM r))
  | _, .index _ q i, r => i.readsM (q.readsM r)
  | _, .obsW q, r | _, .obsL q, r | _, .obsH q, r => q.readsM (r.1, true)
  | _, .seq d a, r => a.readsM (d.readsM r)
  | _, .orElse a b, r => b.readsM (a.readsM r)
  | _, .kite a b t e, r => e.readsM (t.readsM (b.readsM (a.readsM r)))

/-- **What a term reads**, added to `r`.  By the recursor. -/
@[implemented_by LTm.readsM]
def LTm.reads {s : Srt} (t : LTm C s) : Reads → Reads :=
  @LTm.rec C (fun _ _ => Reads → Reads)
    (@fun _ j r => (r.1.insert j, r.2)) (@fun _ o r => (r.1, r.2 || o.readsState))
    (@fun _ _ _ _ ihx r => ihx r)
    (@fun _ _ _ _ _ _ ihx ihy r => ihy (ihx r))
    (@fun _ _ _ _ _ _ _ _ ihx ihy ihz r => ihz (ihy (ihx r)))
    (@fun _ _ _ _ _ _ ihq ihi r => ihi (ihq r))
    (@fun _ _ ih r => ih (r.1, true)) (@fun _ _ ih r => ih (r.1, true))
    (@fun _ _ ih r => ih (r.1, true))
    (@fun _ _ _ _ ihd iha r => iha (ihd r))
    (@fun _ _ _ iha ihb r => ihb (iha r))
    (@fun _ _ _ _ _ _ iha ihb iht ihe r => ihe (iht (ihb (iha r))))
    (@fun _ r => r) s t

theorem LTm.reads_eq_readsM {s : Srt} (t : LTm C s) (r : Reads) : t.reads r = t.readsM r := by
  induction t generalizing r with
  | var | app0 | err => rfl
  | app1 o x ih => simp only [LTm.readsM, ← ih]; rfl
  | app2 o x y ihx ihy => simp only [LTm.readsM, ← ihx, ← ihy]; rfl
  | app3 o x y z ihx ihy ihz => simp only [LTm.readsM, ← ihx, ← ihy, ← ihz]; rfl
  | index it q i ihq ihi => simp only [LTm.readsM, ← ihq, ← ihi]; rfl
  | obsW q ih | obsL q ih | obsH q ih => simp only [LTm.readsM, ← ih]; rfl
  | seq d a ihd iha => simp only [LTm.readsM, ← ihd, ← iha]; rfl
  | orElse a b iha ihb => simp only [LTm.readsM, ← iha, ← ihb]; rfl
  | kite a b t e iha ihb iht ihe => simp only [LTm.readsM, ← iha, ← ihb, ← iht, ← ihe]; rfl

/-- `LFml.reads`' compiled twin. -/
def LFml.readsM : LFml C → Reads → Reads
  | .tt, r => r
  | .eq a b, r => b.reads (a.reads r)
  | .not φ, r => φ.readsM r
  | .and φ ψ, r | .imp φ ψ, r => ψ.readsM (φ.readsM r)
  | .all _ _ φ, r => φ.readsM r

/-- **What a formula reads**, added to `r`.  By the recursor. -/
@[implemented_by LFml.readsM]
def LFml.reads (φ : LFml C) : Reads → Reads :=
  @LFml.rec C (fun _ => Reads → Reads) (fun r => r) (@fun _ a b r => b.reads (a.reads r))
    (fun _ ih r => ih r) (fun _ _ ihφ ihψ r => ihψ (ihφ r)) (fun _ _ ihφ ihψ r => ihψ (ihφ r))
    (fun _ _ _ ih r => ih r) φ

theorem LFml.reads_eq_readsM (φ : LFml C) (r : Reads) : φ.reads r = φ.readsM r := by
  induction φ generalizing r with
  | tt | eq => rfl
  | not φ ih | all k p φ ih => simp only [LFml.readsM, ← ih]; rfl
  | and φ ψ ihφ ihψ | imp φ ψ ihφ ihψ => simp only [LFml.readsM, ← ihφ, ← ihψ]; rfl

/-- `LFml.spine`'s compiled twin. -/
def LFml.spineM : LFml C → List (LFml C) × Reads → List (LFml C) × Reads
  | .imp P ψ, a => ψ.spineM (P :: a.1, a.2)
  | .and φ ψ, a => ψ.spineM (φ.spineM a)
  | .all _ _ φ, a => φ.spineM a
  | φ, a => (a.1, φ.reads a.2)

/-- **The premises of a formula's positive spine**, innermost first, and what
its conclusions read, added to `a`.  By the recursor. -/
@[implemented_by LFml.spineM]
def LFml.spine (φ : LFml C) : List (LFml C) × Reads → List (LFml C) × Reads :=
  @LFml.rec C (fun _ => List (LFml C) × Reads → List (LFml C) × Reads)
    (fun a => (a.1, a.2)) (@fun _ x y a => (a.1, (LFml.eq x y).reads a.2))
    (fun φ _ a => (a.1, (LFml.not φ).reads a.2))
    (fun _ _ ihφ ihψ a => ihψ (ihφ a)) (fun P _ _ ihψ a => ihψ (P :: a.1, a.2))
    (fun _ _ _ ih a => ih a) φ

theorem LFml.spine_eq_spineM (φ : LFml C) (a : List (LFml C) × Reads) :
    φ.spine a = φ.spineM a := by
  induction φ generalizing a with
  | tt => rfl
  | eq | not => simp only [LFml.spineM]; rfl
  | all k p φ ih => simp only [LFml.spineM, ← ih]; rfl
  | and φ ψ ihφ ihψ => simp only [LFml.spineM, ← ihφ, ← ihψ]; rfl
  | imp φ ψ ihφ ihψ => simp only [LFml.spineM, ← ihψ]; rfl

/-- Whether a premise reading `s` bears on what `r` reads: it reads nothing
(a ground fact, which may refute alone), or a position `r` reads, or the
state where `r` reads it. -/
def Reads.bears (r s : Reads) : Bool :=
  (s.1.isEmpty && !s.2) || (r.2 && s.2) || s.1.any r.1.contains

/-- What `r` and `s` read together. -/
def Reads.union (r s : Reads) : Reads := (s.1.foldl (fun l x => l.insert x) r.1, r.2 || s.2)

/-- `r`, grown by every premise of `ss` it bears on, until it grows no
more, at most `n` rounds. -/
def Reads.grow (ss : List Reads) (n : Nat) (r : Reads) : Reads :=
  Nat.rec (motive := fun _ => Reads → Reads) (fun r => r)
    (fun _ ih r =>
      let r' := ss.foldl (fun r s => bif r.bears s then r.union s else r) r
      bif r'.1.length == r.1.length && r'.2 == r.2 then r else ih r') n r

/-- `LFml.dropPrem`'s compiled twin. -/
def LFml.dropPremM (d : LFml C → Bool) : LFml C → LFml C
  | .imp P ψ => bif d P then ψ.dropPremM d else .imp P (ψ.dropPremM d)
  | .and φ ψ => .and (φ.dropPremM d) (ψ.dropPremM d)
  | .all k p φ => .all k p (φ.dropPremM d)
  | φ => φ

/-- **The premises of the positive spine that `d` picks, dropped.**  By the
recursor. -/
@[implemented_by LFml.dropPremM]
def LFml.dropPrem (d : LFml C → Bool) (φ : LFml C) : LFml C :=
  @LFml.rec C (fun _ => LFml C) .tt (@fun _ a b => .eq a b) (fun φ _ => .not φ)
    (fun _ _ ihφ ihψ => .and ihφ ihψ) (fun P _ _ ihψ => bif d P then ihψ else .imp P ihψ)
    (fun k p _ ih => .all k p ih) φ

theorem LFml.dropPrem_eq_dropPremM (d : LFml C → Bool) (φ : LFml C) :
    φ.dropPrem d = φ.dropPremM d := by
  induction φ with
  | tt | eq | not => rfl
  | all k p φ ih => simp only [LFml.dropPremM, ← ih]; rfl
  | and φ ψ ihφ ihψ => simp only [LFml.dropPremM, ← ihφ, ← ihψ]; rfl
  | imp φ ψ ihφ ihψ => simp only [LFml.dropPremM, ← ihψ]; rfl

theorem LFml.dropPremM_holds (d : LFml C → Bool) (g : State C []) :
    ∀ (φ : LFml C) (ν : AEnv), (φ.dropPremM d).holds g ν → φ.holds g ν := by
  intro φ
  induction φ with
  | tt | eq | not => exact fun _ h => h
  | all k p φ ih => exact fun ν h v => ih _ (h v)
  | and φ ψ ihφ ihψ => exact fun ν h => ⟨ihφ ν h.1, ihψ ν h.2⟩
  | imp P ψ _ ihψ =>
    intro ν h
    cases hd : d P
    · simp only [LFml.dropPremM, hd, cond_false] at h
      exact fun hP => ihψ ν (h hP)
    · simp only [LFml.dropPremM, hd, cond_true] at h
      exact fun _ => ihψ ν h

/-- **Dropping premises strengthens a formula.** -/
theorem LFml.dropPrem_holds (d : LFml C → Bool) (g : State C []) (φ : LFml C) (ν : AEnv)
    (h : (φ.dropPrem d).holds g ν) : φ.holds g ν := by
  rw [LFml.dropPrem_eq_dropPremM] at h
  exact LFml.dropPremM_holds d g φ ν h

/-- **A refutation's formula, sliced**: its premises the innermost one (the
condition refuted) and its conclusions do not reach (`Reads.grow`)
dropped. -/
def LFml.slice (φ : LFml C) : LFml C :=
  let sp := φ.spine ([], ([], false))
  let ss := sp.1.map (·.reads ([], false))
  let r := Reads.grow ss ss.length (match ss with
    | [] => sp.2
    | s :: _ => sp.2.union s)
  φ.dropPrem fun P => !r.bears (P.reads ([], false))

theorem LFml.slice_holds {φ : LFml C} {g : State C []} {ν : AEnv} (h : φ.slice.holds g ν) :
    φ.holds g ν :=
  LFml.dropPrem_holds _ g φ ν h

/-- The most stacked storage updates of a refutation the closer reads
whole: past them it is sliced first (`LFml.refuteForm`). -/
def sliceDepth : Nat := 2

/-- **The formula a refutation is closed on**: itself where it stacks at
most `sliceDepth` storage updates, as the leaf closer reads it; else sliced
(`LFml.slice`) where what is left reads no state, so that the closer's
reading of storage and memory, whose cost its bounds (`LFml.boundsOk`) are
set for on the whole leaf, is never asked of a sliced one; else itself. -/
def LFml.refuteForm (φ : LFml C) : LFml C :=
  bif decide (φ.stDepth ≤ sliceDepth) then φ
  else bif (φ.slice.reads ([], false)).2 then φ else φ.slice

theorem LFml.refuteForm_holds {φ : LFml C} {g : State C []} {ν : AEnv}
    (h : φ.refuteForm.holds g ν) : φ.holds g ν := by
  unfold LFml.refuteForm at h
  cases hc : decide (φ.stDepth ≤ sliceDepth)
  · rw [hc, cond_false] at h
    cases hs : (φ.slice.reads ([], false)).2
    · rw [hs, cond_false] at h; exact LFml.slice_holds h
    · rw [hs, cond_true] at h; exact h
  · rw [hc, cond_true] at h; exact h

end Decide

namespace Seq

/-- **The scoped closer on a refutation**: `checkCore` on its formula,
sliced where it stacks storage updates (`LFml.refuteForm`). -/
def refuteCore (ψ : Fml C []) : Bool :=
  match ψ.toLS true SymS.init with
  | some l => l.refuteForm.boundsOk &&
      bif ψ.assumesCT then l.refuteForm.decideMemCT || l.refuteForm.decideMem
      else l.refuteForm.decideMem
  | none => false

theorem refuteCore_valid {ψ : Fml C []} (h : refuteCore ψ = true) : Valid ψ := by
  unfold refuteCore at h
  split at h
  case h_2 => cases h
  rename_i l hl
  rw [Bool.and_eq_true] at h
  have hc := h.2
  cases hct : ψ.assumesCT
  · rw [hct, cond_false] at hc
    exact Valid.of_toLS hl fun g ν => LFml.refuteForm_holds (LFml.decideMem_valid hc g ν)
  · rw [hct, cond_true, Bool.or_eq_true] at hc
    rcases hc with hc | hc
    case inr =>
      exact Valid.of_toLS hl fun g ν => LFml.refuteForm_holds (LFml.decideMem_valid hc g ν)
    intro τ
    by_cases hg : TSto.CleanTails τ.storage.obs
    · exact (Fml.toLS_sound ψ true hl τ AEnv.dflt (Agrees.init τ AEnv.dflt)
        SymS.Fresh.init).1 rfl
        (LFml.refuteForm_holds (LFml.decideMemCT_holds hc τ AEnv.dflt hg))
    · exact Fml.assumesCT_holds ψ hct τ hg

/-- **A split's branch refuted**: `H, c ⟹ false` closed by the scoped closer
on the premises `c` reaches (`refuteCore`). -/
def refuteS {Γ : Ctx} (H : Hyps C [] Γ) (c : Fml C Γ) : Bool :=
  ((H.pre c).wrap .ff).modalFree && refuteCore ((H.pre c).wrap .ff)

theorem refuteS_sound {R : RuleSet} {Γ : Ctx} (H : Hyps C [] Γ) (c : Fml C Γ)
    (h : refuteS H c = true) : Proves C R [] (H.pre c) .ff := by
  rw [refuteS, Bool.and_eq_true] at h
  exact Proves.closeHolds (refuteCore_valid h.2) h.1

end Seq

end Solidity
