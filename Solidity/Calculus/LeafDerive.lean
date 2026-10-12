import Solidity.Calculus.Derive

/-!
# A leaf of `sol_prove`'s walk, closed on the scoped form

`sol_prove`'s walk (`Calculus/ProvesDerive.lean`) leaves a leaf `H ⊢ φ`
where no program rule fits.  Here it is closed on its scoped form, with no
erasure (`Seq.leafCheckS`): the sequent put back together (`Hyps.wrap`),
no modality left (`Fml.modalFree`), its premise `wt(storage)` read as the
layout the storage holds (`Fml.layoutS`, set aside by `Fml.dropWtS`,
proposal 100), its updates pushed in by position (`Fml.toLS`,
`Calculus/DecideScoped.lean`) within `closeSize` nodes, and the reduction
(`Fml.reduceS`) closed by `LFml.closeS`.  Soundness is `Valid.of_reduceSL`
and `LFml.closeS_valid`, then `Proves.closeHolds`.  A leaf outside the
fragment is not read (`none`); the walk hands it to the erased closer
(`Seq.leafS`), the fallback.

The parameters stay quantified: the reduction binds each to its position
(`LFml.all`), which the closer reads with its type (`Facts.bind`).  The
erased route's `pick` (decision 27), the parameters free first and bound
where only that closes, has no scoped counterpart to choose between: bound
is what the scoped leaf is, and the closer knows at least as much of a
bound parameter as of a free one.  Two parallel elements and an
allocation's pair are read as they are (`ElemS.parOk`, `pairLS`), so no
`seqUpd` precedes the reduction.

A leaf the fragment does not read as it is is read prepared (`Fml.prepS`,
each step only implies the leaf, `holds_of_prepS`): a push's returned
alias, `{storage := extend(storage, a) ‖ x := next(a)}` (`T storage x =
a.push();`), is the push and then the alias to the last slot, the length
read after the push (`Upd.pushSplit`, the scoped `Derive.pushAlias?`).

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

/-! ## The alias a push returns, by position

`T storage x = a.push();` leaves `{storage := extend(storage, a) ‖ x :=
next(a)}` (`storageLocalRootPushBind`): the alias names the slot past the
old end, which the push makes live, so the fragment does not read the two
in one state (`ElemS.parOk`).  `Upd.pushSplit` reads it as the push, then
the alias to the last slot, the length read after the push (`lastSlotS`):
the two agree where the path to the array reads the storage only to check
its indices (`Tm.stablePathS`).  The scoped `Derive.pushAlias?`. -/

section PushAlias

open Semantics (Seg Res)
open SemanticsProperties

variable {Γ : Ctx}

/-- A key that reads no storage: a local or a literal. -/
def _root_.Solidity.Tm.keyFreeS : Tm C Γ .val → Bool
  | .pvV _ => true
  | .app0 (.lit _) => true
  | _ => false

/-- `Tm.stablePathS`' compiled twin. -/
def _root_.Solidity.Tm.stablePathSM : {s : Srt} → Tm C Γ s → Bool
  | _, .app0 (.root _) => true
  | _, .pvP _ => true
  | _, .app1 (.field _) _ q => q.stablePathSM
  | _, .app2 .at q k => q.stablePathSM && k.keyFreeS
  | _, _ => false

/-- **A path that reads the storage only to check its indices**: roots,
aliases, members, and indices by locals or literals (`Tm.stablePath` by
position).  A write below it leaves it naming the same location.  By the
recursor. -/
@[implemented_by Tm.stablePathSM]
def _root_.Solidity.Tm.stablePathS {s : Srt} (t : Tm C Γ s) : Bool :=
  Tm.rec (motive := fun _ _ => Bool)
    (fun _ => false) (fun _ => true) (fun _ => false) (fun _ => false) (fun _ _ _ => false)
    (@fun s o => match s, o with
      | _, .root _ => true
      | _, _ => false)
    (@fun a s o _ _ ih => match a, s, o with
      | _, _, .field _ => ih
      | _, _, _ => false)
    (@fun a b s o _ y iha _ => match a, b, s, o, y with
      | _, _, _, .at, y => iha && y.keyFreeS
      | _, _, _, _, _ => false)
    (fun _ _ _ _ _ _ _ => false) t

theorem _root_.Solidity.Tm.stablePathS_eq_stablePathSM {s : Srt} (t : Tm C Γ s) :
    t.stablePathS = t.stablePathSM := by
  induction t with
  | pvV _ | pvP _ | pvS _ | pvI _ | netOf _ _ | app3 _ _ _ _ => rfl
  | app0 o => cases o <;> rfl
  | app1 o _ x ih => cases o <;> first | rfl | (simp only [Tm.stablePathSM, ← ih]; rfl)
  | app2 o x y ihx ihy => cases o <;> first | rfl | (simp only [Tm.stablePathSM, ← ihx]; rfl)

/-- Where `p = a.push();` leaves its alias: the last slot, once the push
is made (`a[a.length - 1]`, the length unchecked), as `Derive.lastSlot`. -/
def lastSlotS (P : Tm C Γ .path) : Tm C Γ .path :=
  .app2 .at P (.app2 (.binop .sub .bool) (.app2 .len (.app0 .storage) P) (.app0 (.lit (.int 1))))

/-- `extend(storage, a)`: the array's type and path. -/
def _root_.Solidity.Tm.extendOf? : Tm C Γ .st → Option (Ty × Tm C Γ .path)
  | .app2 (.extend E) (.app0 .storage) P => some (E, P)
  | _ => none

/-- `next(a)`: the array's path. -/
def _root_.Solidity.Tm.nextOf? : Tm C Γ .path → Option (Tm C Γ .path)
  | .app1 .next _ P => some P
  | _ => none

/-- `{storage := extend(storage, a)}`, the push alone: the array's path,
read before the update and after it (one scope). -/
def _root_.Solidity.Upd.pushOf? {Δ : Ctx} : Upd C Γ Δ → Option (Tm C Γ .path × Tm C Δ .path)
  | .snoc .nil (.storage S) => S.extendOf?.map fun p => (p.2, p.2)
  | _ => none

/-- **The push and its alias, one after the other**: `{storage :=
extend(storage, a) ‖ x := next(a)} φ` read as `{storage := extend(storage,
a)}{x := a[a.length - 1]} φ`, where `a` is a stable path. -/
def _root_.Solidity.Upd.pushSplit (m : Modality) {Δ : Ctx} : Upd C Γ Δ → Fml C Δ → Option (Fml C Γ)
  | .snoc V (.local i (.path n)), φ =>
    match V.pushOf?, n.nextOf? with
    | some (P, Q), some P' =>
      bif P.stablePathS && P.beqR P' then
        some (.upd m V (.upd m (Upd.nil.snoc (.local i (.path (lastSlotS Q)))) φ))
      else none
    | _, _ => none
  | _, _ => none

theorem keyFreeS_eval {σ : EState C Γ} {τ : Semantics.State} :
    (k : Tm C Γ .val) → k.keyFreeS = true → k.eval (σ.withGlob τ) = k.eval σ
  | .pvV _, _ => rfl
  | .app0 (.lit _), _ => rfl

theorem withGlob_saveStorage {σ : Semantics.State} {τ : Semantics.State} {r : Name} {P : List Seg}
    {X : Semantics.SVal} (h : σ.saveStorage r P X = .ok τ) : τ = { σ with storage := τ.storage } := by
  unfold Semantics.State.saveStorage at h
  split at h
  · obtain ⟨_, _, he⟩ := SemanticsProperties.Res.bind_eq_ok.1 h; cases he; rfl
  · cases h

/-- **A path below which the storage was written names the same
location** (`Derive.stable_eval` by position): its checks are of locations
above the write. -/
theorem stable_evalS {σ : EState C Γ} {τ : Semantics.State} {r : Name} {P : List Seg} {X : Semantics.SVal}
    (hsv : σ.glob.saveStorage r P X = .ok τ) :
    (p : Tm C Γ .path) → p.stablePathSM = true → ∀ {r' : Name} {segs : List Seg},
      p.eval σ = .ok (r', segs) → (r' = r → ∃ rest, P = segs ++ rest) →
        p.eval (σ.withGlob τ) = .ok (r', segs)
  | .app0 (.root _), _, _, _, h, _ => h
  | .pvP _, _, _, _, h, _ => h
  | .app1 (.field f) _ q, hp, r', segs, h, hpre => by
    simp only [Tm.stablePathSM] at hp
    simp only [Tm.eval, Op1.eval] at h ⊢
    obtain ⟨⟨r₀, segs₀⟩, h₀, he⟩ := Res.bind_eq_ok.1 h
    cases he
    rw [stable_evalS hsv q hp h₀ fun hr => by
      obtain ⟨rest, hrest⟩ := hpre hr
      exact ⟨.field f :: rest, by simp only [hrest, List.append_assoc, List.cons_append,
          List.nil_append]⟩]
    rfl
  | .app2 .at q k, hp, r', segs, h, hpre => by
    simp only [Tm.stablePathSM, Bool.and_eq_true] at hp
    simp only [Tm.eval, Op2.eval] at h ⊢
    obtain ⟨⟨r₀, segs₀⟩, h₀, h⟩ := Res.bind_eq_ok.1 h
    obtain ⟨v, hv, h⟩ := Res.bind_eq_ok.1 h
    obtain ⟨i, hi, h⟩ := Res.bind_eq_ok.1 h
    obtain ⟨_, hc, he⟩ := Res.bind_eq_ok.1 h
    cases he
    rw [stable_evalS hsv q hp.1 h₀ fun hr => by
      obtain ⟨rest, hrest⟩ := hpre hr
      exact ⟨.at i :: rest, by simp only [hrest, List.append_assoc, List.cons_append,
          List.nil_append]⟩, Res.ok_bind, keyFreeS_eval k hp.2, hv, Res.ok_bind, hi,
      Res.ok_bind]
    have hτ : (σ.withGlob τ).glob = τ := by
      rw [withGlob_saveStorage hsv]; rfl
    rw [hτ, Close.checkIndex_saveStorage_apart i hsv ?_, hc, Res.ok_bind]
    · rfl
    by_cases hr : r₀ = r
    · subst hr
      obtain ⟨rest, hrest⟩ := hpre rfl
      refine .inr fun hpf => ?_
      have hl := congrArg List.length (Close.prefix_append hpf)
      rw [hrest] at hl
      simp only [List.length_append, List.length_cons, List.length_nil] at hl
      omega
    · exact .inl hr
  | .app1 .next _ _, h, _, _, _, _ | .app2 .nextIn _ _, h, _, _, _, _
  | .app3 .atIn _ _ _, h, _, _, _, _ => by simp only [Tm.stablePathSM, Bool.false_eq_true] at h

/-- **The last slot after the push is the slot past the end before it**
(`Derive.lastSlot_eval` by position). -/
theorem lastSlotS_eval {σ : EState C Γ} {P : Tm C Γ .path} (hP : P.stablePathSM = true) {E : Ty}
    {τ : Semantics.State}
    (hs : (Tm.app2 (.extend E) (.app0 .storage) P : Tm C Γ .st).eval σ = .ok τ) :
    (lastSlotS P).eval (σ.withGlob { σ.glob with storage := τ.storage }) =
      (Tm.app1 .next rfl P).eval σ := by
  simp only [Tm.eval, Op2.eval, Op0.eval, pure_bind] at hs
  obtain ⟨⟨r, segs⟩, hp, hs⟩ := Res.bind_eq_ok.1 hs
  obtain ⟨⟨τ', n⟩, hpp, he⟩ := Res.bind_eq_ok.1 hs
  cases he
  simp only [pushPlaceAt] at hpp
  obtain ⟨c, hc, hpp⟩ := Res.bind_eq_ok.1 hpp
  cases c with
  | array elems sh fx =>
    obtain ⟨τ'', hsv, he⟩ := Res.bind_eq_ok.1 hpp
    cases he
    have hst := withGlob_saveStorage hsv
    have hp' := stable_evalS hsv P hP hp (fun _ => ⟨[], by simp only [List.append_nil]⟩)
    have hf := State.findStorage_saveStorage_same hsv
    have hτ : ({ σ.glob with storage := τ'.storage } : Semantics.State) = τ' := hst.symm
    dsimp only
    rw [hτ]
    simp only [lastSlotS, Tm.eval, Op2.eval, Op1.eval, Op0.eval, hp', hp, hc, Res.ok_bind]
    have hg : (σ.withGlob τ').glob = τ' := by rw [hst]; rfl
    simp only [hg, Close.arrayLen_eq, hf, Close.arrLen, evalBinop,
      Semantics.applyBinOp, Semantics.Value.asInt, bind, Except.bind, Semantics.checkArith,
      BinOp.retTy, BinOp.isArith, Close.checkIndex_eq, List.length_append, List.length_singleton,
      pure, Except.pure]
    simp only [↓reduceIte, Int.natCast_add, Int.cast_ofNat_Int, Int.add_sub_cancel, Close.idxOk,
      Int.ofNat_zero_le, Int.toNat_natCast, List.length_append, List.length_cons, List.length_nil,
      Nat.zero_add, Nat.lt_add_one, and_self]
    done
  | prim _ | struct _ | map _ _ => nomatch hpp

theorem _root_.Solidity.Env.set_get_self {Γ : Ctx} {t : LTy} (i : Idx Γ t) (e : Env C Γ) :
    Env.set i (Env.get i e) e = e := by
  induction i with
  | here => rfl
  | there i ih => exact congrArg (e.1, ·) (ih e.2)

/-- `extend(storage, a)` returns where `next(a)` does. -/
theorem next_eval_of_extend {σ : EState C Γ} {P : Tm C Γ .path} {E : Ty} {τ : Semantics.State}
    (hs : (Tm.app2 (.extend E) (.app0 .storage) P : Tm C Γ .st).eval σ = .ok τ) :
    ∃ v, (Tm.app1 .next rfl P).eval σ = .ok v := by
  simp only [Tm.eval, Op2.eval, Op0.eval, pure_bind] at hs
  obtain ⟨⟨r, segs⟩, hp, hs⟩ := Res.bind_eq_ok.1 hs
  obtain ⟨⟨τ', n⟩, hpp, -⟩ := Res.bind_eq_ok.1 hs
  simp only [pushPlaceAt] at hpp
  obtain ⟨c, hc, hpp⟩ := Res.bind_eq_ok.1 hpp
  cases c with
  | array elems sh fx =>
    exact ⟨_, by simp only [Tm.eval, Op1.eval, hp, hc, Res.ok_bind]; rfl⟩
  | prim _ | struct _ | map _ _ => nomatch hpp

/-- `pushSplit`'s soundness on the update it splits. -/
theorem holds_push_alias {m : Modality} {E : Ty} {P : Tm C Γ .path} {R : RefTy}
    {i : Idx Γ (.alias R)} {φ : Fml C Γ} (hP : P.stablePathSM = true) (σ : State C Γ)
    (hψ : holds σ (.upd m (Upd.nil.snoc (.storage (.app2 (.extend E) (.app0 .storage) P)))
      (.upd m (Upd.nil.snoc (.local i (.path (lastSlotS P)))) φ))) :
    holds σ (.upd m ((Upd.nil.snoc (.storage (.app2 (.extend E) (.app0 .storage) P))).snoc
      (.local i (.path (.app1 .next rfl P)))) φ) := by
  show m.afterC (fun τ => ∀ σ' : State C Γ, σ'.erase = τ → σ.H <+: σ'.H → holds σ' φ)
    (Upd.apply σ.erase _)
  have hψ' : m.afterC (fun τ => ∀ σ' : State C Γ, σ'.erase = τ → σ.H <+: σ'.H →
      holds σ' (.upd m (Upd.nil.snoc (.local i (.path (lastSlotS P)))) φ))
      (Upd.apply σ.erase (Upd.nil.snoc (.storage (.app2 (.extend E) (.app0 .storage) P)))) := hψ
  simp only [Upd.apply, UpdElem.write, pure_bind] at hψ' ⊢
  cases hS : (Tm.app2 (.extend E) (.app0 .storage) P : Tm C Γ .st).eval σ.erase with
  | error e => simp only [hS, Res.error_bind] at hψ' ⊢; exact hψ'
  | ok τ =>
    obtain ⟨v, hv⟩ := next_eval_of_extend hS
    have hl := lastSlotS_eval hP hS
    rw [hv] at hl
    simp only [hS, Res.ok_bind, Rhs.eval, hv] at hψ' ⊢
    intro σ'' he hH
    let τ₁ := σ.erase.withGlob { σ.erase.glob with storage := τ.storage }
    let w : Option (SRef C (.ref R)) := TEnv.get i σ.env
    let σ' : State C Γ := σ''.setLocal i w
    have he' : σ'.erase = τ₁ := by
      simp only [σ', State.setLocal_erase, he, EState.setLocal_setLocal]
      have hw : LTy.TDenote.erase (H := σ''.H) (LTy.alias R) w = Env.get i τ₁.env :=
        (TEnv.get_erase i σ.env).symm
      show τ₁.withEnv (Env.set i (LTy.TDenote.erase (H := σ''.H) (LTy.alias R) w) τ₁.env) = τ₁
      rw [hw, Env.set_get_self]
      rfl
    have h₂ := hψ' σ' he' hH
    change m.afterC _ (Upd.apply σ'.erase _) at h₂
    dsimp only at hl
    rw [he'] at h₂
    simp only [τ₁, Upd.apply, UpdElem.write, Rhs.eval, pure_bind, hl, Res.ok_bind] at h₂
    exact h₂ σ'' he (List.prefix_refl _)

/-- **The push, then its alias, give the parallel update**: a state the
first leaves in reads the alias at the last slot where the second read it
past the end before the push (`lastSlotS_eval`); the typed state between
the two is the one the parallel update ends in, its alias as before. -/
theorem holds_pushSplit {m : Modality} {Δ : Ctx} {U : Upd C Γ Δ} {φ : Fml C Δ} {ψ : Fml C Γ}
    (h : U.pushSplit m φ = some ψ) (σ : State C Γ) (hψ : holds σ ψ) : holds σ (.upd m U φ) := by
  unfold Upd.pushSplit at h
  split at h
  · rename_i V t i n
    split at h
    · rename_i P Q P' hV hn
      cases hb : (P.stablePathS && P.beqR P')
      · simp only [hb, cond_false, reduceCtorEq] at h
      simp only [hb, cond_true, Option.some.injEq] at h
      subst h
      simp only [Bool.and_eq_true] at hb
      obtain ⟨hs, hbeq⟩ := hb
      cases Tm.eq_of_beqR hbeq
      unfold Tm.nextOf? at hn
      split at hn
      · rename_i P₀ _
        cases hn
        unfold Upd.pushOf? at hV
        split at hV
        · rename_i S
          unfold Tm.extendOf? at hV
          split at hV
          · rename_i E P
            cases hV
            exact holds_push_alias (Tm.stablePathS_eq_stablePathSM P ▸ hs) σ hψ
          · cases hV
        · cases hV
      · cases hn
    · cases h
  · cases h

end PushAlias

/-! ## A leaf prepared for the fragment -/

section Prep

/-- A hidden binder of a value as the `∀` it reads as; any other kept. -/
def _root_.Solidity.Fml.bindAsAll {Γ : Ctx} (m : Modality) (x : Var) :
    (t : LTy) → Fml C (t :: Γ) → Fml C Γ
  | .val p, φ => .all x p φ
  | t, φ => .bind m x t φ

theorem holds_bindAsAll {Γ : Ctx} {m : Modality} {x : Var} :
    (t : LTy) → {φ : Fml C (t :: Γ)} → (σ : State C Γ) →
      holds σ (Fml.bindAsAll m x t φ) → holds σ (.bind m x t φ)
  | .val _, _, _, h => fun v => h v
  | .alias _, _, _, h | .mem _, _, _, h | .old, _, _, h | .oldNet, _, _, h => h

/-- `Fml.prepS`' compiled twin. -/
def _root_.Solidity.Fml.prepSM : {Γ : Ctx} → Fml C Γ → Fml C Γ
  | _, .upd m U φ =>
    match U.pushSplit m φ.prepSM with
    | some ψ => ψ
    | none => .upd m U φ.prepSM
  | _, .imp a φ => .imp a φ.prepSM
  | _, .and φ ψ => .and φ.prepSM ψ.prepSM
  | _, .all x p φ => .all x p φ.prepSM
  | _, .bind m x t φ => Fml.bindAsAll m x t φ.prepSM
  | _, φ => φ

/-- **A leaf rewritten where the fragment does not read it**, in the
positions a leaf proves (not in a premise): a push and its returned alias
one after the other (`Upd.pushSplit`); a hidden binder of a value as the
`∀` it reads as (a `spec!{f}` obligation binds its parameters so), whose
local the reduction then reads at its position before any update binds
it.  Each step only implies the leaf
(`holds_of_prepS`).  By the recursor. -/
@[implemented_by Fml.prepSM]
def _root_.Solidity.Fml.prepS {Γ : Ctx} (φ : Fml C Γ) : Fml C Γ :=
  Fml.rec (motive := fun Γ _ => Fml C Γ)
    .tt (fun a b => .eq a b) (fun t => .defined t) (fun φ _ => .not φ)
    (fun _ _ ihφ ihψ => .and ihφ ihψ) (fun a _ _ ih => .imp a ih)
    (fun m U _ ih =>
      match U.pushSplit m ih with
      | some ψ => ψ
      | none => .upd m U ih)
    (fun m P κ φ _ => .modal m P κ φ) (fun φ _ => .havoc φ) (fun x p _ ih => .all x p ih)
    (fun m x t _ ih => Fml.bindAsAll m x t ih)
    (fun xs φ _ => .anon xs φ) φ

theorem _root_.Solidity.Fml.prepS_eq_prepSM {Γ : Ctx} (φ : Fml C Γ) : φ.prepS = φ.prepSM := by
  induction φ with
  | upd m U φ ih => simp only [Fml.prepSM, ← ih]; rfl
  | imp a φ _ ih => simp only [Fml.prepSM, ← ih]; rfl
  | and φ ψ ihφ ihψ => simp only [Fml.prepSM, ← ihφ, ← ihψ]; rfl
  | all x p φ ih | bind m x t φ ih => simp only [Fml.prepSM, ← ih]; rfl
  | _ => rfl

/-- An update's reading is monotone in what it asks after. -/
theorem holds_upd_imp {Γ Δ : Ctx} {m : Modality} {U : Upd C Γ Δ} {φ ψ : Fml C Δ}
    (hφ : ∀ σ' : State C Δ, holds σ' φ → holds σ' ψ) (σ : State C Γ)
    (h : holds σ (.upd m U φ)) : holds σ (.upd m U ψ) := by
  change m.afterC (fun τ => ∀ σ' : State C Δ, σ'.erase = τ → σ.H <+: σ'.H → holds σ' ψ)
    (U.apply σ.erase)
  have h' : m.afterC (fun τ => ∀ σ' : State C Δ, σ'.erase = τ → σ.H <+: σ'.H → holds σ' φ)
    (U.apply σ.erase) := h
  revert h'
  cases U.apply σ.erase with
  | error _ => exact id
  | ok τ => exact fun h' σ' he hH => hφ σ' (h' σ' he hH)

/-- **The prepared leaf implies the leaf.** -/
theorem holds_of_prepS {Γ : Ctx} (φ : Fml C Γ) : ∀ σ : State C Γ, holds σ φ.prepS → holds σ φ := by
  rw [Fml.prepS_eq_prepSM]
  induction φ with
  | upd m U φ ih =>
    intro σ h
    simp only [Fml.prepSM] at h
    split at h
    · exact holds_upd_imp ih σ (holds_pushSplit ‹_› σ h)
    · exact holds_upd_imp ih σ h
  | imp a φ _ ih => exact fun σ h ha => ih σ (h ha)
  | and φ ψ ihφ ihψ => exact fun σ h => ⟨ihφ σ h.1, ihψ σ h.2⟩
  | all x p φ ih => exact fun σ h v => ih _ (h v)
  | bind m x t φ ih =>
    exact fun σ h => Modality.forallB_imp (fun v => ih _) (holds_bindAsAll t σ h)
  | _ => exact fun _ h => h

end Prep

/-! ## The leaf closer -/

namespace Seq

/-- `checkCore`'s compiled twin: the formula with its premise set aside
and its updates pushed in computed once. -/
def checkCoreM (ψ : Fml C []) : Option Bool :=
  let ψ' := ψ.dropWtS
  if ψ'.inLS true SymS.empty then
    let l := ψ'.toLS SymS.empty
    some ((l.fits Decide.closeSize).isSome && LFml.closeS ψ.layoutS l.elim)
  else none

/-- **The scoped closer on a leaf `ψ` of no modality**: `none` where it
does not read it (outside the fragment once its `wt(storage)` premise is
set aside); else whether it closes it: within `closeSize` nodes with its
updates pushed in (the cheap bound, tested before the reduction is built),
and its reduction closed by `LFml.closeS` with the premise's layout. -/
@[implemented_by checkCoreM]
def checkCore (ψ : Fml C []) : Option Bool :=
  bif ψ.dropWtS.inLS true SymS.empty then
    some (((ψ.dropWtS.toLS SymS.empty).fits Decide.closeSize).isSome &&
      LFml.closeS ψ.layoutS ψ.dropWtS.reduceS)
  else none

theorem checkCore_eq_checkCoreM (ψ : Fml C []) : checkCore ψ = checkCoreM ψ := by
  simp only [checkCore, checkCoreM, Fml.reduceS]
  cases ψ.dropWtS.inLS true SymS.empty <;> rfl

/-- What `checkCore` closes is valid: `Valid.of_reduceSL` and
`LFml.closeS_valid`. -/
theorem checkCore_valid {ψ : Fml C []} (h : checkCore ψ = some true) : Valid ψ := by
  simp only [checkCore] at h
  cases hc : ψ.dropWtS.inLS true SymS.empty
  · simp only [hc, cond_false, reduceCtorEq] at h
  · simp only [hc, cond_true, Option.some.injEq, Bool.and_eq_true] at h
    exact Valid.of_reduceSL hc (LFml.closeS_valid h.2)

/-- **The scoped closer on a wrapped leaf `ψ`**: none where a modality is
left; else `checkCore` on the leaf, or on it prepared (`Fml.prepS`) where
the fragment does not read it as it is. -/
def leafCheckOn (ψ : Fml C []) : Option Bool :=
  bif ψ.modalFree then
    match checkCore ψ with
    | none => checkCore ψ.prepS
    | r => r
  else none

/-- `leafFitsOn` on a leaf without its modality test. -/
def fitsCore (ψ : Fml C []) : Bool :=
  let ψ' := ψ.dropWtS
  ψ'.inLS true SymS.empty &&
    (let l := ψ'.toLS SymS.empty
     (l.fits Decide.closeSize).isSome && (l.elim.fits Decide.elimSize).isSome)

/-- **The closer's bounds on a wrapped leaf** (`Derive.leafFits` by
position), which `sol_prove?` asks before it tries a step that reduces the
leaf (the reduction, its quoting and its kernel check heed no heartbeats):
the scoped closer reads it, as it is or prepared (`Fml.prepS`), within
`closeSize` with its updates pushed in, and its reduction is within
`elimSize`.  The reduction is built only within the first bound. -/
def leafFitsOn (ψ : Fml C []) : Bool :=
  ψ.modalFree && (fitsCore ψ || fitsCore ψ.prepS)

/-- `leafCheckOn` on the leaf `H ⊢ φ`. -/
def leafCheckS {Γ : Ctx} (H : Hyps C [] Γ) (φ : Fml C Γ) : Option Bool := leafCheckOn (H.wrap φ)

/-- **A leaf the scoped closer closes is proved**: `Proves.closeHolds`. -/
theorem leafCheckS_sound {R : RuleSet} {Γ : Ctx} {H : Hyps C [] Γ} {φ : Fml C Γ}
    (h : leafCheckS H φ = some true) : Proves C R [] H φ := by
  simp only [leafCheckS, leafCheckOn] at h
  cases hm : (H.wrap φ).modalFree
  · simp only [hm, cond_false, reduceCtorEq] at h
  simp only [hm, cond_true] at h
  refine Proves.closeHolds ?_ hm
  split at h
  · exact fun σ => holds_of_prepS _ σ (checkCore_valid h σ)
  · exact checkCore_valid h

end Seq

end Solidity
