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
read after the push (`Upd.pushSplit`).

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
its indices (`Tm.stablePathS`). -/

section PushAlias

open Semantics (Seg Res)
open SemanticsProperties

variable {Γ : Ctx}

/-- A root. -/
def _root_.Solidity.Op0.isRoot {s : Srt} : Op0 C s → Bool
  | .root _ _ => true
  | _ => false

/-- A member. -/
def _root_.Solidity.Op1.isField {a s : Srt} : Op1 C a s → Bool
  | .field _ => true
  | _ => false

/-- An index. -/
def _root_.Solidity.Op2.isAt {a b s : Srt} : Op2 C a b s → Bool
  | .at _ => true
  | _ => false

/-- A key that reads no storage: a local or a literal. -/
def _root_.Solidity.Tm.keyFreeS {s : Srt} : Tm C Γ s → Bool
  | .pvV _ => true
  | .app0 o => o.isLit
  | _ => false

/-- `Tm.stablePathS`' compiled twin. -/
def _root_.Solidity.Tm.stablePathSM : {s : Srt} → Tm C Γ s → Bool
  | _, .app0 o => o.isRoot
  | _, .pvP _ => true
  | _, .app1 o q => o.isField && q.stablePathSM
  | _, .app2 o q k => o.isAt && q.stablePathSM && k.keyFreeS
  | _, _ => false

/-- **A path that reads the storage only to check its indices**: roots,
aliases, members, and indices by locals or literals.  A write below it leaves it naming the same location.  By the
recursor. -/
@[implemented_by Tm.stablePathSM]
def _root_.Solidity.Tm.stablePathS {s : Srt} (t : Tm C Γ s) : Bool :=
  Tm.rec (motive := fun _ _ => Bool)
    (fun _ => false) (fun _ => true) (fun _ => false) (fun _ => false) (fun _ _ _ => false)
    (fun o => o.isRoot) (fun o _ ih => o.isField && ih)
    (fun o _ y iha _ => o.isAt && iha && y.keyFreeS)
    (fun _ _ _ _ _ _ _ => false) t

theorem _root_.Solidity.Tm.stablePathS_eq_stablePathSM {s : Srt} (t : Tm C Γ s) :
    t.stablePathS = t.stablePathSM := by
  induction t with
  | pvV _ | pvP _ | pvS _ | pvI _ | netOf _ _ | app0 _ | app3 _ _ _ _ => rfl
  | app1 o x ih => simp only [Tm.stablePathSM, ← ih]; rfl
  | app2 o x y ihx ihy => simp only [Tm.stablePathSM, ← ihx]; rfl

/-- Where `p = a.push();` leaves its alias: the last slot, once the push
is made (`a[a.length - 1]`). -/
def lastSlotS {E : Ty} (P : Tm C Γ (.path (.ref (.array E)))) : Tm C Γ (.path E) :=
  .app2 (.at (.arr .dyn)) P (.app2 (.binop .sub rfl) (.app2 .len (.app0 .storage) P) (Tm.one .uint rfl))

/-- `extend(storage, a)`: the array's path. -/
def _root_.Solidity.Op2.extendArg? {a b s : Srt} : Op2 C a b s → Tm C Γ a → Tm C Γ b →
    Option ((E : Ty) × Tm C Γ (.path (.ref (.array E))))
  | .extend, st, P => if st.isStorageS then some ⟨_, P⟩ else none
  | _, _, _ => none

/-- `extend(storage, a)`: the array's type and path. -/
def _root_.Solidity.Tm.extendOf? {s : Srt} : Tm C Γ s →
    Option ((E : Ty) × Tm C Γ (.path (.ref (.array E))))
  | .app2 o st P => o.extendArg? st P
  | _ => none

/-- `next(a)`: the array's path. -/
def _root_.Solidity.Op1.nextArg? {a : Srt} {T : Ty} : Op1 C a (.path T) → Tm C Γ a →
    Option (Tm C Γ (.path (.ref (.array T))))
  | .next, P => some P
  | _, _ => none

/-- `next(a)`: the array's path. -/
def _root_.Solidity.Tm.nextOf? {T : Ty} : Tm C Γ (.path T) → Option (Tm C Γ (.path (.ref (.array T))))
  | .app1 o P => o.nextArg? P
  | _ => none

/-- `{storage := extend(storage, a)}`, the push alone: the array's path,
read before the update and after it (one scope). -/
def _root_.Solidity.Upd.pushOf? {Δ : Ctx} : Upd C Γ Δ →
    Option ((E : Ty) × Tm C Γ (.path (.ref (.array E))) × Tm C Δ (.path (.ref (.array E))))
  | .snoc .nil (.storage S) => S.extendOf?.map fun p => ⟨p.1, p.2, p.2⟩
  | _ => none

/-- `x := next(a)`: the alias's type, the array's path, and the right-hand
side at the alias's type rebuilt from a path. -/
def _root_.Solidity.Rhs.pushAlias? {Δ : Ctx} {t : LTy} : Rhs C Γ t →
    Option ((R : RefTy) × Tm C Γ (.path (.ref (.array (.ref R)))) ×
      (Tm C Δ (.path (.ref R)) → Rhs C Δ t))
  | .path n => n.nextOf?.map fun P => ⟨_, P, fun q => .path q⟩
  | _ => none

/-- **The push and its alias, one after the other**: `{storage :=
extend(storage, a) ‖ x := next(a)} φ` read as `{storage := extend(storage,
a)}{x := a[a.length - 1]} φ`, where `a` is a stable path. -/
def _root_.Solidity.Upd.pushSplit (m : Modality) {Δ : Ctx} : Upd C Γ Δ → Fml C Δ → Option (Fml C Γ)
  | .snoc V (.local i r), φ =>
    match V.pushOf?, r.pushAlias? (Δ := Δ) with
    | some ⟨E, P, Q⟩, some ⟨R, P', mk⟩ =>
      if h : E = .ref R then
        bif P.stablePathS && P.beqR P' then
          some (.upd m V (.upd m (Upd.nil.snoc (.local i (mk (lastSlotS (h ▸ Q))))) φ))
        else none
      else none
    | _, _ => none
  | _, _ => none

/-! The push's proofs read two typed states: `σ`, the update applied in,
and `x`, a state the storage write lands on (its global part `σ`'s with the
storage written, the same locals).  That a stable path names the same
location after the write is read on the erasure (`stable_evalE`, the
interpreter's frame lemmas); the rest on the typed storage. -/

theorem keyFreeS_evalE {σ x : State C Γ} (hl : ∀ {t : LTy} (i : Idx Γ t), x.getE i = σ.getE i)
    {s : Srt} (k : Tm C Γ s) (h : k.keyFreeS = true) : k.evalE x = k.evalE σ := by
  cases k with
  | pvV i => rw [Tm.evalE_pvV, Tm.evalE_pvV, hl i]
  | app0 o =>
    cases o <;> simp only [Tm.keyFreeS, Op0.isLit, Bool.false_eq_true] at h
    rw [Tm.evalE_lit, Tm.evalE_lit]
  | _ => simp only [Tm.keyFreeS, Bool.false_eq_true] at h

/-- `stable_evalE` below a size. -/
theorem stable_evalE_n {σ x : State C Γ} {τ : Semantics.State} {r : Name} {Pr : List Seg}
    {X : Semantics.SVal} (hsv : σ.globE.saveStorage r Pr X = .ok τ) (hx : x.globE = τ)
    (hl : ∀ {t : LTy} (i : Idx Γ t), x.getE i = σ.getE i) :
    (n : Nat) → ∀ {T : Ty} (p : Tm C Γ (.path T)), p.lsize < n → p.stablePathSM = true →
      ∀ {r' : Name} {segs : List Seg},
      p.evalE σ = .ok (r', segs) → (r' = r → ∃ rest, Pr = segs ++ rest) →
        p.evalE x = .ok (r', segs)
  | 0, _, _, hn, _, _, _, _, _ => absurd hn (Nat.not_lt_zero _)
  | n + 1, T, p, hn, hp, r', segs, h, hpre => by
    cases p with
    | app0 o =>
      cases o
      rw [Tm.evalE_root] at h ⊢
      exact h
    | pvP i =>
      rw [Tm.evalE_pvP] at h ⊢
      rw [hl i]
      exact h
    | app1 o q =>
      cases o with
      | @field s f T hfld =>
        simp only [Tm.stablePathSM, Op1.isField, Bool.true_and] at hp
        rw [Tm.evalE_field] at h ⊢
        obtain ⟨⟨r₀, segs₀⟩, h₀, he⟩ := Res.bind_eq_ok.1 h
        cases he
        rw [stable_evalE_n hsv hx hl n q (by lsizeS_tac) hp h₀ fun hr => by
          obtain ⟨rest, hrest⟩ := hpre hr
          exact ⟨.field f :: rest, by simp only [hrest, List.append_assoc, List.cons_append,
              List.nil_append]⟩]
        rfl
      | next => simp only [Tm.stablePathSM, Op1.isField, Bool.false_and, Bool.false_eq_true] at hp
    | app2 o q k =>
      cases o with
      | «at» it =>
        simp only [Tm.stablePathSM, Op2.isAt, Bool.true_and, Bool.and_eq_true] at hp
        rw [Tm.evalE_at] at h ⊢
        obtain ⟨⟨r₀, segs₀⟩, h₀, h⟩ := Res.bind_eq_ok.1 h
        obtain ⟨i, hi, h⟩ := Res.bind_eq_ok.1 h
        obtain ⟨v, hv, hi⟩ := Res.bind_eq_ok.1 hi
        obtain ⟨_, hc, he⟩ := Res.bind_eq_ok.1 h
        cases he
        rw [stable_evalE_n hsv hx hl n q (by lsizeS_tac) hp.1 h₀ fun hr => by
          obtain ⟨rest, hrest⟩ := hpre hr
          exact ⟨.at i :: rest, by simp only [hrest, List.append_assoc, List.cons_append,
              List.nil_append]⟩, Res.ok_bind, keyFreeS_evalE hl k hp.2, hv, Res.ok_bind, hi,
          Res.ok_bind]
        rw [hx, Close.checkIndex_saveStorage_apart i hsv ?_, hc, Res.ok_bind]
        by_cases hr : r₀ = r
        · subst hr
          obtain ⟨rest, hrest⟩ := hpre rfl
          refine .inr fun hpf => ?_
          have hl := congrArg List.length (Close.prefix_append hpf)
          rw [hrest] at hl
          simp only [List.length_append, List.length_cons, List.length_nil] at hl
          omega
        · exact .inl hr
      | nextIn => simp only [Tm.stablePathSM, Op2.isAt, Bool.false_and, Bool.false_eq_true] at hp
    | app3 o _ _ _ =>
      cases o
      simp only [Tm.stablePathSM, Bool.false_eq_true] at hp

/-- **A path below which the storage was written names the same
location**, erased: its checks are of locations above the write. -/
theorem stable_evalE {σ x : State C Γ} {τ : Semantics.State} {r : Name} {Pr : List Seg}
    {X : Semantics.SVal} (hsv : σ.globE.saveStorage r Pr X = .ok τ) (hx : x.globE = τ)
    (hl : ∀ {t : LTy} (i : Idx Γ t), x.getE i = σ.getE i) {T : Ty} (p : Tm C Γ (.path T))
    (hp : p.stablePathSM = true) {r' : Name} {segs : List Seg}
    (h : p.evalE σ = .ok (r', segs)) (hpre : r' = r → ∃ rest, Pr = segs ++ rest) :
    p.evalE x = .ok (r', segs) :=
  stable_evalE_n hsv hx hl _ p (Nat.lt_succ_self _) hp h hpre

/-- A write's storage reads back what it wrote. -/
theorem Storage.find_save_self {U : Ty} {st st' : Storage C} {r : SRef C U} {v : SVal U}
    (h : st.save r v = some st') : st'.find r = some v := by
  obtain ⟨x', hs, rfl⟩ := Storage.save_some h
  simp only [Storage.find, SFields.get_set_same]
  exact SVal.find_save_same _ _ _ hs

/-- `extend(storage, a)` returns where `next(a)` does, the push read on the
typed storage: the array found, its slot past the end. -/
theorem extend_typed {σ : State C Γ} {E : Ty} {P : Tm C Γ (.path (.ref (.array E)))}
    {st' : Storage C} (hs : (Tm.app2 .extend (.app0 .storage) P : Tm C Γ .st).eval σ = some st') :
    ∃ r w nv, P.eval σ = some r ∧ σ.storage.find r = some w ∧ σ.storage.save r nv = some st' ∧
      ∃ h : (SVal.view w : ArrView E).n + 1 < 2 ^ 256,
        nv = .array (SVec.ofList ((SVal.view w : ArrView E).elems.toList ++
          [(pushSlot E (SVal.view w : ArrView E).shadow.toList).1]))
          (.ofList (pushSlot E (SVal.view w : ArrView E).shadow.toList).2)
          (SVec.snoc_lt_bound _ _ h) := by
  rw [CloseS.eval_extend, CloseS.eval_storage, Option.bind_some] at hs
  cases hP : P.eval σ with
  | none => rw [hP] at hs; cases hs
  | some r =>
    rw [hP, Option.bind_some] at hs
    cases hp : σ.storage.pushPlace r with
    | none => rw [hp] at hs; cases hs
    | some x =>
      rw [hp, Option.bind_some, Option.some.injEq] at hs
      subst hs
      unfold Storage.pushPlace at hp
      cases hf : σ.storage.find r with
      | none => rw [hf] at hp; cases hp
      | some w =>
        rw [hf] at hp
        simp only [Option.bind_eq_bind, Option.bind_some] at hp
        split at hp
        · rename_i hb
          cases hsv : σ.storage.save r _ with
          | none => rw [hsv] at hp; cases hp
          | some st'' =>
            rw [hsv, Option.bind_some, Option.some.injEq] at hp
            subst hp
            exact ⟨r, w, _, rfl, hf, hsv, hb, rfl⟩
        · cases hp

theorem binopT_sub_one_lenU (n : Nat) (h : n + 1 < 2 ^ 256) :
    binopT .sub (p := .uint) (lenU (n + 1) h) (some (PrimTy.ofLit .uint 1 rfl)) =
      some (lenU n (by omega)) := by
  have hr : PrimTy.uint.inRange (((n + 1 : Nat) : Int) - 1) = true := by
    have : (((n + 1 : Nat) : Int) - 1) = (n : Int) := by omega
    rw [this]; exact lenU_inRange (by omega)
  simp only [binopT, BinOp.shortT, Option.bind_some, BinOp.evalT, BinOp.evalNum, BinOp.arithInt,
    lenU, PrimTy.ofLit, PrimTy.ofInt?, PrimTy.ofValue?, hr, dite_true, Option.some.injEq,
    Subtype.mk.injEq]
  exact Subtype.ext (by show ((n + 1 : Nat) : Int) - 1 = (n : Int); omega)

theorem Storage.atT_dyn {E : Ty} {st : Storage C} {r : SRef C (.ref (.array E))} {m : Nat}
    {e : SVec E m} {sh : SList E} {hm : m < 2 ^ 256} (hf : st.find r = some (.array e sh hm))
    (i : PrimTy.uint.Denote) (hi : i.1 < m) :
    st.atT (.arr .dyn) r i = some (r.index (.arr .dyn) i.1) := by
  have h0 : 0 ≤ i.1 := by
    have := i.2
    simp only [PrimTy.inRange, decide_eq_true_eq] at this
    exact this.1
  have hk : PrimTy.key (p := PrimTy.uint.keyTy) i = i.1 := rfl
  simp only [Storage.atT, Storage.checkIndex, hf, Option.bind_eq_bind, Option.bind_some,
    Storage.inBounds, SVal.view_array, hk]
  rw [if_pos ⟨h0, by omega⟩]
  rfl

/-- **The last slot after the push is the slot past the end before it.** -/
theorem lastSlotS_evalT {σ x : State C Γ} {E : Ty} {P : Tm C Γ (.path (.ref (.array E)))}
    (hP : P.stablePathSM = true) {st' : Storage C}
    (hs : (Tm.app2 .extend (.app0 .storage) P : Tm C Γ .st).eval σ = some st')
    (hx : x.glob = { σ.glob with storage := st' })
    (hl : ∀ {t : LTy} (i : Idx Γ t), x.getV i = σ.getV i) :
    (lastSlotS P).eval x = (Tm.app1 .next P).eval σ := by
  obtain ⟨r, w, nv, hr, hw, hsv, hb, hnv⟩ := extend_typed hs
  -- the path names the same location after the write (on the erasure)
  have hle : ∀ {t : LTy} (i : Idx Γ t), x.getE i = σ.getE i := fun i => by
    rw [← State.getV_erase, ← State.getV_erase, hl i]
  have hsvE := Storage.saveStorage_erase (σ := σ.globE) (st := σ.storage) rfl r nv
  rw [hsv] at hsvE
  have hxE : x.globE = Storage.into σ.globE st' := by
    rw [← State.glob_globE, hx]; rfl
  have hPE : P.evalE σ = .ok (r.root, r.path.erase) := by rw [Tm.evalE_def, hr]; rfl
  have hPx := stable_evalE hsvE hxE hle P hP hPE (fun _ => ⟨[], by simp only [List.append_nil]⟩)
  have hPx' : P.eval x = some r := by
    have := Tm.eval_path_of_evalE (p := P) (q := P) (τ := x) (τ' := σ)
      (fun v => by rw [hPx, hPE])
    rw [this, hr]
  have hxs : x.storage = st' := congrArg State.storage hx
  -- the array after the push: one element more
  have hfind := Storage.find_save_self hsv
  rw [← hxs] at hfind
  -- the right-hand side: the slot past the end
  have hrhs : (Tm.app1 .next P).eval σ =
      some (r.index (.arr .dyn) ((SVal.view w : ArrView E).n : Int)) := by
    rw [CloseS.eval_next, hr, Option.bind_some]
    simp only [Storage.nextT, hw, Option.map_some]
  rw [hrhs]
  simp only [lastSlotS, CloseS.eval_at, CloseS.eval_binop, CloseS.eval_len, CloseS.eval_storage,
    hPx', Option.bind_some, Storage.len, hfind, SVal.view_array]
  subst hnv
  have hn1 : (w.view.elems.toList ++ [(pushSlot E w.view.shadow.toList).fst]).length =
      w.view.n + 1 := by
    rw [List.length_append, SVec.length_toList, List.length_singleton]
  have hlen : ∀ hL, lenU (w.view.elems.toList ++ [(pushSlot E w.view.shadow.toList).fst]).length hL =
      lenU (w.view.n + 1) hb := fun hL => Subtype.ext (by
    show (((w.view.elems.toList ++ [(pushSlot E w.view.shadow.toList).fst]).length : Nat) : Int) =
      ((w.view.n + 1 : Nat) : Int)
    rw [hn1])
  have hone : (Tm.one (C := C) (Γ := Γ) PrimTy.uint rfl).eval x = some (PrimTy.ofLit .uint 1 rfl) :=
    rfl
  simp only [Option.bind_eq_bind, Option.bind_some, SVal.view_array, hlen, hone,
    binopT_sub_one_lenU]
  rw [Storage.atT_dyn hfind _ (by show ((w.view.n : Nat) : Int) <
    ((w.view.elems.toList ++ [(pushSlot E w.view.shadow.toList).fst]).length : Int); omega)]
  rfl

theorem extendOf?_some {S : Tm C Γ .st} {E : Ty} {P : Tm C Γ (.path (.ref (.array E)))}
    (h : S.extendOf? = some ⟨E, P⟩) : S = .app2 .extend (.app0 .storage) P := by
  cases S with
  | app2 o st P₀ =>
    cases o <;> simp only [Tm.extendOf?, Op2.extendArg?, reduceCtorEq] at h
    split at h
    · rename_i hst
      obtain rfl := isStorageS_st hst
      simp only [Option.some.injEq, Sigma.mk.injEq, Ty.ref.injEq, RefTy.array.injEq] at h
      obtain ⟨rfl, h⟩ := h
      cases h
      rfl
    · cases h
  | _ => simp only [Tm.extendOf?, reduceCtorEq] at h

theorem pushOf?_some {Δ : Ctx} {V : Upd C Γ Δ} {E : Ty} {P : Tm C Γ (.path (.ref (.array E)))}
    {Q : Tm C Δ (.path (.ref (.array E)))} (h : V.pushOf? = some ⟨E, P, Q⟩) :
    ∃ hΔ : Γ = Δ, V = hΔ ▸ Upd.nil.snoc (.storage (.app2 .extend (.app0 .storage) P)) ∧
      Q = hΔ ▸ P := by
  unfold Upd.pushOf? at h
  split at h
  · rename_i S
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨⟨E', P'⟩, hS, he⟩ := h
    simp only [Sigma.mk.injEq] at he
    obtain ⟨rfl, he⟩ := he
    simp only [heq_eq_eq, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    obtain rfl := extendOf?_some hS
    exact ⟨rfl, rfl, rfl⟩
  · cases h

theorem nextOf?_some {T : Ty} {n : Tm C Γ (.path T)} {P : Tm C Γ (.path (.ref (.array T)))}
    (h : n.nextOf? = some P) : n = .app1 .next P := by
  cases n with
  | app1 o P₀ =>
    cases o <;> simp only [Tm.nextOf?, Op1.nextArg?, reduceCtorEq, Option.some.injEq] at h
    subst h
    rfl
  | _ => simp only [Tm.nextOf?, reduceCtorEq] at h

/-- The alias a push binds reads the slot past the end wherever the push is
out of gas: the parallel update is out of gas where the push alone is. -/
theorem push_alias_exh {R : RefTy} {P : Tm C Γ (.path (.ref (.array (.ref R))))}
    {i : Idx Γ (.alias R)} (σ : State C Γ)
    (hx : (Upd.nil.snoc (.storage (.app2 .extend (.app0 .storage) P))).exh σ = true) :
    ((Upd.nil.snoc (.storage (.app2 .extend (.app0 .storage) P))).snoc
      (.local i (.path (.app1 .next P)))).exh σ = true := by
  simp only [Upd.exh, Upd.exhAny, Upd.exhOk, Bool.false_or, Bool.true_and, Bool.and_eq_true,
    Bool.or_eq_true] at hx ⊢
  refine ⟨.inl hx.1, hx.2, ?_⟩
  have he : (Tm.app2 Op2.extend (Tm.app0 Op0.storage) P).exhB σ = true := hx.1
  simp only [Tm.exhB, Bool.or_eq_true, Bool.and_eq_true] at he
  rcases he with he | ⟨-, ⟨h₁, -⟩ | ⟨h₁, -⟩⟩
  · left
    show ((Rhs.path (Tm.app1 .next P)).eval σ).isSome = true
    rw [Rhs.eval_eq_evalM]
    show (((Tm.app1 .next P).eval σ).bind fun r => some (some r)).isSome = true
    rw [CloseS.eval_next]
    change Op2.exhB .extend (some σ.storage) (P.eval σ) = true at he
    cases hP : P.eval σ with
    | none => rw [hP] at he; cases he
    | some r =>
      rw [hP] at he
      have hf : σ.storage.full r = true := he
      unfold Storage.full at hf
      cases hw : σ.storage.find r with
      | none => rw [hw] at hf; cases hf
      | some w => simp only [Option.bind_some, Storage.nextT, hw, Option.map_some,
          Option.isSome_some]
  · cases h₁
  · right
    show (Tm.app1 .next P).exhB σ = true
    simp only [Tm.exhB, Bool.and_eq_true]
    exact ⟨by rw [CloseS.eval_next, Tm.eval_of_exhB σ P h₁]; rfl, h₁⟩

/-- `pushSplit`'s soundness on the update it splits: a state the parallel
update lands on, its alias set back to what it held before, is a state the
push alone lands on, and the alias's own update then lands on the first. -/
theorem holds_push_alias {m : Modality} {R : RefTy} {P : Tm C Γ (.path (.ref (.array (.ref R))))}
    {i : Idx Γ (.alias R)} {φ : Fml C Γ} (hP : P.stablePathSM = true) (σ : State C Γ)
    (hψ : holds σ (.upd m (Upd.nil.snoc (.storage (.app2 .extend (.app0 .storage) P)))
      (.upd m (Upd.nil.snoc (.local i (.path (lastSlotS P)))) φ))) :
    holds σ (.upd m ((Upd.nil.snoc (.storage (.app2 .extend (.app0 .storage) P))).snoc
      (.local i (.path (.app1 .next P)))) φ) := by
  have hψ' : Upd.afterT m σ (Upd.nil.snoc (.storage (.app2 .extend (.app0 .storage) P)))
      (holds · (.upd m (Upd.nil.snoc (.local i (.path (lastSlotS P)))) φ)) := hψ
  show Upd.afterT m σ _ (holds · φ)
  rw [Upd.afterT_applyV] at hψ' ⊢
  simp only [CloseS.applyV_snoc, CloseS.applyV_nil, Option.bind_some, CloseS.elem_storage,
    CloseS.glob_storageE, CloseS.elem_local, CloseS.rhs_path] at hψ' ⊢
  cases hS : (Tm.app2 .extend (.app0 .storage) P : Tm C Γ .st).eval σ with
  | none =>
    simp only [hS, Option.map_none, Option.bind_none] at hψ' ⊢
    exact hψ'.imp_right (push_alias_exh σ)
  | some st' =>
    obtain ⟨r, w, nv, hr, hw, -, -, -⟩ := extend_typed hS
    have hv : (Tm.app1 .next P).eval σ =
        some (r.index (.arr .dyn) ((SVal.view w : ArrView (.ref R)).n : Int)) := by
      rw [CloseS.eval_next, hr, Option.bind_some]
      simp only [Storage.nextT, hw, Option.map_some]
    simp only [hS, hv, Option.map_some, Option.bind_some] at hψ' ⊢
    intro σ'' hg hl
    -- the state the push alone lands on: `σ''` with the alias as it was
    let σ' : State C Γ := σ''.setLocal i
      (show (LTy.alias R).TDenote C σ''.H from (TEnv.get i σ.env : Option (SRef C (.ref R))))
    have hg' : σ'.glob = { σ.glob with storage := st' } := hg
    have hl' : ∀ {t : LTy} (j : Idx Γ t), σ'.getV j = σ.locV t j := by
      intro t j
      by_cases h : i.toNat = j.toNat
      · obtain rfl := Idx.ty_eq_of_toNat h
        obtain rfl := Idx.toNat_inj i j h
        exact (State.getV_setLocal_same σ'' i _).trans rfl
      · rw [State.getV_setLocal_ne σ'' i j h, hl j, LocsV.set_ne _ _ _ h]
    have h₂ := hψ' σ' hg' hl'
    have h₂' : Upd.afterT m σ' (Upd.nil.snoc (.local i (.path (lastSlotS P)))) (holds · φ) := h₂
    rw [Upd.afterT_applyV] at h₂'
    have hlast := lastSlotS_evalT hP hS hg' (fun j => hl' j)
    simp only [CloseS.applyV_snoc, CloseS.applyV_nil, Option.bind_some, CloseS.elem_local,
      CloseS.rhs_path, hlast, hv, Option.map_some] at h₂'
    refine h₂' σ'' rfl (fun j => ?_)
    rw [hl j]
    by_cases h : i.toNat = j.toNat
    · obtain rfl := Idx.ty_eq_of_toNat h
      obtain rfl := Idx.toNat_inj i j h
      rw [LocsV.set_same, LocsV.set_same]
    · rw [LocsV.set_ne _ _ _ h, LocsV.set_ne _ _ _ h]
      exact (hl' j).symm

/-- **The push, then its alias, give the parallel update**: a state the
first leaves in reads the alias at the last slot where the second read it
past the end before the push (`lastSlotS_evalT`); the typed state between
the two is the one the parallel update ends in, its alias as before. -/
theorem holds_pushSplit {m : Modality} {Δ : Ctx} {U : Upd C Γ Δ} {φ : Fml C Δ} {ψ : Fml C Γ}
    (h : U.pushSplit m φ = some ψ) (σ : State C Γ) (hψ : holds σ ψ) : holds σ (.upd m U φ) := by
  unfold Upd.pushSplit at h
  split at h
  · rename_i V t i r
    split at h
    · rename_i E P Q R P' mk hV hr
      split at h
      · rename_i hE
        subst hE
        cases hb : (P.stablePathS && P.beqR P')
        · simp only [hb, cond_false, reduceCtorEq] at h
        simp only [hb, cond_true, Option.some.injEq] at h
        subst h
        simp only [Bool.and_eq_true] at hb
        obtain ⟨hs, hbeq⟩ := hb
        cases Tm.eq_of_beqR hbeq
        obtain ⟨rfl, rfl, rfl⟩ := pushOf?_some hV
        cases r with
        | path n =>
          simp only [Rhs.pushAlias?, Option.map_eq_some_iff, Sigma.mk.injEq] at hr
          obtain ⟨P₀, hn, he⟩ := hr
          obtain ⟨hR, he⟩ := he
          cases hR
          simp only [heq_eq_eq, Prod.mk.injEq] at he
          obtain ⟨rfl, rfl⟩ := he
          obtain rfl := nextOf?_some hn
          exact holds_push_alias ((Tm.stablePathS_eq_stablePathSM _).symm.trans hs) σ hψ
        | _ => simp only [Rhs.pushAlias?, reduceCtorEq] at hr
      · cases h
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
    (h : holds σ (.upd m U φ)) : holds σ (.upd m U ψ) :=
  Upd.afterT_imp h hφ

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

/-- **The closer's bounds on a wrapped leaf**, by
position, which `sol_prove?` asks before it tries a step that reduces the
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
