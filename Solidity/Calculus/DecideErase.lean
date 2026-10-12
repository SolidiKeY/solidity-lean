import Solidity.Calculus.DecideScoped
import Solidity.Calculus.CloseScoped

/-!
# The typed reading, erased: what the decision procedure is related to

`sol_decide`'s language (`LTerm`, `LStor`, `LMem`, `LFml`,
`Calculus/DecideLang.lean`) keeps KeY's untyped values: a word is a
`Semantics.Value`, a storage a tree of `Semantics.SVal`, a memory a
`Semantics.State`'s heap.  That is what makes it a decision procedure: the
elimination of reads of writes (`LFml.elim`) and the realizability of the
reads (`Calculus/DecideComplete.lean`) range over every untyped storage, a
Presburger and array fragment over `Value`, with no type to carry through a
case split.  So the reduction is related to the typed state through one
bridge, the erasure of the typed reading:

* `Tm.evalE τ t` is `t.eval τ`, the typed reading, erased
  (`toRes (Srt.erase τ.glob s)`): a value by `PrimTy.erase`, a path by
  `SRef.erase`, a storage or a memory as the erased global part with it, a
  revert where the typed reading is `none`;
* `Upd.applyVE τ U` is `U.applyV τ`, erased (`Upd.applyVE_eq`), computed
  element by element from `Tm.evalE` as the reduction's proofs read it;
* `RelT σ ρ τ` (`Calculus/DecideRel.lean`) relates the reduction's state to
  the typed state's erased global part and locals (`State.globE`,
  `State.loc`).

The equations below restate a symbol's typed reading on the erasure, in
the untyped interpreter's operations the reduction's semantics is written
in (`State.findStorage`, `readAddr`, …), through the erasure lemmas of
`Semantics/StorageErase.lean` and `Semantics/HeapErase.lean`.  They agree
on the values returned (`Sim`): the untyped interpreter halts with other
kinds than a revert.  Three are exact only under a premise, which the
reduction supplies: a push below the bound of `2^256 - 1` elements (the
typed one is out of gas there, `Storage.full`; the reduction guards a push
with the bound, `Tm.pushBoundS`), and a memory read, length or copy
through an identity of the type the term says (`IdOk`: the untyped heap
does not keep an object's type, so a read through an identity of another
type can return where the typed one does not; the reduction's identities
are the typed state's, `IdOKS`).
-/

namespace Solidity

open Semantics SemanticsProperties Decide

variable {C : Contract}

theorem toRes_some {α β : Type} (f : α → β) (a : α) : toRes f (some a) = .ok (f a) := rfl
theorem toRes_none {α β : Type} (f : α → β) : toRes f (none : Option α) = .error .revert := rfl

/-! ## The erased sorts -/

/-- A sort's value as the decision procedure reads it: KeY's untyped one,
a storage or a memory as the global part with it. -/
@[reducible] def Srt.Ev : Srt → Type
  | .val _ => Value
  | .path _ => Name × List Seg
  | .st => Semantics.State
  | .sv _ => Semantics.SVal
  | .ident _ => Nat
  | .addr _ => Addr
  | .mem => Semantics.State
  | .mv _ => Semantics.MVal
  | .sts _ => Semantics.State
  | .spath _ _ => Name × List Seg

/-- The identity `id` names an `R` in `H`: where a typed memory read is
exact. -/
def IdOk (H : HTy) (R : RefTy) (id : Nat) : Prop := H[id]? = some R

theorem HRef.ofId?_of_ok {H : HTy} {R : RefTy} {id : Nat} (h : IdOk H R id) :
    HRef.ofId? H R id = some ⟨id, h⟩ := dif_pos h

theorem IdOk.of_prefix {H H' : HTy} (e : H <+: H') {R : RefTy} {id : Nat} (h : IdOk H R id) :
    IdOk H' R id := by
  obtain ⟨l, rfl⟩ := e
  unfold IdOk at h ⊢
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.1 h).1]
  exact h

theorem IdOk.of_href {H : HTy} {R : RefTy} (r : HRef H R) : IdOk H R r.id := r.get?

/-- The untyped address. -/
def MAddrT.erase {T : Ty} : MAddrT T → Addr
  | @MAddrT.field _ f _ id _ => .memoryField id f
  | .index id _ i => .memoryIndex id i

/-- Its identity names the object it addresses in `H`. -/
def MAddrT.Ok (H : HTy) {T : Ty} : MAddrT T → Prop
  | @MAddrT.field s _ _ id _ => IdOk H (.struct s) id
  | @MAddrT.index R _ id _ _ => IdOk H R id

theorem MAddrT.Ok.of_prefix {H H' : HTy} (e : H <+: H') {T : Ty} :
    {a : MAddrT T} → a.Ok H → a.Ok H'
  | .field .., h => IdOk.of_prefix e h
  | .index .., h => IdOk.of_prefix e h

/-- The untyped memory value. -/
def MvT.erase : (T : Ty) → MvT T → Semantics.MVal
  | .prim p, v => .prim (PrimTy.erase (p := p) v)
  | .ref _, id => .ref id

/-- An identity written names an `R`. -/
def MvT.Ok (H : HTy) : (T : Ty) → MvT T → Prop
  | .prim _, _ => True
  | .ref R, id => IdOk H R id

theorem MvT.Ok.of_prefix {H H' : HTy} (e : H <+: H') : {T : Ty} → {v : MvT T} →
    MvT.Ok H T v → MvT.Ok H' T v
  | .prim _, _, _ => trivial
  | .ref _, _, h => IdOk.of_prefix e h

/-- A typed value of the sort `s`, erased, over the global part `g`: a
storage or a memory as `g`'s erasure with it. -/
def Srt.erase (g : State C []) : (s : Srt) → s.Den C g.H → s.Ev
  | .val _, v => PrimTy.erase v
  | .path _, r => r.erase
  | .st, w => Storage.into g.globE w
  | .sv _, v => v.erase
  | .ident _, n => n
  | .addr _, a => a.erase
  | .mem, m => Heap.into g.globE m.heap
  | .mv T, v => MvT.erase T v
  | .sts _, w => { g.globE with storage := Storage.erase w }
  | .spath _ _, r => r.erase

/-- **The typed reading, erased**: what a term reads in `τ`, as the
decision procedure's untyped values; a revert where it reads `none`. -/
def Tm.evalE {Γ : Ctx} (τ : State C Γ) {s : Srt} (t : Tm C Γ s) : Res s.Ev :=
  toRes (Srt.erase τ.glob s) (t.eval τ)

/-- A local's value erased (`LTy.TDenote.erase`'s, from `LTy.VDen`). -/
def LTy.VDen.erase : (t : LTy) → t.VDen C → t.Denote C
  | .val _, v => PrimTy.erase v
  | .alias _, a => a.map SRef.erase
  | .mem _, i => i
  | .old, w => Storage.erase w
  | .oldNet, l => l

/-- What a local is set to, erased. -/
def Rhs.evalE {Γ : Ctx} (σ₀ : State C Γ) {t : LTy} (r : Rhs C Γ t) : Res (t.Denote C) :=
  toRes (LTy.VDen.erase t) (r.eval σ₀)

/-- The locals, erased. -/
def LocsV.erase {Γ : Ctx} (ℓ : LocsV C Γ) : Locs C Γ := fun t i => LTy.VDen.erase t (ℓ t i)

/-- A path is its segments. -/
theorem Path.erase_injective {T U : Ty} (p : Path T U) :
    ∀ q : Path T U, p.erase = q.erase → p = q := by
  induction p
  case nil =>
    intro q hq
    cases q <;> simp only [Path.erase, List.nil_eq, reduceCtorEq] at hq ⊢
  case field hl p ih =>
    intro q hq
    cases q with
    | nil => simp only [Path.erase, reduceCtorEq] at hq
    | field hl' q =>
      simp only [Path.erase, List.cons.injEq, Semantics.Seg.field.injEq] at hq
      obtain ⟨rfl, hq⟩ := hq
      obtain rfl := Option.some.inj (hl.symm.trans hl')
      rw [ih q hq]
  all_goals
    rename_i i p ih
    intro q hq
    cases q <;> simp only [Path.erase, List.cons.injEq, Semantics.Seg.at.injEq, reduceCtorEq] at hq
    obtain ⟨rfl, hq⟩ := hq
    rw [ih _ hq]

/-- A storage reference is its root and segments. -/
theorem SRef.erase_injective {U : Ty} {r r' : SRef C U} (h : r.erase = r'.erase) : r = r' := by
  obtain ⟨n, hn, p⟩ := r
  obtain ⟨n', hn', p'⟩ := r'
  simp only [SRef.erase, Prod.mk.injEq] at h
  obtain ⟨rfl, hp⟩ := h
  obtain rfl := Option.some.inj (hn.symm.trans hn')
  rw [Path.erase_injective p p' hp]

/-- Two paths read alike erased read alike typed. -/
theorem Tm.eval_path_of_evalE {Γ Γ' : Ctx} {T : Ty} {τ : State C Γ} {τ' : State C Γ'}
    {p : Tm C Γ (.path T)} {q : Tm C Γ' (.path T)} (h : ∀ v, p.evalE τ = .ok v ↔ q.evalE τ' = .ok v) :
    p.eval τ = q.eval τ' := by
  simp only [Tm.evalE] at h
  cases hp : p.eval τ with
  | none =>
    cases hq : q.eval τ' with
    | none => rfl
    | some r =>
      have := (h r.erase).2 (by rw [hq]; rfl)
      rw [hp] at this; cases this
  | some r =>
    have := (h r.erase).1 (by rw [hp]; rfl)
    cases hq : q.eval τ' with
    | none => rw [hq] at this; cases this
    | some r' =>
      rw [hq] at this
      simp only [toRes, Except.ok.injEq] at this
      rw [SRef.erase_injective this.symm]

/-! ## The erased locals -/

namespace Locs

/-- A local set. -/
def set {Δ : Ctx} (ℓ : Locs C Δ) {t : LTy} (i : Idx Δ t) (v : t.Denote C) : Locs C Δ :=
  fun _ j => if h : i.toNat = j.toNat then Idx.ty_eq_of_toNat h ▸ v else ℓ _ j

/-- A suffix popped. -/
def drop {Δ Δ' : Ctx} (h : Ext Δ' Δ) (ℓ : Locs C Δ) : Locs C Δ' := fun _ j => ℓ _ (j.ext h)

/-- A frame thinned. -/
def thin {Δ Δ' : Ctx} (h : Thin Δ' Δ) (ℓ : Locs C Δ) : Locs C Δ' := fun _ j => ℓ _ (j.wk h)

theorem set_same {Δ : Ctx} (ℓ : Locs C Δ) {t : LTy} (i : Idx Δ t) (v : t.Denote C) :
    ℓ.set i v t i = v := by
  unfold Locs.set
  rw [dif_pos rfl]

theorem set_ne {Δ : Ctx} (ℓ : Locs C Δ) {t u : LTy} (i : Idx Δ t) (j : Idx Δ u)
    (h : i.toNat ≠ j.toNat) (v : t.Denote C) : ℓ.set i v u j = ℓ u j := by
  unfold Locs.set
  rw [dif_neg h]

end Locs

theorem LocsV.erase_set {Δ : Ctx} (ℓ : LocsV C Δ) {t : LTy} (i : Idx Δ t) (v : t.VDen C) :
    (ℓ.set i v).erase = ℓ.erase.set i (LTy.VDen.erase t v) := by
  funext u j
  by_cases h : i.toNat = j.toNat
  · obtain rfl := Idx.ty_eq_of_toNat h
    obtain rfl := Idx.toNat_inj i j h
    show LTy.VDen.erase t (ℓ.set i v t i) = _
    rw [LocsV.set_same, Locs.set_same]
  · show LTy.VDen.erase u (ℓ.set i v u j) = _
    rw [LocsV.set_ne _ _ _ h, Locs.set_ne _ _ _ h]
    rfl

theorem LocsV.erase_push {Δ : Ctx} {t : LTy} (ℓ : LocsV C Δ) (v : t.VDen C) :
    (ℓ.push v).erase = ℓ.erase.push (LTy.VDen.erase t v) := by
  funext u j
  cases j <;> rfl

theorem LocsV.erase_drop {Δ Δ' : Ctx} (h : Ext Δ' Δ) (ℓ : LocsV C Δ) :
    (ℓ.drop h).erase = ℓ.erase.drop h := rfl

theorem LocsV.erase_thin {Δ Δ' : Ctx} (h : Thin Δ' Δ) (ℓ : LocsV C Δ) :
    (ℓ.thin h).erase = ℓ.erase.thin h := rfl

theorem State.locV_erase {Γ : Ctx} (τ : State C Γ) : τ.locV.erase = τ.loc := by
  funext t i
  show LTy.VDen.erase t (LTy.VDen.ofT t (TEnv.get i τ.env)) = LTy.TDenote.erase t (TEnv.get i τ.env)
  cases t <;> rfl

theorem State.getV_erase {Γ : Ctx} (τ : State C Γ) {t : LTy} (i : Idx Γ t) :
    LTy.VDen.erase t (τ.getV i) = τ.getE i := by
  cases t <;> rfl

theorem State.glob_globE {Γ : Ctx} (τ : State C Γ) : τ.glob.globE = τ.globE := rfl


/-! ## The erasure lemmas the terms need (W9.8.1's bridge) -/

/-- A memory read on the erasure, its identity typed. -/
theorem Grown.readT_erase {H : HTy} {T : Ty} (m : Grown H (fun _ => Unit)) {σ : Semantics.State}
    (hh : σ.heap = m.heap.erase) (ad : MAddrT T) (hok : ad.Ok m.H') :
    readAddr σ ad.erase = toRes (MVal.erase T) (m.readT ad) := by
  cases ad with
  | field id h =>
    simp only [MAddrT.Ok] at hok
    simp only [Grown.readT, MAddrT.resolve_eq_resolveM, MAddrT.resolveM, HRef.ofId?_of_ok hok,
      Option.map_some, Option.bind_eq_bind, Option.bind_some, Heap.readAddr, readAddr,
      MAddrT.erase]
    exact Heap.readField_erase hh ⟨id, hok⟩ h
  | index id a i =>
    simp only [MAddrT.Ok] at hok
    simp only [Grown.readT, MAddrT.resolve_eq_resolveM, MAddrT.resolveM, HRef.ofId?_of_ok hok,
      Option.map_some, Option.bind_eq_bind, Option.bind_some, Heap.readAddr, readAddr,
      MAddrT.erase]
    exact Heap.readIndex_erase hh ⟨id, hok⟩ a i

theorem MvT.toMVal_ok {H : HTy} : (T : Ty) → (v : MvT T) → MvT.Ok H T v →
    ∃ v' : MVal H T, MvT.toMVal H T v = some v' ∧ MvT.erase T v = MVal.erase T v'
  | .prim _, v, _ => ⟨v, rfl, rfl⟩
  | .ref _, v, hv => ⟨⟨v, hv⟩, HRef.ofId?_of_ok hv, rfl⟩

/-- A memory write on the erasure, its identities typed. -/
theorem Grown.writeT_erase {H : HTy} {T : Ty} (m : Grown H (fun _ => Unit)) (σ : Semantics.State)
    (ad : MAddrT T) (v : MvT T) (hok : ad.Ok m.H') (hv : MvT.Ok m.H' T v) :
    writeAddr (Heap.into σ m.heap) (MvT.erase T v) ad.erase =
      toRes (fun m' : Grown H (fun _ => Unit) => Heap.into σ m'.heap) (m.writeT ad v) := by
  obtain ⟨v', htv, hev⟩ := MvT.toMVal_ok T v hv
  rw [hev]
  cases ad with
  | field id h =>
    simp only [MAddrT.Ok] at hok
    simp only [Grown.writeT, MAddrT.resolve_eq_resolveM, MAddrT.resolveM, HRef.ofId?_of_ok hok,
      Option.map_some, Option.bind_eq_bind, Option.bind_some, htv, Heap.writeAddr, writeAddr,
      MAddrT.erase]
    rw [Heap.memWriteField_erase (σ := Heap.into σ m.heap) rfl ⟨id, hok⟩ h v']
    rfl
  | index id a i =>
    simp only [MAddrT.Ok] at hok
    simp only [Grown.writeT, MAddrT.resolve_eq_resolveM, MAddrT.resolveM, HRef.ofId?_of_ok hok,
      Option.map_some, Option.bind_eq_bind, Option.bind_some, htv, Heap.writeAddr, writeAddr,
      MAddrT.erase]
    rw [Heap.memWriteIndex_erase (σ := Heap.into σ m.heap) rfl ⟨id, hok⟩ a i v']
    cases m.heap.setIndex ⟨id, hok⟩ a i v' <;> rfl

theorem PrimTy.asInt_erase_keyTy : (k : PrimTy) → (i : k.keyTy.Denote) →
    Value.asInt (PrimTy.erase i) = .ok (PrimTy.key i)
  | .bool, _ | .uint, _ | .int, _ => rfl

/-- `p[i]` checked on the erasure. -/
theorem Storage.atT_erase {σ : Semantics.State} {st : Storage C} (hs : σ.storage = st.erase)
    {R : RefTy} {k : PrimTy} {V : Ty} (it : IndexTy R k V) (r : SRef C (.ref R))
    (i : k.keyTy.Denote) :
    (σ.checkIndex r.root r.path.erase (PrimTy.key i) >>= fun _ =>
        .ok (r.root, r.path.erase ++ [Seg.at (PrimTy.key i)]) : Res (Name × List Seg)) =
      toRes SRef.erase (st.atT it r i) := by
  rw [Storage.checkIndex_erase hs r it]
  unfold Storage.atT
  cases st.checkIndex r it (PrimTy.key i) with
  | none => rfl
  | some u =>
    simp only [toRes, bind, Except.bind, Option.bind_some, SRef.erase,
      SRef.index, SRef.append, Path.erase_append, Path.erase_index]

theorem binopT_none_sim (op : BinOp) {p : PrimTy} (a : p.Denote) :
    Sim (toRes PrimTy.erase (binopT op a none)) (evalBinop op p (PrimTy.erase a) (.error .revert)) := by
  intro v
  unfold binopT
  cases op <;> cases p <;> (try cases a) <;>
    simp only [BinOp.shortT, toRes, evalBinop, Option.bind_none, PrimTy.erase, bind, Except.bind,
      reduceCtorEq, ↓reduceIte, BinOp.ret, pure, Except.pure] <;> exact Iff.rfl

/-! ## Terms, erased, one constructor at a time

Each the typed equation (`CloseS.eval_*`, `Calculus/CloseScoped.lean`)
read through the erasure lemmas, in the untyped interpreter's shape the
reduction's proofs read. -/

namespace Tm

section Terms

variable {Γ : Ctx} (τ : State C Γ)

theorem evalE_def {s : Srt} (t : Tm C Γ s) : t.evalE τ = toRes (Srt.erase τ.glob s) (t.eval τ) :=
  rfl

theorem evalE_lit {p : PrimTy} (v : p.Denote) :
    (Tm.app0 (.lit v) : Tm C Γ (.val p)).evalE τ = .ok (PrimTy.erase v) := rfl
theorem evalE_env (k : EnvKey) :
    (Tm.app0 (.env k) : Tm C Γ (.val .uint)).evalE τ = .ok (.int (τ.globE.envVal k)) := by
  cases k <;> rfl
theorem evalE_pvV {p : PrimTy} (i : Idx Γ (.val p)) :
    (Tm.pvV i : Tm C Γ (.val p)).evalE τ = .ok (τ.getE i) := rfl
theorem evalE_pvP {R : RefTy} (i : Idx Γ (.alias R)) :
    (Tm.pvP i : Tm C Γ _).evalE τ = toRes id (τ.getE i) := by
  show toRes SRef.erase (TEnv.get i τ.env) = toRes id ((TEnv.get i τ.env : Option (SRef C _)).map SRef.erase)
  cases (TEnv.get i τ.env : Option (SRef C _)) <;> rfl
theorem evalE_pvS (i : Idx Γ .old) :
    (Tm.pvS i : Tm C Γ .st).evalE τ = .ok { τ.globE with storage := τ.getE i } := rfl
theorem evalE_pvI {R : RefTy} (i : Idx Γ (.mem R)) :
    (Tm.pvI i : Tm C Γ (.ident R)).evalE τ = toRes id (τ.getE i) := by
  show toRes id ((TEnv.get i τ.env : Option (HRef τ.H R)).map (·.id)) = _
  rfl
theorem evalE_root (r : Name) {T : Ty} (h : C.rootType r = some T) :
    (Tm.app0 (.root r h) : Tm C Γ (.path T)).evalE τ = .ok (r, []) := rfl
theorem evalE_storage : (Tm.app0 .storage : Tm C Γ .st).evalE τ = .ok τ.globE := rfl
theorem evalE_memory : (Tm.app0 .memory : Tm C Γ .mem).evalE τ = .ok τ.globE := rfl

theorem evalE_unop (op : UnOp) {p : PrimTy} (h : op.accepts p = true) (a : Tm C Γ (.val p)) :
    (Tm.app1 (.unop op h) a).evalE τ = a.evalE τ >>= fun x => applyUnOp op x >>= unopCheck op p := by
  simp only [evalE_def, CloseS.eval_unop]
  cases a.eval τ with
  | none => rfl
  | some x =>
    simp only [Option.bind_some, toRes, Res.ok_bind]
    exact (UnOp.evalT_erase op h x).symm

theorem evalE_binop (op : BinOp) {p : PrimTy} (h : op.accepts p = true) (a b : Tm C Γ (.val p)) :
    Sim ((Tm.app2 (.binop op h) a b).evalE τ)
      (a.evalE τ >>= fun x => evalBinop op p x (b.evalE τ)) := by
  simp only [evalE_def, CloseS.eval_binop]
  cases a.eval τ with
  | none => exact Sim.refl _
  | some x =>
    simp only [Option.bind_some, toRes, Res.ok_bind]
    cases b.eval τ with
    | none => exact binopT_none_sim op x
    | some y =>
      rw [binopT_some]
      exact Sim.of_eq (BinOp.evalT_erase op h x y).symm

theorem evalE_find {p : PrimTy} (s : Tm C Γ .st) (q : Tm C Γ (.path (.prim p))) :
    (Tm.app2 .find s q).evalE τ = s.evalE τ >>= fun τ' => q.evalE τ >>= fun rs =>
      τ'.findStorage rs.1 rs.2 >>= Semantics.SVal.asValue := by
  simp only [evalE_def, CloseS.eval_find]
  cases s.eval τ with
  | none => rfl
  | some st =>
    cases q.eval τ with
    | none => rfl
    | some r =>
      simp only [Option.bind_some, toRes_some, Res.ok_bind, Srt.erase, SRef.erase]
      rw [Storage.findStorage_erase (σ := Storage.into τ.glob.globE st) (st := st) rfl]
      cases st.find r with
      | none => rfl
      | some v =>
        cases v
        simp only [toRes, Option.bind_some, Res.ok_bind, SVal.erase_prim, SVal.view_prim]
        cases p <;> rfl

theorem evalE_sfind {T : Ty} (s : Tm C Γ .st) (q : Tm C Γ (.path T)) :
    (Tm.app2 .sfind s q).evalE τ = s.evalE τ >>= fun τ' => q.evalE τ >>= fun rs =>
      τ'.findStorage rs.1 rs.2 := by
  simp only [evalE_def, CloseS.eval_sfind]
  cases s.eval τ with
  | none => rfl
  | some st =>
    cases q.eval τ with
    | none => rfl
    | some r =>
      simp only [Option.bind_some, toRes_some, Res.ok_bind, Srt.erase, SRef.erase]
      rw [Storage.findStorage_erase (σ := Storage.into τ.glob.globE st) (st := st) rfl]
      rfl

theorem evalE_len {E : Ty} (s : Tm C Γ .st) (q : Tm C Γ (.path (.ref (.array E)))) :
    (Tm.app2 .len s q).evalE τ = s.evalE τ >>= fun τ' => q.evalE τ >>= fun rs =>
      τ'.findStorage rs.1 rs.2 >>= Close.arrLen := by
  simp only [evalE_def, CloseS.eval_len]
  cases s.eval τ with
  | none => rfl
  | some st =>
    cases q.eval τ with
    | none => rfl
    | some r =>
      simp only [Option.bind_some, toRes_some, Res.ok_bind, Srt.erase, SRef.erase]
      rw [← Close.arrayLen_eq,
        Storage.arrayLen_erase (σ := Storage.into τ.glob.globE st) (st := st) rfl]
      rfl

theorem evalE_ite {p : PrimTy} (c : Tm C Γ (.val .bool)) (a b : Tm C Γ (.val p)) :
    (Tm.app3 .ite c a b).evalE τ = c.evalE τ >>= fun cv => pickBranch cv (a.evalE τ) (b.evalE τ) := by
  simp only [evalE_def, CloseS.eval_ite]
  cases c.eval τ with
  | none => rfl
  | some cv => cases cv <;> rfl

theorem evalE_field {s f : Name} {T : Ty} (h : C.fieldType s f = some T)
    (q : Tm C Γ (.path (.ref (.struct s)))) :
    (Tm.app1 (.field h) q).evalE τ = q.evalE τ >>= fun rs => .ok (rs.1, rs.2 ++ [.field f]) := by
  simp only [evalE_def, CloseS.eval_field]
  cases q.eval τ with
  | none => rfl
  | some r =>
    simp only [Option.map_some, toRes, Res.ok_bind, Srt.erase, SRef.erase, SRef.field,
      SRef.append, Path.erase_append]
    rfl

theorem evalE_at {R : RefTy} {k : PrimTy} {V : Ty} (it : IndexTy R k V)
    (q : Tm C Γ (.path (.ref R))) (i : Tm C Γ (.val k.keyTy)) :
    (Tm.app2 (.at it) q i).evalE τ = q.evalE τ >>= fun rs => i.evalE τ >>= Value.asInt >>= fun j =>
      τ.globE.checkIndex rs.1 rs.2 j >>= fun _ => .ok (rs.1, rs.2 ++ [.at j]) := by
  simp only [evalE_def, CloseS.eval_at]
  cases q.eval τ with
  | none => rfl
  | some r =>
    cases i.eval τ with
    | none => rfl
    | some x =>
      simp only [Option.bind_some, toRes, Res.ok_bind, Srt.erase, PrimTy.asInt_erase_keyTy]
      exact (Storage.atT_erase (σ := τ.globE) (st := τ.storage) rfl it r x).symm

theorem evalE_save {T : Ty} (s : Tm C Γ .st) (q : Tm C Γ (.path T)) (v : Tm C Γ (.sv T)) :
    (Tm.app3 .save s q v).evalE τ = v.evalE τ >>= fun sv => s.evalE τ >>= fun τ' =>
      q.evalE τ >>= fun rs => τ'.writeStorage rs.1 rs.2 sv := by
  simp only [evalE_def, CloseS.eval_save]
  cases s.eval τ with
  | none => cases v.eval τ <;> rfl
  | some st =>
    cases q.eval τ with
    | none => cases v.eval τ <;> rfl
    | some r =>
      cases v.eval τ with
      | none => rfl
      | some w =>
        simp only [Option.bind_some, toRes_some, Res.ok_bind, Srt.erase, SRef.erase]
        rw [          Storage.writeStorage_erase (σ := Storage.into τ.glob.globE st) (st := st) rfl]
        rfl

theorem evalE_delAt {T : Ty} (s : Tm C Γ .st) (q : Tm C Γ (.path T)) :
    (Tm.app2 .delAt s q).evalE τ = s.evalE τ >>= fun τ' => q.evalE τ >>= fun rs =>
      τ'.findStorage rs.1 rs.2 >>= fun cur => τ'.saveStorage rs.1 rs.2 cur.defaultOf := by
  simp only [evalE_def, CloseS.eval_delAt]
  cases s.eval τ with
  | none => rfl
  | some st =>
    cases q.eval τ with
    | none => rfl
    | some r =>
      simp only [Option.bind_some, toRes_some, Res.ok_bind, Srt.erase, SRef.erase]
      have hd := Storage.delete_erase (σ := Storage.into τ.glob.globE st) (st := st) rfl r
      exact hd.symm

theorem evalE_pop (s : Tm C Γ .st) {E : Ty} (q : Tm C Γ (.path (.ref (.array E)))) :
    (Tm.app2 .pop s q).evalE τ = s.evalE τ >>= fun τ' => q.evalE τ >>= fun rs =>
      τ'.findStorage rs.1 rs.2 >>= Close.popOn τ' false rs.1 rs.2 := by
  simp only [evalE_def, CloseS.eval_pop]
  cases s.eval τ with
  | none => rfl
  | some st =>
    cases q.eval τ with
    | none => rfl
    | some r =>
      simp only [Option.bind_some, toRes_some, Res.ok_bind, Srt.erase, SRef.erase]
      rw [← Close.popAt_eq,
        Storage.popAt_erase (σ := Storage.into τ.glob.globE st) (st := st) rfl]
      rfl

theorem evalE_shrink (s : Tm C Γ .st) {E : Ty} (q : Tm C Γ (.path (.ref (.array E)))) :
    (Tm.app2 .shrink s q).evalE τ = s.evalE τ >>= fun τ' => q.evalE τ >>= fun rs =>
      τ'.findStorage rs.1 rs.2 >>= Close.popOn τ' true rs.1 rs.2 := by
  simp only [evalE_def, CloseS.eval_shrink]
  cases s.eval τ with
  | none => rfl
  | some st =>
    cases q.eval τ with
    | none => rfl
    | some r =>
      simp only [Option.bind_some, toRes_some, Res.ok_bind, Srt.erase, SRef.erase]
      rw [← Close.popAt_eq,
        Storage.popAt_erase (σ := Storage.into τ.glob.globE st) (st := st) rfl]
      rfl

/-- A push below the bound: the typed one is out of gas at `2^256 - 1`
elements (`Storage.full`). -/
def PushRoom (s : Tm C Γ .st) {E : Ty} (q : Tm C Γ (.path (.ref (.array E)))) : Prop :=
  ∀ st r, s.eval τ = some st → q.eval τ = some r → st.full r = false

theorem evalE_pushSlot (s : Tm C Γ .st) {E : Ty} (q : Tm C Γ (.path (.ref (.array E))))
    (hr : PushRoom τ s q) :
    (Tm.app2 .pushSlot s q).evalE τ = s.evalE τ >>= fun τ' => q.evalE τ >>= fun rs =>
      τ'.findStorage rs.1 rs.2 >>= Close.pushOn τ' E rs.1 rs.2 pure := by
  simp only [evalE_def, CloseS.eval_pushSlot]
  cases hs : s.eval τ with
  | none => rfl
  | some st =>
    cases hq : q.eval τ with
    | none => rfl
    | some r =>
      simp only [Option.bind_some, toRes_some, Res.ok_bind, Srt.erase, SRef.erase]
      rw [← Close.pushAt_eq,
        Storage.pushAt_erase (σ := Storage.into τ.glob.globE st) (st := st) rfl r pure some
          (fun _ => rfl) (.inl (hr st r hs hq))]
      rfl

theorem evalE_extend (s : Tm C Γ .st) {E : Ty} (q : Tm C Γ (.path (.ref (.array E))))
    (hr : PushRoom τ s q) :
    (Tm.app2 .extend s q).evalE τ = s.evalE τ >>= fun τ' => q.evalE τ >>= fun rs =>
      τ'.findStorage rs.1 rs.2 >>= Close.pushOn τ' E rs.1 rs.2 pure := by
  simp only [evalE_def, CloseS.eval_extend]
  cases hs : s.eval τ with
  | none => rfl
  | some st =>
    cases hq : q.eval τ with
    | none => rfl
    | some r =>
      simp only [Option.bind_some, toRes_some, Res.ok_bind, Srt.erase, SRef.erase]
      have he := Storage.pushAt_erase (σ := Storage.into τ.glob.globE st) (st := st) rfl r pure
        some (fun _ => rfl) (.inl (hr st r hs hq))
      have hp := Storage.pushPlaceAt_erase (σ := Storage.into τ.glob.globE st) (st := st) rfl r
        (hr st r hs hq)
      rw [← Close.pushAt_eq, he]
      have hpp : (st.pushPlace r).map (·.1) = st.push r some := by
        unfold Storage.pushPlace Storage.push
        cases st.find r with
        | none => rfl
        | some v =>
          simp only [Option.bind_eq_bind, Option.bind_some]
          split
          · cases st.save r _ <;> rfl
          · rfl
      rw [← hpp]
      cases st.pushPlace r <;> rfl

theorem evalE_push (s : Tm C Γ .st) {E : Ty} (q : Tm C Γ (.path (.ref (.array E))))
    (v : Tm C Γ (.sv E)) (hr : PushRoom τ s q) :
    (Tm.app3 .push s q v).evalE τ = s.evalE τ >>= fun τ' => q.evalE τ >>= fun rs =>
      τ'.findStorage rs.1 rs.2 >>=
        Close.pushOn τ' .uint rs.1 rs.2 (fun _ => v.evalE τ >>= fun sv => pure sv.strip) := by
  simp only [evalE_def, CloseS.eval_push]
  cases hs : s.eval τ with
  | none => rfl
  | some st =>
    cases hq : q.eval τ with
    | none => rfl
    | some r =>
      simp only [Option.bind_some, toRes_some, Res.ok_bind, Srt.erase, SRef.erase]
      rw [← Close.pushAt_eq,
        pushAt_const _ .uint E,
        Storage.pushAt_erase (σ := Storage.into τ.glob.globE st) (st := st) rfl r _
          (fun _ => (v.eval τ).map SVal.strip)
          (fun _ => by cases v.eval τ <;> simp only [toRes, Option.map_some, Option.map_none,
            SVal.strip_erase, pure, Except.pure, Res.ok_bind, Res.error_bind] <;> rfl)
          (.inl (hr st r hs hq))]
      rfl

theorem evalE_sval {p : PrimTy} (t : Tm C Γ (.val p)) :
    (Tm.app1 .sval t).evalE τ = t.evalE τ >>= fun x => .ok x.toSVal := by
  simp only [evalE_def, CloseS.eval_sval]
  cases t.eval τ with
  | none => rfl
  | some x => simp only [Option.map_some, toRes, Res.ok_bind, Srt.erase, Value.toSVal_erase]

theorem evalE_newArr {R : RefTy} (h : R.newArrOk = true) (n : Tm C Γ (.val .uint))
    (sv : Semantics.SVal) : (Tm.app1 (.newArr h) n).evalE τ = .ok sv ↔
      ∃ c, n.evalE τ = .ok (.int c) ∧ sv = newArrVal R c := by
  simp only [evalE_def, CloseS.eval_newArr]
  cases n.eval τ with
  | none => simp only [Option.map_none, toRes, reduceCtorEq, false_and, exists_false]
  | some x =>
    simp only [Option.map_some, toRes, Srt.erase, Except.ok.injEq, newArrT_erase, PrimTy.erase]
    constructor
    · rintro rfl
      exact ⟨_, rfl, rfl⟩
    · rintro ⟨c, hc, rfl⟩
      cases hc
      rfl

theorem evalE_mval {p : PrimTy} (t : Tm C Γ (.val p)) :
    (Tm.app1 .mval t).evalE τ = t.evalE τ >>= fun x => .ok x.toMVal := by
  simp only [evalE_def, CloseS.eval_mval]
  cases t.eval τ with
  | none => rfl
  | some x => simp only [toRes, Res.ok_bind, Srt.erase, MvT.erase, Close.toMVal_eq]

theorem evalE_ref {R : RefTy} (i : Tm C Γ (.ident R)) :
    (Tm.app1 (.ref (R := R)) i).evalE τ = i.evalE τ >>= fun id => .ok (.ref id) := by
  simp only [evalE_def, CloseS.eval_ref]
  cases i.eval τ <;> rfl

theorem evalE_mfield {s f : Name} {T : Ty} (h : C.fieldType s f = some T)
    (i : Tm C Γ (.ident (.struct s))) :
    (Tm.app1 (.mfield h) i).evalE τ = i.evalE τ >>= fun id => .ok (.memoryField id f) := by
  simp only [evalE_def, CloseS.eval_mfield]
  cases i.eval τ <;> rfl

theorem evalE_mat {R : RefTy} {E : Ty} (a : ArrTy R E) (i : Tm C Γ (.ident R))
    (k : Tm C Γ (.val .uint)) : (Tm.app2 (.mat a) i k).evalE τ =
      i.evalE τ >>= fun id => k.evalE τ >>= Value.asInt >>= fun j => .ok (.memoryIndex id j) := by
  simp only [evalE_def, CloseS.eval_mat]
  cases i.eval τ with
  | none => rfl
  | some id => cases k.eval τ <;> rfl

theorem evalE_alloc (R : RefTy) (h : (Ty.ref R).mapFree = true) (m : Tm C Γ .mem) :
    (Tm.app1 (.alloc R h) m).evalE τ = m.evalE τ >>= fun τ' => allocDefault τ' R >>= fun r => .ok r.2 := by
  simp only [evalE_def]
  show toRes _ (Op1.eval τ.glob (.alloc R h) (m.eval τ)) = _
  rw [Close.Op1.eval_alloc]
  cases m.eval τ with
  | none => rfl
  | some μ =>
    simp only [Option.map_some, toRes, Res.ok_bind, Srt.erase,
      Heap.allocDefault_erase (σ := Heap.into τ.glob.globE μ.heap) (hp := μ.heap) rfl rfl R h]

theorem evalE_addM (R : RefTy) (h : (Ty.ref R).mapFree = true) (m : Tm C Γ .mem) :
    (Tm.app1 (.addM R h) m).evalE τ = m.evalE τ >>= fun τ' => allocDefault τ' R >>= fun r => .ok r.1 := by
  simp only [evalE_def]
  show toRes _ (Op1.eval τ.glob (.addM R h) (m.eval τ)) = _
  rw [Close.Op1.eval_addM]
  cases m.eval τ with
  | none => rfl
  | some μ =>
    simp only [Option.map_some, toRes, Res.ok_bind, Srt.erase,
      Heap.allocDefault_erase (σ := Heap.into τ.glob.globE μ.heap) (hp := μ.heap) rfl rfl R h]
    rfl

theorem evalE_copy {R : RefTy} (h : (Ty.ref R).mapFree = true) (m : Tm C Γ .mem)
    (v : Tm C Γ (.sv (.ref R))) : (Tm.app2 (.copy h) m v).evalE τ =
      v.evalE τ >>= fun sv => m.evalE τ >>= fun τ' => copyStToM τ' sv >>= fun r => r.2.asRef := by
  simp only [evalE_def]
  show toRes _ (Op2.eval τ.glob (.copy h) (m.eval τ) (v.eval τ)) = _
  rw [Close.Op2.eval_copy]
  cases m.eval τ with
  | none => cases v.eval τ <;> rfl
  | some μ =>
    cases v.eval τ with
    | none => rfl
    | some w =>
      simp only [Option.bind_some, toRes, Res.ok_bind, Srt.erase,
        SVal.copyStToM_erase w h μ.heap (Heap.into τ.glob.globE μ.heap) rfl rfl]
      rfl

theorem evalE_copySt {T : Ty} (h : T.mapFree = true) (m : Tm C Γ .mem) (v : Tm C Γ (.sv T)) :
    (Tm.app2 (.copySt h) m v).evalE τ =
      v.evalE τ >>= fun sv => m.evalE τ >>= fun τ' => copyStToM τ' sv >>= fun r => .ok r.1 := by
  simp only [evalE_def]
  show toRes _ (Op2.eval τ.glob (.copySt h) (m.eval τ) (v.eval τ)) = _
  rw [Close.Op2.eval_copySt]
  cases m.eval τ with
  | none => cases v.eval τ <;> rfl
  | some μ =>
    cases v.eval τ with
    | none => rfl
    | some w =>
      simp only [Option.bind_some, toRes, Res.ok_bind, Srt.erase,
        SVal.copyStToM_erase w h μ.heap (Heap.into τ.glob.globE μ.heap) rfl rfl]
      rfl

/-- The identities a memory term's reads go through are of their types in
its heap: where the typed reading is the untyped one. -/
def AddrOk (m : Tm C Γ .mem) {T : Ty} (a : Tm C Γ (.addr T)) : Prop :=
  ∀ μ ad, m.eval τ = some μ → a.eval τ = some ad → ad.Ok μ.H'

def IdentOk (m : Tm C Γ .mem) {R : RefTy} (i : Tm C Γ (.ident R)) : Prop :=
  ∀ μ id, m.eval τ = some μ → i.eval τ = some id → IdOk μ.H' R id

theorem evalE_read {p : PrimTy} (m : Tm C Γ .mem) (a : Tm C Γ (.addr (.prim p)))
    (hok : AddrOk τ m a) : (Tm.app2 .read m a).evalE τ =
      m.evalE τ >>= fun τ' => a.evalE τ >>= fun addr => Close.readVal τ' addr := by
  simp only [evalE_def]
  show toRes _ (Op2.eval τ.glob .read (m.eval τ) (a.eval τ)) = _
  rw [Close.Op2.eval_read]
  cases hm : m.eval τ with
  | none => rfl
  | some μ =>
    cases ha : a.eval τ with
    | none => rfl
    | some ad =>
      simp only [Option.bind_some, toRes, Res.ok_bind, Srt.erase, Close.readVal,
        Grown.readT_erase μ (σ := Heap.into τ.glob.globE μ.heap) rfl ad (hok μ ad hm ha)]
      cases μ.readT ad with
      | none => rfl
      | some w => cases p <;> rfl

theorem evalE_iread {R : RefTy} (m : Tm C Γ .mem) (a : Tm C Γ (.addr (.ref R)))
    (hok : AddrOk τ m a) : (Tm.app2 .iread m a).evalE τ =
      m.evalE τ >>= fun τ' => a.evalE τ >>= fun addr => readAddr τ' addr >>= Semantics.MVal.asRef := by
  simp only [evalE_def]
  show toRes _ (Op2.eval τ.glob .iread (m.eval τ) (a.eval τ)) = _
  rw [Close.Op2.eval_iread]
  cases hm : m.eval τ with
  | none => rfl
  | some μ =>
    cases ha : a.eval τ with
    | none => rfl
    | some ad =>
      simp only [Option.bind_some, toRes, Res.ok_bind, Srt.erase,
        Grown.readT_erase μ (σ := Heap.into τ.glob.globE μ.heap) rfl ad (hok μ ad hm ha)]
      cases μ.readT ad <;> rfl

theorem evalE_mlen {E : Ty} (m : Tm C Γ .mem) (i : Tm C Γ (.ident (.array E)))
    (hok : IdentOk τ m i) : (Tm.app2 .mlen m i).evalE τ =
      m.evalE τ >>= fun τ' => i.evalE τ >>= fun id => memArrayLen τ' id := by
  simp only [evalE_def]
  show toRes _ (Op2.eval τ.glob .mlen (m.eval τ) (i.eval τ)) = _
  rw [Close.Op2.eval_mlen]
  cases hm : m.eval τ with
  | none => rfl
  | some μ =>
    cases hi : i.eval τ with
    | none => rfl
    | some id =>
      have h := hok μ id hm hi
      simp only [Option.bind_some, toRes, Res.ok_bind, Srt.erase, HRef.ofId?_of_ok h]
      rw [Heap.memArrayLen_erase (σ := Heap.into τ.glob.globE μ.heap) (hp := μ.heap) rfl
        (⟨id, h⟩ : HRef μ.H' _) .dyn]
      rfl

theorem evalE_copyMem {R : RefTy} (m : Tm C Γ .mem) (i : Tm C Γ (.ident R))
    (hok : IdentOk τ m i) : (Tm.app2 .copyMem m i).evalE τ =
      m.evalE τ >>= fun τ' => i.evalE τ >>= fun id => copyMem τ' (.ref id) := by
  simp only [evalE_def]
  show toRes _ (Op2.eval τ.glob .copyMem (m.eval τ) (i.eval τ)) = _
  rw [Close.Op2.eval_copyMem]
  cases hm : m.eval τ with
  | none => rfl
  | some μ =>
    cases hi : i.eval τ with
    | none => rfl
    | some id =>
      have h := hok μ id hm hi
      simp only [Option.bind_some, toRes, Res.ok_bind, Srt.erase, HRef.ofId?_of_ok h]
      rw [show Semantics.MVal.ref id = MVal.erase (.ref R) (⟨id, h⟩ : HRef μ.H' R) from rfl,
        MVal.copyMem_erase (σ := Heap.into τ.glob.globE μ.heap) (hp := μ.heap) rfl]

theorem evalE_write {T : Ty} (m : Tm C Γ .mem) (a : Tm C Γ (.addr T)) (v : Tm C Γ (.mv T))
    (hok : AddrOk τ m a) (hv : ∀ μ w, m.eval τ = some μ → v.eval τ = some w → MvT.Ok μ.H' T w) :
    (Tm.app3 .write m a v).evalE τ = v.evalE τ >>= fun mv => m.evalE τ >>= fun τ' =>
      a.evalE τ >>= fun addr => writeAddr τ' mv addr := by
  simp only [evalE_def]
  show toRes _ (Op3.eval τ.glob .write (m.eval τ) (a.eval τ) (v.eval τ)) = _
  rw [Close.Op3.eval_write]
  cases hm : m.eval τ with
  | none => cases v.eval τ <;> rfl
  | some μ =>
    cases ha : a.eval τ with
    | none => cases v.eval τ <;> rfl
    | some ad =>
      cases hvv : v.eval τ with
      | none => rfl
      | some w =>
        simp only [Option.bind_some, toRes, Res.ok_bind, Srt.erase,
          Grown.writeT_erase μ τ.glob.globE ad w (hok μ ad hm ha) (hv μ w hm hvv)]
        cases μ.writeT ad w <;> rfl

end Terms

end Tm

theorem Rhs.evalE_val {Γ : Ctx} (σ₀ : State C Γ) {p : PrimTy} (t : Tm C Γ (.val p)) :
    (Rhs.val t).evalE σ₀ = t.evalE σ₀ := rfl
theorem Rhs.evalE_path {Γ : Ctx} (σ₀ : State C Γ) {R : RefTy} (p : Tm C Γ (.path (.ref R))) :
    (Rhs.path p).evalE σ₀ = p.evalE σ₀ >>= fun rs => .ok (some rs) := by
  simp only [Rhs.evalE, Tm.evalE]
  show toRes _ ((p.eval σ₀).bind _) = _
  cases p.eval σ₀ <;> rfl
theorem Rhs.evalE_mref {Γ : Ctx} (σ₀ : State C Γ) {R : RefTy} (i : Tm C Γ (.ident R)) :
    (Rhs.mref i).evalE σ₀ = i.evalE σ₀ >>= fun id => .ok (some id) := by
  simp only [Rhs.evalE, Tm.evalE]
  show toRes _ ((i.eval σ₀).bind _) = _
  cases i.eval σ₀ <;> rfl
theorem Rhs.evalE_store {Γ : Ctx} (σ₀ : State C Γ) (s : Tm C Γ .st) :
    (Rhs.store s).evalE σ₀ = s.evalE σ₀ >>= fun τ' => .ok τ'.storage := by
  simp only [Rhs.evalE, Tm.evalE]
  show toRes _ ((s.eval σ₀).bind _) = _
  cases s.eval σ₀ <;> rfl

/-! ## Updates, erased

The old untyped application of an update, element by element, its terms
read by `Tm.evalE`; it is the typed one erased (`Upd.applyVE_eq`). -/

section Updates

variable {Γ : Ctx}

/-- The global part one element leaves, erased. -/
def UpdElem.globTE {Δ : Ctx} (σ₀ : State C Γ) :
    UpdElem C Γ Δ → Semantics.State → Res Semantics.State
  | .local _ r, g => do let _ ← r.evalE σ₀; pure g
  | .storage s, g => do
    let st := (← s.evalE σ₀).storage
    pure { g with storage := st }
  | .memory m, g => do
    let μ ← m.evalE σ₀
    pure { g with heap := μ.heap, nextId := μ.nextId }
  | .selfBalance op a, g => do
    let amt ← (← a.evalE σ₀).asInt
    let b := op.apply σ₀.globE.selfBalance amt
    if PrimTy.uint.inRange b = true then pure { g with selfBalance := b } else .error .revert
  | .net r op a, g => do
    let addr ← (← r.evalE σ₀).asInt
    let amt ← (← a.evalE σ₀).asInt
    pure { g with net := setBy addr (op.apply (g.getNet addr) amt) g.net }
  | .pay r a, g => do
    let addr ← (← r.evalE σ₀).asInt
    let amt ← (← a.evalE σ₀).asInt
    if amt < 0 then .error .revert
    else pure { g with
      net := if addr = σ₀.globE.tx.selfAddress then g.net
        else setBy addr (g.getNet addr - amt) g.net }
  | .netMt r a, g => do
    let addr ← (← r.evalE σ₀).asInt
    let amt ← (← a.evalE σ₀).asInt
    pure { g with net := [(addr, amt)] }
  | .setBalance a, g => do
    let amt ← (← a.evalE σ₀).asInt
    pure { g with selfBalance := amt }

/-- One element applied to an erased global part and locals. -/
def UpdElem.applyVE {Δ : Ctx} (σ₀ : State C Γ) :
    UpdElem C Γ Δ → Semantics.State → Locs C Δ → Res (Semantics.State × Locs C Δ)
  | .local i r, g, ℓ => do pure (g, ℓ.set i (← r.evalE σ₀))
  | e, g, ℓ => do pure (← e.globTE σ₀ g, ℓ)

/-- **What an update applied in `σ₀` leaves, erased**: the global part and
the locals' values. -/
def Upd.applyVE (σ₀ : State C Γ) : {Δ : Ctx} → Upd C Γ Δ → Res (Semantics.State × Locs C Δ)
  | _, .nil => pure (σ₀.globE, σ₀.loc)
  | _, .snoc U e => do let p ← U.applyVE σ₀; e.applyVE σ₀ p.1 p.2
  | _, .decl U _ r => do
    let p ← U.applyVE σ₀
    let v ← r.evalE σ₀
    pure (p.1, p.2.push v)
  | _, .pop U h => do let p ← U.applyVE σ₀; pure (p.1, p.2.drop h)
  | _, .drop U h => do let p ← U.applyVE σ₀; pure (p.1, p.2.thin h)

/-- An update's result, erased. -/
def eraseQ {H : HTy} {Δ : Ctx} (q : GlobT C H × LocsV C Δ) : Semantics.State × Locs C Δ :=
  (q.1.1.globE, q.2.erase)

theorem toRes_bind {α β γ : Type} (f : β → γ) (x : Option α) (k : α → Option β) :
    toRes f (x.bind k) = toRes id x >>= fun a => toRes f (k a) := by
  cases x <;> rfl

theorem UpdElem.applyVE_eq {Δ : Ctx} (σ₀ : State C Γ) (e : UpdElem C Γ Δ) (g : GlobT C σ₀.H)
    (ℓ : LocsV C Δ) : e.applyVE σ₀ g.1.globE ℓ.erase = toRes eraseQ (e.applyV σ₀ g ℓ) := by
  rw [UpdElem.applyV_eq_applyVM]
  cases e with
  | «local» i r =>
    simp only [UpdElem.applyVE, UpdElem.applyVM, Rhs.evalE]
    cases r.eval σ₀ with
    | none => rfl
    | some v =>
      simp only [toRes, Option.bind_some, eraseQ, LocsV.erase_set]
      rfl
  | storage s =>
    simp only [UpdElem.applyVE, UpdElem.applyVM, UpdElem.globTE, UpdElem.globT_eq_globTM,
      UpdElem.globTM, Tm.evalE]
    cases s.eval σ₀ <;> rfl
  | memory m =>
    simp only [UpdElem.applyVE, UpdElem.applyVM, UpdElem.globTE, UpdElem.globT_eq_globTM,
      UpdElem.globTM, Tm.evalE]
    cases m.eval σ₀ <;> rfl
  | selfBalance op a =>
    simp only [UpdElem.applyVE, UpdElem.applyVM, UpdElem.globTE, UpdElem.globT_eq_globTM,
      UpdElem.globTM, Tm.evalE]
    cases a.eval σ₀ with
    | none => rfl
    | some amt =>
      simp only [toRes, Option.bind_some, Srt.erase, PrimTy.asInt_erase_uint, Res.ok_bind]
      show (if PrimTy.uint.inRange (op.apply σ₀.selfBalance.1 amt.1) = true then _ else _) >>= _ = _
      simp only [PrimTy.ofInt?, PrimTy.ofValue?]
      split <;> rename_i hb
      · simp only [hb, dite_true, Option.bind_some, pure, Except.pure, Res.ok_bind, toRes]
        rfl
      · simp only [hb, Bool.false_eq_true, dite_false, Option.bind_none, toRes]
        rfl
  | net r op a =>
    simp only [UpdElem.applyVE, UpdElem.applyVM, UpdElem.globTE, UpdElem.globT_eq_globTM,
      UpdElem.globTM, Tm.evalE]
    cases r.eval σ₀ with
    | none => rfl
    | some x => cases a.eval σ₀ <;> rfl
  | pay r a =>
    simp only [UpdElem.applyVE, UpdElem.applyVM, UpdElem.globTE, UpdElem.globT_eq_globTM,
      UpdElem.globTM, Tm.evalE]
    cases r.eval σ₀ with
    | none => rfl
    | some x =>
      cases a.eval σ₀ with
      | none => rfl
      | some y =>
        have hy : ¬ y.1 < 0 := by
          have := y.2
          simp only [PrimTy.inRange, decide_eq_true_eq] at this
          omega
        simp only [toRes, Srt.erase, PrimTy.asInt_erase_uint, Res.ok_bind, hy, ↓reduceIte,
          Option.bind_some]
        rfl
  | netMt r a =>
    simp only [UpdElem.applyVE, UpdElem.applyVM, UpdElem.globTE, UpdElem.globT_eq_globTM,
      UpdElem.globTM, Tm.evalE]
    cases r.eval σ₀ with
    | none => rfl
    | some x => cases a.eval σ₀ <;> rfl
  | setBalance a =>
    simp only [UpdElem.applyVE, UpdElem.applyVM, UpdElem.globTE, UpdElem.globT_eq_globTM,
      UpdElem.globTM, Tm.evalE]
    cases a.eval σ₀ <;> rfl

/-- **The erased application is the typed one, erased.** -/
theorem Upd.applyVE_eq (σ₀ : State C Γ) : {Δ : Ctx} → (U : Upd C Γ Δ) →
    U.applyVE σ₀ = toRes eraseQ (U.applyV σ₀)
  | _, .nil => by
    show pure (σ₀.globE, σ₀.loc) = toRes eraseQ (some (σ₀.globG, σ₀.locV))
    simp only [toRes, eraseQ, State.locV_erase]
    rfl
  | _, .snoc U e => by
    show (U.applyVE σ₀ >>= fun p => e.applyVE σ₀ p.1 p.2) =
      toRes eraseQ ((U.applyV σ₀).bind fun p => e.applyV σ₀ p.1 p.2)
    rw [Upd.applyVE_eq σ₀ U]
    cases U.applyV σ₀ with
    | none => rfl
    | some p => exact UpdElem.applyVE_eq σ₀ e p.1 p.2
  | _, .decl U _ r => by
    show (U.applyVE σ₀ >>= fun p => r.evalE σ₀ >>= fun v => pure (p.1, p.2.push v)) =
      toRes eraseQ ((U.applyV σ₀).bind fun p => (r.eval σ₀).bind fun v => some (p.1, p.2.push v))
    rw [Upd.applyVE_eq σ₀ U]
    cases U.applyV σ₀ with
    | none => rfl
    | some p =>
      simp only [Rhs.evalE]
      cases r.eval σ₀ with
      | none => rfl
      | some v =>
        simp only [toRes, eraseQ, Option.bind_some]
        rw [LocsV.erase_push]
        rfl
  | _, .pop U h => by
    show (U.applyVE σ₀ >>= fun p => pure (p.1, p.2.drop h)) =
      toRes eraseQ ((U.applyV σ₀).bind fun p => some (p.1, p.2.drop h))
    rw [Upd.applyVE_eq σ₀ U]
    cases U.applyV σ₀ <;> rfl
  | _, .drop U h => by
    show (U.applyVE σ₀ >>= fun p => pure (p.1, p.2.thin h)) =
      toRes eraseQ ((U.applyV σ₀).bind fun p => some (p.1, p.2.thin h))
    rw [Upd.applyVE_eq σ₀ U]
    cases U.applyV σ₀ <;> rfl

end Updates

end Solidity
