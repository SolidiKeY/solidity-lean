import Solidity.Calculus.StepFragment
import Solidity.Calculus.ElimWriteFree
import Solidity.Calculus.DecideScoped

/-!
# On the fragment, every leaf of the strategy eliminates write-free

Lean only.  `Calculus/StepFragment.lean` says one rule on the fragment
writes save-like updates; `Calculus/ElimWriteFree.lean` that a read of a
term the elimination has a reading for (`LTm.Elimable`) eliminates to a
storage-free term.  Here the two meet, at the reduction's composition
(`Upd.toLS`, `Fml.toLS`, `Calculus/DecideScoped.lean`): the leaf the
strategy leaves is a nest of updates, and pushing it in substitutes each
update's storage into the next one's `storage`.

* **Terms** (`Tm.ElimOk`): `LTm.Elimable`'s symbols on the scoped terms,
  any local.  Pushed in at a symbolic state whose bindings and storage are
  elimable (`SymS.Ok`), an `ElimOk` term is elimable (`Tm.ElimOk.toL`);
  in save normal form (`Tm.SaveNF`) at a state whose storage is
  (`SymS.OkNF`), it is in `LTm.SaveNF` (`Tm.SaveNF.toL`): a chain of saves
  substituted into a chain stays a chain.  So the composition of updates in
  save normal form is in save normal form (`Upd.toLS_okNF`), from the start
  `SymS.init` on.
* **Steps** (`Premise.ElimOk`): on the fragment every term a rule writes
  is `ElimOk` (`Stmt.step_elimOk`, one lemma per arm), from the lowering of
  a memory-free expression (`Val.lower_elimOk`); the expansion keeps it
  (`Tm.expand?_elimOk`), so every storage right-hand side a step writes,
  expanded and pushed in, is in `LTm.SaveNF` (`Stmt.step_toL_saveNF`).
* **Every expansion at once** (`Tm.pickExpandAll`, all four kinds): an
  equivalence on an update (`holds_upd_expandAll_iff`) that turns a
  save-like update with a reading into one in save normal form
  (`Upd.rwBy_expandAll_nf`), which pushes in onto a chain of saves
  (`Upd.SaveLike.toLS_expandAll_okNF`).
* **Formulas** (`Fml.Frag`): programs in the fragment, updates save-like
  and `ElimOk`, equations `ElimOk`, no `wt`.  `Fml.stepR` keeps it
  (`Fml.stepR_frag`), so `symex` does (`symex_frag`), and the pushed-in
  leaf is elimable (`Fml.Frag.toLS`), hence its reduction storage-free
  (`Fml.Frag.reduceS_stoFree`, `symex_reduceS_stoFree`).  Elimability needs
  no expansion: `delAt`, `push`, `pop` have a reading of their own; save
  normal form is the finer shape the expansion gives.

**Narrowed.**  An alias declared without an initializer
(`T storage x;`) is bound to `err` at a path sort (`Rhs.toL` of `unset`),
which `LTm.Elimable` refuses (the elimination keeps it as written), so
the fragment requires an initializer (`Stmt.Frag`); `wellFormed(s)` pushes
in to `wt`, which the elimination keeps as written, so `Fml.Frag` leaves it
out.  Updates are kept apart on the leaf (`symex` never merges them):
merging (`Upd.seqPar`) is a rewrite of the leaf, which `Fml.toLS` composes
the same way.
-/

namespace Solidity

open Solidity (Srt Op0 Op1 Op2 Op3 Modality)
open Decide

variable {C : Contract}

/-! ## Terms with a reading -/

section Terms

variable {Γ : Ctx}

/-- **A term the elimination has a reading for, once pushed in**: the
symbols `LTm.Elimable` admits, any local. -/
inductive Tm.ElimOk : {s : Srt} → Tm C Γ s → Prop where
  | pvV {p : PrimTy} (i : Idx Γ (.val p)) : Tm.ElimOk (.pvV i)
  | pvP {R : RefTy} (i : Idx Γ (.alias R)) : Tm.ElimOk (.pvP i)
  | pvS (i : Idx Γ .old) : Tm.ElimOk (.pvS i)
  | pvI {R : RefTy} (i : Idx Γ (.mem R)) : Tm.ElimOk (.pvI i)
  | pvZ (i : Idx Γ .kint) : Tm.ElimOk (.pvZ i)
  | app0 {s : Srt} {o : Op0 C s} (ho : o.elimOk = true) : Tm.ElimOk (.app0 o)
  | app1 {a s : Srt} {o : Op1 C a s} {x : Tm C Γ a} (ho : o.elimOk = true) (hx : Tm.ElimOk x) :
      Tm.ElimOk (.app1 o x)
  | app2 {a b s : Srt} {o : Op2 C a b s} {x : Tm C Γ a} {y : Tm C Γ b} (ho : o.elimOk = true)
      (hx : Tm.ElimOk x) (hy : Tm.ElimOk y) : Tm.ElimOk (.app2 o x y)
  | app3 {a b c s : Srt} {o : Op3 C a b c s} {x : Tm C Γ a} {y : Tm C Γ b} {z : Tm C Γ c}
      (ho : o.elimOk = true) (hx : Tm.ElimOk x) (hy : Tm.ElimOk y) (hz : Tm.ElimOk z) :
      Tm.ElimOk (.app3 o x y z)

theorem Tm.ElimOk.castV {p q : PrimTy} (h : p = q) {t : Tm C Γ (.val p)} (ht : t.ElimOk) :
    (Tm.castV h t).ElimOk := by
  subst h; exact ht

end Terms

/-! ## The symbolic state, elimable -/

section State

/-- Every binding is elimable. -/
def Decide.BEnv.Ok : {Γ : Ctx} → BEnv C Γ → Prop
  | [], _ => True
  | _ :: _, e => (∀ b, e.1 = some b → LTm.Elimable b) ∧ BEnv.Ok e.2

theorem Decide.BEnv.Ok.get : {Γ : Ctx} → {t : LTy} → (i : Idx Γ t) → {e : BEnv C Γ} → e.Ok →
    ∀ {b : LTm C t.bs}, e.get i = some b → b.Elimable
  | _, _, .here, _, he, _, hb => he.1 _ hb
  | _, _, .there i, _, he, _, hb => BEnv.Ok.get i he.2 hb

theorem Decide.BEnv.Ok.set : {Γ : Ctx} → {t : LTy} → (i : Idx Γ t) → {e : BEnv C Γ} → e.Ok →
    {w : Option (LTm C t.bs)} → (∀ b, w = some b → b.Elimable) → (e.set i w).Ok
  | _, _, .here, _, he, _, hw => ⟨hw, he.2⟩
  | _, _, .there i, _, he, _, hw => ⟨he.1, BEnv.Ok.set i he.2 hw⟩

theorem Decide.BEnv.Ok.drop {Γ : Ctx} : {Δ : Ctx} → (h : Ext Γ Δ) → {e : BEnv C Δ} → e.Ok →
    (BEnv.drop h e).Ok
  | _, .refl, _, he => he
  | _, .push h, _, he => BEnv.Ok.drop h he.2

theorem Decide.BEnv.Ok.thin : {Γ Δ : Ctx} → (h : Thin Γ Δ) → {e : BEnv C Δ} → e.Ok →
    (BEnv.thin h e).Ok
  | _, _, .refl, _, he => he
  | _, _, .keep h, _, he => ⟨he.1, BEnv.Ok.thin h he.2⟩
  | _, _, .drop h, _, he => BEnv.Ok.thin h he.2

/-- **A symbolic state the elimination reads**: its bindings, its
storage and its balance elimable. -/
def Decide.SymS.Ok {Γ : Ctx} (ρ : SymS C Γ) : Prop :=
  ρ.loc.Ok ∧ ρ.stor.Elimable ∧ ρ.bal.Elimable

/-- Its bindings and balance elimable, its storage in save normal form. -/
def Decide.SymS.OkNF {Γ : Ctx} (ρ : SymS C Γ) : Prop :=
  ρ.loc.Ok ∧ ρ.stor.SaveNF ∧ ρ.bal.Elimable

theorem Decide.SymS.OkNF.ok {Γ : Ctx} {ρ : SymS C Γ} (h : ρ.OkNF) : ρ.Ok :=
  ⟨h.1, h.2.1.elimable, h.2.2⟩

theorem Decide.SymS.init_okNF : (SymS.init : SymS C []).OkNF := ⟨trivial, .storage, .app0 rfl⟩

theorem Decide.SymS.Ok.push {Γ : Ctx} {t : LTy} {ρ : SymS C Γ} (h : ρ.Ok)
    {b : Option (LTm C t.bs)} (hb : ∀ x, b = some x → x.Elimable) : (ρ.push b).Ok :=
  ⟨⟨hb, h.1⟩, h.2⟩

theorem Decide.SymS.OkNF.push {Γ : Ctx} {t : LTy} {ρ : SymS C Γ} (h : ρ.OkNF)
    {b : Option (LTm C t.bs)} (hb : ∀ x, b = some x → x.Elimable) : (ρ.push b).OkNF :=
  ⟨⟨hb, h.1⟩, h.2⟩

theorem Decide.SymS.Ok.pushQ {Γ : Ctx} (p : PrimTy) {ρ : SymS C Γ} (h : ρ.Ok) :
    (ρ.pushQ p).Ok :=
  h.push fun _ hx => by cases hx; exact .var _

theorem Decide.SymS.Ok.pushB {Γ : Ctx} (t : LTy) {ρ : SymS C Γ} (h : ρ.Ok) : (ρ.pushB t).Ok := by
  cases t with
  | val p => exact h.pushQ p
  | _ => exact h.push fun _ hx => by cases hx

end State

/-! ## Pushed in, a term with a reading is elimable -/

section ToL

variable {Γ : Ctx}

theorem Decide.lit_elimable {p : PrimTy} (v : p.Denote) : (LTm.lit v : LTm C (.val p)).Elimable :=
  .app0 rfl

theorem Decide.literalRead_elimable {p : PrimTy} {t : LTm C (.val p)} (ht : t.Elimable) :
    t.literalRead.Elimable := by
  unfold LTm.literalRead
  split
  · dsimp only
    split
    · rename_i h
      obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp h
      rw [LTm.eq_of_litV? hv]; exact .app0 rfl
    · exact ht
  · exact ht

theorem Decide.foldAt_elimable {R : RefTy} {k : PrimTy} {V : Ty} (it : IndexTy R k V)
    {S : LTm C .st} {q : LTm C (.path (.ref R))} {i : LTm C (.val k)} (hS : S.Elimable)
    (hq : q.Elimable) (hi : i.Elimable) : (foldAt it S q i).Elimable := by
  unfold foldAt
  split
  · split
    · exact .index hq hi
    · exact .app3 rfl hS hq hi
  · exact .app3 rfl hS hq hi

theorem Decide.foldNext_elimable {E : Ty} {S : LTm C .st} {q : LTm C (.path (.ref (.array E)))}
    (hS : S.Elimable) (hq : q.Elimable) : (foldNext S q).Elimable := by
  unfold foldNext
  split
  · split
    · exact .index hq (.app0 rfl)
    · exact .app2 rfl hS hq
  · exact .app2 rfl hS hq

theorem Decide.fold1_unop_elimable (op : UnOp) {p : PrimTy} (h : op.accepts p = true)
    {x : LTm C (.val p)} (hx : x.Elimable) : (fold1 (.unop op h) x).Elimable := by
  unfold fold1
  simp only
  split
  · split
    · exact .app0 rfl
    · exact .err
  · exact .app1 rfl hx

theorem Decide.fold2_binop_elimable (op : BinOp) {p : PrimTy} (h : op.accepts p = true)
    {x y : LTm C (.val p)} (hx : x.Elimable) (hy : y.Elimable) :
    (fold2 (.binop op h) x y).Elimable := by
  unfold fold2
  simp only
  split
  · split
    · exact .app0 rfl
    · split
      · split
        · exact .app2 rfl hx hy
        · split
          · exact .app0 rfl
          · exact .err
      · exact .app2 rfl hx hy
  · exact .app2 rfl hx hy

theorem Op0.toL_elimable {ρ : SymS C Γ} (hρ : ρ.Ok) {s : Srt} (o : Op0 C s)
    (ho : o.elimOk = true) {l : LTm C s} (h : o.toL ρ = some l) : l.Elimable := by
  cases o <;> simp only [Op0.elimOk, Bool.false_eq_true] at ho <;>
    simp only [Op0.toL, Option.some.injEq] at h <;> subst h
  all_goals first | exact .app0 rfl | exact hρ.2.1 | skip
  rename_i k
  cases k <;> first | exact hρ.2.2 | exact .app0 rfl

theorem Op1.toL_elimable {ρ : SymS C Γ} (hρ : ρ.Ok) {a s : Srt} (o : Op1 C a s)
    (ho : o.elimOk = true) {x : LTm C a} (hx : x.Elimable) {l : LTm C s} (h : o.toL ρ x = some l) :
    l.Elimable := by
  cases o <;> simp only [Op1.elimOk, Bool.false_eq_true] at ho <;>
    simp only [Op1.toL, Option.some.injEq, reduceCtorEq] at h <;> subst h
  all_goals first
    | exact Decide.fold1_unop_elimable _ _ hx
    | exact Decide.foldNext_elimable hρ.2.1 hx
    | exact .app1 rfl hx

theorem Op2.toL_elimable {ρ : SymS C Γ} (hρ : ρ.Ok) {a b s : Srt} (o : Op2 C a b s)
    (ho : o.elimOk = true) {x : LTm C a} {y : LTm C b} (hx : x.Elimable) (hy : y.Elimable)
    {l : LTm C s} (h : o.toL ρ x y = some l) : l.Elimable := by
  cases o <;> simp only [Op2.elimOk, Bool.false_eq_true] at ho <;>
    simp only [Op2.toL, Option.some.injEq] at h <;> subst h
  all_goals first
    | exact Decide.fold2_binop_elimable _ _ hx hy
    | exact Decide.literalRead_elimable (.app2 rfl hx hy)
    | exact Decide.foldAt_elimable _ hρ.2.1 hx hy
    | exact .app2 rfl hx hy

theorem Op3.toL_elimable {a b c s : Srt} (o : Op3 C a b c s) (ho : o.elimOk = true)
    {x : LTm C a} {y : LTm C b} {z : LTm C c} (hx : x.Elimable) (hy : y.Elimable)
    (hz : z.Elimable) {l : LTm C s} (h : o.toL x y z = some l) : l.Elimable := by
  cases o <;> simp only [Op3.elimOk, Bool.false_eq_true] at ho <;>
    simp only [Op3.toL, Option.some.injEq] at h <;> subst h
  all_goals first
    | exact Decide.foldAt_elimable _ hx hy hz
    | exact .app3 rfl hx hy hz

/-- **Pushed in at an elimable state, a term with a reading is elimable.** -/
theorem Tm.ElimOk.toL {ρ : SymS C Γ} (hρ : ρ.Ok) {s : Srt} {t : Tm C Γ s} (ht : t.ElimOk) :
    ∀ {l : LTm C s}, t.toL ρ = some l → l.Elimable := by
  intro l h
  rw [Tm.toL_eq_toLM] at h
  induction ht with
  | pvV i | pvP i | pvS i | pvI i | pvZ i => exact hρ.1.get i h
  | app0 ho => exact Op0.toL_elimable hρ _ ho h
  | app1 ho _ ih =>
    simp only [Tm.toLM, Option.bind_eq_some_iff] at h
    obtain ⟨x', hx, h⟩ := h
    exact Op1.toL_elimable hρ _ ho (ih hx) h
  | app2 ho _ _ ihx ihy =>
    simp only [Tm.toLM, Option.bind_eq_some_iff] at h
    obtain ⟨x', hx, y', hy, h⟩ := h
    exact Op2.toL_elimable hρ _ ho (ihx hx) (ihy hy) h
  | app3 ho _ _ _ ihx ihy ihz =>
    simp only [Tm.toLM, Option.bind_eq_some_iff] at h
    obtain ⟨x', hx, y', hy, z', hz, h⟩ := h
    exact Op3.toL_elimable _ ho (ihx hx) (ihy hy) (ihz hz) h

end ToL

/-! ## A chain of saves pushed in is a chain of saves -/

section SaveNF

variable {Γ : Ctx}

/-- **The bridge**: a storage in save normal form whose paths and values
have a reading, pushed in at a state whose storage is in save normal form,
is in `LTm.SaveNF`.  With `ρ`'s storage `storage` (`SymS.init`), this is
`Tm.SaveNF`'s shape read as `LTm.SaveNF`'s. -/
theorem Tm.SaveNF.toL {ρ : SymS C Γ} (hρ : ρ.OkNF) {t : Tm C Γ .st} (ht : t.SaveNF)
    (he : t.ElimOk) : ∀ {l : LTm C .st}, t.toL ρ = some l → l.SaveNF := by
  induction ht with
  | storage =>
    intro l h
    simp only [Tm.toL_eq_toLM, Tm.toLM, Op0.toL, Option.some.injEq] at h
    subst h; exact hρ.2.1
  | save p v hs ih =>
    intro l h
    cases he with
    | app3 _ hx hy hz =>
      rw [Tm.toL_eq_toLM] at h
      simp only [Tm.toLM, Option.bind_eq_some_iff] at h
      obtain ⟨x', hx', y', hy', z', hz', h⟩ := h
      simp only [Op3.toL, foldRead3, Option.some.injEq] at h
      subst h
      rw [← Tm.toL_eq_toLM] at hx' hy' hz'
      exact .save (ih hx hx') (hy.toL hρ.ok hy') (hz.toL hρ.ok hz')
  | pushSlot p hs ih =>
    intro l h
    cases he with
    | app2 _ hx hy =>
      rw [Tm.toL_eq_toLM] at h
      simp only [Tm.toLM, Option.bind_eq_some_iff] at h
      obtain ⟨x', hx', y', hy', h⟩ := h
      simp only [Op2.toL, Option.some.injEq] at h
      subst h
      rw [← Tm.toL_eq_toLM] at hx' hy'
      exact .pushSlot (ih hx hx') (hy.toL hρ.ok hy')
  | shrink p hs ih =>
    intro l h
    cases he with
    | app2 _ hx hy =>
      rw [Tm.toL_eq_toLM] at h
      simp only [Tm.toLM, Option.bind_eq_some_iff] at h
      obtain ⟨x', hx', y', hy', h⟩ := h
      simp only [Op2.toL, Option.some.injEq] at h
      subst h
      rw [← Tm.toL_eq_toLM] at hx' hy'
      exact .shrink (ih hx hx') (hy.toL hρ.ok hy')

/-- Hence a word read of it eliminates storage-free. -/
theorem Tm.SaveNF.find_stoFree {ρ : SymS C Γ} (hρ : ρ.OkNF) {t : Tm C Γ .st} (ht : t.SaveNF)
    (he : t.ElimOk) {l : LTm C .st} (hl : t.toL ρ = some l) {p : PrimTy}
    {q : LTm C (.path (.prim p))} (hq : q.Elimable) :
    ((LTm.app2 .find l q).elim : LTm C (.val p)).StoFree :=
  LTm.SaveNF.find_stoFree (ht.toL hρ he hl) hq

end SaveNF

/-! ## Updates pushed in -/

section Upd

variable {Γ : Ctx}

/-- A right-hand side with a reading: an alias is set (`unset` binds `err`
at a path, which the elimination keeps as written). -/
def Rhs.ElimOk {t : LTy} : Rhs C Γ t → Prop
  | .val x => x.ElimOk
  | .path p => p.ElimOk
  | .unset => False
  | .mref i => i.ElimOk
  | .store s => s.ElimOk
  | .saveNet => True
  | .saveNetMt => True
  | .zint x => x.ElimOk

/-- An element with a reading: a local, or the storage. -/
def UpdElem.ElimOk {Δ : Ctx} : UpdElem C Γ Δ → Prop
  | .local _ r => r.ElimOk
  | .storage s => s.ElimOk
  | _ => False

/-- Every element and declaration has a reading. -/
def Upd.ElimOk : {Δ : Ctx} → Upd C Γ Δ → Prop
  | _, .nil => True
  | _, .snoc U e => U.ElimOk ∧ e.ElimOk
  | _, .decl U _ r => U.ElimOk ∧ r.ElimOk
  | _, .pop U _ => U.ElimOk
  | _, .drop U _ => U.ElimOk

/-- An element writes the storage, if at all, in save normal form. -/
def UpdElem.NF {Δ : Ctx} : UpdElem C Γ Δ → Prop
  | .storage s => s.SaveNF
  | _ => True

/-- Every storage element is in save normal form. -/
def Upd.NF : {Δ : Ctx} → Upd C Γ Δ → Prop
  | _, .nil => True
  | _, .snoc U e => U.NF ∧ e.NF
  | _, .decl U _ _ => U.NF
  | _, .pop U _ => U.NF
  | _, .drop U _ => U.NF

theorem Decide.seqL_elimable {s' s : Srt} {g : LTm C s'} {a : LTm C s} (hg : g.Elimable)
    (ha : a.Elimable) : (seqL g a).Elimable := by
  unfold seqL
  split
  · exact ha
  · exact .seq hg ha

theorem Decide.tt_elimable : (LTm.tt : LTm C (.val .bool)).Elimable := .app0 rfl

theorem Rhs.ElimOk.toL {ρ : SymS C Γ} (hρ : ρ.Ok) {t : LTy} {r : Rhs C Γ t} (hr : r.ElimOk)
    {b : LTm C t.bs × LTm C (.val .bool)} (h : r.toL ρ = some b) :
    b.1.Elimable ∧ b.2.Elimable := by
  cases r with
  | val x | path x | mref x | store x | zint x =>
    simp only [Rhs.toL, Option.map_eq_some_iff] at h
    obtain ⟨x', hx, rfl⟩ := h
    have hx' := Tm.ElimOk.toL hρ hr hx
    exact ⟨hx', Decide.seqL_elimable hx' Decide.tt_elimable⟩
  | unset => exact hr.elim
  | saveNet | saveNetMt => simp only [Rhs.toL, reduceCtorEq] at h

theorem UpdElem.ElimOk.toLS {Δ : Ctx} {ρ₀ : SymS C Γ} (hρ₀ : ρ₀.Ok) {e : UpdElem C Γ Δ}
    (he : e.ElimOk) {ρ : SymS C Δ} (hρ : ρ.Ok) {q : SymS C Δ × LTm C (.val .bool)}
    (h : e.toLS ρ₀ ρ = some q) : q.1.Ok ∧ q.2.Elimable := by
  cases e with
  | «local» i r =>
    simp only [UpdElem.toLS, Option.map_eq_some_iff] at h
    obtain ⟨b, hb, rfl⟩ := h
    have hb' := Rhs.ElimOk.toL hρ₀ he hb
    exact ⟨⟨hρ.1.set i (fun x hx => by cases hx; exact hb'.1), hρ.2⟩, hb'.2⟩
  | storage s =>
    simp only [UpdElem.toLS, Option.map_eq_some_iff] at h
    obtain ⟨s', hs, rfl⟩ := h
    have hs' := Tm.ElimOk.toL hρ₀ he hs
    exact ⟨⟨hρ.1, hs', hρ.2.2⟩, Decide.seqL_elimable hs' Decide.tt_elimable⟩
  | _ => exact he.elim

theorem UpdElem.ElimOk.toLS_nf {Δ : Ctx} {ρ₀ : SymS C Γ} (hρ₀ : ρ₀.OkNF) {e : UpdElem C Γ Δ}
    (he : e.ElimOk) (hn : e.NF) {ρ : SymS C Δ} (hρ : ρ.OkNF) {q : SymS C Δ × LTm C (.val .bool)}
    (h : e.toLS ρ₀ ρ = some q) : q.1.OkNF := by
  have hq := he.toLS hρ₀.ok hρ.ok h
  cases e with
  | «local» i r =>
    simp only [UpdElem.toLS, Option.map_eq_some_iff] at h
    obtain ⟨b, hb, rfl⟩ := h
    exact ⟨hq.1.1, hρ.2⟩
  | storage s =>
    simp only [UpdElem.toLS, Option.map_eq_some_iff] at h
    obtain ⟨s', hs, rfl⟩ := h
    exact ⟨hρ.1, Tm.SaveNF.toL hρ₀ hn he hs, hρ.2.2⟩
  | _ => exact he.elim

/-- **An update with a reading, pushed in at an elimable state**, leaves an
elimable state, and what must return for it to land is elimable. -/
theorem Upd.ElimOk.toLS {ρ₀ : SymS C Γ} (hρ₀ : ρ₀.Ok) : {Δ : Ctx} → {U : Upd C Γ Δ} →
    U.ElimOk → ∀ {q : SymS C Δ × LTm C (.val .bool)}, U.toLS ρ₀ = some q →
    q.1.Ok ∧ q.2.Elimable := by
  intro Δ U hU q h
  rw [Upd.toLS_eq_toLSM] at h
  induction U with
  | nil =>
    simp only [Upd.toLSM, Option.some.injEq] at h
    subst h; exact ⟨hρ₀, Decide.tt_elimable⟩
  | snoc U e ih =>
    simp only [Upd.toLSM, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨p, hp, r, hr, rfl⟩ := h
    have hp' := ih hU.1 hp
    have hr' := hU.2.toLS hρ₀ hp'.1 hr
    exact ⟨hr'.1, Decide.seqL_elimable hp'.2 hr'.2⟩
  | decl U x r ih =>
    simp only [Upd.toLSM, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨p, hp, b, hb, rfl⟩ := h
    have hp' := ih hU.1 hp
    have hb' := Rhs.ElimOk.toL hρ₀ hU.2 hb
    exact ⟨hp'.1.push (fun y hy => by cases hy; exact hb'.1), Decide.seqL_elimable hp'.2 hb'.2⟩
  | pop U h' ih =>
    simp only [Upd.toLSM, Option.map_eq_some_iff] at h
    obtain ⟨p, hp, rfl⟩ := h
    have hp' := ih hU hp
    exact ⟨⟨hp'.1.1.drop h', hp'.1.2⟩, hp'.2⟩
  | drop U h' ih =>
    simp only [Upd.toLSM, Option.map_eq_some_iff] at h
    obtain ⟨p, hp, rfl⟩ := h
    have hp' := ih hU hp
    exact ⟨⟨hp'.1.1.thin h', hp'.1.2⟩, hp'.2⟩

/-- **Updates in save normal form compose in save normal form**: pushed in
at a state whose storage is a chain of saves on `storage`, an update whose
storage elements are chains (with paths and values that have a reading)
leaves one. -/
theorem Upd.toLS_okNF {ρ₀ : SymS C Γ} (hρ₀ : ρ₀.OkNF) : {Δ : Ctx} → {U : Upd C Γ Δ} →
    U.ElimOk → U.NF → ∀ {q : SymS C Δ × LTm C (.val .bool)}, U.toLS ρ₀ = some q → q.1.OkNF := by
  intro Δ U hU hN q h
  rw [Upd.toLS_eq_toLSM] at h
  induction U with
  | nil =>
    simp only [Upd.toLSM, Option.some.injEq] at h
    subst h; exact hρ₀
  | snoc U e ih =>
    simp only [Upd.toLSM, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨p, hp, r, hr, rfl⟩ := h
    exact (hU.2.toLS_nf hρ₀ hN.2 (ih hU.1 hN.1 hp) hr : r.1.OkNF)
  | decl U x r ih =>
    simp only [Upd.toLSM, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨p, hp, b, hb, rfl⟩ := h
    have hb' := Rhs.ElimOk.toL hρ₀.ok hU.2 hb
    exact (ih hU.1 hN hp).push (fun y hy => by cases hy; exact hb'.1)
  | pop U h' ih =>
    simp only [Upd.toLSM, Option.map_eq_some_iff] at h
    obtain ⟨p, hp, rfl⟩ := h
    have hp' := ih hU hN hp
    exact ⟨hp'.1.drop h', hp'.2⟩
  | drop U h' ih =>
    simp only [Upd.toLSM, Option.map_eq_some_iff] at h
    obtain ⟨p, hp, rfl⟩ := h
    have hp' := ih hU hN hp
    exact ⟨hp'.1.thin h', hp'.2⟩

end Upd

/-! ## Formulas pushed in -/

section Fml

/-- What follows a fragment program: fragment programs and scope ends. -/
def Frames.Frag : {Γ Γ₀ : Ctx} → Frames C Γ Γ₀ → Prop
  | _, _, .nil => True
  | _, _, .seq ω κ => ω.Frag = true ∧ κ.Frag
  | _, _, .pop _ _ κ => κ.Frag
  | _, _, .drop _ κ => κ.Frag

/-- **A formula of the fragment**: its programs in the fragment
(`Prog.Frag`), its updates save-like with a reading, its equations with a
reading, no `wt`. -/
def Fml.Frag : {Γ : Ctx} → Fml C Γ → Prop
  | _, .tt => True
  | _, .eq a b => a.ElimOk ∧ b.ElimOk
  | _, .wellFormed _ => False
  | _, .not φ => φ.Frag
  | _, .and φ ψ => φ.Frag ∧ ψ.Frag
  | _, .imp φ ψ => φ.Frag ∧ ψ.Frag
  | _, .upd _ U φ => (U.SaveLike ∧ U.ElimOk) ∧ φ.Frag
  | _, .modal _ P κ φ => P.Frag = true ∧ κ.Frag ∧ φ.Frag
  | _, .havoc φ => φ.Frag
  | _, .all _ _ φ => φ.Frag
  | _, .bind _ _ _ φ => φ.Frag
  | _, .anon _ φ | _, .allocAll _ _ φ => φ.Frag

variable {Γ : Ctx}

theorem Decide.fullL_elimable {st : LTm C .st} {E : Ty} {q : LTm C (.path (.ref (.array E)))}
    (hs : st.Elimable) (hq : q.Elimable) : (fullL st q).Elimable :=
  .app2 rfl (.app2 rfl hs hq) (.app0 rfl)

theorem Tm.ElimOk.exhL {ρ : SymS C Γ} (hρ : ρ.Ok) {s : Srt} {t : Tm C Γ s} (ht : t.ElimOk)
    {X : LTm C (.val .bool)} (h : t.exhL ρ = some X) : X.Elimable := by
  cases ht with
  | app2 ho hx hy =>
    simp only [Tm.exhL] at h
    unfold Op2.exhL at h
    split at h
    all_goals first
      | (simp only [reduceCtorEq] at h)
      | (simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
         obtain ⟨st', hs, q', hq, rfl⟩ := h
         exact Decide.fullL_elimable (hx.toL hρ hs) (hy.toL hρ hq))
  | @app3 _ _ _ _ o x y z ho hx hy hz =>
    simp only [Tm.exhL] at h
    cases o <;> simp only [Op3.exhL, reduceCtorEq] at h
    simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨st', hs, q', hq, v', hv, rfl⟩ := h
    exact .kite (Decide.fullL_elimable (hx.toL hρ hs) (hy.toL hρ hq)) Decide.tt_elimable
      (Decide.seqL_elimable (hz.toL hρ hv) Decide.tt_elimable) (.app0 rfl)
  | _ => simp only [Tm.exhL, reduceCtorEq] at h

theorem Upd.ElimOk.exhL {ρ : SymS C Γ} (hρ : ρ.Ok) {Δ : Ctx} {U : Upd C Γ Δ} (hU : U.ElimOk)
    {X : LTm C (.val .bool)} (h : U.exhL ρ = some X) : X.Elimable := by
  unfold Upd.exhL at h
  split at h
  · exact Tm.ElimOk.exhL hρ hU.2 h
  · unfold pushLocalExhL at h
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨X', hX, b, hb, rfl⟩ := h
    exact Decide.seqL_elimable (Rhs.ElimOk.toL hρ hU.2 hb).2 (Tm.ElimOk.exhL hρ hU.1.2 hX)
  · simp only [reduceCtorEq] at h

theorem Decide.guardM_elimable (m : Modality) {X : Option (LTm C (.val .bool))}
    (hX : ∀ x, X = some x → x.Elimable) {g : LTm C (.val .bool)} (hg : g.Elimable) {φ : LFml C}
    (hφ : φ.Elimable) : (guardM m X g φ).Elimable := by
  cases m with
  | box => exact ⟨⟨hg, hg⟩, hφ⟩
  | diamond =>
    cases X with
    | none => exact ⟨⟨hg, hg⟩, hφ⟩
    | some x =>
      exact ⟨⟨(show (LFml.eq x LTm.tt).Elimable from ⟨hX x rfl, Decide.tt_elimable⟩), hg, hg⟩,
        ⟨hg, hg⟩, hφ⟩

theorem Fml.eqAt_elimable (pos : Bool) {p : PrimTy} (a b : Tm C Γ (.val p))
    {a' b' : LTm C (.val p)} (ha : a'.Elimable) (hb : b'.Elimable) :
    (Fml.eqAt pos a b a' b').Elimable := by
  unfold Fml.eqAt
  split
  · split
    · exact ⟨ha, hb⟩
    · exact ⟨⟨⟨ha, ha⟩, ⟨hb, hb⟩, ⟨ha, hb⟩⟩, ⟨⟨ha, ha⟩, ⟨hb, hb⟩⟩, ⟨⟨hb, hb⟩, ⟨ha, ha⟩⟩⟩
  · split
    · exact ⟨ha, hb⟩
    · exact ⟨⟨ha, ha⟩, ⟨hb, hb⟩, ⟨ha, hb⟩⟩

/-- **A fragment formula pushed in at an elimable state is elimable.** -/
theorem Fml.Frag.toLS {φ : Fml C Γ} (hφ : φ.Frag) :
    ∀ {pos : Bool} {ρ : SymS C Γ}, ρ.Ok → ∀ {ψ : LFml C}, φ.toLS pos ρ = some ψ → ψ.Elimable := by
  intro pos ρ hρ ψ h
  rw [Fml.toLS_eq_toLSM] at h
  induction φ generalizing pos ψ with
  | tt =>
    simp only [Fml.toLSM, Option.some.injEq] at h; subst h; exact trivial
  | eq a b =>
    simp only [Fml.toLSM, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨a', ha, b', hb, rfl⟩ := h
    exact Fml.eqAt_elimable _ a b (hφ.1.toL hρ ha) (hφ.2.toL hρ hb)
  | wellFormed s => exact hφ.elim
  | not φ ih =>
    simp only [Fml.toLSM, Option.map_eq_some_iff] at h
    obtain ⟨φ', h', rfl⟩ := h
    exact (ih hφ hρ h' : φ'.Elimable)
  | and φ χ ihφ ihχ =>
    simp only [Fml.toLSM, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨φ', h1, χ', h2, rfl⟩ := h
    exact ⟨ihφ hφ.1 hρ h1, ihχ hφ.2 hρ h2⟩
  | imp φ χ ihφ ihχ =>
    simp only [Fml.toLSM, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨φ', h1, χ', h2, rfl⟩ := h
    exact ⟨ihφ hφ.1 hρ h1, ihχ hφ.2 hρ h2⟩
  | upd m U φ ih =>
    simp only [Fml.toLSM] at h
    split at h
    · simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨q, hq, φ', h', rfl⟩ := h
      have hq' := hφ.1.2.toLS hρ hq
      exact Decide.guardM_elimable m (fun x hx => hφ.1.2.exhL hρ hx) hq'.2 (ih hφ.2 hq'.1 h')
    · simp only [Option.some.injEq] at h; subst h; exact trivial
  | modal m P κ φ =>
    simp only [Fml.toLSM] at h
    split at h <;> (simp only [Option.some.injEq] at h; subst h; exact trivial)
  | havoc φ ih =>
    simp only [Fml.toLSM] at h
    split at h
    · simp only [reduceCtorEq] at h
    · simp only [Option.some.injEq] at h; subst h; exact trivial
  | all x p φ ih =>
    simp only [Fml.toLSM, Option.map_eq_some_iff] at h
    obtain ⟨φ', h', rfl⟩ := h
    exact (ih hφ (hρ.pushQ p) h' : φ'.Elimable)
  | bind m x t φ ih =>
    simp only [Fml.toLSM] at h
    split at h
    · simp only [Option.map_eq_some_iff] at h
      obtain ⟨φ', h', rfl⟩ := h
      have := ih hφ (hρ.pushB t) h'
      unfold LFml.allB
      split
      · exact this
      · exact this
    · simp only [reduceCtorEq] at h
  | anon xs φ ih =>
    simp only [Fml.toLSM] at h
    split at h
    · simp only [reduceCtorEq] at h
    · simp only [Option.some.injEq] at h; subst h; exact trivial

/-- **Its reduction mentions no storage**: every read of a write
eliminates to the observation atoms. -/
theorem Fml.Frag.reduceS_stoFree {φ : Fml C []} (hφ : φ.Frag) {ψ : LFml C}
    (h : φ.reduceS = some ψ) : ψ.StoFree := by
  simp only [Fml.reduceS, Option.map_eq_some_iff] at h
  obtain ⟨ψ', h', rfl⟩ := h
  exact LFml.elim_stoFree ψ' (hφ.toLS SymS.init_okNF.ok h')

end Fml

/-! ## A memory-free expression lowers to a term with a reading -/

section Lower

variable {Γ : Ctx}

theorem Simple.lower_elimOk {p : PrimTy} (s : Simple C Γ p) : s.lower.ElimOk := by
  cases s with
  | lit n h => exact .app0 rfl
  | bool b => exact .app0 rfl
  | «local» i => exact .pvV i
  | env k hp => exact Tm.ElimOk.castV _ (.app0 rfl)

mutual

theorem SPath.lower_elimOk : {T : Ty} → (b : SPath C Γ T) → b.MemFree = true → b.lower.ElimOk
  | _, .alias i, _ => .pvP i
  | _, .loc l, h => Loc.lower_elimOk l h

theorem Loc.lower_elimOk : {T : Ty} → (l : Loc C Γ T) → l.MemFree = true → l.lower.ElimOk
  | _, .root _ _, _ => .app0 rfl
  | _, .field b _ _, h => .app1 rfl (SPath.lower_elimOk b h)
  | _, .index _ b i, h => by
    simp only [Loc.MemFree, Bool.and_eq_true] at h
    exact .app2 rfl (SPath.lower_elimOk b h.1) (Val.lower_elimOk i h.2)

theorem Val.lower_elimOk : {p : PrimTy} → (v : Val C Γ p) → v.MemFree = true → v.lower.ElimOk
  | _, .simple s, _ => Simple.lower_elimOk s
  | _, .read l, h => .app2 rfl (.app0 rfl) (Loc.lower_elimOk l h)
  | _, .binop _ _ hq a b, h => by
    simp only [Val.MemFree, Bool.and_eq_true] at h
    exact Tm.ElimOk.castV hq (.app2 rfl (Val.lower_elimOk a h.1) (Val.lower_elimOk b h.2))
  | _, .unop _ _ hq a, h => Tm.ElimOk.castV hq (.app1 rfl (Val.lower_elimOk a h))
  | _, .ternary c a b, h => by
    simp only [Val.MemFree, Bool.and_eq_true] at h
    exact .app3 rfl (Val.lower_elimOk c h.1.1) (Val.lower_elimOk a h.1.2) (Val.lower_elimOk b h.2)
  | _, .readMem _, h => absurd h Bool.false_ne_true
  | _, .len b hp, h => Tm.ElimOk.castV hp.symm (.app2 rfl (.app0 rfl) (SPath.lower_elimOk b h))
  | _, .mlen _ _, h => absurd h Bool.false_ne_true
  | _, .keccak _ _, h => absurd h Bool.false_ne_true
  | _, .modular _ a b k, h => by
    simp only [Val.MemFree, Bool.and_eq_true] at h
    exact .app3 rfl (Val.lower_elimOk a h.1.1) (Val.lower_elimOk b h.1.2) (Val.lower_elimOk k h.2)

end

theorem Src.lower_elimOk {T : Ty} (r : Src C Γ T) (h : r.Frag = true) : r.lower.ElimOk := by
  cases r with
  | val v => exact .app1 rfl (Val.lower_elimOk v h)
  | copy p _ => exact .app2 rfl (.app0 rfl) (SPath.lower_elimOk p h)
  | fixedCopy p _ _ => exact .app1 rfl (.app2 rfl (.app0 rfl) (SPath.lower_elimOk p h))
  | copyMem _ => exact absurd h Bool.false_ne_true

end Lower

/-! ## The expansion keeps a reading -/

section Expand

variable {Γ : Ctx}

theorem Tm.leafPath_elimOk {s : Tm C Γ .st} (hs : s.ElimOk) :
    {T U : Ty} → {p : Tm C Γ (.path T)} → p.ElimOk → (l : Path T U) → (Tm.leafPath s p l).ElimOk
  | _, _, _, hp, .nil => hp
  | _, _, _, hp, .field _ l => Tm.leafPath_elimOk hs (.app1 rfl hp) l
  | _, _, _, hp, .atF _ l => Tm.leafPath_elimOk hs (.app3 rfl hs hp (.app0 rfl)) l
  | _, _, _, hp, .at _ l => Tm.leafPath_elimOk hs (.app3 rfl hs hp (.app0 rfl)) l
  | _, _, _, hp, .key _ l => Tm.leafPath_elimOk hs (.app3 rfl hs hp (.app0 rfl)) l

theorem Tm.saveLeaves_elimOk {s : Tm C Γ .st} (hs : s.ElimOk) {T : Ty} {p : Tm C Γ (.path T)}
    (hp : p.ElimOk) {val : (l : Leaf T) → Tm C Γ (.sv (.prim l.1))} (hv : ∀ l, (val l).ElimOk) :
    (ls : List (Leaf T)) → {acc : Tm C Γ .st} → acc.ElimOk → (Tm.saveLeaves s p val ls acc).ElimOk
  | [], _, h => h
  | l :: ls, _, h =>
    Tm.saveLeaves_elimOk hs hp hv ls (.app3 rfl h (Tm.leafPath_elimOk hs hp l.2) (hv l))

/-- **The expansion keeps a reading.** -/
theorem Tm.expand?_elimOk {t t' : Tm C Γ .st} (h : t.expand? = some t') (ht : t.ElimOk) :
    t'.ElimOk := by
  obtain ⟨k, hk⟩ := Tm.expand?_kind h
  cases k
  · obtain ⟨T, s, p, rfl, rfl, -⟩ := Tm.delAtExpand?_some hk
    cases ht with
    | app2 _ hs hp => exact Tm.saveLeaves_elimOk hs hp (fun _ => .app1 rfl (.app0 rfl)) _ hs
  · obtain ⟨T, s, p, q, rfl, rfl, -⟩ := Tm.copyExpand?_some hk
    cases ht with
    | app3 _ hs hp hv =>
      cases hv with
      | app2 _ _ hq =>
        exact Tm.saveLeaves_elimOk hs hp
          (fun l => .app1 rfl (.app2 rfl hs (Tm.leafPath_elimOk hs hq l.2))) _ hs
  · obtain ⟨P, s, p, x, rfl, rfl, -⟩ := Tm.pushExpand?_some hk
    cases ht with
    | app3 _ hs hp hv => exact .app3 rfl (.app2 rfl hs hp) (.app2 rfl hs hp) hv
  · obtain ⟨P, s, p, rfl, rfl, -⟩ := Tm.popExpand?_some hk
    cases ht with
    | app2 _ hs hp =>
      exact .app2 rfl (.app3 rfl hs (.app3 rfl hs hp (.app2 rfl (.app2 rfl hs hp) (.app0 rfl)))
        (.app1 rfl (.app0 rfl))) hp

theorem Tm.expand_getD_elimOk {t : Tm C Γ .st} (ht : t.ElimOk) : ((t.expand?).getD t).ElimOk := by
  cases h : t.expand? with
  | none => exact ht
  | some t' => exact Tm.expand?_elimOk h ht

end Expand

/-! ## On the fragment, a rule writes terms with a reading -/

section Premises

variable {Γ : Ctx}

/-- **A premise with a reading**: every update it writes has one, every
condition it states is a fragment formula.  What it runs next is
`Premise.SaveLike`'s. -/
def Premise.ElimOk {Γ' : Ctx} : Premise C Γ Γ' → Prop
  | .update U => U.ElimOk
  | .updates U V => U.ElimOk ∧ V.ElimOk
  | .unfold .. => True
  | .bind .. => True
  | .split _ c c' _ _ => c.Frag ∧ c'.Frag
  | .check c => c.Frag
  | .done _ => True
  | .branches _ => False
  | .cases fs us => (∀ φ ∈ fs, φ.Frag) ∧ ∀ U ∈ us, U.ElimOk
  | .inv .. => False
  | .inline .. => True
  | .guardedUpdates c U V => c.Frag ∧ U.ElimOk ∧ V.ElimOk

theorem Upd.ElimOk.stores {Δ : Ctx} :
    {U : Upd C Γ Δ} → U.ElimOk → ∀ t ∈ U.stores, t.ElimOk
  | .nil, _, t, ht => absurd ht List.not_mem_nil
  | .snoc U e, h, t, ht => by
    cases e with
    | storage s =>
      simp only [Upd.stores, List.mem_append, List.mem_singleton] at ht
      rcases ht with ht | rfl
      · exact Upd.ElimOk.stores h.1 t ht
      · exact h.2
    | «local» i r => exact Upd.ElimOk.stores h.1 t ht
    | _ => exact h.2.elim
  | .decl U _ _, h, t, ht => Upd.ElimOk.stores (U := U) h.1 t ht
  | .pop U _, h, t, ht => Upd.ElimOk.stores (U := U) h t ht
  | .drop U _, h, t, ht => Upd.ElimOk.stores (U := U) h t ht

theorem Premise.ElimOk.upds {Γ' : Ctx} {P : Premise C Γ Γ'} (h : P.ElimOk) :
    ∀ U ∈ P.upds, U.2.2.ElimOk := by
  intro W hW
  cases P with
  | update U =>
    simp only [Premise.upds, List.mem_singleton] at hW; subst hW; exact h
  | updates U V =>
    simp only [Premise.upds, List.mem_cons, List.not_mem_nil, or_false] at hW
    rcases hW with rfl | rfl
    · exact h.1
    · exact h.2
  | guardedUpdates c U V =>
    simp only [Premise.upds, List.mem_cons, List.not_mem_nil, or_false] at hW
    rcases hW with rfl | rfl
    · exact h.2.1
    · exact h.2.2
  | cases fs us =>
    simp only [Premise.upds, List.mem_map] at hW
    obtain ⟨U, hU, rfl⟩ := hW
    exact h.2 U hU
  | inv => exact h.elim
  | _ => simp only [Premise.upds, List.not_mem_nil] at hW

theorem Premise.elimOk_setLocal {p : PrimTy} (i : Idx Γ (.val p)) (v : Val C Γ p)
    (hv : v.MemFree = true) : (Premise.setLocal i v).ElimOk := ⟨trivial, Val.lower_elimOk v hv⟩

theorem Premise.elimOk_save {T : Ty} (l : Loc C Γ T) (r : Src C Γ T) (hl : l.MemFree = true)
    (hr : r.Frag = true) : (Premise.save l r).ElimOk :=
  ⟨trivial, .app3 rfl (.app0 rfl) (Loc.lower_elimOk l hl) (Src.lower_elimOk r hr)⟩

theorem Premise.elimOk_delAt {T : Ty} (l : Loc C Γ T) (hl : l.MemFree = true) :
    (Premise.delAt l).ElimOk :=
  ⟨trivial, .app2 rfl (.app0 rfl) (Loc.lower_elimOk l hl)⟩

theorem Premise.elimOk_path {R : RefTy} (i : Idx Γ (.alias R)) {q : Tm C Γ (.path (.ref R))}
    (hq : q.ElimOk) : (Premise.upd1 (.local i (.path q))).ElimOk := ⟨trivial, hq⟩

theorem Fml.isBool_frag {t : Tm C Γ (.val .bool)} (ht : t.ElimOk) (b : Bool) :
    (Fml.isBool t b).Frag := ⟨ht, .app0 rfl⟩

end Premises

section Holes

variable (k : Nat) {Γ : Ctx}

theorem SHole.readStep_elimOk {T : Ty} (lhs : SHole C Γ T)
    {root : (r : Name) → C.rootType r = some T → Premise C Γ Γ}
    {field : {s : Name} → SPath C Γ (.struct s) → (f : Name) → C.fieldType s f = some T →
      Premise C Γ Γ}
    {index : {R : RefTy} → {kp : PrimTy} → IndexTy R kp T → SPath C Γ (.ref R) →
      Simple C Γ kp → Premise C Γ Γ}
    (hr : ∀ r h, (root r h).ElimOk)
    (hf : ∀ (s : Name) (b : SPath C Γ (.struct s)) f h, b.MemFree = true → (field b f h).ElimOk)
    (hi : ∀ (R : RefTy) (kp : PrimTy) (it : IndexTy R kp T) (b : SPath C Γ (.ref R)) ie,
      b.MemFree = true → (index it b ie).ElimOk)
    (l : Loc C Γ T) (hm : l.MemFree = true) : (lhs.readStep k root field index l).ElimOk := by
  cases l with
  | root r h => exact hr r h
  | field b f h =>
    simp only [Loc.MemFree] at hm
    simp only [SHole.readStep]
    split
    · exact hf _ b f h hm
    · trivial
  | index it b i =>
    simp only [Loc.MemFree, Bool.and_eq_true] at hm
    simp only [SHole.readStep]
    split
    · cases i with
      | simple ie => exact hi _ _ it b ie hm.1
      | _ => trivial
    · trivial

theorem ternaryStep_elimOk {p : PrimTy} (lhs : VHole C Γ p) (c : Val C Γ .bool) (a b : Val C Γ p) :
    (ternaryStep k lhs c a b).ElimOk := by
  cases c <;> trivial

theorem VHole.step_elimOk {p : PrimTy} (lhs : VHole C Γ p) {simple : Simple C Γ p → Premise C Γ Γ}
    (hs : ∀ se, (simple se).ElimOk) (e : Val C Γ p) : (lhs.step k simple e).ElimOk := by
  cases e with
  | simple se => exact hs se
  | ternary c a b => exact ternaryStep_elimOk k lhs c a b
  | _ => trivial

theorem VHole.lower_elimOk {p : PrimTy} (lhs : VHole C Γ p) {other : Premise C Γ Γ}
    (ho : other.ElimOk) (e : Val C Γ p) : (lhs.lower k other e).ElimOk := by
  cases e with
  | ternary c a b => exact ternaryStep_elimOk k lhs c a b
  | _ => exact ho

end Holes

section Arms

variable (k : Nat) {Γ : Ctx}

theorem copyStep_elimOk {R : RefTy} (l : Loc C Γ (.ref R)) (hm : (Ty.ref R).mapFree = true)
    (hl : l.MemFree = true) (q : SPath C Γ (.ref R)) (hq : q.MemFree = true) :
    (copyStep k l hm q).ElimOk := by
  cases q with
  | alias y => exact Premise.elimOk_save _ _ hl rfl
  | loc l' =>
    apply SHole.readStep_elimOk k (SHole.copy l hm)
    · intro r h; exact Premise.elimOk_save _ _ hl hq
    · intro s b f h hb; trivial
    · intro R kp it b ie hb; trivial
    · exact hq

theorem assignStep_elimOk {T : Ty} (l : Loc C Γ T) (r : Src C Γ T) (hl : l.MemFree = true)
    (hr : r.Frag = true) : (assignStep k l r).ElimOk := by
  cases r with
  | copyMem q => exact absurd hr Bool.false_ne_true
  | fixedCopy q shape hm => cases l <;> exact Premise.elimOk_save _ _ hl hr
  | val e =>
    cases l with
    | root r h => exact VHole.step_elimOk k _ (fun _ => Premise.elimOk_save _ _ rfl rfl) e
    | field b f h =>
      simp only [assignStep]
      split
      · exact VHole.step_elimOk k _ (fun _ => Premise.elimOk_save _ _ hl rfl) e
      · exact VHole.lower_elimOk k _ (by trivial) e
    | index it b i =>
      simp only [Loc.MemFree, Bool.and_eq_true] at hl
      simp only [assignStep]
      split
      · cases i with
        | simple ie =>
          exact VHole.step_elimOk k _ (fun _ => Premise.elimOk_save _ _
            (by simp only [Loc.MemFree, hl.1, Val.MemFree, Bool.and_self]) rfl) e
        | _ => exact VHole.lower_elimOk k _ (by trivial) e
      · exact VHole.lower_elimOk k _ (by trivial) e
  | copy q hm =>
    cases l with
    | root r h =>
      cases q with
      | alias j => exact Premise.elimOk_save _ _ rfl rfl
      | loc l' =>
        apply SHole.readStep_elimOk k (SHole.copy (.root r h) hm)
        · intro _ _; exact Premise.elimOk_save _ _ rfl hr
        · intro _ _ _ _ _; exact Premise.elimOk_save _ _ rfl hr
        · intro _ _ _ _ _ _; exact Premise.elimOk_save _ _ rfl hr
        · exact hr
    | field b f h =>
      simp only [assignStep]
      split
      · exact copyStep_elimOk k (.field b f h) hm hl q hr
      · trivial
    | index it b i =>
      simp only [Loc.MemFree, Bool.and_eq_true] at hl
      simp only [assignStep]
      split
      · cases i with
        | simple ie =>
          exact copyStep_elimOk k _ hm (by simp only [Loc.MemFree, hl.1, Val.MemFree,
            Bool.and_self]) q hr
        | _ => trivial
      · trivial

theorem shortStep_elimOk {p p' : PrimTy} (i : Idx Γ (.val p)) (op : BinOp)
    (ha : op.accepts p' = true) (hq : op.ret p' = p) (a : Simple C Γ p') (b : Val C Γ p') :
    (shortStep i op ha hq a b).ElimOk := by
  unfold shortStep
  split <;> trivial

theorem localStep_elimOk {p : PrimTy} (i : Idx Γ (.val p)) (v : Val C Γ p)
    (hv : v.MemFree = true) : (localStep k i v).ElimOk := by
  cases v with
  | simple s => exact Premise.elimOk_setLocal i _ rfl
  | read l =>
    apply SHole.readStep_elimOk k (SHole.local i)
    · intro r h; exact Premise.elimOk_setLocal i _ rfl
    · intro s b f h hb; exact Premise.elimOk_setLocal i _ hb
    · intro R kp it b ie hb
      exact Premise.elimOk_setLocal i _ (by simp only [Val.MemFree, Loc.MemFree, hb,
        Bool.and_self])
    · exact hv
  | binop op ha hq a b =>
    cases a with
    | simple a =>
      cases b with
      | simple b => exact Premise.elimOk_setLocal i _ rfl
      | _ =>
        simp only [localStep]
        split
        · exact shortStep_elimOk i op ha hq a _
        · trivial
    | _ => trivial
  | unop op ha hq a =>
    cases a with
    | simple a => exact Premise.elimOk_setLocal i _ rfl
    | _ => trivial
  | ternary c a b => exact ternaryStep_elimOk k (.local i) c a b
  | readMem l => exact absurd hv Bool.false_ne_true
  | len b hp =>
    simp only [localStep]
    split
    · exact Premise.elimOk_setLocal i _ hv
    · trivial
  | mlen b hp => exact absurd hv Bool.false_ne_true
  | modular op a b n => exact Premise.elimOk_setLocal i _ hv
  | keccak b hp => exact absurd hv Bool.false_ne_true

theorem rebindStep_elimOk {R : RefTy} (i : Idx Γ (.alias R)) (r : ARhs C Γ R)
    (hr : r.MemFree = true) : (rebindStep k i r).ElimOk := by
  cases r with
  | path q =>
    simp only [ARhs.MemFree] at hr
    cases q with
    | alias j => exact Premise.elimOk_path i (.pvP j)
    | loc l =>
      apply SHole.readStep_elimOk k (SHole.rebind i)
      · intro r h; exact Premise.elimOk_path i (.app0 rfl)
      · intro s b f h hb; exact Premise.elimOk_path i (.app1 rfl (SPath.lower_elimOk b hb))
      · intro R kp it b ie hb
        exact Premise.elimOk_path i (.app2 rfl (SPath.lower_elimOk b hb) (Simple.lower_elimOk ie))
      · exact hr
  | push b hd =>
    simp only [ARhs.MemFree] at hr
    have hb := SPath.lower_elimOk b hr
    simp only [rebindStep]
    split
    · split
      · exact ⟨⟨trivial, .app2 rfl (.app0 rfl) hb⟩, .app1 rfl hb⟩
      · exact ⟨⟨trivial, .app2 rfl (.app0 rfl) hb⟩, .app1 rfl hb⟩
    · trivial

theorem deleteStep_elimOk {T : Ty} (l : Loc C Γ T) (hl : l.MemFree = true) :
    (deleteStep k l).ElimOk := by
  cases l with
  | root r h => exact Premise.elimOk_delAt _ rfl
  | field b f h =>
    simp only [deleteStep]
    split
    · exact Premise.elimOk_delAt _ hl
    · trivial
  | index it b i =>
    simp only [Loc.MemFree, Bool.and_eq_true] at hl
    simp only [deleteStep]
    split
    · cases i with
      | simple ie =>
        exact Premise.elimOk_delAt _ (by simp only [Loc.MemFree, hl.1, Val.MemFree,
          Bool.and_self])
      | _ => trivial
    · trivial

theorem pushStep_elimOk {E : Ty} (b : SPath C Γ (.array E)) (v : Option (Src C Γ E))
    (hd : (v.isSome || E.defaultOkS) = true) (hb : b.MemFree = true)
    (hv : pushArgFrag v = true) : (pushStep k b v hd).ElimOk := by
  have hb' := SPath.lower_elimOk b hb
  unfold pushStep
  split
  · rcases v with _ | (e | _ | _ | _)
    · simp only
      split
      · exact ⟨trivial, .app2 rfl (.app0 rfl) hb'⟩
      · split <;> exact ⟨trivial, .app2 rfl (.app0 rfl) hb'⟩
    · cases e with
      | simple se => exact ⟨trivial, .app3 rfl (.app0 rfl) hb' (.app1 rfl (Simple.lower_elimOk se))⟩
      | _ => trivial
    all_goals exact absurd hv Bool.false_ne_true
  · trivial

theorem popStep_elimOk {E : Ty} (b : SPath C Γ (.array E)) (hb : b.MemFree = true) :
    (popStep k b).ElimOk := by
  have hb' := SPath.lower_elimOk b hb
  unfold popStep
  split
  · split
    · exact ⟨trivial, .app2 rfl (.app0 rfl) hb'⟩
    · exact ⟨trivial, .app2 rfl (.app0 rfl) hb'⟩
  · trivial

theorem iteStep_elimOk {Γ₁ Γ₂ : Ctx} (c : Val C Γ .bool) (thn : Prog C Γ Γ₁)
    (els : Prog C Γ Γ₂) : (iteStep k c thn els).ElimOk := by
  cases c with
  | simple s =>
    exact ⟨Fml.isBool_frag (Simple.lower_elimOk s) _, Fml.isBool_frag (Simple.lower_elimOk s) _⟩
  | _ => trivial

theorem requireStep_elimOk (c : Val C Γ .bool) : (requireStep k c).ElimOk := by
  cases c with
  | simple s =>
    exact ⟨Fml.isBool_frag (Simple.lower_elimOk s) _, Fml.isBool_frag (Simple.lower_elimOk s) _⟩
  | _ => trivial

theorem assertStep_elimOk (c : Val C Γ .bool) : (assertStep k c).ElimOk := by
  cases c with
  | simple s => exact Fml.isBool_frag (Simple.lower_elimOk s) _
  | _ => trivial

end Arms

section Step

variable (k : Nat) (m : Modality)

/-- **On the fragment, every term a rule writes has a reading.** -/
theorem Stmt.step_elimOk {Γ Γ' : Ctx} (s : Stmt C Γ Γ') (h : s.Frag = true) :
    (s.step k m).ElimOk := by
  cases s with
  | assign l r =>
    simp only [Stmt.Frag, Bool.and_eq_true] at h
    exact assignStep_elimOk k l r h.1 h.2
  | rebind i r => exact rebindStep_elimOk k i r h
  | assignLocal i v => exact localStep_elimOk k i v h
  | declLocal p x init =>
    cases init with
    | none => exact ⟨trivial, .app0 rfl⟩
    | some e => trivial
  | declStorage R x init =>
    cases init with
    | none => simp only [Stmt.Frag, Option.any_none, Bool.false_eq_true] at h
    | some r => trivial
  | push b v hd =>
    simp only [Stmt.Frag, Bool.and_eq_true] at h
    exact pushStep_elimOk k b v hd h.1 h.2
  | pop b =>
    simp only [Stmt.Frag, Bool.and_eq_true] at h
    exact popStep_elimOk k b h.1
  | delete l =>
    simp only [Stmt.Frag, Bool.and_eq_true] at h
    exact deleteStep_elimOk k l h.2
  | ite c thn els => exact iteStep_elimOk k c thn els
  | require c => exact requireStep_elimOk k c
  | assert c => exact assertStep_elimOk k c
  | revert => cases m <;> trivial
  | assumeFalse => trivial
  | block body => trivial
  | _ => simp only [Stmt.Frag, Bool.false_eq_true] at h

/-- **The bridge, per step**: on the fragment, every storage right-hand
side a rule writes, expanded, is in save normal form with a reading, so
pushed in at a state whose storage is in save normal form it is in
`LTm.SaveNF`, and a word read of it eliminates storage-free. -/
theorem Stmt.step_toL_saveNF {Γ Γ' : Ctx} (s : Stmt C Γ Γ') (h : s.Frag = true) :
    ∀ U ∈ (s.step k m).upds, ∀ t ∈ U.2.2.stores, ∀ (ρ : SymS C U.1), ρ.OkNF →
      ∀ l, ((t.expand?).getD t).toL ρ = some l → l.SaveNF := by
  intro U hU t ht ρ hρ l hl
  have hS := Stmt.step_saveNF k m s h U hU t ht
  have hE : t.ElimOk := Upd.ElimOk.stores (Premise.ElimOk.upds (Stmt.step_elimOk k m s h) U hU) t ht
  exact Tm.SaveNF.toL hρ hS (Tm.expand_getD_elimOk hE) hl

end Step

/-! ## The strategy keeps the fragment -/

section Strategy

theorem Frames.exit_frag (m : Modality) {Γ Γ₀ : Ctx} (κ : Frames C Γ Γ₀) (hκ : κ.Frag)
    {φ : Fml C Γ₀} (hφ : φ.Frag) : (κ.exit m φ).Frag := by
  induction κ with
  | nil => exact hφ
  | seq ω κ ih =>
    cases ω with
    | nil => exact ih hκ.2 hφ
    | cons s ω => exact ⟨hκ.1, hκ.2, hφ⟩
  | pop _ _ κ ih => exact ⟨⟨trivial, trivial⟩, ih hκ hφ⟩
  | drop _ κ ih => exact ⟨⟨trivial, trivial⟩, ih hκ hφ⟩

theorem Fml.modalK_frag (m : Modality) {Γ Γ₁ Γ₀ : Ctx} (ω : Prog C Γ Γ₁) (κ : Frames C Γ₁ Γ₀)
    {φ : Fml C Γ₀} (hω : ω.Frag = true) (hκ : κ.Frag) (hφ : φ.Frag) :
    (Fml.modalK m ω κ φ).Frag := by
  cases ω with
  | nil => exact Frames.exit_frag m κ hκ hφ
  | cons s ω => exact ⟨hω, hκ, hφ⟩

theorem Fml.conj_frag {Γ : Ctx} : (fs : List (Fml C Γ)) → (∀ φ ∈ fs, φ.Frag) → (Fml.conj fs).Frag
  | [], _ => trivial
  | [φ], h => h φ (List.mem_singleton.mpr rfl)
  | φ :: ψ :: fs, h =>
    ⟨h φ List.mem_cons_self, Fml.conj_frag (ψ :: fs) fun χ hχ => h χ (List.mem_cons_of_mem _ hχ)⟩

/-- **A premise of the fragment in front of the rest is a fragment
formula.** -/
theorem Premise.fml_frag (m : Modality) {Γ Γ' Γ₁ Γ₀ : Ctx} (P : Premise C Γ Γ')
    (hS : P.SaveLike) (hE : P.ElimOk) (ω : Prog C Γ' Γ₁) (κ : Frames C Γ₁ Γ₀) {φ : Fml C Γ₀}
    (hω : ω.Frag = true) (hκ : κ.Frag) (hφ : φ.Frag) : (P.fml m ω κ φ).Frag := by
  cases P with
  | update U => exact ⟨⟨hS, hE⟩, Fml.modalK_frag m ω κ hω hκ hφ⟩
  | updates U V => exact ⟨⟨hS.1, hE.1⟩, ⟨hS.2, hE.2⟩, Fml.modalK_frag m ω κ hω hκ hφ⟩
  | unfold P h => exact ⟨hS, ⟨hω, hκ⟩, hφ⟩
  | bind x t P => exact ⟨hS, ⟨hω, hκ⟩, hφ⟩
  | split b c c' P Q =>
    exact ⟨⟨hE.1, Fml.modalK_frag m P _ hS.1 ⟨hω, hκ⟩ hφ⟩,
      ⟨hE.2, Fml.modalK_frag m Q _ hS.2 ⟨hω, hκ⟩ hφ⟩⟩
  | check c => exact ⟨⟨hE, Fml.modalK_frag m ω κ hω hκ hφ⟩, hE⟩
  | done b =>
    show (if b then Fml.tt else Fml.ff).Frag
    split <;> trivial
  | branches bs => exact hS.elim
  | cases fs us =>
    apply Fml.conj_frag
    intro χ hχ
    rcases List.mem_append.mp hχ with hχ | hχ
    · exact hE.1 χ hχ
    · obtain ⟨U, hU, rfl⟩ := List.mem_map.mp hχ
      exact ⟨⟨hS U hU, hE.2 U hU⟩, Fml.modalK_frag m ω κ hω hκ hφ⟩
  | inv => exact hS.elim
  | inline P h => exact ⟨hS, ⟨hω, hκ⟩, hφ⟩
  | guardedUpdates c U V =>
    exact ⟨⟨hE.1, ⟨hS.1, hE.2.1⟩, ⟨hS.2, hE.2.2⟩, Fml.modalK_frag m ω κ hω hκ hφ⟩,
      ⟨hE.1, by simp only [Prog.Frag, Stmt.Frag, hω, Bool.and_self], hκ, hφ⟩⟩

/-- **One step of the strategy keeps the fragment.** -/
theorem Fml.stepR_frag (k : Nat) {Γ : Ctx} {φ : Fml C Γ} (hφ : φ.Frag) :
    ∀ {ψ : Fml C Γ}, φ.stepR k = some ψ → ψ.Frag := by
  intro ψ h
  induction φ with
  | tt | eq | wellFormed | not => exact nomatch h
  | and φ χ ihφ ihχ =>
    change (match Fml.stepR k φ with
      | some φ' => some (Fml.and φ' χ)
      | none => (Fml.stepR k χ).map (Fml.and φ)) = some ψ at h
    split at h
    · rename_i φ' hφ'
      cases h; exact ⟨ihφ hφ.1 hφ', hφ.2⟩
    · obtain ⟨χ', hχ', rfl⟩ := Option.map_eq_some_iff.mp h
      exact ⟨hφ.1, ihχ hφ.2 hχ'⟩
  | imp a φ _ ih =>
    change (Fml.stepR k φ).map (Fml.imp a) = some ψ at h
    obtain ⟨φ', h', rfl⟩ := Option.map_eq_some_iff.mp h
    exact ⟨hφ.1, ih hφ.2 h'⟩
  | upd m U φ ih =>
    change (Fml.stepR k φ).map (Fml.upd m U) = some ψ at h
    obtain ⟨φ', h', rfl⟩ := Option.map_eq_some_iff.mp h
    exact ⟨hφ.1, ih hφ.2 h'⟩
  | modal m P κ φ =>
    cases P with
    | nil =>
      change some (κ.exit m φ) = some ψ at h
      cases h; exact Frames.exit_frag m κ hφ.2.1 hφ.2.2
    | cons s ω =>
      change some ((s.step k m).fml m ω κ φ) = some ψ at h
      cases h
      have hs : s.Frag = true ∧ ω.Frag = true := by
        simpa only [Prog.Frag, Bool.and_eq_true] using hφ.1
      exact Premise.fml_frag m _ (Stmt.step_saveLike k m s hs.1) (Stmt.step_elimOk k m s hs.1) ω κ
        hs.2 hφ.2.1 hφ.2.2
  | havoc φ ih =>
    change (Fml.stepR k φ).map Fml.havoc = some ψ at h
    obtain ⟨φ', h', rfl⟩ := Option.map_eq_some_iff.mp h
    exact (ih hφ h' : φ'.Frag)
  | all x p φ ih =>
    change (Fml.stepR k φ).map (Fml.all x p) = some ψ at h
    obtain ⟨φ', h', rfl⟩ := Option.map_eq_some_iff.mp h
    exact (ih hφ h' : φ'.Frag)
  | bind m x t φ ih =>
    change (Fml.stepR k φ).map (Fml.bind m x t) = some ψ at h
    obtain ⟨φ', h', rfl⟩ := Option.map_eq_some_iff.mp h
    exact (ih hφ h' : φ'.Frag)
  | anon xs φ ih =>
    change (Fml.stepR k φ).map (Fml.anon xs) = some ψ at h
    obtain ⟨φ', h', rfl⟩ := Option.map_eq_some_iff.mp h
    exact (ih hφ h' : φ'.Frag)

/-- **The strategy keeps the fragment**, however many steps it runs. -/
theorem symex_frag {Γ : Ctx} : (n : Nat) → {φ : Fml C Γ} → φ.Frag → (symex n φ).Frag
  | 0, _, h => h
  | n + 1, φ, h => by
    simp only [symex]
    split
    · rename_i ψ hψ
      exact symex_frag n (Fml.stepR_frag φ.fresh h hψ)
    · exact h

/-- **Every leaf of the strategy on a fragment formula reduces
storage-free**: its updates pushed in, every read of a write eliminates
to the observation atoms of the start. -/
theorem symex_reduceS_stoFree (n : Nat) {φ : Fml C []} (h : φ.Frag) {ψ : LFml C}
    (hψ : (symex n φ).reduceS = some ψ) : ψ.StoFree :=
  (symex_frag n h).reduceS_stoFree hψ

end Strategy

/-! ## Every storage element expanded at once -/

section ExpandAll

variable {Γ : Ctx}

/-- Every expansion, whichever kind fires, at a storage term's head
(`Tm.pickExpand` of all four kinds). -/
def Tm.pickExpandAll : {s : Srt} → Tm C Γ s → Option (Tm C Γ s)
  | .st, t => t.expand?
  | _, _ => none

theorem Tm.pickExpandAll_eq (σ : State C Γ) : PickEq Tm.pickExpandAll σ := by
  intro s t t' h
  cases s with
  | st => exact Tm.eval_expand? σ h
  | _ => cases h

theorem Tm.pickExpandAll_exh (σ : State C Γ) : PickExh Tm.pickExpandAll σ := by
  intro s t t' h
  cases s with
  | st =>
    obtain ⟨k, hk⟩ := Tm.expand?_kind h
    exact Tm.exhB_expandK? σ k hk
  | _ => cases h

/-- **Every storage element of an update expanded, under either modality**,
is an equivalence. -/
theorem holds_upd_expandAll_iff {m : Modality} {Δ : Ctx} {U : Upd C Γ Δ} {φ : Fml C Δ}
    (σ : State C Γ) :
    holds σ (.upd m (Upd.rwBy Tm.pickExpandAll U) φ) ↔ holds σ (.upd m U φ) :=
  Upd.rwBy_afterT σ (Tm.pickExpandAll_eq σ) (Tm.pickExpandAll_exh σ) m U _

theorem Tm.pickExpandAll_elimOk {s : Srt} {t t' : Tm C Γ s} (h : Tm.pickExpandAll t = some t')
    (ht : t.ElimOk) : t'.ElimOk := by
  cases s with
  | st => exact Tm.expand?_elimOk h ht
  | _ => cases h

theorem Tm.ElimOk.rwBy_expandAll {s : Srt} {t : Tm C Γ s} (ht : t.ElimOk) :
    (Tm.rwBy Tm.pickExpandAll t).ElimOk := by
  induction ht with
  | pvV i => exact .pvV i
  | pvP i => exact .pvP i
  | pvS i => exact .pvS i
  | pvI i => exact .pvI i
  | pvZ i => exact .pvZ i
  | @app0 s o ho =>
    simp only [Tm.rwBy]
    cases hf : Tm.pickExpandAll (Tm.app0 (C := C) (Γ := Γ) o) with
    | none => exact .app0 ho
    | some t' => exact Tm.pickExpandAll_elimOk hf (.app0 ho)
  | @app1 a s o x ho hx ih =>
    simp only [Tm.rwBy]
    cases hf : Tm.pickExpandAll (Tm.app1 o x) with
    | none => exact .app1 ho ih
    | some t' => exact Tm.pickExpandAll_elimOk hf (.app1 ho hx)
  | @app2 a b s o x y ho hx hy ihx ihy =>
    simp only [Tm.rwBy]
    cases hf : Tm.pickExpandAll (Tm.app2 o x y) with
    | none => exact .app2 ho ihx ihy
    | some t' => exact Tm.pickExpandAll_elimOk hf (.app2 ho hx hy)
  | @app3 a b c s o x y z ho hx hy hz ihx ihy ihz =>
    simp only [Tm.rwBy]
    cases hf : Tm.pickExpandAll (Tm.app3 o x y z) with
    | none => exact .app3 ho ihx ihy ihz
    | some t' => exact Tm.pickExpandAll_elimOk hf (.app3 ho hx hy hz)

/-- An expansion of a term in save normal form is in save normal form: only
a copy's fires on one, onto saves over the same storage. -/
theorem Tm.SaveNF.expand? {t t' : Tm C Γ .st} (ht : t.SaveNF) (h : t.expand? = some t') :
    t'.SaveNF := by
  obtain ⟨k, hk⟩ := Tm.expand?_kind h
  cases k
  · obtain ⟨T, s, p, rfl, rfl, -⟩ := Tm.delAtExpand?_some hk
    cases ht
  · obtain ⟨T, s, p, q, rfl, rfl, -⟩ := Tm.copyExpand?_some hk
    cases ht with
    | save _ _ hs => exact Tm.SaveNF.saveLeaves _ _ _ _ hs
  · obtain ⟨P, s, p, x, rfl, rfl, -⟩ := Tm.pushExpand?_some hk
    cases ht
  · obtain ⟨P, s, p, rfl, rfl, -⟩ := Tm.popExpand?_some hk
    cases ht

theorem Tm.SaveNF.rwBy_expandAll {t : Tm C Γ .st} (ht : t.SaveNF) :
    (Tm.rwBy Tm.pickExpandAll t).SaveNF := by
  induction ht with
  | storage =>
    simp only [Tm.rwBy]
    cases hf : Tm.pickExpandAll (Tm.app0 (C := C) (Γ := Γ) Op0.storage) with
    | none => exact .storage
    | some t' => exact Tm.SaveNF.expand? .storage hf
  | save p v hs ih =>
    simp only [Tm.rwBy]
    cases hf : Tm.pickExpandAll (Tm.app3 .save _ p v) with
    | none => exact .save _ _ ih
    | some t' => exact Tm.SaveNF.expand? (.save p v hs) hf
  | pushSlot p hs ih =>
    simp only [Tm.rwBy]
    cases hf : Tm.pickExpandAll (Tm.app2 .pushSlot _ p) with
    | none => exact .pushSlot _ ih
    | some t' => exact Tm.SaveNF.expand? (.pushSlot p hs) hf
  | shrink p hs ih =>
    simp only [Tm.rwBy]
    cases hf : Tm.pickExpandAll (Tm.app2 .shrink _ p) with
    | none => exact .shrink _ ih
    | some t' => exact Tm.SaveNF.expand? (.shrink p hs) hf

/-- **A save-like storage term, every expansion done, is in save normal
form.** -/
theorem Tm.SaveLike.rwBy_expandAll {t : Tm C Γ .st} (ht : t.SaveLike) :
    (Tm.rwBy Tm.pickExpandAll t).SaveNF := by
  have h := ht.saveNF_expand
  cases hf : t.expand? with
  | none =>
    rw [hf, Option.getD_none] at h
    exact h.rwBy_expandAll
  | some t' =>
    rw [hf, Option.getD_some] at h
    cases ht <;> simp only [Tm.rwBy, Tm.pickExpandAll, hf, Option.getD_some] <;> exact h

/-- **An update of the fragment, every storage element expanded**, is in
save normal form with a reading: `Upd.toLS_okNF` composes it. -/
theorem Upd.rwBy_expandAll_nf {Δ : Ctx} :
    {U : Upd C Γ Δ} → U.SaveLike → U.ElimOk →
      (Upd.rwBy Tm.pickExpandAll U).NF ∧ (Upd.rwBy Tm.pickExpandAll U).ElimOk
  | .nil, _, _ => ⟨trivial, trivial⟩
  | .snoc U e, hS, hE => by
    have ih := Upd.rwBy_expandAll_nf hS.1 hE.1
    cases e with
    | storage s => exact ⟨⟨ih.1, hS.2.rwBy_expandAll⟩, ⟨ih.2, hE.2.rwBy_expandAll⟩⟩
    | «local» i r =>
      refine ⟨⟨ih.1, trivial⟩, ⟨ih.2, ?_⟩⟩
      cases r with
      | unset => exact hE.2.elim
      | saveNet | saveNetMt => trivial
      | val x | path x | mref x | store x | zint x => exact Tm.ElimOk.rwBy_expandAll hE.2
    | _ => exact hE.2.elim
  | .decl U _ r, hS, hE => by
    have ih := Upd.rwBy_expandAll_nf (U := U) hS hE.1
    refine ⟨ih.1, ih.2, ?_⟩
    cases r with
    | unset => exact hE.2.elim
    | saveNet | saveNetMt => trivial
    | val x | path x | mref x | store x | zint x => exact Tm.ElimOk.rwBy_expandAll hE.2
  | .pop U _, hS, hE => Upd.rwBy_expandAll_nf (U := U) hS hE
  | .drop U _, hS, hE => Upd.rwBy_expandAll_nf (U := U) hS hE

/-- **The lift, at the composition**: on a leaf of the fragment, each
update expanded and pushed in at a state whose storage is a chain of saves
on `storage` (from `SymS.init` on) leaves one, so every storage the leaf's
reads see is in `LTm.SaveNF`. -/
theorem Upd.SaveLike.toLS_expandAll_okNF {Δ : Ctx} {U : Upd C Γ Δ} (hS : U.SaveLike)
    (hE : U.ElimOk) {ρ₀ : SymS C Γ} (hρ₀ : ρ₀.OkNF) {q : SymS C Δ × LTm C (.val .bool)}
    (h : (Upd.rwBy Tm.pickExpandAll U).toLS ρ₀ = some q) : q.1.OkNF :=
  have hN := Upd.rwBy_expandAll_nf hS hE
  Upd.toLS_okNF hρ₀ hN.2 hN.1 h

end ExpandAll

end Solidity
