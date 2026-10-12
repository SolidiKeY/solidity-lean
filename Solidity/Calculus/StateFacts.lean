import Solidity.Update
import Solidity.Semantics.Properties
import Solidity.Theory.Bridge.Denote
import Solidity.Calculus.ReadWrite

/-!
# Facts about the interpreter's states and symbols

What the scoped calculus reads of the interpreter, by the symbols `Op0`–`Op3`
and the untyped state they run on (`Semantics.State`): a result refining
another (`Res.Le`, `Srt.Le`, `Op1.eval_le`, …), two results returning alike
(`Res.OkEq`), the parts of a state a symbol reads (`Srt.AgreePart`,
`State.HeapEq`, `StPartEq`, `MemPartEq`), what a symbol keeps
(`State.Keeps`, `Op2.stExplicit`), denotations that agree (`Srt.DEquiv`,
`Op1.denote_congr`), a root read member-wise (`State.selectRoot`,
`State.frameOf`), and the shapes of the paths a law's side condition reads
(`SegT`).  Collected from the modules of the erased syntax as they went
(`docs/intrinsic.md`, W9.5a); each is about states and symbols only.
-/

namespace Solidity

/-! ## From `Solidity.Calculus.TermRules` -/

section
open Semantics SemanticsProperties Theory
variable {C : Contract}

/-- A memory read (`read`, `mlen`, `copyMem`): its denotation is its
evaluation, so a rewrite never looks inside it. -/
def Op2.opaque : Op2 a b s → Bool
  | .read | .mlen | .copyMem => true
  | _ => false

/-- Two equivalent values are one primitive, or two nodes. -/
theorem Theory.StValue.Equiv.eq_or_st {v w : StValue} (h : StValue.Equiv v w) :
    v = w ∨ ∃ s t, v = .st s ∧ w = .st t := by
  cases v with
  | prim p => exact Or.inl (StValue.Equiv.prim_iff.1 h.symm).symm
  | st s => cases w with
    | prim p => cases StValue.Equiv.prim_iff.1 h
    | st t => exact Or.inr ⟨s, t, rfl, rfl⟩

/-- Equivalent values are one interpreter result. -/
theorem Theory.StValue.Equiv.toRes {v w : StValue} (h : StValue.Equiv v w) :
    v.toRes = w.toRes := by
  rcases h.eq_or_st with rfl | ⟨s, t, rfl, rfl⟩ <;> rfl

end

section
open Semantics SemanticsProperties Theory
variable {C : Contract}
section Denote
variable {q : Term C × Term C} {σ : State}

/-- Two denotations of a sort agree in the Theory: `Equiv` for a value or a
storage, equal paths. -/
def Srt.DEquiv : (s : Srt) → s.Den → s.Den → Prop
  | .val => StValue.Equiv
  | .path => Eq
  | .st => Struct.Equiv
  | .sv => StValue.Equiv
  | .ident | .addr | .mem | .mv => fun _ _ => True

theorem Srt.DEquiv.refl : (s : Srt) → (d : s.Den) → Srt.DEquiv s d d
  | .val, _ | .st, _ | .sv, _ => StValue.Equiv.refl _
  | .path, _ => rfl
  | .ident, _ | .addr, _ | .mem, _ | .mv, _ => trivial

/-- A unary symbol respects `Equiv` of its argument's denotation. -/
theorem Op1.denote_congr : (o : Op1 a s) → {d d' : a.Den} →
    Srt.DEquiv a d d' → Srt.DEquiv s (o.denote σ d) (o.denote σ d')
  | .unop .., _, _, h => by
    simp only [Srt.DEquiv, Op1.denote] at h ⊢
    rw [h.toRes]
    exact StValue.Equiv.refl _
  | .net, _, _, h => by
    simp only [Srt.DEquiv] at h ⊢
    rcases h.eq_or_st with h | ⟨s, t, hs, ht⟩
    · rw [h]; exact StValue.Equiv.refl _
    · simp only [Op1.denote, hs, ht]; exact StValue.Equiv.refl _
  | .netOf x, _, _, h => by
    simp only [Srt.DEquiv] at h ⊢
    rcases h.eq_or_st with h | ⟨s, t, hs, ht⟩
    · rw [h]; exact StValue.Equiv.refl _
    · simp only [Op1.denote, hs, ht]
      rcases σ.getEnv x with _ | b
      · exact StValue.Equiv.refl _
      · cases b <;> exact StValue.Equiv.refl _
  | .field _, _, _, h | .next, _, _, h => by
    simp only [Srt.DEquiv] at h ⊢; rw [h]
  | .delValue, _, _, h => by
    simp only [Srt.DEquiv, Op1.denote] at h ⊢
    exact StValue.Equiv.delValue h
  | .select _, _, _, h => by
    simp only [Srt.DEquiv, Op1.denote] at h ⊢
    exact StValue.Equiv.asStruct (StValue.Equiv.findSt h [_])
  | .sval, _, _, h => h
  | .newArr _, _, _, h => by
    simp only [Srt.DEquiv, Op1.denote] at h ⊢
    rw [h.asInt]
    exact StValue.Equiv.refl _
  | .alloc _, _, _, _ | .mfield _, _, _, _ | .addM _, _, _, _
  | .mval, _, _, _ | .ref, _, _, _ => trivial
  | .wt _, _, _, _ => StValue.Equiv.refl _

/-- A binary symbol that is no memory read respects `Equiv` of its
arguments' denotations, whatever their readings. -/
theorem Op2.denote_congr : (o : Op2 a b s) → o.opaque = false → {ra ra' : a.Ev} →
    {rb rb' : b.Ev} → {da da' : a.Den} → {db db' : b.Den} → Srt.DEquiv a da da' →
    Srt.DEquiv b db db' → Srt.DEquiv s (o.denote σ ra rb da db) (o.denote σ ra' rb' da' db')
  | .binop .., _, _, _, _, _, _, _, _, _, ha, hb => by
    simp only [Srt.DEquiv, Op2.denote] at ha hb ⊢
    rw [ha.toRes, hb.toRes]
    exact StValue.Equiv.refl _
  | .find, _, _, _, _, _, _, _, _, _, hs, hp | .sfind, _, _, _, _, _, _, _, _, _, hs, hp
  | .len, _, _, _, _, _, _, _, _, _, hs, hp => by
    simp only [Srt.DEquiv, Op2.denote] at hs hp ⊢
    rw [hp]
    exact StValue.Equiv.findSt hs _
  | .at, _, _, _, _, _, _, _, _, _, hp, hi => by
    simp only [Srt.DEquiv, Op2.denote] at hp hi ⊢
    rw [hp, hi.asInt]
  | .nextIn, _, _, _, _, _, _, _, _, _, hs, hp => by
    simp only [Srt.DEquiv, Op2.denote] at hs hp ⊢
    rw [hp, Struct.Equiv.lenAt hs]
  | .delAt, _, _, _, _, _, _, _, _, _, hs, hp => by
    simp only [Srt.DEquiv, Op2.denote] at hs hp ⊢
    rw [hp]
    exact Struct.Equiv.delAt hs _
  | .pushSlot _, _, _, _, _, _, _, _, _, _, hs, hp
  | .extend _, _, _, _, _, _, _, _, _, _, hs, hp => by
    simp only [Srt.DEquiv, Op2.denote] at hs hp ⊢
    rw [hp]
    exact Struct.Equiv.pushSlotT _ _ hs _
  | .pop, _, _, _, _, _, _, _, _, _, hs, hp => by
    simp only [Srt.DEquiv, Op2.denote] at hs hp ⊢
    rw [hp]
    exact Struct.Equiv.popT hs _
  | .shrink, _, _, _, _, _, _, _, _, _, hs, hp => by
    simp only [Srt.DEquiv, Op2.denote] at hs hp ⊢
    rw [hp]
    exact Struct.Equiv.shrinkT hs _
  | .iread, _, _, _, _, _, _, _, _, _, _, _ | .copy, _, _, _, _, _, _, _, _, _, _, _
  | .mat, _, _, _, _, _, _, _, _, _, _, _ | .copySt, _, _, _, _, _, _, _, _, _, _, _ => trivial

/-- A ternary symbol respects `Equiv` of its arguments' denotations. -/
theorem Op3.denote_congr : (o : Op3 a b c s) → {da da' : a.Den} → {db db' : b.Den} →
    {dc dc' : c.Den} → Srt.DEquiv a da da' → Srt.DEquiv b db db' → Srt.DEquiv c dc dc' →
    Srt.DEquiv s (o.denote da db dc) (o.denote da' db' dc')
  | .ite, _, _, _, _, _, _, hc, ha, hb => by
    simp only [Srt.DEquiv, Op3.denote] at hc ha hb ⊢
    rcases hc.eq_or_st with h | ⟨s, t, hs, ht⟩
    · rw [h]
      split
      · exact ha
      · exact hb
      · exact StValue.Equiv.refl _
    · simp only [hs, ht]
      exact StValue.Equiv.refl _
  | .atIn, _, _, _, _, _, _, _, hp, hi => by
    simp only [Srt.DEquiv, Op3.denote] at hp hi ⊢
    rw [hp, hi.asInt]
  | .save, _, _, _, _, _, _, hs, hp, hv => by
    simp only [Srt.DEquiv, Op3.denote] at hs hp hv ⊢
    rw [hp]
    exact Struct.Equiv.copyTo hs hv _
  | .push, _, _, _, _, _, _, hs, hp, hv => by
    simp only [Srt.DEquiv, Op3.denote] at hs hp hv ⊢
    rw [hp]
    exact Struct.Equiv.pushT hs (StValue.Equiv.stripVal hv) _
  | .write, _, _, _, _, _, _, _, _, _ => trivial

end Denote
end

/-! ## From `Solidity.Calculus.NFmlUpdateRules` -/

section
open Semantics
variable {C : Contract}
section SubstDenote
variable {U : Surface.Upd C} {ns : List Var} {σ τ : State}
open Theory Theory.StValue

theorem Srt.DEquiv.of_eq {s : Srt} {d d' e : s.Den} (h : d = d') (he : Srt.DEquiv s d' e) :
    Srt.DEquiv s d e := h ▸ he

end SubstDenote
end

section
open Semantics
variable {C : Contract}
section StorageWrite
open SemanticsProperties

/-- `τ` is `σ` with another storage. -/
def Semantics.State.Keeps (σ τ : State) : Prop := { σ with storage := τ.storage } = τ

/-- A symbol that reads no storage of the state: not `memory`, a push slot
(`next`), an index check (`at`) or a memory read. -/
def Op0.stExplicit : Op0 s → Bool
  | .memory => false
  | _ => true

def Op1.stExplicit : Op1 a s → Bool
  | .next => false
  | _ => true

def Op2.stExplicit (o : Op2 a b s) : Bool :=
  match o with
  | .at => false
  | _ => !o.opaque

end StorageWrite
end

section
open Semantics
variable {C : Contract}
section StorageWrite
open SemanticsProperties
section WithSt
variable {σ τ : State}

theorem Op2.opaque_of_stExplicit : {o : Op2 a b s} → o.stExplicit = true → o.opaque = false := by
  intro o h; cases o <;> simp_all only [Op2.stExplicit, Op2.opaque, Bool.not_true, reduceCtorEq]

/-- A unary symbol that reads no storage reads alike before and after a
write that keeps everything but the storage. -/
theorem Op1.eval_keeps (hk : σ.Keeps τ) :
    (o : Op1 a s) → o.stExplicit = true → (r : a.Ev) → o.eval σ r = o.eval τ r := by
  intro o he r
  cases o <;> first | rfl | (rw [← hk]; rfl) | simp only [Op1.stExplicit, Bool.false_eq_true] at he

theorem Op2.eval_keeps (_hk : σ.Keeps τ) :
    (o : Op2 a b s) → o.stExplicit = true → (ra : a.Ev) → (rb : b.Ev) →
      o.eval σ ra rb = o.eval τ ra rb := by
  intro o he ra rb
  cases o <;> first | rfl | simp only [Op2.stExplicit, Bool.false_eq_true] at he

end WithSt
end StorageWrite
end

section
open Semantics
variable {C : Contract}
section StorageWrite
open SemanticsProperties
section WithStDenote
open Theory Theory.StValue
variable {σ τ : State}

theorem Op1.denote_keeps (hk : σ.Keeps τ) :
    (o : Op1 a s) → o.stExplicit = true → (d : a.Den) → o.denote σ d = o.denote τ d := by
  intro o he d
  cases o <;> first | rfl | (rw [← hk]; rfl) | simp only [Op1.stExplicit, Bool.false_eq_true] at he

theorem Op2.denote_keeps (_hk : σ.Keeps τ) :
    (o : Op2 a b s) → o.stExplicit = true → (ra ra' : a.Ev) → (rb rb' : b.Ev) → (d : a.Den) →
      (e : b.Den) → o.denote σ ra rb d e = o.denote τ ra' rb' d e := by
  intro o he ra ra' rb rb' d e
  cases o <;> first | rfl | simp only [Op2.stExplicit, Op2.opaque, Bool.not_true,
    Bool.false_eq_true] at he

end WithStDenote
end StorageWrite
end

section
open Semantics
variable {C : Contract}
section RwEval

/-- Where `a` returns a value, `b` returns it too. -/
def Semantics.Res.Le {α : Type} (a b : Res α) : Prop := ∀ x, a = .ok x → b = .ok x

theorem Semantics.Res.Le.refl {α : Type} (a : Res α) : Res.Le a a := fun _ h => h

theorem Semantics.Res.Le.bind {α β : Type} {a a' : Res α} {f f' : α → Res β} (ha : Res.Le a a')
    (hf : ∀ x, Res.Le (f x) (f' x)) : Res.Le (a >>= f) (a' >>= f') := fun y h => by
  obtain ⟨x, hx, hy⟩ := bind_ok_inv h
  rw [ha x hx]
  exact hf x y hy

theorem evalBinop_le {op : BinOp} {p : PrimTy} {v : Value} {b b' : Res Value} (hb : Res.Le b b') :
    Res.Le (evalBinop op p v b) (evalBinop op p v b') := by
  unfold evalBinop
  split
  · exact Res.Le.refl _
  · exact Res.Le.refl _
  · exact Res.Le.bind hb fun _ => Res.Le.refl _

theorem pickBranch_le {c : Value} {a a' b b' : Res Value} (ha : Res.Le a a') (hb : Res.Le b b') :
    Res.Le (pickBranch c a b) (pickBranch c a' b') := by
  unfold pickBranch
  split
  · exact ha
  · exact hb
  · exact Res.Le.refl _

theorem pushAt_le {σ : State} {E : Ty} {r : Name} {segs : List Seg} {val val' : SVal → Res SVal}
    (hv : ∀ x, Res.Le (val x) (val' x)) : Res.Le (pushAt σ E r segs val) (pushAt σ E r segs val') := by
  unfold pushAt
  refine Res.Le.bind (Res.Le.refl _) fun cur => ?_
  cases cur with
  | array elems shadow fx => exact Res.Le.bind (hv _) fun _ => Res.Le.refl _
  | prim _ | struct _ | map _ _ => exact Res.Le.refl _

end RwEval
end

section
open Semantics
variable {C : Contract}
section RwEval
variable {q : Term C × Term C}

/-- Where the first reading returns, the second returns the same. -/
def Srt.Le : (s : Srt) → s.Ev → s.Ev → Prop
  | .val => Res.Le
  | .path => Res.Le
  | .st => Res.Le
  | .sv => Res.Le
  | .ident => Res.Le
  | .addr => Res.Le
  | .mem => Res.Le
  | .mv => Res.Le

theorem Srt.Le.refl : (s : Srt) → (r : s.Ev) → Srt.Le s r r
  | .val, r | .path, r | .st, r | .sv, r | .ident, r | .addr, r | .mem, r | .mv, r =>
    Res.Le.refl r

/-- A symbol keeps every value its arguments return: its reading is binds
on theirs. -/
theorem Op1.eval_le {σ : State} : (o : Op1 a s) → {r r' : a.Ev} → Srt.Le a r r' →
    Srt.Le s (o.eval σ r) (o.eval σ r')
  | .netOf _, _, _, h => Res.Le.bind (Res.Le.refl _) fun b => by
      cases b <;> first
        | exact Res.Le.refl _
        | exact Res.Le.bind h fun _ => Res.Le.refl _
  | .unop .., _, _, h | .net, _, _, h | .delValue, _, _, h | .field _, _, _, h | .next, _, _, h
  | .select _, _, _, h | .sval, _, _, h | .newArr _, _, _, h | .alloc _, _, _, h
  | .mfield _, _, _, h | .addM _, _, _, h | .mval, _, _, h | .ref, _, _, h
  | .wt _, _, _, h =>
    Res.Le.bind h fun _ => Res.Le.refl _

theorem Op2.eval_le {σ : State} : (o : Op2 a b s) → {ra ra' : a.Ev} → {rb rb' : b.Ev} →
    Srt.Le a ra ra' → Srt.Le b rb rb' → Srt.Le s (o.eval σ ra rb) (o.eval σ ra' rb')
  | .binop .., _, _, _, _, ha, hb => Res.Le.bind ha fun _ => evalBinop_le hb
  | .copy, _, _, _, _, ha, hb | .copySt, _, _, _, _, ha, hb =>
    Res.Le.bind hb fun _ => Res.Le.bind ha fun _ => Res.Le.refl _
  | .find, _, _, _, _, ha, hb | .len, _, _, _, _, ha, hb | .read, _, _, _, _, ha, hb
  | .mlen, _, _, _, _, ha, hb | .at, _, _, _, _, ha, hb | .nextIn, _, _, _, _, ha, hb
  | .delAt, _, _, _, _, ha, hb | .pushSlot _, _, _, _, _, ha, hb | .pop, _, _, _, _, ha, hb | .shrink, _, _, _, _, ha, hb
  | .extend _, _, _, _, _, ha, hb | .sfind, _, _, _, _, ha, hb | .copyMem, _, _, _, _, ha, hb
  | .iread, _, _, _, _, ha, hb | .mat, _, _, _, _, ha, hb =>
    Res.Le.bind ha fun _ => Res.Le.bind hb fun _ => Res.Le.refl _

theorem Op3.eval_le {σ : State} : (o : Op3 a b c s) → {ra ra' : a.Ev} → {rb rb' : b.Ev} →
    {rc rc' : c.Ev} → Srt.Le a ra ra' → Srt.Le b rb rb' → Srt.Le c rc rc' →
    Srt.Le s (o.eval σ ra rb rc) (o.eval σ ra' rb' rc')
  | .ite, _, _, _, _, _, _, hc, ha, hb => Res.Le.bind hc fun _ => pickBranch_le ha hb
  | .atIn, _, _, _, _, _, _, hs, hp, hi =>
    Res.Le.bind hs fun _ => Res.Le.bind hp fun _ => Res.Le.bind hi fun _ =>
      Res.Le.bind (Res.Le.refl _) fun _ => Res.Le.refl _
  | .save, _, _, _, _, _, _, hs, hp, hv =>
    Res.Le.bind hv fun _ => Res.Le.bind hs fun _ => Res.Le.bind hp fun _ => Res.Le.refl _
  | .push, _, _, _, _, _, _, hs, hp, hv =>
    Res.Le.bind hs fun _ => Res.Le.bind hp fun _ =>
      pushAt_le fun _ => Res.Le.bind hv fun _ => Res.Le.refl _
  | .write, _, _, _, _, _, _, hm, ha, hv =>
    Res.Le.bind hv fun _ => Res.Le.bind hm fun _ => Res.Le.bind ha fun _ => Res.Le.refl _

end RwEval
end

/-! ## From `Solidity.Calculus.StateParts` -/

section
open Semantics SemanticsProperties
variable {C : Contract}

/-- The parts of a state neither a storage or memory term nor a local
writes: the ledger, the funds and the transaction. -/
structure Semantics.State.Rest (σ τ : State) : Prop where
  net : σ.net = τ.net
  selfBalance : σ.selfBalance = τ.selfBalance
  tx : σ.tx = τ.tx

/-- Two states of one storage, and of one heap and next identity. -/
def Semantics.State.HeapEq (σ τ : State) : Prop := σ.heap = τ.heap ∧ σ.nextId = τ.nextId

/-- What a storage write takes of a storage reading. -/
def Semantics.Res.stPart (a : Res State) : Res (List (Name × SVal)) := a.map (·.storage)

/-- What a memory write takes of a memory reading. -/
def Semantics.Res.memPart (a : Res State) : Res (List (Nat × MObj) × Nat) := a.map fun ρ => (ρ.heap, ρ.nextId)

/-- Two storage readings of one storage (a structure, so that a match on a
reading does not split it). -/
structure StPartEq (a b : Res State) : Prop where
  eq : Res.stPart a = Res.stPart b

/-- Two memory readings of one heap and next identity. -/
structure MemPartEq (a b : Res State) : Prop where
  eq : Res.memPart a = Res.memPart b

/-- Two readings agree where a write looks: a storage by its storage, a
memory by its heap and next identity, anything else as it is. -/
def Srt.AgreePart : (s : Srt) → s.Ev → s.Ev → Prop
  | .st => StPartEq
  | .mem => MemPartEq
  | .val | .path | .sv | .ident | .addr | .mv => Eq

theorem Semantics.Res.stPart_cases {a b : Res State} (h : Res.stPart a = Res.stPart b) :
    (∃ e, a = .error e ∧ b = .error e) ∨
      ∃ τ₁ τ₂, a = .ok τ₁ ∧ b = .ok τ₂ ∧ τ₁.storage = τ₂.storage := by
  cases a with
  | error e =>
    cases b with
    | error e' =>
      simp only [Res.stPart, Except.map, Except.error.injEq] at h
      exact Or.inl ⟨e, rfl, by rw [h]⟩
    | ok _ => simp [Res.stPart, Except.map] at h
  | ok τ₁ =>
    cases b with
    | error _ => simp [Res.stPart, Except.map] at h
    | ok τ₂ =>
      simp only [Res.stPart, Except.map, Except.ok.injEq] at h
      exact Or.inr ⟨τ₁, τ₂, rfl, rfl, h⟩

theorem Semantics.Res.memPart_cases {a b : Res State} (h : Res.memPart a = Res.memPart b) :
    (∃ e, a = .error e ∧ b = .error e) ∨
      ∃ τ₁ τ₂, a = .ok τ₁ ∧ b = .ok τ₂ ∧ τ₁.HeapEq τ₂ := by
  cases a with
  | error e =>
    cases b with
    | error e' =>
      simp only [Res.memPart, Except.map, Except.error.injEq] at h
      exact Or.inl ⟨e, rfl, by rw [h]⟩
    | ok _ => simp [Res.memPart, Except.map] at h
  | ok τ₁ =>
    cases b with
    | error _ => simp [Res.memPart, Except.map] at h
    | ok τ₂ =>
      simp only [Res.memPart, Except.map, Except.ok.injEq, Prod.mk.injEq] at h
      exact Or.inr ⟨τ₁, τ₂, rfl, rfl, h⟩

theorem Semantics.Res.stPart_ok {τ₁ τ₂ : State} (h : τ₁.storage = τ₂.storage) :
    StPartEq (Except.ok τ₁) (Except.ok τ₂) := ⟨by simp only [Res.stPart, Except.map, h]⟩

theorem Semantics.Res.memPart_ok {τ₁ τ₂ : State} (h : τ₁.HeapEq τ₂) :
    MemPartEq (Except.ok τ₁) (Except.ok τ₂) := ⟨by simp only [Res.memPart, Except.map, h.1, h.2]⟩

end

section
open Semantics SemanticsProperties
variable {C : Contract}
section StorageOnly
variable {σ τ : State} (hst : σ.storage = τ.storage)
include hst

theorem Semantics.State.findStorage_of_storage (r : Name) (q : List Seg) :
    σ.findStorage r q = τ.findStorage r q := by
  unfold State.findStorage; rw [hst]

theorem Semantics.State.checkIndex_of_storage (r : Name) (q : List Seg) (i : Int) :
    σ.checkIndex r q i = τ.checkIndex r q i := by
  unfold State.checkIndex; rw [State.findStorage_of_storage hst]

theorem arrayLen_of_storage (r : Name) (q : List Seg) : arrayLen σ r q = arrayLen τ r q := by
  unfold arrayLen; rw [State.findStorage_of_storage hst]

theorem Semantics.State.saveStorage_of_storage (r : Name) (q : List Seg) (v : SVal) :
    Res.stPart (σ.saveStorage r q v) = Res.stPart (τ.saveStorage r q v) := by
  unfold State.saveStorage
  rw [hst]
  cases lookupBy r τ.storage with
  | none => rfl
  | some w =>
    simp only [bind, Except.bind]
    cases w.save q v <;> rfl

theorem Semantics.State.writeStorage_of_storage (r : Name) (q : List Seg) (v : SVal) :
    Res.stPart (σ.writeStorage r q v) = Res.stPart (τ.writeStorage r q v) := by
  unfold State.writeStorage
  cases v with
  | prim p => exact State.saveStorage_of_storage hst r q _
  | struct _ | array _ _ _ | map _ _ =>
    rw [State.findStorage_of_storage hst]
    simp only [bind, Except.bind]
    cases τ.findStorage r q with
    | error _ => rfl
    | ok cur => exact State.saveStorage_of_storage hst r q _

theorem pushAt_of_storage (E : Ty) (r : Name) (q : List Seg) (val : SVal → Res SVal) :
    Res.stPart (pushAt σ E r q val) = Res.stPart (pushAt τ E r q val) := by
  unfold pushAt
  rw [State.findStorage_of_storage hst]
  cases τ.findStorage r q with
  | error _ => rfl
  | ok cur =>
    cases cur with
    | array elems shadow fx =>
      simp only [bind, Except.bind]
      cases val (pushSlot E shadow).1 with
      | error _ => rfl
      | ok w => exact State.saveStorage_of_storage hst r q _
    | prim _ | struct _ | map _ _ => rfl

theorem pushPlaceAt_of_storage (E : Ty) (r : Name) (q : List Seg) :
    Res.stPart (pushPlaceAt σ E r q >>= fun x => pure x.1) =
      Res.stPart (pushPlaceAt τ E r q >>= fun x => pure x.1) := by
  unfold pushPlaceAt
  rw [State.findStorage_of_storage hst]
  cases τ.findStorage r q with
  | error _ => rfl
  | ok cur =>
    cases cur with
    | array elems shadow fx =>
      simp only [bind, Except.bind]
      have h := State.saveStorage_of_storage hst r q
        (.array (elems ++ [(pushSlot E shadow).1]) (pushSlot E shadow).2 fx)
      rcases Res.stPart_cases h with ⟨e, h1, h2⟩ | ⟨τ₁, τ₂, h1, h2, h3⟩
      · simp only [h1, h2]
      · simp only [h1, h2, pure, Except.pure, Res.stPart, Except.map, h3]
    | prim _ | struct _ | map _ _ => rfl

theorem popAt_of_storage (keep : Bool) (r : Name) (q : List Seg) :
    Res.stPart (popAt σ keep r q) = Res.stPart (popAt τ keep r q) := by
  unfold popAt
  rw [State.findStorage_of_storage hst]
  cases τ.findStorage r q with
  | error _ => rfl
  | ok cur =>
    cases cur with
    | array elems shadow fx =>
      simp only [bind, Except.bind]
      cases elems.reverse with
      | nil => rfl
      | cons last rest => exact State.saveStorage_of_storage hst r q _
    | prim _ | struct _ | map _ _ => rfl

end StorageOnly
end

section
open Semantics SemanticsProperties
variable {C : Contract}
section HeapOnly
variable {σ τ : State}

theorem Semantics.State.getObj_of_heap (hh : σ.heap = τ.heap) (id : Nat) : σ.getObj id = τ.getObj id := by
  unfold State.getObj; rw [hh]

theorem readAddr_of_heap (hh : σ.heap = τ.heap) (a : Addr) : readAddr σ a = readAddr τ a := by
  cases a <;> simp only [readAddr, State.getObj_of_heap hh]

theorem memArrayLen_of_heap (hh : σ.heap = τ.heap) (id : Nat) :
    memArrayLen σ id = memArrayLen τ id := by
  unfold memArrayLen; rw [State.getObj_of_heap hh]

theorem writeAddr_of_heap (h : σ.HeapEq τ) (mv : MVal) (a : Addr) :
    Res.memPart (writeAddr σ mv a) = Res.memPart (writeAddr τ mv a) := by
  cases a with
  | memoryField id f =>
    simp only [writeAddr, memWriteField, bind, Except.bind, State.getObj_of_heap h.1]
    cases τ.getObj id with
    | error _ => rfl
    | ok obj =>
      cases obj with
      | struct fields => simp only [Res.memPart, Except.map, State.setObj, h.1, h.2]
      | array _ _ => rfl
  | memoryIndex id i =>
    simp only [writeAddr, memWriteIndex, bind, Except.bind, State.getObj_of_heap h.1]
    cases τ.getObj id with
    | error _ => rfl
    | ok obj =>
      cases obj with
      | struct _ => rfl
      | array elems fx =>
        by_cases hc : 0 ≤ i ∧ i.toNat < elems.length <;>
          simp [hc, Res.memPart, Except.map, State.setObj, h.1, h.2]

/-- Two copies that halt alike, or return one value into states of one heap. -/
def ResHeap {α : Type} : Res (State × α) → Res (State × α) → Prop
  | .error e₁, .error e₂ => e₁ = e₂
  | .ok (s₁, a₁), .ok (s₂, a₂) => a₁ = a₂ ∧ s₁.HeapEq s₂
  | _, _ => False

theorem ResHeap.bind {α β : Type} {x₁ x₂ : Res (State × α)} (hx : ResHeap x₁ x₂)
    {f₁ f₂ : State × α → Res (State × β)}
    (hf : ∀ s₁ s₂ a, s₁.HeapEq s₂ → ResHeap (f₁ (s₁, a)) (f₂ (s₂, a))) :
    ResHeap (x₁ >>= f₁) (x₂ >>= f₂) := by
  match x₁, x₂, hx with
  | .error _, .error _, hx => subst hx; exact rfl
  | .ok (s₁, a), .ok (s₂, a'), ⟨ha, hs⟩ => subst ha; exact hf s₁ s₂ a hs

theorem ResHeap.cases {α : Type} {x₁ x₂ : Res (State × α)} (hx : ResHeap x₁ x₂) :
    (∃ e, x₁ = .error e ∧ x₂ = .error e) ∨
      ∃ s₁ s₂ a, x₁ = .ok (s₁, a) ∧ x₂ = .ok (s₂, a) ∧ s₁.HeapEq s₂ := by
  match x₁, x₂, hx with
  | .error e, .error _, hx => exact Or.inl ⟨e, rfl, by rw [hx]⟩
  | .ok (s₁, a), .ok (s₂, _), ⟨rfl, hs⟩ => exact Or.inr ⟨s₁, s₂, a, rfl, rfl, hs⟩

mutual
theorem copyStToM_heap {σ τ : State} (h : σ.HeapEq τ) (v : SVal) : ResHeap (copyStToM σ v) (copyStToM τ v) := by
  match v with
  | .int v => rw [copyStToM, copyStToM]; exact ⟨rfl, h⟩
  | .bool b => rw [copyStToM, copyStToM]; exact ⟨rfl, h⟩
  | .struct fields =>
    rw [copyStToM, copyStToM]
    refine ResHeap.bind (copyStFields_heap h fields) ?_
    intro t₁ t₂ mfields ht
    exact ⟨by simp [ht.2], by simp [State.HeapEq, ht.1, ht.2]⟩
  | .array elems _ _ =>
    rw [copyStToM, copyStToM]
    refine ResHeap.bind (copyStElems_heap h elems) ?_
    intro t₁ t₂ melems ht
    exact ⟨by simp [ht.2], by simp [State.HeapEq, ht.1, ht.2]⟩
  | .map _ _ => rw [copyStToM, copyStToM]; exact rfl

theorem copyStFields_heap {σ τ : State} (h : σ.HeapEq τ) (fields : List (Name × SVal)) :
    ResHeap (copyStFields σ fields) (copyStFields τ fields) := by
  match fields with
  | [] => rw [copyStFields, copyStFields]; exact ⟨rfl, h⟩
  | (name, v) :: rest =>
    rw [copyStFields, copyStFields]
    refine ResHeap.bind (copyStToM_heap h v) ?_
    intro t₁ t₂ mv ht
    refine ResHeap.bind (copyStFields_heap ht rest) ?_
    intro u₁ u₂ mrest hu
    exact ⟨rfl, hu⟩

theorem copyStElems_heap {σ τ : State} (h : σ.HeapEq τ) (elems : List SVal) :
    ResHeap (copyStElems σ elems) (copyStElems τ elems) := by
  match elems with
  | [] => rw [copyStElems, copyStElems]; exact ⟨rfl, h⟩
  | v :: rest =>
    rw [copyStElems, copyStElems]
    refine ResHeap.bind (copyStToM_heap h v) ?_
    intro t₁ t₂ mv ht
    refine ResHeap.bind (copyStElems_heap ht rest) ?_
    intro u₁ u₂ mrest hu
    exact ⟨rfl, hu⟩
end

theorem allocDefault_heap (h : σ.HeapEq τ) (R : RefTy) :
    ResHeap (allocDefault σ R) (allocDefault τ R) := by
  unfold allocDefault
  rcases (copyStToM_heap h (defaultForRef R)).cases with ⟨e, h₁, h₂⟩ | ⟨t₁, t₂, mv, h₁, h₂, ht⟩
  · rw [h₁, h₂]; exact rfl
  · rw [h₁, h₂]
    cases mv with
    | prim p => cases p <;> exact rfl
    | ref id => exact ⟨rfl, ht⟩

mutual
theorem copyMToSt_of_heap {σ τ : State} (hh : σ.heap = τ.heap) (rem : List Nat) (v : MVal) :
    copyMToSt σ rem v = copyMToSt τ rem v := by
  match v with
  | .int v => rw [copyMToSt.eq_def, copyMToSt.eq_def]
  | .bool b => rw [copyMToSt.eq_def, copyMToSt.eq_def]
  | .ref id =>
    rw [copyMToSt.eq_def, copyMToSt.eq_def]
    by_cases hmem : id ∈ rem
    · simp only [hmem, dif_pos, State.getObj_of_heap hh, copyMFields_of_heap hh (rem.erase id),
        copyMElems_of_heap hh (rem.erase id)]
    · simp only [hmem, dif_neg, not_false_iff]
termination_by (rem.length, 0)
decreasing_by all_goals
  (apply Prod.Lex.left
   have h1 := List.length_erase_of_mem hmem
   have h2 := List.length_pos_of_mem hmem
   omega)

theorem copyMFields_of_heap {σ τ : State} (hh : σ.heap = τ.heap) (rem : List Nat) (fields : List (Name × MVal)) :
    copyMFields σ rem fields = copyMFields τ rem fields := by
  match fields with
  | [] => rw [copyMFields, copyMFields]
  | (name, v) :: rest =>
    rw [copyMFields, copyMFields, copyMToSt_of_heap hh rem v, copyMFields_of_heap hh rem rest]
termination_by (rem.length, fields.length + 1)

theorem copyMElems_of_heap {σ τ : State} (hh : σ.heap = τ.heap) (rem : List Nat) (elems : List MVal) :
    copyMElems σ rem elems = copyMElems τ rem elems := by
  match elems with
  | [] => rw [copyMElems, copyMElems]
  | v :: rest =>
    rw [copyMElems, copyMElems, copyMToSt_of_heap hh rem v, copyMElems_of_heap hh rem rest]
termination_by (rem.length, elems.length + 1)
end

theorem copyMem_of_heap (hh : σ.heap = τ.heap) (v : MVal) :
    Semantics.copyMem σ v = Semantics.copyMem τ v := by
  unfold Semantics.copyMem
  rw [hh, copyMToSt_of_heap hh]

end HeapOnly
end

section
open Semantics SemanticsProperties
variable {C : Contract}
section OpPart

/-- The symbol reads the storage of the state it runs in: a push slot. -/
def Op1.stDirect : Op1 a s → Bool
  | .next => true
  | _ => false

/-- The symbol reads the storage of the state it runs in: an index check. -/
def Op2.stDirect : Op2 a b s → Bool
  | .at => true
  | _ => false

end OpPart
end

section
open Semantics SemanticsProperties
variable {C : Contract}
section OpPart
variable {σ τ : State}

/-- A unary symbol reads its argument where a write looks, and of the state
the ledger (`net`) and a ledger variable it carries (`netOf`, bound alike
in the two states: `he`). -/
theorem Op1.eval_part (hr : σ.Rest τ) :
    (o : Op1 a s) → (∀ x, o.vars = [x] → σ.getEnv x = τ.getEnv x) →
      (o.stDirect = false ∨ σ.storage = τ.storage) → {x₁ x₂ : a.Ev} →
      Srt.AgreePart a x₁ x₂ → Srt.AgreePart s (o.eval σ x₁) (o.eval τ x₂)
  | .unop .., _, _, _, _, hx | .delValue, _, _, _, _, hx | .field _, _, _, _, _, hx
  | .sval, _, _, _, _, hx | .newArr _, _, _, _, _, hx | .mfield _, _, _, _, _, hx
  | .mval, _, _, _, _, hx | .ref, _, _, _, _, hx => by
    simp only [Srt.AgreePart] at hx ⊢; subst hx; rfl
  | .net, _, _, _, _, hx => by
    simp only [Srt.AgreePart] at hx ⊢; subst hx
    simp only [Op1.eval, State.getNet, hr.net]
  | .netOf x, he, _, _, _, hx => by
    simp only [Srt.AgreePart] at hx ⊢; subst hx
    simp only [Op1.eval, he x rfl]
  | .next, _, ho, _, _, hx => by
    simp only [Srt.AgreePart] at hx ⊢; subst hx
    have hst := ho.resolve_left (by simp [Op1.stDirect])
    simp only [Op1.eval, State.findStorage_of_storage hst]
  | .select r, _, _, _, _, hx => by
    simp only [Srt.AgreePart, Op1.eval] at hx ⊢
    rcases Res.stPart_cases hx.eq with ⟨e, rfl, rfl⟩ | ⟨τ₁, τ₂, rfl, rfl, h⟩
    · exact ⟨rfl⟩
    · simp only [bind, Except.bind, State.findStorage_of_storage h]
      cases τ₂.findStorage r [] with
      | error e => exact ⟨rfl⟩
      | ok w =>
        cases w with
        | struct fields => exact Res.stPart_ok rfl
        | prim _ | array _ _ _ | map _ _ => exact ⟨rfl⟩
  | .alloc R, _, _, _, _, hx => by
    simp only [Srt.AgreePart, Op1.eval] at hx ⊢
    rcases Res.memPart_cases hx.eq with ⟨e, rfl, rfl⟩ | ⟨τ₁, τ₂, rfl, rfl, h⟩
    · rfl
    · simp only [bind, Except.bind]
      rcases (allocDefault_heap h R).cases with ⟨e, h₁, h₂⟩ | ⟨_, _, a, h₁, h₂, _⟩ <;>
        simp only [h₁, h₂] <;> rfl
  | .addM R, _, _, _, _, hx => by
    simp only [Srt.AgreePart, Op1.eval] at hx ⊢
    rcases Res.memPart_cases hx.eq with ⟨e, rfl, rfl⟩ | ⟨τ₁, τ₂, rfl, rfl, h⟩
    · exact ⟨rfl⟩
    · simp only [bind, Except.bind]
      rcases (allocDefault_heap h R).cases with ⟨e, h₁, h₂⟩ | ⟨_, _, a, h₁, h₂, h₃⟩
      · simp only [h₁, h₂]; exact ⟨rfl⟩
      · simp only [h₁, h₂, pure, Except.pure]; exact Res.memPart_ok h₃
  | .wt _, _, _, _, _, hx => by
    simp only [Srt.AgreePart, Op1.eval] at hx ⊢
    rcases Res.stPart_cases hx.eq with ⟨e, rfl, rfl⟩ | ⟨τ₁, τ₂, rfl, rfl, h⟩
    · rfl
    · simp only [bind, Except.bind, h]

theorem Op2.eval_part :
    (o : Op2 a b s) → (o.stDirect = false ∨ σ.storage = τ.storage) → {x₁ x₂ : a.Ev} →
      {y₁ y₂ : b.Ev} → Srt.AgreePart a x₁ x₂ → Srt.AgreePart b y₁ y₂ →
      Srt.AgreePart s (o.eval σ x₁ y₁) (o.eval τ x₂ y₂)
  | .binop .., _, _, _, _, _, hx, hy | .mat, _, _, _, _, _, hx, hy => by
    simp only [Srt.AgreePart] at hx hy ⊢; subst hx hy; rfl
  | .at, ho, _, _, _, _, hx, hy => by
    simp only [Srt.AgreePart] at hx hy ⊢; subst hx hy
    have hst := ho.resolve_left (by simp [Op2.stDirect])
    simp only [Op2.eval, State.checkIndex_of_storage hst]
  | .find, _, _, _, _, _, hx, hy | .sfind, _, _, _, _, _, hx, hy
  | .nextIn, _, _, _, _, _, hx, hy => by
    simp only [Srt.AgreePart, Op2.eval] at hx hy ⊢; subst hy
    rcases Res.stPart_cases hx.eq with ⟨e, rfl, rfl⟩ | ⟨τ₁, τ₂, rfl, rfl, h⟩
    · rfl
    · simp only [bind, Except.bind, State.findStorage_of_storage h]
  | .len, _, _, _, _, _, hx, hy => by
    simp only [Srt.AgreePart, Op2.eval] at hx hy ⊢; subst hy
    rcases Res.stPart_cases hx.eq with ⟨e, rfl, rfl⟩ | ⟨τ₁, τ₂, rfl, rfl, h⟩
    · rfl
    · simp only [bind, Except.bind, arrayLen_of_storage h]
  | .read, _, _, _, _, _, hx, hy | .iread, _, _, _, _, _, hx, hy => by
    simp only [Srt.AgreePart, Op2.eval] at hx hy ⊢; subst hy
    rcases Res.memPart_cases hx.eq with ⟨e, rfl, rfl⟩ | ⟨τ₁, τ₂, rfl, rfl, h⟩
    · rfl
    · simp only [bind, Except.bind, readAddr_of_heap h.1]
  | .mlen, _, _, _, _, _, hx, hy => by
    simp only [Srt.AgreePart, Op2.eval] at hx hy ⊢; subst hy
    rcases Res.memPart_cases hx.eq with ⟨e, rfl, rfl⟩ | ⟨τ₁, τ₂, rfl, rfl, h⟩
    · rfl
    · simp only [bind, Except.bind, memArrayLen_of_heap h.1]
  | .copyMem, _, _, _, _, _, hx, hy => by
    simp only [Srt.AgreePart, Op2.eval] at hx hy ⊢; subst hy
    rcases Res.memPart_cases hx.eq with ⟨e, rfl, rfl⟩ | ⟨τ₁, τ₂, rfl, rfl, h⟩
    · rfl
    · simp only [bind, Except.bind, copyMem_of_heap h.1]
  | .delAt, _, _, _, y, _, hx, hy => by
    simp only [Srt.AgreePart, Op2.eval] at hx hy ⊢; subst hy
    rcases Res.stPart_cases hx.eq with ⟨e, rfl, rfl⟩ | ⟨τ₁, τ₂, rfl, rfl, h⟩
    · exact ⟨rfl⟩
    · simp only [bind, Except.bind, State.findStorage_of_storage h]
      cases y with
      | error e => exact ⟨rfl⟩
      | ok rs =>
        dsimp only
        cases τ₂.findStorage rs.1 rs.2 with
        | error e => exact ⟨rfl⟩
        | ok cur => exact ⟨State.saveStorage_of_storage h _ _ _⟩
  | .pushSlot E, _, _, _, y, _, hx, hy => by
    simp only [Srt.AgreePart, Op2.eval] at hx hy ⊢; subst hy
    rcases Res.stPart_cases hx.eq with ⟨e, rfl, rfl⟩ | ⟨τ₁, τ₂, rfl, rfl, h⟩
    · exact ⟨rfl⟩
    · simp only [bind, Except.bind]
      cases y with
      | error e => exact ⟨rfl⟩
      | ok rs => dsimp only; exact ⟨pushAt_of_storage h E rs.1 rs.2 pure⟩
  | .pop, _, _, _, y, _, hx, hy | .shrink, _, _, _, y, _, hx, hy => by
    simp only [Srt.AgreePart, Op2.eval] at hx hy ⊢; subst hy
    rcases Res.stPart_cases hx.eq with ⟨e, rfl, rfl⟩ | ⟨τ₁, τ₂, rfl, rfl, h⟩
    · exact ⟨rfl⟩
    · simp only [bind, Except.bind]
      cases y with
      | error e => exact ⟨rfl⟩
      | ok rs => dsimp only; exact ⟨popAt_of_storage h _ rs.1 rs.2⟩
  | .extend E, _, _, _, y, _, hx, hy => by
    simp only [Srt.AgreePart, Op2.eval] at hx hy ⊢; subst hy
    rcases Res.stPart_cases hx.eq with ⟨e, rfl, rfl⟩ | ⟨τ₁, τ₂, rfl, rfl, h⟩
    · exact ⟨rfl⟩
    · simp only [bind, Except.bind]
      cases y with
      | error e => exact ⟨rfl⟩
      | ok rs => dsimp only; exact ⟨pushPlaceAt_of_storage h E rs.1 rs.2⟩
  | .copy, _, _, _, y, _, hx, hy => by
    simp only [Srt.AgreePart, Op2.eval] at hx hy ⊢; subst hy
    cases y with
    | error e => rfl
    | ok sv =>
      rcases Res.memPart_cases hx.eq with ⟨e, rfl, rfl⟩ | ⟨τ₁, τ₂, rfl, rfl, h⟩
      · rfl
      · simp only [bind, Except.bind]
        rcases (copyStToM_heap h sv).cases with ⟨e, h₁, h₂⟩ | ⟨_, _, a, h₁, h₂, _⟩ <;>
          simp only [h₁, h₂] <;> rfl
  | .copySt, _, _, _, y, _, hx, hy => by
    simp only [Srt.AgreePart, Op2.eval] at hx hy ⊢; subst hy
    cases y with
    | error e => exact ⟨rfl⟩
    | ok sv =>
      rcases Res.memPart_cases hx.eq with ⟨e, rfl, rfl⟩ | ⟨τ₁, τ₂, rfl, rfl, h⟩
      · exact ⟨rfl⟩
      · simp only [bind, Except.bind]
        rcases (copyStToM_heap h sv).cases with ⟨e, h₁, h₂⟩ | ⟨_, _, a, h₁, h₂, h₃⟩
        · simp only [h₁, h₂]; exact ⟨rfl⟩
        · simp only [h₁, h₂, pure, Except.pure]; exact Res.memPart_ok h₃

theorem Op3.eval_part :
    (o : Op3 a b c s) → {x₁ x₂ : a.Ev} → {y₁ y₂ : b.Ev} → {z₁ z₂ : c.Ev} →
      Srt.AgreePart a x₁ x₂ → Srt.AgreePart b y₁ y₂ → Srt.AgreePart c z₁ z₂ →
      Srt.AgreePart s (o.eval σ x₁ y₁ z₁) (o.eval τ x₂ y₂ z₂)
  | .ite, _, _, _, _, _, _, hx, hy, hz => by
    simp only [Srt.AgreePart] at hx hy hz ⊢; subst hx hy hz; rfl
  | .atIn, _, _, _, _, _, _, hx, hy, hz => by
    simp only [Srt.AgreePart, Op3.eval] at hx hy hz ⊢; subst hy hz
    rcases Res.stPart_cases hx.eq with ⟨e, rfl, rfl⟩ | ⟨τ₁, τ₂, rfl, rfl, h⟩
    · rfl
    · simp only [bind, Except.bind, State.checkIndex_of_storage h]
  | .save, _, _, y, _, z, _, hx, hy, hz => by
    simp only [Srt.AgreePart, Op3.eval] at hx hy hz ⊢; subst hy hz
    cases z with
    | error e => exact ⟨rfl⟩
    | ok sv =>
      rcases Res.stPart_cases hx.eq with ⟨e, rfl, rfl⟩ | ⟨τ₁, τ₂, rfl, rfl, h⟩
      · exact ⟨rfl⟩
      · simp only [bind, Except.bind]
        cases y with
        | error e => exact ⟨rfl⟩
        | ok rs => dsimp only; exact ⟨State.writeStorage_of_storage h rs.1 rs.2 sv⟩
  | .push, _, _, y, _, _, _, hx, hy, hz => by
    simp only [Srt.AgreePart, Op3.eval] at hx hy hz ⊢; subst hy hz
    rcases Res.stPart_cases hx.eq with ⟨e, rfl, rfl⟩ | ⟨τ₁, τ₂, rfl, rfl, h⟩
    · exact ⟨rfl⟩
    · simp only [bind, Except.bind]
      cases y with
      | error e => exact ⟨rfl⟩
      | ok rs => dsimp only; exact ⟨pushAt_of_storage h _ rs.1 rs.2 _⟩
  | .write, _, _, y, _, z, _, hx, hy, hz => by
    simp only [Srt.AgreePart, Op3.eval] at hx hy hz ⊢; subst hy hz
    cases z with
    | error e => exact ⟨rfl⟩
    | ok mv =>
      rcases Res.memPart_cases hx.eq with ⟨e, rfl, rfl⟩ | ⟨τ₁, τ₂, rfl, rfl, h⟩
      · exact ⟨rfl⟩
      · simp only [bind, Except.bind]
        cases y with
        | error e => exact ⟨rfl⟩
        | ok a => dsimp only; exact ⟨writeAddr_of_heap h mv a⟩

end OpPart
end

/-! ## From `Solidity.Calculus.ChainRewrites` -/

section
open Semantics SemanticsProperties
variable {C : Contract}

/-- A member path is a field segment or more. -/
def Seg.isField : Seg → Bool
  | .field _ => true
  | .at _ => false

/-- The Theory's `diverges` gives the interpreter's `Diverge`. -/
theorem Diverge_of_diverges : (a b : List Seg) → Theory.StValue.diverges a b = true → Close.Diverge a b
  | [], _, h => nomatch h
  | _ :: _, [], h => nomatch h
  | x :: p, y :: q, h => by
    simp only [Theory.StValue.diverges] at h
    split at h
    · exact Or.inr (Diverge_of_diverges p q h)
    · exact Or.inl ‹_›

/-- A reset struct keeps its members, each reset: a word read below the node
reads a word after the reset. -/
theorem Semantics.SVal.find_defaultOf_prim : (tail : List Seg) → tail.all Seg.isField = true → (v : SVal) →
    ∀ {x : PrimVal}, v.find tail = .ok (.prim x) → ∃ y, v.defaultOf.find tail = .ok (.prim y)
  | [], _, v, x, h => by
    rw [SVal.find_nil] at h
    cases h
    cases x <;> exact ⟨_, rfl⟩
  | .field n :: rest, hf, v, x, h => by
    simp only [List.all_cons, Seg.isField, Bool.true_and] at hf
    cases v with
    | prim _ => nomatch h
    | map _ _ => nomatch h
    | struct fields =>
      simp only [SVal.find] at h
      split at h
      · rename_i u hu
        obtain ⟨y, hy⟩ := SVal.find_defaultOf_prim rest hf u h
        refine ⟨y, ?_⟩
        simp only [SVal.defaultOf, SVal.find, lookupBy_defaultOfFields, hu, Option.map_some]
        exact hy
      · nomatch h
    | array elems sh fx =>
      by_cases hn : n = "length"
      · subst hn
        cases fx with
        | true => nomatch h
        | false =>
          cases rest with
          | nil =>
            exact ⟨.int 0, rfl⟩
          | cons _ _ => nomatch h
      · exact absurd h (by cases rest <;> simp [SVal.find])
  | .at _ :: _, hf, _, _, _ => by
    simp only [List.all_cons, Seg.isField, Bool.false_and, Bool.false_eq_true] at hf

/-- A write that returned saved, with the value it wrote laid over the old one
where it is not a word. -/
theorem Semantics.State.writeStorage_ok {σ τ : State} {r : Name} {segs : List Seg} {v : SVal}
    (h : σ.writeStorage r segs v = .ok τ) : ∃ x, σ.saveStorage r segs x = .ok τ := by
  cases v with
  | prim _ => exact ⟨_, h⟩
  | struct _ =>
    simp only [State.writeStorage] at h
    obtain ⟨cur, -, h⟩ := bind_ok_inv h
    exact ⟨_, h⟩
  | array _ _ _ =>
    simp only [State.writeStorage] at h
    obtain ⟨cur, -, h⟩ := bind_ok_inv h
    exact ⟨_, h⟩
  | map _ _ =>
    simp only [State.writeStorage] at h
    obtain ⟨cur, -, h⟩ := bind_ok_inv h
    exact ⟨_, h⟩

/-- `select(s, r)`'s run on the state `s` leaves: that state with the struct
at the root `r` for its storage (`Op1.eval`). -/
def Semantics.State.selectRoot (r : Name) (τ : State) : Res State := do
  match ← τ.findStorage r [] with
  | .struct fields => pure { τ with storage := fields }
  | .prim _ | .array .. | .map .. => .error .undef

/-- The frame `F`: the state with the struct at `r₁.r₂…` for its storage. -/
def Semantics.State.frameOf : List Name → State → Res State
  | [], τ => .ok τ
  | r :: F, τ => State.selectRoot r τ >>= State.frameOf F

theorem Semantics.State.frameOf_append (F G : List Name) (τ : State) :
    State.frameOf (F ++ G) τ = (State.frameOf F τ >>= State.frameOf G) := by
  induction F generalizing τ with
  | nil => rfl
  | cons r F ih =>
    simp only [List.cons_append, State.frameOf]
    cases State.selectRoot r τ with
    | error e => rfl
    | ok τ' => exact ih τ'

/-- In the frame at `r`, a read at `g.segs` is the read at `r.g.segs` outside it. -/
theorem Semantics.State.findStorage_selectRoot {r : Name} {τ τ' : State} (h : State.selectRoot r τ = .ok τ')
    (g : Name) (segs : List Seg) : τ'.findStorage g segs = τ.findStorage r (.field g :: segs) := by
  unfold State.selectRoot at h
  simp only [State.findStorage] at h
  cases hv : lookupBy r τ.storage with
  | none =>
    rw [hv] at h
    simp [bind, Except.bind] at h
  | some V =>
    rw [hv] at h
    cases V with
    | struct fields =>
      simp only [SVal.find, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
      subst h
      simp only [State.findStorage, hv, SVal.find]
    | prim _ | array _ _ _ | map _ _ => simp [SVal.find, bind, Except.bind] at h

/-- In the frame at `r`, a write at `g.rest` is the write at `r.g.rest` outside
it, the frame taken after: the two runs end alike. -/
theorem Semantics.State.saveStorage_selectRoot (r : Name) (τ : State) (g : Name) (rest : List Seg) (new : SVal) :
    (τ.saveStorage r (.field g :: rest) new >>= State.selectRoot r) =
      (State.selectRoot r τ >>= fun τ' => τ'.saveStorage g rest new) := by
  unfold State.selectRoot State.saveStorage
  simp only [State.findStorage]
  cases hv : lookupBy r τ.storage with
  | none => simp [bind, Except.bind]
  | some V =>
    cases V with
    | prim _ | array _ _ _ | map _ _ => simp [SVal.save, SVal.find, bind, Except.bind]
    | struct fields =>
      cases hg : lookupBy g fields with
      | none => simp [SVal.save, SVal.find, hg, bind, Except.bind, pure, Except.pure]
      | some old =>
        cases hs : old.save rest new with
        | error e => simp [SVal.save, SVal.find, hg, hs, bind, Except.bind, pure, Except.pure]
        | ok upd =>
          simp [SVal.save, SVal.find, hg, hs, bind, Except.bind, pure, Except.pure, lookupBy_setBy_self]

/-- Where a run returns, the other returns the same: the two agree but for
how they halt. -/
def Semantics.Res.OkEq {α : Type} (a b : Res α) : Prop := ∀ x, a = .ok x ↔ b = .ok x

theorem Semantics.Res.OkEq.refl {α : Type} (a : Res α) : Res.OkEq a a := fun _ => Iff.rfl

theorem Semantics.Res.OkEq.symm {α : Type} {a b : Res α} (h : Res.OkEq a b) : Res.OkEq b a :=
  fun x => (h x).symm

theorem Semantics.Res.OkEq.trans {α : Type} {a b c : Res α} (h : Res.OkEq a b) (h' : Res.OkEq b c) :
    Res.OkEq a c := fun x => (h x).trans (h' x)

theorem Semantics.Res.OkEq.of_eq {α : Type} {a b : Res α} (h : a = b) : Res.OkEq a b := h ▸ Res.OkEq.refl a

theorem Semantics.Res.OkEq.le {α : Type} {a b : Res α} (h : Res.OkEq a b) : Res.Le a b := fun x => (h x).1

theorem Semantics.Res.OkEq.ge {α : Type} {a b : Res α} (h : Res.OkEq a b) : Res.Le b a := fun x => (h x).2

theorem Semantics.Res.OkEq.bind {α β : Type} {a a' : Res α} {f f' : α → Res β} (ha : Res.OkEq a a')
    (hf : ∀ x, Res.OkEq (f x) (f' x)) : Res.OkEq (a >>= f) (a' >>= f') := fun y => by
  constructor
  · intro h
    obtain ⟨x, hx, hy⟩ := bind_ok_inv h
    rw [(ha x).1 hx]
    exact (hf x y).1 hy
  · intro h
    obtain ⟨x, hx, hy⟩ := bind_ok_inv h
    rw [(ha x).2 hx]
    exact (hf x y).2 hy

/-- In the frame at `r`, a write of a value at `g.rest` is the write at
`r.g.rest` outside it, the frame taken after. -/
theorem Semantics.State.writeStorage_selectRoot (r : Name) (τ : State) (g : Name) (rest : List Seg) (new : SVal) :
    Res.OkEq (τ.writeStorage r (.field g :: rest) new >>= State.selectRoot r)
      (State.selectRoot r τ >>= fun τ' => τ'.writeStorage g rest new) := by
  have key : ∀ x : SVal, Res.OkEq
      ((τ.findStorage r (.field g :: rest) >>= fun cur =>
        τ.saveStorage r (.field g :: rest) (cur.overlay x)) >>= State.selectRoot r)
      (State.selectRoot r τ >>= fun τ' => τ'.findStorage g rest >>= fun cur =>
        τ'.saveStorage g rest (cur.overlay x)) := by
    intro x
    cases hs : State.selectRoot r τ with
    | ok τ' =>
      simp only [bind, Except.bind]
      rw [State.findStorage_selectRoot hs]
      cases τ.findStorage r (.field g :: rest) with
      | error e => exact Res.OkEq.refl _
      | ok cur =>
        have e := State.saveStorage_selectRoot r τ g rest (cur.overlay x)
        rw [hs] at e
        simp only [bind, Except.bind] at e
        exact Res.OkEq.of_eq e
    | error e =>
      -- the root is no struct: the write outside halts too
      intro y
      constructor
      · intro h
        obtain ⟨τ₁, h₁, h₂⟩ := bind_ok_inv h
        obtain ⟨cur, -, h₁⟩ := bind_ok_inv h₁
        have e' := State.saveStorage_selectRoot r τ g rest (cur.overlay x)
        rw [hs, h₁] at e'
        simp only [bind, Except.bind] at e'
        rw [e'] at h₂
        cases h₂
      · intro h
        simp [bind, Except.bind] at h
  cases new with
  | prim _ => exact Res.OkEq.of_eq (State.saveStorage_selectRoot r τ g rest _)
  | struct fs => exact key (.struct fs)
  | array a b c => exact key (.array a b c)
  | map a b => exact key (.map a b)

/-- `delete` at `g.segs`: the slot read, then written to its default. -/
def _root_.Solidity.Semantics.State.delAtAt (τ : State) (g : Name) (segs : List Seg) : Res State :=
  τ.findStorage g segs >>= fun cur => τ.saveStorage g segs cur.defaultOf

/-- A storage word and its default either both fail to be words, or read as
the value and its primitive default. -/
theorem Semantics.SVal.defaultOf_asValue_primDefault (v : SVal) :
    v.defaultOf.asValue = (do pure (Theory.StValue.primDefault (← v.asValue))) := by
  cases v with
  | prim p => cases p <;> rfl
  | struct _ | map _ _ => rfl
  | array _ _ fx => cases fx <;> rfl

/-- A write below an array keeps its length. -/
theorem Close.arrLen_save_cons {a : Seg} {rest : List Seg} {old new upd : SVal}
    (h : old.save (a :: rest) new = .ok upd) : Close.arrLen upd = Close.arrLen old := by
  cases old with
  | prim _ => cases a <;> simp [SVal.save] at h
  | struct fields =>
    cases a with
    | «at» _ => simp [SVal.save] at h
    | field n =>
      simp only [SVal.save] at h
      split at h
      · obtain ⟨u, _, h⟩ := bind_ok_inv h
        cases h
        rfl
      · simp at h
  | array elems shadow fx =>
    cases a with
    | field _ => simp [SVal.save] at h
    | «at» i =>
      simp only [SVal.save] at h
      split at h
      · obtain ⟨u, _, h⟩ := bind_ok_inv h
        cases h
        have hlen : (((elems ++ shadow).set i.toNat u).take elems.length).length =
            elems.length := by simp
        simp only [Close.arrLen, hlen]
      · simp at h
  | map entries dflt =>
    cases a with
    | field _ => simp [SVal.save] at h
    | «at» i =>
      simp only [SVal.save] at h
      split at h <;> (obtain ⟨u, _, h⟩ := bind_ok_inv h; cases h; rfl)

/-- Reading an array length above or apart from a write gives its old
length. -/
theorem Close.find_save_arrLen : ∀ {p q : List Seg} {old new upd : SVal},
    old.save p new = .ok upd → ¬ Close.Prefix p q →
      (upd.find q >>= Close.arrLen) = (old.find q >>= Close.arrLen)
  | [], _, _, _, _, _, hq => (hq trivial).elim
  | _ :: _, [], _, _, _, hs, _ => by
      simp only [SVal.find_nil, bind, Except.bind]
      exact Close.arrLen_save_cons hs
  | a :: p, b :: q, old, upd, new, hs, hq => by
      by_cases hab : a = b
      · subst hab
        have hq' : ¬ Close.Prefix p q := fun h => hq ⟨rfl, h⟩
        obtain ⟨c, u, hu, hf⟩ := Close.save_cons_find hs
        rw [(hf q).1, (hf q).2]
        exact Close.find_save_arrLen hu hq'
      · rw [Close.find_save_diverge (show Close.Diverge (a :: p) (b :: q) from Or.inl hab) hs]

/-- `find_save_arrLen` at a root of the storage. -/
theorem Close.arrayLen_saveStorage_frame {σ τ : State} {r r' : Name} {p q : List Seg}
    {v : SVal} (h : σ.saveStorage r p v = .ok τ)
    (hq : r' ≠ r ∨ ¬ Close.Prefix p q) : arrayLen τ r' q = arrayLen σ r' q := by
  rw [Close.arrayLen_eq, Close.arrayLen_eq]
  unfold State.saveStorage at h
  split at h
  · rename_i old hl
    obtain ⟨u, hu, h⟩ := bind_ok_inv h
    cases h
    by_cases hr : r' = r
    · subst hr
      simp only [State.findStorage, lookupBy_setBy_self, hl]
      exact Close.find_save_arrLen hu (hq.resolve_left (· rfl))
    · simp only [State.findStorage, lookupBy_setBy_ne hr]
  · simp at h

/-- A divergent path is not a prefix of the path it diverges from. -/
theorem Close.Diverge.not_prefix : ∀ {p q : List Seg}, Close.Diverge p q → ¬ Close.Prefix p q
  | _ :: _, _ :: _, h => fun hp => by
      rcases h with h | h
      · exact h hp.1
      · exact h.not_prefix hp.2

/-- A prefix remains a prefix when the path on the right is extended. -/
theorem Close.Prefix.right_append : ∀ {p q : List Seg}, Close.Prefix p q → (tail : List Seg) →
    Close.Prefix p (q ++ tail)
  | [], _, _, _ => trivial
  | _ :: _, _ :: _, h, tail => ⟨h.1, h.2.right_append tail⟩

/-- In the frame at `r`, a delete at `g.rest` is the delete at `r.g.rest`
outside it, the frame taken after. -/
theorem Semantics.State.delAtAt_selectRoot (r : Name) (τ : State) (g : Name) (rest : List Seg) :
    Res.OkEq (τ.delAtAt r (.field g :: rest) >>= State.selectRoot r)
      (State.selectRoot r τ >>= fun τ' => τ'.delAtAt g rest) := by
  unfold State.delAtAt
  cases hs : State.selectRoot r τ with
  | ok τ' =>
    simp only [bind, Except.bind]
    rw [State.findStorage_selectRoot hs]
    cases τ.findStorage r (.field g :: rest) with
    | error e => exact Res.OkEq.refl _
    | ok cur =>
      have e := State.saveStorage_selectRoot r τ g rest cur.defaultOf
      rw [hs] at e
      simp only [bind, Except.bind] at e
      exact Res.OkEq.of_eq e
  | error e =>
    intro x
    constructor
    · intro h
      obtain ⟨τ₁, h₁, h₂⟩ := bind_ok_inv h
      obtain ⟨cur, -, h₁⟩ := bind_ok_inv h₁
      have e' := State.saveStorage_selectRoot r τ g rest cur.defaultOf
      rw [hs, h₁] at e'
      simp only [bind, Except.bind] at e'
      rw [e'] at h₂
      cases h₂
    · intro h
      simp [bind, Except.bind] at h

theorem Semantics.Res.bind_assoc {α β γ : Type} (x : Res α) (f : α → Res β) (g : β → Res γ) :
    ((x >>= f) >>= g) = (x >>= fun a => f a >>= g) := by cases x <;> rfl

/-- A read of a word through a node that is no struct halts, but at the
`length` of an array with nothing after it. -/
theorem Semantics.SVal.find_field_of_nonStruct {V : SVal} (hV : ∀ fields, V ≠ .struct fields) {g : Name}
    {segs : List Seg} (hg : g = "length" → segs ≠ []) {x : SVal} :
    V.find (.field g :: segs) ≠ .ok x := by
  cases V with
  | struct fields => exact absurd rfl (hV fields)
  | prim _ => simp [SVal.find]
  | map _ _ => simp [SVal.find]
  | array elems sh fx =>
    by_cases h : g = "length"
    · subst h
      cases fx with
      | true => simp [SVal.find]
      | false =>
        cases segs with
        | nil => exact absurd rfl (hg rfl)
        | cons _ _ => simp [SVal.find]
    · simp [SVal.find]

theorem Semantics.Res.bind_pure_ok {α : Type} (x : Res α) : (x >>= fun a => (Except.ok a : Res α)) = x := by
  cases x <;> rfl

/-- A read in the frame `F` is the read outside it, at `F`'s members then the
path, where the path's root is not an array's `length`. -/
theorem Semantics.State.frameOf_findStorage (r₁ : Name) (g : Name) (segs : List Seg) (hg : g ≠ "length") :
    (F' : List Name) → (τ : State) →
      Res.OkEq (State.frameOf (r₁ :: F') τ >>= fun τ' => τ'.findStorage g segs)
        (τ.findStorage r₁ (F'.map Seg.field ++ (.field g :: segs)))
  | [], τ => by
    show Res.OkEq ((State.selectRoot r₁ τ >>= fun x => (Except.ok x : Res State)) >>= fun τ' =>
      τ'.findStorage g segs) _
    rw [Res.bind_pure_ok]
    simp only [List.map_nil, List.nil_append]
    cases hs : State.selectRoot r₁ τ with
    | ok τ' =>
      rw [Res.ok_bind']
      exact Res.OkEq.of_eq (State.findStorage_selectRoot hs g segs)
    | error e =>
      intro x
      constructor
      · intro h; simp [bind, Except.bind] at h
      · intro h
        exfalso
        unfold State.selectRoot at hs
        simp only [State.findStorage] at hs h
        cases hv : lookupBy r₁ τ.storage with
        | none => rw [hv] at h; cases h
        | some V =>
          rw [hv] at hs h
          cases V with
          | struct fields => simp [SVal.find, bind, Except.bind, pure, Except.pure] at hs
          | prim _ | map _ _ | array _ _ _ =>
            exact SVal.find_field_of_nonStruct (by intro _ h; cases h) (fun h' _ => hg h') h
  | r₂ :: F'', τ => by
    show Res.OkEq ((State.selectRoot r₁ τ >>= State.frameOf (r₂ :: F'')) >>= fun τ' =>
      τ'.findStorage g segs) _
    simp only [List.map_cons, List.cons_append]
    cases hs : State.selectRoot r₁ τ with
    | ok τ' =>
      rw [Res.ok_bind']
      exact (State.frameOf_findStorage r₂ g segs hg F'' τ').trans
        (Res.OkEq.of_eq (State.findStorage_selectRoot hs _ _))
    | error e =>
      intro x
      constructor
      · intro h; simp [bind, Except.bind] at h
      · intro h
        exfalso
        unfold State.selectRoot at hs
        simp only [State.findStorage] at hs h
        cases hv : lookupBy r₁ τ.storage with
        | none => rw [hv] at h; cases h
        | some V =>
          rw [hv] at hs h
          cases V with
          | struct fields => simp [SVal.find, bind, Except.bind, pure, Except.pure] at hs
          | prim _ | map _ _ | array _ _ _ =>
            exact SVal.find_field_of_nonStruct (by intro _ h; cases h)
              (fun _ h' => by simp at h') h

/-- A write in the frame `F` is the write outside it, the frame taken after. -/
theorem Semantics.State.frameOf_writeStorage (r₁ : Name) (g : Name) (segs : List Seg) (sv : SVal) :
    (F' : List Name) → (τ : State) →
      Res.OkEq (τ.writeStorage r₁ (F'.map Seg.field ++ (.field g :: segs)) sv >>= State.frameOf (r₁ :: F'))
        (State.frameOf (r₁ :: F') τ >>= fun τ' => τ'.writeStorage g segs sv)
  | [], τ => by
    show Res.OkEq (τ.writeStorage r₁ ([].map Seg.field ++ (.field g :: segs)) sv >>= fun x =>
        State.selectRoot r₁ x >>= fun x => (Except.ok x : Res State))
      ((State.selectRoot r₁ τ >>= fun x => (Except.ok x : Res State)) >>= fun τ' =>
        τ'.writeStorage g segs sv)
    simp only [Res.bind_pure_ok, List.map_nil, List.nil_append]
    exact State.writeStorage_selectRoot r₁ τ g segs sv
  | r₂ :: F'', τ => by
    show Res.OkEq (τ.writeStorage r₁ ((r₂ :: F'').map Seg.field ++ (.field g :: segs)) sv >>= fun x =>
        State.selectRoot r₁ x >>= State.frameOf (r₂ :: F''))
      ((State.selectRoot r₁ τ >>= State.frameOf (r₂ :: F'')) >>= fun τ' => τ'.writeStorage g segs sv)
    simp only [List.map_cons, List.cons_append]
    rw [← Res.bind_assoc, Res.bind_assoc (State.selectRoot r₁ τ)]
    refine Res.OkEq.trans (Res.OkEq.bind (State.writeStorage_selectRoot r₁ τ r₂ _ sv)
      fun _ => Res.OkEq.refl _) ?_
    rw [Res.bind_assoc]
    exact Res.OkEq.bind (Res.OkEq.refl _) fun τ' => State.frameOf_writeStorage r₂ g segs sv F'' τ'

/-- A delete in the frame `F` is the delete outside it, the frame taken after. -/
theorem Semantics.State.frameOf_delAtAt (r₁ : Name) (g : Name) (segs : List Seg) :
    (F' : List Name) → (τ : State) →
      Res.OkEq (τ.delAtAt r₁ (F'.map Seg.field ++ (.field g :: segs)) >>= State.frameOf (r₁ :: F'))
        (State.frameOf (r₁ :: F') τ >>= fun τ' => τ'.delAtAt g segs)
  | [], τ => by
    show Res.OkEq (τ.delAtAt r₁ ([].map Seg.field ++ (.field g :: segs)) >>= fun x =>
        State.selectRoot r₁ x >>= fun x => (Except.ok x : Res State))
      ((State.selectRoot r₁ τ >>= fun x => (Except.ok x : Res State)) >>= fun τ' => τ'.delAtAt g segs)
    simp only [Res.bind_pure_ok, List.map_nil, List.nil_append]
    exact State.delAtAt_selectRoot r₁ τ g segs
  | r₂ :: F'', τ => by
    show Res.OkEq (τ.delAtAt r₁ ((r₂ :: F'').map Seg.field ++ (.field g :: segs)) >>= fun x =>
        State.selectRoot r₁ x >>= State.frameOf (r₂ :: F''))
      ((State.selectRoot r₁ τ >>= State.frameOf (r₂ :: F'')) >>= fun τ' => τ'.delAtAt g segs)
    simp only [List.map_cons, List.cons_append]
    rw [← Res.bind_assoc, Res.bind_assoc (State.selectRoot r₁ τ)]
    refine Res.OkEq.trans (Res.OkEq.bind (State.delAtAt_selectRoot r₁ τ r₂ _)
      fun _ => Res.OkEq.refl _) ?_
    rw [Res.bind_assoc]
    exact Res.OkEq.bind (Res.OkEq.refl _) fun τ' => State.frameOf_delAtAt r₂ g segs F'' τ'

/-- A save at `r.g.rest` that returned went through the struct at `r`, before
and after: the save at `g.rest` in that frame. -/
theorem Semantics.State.saveStorage_field_ok {r g : Name} {rest : List Seg} {new : SVal} {τ τ₁ : State}
    (h : τ.saveStorage r (.field g :: rest) new = .ok τ₁) :
    ∃ τ' τ₁', State.selectRoot r τ = .ok τ' ∧ State.selectRoot r τ₁ = .ok τ₁' ∧
      τ'.saveStorage g rest new = .ok τ₁' := by
  have e := State.saveStorage_selectRoot r τ g rest new
  rw [h, Res.ok_bind'] at e
  obtain ⟨V, up, hV, hs, rfl⟩ := State.saveStorage_ok_inv h
  cases V with
  | prim _ | array _ _ _ | map _ _ => simp [SVal.save] at hs
  | struct fields =>
    have hsel : State.selectRoot r τ = .ok { τ with storage := fields } := by
      unfold State.selectRoot
      simp [State.findStorage, hV, SVal.find, bind, Except.bind, pure, Except.pure]
    rw [hsel, Res.ok_bind'] at e
    simp only [SVal.save] at hs
    cases hg : lookupBy g fields with
    | none => simp [hg] at hs
    | some old =>
      simp only [hg] at hs
      cases hs' : old.save rest new with
      | error _ => simp [hs', bind, Except.bind] at hs
      | ok u' =>
        simp only [hs', bind, Except.bind, Except.ok.injEq] at hs
        subst hs
        have inner : State.saveStorage { τ with storage := fields } g rest new =
            .ok { τ with storage := setBy g u' fields } := by
          unfold State.saveStorage
          simp [hg, hs', bind, Except.bind]
        exact ⟨_, _, hsel, by rw [e]; exact inner, inner⟩

/-- The frame `F` of a save at `F.g.segs` that returned exists, before and after it. -/
theorem Semantics.State.frameOf_of_saveStorage (r₁ g : Name) (segs : List Seg) (new : SVal) :
    (F' : List Name) → (τ τ₁ : State) →
      τ.saveStorage r₁ (F'.map Seg.field ++ (.field g :: segs)) new = .ok τ₁ →
      (∃ τ', State.frameOf (r₁ :: F') τ = .ok τ') ∧ ∃ τ₁', State.frameOf (r₁ :: F') τ₁ = .ok τ₁'
  | [], τ, τ₁, h => by
    obtain ⟨τ', τ₁', hs, hs₁, -⟩ := State.saveStorage_field_ok h
    refine ⟨⟨τ', ?_⟩, ⟨τ₁', ?_⟩⟩
    · show (State.selectRoot r₁ τ >>= State.frameOf []) = _
      rw [hs]; rfl
    · show (State.selectRoot r₁ τ₁ >>= State.frameOf []) = _
      rw [hs₁]; rfl
  | r₂ :: F'', τ, τ₁, h => by
    obtain ⟨τ', τ₁', hs, hs₁, h'⟩ := State.saveStorage_field_ok h
    obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := State.frameOf_of_saveStorage r₂ g segs new F'' τ' τ₁' h'
    refine ⟨⟨a, ?_⟩, ⟨b, ?_⟩⟩
    · show (State.selectRoot r₁ τ >>= State.frameOf (r₂ :: F'')) = _
      rw [hs, Res.ok_bind']; exact ha
    · show (State.selectRoot r₁ τ₁ >>= State.frameOf (r₂ :: F'')) = _
      rw [hs₁, Res.ok_bind']; exact hb

/-- A write of the frame `F` at `F.p` that returned leaves the frame in place. -/
theorem Semantics.State.frameOf_of_writeStorage {r₁ g : Name} {segs : List Seg} {sv : SVal} {F' : List Name}
    {τ τ₁ : State} (h : τ.writeStorage r₁ (F'.map Seg.field ++ (.field g :: segs)) sv = .ok τ₁) :
    ∃ τ₁', State.frameOf (r₁ :: F') τ₁ = .ok τ₁' := by
  obtain ⟨x, hx⟩ := State.writeStorage_ok h
  exact (State.frameOf_of_saveStorage r₁ g segs x F' τ τ₁ hx).2

theorem Semantics.State.frameOf_of_delAtAt {r₁ g : Name} {segs : List Seg} {F' : List Name} {τ τ₁ : State}
    (h : τ.delAtAt r₁ (F'.map Seg.field ++ (.field g :: segs)) = .ok τ₁) :
    ∃ τ₁', State.frameOf (r₁ :: F') τ₁ = .ok τ₁' := by
  obtain ⟨cur, -, hx⟩ := bind_ok_inv h
  exact (State.frameOf_of_saveStorage r₁ g segs cur.defaultOf F' τ τ₁ hx).2

theorem Semantics.Value.toMVal_asValue (v : Value) : v.toMVal.asValue = .ok v := by cases v <;> rfl

theorem PrimVal.asValue_eq (p : PrimVal) : (SVal.prim p).asValue = (MVal.prim p).asValue := by
  cases p <;> rfl

theorem Semantics.SVal.strip_asValue (v : SVal) : v.strip.asValue = v.asValue := by cases v <;> rfl

theorem Semantics.SVal.overlay_asValue (old new : SVal) : (old.overlay new).asValue = new.asValue := by
  cases old <;> cases new <;> first | rfl | exact SVal.strip_asValue _

theorem Close.layAt_asValue (old : SVal) (q : List Seg) (v : SVal) :
    (Close.layAt old q v).asValue = v.asValue := by
  induction q generalizing old with
  | nil => simp only [Close.layAt]; exact SVal.overlay_asValue old v
  | cons sg q ih =>
    cases sg with
    | «at» _ => cases old <;> simp only [Close.layAt] <;> exact SVal.strip_asValue v
    | field f =>
      cases old with
      | struct ofs =>
        simp only [Close.layAt]
        cases lookupBy f ofs with
        | none => exact SVal.strip_asValue v
        | some o => exact ih o
      | prim _ | array _ _ _ | map _ _ => simp only [Close.layAt]; exact SVal.strip_asValue v

/-- A member read at a word below a storage write reads the word written
there, whatever the write copied over. -/
theorem Semantics.State.writeStorage_find_field {σ τ : State} {r : Name} {segs : List Seg} {sv : SVal}
    (h : σ.writeStorage r segs sv = .ok τ) (f : Name) :
    (τ.findStorage r (segs ++ [.field f]) >>= SVal.asValue) = (sv.find [.field f] >>= SVal.asValue) := by
  rw [State.findStorage_append]
  unfold State.writeStorage at h
  cases sv with
  | prim p =>
    rw [State.findStorage_saveStorage_same h]
    rfl
  | struct _ | array _ _ _ | map _ _ =>
    simp only [bind, Except.bind] at h
    cases hc : σ.findStorage r segs with
    | error e => rw [hc] at h; cases h
    | ok cur =>
      rw [hc] at h
      rw [State.findStorage_saveStorage_same h, Res.ok_bind', Close.find_overlay_fields _ _ _ rfl]
      cases SVal.find _ [Seg.field f] with
      | error _ => rfl
      | ok v => simp only [bind, Except.bind, Close.layAt_asValue]

/-- A member copied out of memory reads as the member in memory: a word as
the word, a reference as no word. -/
theorem Close.copyLeaf_asValue (σ : State) (id : Nat) (mv : MVal) (x : Value) :
    (Close.copyLeaf σ id mv >>= SVal.asValue) = .ok x ↔ mv.asValue = .ok x := by
  cases mv with
  | prim p => rw [Close.copyLeaf_prim, Res.ok_bind', PrimVal.asValue_eq]
  | ref id' =>
    unfold Close.copyLeaf
    rw [copyMToSt.eq_def]
    simp only
    constructor
    · intro h
      exfalso
      split at h
      · split at h
        · rename_i hmem _ fields hg
          rcases hcf : copyMFields σ (((List.map Prod.fst σ.heap).erase id).erase id') fields with _ | sf <;>
            simp [hcf, bind, Except.bind, SVal.asValue] at h
        · rename_i hmem _ elems fx hg
          rcases hcf : copyMElems σ (((List.map Prod.fst σ.heap).erase id).erase id') elems with _ | se <;>
            simp [hcf, bind, Except.bind, SVal.asValue] at h
        · simp [bind, Except.bind] at h
      · simp [bind, Except.bind] at h
    · intro h; cases h

theorem Ty.memberTy_snoc_some {T T' : Ty} {p : List Seg} {s : Seg}
    (h : T.memberTy (p ++ [s]) = some T') : ∃ R', T.memberTy p = some (.ref R') := by
  rw [Ty.memberTy_append] at h
  cases hp : T.memberTy p with
  | none => simp [hp] at h
  | some T'' =>
    cases T'' with
    | prim q => simp [hp, Ty.memberTy, Ty.at_prim] at h
    | ref R' => exact ⟨R', rfl⟩

end

/-! ## From `Solidity.Calculus.TermTaclets` -/

section
open Semantics Theory Theory.StValue
variable {C : Contract}

/-- The shape of a path's segment: a member, or an element at a literal
index (`some k`) or at an index the syntax does not decide (`none`: a
local, a length, the slot past the end). -/
inductive SegT where
  | field (f : Name)
  | at (k : Option Int)
  deriving DecidableEq, Repr

/-- The segment has the shape. -/
def SegT.fits : SegT → Seg → Bool
  | .field f, .field g => f == g
  | .at (some k), .at i => k == i
  | .at none, .at _ => true
  | _, _ => false

/-- The path has the shape, segment by segment. -/
def SegT.matches : List SegT → List Seg → Bool
  | [], [] => true
  | x :: a, s :: p => x.fits s && SegT.matches a p
  | _, _ => false

/-- Whether two shapes tell their segments apart: `some true` when the
segments differ in every state (a member against an element, two members
or two literal indices by name or value), `some false` when they are one
segment in every state, `none` when a symbolic index decides nothing. -/
def SegT.apart : SegT → SegT → Option Bool
  | .field f, .field g => some (f != g)
  | .field _, .at _ => some true
  | .at _, .field _ => some true
  | .at (some i), .at (some j) => some (i != j)
  | .at none, .at _ => none
  | .at (some _), .at none => none

/-- The two shapes leave each other: at some position both have a segment
and the segments differ, the ones before being the same — the syntactic
form of the Theory's `diverges`.  A symbolic index decides nothing. -/
def SegT.diverges : List SegT → List SegT → Bool
  | x :: a, y :: b => match x.apart y with
    | some true => true
    | some false => SegT.diverges a b
    | none => false
  | _, _ => false

/-- Two paths that have the shapes `a ++ b` have the shape of their halves. -/
theorem SegT.matches_append : (a b : List SegT) → (p q : List Seg) → SegT.matches a p = true →
    SegT.matches b q = true → SegT.matches (a ++ b) (p ++ q) = true
  | [], _, [], _, _, hb => hb
  | x :: a, b, s :: p, q, ha, hb => by
    simp only [SegT.matches, Bool.and_eq_true] at ha
    simp only [List.cons_append, SegT.matches, ha.1, SegT.matches_append a b p q ha.2 hb,
      Bool.and_self]
  | [], _, _ :: _, _, ha, _ | _ :: _, _, [], _, ha, _ => nomatch ha

/-- `apart` decides the segments as it says. -/
theorem SegT.apart_sound : {x y : SegT} → {d : Bool} → {s t : Seg} → x.apart y = some d →
    x.fits s = true → y.fits t = true → (d = true → s ≠ t) ∧ (d = false → s = t)
  | .field _, .field _, _, .field _, .field _, h, hs, ht => by
    simp only [SegT.fits, beq_iff_eq] at hs ht
    simp only [SegT.apart, Option.some.injEq] at h
    subst hs ht h
    exact ⟨fun hne e => (bne_iff_ne.1 hne) (Seg.field.inj e),
      fun he => by rw [bne_eq_false_iff_eq.1 he]⟩
  | .at (some _), .at (some _), _, .at _, .at _, h, hs, ht => by
    simp only [SegT.fits, beq_iff_eq] at hs ht
    simp only [SegT.apart, Option.some.injEq] at h
    subst hs ht h
    exact ⟨fun hne e => (bne_iff_ne.1 hne) (Seg.at.inj e),
      fun he => by rw [bne_eq_false_iff_eq.1 he]⟩
  | .field _, .at _, _, .field _, .at _, h, _, _ | .at _, .field _, _, .at _, .field _, h, _, _ => by
    simp only [SegT.apart, Option.some.injEq] at h
    subst h
    exact ⟨fun _ e => Seg.noConfusion e, fun h => nomatch h⟩
  | .at none, .at _, _, _, _, h, _, _ | .at (some _), .at none, _, _, _, h, _, _ => by
    simp only [SegT.apart, reduceCtorEq] at h
  | .field _, _, _, .at _, _, _, hs, _ | .at _, _, _, .field _, _, _, hs, _ => by
    simp only [SegT.fits, Bool.false_eq_true] at hs
  | _, .field _, _, _, .at _, _, _, ht | _, .at _, _, _, .field _, _, _, ht => by
    simp only [SegT.fits, Bool.false_eq_true] at ht

/-- Shapes that diverge have paths that diverge. -/
theorem SegT.diverges_sound : (a b : List SegT) → (p q : List Seg) → SegT.diverges a b = true →
    SegT.matches a p = true → SegT.matches b q = true → Theory.StValue.diverges p q = true
  | x :: a, y :: b, s :: p, t :: q, hd, ha, hb => by
    simp only [SegT.matches, Bool.and_eq_true] at ha hb
    simp only [SegT.diverges] at hd
    simp only [Theory.StValue.diverges]
    cases hx : x.apart y with
    | none => rw [hx] at hd; cases hd
    | some d =>
      rw [hx] at hd
      have hst := SegT.apart_sound hx ha.1 hb.1
      cases d with
      | true => rw [if_neg (hst.1 rfl)]
      | false =>
        rw [if_pos (hst.2 rfl)]
        exact SegT.diverges_sound a b p q hd ha.2 hb.2
  | [], _, _, _, hd, _, _ | _ :: _, [], _, _, hd, _, _ => nomatch hd
  | _ :: _, _ :: _, [], _, _, ha, _ => nomatch ha
  | _ :: _, _ :: _, _ :: _, [], _, _, hb => nomatch hb

end


end Solidity
