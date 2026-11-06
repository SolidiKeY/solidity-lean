import Solidity.Optimizer.Loads
import Solidity.Semantics.Storage.Anon

/-!
# O03/X06 dead store elimination for storage and memory

`v = e₁; v = e₂;` becomes `v = e₂;` for a primitive state variable `v` when
`e₁` is simple (it cannot fail) and `e₂` is pure (`Val.isPure`: it reads no storage
and no memory, so it evaluates as it did before the first store); `m.f = s₁; m.f = s₂;` and
`m[k] = s₁; m[k] = s₂;` become the second store for a static memory location
(`Load.ofMLoc?`) when both values are simple. The rewrite is applied in every
sequence (blocks, `if` branches, loop bodies; `Prog.dstore`).

Why each side condition is needed, and why nothing observable is dropped:

* the first store's value must not fail: otherwise its halt is the program's;
* storage: a store at a state variable never fails (`write_root`), and the last of
  two stores wins (`SFields.set_set`), so the storage after both is the storage
  after the second; `e₂` pure reads only locals and the environment, which the
  first store leaves;
* memory: a store at a static location fails exactly when the location is
  unset or out of bounds, which does not depend on the value written
  (`writeAddr_none`), so the first store fails exactly when the second would,
  with the same halt; both values simple, so the second store's value cannot
  fail before its address does in the rewritten program;
  the heap after both is the heap after the second (`writeAddr_writeAddr`);
* memory size and gas: the typed semantics has no memory size or gas
  observation (the lowering IR has neither, `docs/feature-work/fullscope-vo1.md`);
  a store at an existing slot never grows the heap (`Out.ext` is the
  reflexive prefix in both programs, and the heap typing `H` is unchanged), so
  the removed store has no expansion effect to preserve: the result is
  equality of the whole typed run (`Prog.dstore_runC`).
-/
namespace Solidity.Optimizer.ConstFold
open Solidity

variable {C : Contract} {Γ : Ctx}

/-! ## Storage: the last store at a state variable wins -/

/-- A store at a state variable (`total = 1;`) always lands: the root is replaced. -/
theorem write_root {st : Storage C} {p : PrimTy} (n : Name) (h : C.rootType n = some (.prim p))
    (x : p.Denote) : st.write (SRef.ofRoot n h) (.prim x) = some (st.set h (.prim x)) := rfl

/-- **`v = s; v = e; Q` runs as `v = e; Q`** for a state variable `v`, `s` simple and `e` pure (`total = 1; total = a + 2;`). -/
theorem sstore_dead_runC {Δ : Ctx} {p : PrimTy} (n : Name) (h : C.rootType n = some (.prim p))
    (s : Simple C Γ p) (e : Val C Γ p) (he : Val.isPure e = true) (Q : Prog C Γ Δ) :
    Prog.runC (.cons (.assign (.root n h) (.val (.simple s)))
        (.cons (.assign (.root n h) (.val e)) Q)) =
      Prog.runC (.cons (.assign (.root n h) (.val e)) Q) := by
  funext σ
  simp only [Prog.runC, TRun.seq, Stmt.runC, TRun.assign, Src.valueT, Val.evalT, Loc.resolveT,
    ok_bind, write_root, TRes.ofOpt, pure, Except.pure]
  rw [Val.evalT_keep (σ := σ) (τ := σ.withStorage (SFields.set σ.storage h (SVal.prim (s.evalT σ)))) (fun _ _ => rfl) (fun _ => rfl) e he]
  cases e.evalT σ with
  | error => rfl
  | ok w =>
    simp only [ok_bind, write_root, State.withStorage, SFields.set_set]
    cases Q.runC _ <;> rfl

/-! ## Memory: the last write at an address wins -/

/-- The last of two object replacements at one identity wins. -/
theorem Objs.set_set {H : HTy} {R : RefTy} : (Rs : List RefTy) → (os : Objs H Rs) → (i : Nat) →
    (h : Rs[i]? = some R) → (o o' : MObj H R) →
      Objs.set Rs (Objs.set Rs os i h o) i h o' = Objs.set Rs os i h o'
  | [], _, _, _, _, _ => rfl
  | R' :: _, _, 0, h, _, _ => by
    obtain rfl : R' = R := Option.some.inj (by simpa only [List.getElem?_cons_zero] using h)
    rfl
  | _ :: Rs, os, i + 1, h, o, o' => congrArg (Prod.mk os.1) (Objs.set_set Rs os.2 i _ o o')

/-- The last of two object replacements at one reference wins. -/
theorem Heap.set_set {H : HTy} {R : RefTy} (hp : Heap H) (r : HRef H R) (o o' : MObj H R) :
    (hp.set r o).set r o' = hp.set r o' :=
  Objs.set_set H hp r.id r.get? o o'

/-- The last of two member writes wins (`m.f = 1; m.f = 2;`). -/
theorem MFields.set_set {H : HTy} {f : Name} : (fs : List (Name × Ty)) → {T : Ty} →
    (x : MFields H fs) → (h : Semantics.lookupBy f fs = some T) → (v w : MVal H T) →
      MFields.set fs (MFields.set fs x h v) h w = MFields.set fs x h w
  | [], _, _, _, _, _ => rfl
  | (f', T') :: fs, T, x, h, v, w => by
    by_cases e : f = f'
    · have hT := SFields.lookupBy_cons_pos e h
      subst hT
      simp only [MFields.set, e, dite_true]
    · simp only [MFields.set, e, dite_false, MFields.set_set fs x.2 _ v w]

/-- The last of two element writes wins (`xs[0] = 1; xs[0] = 2;`). -/
theorem MObj.setElem_setElem {H : HTy} {R : RefTy} {E : Ty} (a : ArrTy R E) (o : MObj H R)
    (i : Nat) (v w : MVal H E) :
    MObj.setElem a (MObj.setElem a o i v) i w = MObj.setElem a o i w := by
  cases a <;> simp only [MObj.setElem_dyn, MObj.setElem_fixed, List.set_set]

/-- **The last of two writes at one address wins**, given the first lands. -/
theorem Heap.writeAddr_writeAddr {H : HTy} {T : Ty} {hp hp₁ : Heap H} {ad : MAddr H T}
    {v : MVal H T} (h : hp.writeAddr ad v = some hp₁) (w : MVal H T) :
    hp₁.writeAddr ad w = hp.writeAddr ad w := by
  cases ad with
  | field r hf =>
    simp only [Heap.writeAddr, Option.some.injEq] at h
    subst h
    simp only [Heap.writeAddr, Heap.setField, Heap.get_set_same, Heap.set_set, MFields.set_set]
  | index r a i =>
    simp only [Heap.writeAddr, Heap.setIndex] at h
    split at h
    · next hb =>
      simp only [Option.some.injEq] at h
      subst h
      simp only [Heap.writeAddr, Heap.setIndex, Heap.get_set_same, MObj.elems_setElem,
        List.length_set, hb, if_true, Heap.set_set, MObj.setElem_setElem]
    · simp only [reduceCtorEq] at h

/-- A write that does not land (`xs[5] = v;` past the end) fails for every value. -/
theorem Heap.writeAddr_none {H : HTy} {T : Ty} {hp : Heap H} {ad : MAddr H T} {v : MVal H T}
    (h : hp.writeAddr ad v = none) (w : MVal H T) : hp.writeAddr ad w = none := by
  cases ad with
  | field r hf => simp only [Heap.writeAddr, reduceCtorEq] at h
  | index r a i =>
    simp only [Heap.writeAddr, Heap.setIndex] at h ⊢
    split at h
    · simp only [reduceCtorEq] at h
    · next hb => simp only [hb, if_false]

/-- **`m = s₁; m = s₂; Q` runs as `m = s₂; Q`** at a static memory location (`xs[0] = 1; xs[0] = 2;`). -/
theorem mstore_dead_runC {Δ : Ctx} {p : PrimTy} (m : MLoc C Γ (.prim p)) {l : Load C Γ p}
    (hl : Load.ofMLoc? m = some l) (s₁ s₂ : Simple C Γ p) (Q : Prog C Γ Δ) :
    Prog.runC (.cons (.assignMem m (.val (.simple s₁)))
        (.cons (.assignMem m (.val (.simple s₂))) Q)) =
      Prog.runC (.cons (.assignMem m (.val (.simple s₂))) Q) := by
  funext σ
  simp only [Prog.runC, TRun.seq, Stmt.runC, TRun.assignMem, MSrc.mvalT, Val.evalT, ok_bind]
  cases ha : m.addrT σ with
  | error e => rfl
  | ok a =>
    simp only [ok_bind]
    cases hw : σ.heap.writeAddr a (s₁.evalT σ) with
    | none =>
      simp only [TRes.ofOpt, Heap.writeAddr_none hw (s₂.evalT σ)]
      rfl
    | some hp₁ =>
      simp only [TRes.ofOpt, pure, Except.pure, ok_bind]
      rw [Simple.evalT_withHeap, Load.addrT_withHeap σ hp₁ (Load.ofMLoc?_mloc hl), ha]
      simp only [ok_bind]
      rw [show (σ.withHeap hp₁).heap = hp₁ from rfl, Heap.writeAddr_writeAddr hw]
      cases σ.heap.writeAddr a (s₂.evalT σ) with
      | none => rfl
      | some hp₂ =>
        simp only [ok_bind]
        show Except.map _ (Except.map _ (Q.runC (σ.withHeap hp₂))) = _
        cases Q.runC (σ.withHeap hp₂) <;> rfl

/-! ## The pass -/

/-- A store of a value at a state variable: its type, root and value. -/
def rootStore? {T : Ty} (l : Loc C Γ T) : Src C Γ T → Option ((p : PrimTy) × Name × Val C Γ p)
  | .val v =>
    match l with
    | .root n _ => some ⟨_, n, v⟩
    | .field .. | .index .. => none
  | .copy .. | .fixedCopy .. | .copyMem .. | .fixedCopyMem .. => none

/-- The state-variable store a sequence starts with. -/
def headSStore? {Δ : Ctx} : Prog C Γ Δ → Option ((p : PrimTy) × Name × Val C Γ p)
  | .nil => none
  | .cons s _ =>
    match s with
    | .assign l r => rootStore? l r
    | .rebind .. | .assignLocal .. | .declLocal .. | .declStorage .. | .opAssign .. | .incDec .. | .assignIncDec .. | .assignLocalPush .. | .push .. | .pop .. | .transfer .. | .send .. | .declMem .. | .rebindMem .. | .assignFromMem .. | .assignMem .. | .delete .. | .deleteMem .. | .assignNew .. | .ite .. | .require .. | .assert .. | .revert | .assumeFalse | .call .. | .tryCall .. | .loop .. | .block .. | .pushOpAssign .. | .pushIncDec .. | .callReceiver .. | .callReceiverPush .. | .callRec .. | .revertData .. | .catchData .. => none

theorem headSStore?_eq {Δ : Ctx} {P : Prog C Γ Δ} {q : PrimTy} {n : Name} {e : Val C Γ q}
    (h : headSStore? P = some ⟨q, n, e⟩) :
    ∃ (h' : C.rootType n = some (.prim q)) (Q : Prog C Γ Δ),
      P = .cons (.assign (.root n h') (.val e)) Q := by
  cases P with
  | nil => simp only [headSStore?, reduceCtorEq] at h
  | cons s Q =>
    cases s with
    | assign l r =>
      cases r with
      | val v =>
        cases l with
        | root n' h' =>
          simp only [headSStore?, rootStore?, Option.some.injEq, Sigma.mk.injEq] at h
          obtain ⟨rfl, h2⟩ := h
          simp only [heq_eq_eq, Prod.mk.injEq] at h2
          obtain ⟨rfl, rfl⟩ := h2
          exact ⟨h', Q, rfl⟩
        | field | index => simp only [headSStore?, rootStore?, reduceCtorEq] at h
      | copy | fixedCopy | copyMem | fixedCopyMem =>
        simp only [headSStore?, rootStore?, reduceCtorEq] at h
    | rebind | assignLocal | declLocal | declStorage | opAssign | incDec | assignIncDec | assignLocalPush | push | pop | transfer | send | declMem | rebindMem | assignFromMem | assignMem | delete | deleteMem | assignNew | ite | require | assert | revert | assumeFalse | call | tryCall | loop | block | pushOpAssign | pushIncDec | callReceiver | callReceiverPush | callRec | revertData | catchData => simp only [headSStore?, reduceCtorEq] at h

/-- The first store is dead: `n = s; n = e; …` with `s` simple and `e` pure. -/
def sDeadB {T : Ty} (l : Loc C Γ T) (r : Src C Γ T) {Δ : Ctx} (P : Prog C Γ Δ) : Bool :=
  match rootStore? l r, headSStore? P with
  | some ⟨_, n, v⟩, some ⟨_, n', e⟩ => v.isSimple && n == n' && Val.isPure e
  | _, _ => false

/-- Two static memory locations that are the same. -/
def mSameB {p q : PrimTy} (m : MLoc C Γ (.prim p)) (m' : MLoc C Γ (.prim q)) : Bool :=
  match Load.ofMLoc? m, Load.ofMLoc? m' with
  | some l, some l' => if h : q = p then Load.beq l (h ▸ l') else false
  | _, _ => false

theorem mSameB_eq {p q : PrimTy} {m : MLoc C Γ (.prim p)} {m' : MLoc C Γ (.prim q)}
    (h : mSameB m m' = true) : ∃ e : q = p, (e ▸ m') = m ∧ ∃ l, Load.ofMLoc? m = some l := by
  unfold mSameB at h
  split at h
  · next l l' hl hl' =>
    split at h
    · next e =>
      subst e
      have hll := Load.eq_of_beq _ _ h
      subst hll
      refine ⟨rfl, ?_, l, hl⟩
      have h1 := Load.ofMLoc?_eq hl
      have h2 := Load.ofMLoc?_eq hl'
      rw [h1] at h2
      exact (Val.readMem.inj h2).symm
    · simp only [Bool.false_eq_true] at h
  · simp only [Bool.false_eq_true] at h

/-- A memory store of a simple value: its type, location and value. -/
def simpleMStore? {T : Ty} (m : MLoc C Γ T) : MSrc C Γ T →
    Option ((p : PrimTy) × MLoc C Γ (.prim p) × Simple C Γ p)
  | .val v => (simple? v).map fun s => ⟨_, m, s⟩
  | .ref _ => none

/-- The memory store a sequence starts with. -/
def headMStore? {Δ : Ctx} : Prog C Γ Δ →
    Option ((p : PrimTy) × MLoc C Γ (.prim p) × Simple C Γ p)
  | .nil => none
  | .cons s _ =>
    match s with
    | .assignMem m r => simpleMStore? m r
    | .assign .. | .rebind .. | .assignLocal .. | .declLocal .. | .declStorage .. | .opAssign .. | .incDec .. | .assignIncDec .. | .assignLocalPush .. | .push .. | .pop .. | .transfer .. | .send .. | .declMem .. | .rebindMem .. | .assignFromMem .. | .delete .. | .deleteMem .. | .assignNew .. | .ite .. | .require .. | .assert .. | .revert | .assumeFalse | .call .. | .tryCall .. | .loop .. | .block .. | .pushOpAssign .. | .pushIncDec .. | .callReceiver .. | .callReceiverPush .. | .callRec .. | .revertData .. | .catchData .. => none

theorem simpleMStore?_eq {T : Ty} {m : MLoc C Γ T} {r : MSrc C Γ T} {q : PrimTy}
    {m' : MLoc C Γ (.prim q)} {s : Simple C Γ q} (h : simpleMStore? m r = some ⟨q, m', s⟩) :
    ∃ _ : T = .prim q, HEq m m' ∧ HEq r (MSrc.val (C := C) (Γ := Γ) (.simple s)) := by
  cases r with
  | val v =>
    simp only [simpleMStore?, Option.map_eq_some_iff] at h
    obtain ⟨t, ht, h2⟩ := h
    simp only [Sigma.mk.injEq] at h2
    obtain ⟨rfl, h2⟩ := h2
    simp only [heq_eq_eq, Prod.mk.injEq] at h2
    obtain ⟨rfl, rfl⟩ := h2
    rw [simple?_eq ht]
    exact ⟨rfl, HEq.rfl, HEq.rfl⟩
  | ref => simp only [simpleMStore?, reduceCtorEq] at h

theorem headMStore?_eq {Δ : Ctx} {P : Prog C Γ Δ} {q : PrimTy} {m : MLoc C Γ (.prim q)}
    {s : Simple C Γ q} (h : headMStore? P = some ⟨q, m, s⟩) :
    ∃ Q : Prog C Γ Δ, P = .cons (.assignMem m (.val (.simple s))) Q := by
  cases P with
  | nil => simp only [headMStore?, reduceCtorEq] at h
  | cons s' Q =>
    cases s' with
    | assignMem m' r =>
      simp only [headMStore?] at h
      obtain ⟨rfl, hm, hr⟩ := simpleMStore?_eq h
      cases hm
      cases hr
      exact ⟨Q, rfl⟩
    | assign | rebind | assignLocal | declLocal | declStorage | opAssign | incDec | assignIncDec | assignLocalPush | push | pop | transfer | send | declMem | rebindMem | assignFromMem | delete | deleteMem | assignNew | ite | require | assert | revert | assumeFalse | call | tryCall | loop | block | pushOpAssign | pushIncDec | callReceiver | callReceiverPush | callRec | revertData | catchData => simp only [headMStore?, reduceCtorEq] at h

/-- The first memory store is dead: `m = s₁; m = s₂; …` at one static location. -/
def mDeadB {T : Ty} (m : MLoc C Γ T) (r : MSrc C Γ T) {Δ : Ctx} (P : Prog C Γ Δ) : Bool :=
  match simpleMStore? m r, headMStore? P with
  | some ⟨_, m₁, _⟩, some ⟨_, m₂, _⟩ => mSameB m₁ m₂
  | _, _ => false

/-- A store before a sequence: dropped when the sequence starts with a store
that overwrites it. -/
def dstoreCons : {Γ Γ₁ Δ : Ctx} → Stmt C Γ Γ₁ → Prog C Γ₁ Δ → Prog C Γ Δ
  | _, _, _, .assign l r, P => if sDeadB l r P then P else .cons (.assign l r) P
  | _, _, _, .assignMem m r, P => if mDeadB m r P then P else .cons (.assignMem m r) P
  | _, _, _, s@(.rebind ..), P => .cons s P
  | _, _, _, s@(.assignLocal ..), P => .cons s P
  | _, _, _, s@(.declLocal ..), P => .cons s P
  | _, _, _, s@(.declStorage ..), P => .cons s P
  | _, _, _, s@(.opAssign ..), P => .cons s P
  | _, _, _, s@(.incDec ..), P => .cons s P
  | _, _, _, s@(.assignIncDec ..), P => .cons s P
  | _, _, _, s@(.assignLocalPush ..), P => .cons s P
  | _, _, _, s@(.push ..), P => .cons s P
  | _, _, _, s@(.pop ..), P => .cons s P
  | _, _, _, s@(.transfer ..), P => .cons s P
  | _, _, _, s@(.send ..), P => .cons s P
  | _, _, _, s@(.declMem ..), P => .cons s P
  | _, _, _, s@(.rebindMem ..), P => .cons s P
  | _, _, _, s@(.assignFromMem ..), P => .cons s P
  | _, _, _, s@(.delete ..), P => .cons s P
  | _, _, _, s@(.deleteMem ..), P => .cons s P
  | _, _, _, s@(.assignNew ..), P => .cons s P
  | _, _, _, s@(.ite ..), P => .cons s P
  | _, _, _, s@(.require ..), P => .cons s P
  | _, _, _, s@(.assert ..), P => .cons s P
  | _, _, _, s@(.revert), P => .cons s P
  | _, _, _, s@(.assumeFalse), P => .cons s P
  | _, _, _, s@(.call ..), P => .cons s P
  | _, _, _, s@(.tryCall ..), P => .cons s P
  | _, _, _, s@(.loop ..), P => .cons s P
  | _, _, _, s@(.block ..), P => .cons s P
  | _, _, _, s@(.pushOpAssign ..), P => .cons s P
  | _, _, _, s@(.pushIncDec ..), P => .cons s P
  | _, _, _, s@(.callReceiver ..), P => .cons s P
  | _, _, _, s@(.callReceiverPush ..), P => .cons s P
  | _, _, _, s@(.callRec ..), P => .cons s P
  | _, _, _, s@(.revertData ..), P => .cons s P
  | _, _, _, s@(.catchData ..), P => .cons s P

/-- A store dropped before the store that overwrites it runs as before. -/
theorem dstoreCons_runC : {Γ Γ₁ Δ : Ctx} → (s : Stmt C Γ Γ₁) → (P : Prog C Γ₁ Δ) →
    Prog.runC (dstoreCons s P) = Prog.runC (.cons s P)
  | _, _, _, .assign l r, P => by
    simp only [dstoreCons]
    split
    · next hd =>
      unfold sDeadB at hd
      split at hd
      · next _ _ p n v q n' e h1 h2 =>
        simp only [Bool.and_eq_true, beq_iff_eq] at hd
        obtain ⟨⟨hs, rfl⟩, he⟩ := hd
        obtain ⟨h', Q, rfl⟩ := headSStore?_eq h2
        cases r with
        | val v' =>
          cases l with
          | root n'' h =>
            simp only [rootStore?, Option.some.injEq, Sigma.mk.injEq] at h1
            obtain ⟨rfl, h1⟩ := h1
            simp only [heq_eq_eq, Prod.mk.injEq] at h1
            obtain ⟨rfl, rfl⟩ := h1
            obtain rfl := Ty.prim.inj (Option.some.inj (h.symm.trans h'))
            cases v' with
            | simple s₁ => exact (sstore_dead_runC _ h s₁ e he Q).symm
            | read | binop | unop | ternary | readMem | len | mlen | modular | hash =>
              simp only [Val.isSimple, Bool.false_eq_true] at hs
          | field | index => simp only [rootStore?, reduceCtorEq] at h1
        | copy | fixedCopy | copyMem | fixedCopyMem => simp only [rootStore?, reduceCtorEq] at h1
      · simp only [Bool.false_eq_true] at hd
    · rfl
  | _, _, _, .assignMem m r, P => by
    simp only [dstoreCons]
    split
    · next hd =>
      unfold mDeadB at hd
      split at hd
      · next _ _ p m₁ s₁ q m₂ s₂ h1 h2 =>
        obtain ⟨Q, rfl⟩ := headMStore?_eq h2
        obtain ⟨rfl, hm, hr⟩ := simpleMStore?_eq h1
        cases hm
        cases hr
        obtain ⟨e, hme, l, hl⟩ := mSameB_eq hd
        subst e
        subst hme
        exact (mstore_dead_runC _ hl s₁ s₂ Q).symm
      · simp only [Bool.false_eq_true] at hd
    · rfl
  | _, _, _, .rebind .., _
  | _, _, _, .assignLocal .., _
  | _, _, _, .declLocal .., _
  | _, _, _, .declStorage .., _
  | _, _, _, .opAssign .., _
  | _, _, _, .incDec .., _
  | _, _, _, .assignIncDec .., _
  | _, _, _, .assignLocalPush .., _
  | _, _, _, .push .., _
  | _, _, _, .pop .., _
  | _, _, _, .transfer .., _
  | _, _, _, .send .., _
  | _, _, _, .declMem .., _
  | _, _, _, .rebindMem .., _
  | _, _, _, .assignFromMem .., _
  | _, _, _, .delete .., _
  | _, _, _, .deleteMem .., _
  | _, _, _, .assignNew .., _
  | _, _, _, .ite .., _
  | _, _, _, .require .., _
  | _, _, _, .assert .., _
  | _, _, _, .revert, _
  | _, _, _, .assumeFalse, _
  | _, _, _, .call .., _
  | _, _, _, .tryCall .., _
  | _, _, _, .loop .., _
  | _, _, _, .block .., _
  | _, _, _, .pushOpAssign .., _
  | _, _, _, .pushIncDec .., _
  | _, _, _, .callReceiver .., _
  | _, _, _, .callReceiverPush .., _
  | _, _, _, .callRec .., _
  | _, _, _, .revertData .., _
  | _, _, _, .catchData .., _ => rfl

mutual
/-- Dead storage and memory stores removed in every sequence of a statement. -/
def Stmt.dstore : {Γ Γ' : Ctx} → Stmt C Γ Γ' → Stmt C Γ Γ'
  | _, _, .ite c thn els => .ite c (Prog.dstore thn) (Prog.dstore els)
  | _, _, .block body => .block (Prog.dstore body)
  | _, _, .loop a c body => .loop a c (Prog.dstore body)
  | _, _, s@(.assign ..) => s
  | _, _, s@(.rebind ..) => s
  | _, _, s@(.assignLocal ..) => s
  | _, _, s@(.declLocal ..) => s
  | _, _, s@(.declStorage ..) => s
  | _, _, s@(.opAssign ..) => s
  | _, _, s@(.incDec ..) => s
  | _, _, s@(.assignIncDec ..) => s
  | _, _, s@(.assignLocalPush ..) => s
  | _, _, s@(.push ..) => s
  | _, _, s@(.pop ..) => s
  | _, _, s@(.transfer ..) => s
  | _, _, s@(.send ..) => s
  | _, _, s@(.declMem ..) => s
  | _, _, s@(.rebindMem ..) => s
  | _, _, s@(.assignFromMem ..) => s
  | _, _, s@(.assignMem ..) => s
  | _, _, s@(.delete ..) => s
  | _, _, s@(.deleteMem ..) => s
  | _, _, s@(.assignNew ..) => s
  | _, _, s@(.require ..) => s
  | _, _, s@(.assert ..) => s
  | _, _, s@(.revert) => s
  | _, _, s@(.assumeFalse) => s
  | _, _, s@(.call ..) => s
  | _, _, s@(.tryCall ..) => s
  | _, _, s@(.pushOpAssign ..) => s
  | _, _, s@(.pushIncDec ..) => s
  | _, _, s@(.callReceiver ..) => s
  | _, _, s@(.callReceiverPush ..) => s
  | _, _, s@(.callRec ..) => s
  | _, _, s@(.revertData ..) => s
  | _, _, s@(.catchData ..) => s

/-- Dead storage and memory stores removed in a sequence. -/
def Prog.dstore : {Γ Γ' : Ctx} → Prog C Γ Γ' → Prog C Γ Γ'
  | _, _, .nil => .nil
  | _, _, .cons s P => dstoreCons (Stmt.dstore s) (Prog.dstore P)
end

mutual
theorem Stmt.dstore_runC : {Γ Γ' : Ctx} → (s : Stmt C Γ Γ') →
    Stmt.runC (Stmt.dstore s) = Stmt.runC s
  | _, _, .ite c thn els => by
    simp only [Stmt.dstore, Stmt.runC]
    rw [Prog.dstore_runC thn, Prog.dstore_runC els]
    exact TRun.ite_congr (fun _ => rfl) _ _ _ _ _ _
  | _, _, .block body => by
    simp only [Stmt.dstore, Stmt.runC]
    rw [Prog.dstore_runC body]
    exact TRun.block_congr _ _ _
  | _, _, .loop a c body => by
    simp only [Stmt.dstore, Stmt.runC]
    rw [Prog.dstore_runC body]
    exact TRun.loop_congr (fun _ => rfl) _ _ _
  | _, _, .assign ..
  | _, _, .rebind ..
  | _, _, .assignLocal ..
  | _, _, .declLocal ..
  | _, _, .declStorage ..
  | _, _, .opAssign ..
  | _, _, .incDec ..
  | _, _, .assignIncDec ..
  | _, _, .assignLocalPush ..
  | _, _, .push ..
  | _, _, .pop ..
  | _, _, .transfer ..
  | _, _, .send ..
  | _, _, .declMem ..
  | _, _, .rebindMem ..
  | _, _, .assignFromMem ..
  | _, _, .assignMem ..
  | _, _, .delete ..
  | _, _, .deleteMem ..
  | _, _, .assignNew ..
  | _, _, .require ..
  | _, _, .assert ..
  | _, _, .revert
  | _, _, .assumeFalse
  | _, _, .call ..
  | _, _, .tryCall ..
  | _, _, .pushOpAssign ..
  | _, _, .pushIncDec ..
  | _, _, .callReceiver ..
  | _, _, .callReceiverPush ..
  | _, _, .callRec ..
  | _, _, .revertData ..
  | _, _, .catchData .. => rfl

theorem Prog.dstore_runC : {Γ Γ' : Ctx} → (P : Prog C Γ Γ') →
    Prog.runC (Prog.dstore P) = Prog.runC P
  | _, _, .nil => rfl
  | _, _, .cons s P => by
    simp only [Prog.dstore]
    rw [dstoreCons_runC]
    simp only [Prog.runC]
    rw [Stmt.dstore_runC s, Prog.dstore_runC P]
end

/-- Dead store elimination as an O01 pass preserving `SameRun`. -/
theorem dstore_preserves (Γ Γ' : Ctx) :
    Preserves (SameRun (C := C) (Γ := Γ) (Γ' := Γ')) (Prog.dstore : Lowering.Pass C Γ Γ') :=
  fun P => (Prog.dstore_runC P).symm

end Solidity.Optimizer.ConstFold
