import Solidity.Typing.State
import Solidity.Semantics.Erased

/-!
# Type soundness on the erasure: the evaluators are typed

The typed syntax rules out every *static* mismatch: a member exists, an
operator takes its operand, a copy holds no mapping, a pushed default is
well-formed, and, since the scoped syntax (`Syntax/Scoped.lean`), a local is a
position in a context `Γ`, read and written at the type `Γ` gives it.  The
typed run (`Semantics/Run.lean`) rules out the dynamic ones: its
states hold values of their types, so their erasure is well-typed by
construction (`State.erase_wt`, `Typing/TypedWT.lean`).

`RunWT C H σ` is that invariant on an erased state: the global part
`StateWT` (`Typing/State.lean`: storage inhabits `C`'s layout, the heap the
store typing `H`, the allocation counter is fresh) and every local of its
type (`LTy.WT`: a number in a `uint` local, a path the layout types at an
alias's type, an identity `H` claims at a memory local's type).  What is
proved here is what the closer and the other invariants read of it: the
erasure's evaluators (`Semantics/Erased.lean`) find values of their types —
the paths resolve to a place the layout types at the path's type
(`Loc.resolve_wt`), the memory reads find a slot of the path's type
(`MLoc.read_wt`), a value evaluates to one of its type (`Val.eval_wt`) —
and each statement's write on the global part stores what the place holds.
`RunInv` is the shape of an invariant with a part on the global state and
one on each local, which `Typing/TypedRunInv.lean` carries along the typed
run and `Reachability.lean` and `Constructibility.lean` instantiate.
-/

namespace Solidity

open Semantics
open SemanticsProperties (lookupBy_setBy_self lookupBy_setBy_ne HeapWellFormed
  lookupBy_eq_some_mem)

variable {C : Contract}

/-! ## The layout a contract declares -/

/-- The storage layout of `C`: its roots at their declared types.  A root's
type is `C.rootType`, and one step down is `segTy`, which reads the same
`structDef` as `C.fieldType`. -/
def Contract.layout (C : Contract) : Layout := ⟨C.vars⟩

/-- `alice` in `StandardExample` has type `Person` in the layout, as
declared. -/
theorem Contract.layout_tyAt_root {C : Contract} {r : Name} {T : Ty}
    (h : C.rootType r = some T) : C.layout.tyAt r [] = some T := by
  simp only [Layout.tyAt, Contract.layout]
  rw [show lookupBy r C.vars = some T from h]
  rfl

/-! ## Value and heap lemmas -/

section Lemmas

variable {H : HeapTy}

/-- A reference slot typed at a reference type is the store typing's claim. -/
theorem Semantics.MVal.hasTyH_ref {id : Nat} {R : RefTy} :
    MVal.hasTyH H (.ref id) (.ref R) = true ↔ lookupBy id H = some (.ref R) := by
  simp [MVal.hasTyH]

/-- The object at a claimed identity exists and has the claimed type. -/
theorem heapTypedB_obj {heap : List (Nat × MObj)} {id : Nat} {ty : Ty}
    (hheap : heapTypedB H heap = true) (h : lookupBy id H = some ty) :
    ∃ obj, lookupBy id heap = some obj ∧ obj.hasTyH H ty = true := by
  have := List.all_eq_true.mp hheap _ (lookupBy_eq_some_mem h)
  revert this
  cases hl : lookupBy id heap with
  | none => intro h; exact absurd h (by simp)
  | some obj => intro h; exact ⟨obj, rfl, h⟩

/-- A member of a typed memory struct has its declared type: `m.age` a `uint`. -/
theorem mHasTyHFields_lookup {str : Name} {fields : List (Name × MVal)} {n : Name} {v : MVal}
    (hwt : MObj.hasTyH.hasTyHFields H str fields = true)
    (hlook : lookupBy n fields = some v) :
    ∃ ty, lookupBy n (structDef str) = some ty ∧ MVal.hasTyH H v ty = true := by
  induction fields with
  | nil => simp [lookupBy] at hlook
  | cons p rest ih =>
      obtain ⟨n', v'⟩ := p
      simp only [MObj.hasTyH.hasTyHFields, Bool.and_eq_true] at hwt
      by_cases hn : n = n'
      · subst hn
        simp [lookupBy] at hlook
        subst hlook
        cases hdef : lookupBy n (structDef str) with
        | none => rw [hdef] at hwt; exact Bool.noConfusion hwt.1
        | some ty =>
            rw [hdef] at hwt
            exact ⟨ty, rfl, hwt.1⟩
      · simp [lookupBy, hn] at hlook
        exact ih hwt.2 hlook

/-- An element of a typed memory array has the element type: `ns[i]` a `uint`. -/
theorem mHasTyHElems_mem {elem : Ty} {elems : List MVal} {v : MVal}
    (hwt : MObj.hasTyH.hasTyHElems H elem elems = true) (hmem : v ∈ elems) :
    MVal.hasTyH H v elem = true := by
  induction elems with
  | nil => cases hmem
  | cons w rest ih =>
      simp only [MObj.hasTyH.hasTyHElems, Bool.and_eq_true] at hwt
      cases hmem with
      | head => exact hwt.1
      | tail _ hmem => exact ih hwt.2 hmem

/-- `m.age = 3;` keeps `m`'s object a `Person`. -/
theorem mHasTyHFields_setBy {str : Name} {fields : List (Name × MVal)} {n : Name} {w : MVal}
    {tyf : Ty} (hwt : MObj.hasTyH.hasTyHFields H str fields = true)
    (hdef : lookupBy n (structDef str) = some tyf) (hw : MVal.hasTyH H w tyf = true) :
    MObj.hasTyH.hasTyHFields H str (setBy n w fields) = true := by
  induction fields with
  | nil => simp [setBy, MObj.hasTyH.hasTyHFields, hdef, hw]
  | cons p rest ih =>
      obtain ⟨k, v⟩ := p
      simp only [MObj.hasTyH.hasTyHFields, Bool.and_eq_true] at hwt
      by_cases hn : n = k
      · subst hn
        simp [setBy, MObj.hasTyH.hasTyHFields, hdef, hw, hwt.2]
      · simp [setBy, hn, MObj.hasTyH.hasTyHFields, hwt.1, ih hwt.2]

/-- The element type of an array type of either kind: `uint` of `uint[]` and
of `uint[3]`. -/
def RefTy.arrElem? : RefTy → Option Ty
  | .array E | .fixed E _ => some E
  | _ => none

theorem ArrTy.arrElem {R : RefTy} {E : Ty} : ArrTy R E → R.arrElem? = some E
  | .dyn | .fixed => rfl

/-- An object typed at an array type is an array of the element type. -/
theorem Semantics.MObj.hasTyH_arrElem {R : RefTy} {E : Ty} {obj : MObj} (hR : R.arrElem? = some E)
    (h : MObj.hasTyH H obj (.ref R) = true) :
    ∃ elems fx, obj = .array elems fx ∧ MObj.hasTyH.hasTyHElems H E elems = true := by
  cases R <;> simp only [RefTy.arrElem?, Option.some.injEq, reduceCtorEq] at hR <;> subst hR <;>
    cases obj <;> simp_all [MObj.hasTyH]

/-- `ns[i] = 3;` keeps `ns`'s object a `uint[]`. -/
theorem mHasTyHElems_set {elem : Ty} {elems : List MVal} {i : Nat} {w : MVal}
    (hwt : MObj.hasTyH.hasTyHElems H elem elems = true) (hw : MVal.hasTyH H w elem = true) :
    MObj.hasTyH.hasTyHElems H elem (elems.set i w) = true := by
  induction elems generalizing i with
  | nil => exact hwt
  | cons v rest ih =>
      simp only [MObj.hasTyH.hasTyHElems, Bool.and_eq_true] at hwt
      cases i with
      | zero =>
          simp only [List.set, MObj.hasTyH.hasTyHElems, Bool.and_eq_true]
          exact ⟨hw, hwt.2⟩
      | succ n =>
          simp only [List.set, MObj.hasTyH.hasTyHElems, Bool.and_eq_true]
          exact ⟨hwt.1, ih hwt.2⟩

/-- Writing a typed object over a claimed identity keeps the heap typed. -/
theorem heapTypedB_setObj {heap : List (Nat × MObj)} {id : Nat} {ty : Ty} {obj : MObj}
    (hnd : nodupKeysB H = true) (hheap : heapTypedB H heap = true)
    (hclaim : lookupBy id H = some ty) (hobj : obj.hasTyH H ty = true) :
    heapTypedB H (setBy id obj heap) = true := by
  refine List.all_eq_true.mpr fun r hr => ?_
  show (match lookupBy r.1 (setBy id obj heap) with
    | some o => o.hasTyH H r.2
    | none => false) = true
  by_cases hid : r.1 = id
  · have : r.2 = ty := by
      have hl := lookupBy_eq_of_nodup hnd hr
      rw [hid, hclaim] at hl
      exact (Option.some.inj hl).symm
    rw [hid, lookupBy_setBy_self, this]
    exact hobj
  · rw [lookupBy_setBy_ne hid]
    exact List.all_eq_true.mp hheap _ hr

/-- `setObj` on a present identity keeps the allocation counter fresh. -/
theorem HeapWellFormed.setObj' {s : State} {id : Nat} {obj : MObj}
    (hwf : HeapWellFormed s) (hpresent : lookupBy id s.heap ≠ none) :
    HeapWellFormed (s.setObj id obj) := by
  intro i hi
  show lookupBy i (setBy id obj s.heap) = none
  have hne : i ≠ id := by
    intro he
    subst he
    exact hpresent (hwf i hi)
  rw [lookupBy_setBy_ne hne]
  exact hwf i hi

/-- A primitive slot read out is a stack value of the slot's type. -/
theorem Semantics.MVal.asValue_hasTy {mv : MVal} {ty : Ty} {v : Value}
    (h : MVal.hasTyH H mv ty = true) (hval : mv.asValue = .ok v) :
    (Value.toSVal v).hasTy ty = true := by
  cases mv with
  | prim p =>
      cases p <;> simp only [MVal.asValue] at hval <;> cases hval <;>
        cases ty with
        | prim pt => cases pt <;> simp_all [MVal.hasTyH, Value.toSVal, SVal.hasTy]
        | ref r => simp [MVal.hasTyH] at h
  | ref id => exact nomatch hval

/-- A typed stack value stored in memory is a typed slot. -/
theorem Semantics.Value.toMVal_hasTyH {v : Value} {ty : Ty}
    (h : (Value.toSVal v).hasTy ty = true) : MVal.hasTyH H v.toMVal ty = true := by
  cases v <;> cases ty with
  | prim pt => cases pt <;> simp_all [Value.toSVal, SVal.hasTy, Value.toMVal, MVal.hasTyH]
  | ref r => simp [Value.toSVal, SVal.hasTy] at h

/-- A stored primitive read out is a stack value of its type. -/
theorem Semantics.SVal.asValue_hasTy {sv : SVal} {ty : Ty} {v : Value}
    (h : sv.hasTy ty = true) (hval : sv.asValue = .ok v) : (Value.toSVal v).hasTy ty = true := by
  rw [SVal.asValue_toSVal hval]; exact h

/-- A slot read as an object is a reference: `m` in `m.age`. -/
theorem Semantics.MVal.asRef_ok {mv : MVal} {id : Nat} (h : mv.asRef = .ok id) : mv = .ref id := by
  cases mv with
  | ref i => cases h; rfl
  | prim _ => exact nomatch h

/-- An integer is a value of every numeric type. -/
theorem int_toSVal_hasTy {p : PrimTy} (hp : p.isNumeric = true) (n : Int) :
    (Value.toSVal (.int n)).hasTy (.prim p) = true := by
  cases p <;> simp_all [PrimTy.isNumeric, Value.toSVal, SVal.hasTy]

/-- Comparisons and connectives produce booleans. -/
theorem applyBinOp_nonarith_bool {op : BinOp} {l r v : Value}
    (hop : op.isArith = false) (h : applyBinOp op l r = .ok v) : ∃ b, v = .bool b := by
  cases op <;> simp only [BinOp.isArith] at hop <;> try exact Bool.noConfusion hop
  all_goals simp only [applyBinOp, bind, Except.bind] at h
  all_goals repeat' split at h
  all_goals first
    | exact ⟨_, (Except.ok.inj h).symm⟩
    | exact nomatch h

end Lemmas

/-! ## Operators -/

/-- `a ⊕ b` evaluates to a value of the type `⊕` returns: `a + b` at `uint`
is a number, `a < b` a boolean, whatever the operands held. -/
theorem evalBinop_wt {op : BinOp} {p q : PrimTy} {lv : Value} {rb : Res Value} {w : Value}
    (hacc : op.accepts p = true) (hq : op.ret p = q) (h : evalBinop op p lv rb = .ok w) :
    (Value.toSVal w).hasTy (.prim q) = true := by
  subst hq
  unfold evalBinop at h
  split at h
  · cases h; rfl
  · cases h; rfl
  · obtain ⟨rv, _, h⟩ := bind_ok_inv h
    obtain ⟨v', hv', h⟩ := bind_ok_inv h
    have hw := checkArith_ok_eq h
    subst hw
    cases hA : op.isArith
    · obtain ⟨b, rfl⟩ := applyBinOp_nonarith_bool hA hv'
      simp [BinOp.ret, hA, Value.toSVal, SVal.hasTy]
    · obtain ⟨n, rfl⟩ := applyBinOp_arith_int hA hv'
      have hnum : p.isNumeric = true := by
        cases op <;> simp_all [BinOp.isArith, BinOp.accepts, PrimTy.isNumeric]
      simp only [BinOp.ret, hA, if_true]
      exact int_toSVal_hasTy hnum n

/-- `-a`, `!a` and `~a` evaluate to a value of the type they return. -/
theorem evalUnop_wt {op : UnOp} {p q : PrimTy} {v w : Value}
    (hacc : op.accepts p = true) (hq : op.ret p = q)
    (h : (do unopCheck op p (← applyUnOp op v)) = (.ok w : Res Value)) :
    (Value.toSVal w).hasTy (.prim q) = true := by
  subst hq
  obtain ⟨u, hu, h⟩ := bind_ok_inv h
  have hw : w = u := by
    unfold unopCheck at h
    split at h
    · exact checkArith_ok_eq h
    · cases h; rfl
  subst hw
  cases op with
  | neg =>
    simp only [applyUnOp, bind, Except.bind] at hu
    split at hu
    · exact nomatch hu
    · cases hu
      obtain rfl : p = .int := by simpa only [UnOp.accepts, beq_iff_eq] using hacc
      exact int_toSVal_hasTy rfl _
  | not =>
    simp only [applyUnOp, bind, Except.bind] at hu
    split at hu
    · exact nomatch hu
    · cases hu; rfl
  | bnot =>
    simp only [applyUnOp, bind, Except.bind] at hu
    split at hu
    · exact nomatch hu
    · cases hu; exact int_toSVal_hasTy (by simp_all [UnOp.accepts, UnOp.ret, PrimTy.isNumeric]) _

/-! ## Well-formed defaults

The syntax carries `defaultOkS`, which the kernel evaluates; the typing
lemmas want `defaultOk`, which it cannot (it recurses through `structDef`
by well-founded recursion).  They agree on every struct `defaultOkS`
admits, checked here once per struct. -/

theorem defaultOk_struct_of_mem {s : Name} (h : s ∈ defaultOkStructs) :
    defaultOk (.ref (.struct s)) = true := by
  simp only [defaultOkStructs, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [defaultOk, defaultOkFields, structDef, lookupBy]

/-- `Person memory m;` and `persons.push();` build a default of the type
they name: `defaultOkS` is enough for `defaultForTy_hasTy`. -/
theorem defaultOk_of_defaultOkS : ∀ {T : Ty}, T.defaultOkS = true → defaultOk T = true
  | .prim _, _ => by simp [defaultOk]
  | .ref (.struct _), h => defaultOk_struct_of_mem (by simpa [Ty.defaultOkS] using h)
  | .ref (.array _), _ => by simp [defaultOk]
  | .ref (.fixed _ _), h => by
    rw [defaultOk]; exact defaultOk_of_defaultOkS (by simpa [Ty.defaultOkS] using h)
  | .ref (.mapping _ _), h => by
    rw [defaultOk]; exact defaultOk_of_defaultOkS (by simpa [Ty.defaultOkS] using h)


/-! ## The global invariant under the state operations -/

namespace Semantics.StateWT

variable {H : HeapTy} {σ σ' : State}

/-- A storage write of a value of the place's type: `alice.age = 10;`
writes a number where the layout says `uint`. -/
theorem save (hwt : StateWT H C.layout σ) {r : Name} {segs : List Seg} {T : Ty} {new : SVal}
    (hty : C.layout.tyAt r segs = some T) (hnew : new.hasTy T = true)
    (h : σ.saveStorage r segs new = .ok σ') : StateWT H C.layout σ' := by
  obtain ⟨hheap, hnext, _, _⟩ := SemanticsProperties.State.saveStorage_frame h
  refine ⟨hwt.layoutNodup, hwt.heapTyNodup,
    State.saveStorage_wellTyped hwt.layoutNodup hwt.storage hty hnew h, ?_, ?_⟩
  · rw [hheap]; exact hwt.heap
  · intro i hi; rw [hheap]; exact hwt.heapWf i (hnext ▸ hi)

/-- A storage write of what an assignment's right-hand side denotes, of the
place's type: a word saved, or a copy over what is there (`SVal.overlay`),
which keeps the type the old value had. -/
theorem write (hwt : StateWT H C.layout σ) {r : Name} {segs : List Seg} {T : Ty} {new : SVal}
    (hty : C.layout.tyAt r segs = some T) (hnew : new.hasTy T = true)
    (h : σ.writeStorage r segs new = .ok σ') : StateWT H C.layout σ' := by
  rcases State.writeStorage_ok_inv h with h | ⟨cur, hcur, h⟩
  · exact hwt.save hty hnew h
  · exact hwt.save hty (SVal.overlay_hasTy (findStorage_hasTy hwt.storage hty hcur) hnew) h

/-- Along an allocation (a storage→memory copy, a fresh default) the
store typing grows and everything typed stays typed. -/
theorem ofCopyOut {H' : HeapTy} (hwt : StateWT H C.layout σ) (hout : CopyOut H σ H' σ') :
    StateWT H' C.layout σ' where
  layoutNodup := hwt.layoutNodup
  heapTyNodup := hout.nodup
  storage := by rw [hout.storage]; exact hwt.storage
  heap := hout.heap
  heapWf := hout.heapWf

/-- A memory write of an object of the identity's claimed type:
`m.age = 3;` keeps `m`'s object a `Person`. -/
theorem setObj (hwt : StateWT H C.layout σ) {id : Nat} {ty : Ty} {obj obj₀ : MObj}
    (hclaim : lookupBy id H = some ty) (hpresent : lookupBy id σ.heap = some obj₀)
    (hobj : obj.hasTyH H ty = true) : StateWT H C.layout (σ.setObj id obj) where
  layoutNodup := hwt.layoutNodup
  heapTyNodup := hwt.heapTyNodup
  storage := hwt.storage
  heap := heapTypedB_setObj hwt.heapTyNodup hwt.heap hclaim hobj
  heapWf := HeapWellFormed.setObj' hwt.heapWf (by simp [hpresent])

/-- A payment books the ledger only. -/
theorem pay (hwt : StateWT H C.layout σ) {addr amt : Int} :
    StateWT H C.layout (σ.pay addr amt) := by
  rw [State.pay_eq]; exact ⟨hwt.1, hwt.2, hwt.3, hwt.4, hwt.5⟩

/-- `a.transfer(v)` books the ledger only. -/
theorem transferAt (hwt : StateWT H C.layout σ) {addr amt : Int}
    (h : Solidity.transferAt σ addr amt = .ok σ') : StateWT H C.layout σ' := by
  unfold Solidity.transferAt at h
  split at h
  · exact nomatch h
  · cases h; exact hwt.pay

end Semantics.StateWT

/-! ## The statements' effects on the global part are typed -/

section Effects

variable {H : HeapTy} {σ σ' : State}


theorem arith_new_wt {op : BinOp} {p : PrimTy} {old v n₁ n₂ : Value}
    (hop : op.isArith = true) (hp : p.isNumeric = true)
    (h₁ : applyBinOp op old v = .ok n₁) (h₂ : checkArith (.prim p) n₁ = .ok n₂) :
    (Value.toSVal n₂).hasTy (.prim p) = true := by
  rw [checkArith_ok_eq h₂]
  obtain ⟨n, rfl⟩ := applyBinOp_arith_int hop h₁
  exact int_toSVal_hasTy hp n

/-- `x++` stores and yields numbers of `x`'s type. -/
theorem bump_new_wt {p : PrimTy} {m : Int} {n : Value} (hp : p.isNumeric = true)
    (h : checkArith (.prim p) (.int m) = .ok n) : (Value.toSVal n).hasTy (.prim p) = true := by
  rw [checkArith_ok_eq h]; exact int_toSVal_hasTy hp m

/-- `+=` .. `%=` are arithmetic, so `x += 1` writes a number. -/
theorem compound_isArith {op : BinOp} (h : op.hasCompoundAssign = true) : op.isArith = true := by
  cases op <;> simp_all [BinOp.hasCompoundAssign, BinOp.isArith]

/-- `b.push(v)` at an array of `E`s appends an `E`.  The slot the push
lands on is an `E` whenever `E`'s default is well-formed; a push with an
argument does not look at it. -/
theorem pushAt_wt (hwt : StateWT H C.layout σ) {E : Ty} {r : Name} {segs : List Seg}
    {val : SVal → Res SVal} (hty : C.layout.tyAt r segs = some (.ref (.array E)))
    (hval : ∀ slot v, (defaultOk E = true → slot.hasTy E = true) → val slot = .ok v →
      v.hasTy E = true)
    (h : pushAt σ E r segs val = .ok σ') : StateWT H C.layout σ' := by
  obtain ⟨sv, hsv, h⟩ := bind_ok_inv h
  have hsvt := findStorage_hasTy hwt.storage hty hsv
  cases sv with
  | array elems shadow fx =>
    simp only [SVal.hasTy, Bool.and_eq_true] at hsvt
    obtain ⟨newElem, hnew, h⟩ := bind_ok_inv h
    have hslot : defaultOk E = true → (pushSlot E shadow).1.hasTy E = true :=
      fun hok => (pushSlot_hasTy hsvt.2 hok).1
    refine hwt.save hty ?_ h
    simp only [SVal.hasTy, Bool.and_eq_true]
    refine ⟨⟨hsvt.1.1, hasTyElems_append hsvt.1.2 ?_⟩, pushSlot_rest_hasTy hsvt.2⟩
    simp [SVal.hasTy.hasTyElems, hval _ _ hslot hnew]
  | prim _ => exact nomatch h
  | struct _ => exact nomatch h
  | map _ _ => exact nomatch h

/-- `b.push()` as a place: the array stays typed. -/
theorem pushPlaceAt_wt (hwt : StateWT H C.layout σ) {E : Ty} {r : Name} {segs : List Seg} {n : Int}
    (hty : C.layout.tyAt r segs = some (.ref (.array E))) (hok : defaultOk E = true)
    (h : pushPlaceAt σ E r segs = .ok (σ', n)) : StateWT H C.layout σ' := by
  obtain ⟨sv, hsv, h⟩ := bind_ok_inv h
  have hsvt := findStorage_hasTy hwt.storage hty hsv
  cases sv with
  | array elems shadow fx =>
    simp only [SVal.hasTy, Bool.and_eq_true] at hsvt
    obtain ⟨σ₁, hσ₁, h⟩ := bind_ok_inv h
    cases h
    refine hwt.save hty ?_ hσ₁
    simp only [SVal.hasTy, Bool.and_eq_true]
    refine ⟨⟨hsvt.1.1, hasTyElems_append hsvt.1.2 ?_⟩, pushSlot_rest_hasTy hsvt.2⟩
    simp only [SVal.hasTy.hasTyElems, Bool.and_true]
    exact (pushSlot_hasTy hsvt.2 hok).1
  | prim _ => exact nomatch h
  | struct _ => exact nomatch h
  | map _ _ => exact nomatch h

/-- `b.pop()` keeps the array typed: the popped element is cleared into
the recycled slots at its own type. -/
theorem popAt_wt (hwt : StateWT H C.layout σ) {E : Ty} {keep : Bool} {r : Name} {segs : List Seg}
    (hty : C.layout.tyAt r segs = some (.ref (.array E))) (h : popAt σ keep r segs = .ok σ') :
    StateWT H C.layout σ' := by
  obtain ⟨sv, hsv, h⟩ := bind_ok_inv h
  have hsvt := findStorage_hasTy hwt.storage hty hsv
  cases sv with
  | array elems shadow fx =>
    simp only [SVal.hasTy, Bool.and_eq_true] at hsvt
    simp only at h
    split at h
    · exact nomatch h
    · rename_i last restRev hrev
      have hmem : ∀ v, v ∈ last :: restRev → v ∈ elems := by
        intro v hv; rw [← hrev] at hv; exact List.mem_reverse.mp hv
      refine hwt.save hty ?_ h
      simp only [SVal.hasTy, Bool.and_eq_true, SVal.hasTy.hasTyElems]
      refine ⟨⟨hsvt.1.1, hasTyElems_of_forall_mem fun v hv => ?_⟩, ?_, hsvt.2⟩
      · exact hasTyElems_mem hsvt.1.2 (hmem v (List.mem_cons_of_mem _ (List.mem_reverse.mp hv)))
      · have hl := hasTyElems_mem hsvt.1.2 (hmem last List.mem_cons_self)
        cases keep
        · exact SVal.defaultOf_hasTy hl
        · exact hl
  | prim _ => exact nomatch h
  | struct _ => exact nomatch h
  | map _ _ => exact nomatch h

/-- A write into a memory struct's member of the member's type. -/
theorem memWriteField_wt (hwt : StateWT H C.layout σ) {id : Nat} {s f : Name} {T : Ty} {mv : MVal}
    (hid : lookupBy id H = some (.ref (.struct s))) (hf : lookupBy f (structDef s) = some T)
    (hmv : MVal.hasTyH H mv T = true) (h : memWriteField σ id f mv = .ok σ') :
    StateWT H C.layout σ' := by
  obtain ⟨obj, hobj, hty⟩ := heapTypedB_obj hwt.heap hid
  obtain ⟨o, ho, h⟩ := bind_ok_inv h
  simp only [State.getObj, hobj] at ho
  cases ho
  cases obj with
  | struct fields =>
    cases h
    exact hwt.setObj hid hobj
      (by simpa [MObj.hasTyH] using mHasTyHFields_setBy (by simpa [MObj.hasTyH] using hty) hf hmv)
  | array _ => exact nomatch h

/-- A write into a memory array's element of the element type. -/
theorem memWriteIndex_wt (hwt : StateWT H C.layout σ) {id : Nat} {i : Int} {R : RefTy} {E : Ty}
    {mv : MVal} (hid : lookupBy id H = some (.ref R)) (hR : R.arrElem? = some E)
    (hmv : MVal.hasTyH H mv E = true)
    (h : memWriteIndex σ id i mv = .ok σ') : StateWT H C.layout σ' := by
  obtain ⟨obj, hobj, hty⟩ := heapTypedB_obj hwt.heap hid
  obtain ⟨o, ho, h⟩ := bind_ok_inv h
  simp only [State.getObj, hobj] at ho
  cases ho
  cases obj with
  | array elems fx =>
    simp only at h
    split at h
    · cases h
      refine hwt.setObj hid hobj ?_
      cases R <;> simp only [RefTy.arrElem?, Option.some.injEq, reduceCtorEq] at hR <;>
        subst hR <;> simp only [MObj.hasTyH, Bool.and_eq_true, beq_iff_eq] at hty ⊢
      · exact ⟨hty.1, mHasTyHElems_set hty.2 hmv⟩
      · exact ⟨⟨hty.1.1, by simp [hty.1.2]⟩, mHasTyHElems_set hty.2 hmv⟩
    · exact nomatch h
  | struct _ => exact nomatch h

/-- The memory place a memory target resolves to holds a `p`: `m.age`
with `m : Person memory`, `ns[i]` with `ns : uint[] memory`. -/
def AddrTy (H : HeapTy) (p : PrimTy) : Addr → Prop
  | .memoryField id f => ∃ s, lookupBy id H = some (.ref (.struct s)) ∧
      lookupBy f (structDef s) = some (.prim p)
  | .memoryIndex id _ => ∃ R, lookupBy id H = some (.ref R) ∧ R.arrElem? = some (.prim p)

/-- The memory place a memory location resolves to holds a `T`. -/
def AddrTyT (H : HeapTy) (T : Ty) : Addr → Prop
  | .memoryField id f => ∃ s, lookupBy id H = some (.ref (.struct s)) ∧
      lookupBy f (structDef s) = some T
  | .memoryIndex id _ => ∃ R, lookupBy id H = some (.ref R) ∧ R.arrElem? = some T

/-- A typed place stays typed as the store typing grows (an allocation). -/
theorem AddrTyT.mono {H H' : HeapTy} {T : Ty} {a : Addr} (hext : H.Extends H')
    (h : AddrTyT H T a) : AddrTyT H' T a := by
  cases a with
  | memoryField id f => obtain ⟨s, hid, hf⟩ := h; exact ⟨s, hext _ _ hid, hf⟩
  | memoryIndex id i => obtain ⟨R, hid, hR⟩ := h; exact ⟨R, hext _ _ hid, hR⟩

/-- `delete m.inner;` writes an object of the member's type there. -/
theorem writeAddr_wt (hwt : StateWT H C.layout σ) {T : Ty} {a : Addr} {mv : MVal}
    (ha : AddrTyT H T a) (hmv : MVal.hasTyH H mv T = true)
    (h : writeAddr σ mv a = .ok σ') : StateWT H C.layout σ' := by
  cases a with
  | memoryField id f =>
    obtain ⟨s, hid, hf⟩ := ha
    exact memWriteField_wt hwt hid hf hmv h
  | memoryIndex id i => obtain ⟨R, hid, hR⟩ := ha; exact memWriteIndex_wt hwt hid hR hmv h

/-- `m.age -= 1;` writes a number where the heap says `uint`. -/
theorem writeLoc_wt (hwt : StateWT H C.layout σ) {p : PrimTy} {loc : Addr} {v : Value}
    (hloc : AddrTy H p loc) (hv : (Value.toSVal v).hasTy (.prim p) = true)
    (h : writeLoc σ loc v = .ok σ') : StateWT H C.layout σ' := by
  cases loc with
  | memoryField id f =>
    obtain ⟨s, hid, hf⟩ := hloc
    exact memWriteField_wt hwt hid hf (Value.toMVal_hasTyH hv) h
  | memoryIndex id i =>
    obtain ⟨R, hid, hR⟩ := hloc
    exact memWriteIndex_wt hwt hid hR (Value.toMVal_hasTyH hv) h

/-- `x ⊕= e` at a storage place of a numeric type. -/
theorem opStore_wt (hwt : StateWT H C.layout σ) {op : BinOp} {p : PrimTy} {r : Name}
    {segs : List Seg} {v : Value} (hop : op.isArith = true) (hp : p.isNumeric = true)
    (hty : C.layout.tyAt r segs = some (.prim p)) (h : opStore σ op p r segs v = .ok σ') :
    StateWT H C.layout σ' := by
  obtain ⟨_, _, _, h₁, h₂, h⟩ := opStore_ok_inv h
  exact hwt.save hty (arith_new_wt hop hp h₁ h₂) h

/-- `m.age += x;` keeps the heap typed. -/
theorem opMem_wt (hwt : StateWT H C.layout σ) {op : BinOp} {p : PrimTy} {loc : Addr} {v : Value}
    (hop : op.isArith = true) (hp : p.isNumeric = true) (hloc : AddrTy H p loc)
    (h : opMem σ op p loc v = .ok σ') : StateWT H C.layout σ' := by
  obtain ⟨_, _, _, h₁, h₂, h⟩ := opMem_ok_inv h
  exact writeLoc_wt hwt hloc (arith_new_wt hop hp h₁ h₂) h

/-- `alice.age++` stores and yields numbers. -/
theorem bumpStore_wt (hwt : StateWT H C.layout σ) {op : IncDec} {p : PrimTy} {r : Name}
    {segs : List Seg} {w : Value} (hp : p.isNumeric = true)
    (hty : C.layout.tyAt r segs = some (.prim p)) (h : bumpStore σ op p r segs = .ok (σ', w)) :
    StateWT H C.layout σ' ∧ (Value.toSVal w).hasTy (.prim p) = true := by
  obtain ⟨m, n, hn, hσ₁, rfl⟩ := bumpStore_ok_inv h
  have hnew := bump_new_wt hp hn
  refine ⟨hwt.save hty hnew hσ₁, ?_⟩
  split
  · exact hnew
  · exact int_toSVal_hasTy hp m

/-- `m.age++` stores and yields numbers. -/
theorem bumpMem_wt (hwt : StateWT H C.layout σ) {op : IncDec} {p : PrimTy} {loc : Addr} {w : Value}
    (hp : p.isNumeric = true) (hloc : AddrTy H p loc) (h : bumpMem σ op p loc = .ok (σ', w)) :
    StateWT H C.layout σ' ∧ (Value.toSVal w).hasTy (.prim p) = true := by
  obtain ⟨m, n, hn, hσ₁, rfl⟩ := bumpMem_ok_inv h
  have hnew := bump_new_wt hp hn
  refine ⟨writeLoc_wt hwt hloc hnew hσ₁, ?_⟩
  split
  · exact hnew
  · exact int_toSVal_hasTy hp m

/-- `new uint[](n)` copies in a value of its type: `n` well-formed defaults. -/
theorem newArrVal_hasTy {R : RefTy} (h : R.newArrOk = true) (n : Int) :
    (newArrVal R n).hasTy (.ref R) = true := by
  cases R with
  | array E =>
    simp only [RefTy.newArrOk, Bool.and_eq_true] at h
    have hE := defaultForTy_hasTy (defaultOk_of_defaultOkS h.2)
    simp only [newArrVal, SVal.hasTy, SVal.hasTy.hasTyElems, Bool.and_true, Bool.not_false,
      Bool.true_and]
    induction n.toNat with
    | zero => rfl
    | succ k ih => simp [List.replicate_succ, SVal.hasTy.hasTyElems, hE, ih]
  | struct _ => simp [RefTy.newArrOk] at h
  | fixed _ _ => simp [RefTy.newArrOk] at h
  | mapping _ _ => simp [RefTy.newArrOk] at h


end Effects


/-! ## Where a run starts -/

theorem Semantics.lookupBy_map_snd {k : Name} {f : Ty → SVal} :
    ∀ l : List (Name × Ty), lookupBy k (l.map fun (n, T) => (n, f T)) = (lookupBy k l).map f
  | [] => rfl
  | (n, T) :: rest => by
    by_cases h : k = n
    · simp [lookupBy, h]
    · simp [lookupBy, h, lookupBy_map_snd rest]


/-- A contract starts well-typed: each root at its type's default, an empty
heap.  `StandardExample` starts in `State.exampleStore`
(`exampleStore_wt`). -/
theorem Semantics.StateWT.init {σ : State} (hnd : nodupKeysB C.vars = true)
    (hok : C.vars.all (·.2.defaultOkS) = true)
    (hst : σ.storage = C.initStorage) (hheap : σ.heap = []) : StateWT [] C.layout σ where
  layoutNodup := hnd
  heapTyNodup := rfl
  storage := by
    rw [hst]
    refine List.all_eq_true.mpr fun g hg => ?_
    show (match lookupBy g.1 C.initStorage with
      | some v => v.hasTy g.2
      | none => false) = true
    simp only [Contract.initStorage, lookupBy_map_snd, lookupBy_eq_of_nodup hnd hg, Option.map]
    exact defaultForTy_hasTy (defaultOk_of_defaultOkS (List.all_eq_true.mp hok g hg))
  heap := rfl
  heapWf := fun i _ => by rw [hheap]; rfl

/-- `StandardExample`'s store is well-typed. -/
theorem exampleStore_wt : StateWT [] StandardExample.layout State.exampleStore :=
  StateWT.init (by decide) (by decide) initStorage_standardExample.symm rfl

end Solidity

/-! # Over the scoped syntax

The locals are typed by their context: `Env.All (LTy.WT C H) σ.env` says each
local holds what its type says, and `RunWT` adds the global part. -/

namespace Solidity

open Semantics hiding State
open SemanticsProperties (HeapWellFormed)

variable {C : Contract}

/-! ## Results -/

theorem map_ok_inv {α β : Type} {f : α → β} {x : Res α} {b : β} (h : f <$> x = .ok b) :
    ∃ a, x = .ok a ∧ f a = b := by
  cases x with
  | error e => exact nomatch h
  | ok a => exact ⟨a, rfl, Except.ok.inj h⟩

/-! ## Locals that satisfy a predicate -/

/-- Every local of `e` satisfies `P` at its type. -/
def Env.All (P : (t : LTy) → t.Denote C → Prop) : {Γ : Ctx} → Env C Γ → Prop
  | [], _ => True
  | _ :: _, e => P _ e.1 ∧ Env.All P e.2

namespace Env.All

variable {P Q : (t : LTy) → t.Denote C → Prop}

theorem get : {Γ : Ctx} → {t : LTy} → (i : Idx Γ t) → {e : Env C Γ} → Env.All P e →
    P t (Env.get i e) := by
  intro Γ t i
  induction i with
  | here => intro e h; exact h.1
  | there i ih => intro e h; exact ih h.2

theorem set : {Γ : Ctx} → {t : LTy} → (i : Idx Γ t) → {e : Env C Γ} → {v : t.Denote C} →
    Env.All P e → P t v → Env.All P (Env.set i v e) := by
  intro Γ t i
  induction i with
  | here => intro e v h hv; exact ⟨hv, h.2⟩
  | there i ih => intro e v h hv; exact ⟨h.1, ih h.2 hv⟩

theorem drop {Γ : Ctx} : {Δ : Ctx} → (h : Ext Γ Δ) → {e : Env C Δ} → Env.All P e →
    Env.All P (Env.drop h e) := by
  intro Δ h
  induction h with
  | refl => intro e he; exact he
  | push h ih => intro e he; exact ih he.2

theorem append {Γ : Ctx} : (ρ : Ctx) → {r : Env C ρ} → {e : Env C Γ} → Env.All P r →
    Env.All P e → Env.All P (Env.append ρ r e)
  | [], _, _, _, he => he
  | _ :: ρ, _, _, hr, he => ⟨hr.1, append ρ hr.2 he⟩

theorem take {Γ : Ctx} : (ρ : Ctx) → {e : Env C (ρ ++ Γ)} → Env.All P e → Env.All P (Env.take ρ e)
  | [], _, _ => trivial
  | _ :: ρ, _, he => ⟨he.1, take ρ he.2⟩

theorem mono (hPQ : ∀ t v, P t v → Q t v) : {Γ : Ctx} → {e : Env C Γ} → Env.All P e →
    Env.All Q e
  | [], _, _ => trivial
  | _ :: _, _, he => ⟨hPQ _ _ he.1, mono hPQ he.2⟩

theorem and : {Γ : Ctx} → {e : Env C Γ} → Env.All P e → Env.All Q e →
    Env.All (fun t v => P t v ∧ Q t v) e
  | [], _, _, _ => trivial
  | _ :: _, _, hp, hq => ⟨⟨hp.1, hq.1⟩, and hp.2 hq.2⟩

end Env.All

/-- Leaving a call keeps every local satisfying `P` when the caller's and the
frame's return variables do. -/
theorem CallRet.leave_all {P : (t : LTy) → t.Denote C → Prop} {Γ rs Γ' : Ctx}
    (ret : CallRet Γ rs Γ') {e : Env C Γ} {r : Env C rs} (he : Env.All P e) (hr : Env.All P r) :
    Env.All P (ret.leave e r) := by
  cases ret with
  | none => exact he
  | val p x res =>
    cases res with
    | none => exact he
    | some i => exact Env.All.set i he hr.1
  | rets bs => exact Env.All.append _ hr he
  | mem R x hd hm => exact ⟨hr.1, he⟩

/-! ## Invariants of runs

What a run keeps is a part on the global state and a part on each local,
the latter kept as the store typing grows (`Typing/TypedRunInv.lean` carries
it along the typed run). -/

/-- An invariant of runs: a part on the global state, a part on each
local, kept as the store typing `H` grows, and blind to the locals. -/
structure RunInv (C : Contract) where
  glob : HeapTy → Semantics.State → Prop
  loc : HeapTy → (t : LTy) → t.Denote C → Prop
  loc_mono : ∀ {H H' : HeapTy} {t : LTy} {v : t.Denote C}, H.Extends H' → loc H t v →
    loc H' t v
  reglob : ∀ {H : HeapTy} {τ : Semantics.State} {Γ : Ctx} (e : Env C Γ), glob H τ →
    glob H (EState.ofGlob τ e).glob

namespace RunInv

variable (I : RunInv C)

/-- The invariant holds of a state under the store typing `H`. -/
def Holds {Γ : Ctx} (H : HeapTy) (σ : EState C Γ) : Prop :=
  I.glob H σ.glob ∧ Env.All (I.loc H) σ.env

/-- A step on erased states keeps the invariant: from a state it holds of,
it ends, if in a state, in one it holds of under a store typing that only
grew (what a typed leaf erases to, `RunInv.TKeeps.of_agrees`). -/
def Keeps {Γ Γ' : Ctx} (f : EState C Γ → Res (EState C Γ')) : Prop :=
  ∀ (H : HeapTy) (σ : EState C Γ) (σ' : EState C Γ'), I.Holds H σ → f σ = .ok σ' →
    ∃ H', H.Extends H' ∧ I.Holds H' σ'

variable {I}

theorem env_mono {Γ : Ctx} {H H' : HeapTy} (hext : H.Extends H') {e : Env C Γ}
    (h : Env.All (I.loc H) e) : Env.All (I.loc H') e :=
  Env.All.mono (fun _ _ => I.loc_mono hext) h

theorem Holds.withEnv {Γ Δ : Ctx} {H : HeapTy} {σ : EState C Γ} (h : I.Holds H σ) {e : Env C Δ}
    (he : Env.All (I.loc H) e) : I.Holds H (σ.withEnv e) :=
  ⟨h.1, he⟩

theorem Holds.drop {Γ Δ : Ctx} {H : HeapTy} {σ : EState C Δ} (h : I.Holds H σ) (x : Ext Γ Δ) :
    I.Holds H (σ.drop x) :=
  ⟨h.1, Env.All.drop x h.2⟩

end RunInv

/-! ## The typed locals -/

/-- A local's value is of its type: a value of its primitive type, an alias
bound (if at all) to a path the layout types at its type, a memory local,
if set at all, an identity the store typing claims at its type (an unset
one, decision 17', reads as a revert). -/
def LTy.WT (C : Contract) (H : HeapTy) : (t : LTy) → t.Denote C → Prop
  | .val p, v => (Value.toSVal v).hasTy (.prim p) = true
  | .alias R, o => ∀ r segs, o = some (r, segs) → C.layout.tyAt r segs = some (.ref R)
  | .mem R, o => ∀ id, o = some id → MVal.hasTyH H (.ref id) (.ref R) = true
  | .old, _ => True
  | .oldNet, _ => True

/-- A memory local set to an identity of its type. -/
theorem LTy.WT.mem_some {H : HeapTy} {R : RefTy} {id : Nat}
    (h : MVal.hasTyH H (.ref id) (.ref R) = true) : LTy.WT C H (.mem R) (some id) :=
  fun _ e => Option.some.inj e ▸ h

theorem LTy.WT.mono {H H' : HeapTy} (hext : H.Extends H') :
    {t : LTy} → {v : t.Denote C} → LTy.WT C H t v → LTy.WT C H' t v
  | .val _, _, h => h
  | .alias _, _, h => h
  | .mem _, _, h => fun id hid => MVal.hasTyH_mono hext (h id hid)
  | .old, _, h => h
  | .oldNet, _, h => h

theorem LTy.WT.default (p : PrimTy) : LTy.WT C H (.val p) (PrimTy.default p) := by
  cases p <;> rfl

/-- A storage-and-heap invariant is blind to the locals. -/
theorem _root_.Solidity.Semantics.StateWT.reglob {H : HeapTy} {L : Layout} {τ : Semantics.State}
    {Γ : Ctx} (h : StateWT H L τ) (e : Env C Γ) : StateWT H L (EState.ofGlob τ e).glob :=
  ⟨h.1, h.2, h.3, h.4, h.5⟩

/-- Type soundness's invariant: the global part well-typed, every local of
its type. -/
def wtInv (C : Contract) : RunInv C where
  glob H τ := StateWT H C.layout τ
  loc := LTy.WT C
  loc_mono hext h := LTy.WT.mono hext h
  reglob e h := h.reglob e

/-- The state invariant over a context: the global part well-typed under
`C`'s layout and the store typing `H`, each local of its type. -/
abbrev RunWT (C : Contract) {Γ : Ctx} (H : HeapTy) (σ : EState C Γ) : Prop := (wtInv C).Holds H σ

namespace RunWT

variable {Γ : Ctx} {H : HeapTy} {σ : EState C Γ}

theorem glob (hwt : RunWT C H σ) : StateWT H C.layout σ.glob := hwt.1

theorem env (hwt : RunWT C H σ) : Env.All (LTy.WT C H) σ.env := hwt.2

/-- The global part replaced by a well-typed one under a grown store
typing. -/
theorem withGlob {H' : HeapTy} (hwt : RunWT C H σ) (hext : H.Extends H') {τ : Semantics.State}
    (hτ : StateWT H' C.layout τ) : RunWT C H' (σ.withGlob τ) :=
  ⟨hτ.reglob σ.env, Env.All.mono (fun _ _ => LTy.WT.mono hext) hwt.env⟩

theorem setLocal (hwt : RunWT C H σ) {t : LTy} (i : Idx Γ t) {v : t.Denote C}
    (hv : LTy.WT C H t v) : RunWT C H (σ.setLocal i v) :=
  ⟨hwt.glob, Env.All.set i hwt.env hv⟩

theorem push (hwt : RunWT C H σ) {t : LTy} {v : t.Denote C} (hv : LTy.WT C H t v) :
    RunWT C H (σ.push v) :=
  ⟨hwt.glob, hv, hwt.env⟩

end RunWT

/-! ## The evaluators are typed

Each mirrors `Semantics.lean`'s evaluator's typing, a local read where the
old one looked a name up.  `H` is fixed here: nothing an expression does
allocates. -/

section Eval

variable {Γ : Ctx} {H : HeapTy} {σ : EState C Γ}

/-- A simple value is of its type: the local `x : uint` holds a number. -/
theorem Simple.eval_wt (hwt : RunWT C H σ) {p : PrimTy} {s : Simple C Γ p} {w : Value}
    (h : s.eval σ = .ok w) : (Value.toSVal w).hasTy (.prim p) = true := by
  cases s with
  | lit n hn => cases h; exact int_toSVal_hasTy (PrimTy.isNumeric_of_inRange hn) n
  | bool b => cases h; rfl
  | «local» i => cases h; exact hwt.env.get i
  | env k hp => subst hp; cases h; rfl

/-- An alias is bound to a path the layout types at its type. -/
theorem aliasPath_wt (hwt : RunWT C H σ) {R : RefTy} (i : Idx Γ (.alias R)) {r : Name}
    {segs : List Seg} (h : aliasPath σ i = .ok (r, segs)) :
    C.layout.tyAt r segs = some (.ref R) := by
  have hi : LTy.WT C H (.alias R) (Env.get i σ.env) := hwt.env.get i
  unfold aliasPath at h
  split at h
  · rename_i p hp
    cases h
    exact hi _ _ hp
  · exact nomatch h

mutual

/-- A storage path resolves to a place the layout types at the path's type:
`p.age`, with `p : Person storage`, at `uint`. -/
theorem SPath.resolve_wt (hwt : RunWT C H σ) :
    ∀ {T : Ty} (p : SPath C Γ T) {r : Name} {segs : List Seg},
      p.resolve σ = .ok (r, segs) → C.layout.tyAt r segs = some T
  | _, .alias i, _, _, h => aliasPath_wt hwt i h
  | _, .loc l, _, _, h => Loc.resolve_wt hwt l h

/-- `alice.age` resolves to `(alice, [age])`, which the layout types `uint`. -/
theorem Loc.resolve_wt (hwt : RunWT C H σ) :
    ∀ {T : Ty} (l : Loc C Γ T) {r : Name} {segs : List Seg},
      l.resolve σ = .ok (r, segs) → C.layout.tyAt r segs = some T
  | _, .root r' hr, r, segs, h => by
    cases h
    exact Contract.layout_tyAt_root hr
  | _, .field b f hf, r, segs, h => by
    obtain ⟨⟨r0, s0⟩, h0, h⟩ := bind_ok_inv h
    cases h
    exact tyAt_append_seg (SPath.resolve_wt hwt b h0) hf
  | _, .index it b i, r, segs, h => by
    obtain ⟨⟨r0, s0⟩, h0, h⟩ := bind_ok_inv h
    obtain ⟨k, _, h⟩ := bind_ok_inv h
    obtain ⟨iv, _, h⟩ := bind_ok_inv h
    bind_inv h
    cases h
    have hb := SPath.resolve_wt hwt b h0
    cases it with
    | map => exact tyAt_append_seg hb rfl
    | arr a => cases a <;> exact tyAt_append_seg hb rfl

end

mutual

/-- A memory path holds a slot of its type: `m`, with `m : Person memory`,
an identity the store typing claims at `Person`. -/
theorem MPath.mval_wt (hwt : RunWT C H σ) :
    ∀ {T : Ty} (p : MPath C Γ T) {mv : MVal}, p.mval σ = .ok mv → MVal.hasTyH H mv T = true
  | _, .var i _, mv, h => by
    simp only [MPath.mval, memRef] at h
    split at h
    · cases h; exact hwt.env.get i _ ‹_›
    · cases h
  | _, .loc l, mv, h => MLoc.read_wt hwt l h

/-- `m.age` reads a slot the heap types `uint`. -/
theorem MLoc.read_wt (hwt : RunWT C H σ) :
    ∀ {T : Ty} (l : MLoc C Γ T) {mv : MVal}, l.read σ = .ok mv → MVal.hasTyH H mv T = true
  | _, @MLoc.field _ _ s _ b f hf, mv, h => by
    obtain ⟨m0, hm0, h⟩ := bind_ok_inv h
    obtain ⟨id, hid, h⟩ := bind_ok_inv h
    have hb := MPath.mval_wt hwt b hm0
    rw [MVal.asRef_ok hid, MVal.hasTyH_ref] at hb
    obtain ⟨obj, hobj, hty⟩ := heapTypedB_obj hwt.glob.heap hb
    obtain ⟨o, ho, h⟩ := bind_ok_inv h
    simp only [Semantics.State.getObj, hobj] at ho
    cases ho
    cases obj with
    | struct fields =>
      simp only at h
      split at h
      · rename_i v hv
        cases h
        obtain ⟨ty, hdef, hv⟩ := mHasTyHFields_lookup (by simpa [MObj.hasTyH] using hty) hv
        have : ty = _ := Option.some.inj (hdef.symm.trans hf)
        subst this
        exact hv
      · exact nomatch h
    | array _ => exact nomatch h
  | _, @MLoc.index _ _ _ E a b i, mv, h => by
    obtain ⟨m0, hm0, h⟩ := bind_ok_inv h
    obtain ⟨id, hid, h⟩ := bind_ok_inv h
    have hb := MPath.mval_wt hwt b hm0
    rw [MVal.asRef_ok hid, MVal.hasTyH_ref] at hb
    obtain ⟨obj, hobj, hty⟩ := heapTypedB_obj hwt.glob.heap hb
    obtain ⟨elems, fx, rfl, hel⟩ := MObj.hasTyH_arrElem a.arrElem hty
    bind_inv h
    obtain ⟨iv, _, h⟩ := bind_ok_inv h
    obtain ⟨o, ho, h⟩ := bind_ok_inv h
    simp only [Semantics.State.getObj, hobj] at ho
    cases ho
    simp only at h
    split at h
    · cases h
      exact mHasTyHElems_mem hel (List.get_mem _ _)
    · exact nomatch h

end

/-- A value evaluates to a value of its type: `alice.age + 1` to a number,
`x < y` to a boolean. -/
theorem Val.eval_wt (hwt : RunWT C H σ) :
    ∀ {p : PrimTy} (v : Val C Γ p) {w : Value}, v.eval σ = .ok w →
      (Value.toSVal w).hasTy (.prim p) = true
  | _, .simple s, w, h => Simple.eval_wt hwt h
  | _, .read l, w, h => by
    obtain ⟨⟨r, segs⟩, hr, h⟩ := bind_ok_inv h
    obtain ⟨sv, hsv, h⟩ := bind_ok_inv h
    exact SVal.asValue_hasTy
      (findStorage_hasTy hwt.glob.storage (Loc.resolve_wt hwt l hr) hsv) h
  | _, .binop op hacc hq a b, w, h => by
    obtain ⟨lv, _, h⟩ := bind_ok_inv h
    exact evalBinop_wt hacc hq h
  | _, .unop op hacc hq a, w, h => by
    obtain ⟨av, _, h⟩ := bind_ok_inv h
    exact evalUnop_wt hacc hq h
  | _, .ternary c a b, w, h => by
    obtain ⟨cv, _, h⟩ := bind_ok_inv h
    unfold pickBranch at h
    split at h
    · exact Val.eval_wt hwt a h
    · exact Val.eval_wt hwt b h
    · exact nomatch h
  | _, .readMem l, w, h => by
    obtain ⟨mv, hmv, h⟩ := bind_ok_inv h
    exact MVal.asValue_hasTy (MLoc.read_wt hwt l hmv) h
  | _, .len b hp, w, h => by
    subst hp
    bind_inv h
    obtain ⟨sv, _, h⟩ := bind_ok_inv h
    split at h
    · cases h; rfl
    all_goals exact nomatch h
  | _, .mlen b hp, w, h => by
    subst hp
    iterate 2 bind_inv h
    obtain ⟨o, _, h⟩ := bind_ok_inv h
    split at h
    · cases h; rfl
    all_goals exact nomatch h

/-- A source stores a value of its type: `alice = bob;` copies a `Person`. -/
theorem Src.value_wt (hwt : RunWT C H σ) {T : Ty} {r : Src C Γ T} {sv : SVal}
    (h : r.value σ = .ok sv) : sv.hasTy T = true := by
  cases r with
  | val v =>
    obtain ⟨w, hv, h⟩ := bind_ok_inv h
    cases h
    exact Val.eval_wt hwt v hv
  | copy p _ =>
    obtain ⟨⟨r, segs⟩, hr, h⟩ := bind_ok_inv h
    exact findStorage_hasTy hwt.glob.storage (SPath.resolve_wt hwt p hr) h

/-- A memory location resolves to a place of its type. -/
theorem MLoc.addr_wt (hwt : RunWT C H σ) :
    ∀ {T : Ty} (l : MLoc C Γ T) {a : Addr}, l.addr σ = .ok a → AddrTyT H T a
  | _, @MLoc.field _ _ s _ b f hf, a, h => by
    obtain ⟨m0, hm0, h⟩ := bind_ok_inv h
    obtain ⟨id, hid, h⟩ := bind_ok_inv h
    cases h
    have hb := MPath.mval_wt hwt b hm0
    rw [MVal.asRef_ok hid, MVal.hasTyH_ref] at hb
    exact ⟨s, hb, hf⟩
  | _, .index ak b i, a, h => by
    obtain ⟨m0, hm0, h⟩ := bind_ok_inv h
    obtain ⟨id, hid, h⟩ := bind_ok_inv h
    bind_inv h
    obtain ⟨iv, _, h⟩ := bind_ok_inv h
    cases h
    have hb := MPath.mval_wt hwt b hm0
    rw [MVal.asRef_ok hid, MVal.hasTyH_ref] at hb
    exact ⟨_, hb, ak.arrElem⟩

/-- What a memory write stores is of the place's type. -/
theorem MSrc.mval_wt (hwt : RunWT C H σ) {T : Ty} {r : MSrc C Γ T} {mv : MVal}
    (h : r.mval σ = .ok mv) : MVal.hasTyH H mv T = true := by
  cases r with
  | val v =>
    obtain ⟨w, hv, h⟩ := bind_ok_inv h
    cases h
    exact Value.toMVal_hasTyH (Val.eval_wt hwt v hv)
  | ref p =>
    obtain ⟨m0, hm0, h⟩ := bind_ok_inv h
    obtain ⟨id, hid, h⟩ := bind_ok_inv h
    cases h
    have := MPath.mval_wt hwt p hm0
    rwa [MVal.asRef_ok hid] at this

/-- A call's arguments are of their parameters' types. -/
theorem Args.eval_wt (hwt : RunWT C H σ) :
    {ps : Ctx} → (args : Args C Γ ps) → {a : Env C ps} → args.eval σ = .ok a →
      Env.All (LTy.WT C H) a
  | _, .nil, _, _ => trivial
  | _, .snoc as _ _ e, _, h => by
    obtain ⟨r, hr, h⟩ := bind_ok_inv h
    obtain ⟨v, hv, h⟩ := bind_ok_inv h
    cases h
    exact ⟨Val.eval_wt hwt e hv, Args.eval_wt hwt as hr⟩

end Eval

/-! ## The statements' effects are typed -/

section Effects

variable {Γ : Ctx} {H : HeapTy} {σ σ' : EState C Γ}

/-- `x ⊕= e` keeps the state typed: the target is resolved once, and the
number written back is of its type. -/
theorem OpLoc.store_wt (hwt : RunWT C H σ) {op : BinOp} (hop : op.isArith = true) :
    ∀ {p : PrimTy} (l : OpLoc C Γ p) {v : Value}, p.isNumeric = true →
      l.store σ op v = .ok σ' → RunWT C H σ'
  | p, .local i, v, hp, h => by
    obtain ⟨n₁, h₁, h⟩ := bind_ok_inv h
    obtain ⟨n₂, h₂, h⟩ := bind_ok_inv h
    cases h
    exact hwt.setLocal i (arith_new_wt hop hp h₁ h₂)
  | p, .root r hr, v, hp, h => by
    obtain ⟨τ, hτ, rfl⟩ := map_ok_inv h
    exact hwt.withGlob (.refl H) (opStore_wt hwt.glob hop hp (Contract.layout_tyAt_root hr) hτ)
  | p, .field b f hf, v, hp, h => by
    obtain ⟨⟨rt, segs⟩, hr, h⟩ := bind_ok_inv h
    obtain ⟨τ, hτ, rfl⟩ := map_ok_inv h
    exact hwt.withGlob (.refl H)
      (opStore_wt hwt.glob hop hp (Loc.resolve_wt hwt (.field b f hf) hr) hτ)
  | p, .index it b i, v, hp, h => by
    obtain ⟨⟨rt, segs⟩, hr, h⟩ := bind_ok_inv h
    obtain ⟨τ, hτ, rfl⟩ := map_ok_inv h
    exact hwt.withGlob (.refl H)
      (opStore_wt hwt.glob hop hp (Loc.resolve_wt hwt (.index it b (.simple i)) hr) hτ)
  | p, @OpLoc.mfield _ _ s _ b f hf, v, hp, h => by
    obtain ⟨m0, hm0, h⟩ := bind_ok_inv h
    obtain ⟨id, hid, h⟩ := bind_ok_inv h
    have hb := MPath.mval_wt hwt b hm0
    rw [MVal.asRef_ok hid, MVal.hasTyH_ref] at hb
    obtain ⟨τ, hτ, rfl⟩ := map_ok_inv h
    exact hwt.withGlob (.refl H)
      (opMem_wt hwt.glob hop hp (loc := .memoryField id f) ⟨s, hb, hf⟩ hτ)
  | p, .mindex ak b i, v, hp, h => by
    obtain ⟨m0, hm0, h⟩ := bind_ok_inv h
    obtain ⟨id, hid, h⟩ := bind_ok_inv h
    have hb := MPath.mval_wt hwt b hm0
    rw [MVal.asRef_ok hid, MVal.hasTyH_ref] at hb
    bind_inv h
    obtain ⟨iv, _, h⟩ := bind_ok_inv h
    obtain ⟨τ, hτ, rfl⟩ := map_ok_inv h
    exact hwt.withGlob (.refl H)
      (opMem_wt hwt.glob hop hp (loc := .memoryIndex id iv) ⟨_, hb, ak.arrElem⟩ hτ)

/-- `x++` keeps the state typed, and its value is of `x`'s type. -/
theorem OpLoc.bump_wt (hwt : RunWT C H σ) {op : IncDec} :
    ∀ {p : PrimTy} (l : OpLoc C Γ p) {w : Value}, p.isNumeric = true →
      l.bump σ op = .ok (σ', w) → RunWT C H σ' ∧ (Value.toSVal w).hasTy (.prim p) = true
  | p, .local i, w, hp, h => by
    obtain ⟨m, hm, h⟩ := bind_ok_inv h
    obtain ⟨n, hn, h⟩ := bind_ok_inv h
    cases h
    have hnew := bump_new_wt hp hn
    refine ⟨hwt.setLocal i hnew, ?_⟩
    split
    · exact hnew
    · rw [Value.asInt_ok hm]; exact int_toSVal_hasTy hp m
  | p, .root r hr, w, hp, h => by
    obtain ⟨⟨τ, v⟩, hτ, h⟩ := map_ok_inv h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    obtain ⟨hτ', hv⟩ := bumpStore_wt hwt.glob hp (Contract.layout_tyAt_root hr) hτ
    exact ⟨hwt.withGlob (.refl H) hτ', hv⟩
  | p, .field b f hf, w, hp, h => by
    obtain ⟨⟨rt, segs⟩, hr, h⟩ := bind_ok_inv h
    obtain ⟨⟨τ, v⟩, hτ, h⟩ := map_ok_inv h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    obtain ⟨hτ', hv⟩ := bumpStore_wt hwt.glob hp (Loc.resolve_wt hwt (.field b f hf) hr) hτ
    exact ⟨hwt.withGlob (.refl H) hτ', hv⟩
  | p, .index it b i, w, hp, h => by
    obtain ⟨⟨rt, segs⟩, hr, h⟩ := bind_ok_inv h
    obtain ⟨⟨τ, v⟩, hτ, h⟩ := map_ok_inv h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    obtain ⟨hτ', hv⟩ :=
      bumpStore_wt hwt.glob hp (Loc.resolve_wt hwt (.index it b (.simple i)) hr) hτ
    exact ⟨hwt.withGlob (.refl H) hτ', hv⟩
  | p, @OpLoc.mfield _ _ s _ b f hf, w, hp, h => by
    obtain ⟨m0, hm0, h⟩ := bind_ok_inv h
    obtain ⟨id, hid, h⟩ := bind_ok_inv h
    have hb := MPath.mval_wt hwt b hm0
    rw [MVal.asRef_ok hid, MVal.hasTyH_ref] at hb
    obtain ⟨⟨τ, v⟩, hτ, h⟩ := map_ok_inv h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    obtain ⟨hτ', hv⟩ := bumpMem_wt hwt.glob hp (loc := .memoryField id f) ⟨s, hb, hf⟩ hτ
    exact ⟨hwt.withGlob (.refl H) hτ', hv⟩
  | p, .mindex ak b i, w, hp, h => by
    obtain ⟨m0, hm0, h⟩ := bind_ok_inv h
    obtain ⟨id, hid, h⟩ := bind_ok_inv h
    have hb := MPath.mval_wt hwt b hm0
    rw [MVal.asRef_ok hid, MVal.hasTyH_ref] at hb
    bind_inv h
    obtain ⟨iv, _, h⟩ := bind_ok_inv h
    obtain ⟨⟨τ, v⟩, hτ, h⟩ := map_ok_inv h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    obtain ⟨hτ', hv⟩ := bumpMem_wt hwt.glob hp (loc := .memoryIndex id iv) ⟨_, hb, ak.arrElem⟩ hτ
    exact ⟨hwt.withGlob (.refl H) hτ', hv⟩

/-- `m.age = 3;` writes a slot of the member's type. -/
theorem MLoc.write_wt (hwt : RunWT C H σ) {mv : MVal} :
    ∀ {T : Ty} (l : MLoc C Γ T), MVal.hasTyH H mv T = true → l.write σ mv = .ok σ' →
      RunWT C H σ'
  | _, @MLoc.field _ _ s _ b f hf, hmv, h => by
    obtain ⟨m0, hm0, h⟩ := bind_ok_inv h
    obtain ⟨id, hid, h⟩ := bind_ok_inv h
    have hb := MPath.mval_wt hwt b hm0
    rw [MVal.asRef_ok hid, MVal.hasTyH_ref] at hb
    obtain ⟨τ, hτ, rfl⟩ := map_ok_inv h
    exact hwt.withGlob (.refl H) (memWriteField_wt hwt.glob hb hf hmv hτ)
  | _, .index ak b i, hmv, h => by
    obtain ⟨m0, hm0, h⟩ := bind_ok_inv h
    obtain ⟨id, hid, h⟩ := bind_ok_inv h
    have hb := MPath.mval_wt hwt b hm0
    rw [MVal.asRef_ok hid, MVal.hasTyH_ref] at hb
    bind_inv h
    obtain ⟨iv, _, h⟩ := bind_ok_inv h
    obtain ⟨τ, hτ, rfl⟩ := map_ok_inv h
    exact hwt.withGlob (.refl H) (memWriteIndex_wt hwt.glob hb ak.arrElem hmv hτ)

/-- `m = n;` and `m = alice;` name an object of `m`'s type: `n`'s, or a
fresh deep copy, which grows the store typing. -/
theorem MRhs.eval_wt (hwt : RunWT C H σ) {R : RefTy} {r : MRhs C Γ R} {σ₁ : EState C Γ}
    {id : Nat} (h : r.eval σ = .ok (σ₁, id)) :
    ∃ H', H.Extends H' ∧ RunWT C H' σ₁ ∧ MVal.hasTyH H' (.ref id) (.ref R) = true := by
  cases r with
  | alias p =>
    obtain ⟨m0, hm0, h⟩ := bind_ok_inv h
    obtain ⟨id', hid, h⟩ := bind_ok_inv h
    cases h
    have := MPath.mval_wt hwt p hm0
    rw [MVal.asRef_ok hid] at this
    exact ⟨H, .refl H, hwt, this⟩
  | copy p _ =>
    obtain ⟨⟨root, segs⟩, hr, h⟩ := bind_ok_inv h
    obtain ⟨sv, hsv, h⟩ := bind_ok_inv h
    obtain ⟨⟨τ, mv⟩, hcopy, h⟩ := bind_ok_inv h
    obtain ⟨id', hid, h⟩ := bind_ok_inv h
    cases h
    have hsvt := findStorage_hasTy hwt.glob.storage (SPath.resolve_wt hwt p hr) hsv
    obtain ⟨H', hout, hmv⟩ :=
      copyStToM_typed hwt.glob.heapTyNodup hwt.glob.heap hwt.glob.heapWf hsvt hcopy
    rw [MVal.asRef_ok hid] at hmv
    exact ⟨H', hout.ext, hwt.withGlob hout.ext (hwt.glob.ofCopyOut hout), hmv⟩
  | newArr n hn =>
    bind_inv h
    obtain ⟨nv, _, h⟩ := bind_ok_inv h
    obtain ⟨⟨τ, mv⟩, hcopy, h⟩ := bind_ok_inv h
    obtain ⟨id', hid, h⟩ := bind_ok_inv h
    cases h
    obtain ⟨H', hout, hmv⟩ := copyStToM_typed hwt.glob.heapTyNodup hwt.glob.heap
      hwt.glob.heapWf (newArrVal_hasTy hn nv) hcopy
    rw [MVal.asRef_ok hid] at hmv
    exact ⟨H', hout.ext, hwt.withGlob hout.ext (hwt.glob.ofCopyOut hout), hmv⟩

/-- `p = alice;` and `p = persons.push();` name a path the layout types at
`p`'s type. -/
theorem ARhs.eval_wt (hwt : RunWT C H σ) {R : RefTy} {r : ARhs C Γ R} {σ₁ : EState C Γ}
    {root : Name} {segs : List Seg} (h : r.eval σ = .ok (σ₁, (root, segs))) :
    RunWT C H σ₁ ∧ C.layout.tyAt root segs = some (.ref R) := by
  cases r with
  | path p =>
    obtain ⟨rs, hr, h⟩ := bind_ok_inv h
    cases h
    exact ⟨hwt, SPath.resolve_wt hwt p hr⟩
  | push b hd =>
    obtain ⟨⟨root', segs'⟩, hr, h⟩ := bind_ok_inv h
    obtain ⟨⟨τ, n⟩, hpush, h⟩ := bind_ok_inv h
    cases h
    have hty := SPath.resolve_wt hwt b hr
    exact ⟨hwt.withGlob (.refl H) (pushPlaceAt_wt hwt.glob hty (defaultOk_of_defaultOkS hd) hpush),
      tyAt_append_seg hty rfl⟩

/-- An alias bound by what `r` names is of `r`'s type. -/
theorem ARhs.alias_wt {R : RefTy} {root : Name} {segs : List Seg}
    (hty : C.layout.tyAt root segs = some (.ref R)) :
    LTy.WT C H (.alias R) (some (root, segs)) := by
  intro r s h
  cases h
  exact hty

/-- A decoded word is of its local's type. -/
theorem Value.fits_wt {v : Value} {p : PrimTy} (h : v.fits p = true) :
    (Value.toSVal v).hasTy (.prim p) = true := by
  cases p <;> cases v <;> simp_all [PrimVal.fits, Value.toSVal, SVal.hasTy]

/-- The locals an outcome of an external call binds, each a value of its
type: decoding checked it. -/
theorem Binders.decode_wt : {ρ : Ctx} → (bs : Binders ρ) → {vs : List Value} → {r : Env C ρ} →
    {rest : List Value} → bs.decode vs = .ok (r, rest) → Env.All (LTy.WT C H) r
  | _, .nil, _, _, _, _ => trivial
  | _, .snoc bs p x, vs, r, rest, h => by
    obtain ⟨⟨e, rest'⟩, he, h⟩ := bind_ok_inv h
    cases rest' with
    | nil => exact nomatch h
    | cons v rest'' =>
      by_cases hv : v.fits p = true
      · simp only [hv, ↓reduceIte] at h
        cases h
        exact ⟨Value.fits_wt hv, Binders.decode_wt bs he⟩
      · simp only [hv] at h
        exact nomatch h

/-- The `Panic` code a clause binds is a `uint`. -/
theorem CodeBinder.decode_wt {κ : Ctx} (code : CodeBinder κ) {c : Value} {r : Env C κ}
    (h : code.decode c = .ok r) : Env.All (LTy.WT C H) r := by
  cases code with
  | none => trivial
  | some x =>
    unfold CodeBinder.decode at h
    split at h
    · rename_i hc
      cases h
      exact ⟨Value.fits_wt hc, trivial⟩
    · exact nomatch h

/-- The return variables at their defaults are of their types. -/
theorem Binders.defaults_wt : {ρ : Ctx} → (bs : Binders ρ) →
    Env.All (LTy.WT C H) (Binders.defaults (C := C) bs)
  | _, .nil => trivial
  | _, .snoc bs p _ => ⟨LTy.WT.default p, Binders.defaults_wt bs⟩

/-- Entering a call: the return variables at their defaults, a memory
return a fresh default object, which grows the store typing. -/
theorem CallRet.enter_wt {rs Γ' : Ctx} (ret : CallRet Γ rs Γ') {τ τ' : Semantics.State}
    {r : Env C rs} (hτ : StateWT H C.layout τ) (h : ret.enter τ = .ok (τ', r)) :
    ∃ H', H.Extends H' ∧ StateWT H' C.layout τ' ∧ Env.All (LTy.WT C H') r := by
  cases ret with
  | none => cases h; exact ⟨H, .refl H, hτ, trivial⟩
  | val p x res => cases h; exact ⟨H, .refl H, hτ, LTy.WT.default p, trivial⟩
  | rets bs => cases h; exact ⟨H, .refl H, hτ, Binders.defaults_wt bs⟩
  | mem R x hd hm =>
    obtain ⟨⟨τ₁, id⟩, ha, h⟩ := bind_ok_inv h
    cases h
    obtain ⟨H', hout, hid⟩ := allocDefault_typed hτ.heapTyNodup hτ.heap hτ.heapWf
      (defaultOk_of_defaultOkS hd) ha
    exact ⟨H', hout.ext, hτ.ofCopyOut hout, LTy.WT.mem_some hid, trivial⟩

end Effects

/-! ## Where a run starts -/

/-- A contract starts well-typed: each root at its type's default, no
locals, an empty heap. -/
theorem RunWT.init {σ : EState C []} (hnd : nodupKeysB C.vars = true)
    (hok : C.vars.all (·.2.defaultOkS) = true) (hst : σ.storage = C.initStorage)
    (hheap : σ.heap = []) : RunWT C [] σ :=
  ⟨StateWT.init (σ := σ.glob) hnd hok hst hheap, trivial⟩

end Solidity
