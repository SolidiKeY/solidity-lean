import Solidity.Update
import Solidity.Semantics.Properties
import Solidity.Semantics.NoPanicOps

/-!
# The interpreter's writes, reshaped

Lemmas that put the interpreter's state operations into the shape a rule's
soundness proof or the closer reads them in: a write as a new storage or heap
with the rest of the state kept (`State.writeStorage_eq`, `writeAddr_eq`,
`copyStToM_eq`, `allocDefault_eq`), a write that keeps only its own
component (`State.saveStorage_with`, `pushAt_with`, `popAt_with`), an
operator's evaluation unfolded (`evalBinop_compound`, `evalBinop_bump`),
and what a binding holds (`Close.bindingVal`, …).  Today's taclet soundness
(`Calculus/SoundKit.lean`, `Calculus/SoundArms.lean`), the scoped one
(`Calculus/SoundArms.lean`) and the closer (`Calculus/NFmlClose.lean`,
`Calculus/Decide.lean`) share them.  Moved out of `SoundKit.lean` and
`Calculus/SoundArms.lean` (`docs/intrinsic.md`, W4 item 11).
-/

namespace Solidity

open Semantics SemanticsProperties

variable {C : Contract}

/-! ### A local's write leaves the state's other parts -/

section
variable {σ : State} {x : Var} {b : Binding}

@[simp] theorem Semantics.State.findStorage_setEnv (r : Name) (segs : List Seg) :
    (σ.setEnv x b).findStorage r segs = σ.findStorage r segs := rfl
@[simp] theorem Semantics.State.checkIndex_setEnv (r : Name) (segs : List Seg) (i : Int) :
    (σ.setEnv x b).checkIndex r segs i = σ.checkIndex r segs i := rfl
@[simp] theorem Semantics.State.getObj_setEnv (id : Nat) : (σ.setEnv x b).getObj id = σ.getObj id := rfl
@[simp] theorem arrayLen_setEnv (r : Name) (segs : List Seg) :
    arrayLen (σ.setEnv x b) r segs = arrayLen σ r segs := rfl
@[simp] theorem memArrayLen_setEnv (id : Nat) : memArrayLen (σ.setEnv x b) id = memArrayLen σ id := rfl

end

/-! ### Writes as a new storage or heap, the rest of the state kept -/

/-- The storage a successful `writeStorage` leaves: a word saved, or a copy
over what is there. -/
def Semantics.State.writeRes (σ : State) (r : Name) (segs : List Seg) (x : SVal) :
    Res (List (Name × SVal)) :=
  match x with
  | .prim p => σ.storeRes r segs (.prim p)
  | .struct _ | .array .. | .map .. => do
    let cur ← σ.findStorage r segs
    σ.storeRes r segs (cur.overlay x)

@[simp] theorem Semantics.State.writeRes_toSVal (σ : State) (r segs) (v : Value) :
    σ.writeRes r segs v.toSVal = σ.storeRes r segs v.toSVal := by
  cases v <;> rfl

theorem Semantics.State.writeStorage_eq (σ : State) (r segs x) :
    σ.writeStorage r segs x = (do let s ← σ.writeRes r segs x; pure { σ with storage := s }) := by
  unfold State.writeStorage State.writeRes
  cases x <;> simp only [State.saveStorage_eq, bind_assoc]

/-- The heap a successful `writeAddr` leaves. -/
def heapRes (σ : State) (mv : MVal) : Addr → Res (List (Nat × MObj))
  | .memoryField id f => do
    match ← σ.getObj id with
    | .struct fields => pure (setBy id (.struct (setBy f mv fields)) σ.heap)
    | .array _ _ => .error .undef
  | .memoryIndex id i => do
    match ← σ.getObj id with
    | .array elems fx =>
      if 0 ≤ i ∧ i.toNat < elems.length then pure (setBy id (.array (elems.set i.toNat mv) fx) σ.heap)
      else .error .revert
    | .struct _ => .error .undef

theorem writeAddr_eq (σ : State) (mv : MVal) (a : Addr) :
    writeAddr σ mv a = (do let h ← heapRes σ mv a; pure { σ with heap := h }) := by
  cases a with
  | memoryField id f =>
    simp only [writeAddr, heapRes, memWriteField, bind, Except.bind]
    cases σ.getObj id with
    | error _ => rfl
    | ok o => cases o <;> rfl
  | memoryIndex id i =>
    simp only [writeAddr, heapRes, memWriteIndex, bind, Except.bind]
    cases σ.getObj id with
    | error _ => rfl
    | ok o =>
      cases o with
      | struct _ => rfl
      | array elems => by_cases hh : 0 ≤ i ∧ i.toNat < elems.length <;> simp [hh] <;> rfl

theorem Semantics.State.saveStorage_with (σ : State) (r segs v) :
    (σ.saveStorage r segs v >>= fun τ => pure { σ with storage := τ.storage }) =
      σ.saveStorage r segs v := by
  rw [State.saveStorage_eq]; cases σ.storeRes r segs v <;> rfl

theorem Semantics.State.writeStorage_with (σ : State) (r segs v) :
    (σ.writeStorage r segs v >>= fun τ => pure { σ with storage := τ.storage }) =
      σ.writeStorage r segs v := by
  rw [State.writeStorage_eq]; cases σ.writeRes r segs v <;> rfl

theorem writeAddr_with (σ : State) (mv : MVal) (a : Addr) :
    (writeAddr σ mv a >>= fun μ => pure { σ with heap := μ.heap, nextId := μ.nextId }) =
      writeAddr σ mv a := by
  rw [writeAddr_eq]; cases heapRes σ mv a <;> rfl

theorem evalBinop_compound {op : BinOp} (hop : op.hasCompoundAssign = true) (p : PrimTy) (lv : Value)
    (b : Res Value) : evalBinop op p lv b = (do checkArith (.prim p) (← applyBinOp op lv (← b))) := by
  cases op <;> simp [BinOp.hasCompoundAssign] at hop <;> rfl

theorem evalBinop_bump (op : IncDec) (p : PrimTy) (lv : Value) (b : Res Value) :
    evalBinop op.binOp p lv b = (do
      checkArith (.prim p) (← applyBinOp op.binOp lv (← b))) := by
  cases op <;> rfl

theorem applyBinOp_bump (op : IncDec) (lv : Value) :
    applyBinOp op.binOp lv (.int 1) =
      (do let n ← lv.asInt; pure (.int (if op.isIncrement then n + 1 else n - 1))) := by
  cases op <;> cases lv <;> rfl

/-! ### What a binding holds

The update and the statement read the same things through differently shaped
code; these name the reads, so both sides split on the same atoms. -/

namespace Close

/-- The value a local holds: `x` after `uint x = 10;` is `10`; an alias or
a memory local has none. -/
def bindingVal : Binding → Res Value
  | .val v => .ok v
  | .spath .. | .mref _ | .store _ | .ledger _ | .unset => .error .undef

/-- The path an alias holds: `p` after `Person storage p = alice;` is
`alice`. -/
def bindingPath : Binding → Res (Name × List Seg)
  | .spath r segs => .ok (r, segs)
  | .unset => .error .revert
  | .val _ | .mref _ | .store _ | .ledger _ => .error .undef

/-- The object a memory local holds: `m` after `Person memory m;`; an unset
one reverts, as `MPath.mval` does. -/
def bindingRef : Binding → Res Nat
  | .mref id => .ok id
  | .unset => .error .revert
  | .val _ | .spath .. | .store _ | .ledger _ => .error .undef

/-- The storage a storage variable holds: `old` after `{old := storage}`. -/
def bindingStore : Binding → Res (List (Name × SVal))
  | .store st => .ok st
  | .val _ | .spath .. | .mref _ | .ledger _ | .unset => .error .undef

/-- The ledger a ledger variable holds: `oldNet` after `{oldNet := net}`. -/
def bindingLedger : Binding → Res (List (Int × Int))
  | .ledger l => .ok l
  | .val _ | .spath .. | .mref _ | .store _ | .unset => .error .undef

end Close

/-! ### A memory location read and written -/

@[simp] theorem readLoc_eq (σ : State) (a : Addr) : readLoc σ a = (do (← readAddr σ a).asValue) := by
  cases a with
  | memoryField id f =>
    simp only [readLoc, readAddr, bind, Except.bind, pure, Except.pure]
    repeat' split
    all_goals simp_all
  | memoryIndex id i =>
    simp only [readLoc, readAddr, bind, Except.bind, pure, Except.pure]
    cases σ.getObj id with
    | error _ => rfl
    | ok o =>
      cases o with
      | struct _ => rfl
      | array elems => by_cases hh : 0 ≤ i ∧ i.toNat < elems.length <;> simp [hh]

@[simp] theorem Semantics.writeLoc_eq (σ : State) (a : Addr) (v : Value) :
    writeLoc σ a v = writeAddr σ v.toMVal a := by
  cases a <;> rfl

/-! ### Copies and allocations: a new heap and counter, the rest kept -/

theorem res_frame_eq {α : Type} {σ : State} {x : Res (State × α)} (hx : FramePreserving σ x) :
    x = ((x.map fun p => (p.1.heap, p.1.nextId, p.2)) >>= fun q =>
      pure ({ σ with heap := q.1, nextId := q.2.1 }, q.2.2)) := by
  cases h : x with
  | error _ => rfl
  | ok p =>
    obtain ⟨τ, a⟩ := p
    obtain ⟨h1, h2, h3, h4, h5⟩ := hx τ a h
    cases τ; cases σ
    simp_all [Except.map, bind, Except.bind, pure, Except.pure]

/-- What a copy into memory leaves: the heap, the counter, the value. -/
def copyHN (σ : State) (sv : SVal) : Res (List (Nat × MObj) × Nat × MVal) :=
  (copyStToM σ sv).map fun p => (p.1.heap, p.1.nextId, p.2)

theorem copyStToM_eq (σ : State) (sv : SVal) :
    copyStToM σ sv = (copyHN σ sv >>= fun q => pure ({ σ with heap := q.1, nextId := q.2.1 }, q.2.2)) :=
  res_frame_eq (SemanticsProperties.copyStToM_frame σ sv)

theorem allocDefault_frame (σ : State) (R : RefTy) : FramePreserving σ (allocDefault σ R) := by
  intro t a h
  unfold allocDefault at h
  have hf := copyStToM_frame σ (defaultForRef R)
  split at h
  · rename_i s id heq
    cases h
    exact hf _ _ heq
  · cases h
  · cases h

/-- What a default allocation leaves: the heap, the counter, the identity. -/
def allocHN (σ : State) (R : RefTy) : Res (List (Nat × MObj) × Nat × Nat) :=
  (allocDefault σ R).map fun p => (p.1.heap, p.1.nextId, p.2)

@[no_panic_simp] theorem allocHN_noPanic (σ : State) (R : RefTy) : NoPanic (allocHN σ R) := by
  simp only [allocHN]
  cases h : allocDefault σ R with
  | error e =>
    exact fun hp => NoPanic.ne_of_eq (allocDefault_noPanic σ R) h (Except.error.inj hp)
  | ok _ => simp only [Except.map, ne_eq, reduceCtorEq, not_false_eq_true]

theorem allocDefault_eq (σ : State) (R : RefTy) :
    allocDefault σ R = (allocHN σ R >>= fun q => pure ({ σ with heap := q.1, nextId := q.2.1 }, q.2.2)) :=
  res_frame_eq (allocDefault_frame σ R)

theorem pushAt_const (σ : State) (E E' : Ty) (r : Name) (segs : List Seg) (f : Res SVal) :
    pushAt σ E r segs (fun _ => f) = pushAt σ E' r segs (fun _ => f) := by
  unfold pushAt
  cases σ.findStorage r segs with
  | error _ => rfl
  | ok v =>
    cases v with
    | array elems shadow => cases shadow <;> rfl
    | _ => rfl

theorem pushAt_with (σ : State) (E : Ty) (r : Name) (segs : List Seg) (f : SVal → Res SVal) :
    (pushAt σ E r segs f >>= fun τ => pure { σ with storage := τ.storage }) = pushAt σ E r segs f := by
  unfold pushAt
  simp only [bind, Except.bind]
  cases σ.findStorage r segs with
  | error _ => rfl
  | ok v =>
    cases v with
    | array elems shadow =>
      simp only
      cases f (pushSlot E shadow).1 with
      | error _ => rfl
      | ok w => exact State.saveStorage_with σ r segs _
    | _ => rfl

theorem popAt_with (σ : State) (keep : Bool) (r : Name) (segs : List Seg) :
    (popAt σ keep r segs >>= fun τ => pure { σ with storage := τ.storage }) =
      popAt σ keep r segs := by
  unfold popAt
  simp only [bind, Except.bind]
  cases σ.findStorage r segs with
  | error _ => rfl
  | ok v =>
    cases v with
    | array elems shadow =>
      simp only
      cases elems.reverse with
      | nil => rfl
      | cons last rest => exact State.saveStorage_with σ r segs _
    | _ => rfl

/-! ### An update keeps the locals it does not write -/

end Solidity
