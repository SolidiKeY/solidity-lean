import Solidity.Semantics.IntrinsicStorage.Preimages.Frames
import Solidity.Semantics.RunFuel

/-! Audited storage operations preserve actual results, including failures. -/
namespace Solidity.Semantics.IntrinsicStorage

open Solidity.Storage

structure Inputs where
  slots : List (List UInt8) := []
  ordinary : List (List UInt8) := []

namespace Inputs

def append (a b : Inputs) : Inputs := ⟨a.slots ++ b.slots, a.ordinary ++ b.ordinary⟩
def hashed (a : Inputs) : List (List UInt8) := a.slots ++ a.ordinary

theorem slot_hashed (a : Inputs) {b : List UInt8} (h : b ∈ a.slots) : b ∈ a.hashed :=
  List.mem_append_left _ h

end Inputs

structure Audit (α : Type) where
  result : TRes α
  inputs : Inputs := {}

namespace Audit

def pure (x : α) : Audit α := ⟨.ok x, {}⟩
def lift (x : TRes α) : Audit α := ⟨x, {}⟩
def bind (x : Audit α) (f : α → Audit β) : Audit β :=
  match x.result with
  | .error e => ⟨.error e, x.inputs⟩
  | .ok a => let y := f a; ⟨y.result, x.inputs.append y.inputs⟩
/-- Case analysis on a result retains the prefix, including a caught error. -/
def follow (x : Audit α) (f : TRes α → Audit β) : Audit β :=
  let y := f x.result
  ⟨y.result, x.inputs.append y.inputs⟩

@[simp] theorem result_follow (x : Audit α) (f : TRes α → Audit β) :
    (follow x f).result = (f x.result).result := rfl

theorem follow_slots (x : Audit α) (f : TRes α → Audit β) {b : List UInt8}
    (h : b ∈ x.inputs.slots) : b ∈ (follow x f).inputs.slots := List.mem_append_left _ h

def map (f : α → β) (x : Audit α) : Audit β := ⟨x.result.map f, x.inputs⟩

instance : Monad Audit where
  pure := pure
  bind := bind
  map := map

@[simp] theorem result_pure (a : α) :
    (Pure.pure a : Audit α).result = (Pure.pure a : TRes α) := rfl
@[simp] theorem result_lift (a : TRes α) : (lift a).result = a := rfl
@[simp] theorem result_bind (a : Audit α) (f : α → Audit β) :
    (a >>= f).result = a.result >>= fun x => (f x).result := by
  cases a with
  | mk result inputs => cases result <;> rfl
@[simp] theorem result_map (f : α → β) (a : Audit α) :
    (f <$> a).result = a.result.map f := rfl

@[simp] theorem result_map_direct (f : α → β) (a : Audit α) :
    (Audit.map f a).result = a.result.map f := rfl

theorem result_mapM (f : α → Audit β) (xs : List α) :
    (xs.mapM f).result = xs.mapM (fun x => (f x).result) := by
  have go : ∀ xs acc, (List.mapM.loop f xs acc).result =
      List.mapM.loop (fun x => (f x).result) xs acc := by
    intro xs
    induction xs with
    | nil => intro acc; rfl
    | cons x xs ih =>
      intro acc
      simp only [List.mapM.loop, result_bind, ih]
  exact go xs []

theorem failed_bind (a : Audit α) (f : α → Audit β) {e : THalt}
    (h : a.result = .error e) : (a >>= f).inputs = a.inputs := by
  change (bind a f).inputs = _
  simp only [bind, h]

theorem bind_slots_left (a : Audit α) (f : α → Audit β) {b : List UInt8}
    (h : b ∈ a.inputs.slots) : b ∈ (a >>= f).inputs.slots := by
  change b ∈ (bind a f).inputs.slots
  unfold bind
  cases a.result with
  | error e => exact h
  | ok x => exact List.mem_append_left _ h

theorem bind_slots_right (a : Audit α) (f : α → Audit β) {x : α}
    (hx : a.result = .ok x) {b : List UInt8} (h : b ∈ (f x).inputs.slots) :
    b ∈ (a >>= f).inputs.slots := by
  change b ∈ (bind a f).inputs.slots
  simp only [bind, hx, Inputs.append]
  exact List.mem_append_right _ h

noncomputable def atRef {C : Contract} {T : Ty} (r : SRef C T) (a : TRes α) : Audit α :=
  ⟨a, ⟨(ancestry (reference r)).map encoded, []⟩⟩

@[simp] theorem result_atRef {C : Contract} {T : Ty} (r : SRef C T) (a : TRes α) :
    (atRef r a).result = a := rfl

noncomputable def read {C : Contract} {T : Ty} (st : Solidity.Storage C) (r : SRef C T) :
    Audit (SVal T) :=
  ⟨TRes.ofOpt (st.find r), ⟨(ancestry (reference r)).map encoded ++
    (match st.find r with | none => [] | some v => valueInputs v (reference r)), []⟩⟩

@[simp] theorem result_read {C : Contract} {T : Ty} (st : Solidity.Storage C) (r : SRef C T) :
    (read st r).result = TRes.ofOpt (st.find r) := rfl

noncomputable def write {C : Contract} {T : Ty} (st : Solidity.Storage C) (r : SRef C T)
    (v : SVal T) : Audit (Solidity.Storage C) :=
  ⟨TRes.ofOpt (st.write r v), ⟨(ancestry (reference r)).map encoded ++
    valueInputs v (reference r) ++
    (match st.find r with | none => [] | some old => valueInputs old (reference r)), []⟩⟩

@[simp] theorem result_write {C : Contract} {T : Ty} (st : Solidity.Storage C)
    (r : SRef C T) (v : SVal T) : (write st r v).result = TRes.ofOpt (st.write r v) := rfl

/-- The data region is reached by a push, or by a nonempty pop. The choice
uses the actual pre-operation array, not the post-rollback world. -/
noncomputable def arrayOp {C : Contract} {E : Ty} (st : Solidity.Storage C)
    (r : SRef C (.ref (.array E))) (pop : Bool) (a : TRes α) : Audit α :=
  ⟨a, ⟨(ancestry (reference r)).map encoded ++
    (match st.find r with
    | none => []
    | some v => if pop && decide ((SVal.view v : ArrView E).n = 0) then []
      else valueInputs v (reference r) ++
        [encoded (.data ((reference r).word (2 ^ 256) keccakH))]), []⟩⟩

@[simp] theorem result_arrayOp {C : Contract} {E : Ty} (st : Solidity.Storage C)
    (r : SRef C (.ref (.array E))) (pop : Bool) (a : TRes α) :
    (arrayOp st r pop a).result = a := rfl

/-- Include the actual old destination, whose nested cells may be cleared. -/
noncomputable def touch {C : Contract} {T : Ty} (st : Solidity.Storage C)
    (r : SRef C T) (a : TRes α) : Audit α :=
  ⟨a, (read st r).inputs⟩

@[simp] theorem result_touch {C : Contract} {T : Ty} (st : Solidity.Storage C)
    (r : SRef C T) (a : TRes α) : (touch st r a).result = a := rfl

/-- A pushed aggregate is accounted at its new destination, not its source. -/
noncomputable def push {C : Contract} {E : Ty} (st : Solidity.Storage C)
    (r : SRef C (.ref (.array E))) (val : SVal E → Option (SVal E)) :
    Audit (Solidity.Storage C) :=
  let a := arrayOp st r false (TRes.ofOpt (st.push r val))
  ⟨a.result, ⟨a.inputs.slots ++ (match st.find r with
    | none => []
    | some v =>
      let w : ArrView E := SVal.view v
      match val (pushSlot E w.shadow.toList).1 with
      | none => []
      | some x => valueInputs x (.data (reference r) (w.n * size E))), []⟩⟩

@[simp] theorem result_push {C : Contract} {E : Ty} (st : Solidity.Storage C)
    (r : SRef C (.ref (.array E))) (val : SVal E → Option (SVal E)) :
    (push st r val).result = TRes.ofOpt (st.push r val) := rfl

noncomputable def place {C : Contract} {E : Ty} (st : Solidity.Storage C)
    (r : SRef C (.ref (.array E))) : Audit (Solidity.Storage C × PrimTy.uint.Denote) :=
  ⟨TRes.ofOpt (st.pushPlace r), (push st r some).inputs⟩

@[simp] theorem result_place {C : Contract} {E : Ty} (st : Solidity.Storage C)
    (r : SRef C (.ref (.array E))) : (place st r).result = TRes.ofOpt (st.pushPlace r) := rfl

theorem read_value {C : Contract} {T : Ty} (st : Solidity.Storage C) (r : SRef C T)
    {v : SVal T} (hv : st.find r = some v) {p : Pre}
    (hp : ValueInput v (reference r) p) : encoded p ∈ (read st r).inputs.slots := by
  simp only [read, hv]
  exact List.mem_append_right _ (valueInputs_covers v _ (reference_bounded r) hp)

theorem write_value {C : Contract} {T : Ty} (st : Solidity.Storage C) (r : SRef C T)
    (v : SVal T) {p : Pre} (hp : ValueInput v (reference r) p) :
    encoded p ∈ (write st r v).inputs.slots := by
  exact List.mem_append_left _ (List.mem_append_right _
    (valueInputs_covers v _ (reference_bounded r) hp))

theorem write_old {C : Contract} {T : Ty} (st : Solidity.Storage C) (r : SRef C T)
    (v : SVal T) {old : SVal T} (hv : st.find r = some old) {p : Pre}
    (hp : ValueInput old (reference r) p) : encoded p ∈ (write st r v).inputs.slots := by
  simp only [write, hv]
  exact List.mem_append_right _ (valueInputs_covers old _ (reference_bounded r) hp)

def hashing {C : Contract} {Γ : Ctx} {R : RefTy} (σ : State C Γ)
    (k : HashKind) (r : HRef σ.H R) : Audit PrimTy.uint.Denote :=
  ⟨.ok (σ.heap.hash k r), ⟨[], match k with
    | .keccak => [(MObj.words R (σ.heap.get r)).map (fun n => UInt8.ofNat n.toNat)]
    | _ => []⟩⟩

@[simp] theorem result_hashing {C : Contract} {Γ : Ctx} {R : RefTy} (σ : State C Γ)
    (k : HashKind) (r : HRef σ.H R) : (hashing σ k r).result = .ok (σ.heap.hash k r) := rfl

end Audit

end Solidity.Semantics.IntrinsicStorage
