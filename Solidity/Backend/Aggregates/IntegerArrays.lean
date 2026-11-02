import Solidity.Backend.Aggregates.BoolArrays
import Solidity.Lowering.V07.Scalar
/-! G18.04/.05 arbitrary-width integer calldata-array value/frame consumer.
Development prerequisite: exact V07 Scalar checkpoint5d45c086, validated in a
private source-keyed stage. No admission, general frame/compiler, machine gas,
or fetched-EVM correspondence follows. Source widths remain in Source values;
the target uses V07's actual signed/unsigned intrinsic primitive. -/
namespace Solidity.Backend.Aggregates.IntegerArrays
open Solidity Lowering.V07
abbrev runtimeTy (t : Source.IntTy) : RefTy := .array (.prim (integerPrim t))
abbrev sourceTy (t : Source.IntTy) : Source.STy := .array .memory (.int t) none

def value {D : Source.Layout} (t : Source.IntTy) : Source.Val D (.int t) → (integerPrim t).Denote
  | .int n h => integerValue t n h
  | .memRef impossible _ => nomatch impossible
  | .storRef impossible _ => nomatch impossible
  | .cdRef impossible _ _ => nomatch impossible

theorem value_related {D : Source.Layout} (t : Source.IntTy) (v : Source.Val D (.int t)) :
    IntValueRel t v (value t v) := by
  cases v with
  | int n h => exact integer_related t n h
  | memRef impossible _ => nomatch impossible
  | storRef impossible _ => nomatch impossible
  | cdRef impossible _ _ => nomatch impossible

/-- Real ABI region and ordered validation derive target object capacity. -/
theorem capacity {E : Source.Env} (t : Source.IntTy) (frame : Source.Fr)
    (selector data : Roadmap.Bytes) (selector_length : selector.length = 4)
    (input : frame.cd = selector ++ data) {index offset length : Nat}
    (entry : Source.cdTail data index 32 = .ok (offset,length))
    {values : List (Source.Val E.layout (.int t))}
    (validation : (List.range length).mapM (fun j => Source.decodeWord E.layout
      (Source.cdWordAt frame (offset+32*j)) (.int t)) = .ok values) :
    (values.map (value t)).length < 2^256 := by
  rw [List.length_map, Source.cdToMem_array_length frame (.int t) offset length validation]
  exact Nat.lt_trans (BoolArrays.entry_geometry frame selector data selector_length input entry).1 (by decide)

def object {D : Source.Layout} (H : HTy) (t : Source.IntTy)
    (values : List (Source.Val D (.int t)))
    (room : (values.map (value t)).length < 2^256) : MObj H (runtimeTy t) :=
  ⟨values.map (value t),room⟩

def lower {D : Source.Layout} {C : Contract} {Γ : Ctx} (target : State C Γ)
    (t : Source.IntTy) (values : List (Source.Val D (.int t)))
    (room : (values.map (value t)).length < 2^256) : State C (.mem (runtimeTy t) :: Γ) :=
  target.allocPush (object target.H t values room)

def Related {D : Source.Layout} (t : Source.IntTy) (source : Source.Heap D) (address : Nat)
    {H : HTy} (target : Heap H) (reference : HRef H (runtimeTy t)) : Prop :=
  ∃ values : List (Source.Val D (.int t)),
    source.get address = some ⟨sourceTy t, Source.Data.array values.length
      (fun _ h => nomatch h) (fun k => .val (values.get k))⟩ ∧
    MObj.elems ArrTy.dyn (target.get reference) = values.map (value t)

/-- Actual Source copy and intrinsic allocation have the same ordered values,
using V07 integer transport, with independent fresh identities. Entry and
validation are actual operation equations, not a simulation premise. -/
theorem copy_related {E : Source.Env} {Λ : Source.RCtx} {C : Contract} {Γ : Ctx}
    (t : Source.IntTy) (frame : Source.Fr) (selector data : Roadmap.Bytes)
    (selector_length : selector.length = 4) (input : frame.cd = selector ++ data)
    {index offset length : Nat} (entry : Source.cdTail data index 32 = .ok (offset,length))
    (source : Source.EMState E Λ) (target : State C Γ)
    {values : List (Source.Val E.layout (.int t))}
    (validation : (List.range length).mapM (fun j => Source.decodeWord E.layout
      (Source.cdWordAt frame (offset+32*j)) (.int t)) = .ok values) :
    let room := capacity t frame selector data selector_length input entry validation
    Related t ((Source.cdToMem frame (sourceTy t) offset length).run source).2.2.heap
      source.2.heap.next (lower target t values room).heap
      (target.alloc (object target.H t values room)).2 := by

  dsimp only
  rw [Source.cdToMem_array_run, validation]
  refine ⟨values, Source.Heap.alloc_get source.2.heap _, ?_⟩
  change MObj.elems ArrTy.dyn ((target.heap.alloc (object target.H t values (capacity t frame selector data selector_length input entry validation))).1.get
    (target.heap.alloc (object target.H t values (capacity t frame selector data selector_length input entry validation))).2) = values.map (value t)
  rw [Heap.get_alloc_self]
  simp only [object, MObj.wk, MObj.elems_dyn, List.map_map]
  rfl


/-- Total validation adapter over an actual successful ABI entry. Errors are
Source.Halt diagnostics; this is not machine execution or a gas model. -/
def lowerCopy {E : Source.Env} {C : Contract} {Γ : Ctx} (target : State C Γ)
    (t : Source.IntTy) (frame : Source.Fr) (selector data : Roadmap.Bytes)
    (selector_length : selector.length = 4) (input : frame.cd = selector ++ data)
    {index offset length : Nat} (entry : Source.cdTail data index 32 = .ok (offset,length)) :
    Except Source.Halt (State C (.mem (runtimeTy t) :: Γ)) :=
  match validation : (List.range length).mapM (fun j => Source.decodeWord E.layout
      (Source.cdWordAt frame (offset+32*j)) (.int t)) with
  | .error halt => .error halt
  | .ok values => .ok (lower target t values
      (capacity t frame selector data selector_length input entry validation))

/-- Reflect exact Source diagnostics in both directions, retaining the unchanged
full original state on validation failure.
ABI entry is certified; no target halt/resource/world claim is made. -/
theorem error_iff_copy_error {E : Source.Env} {Λ : Source.RCtx} {C : Contract} {Γ : Ctx}
    (source : Source.EMState E Λ) (target : State C Γ) (t : Source.IntTy)
    (frame : Source.Fr) (selector data : Roadmap.Bytes)
    (selector_length : selector.length = 4) (input : frame.cd = selector ++ data)
    {index offset length : Nat} (entry : Source.cdTail data index 32 = .ok (offset,length))
    (halt : Source.Halt) :
    lowerCopy (E := E) target t frame selector data selector_length input entry = .error halt ↔
      (Source.cdToMem frame (sourceTy t) offset length).run source = (.error halt,source) := by

  rw [Source.cdToMem_array_run]
  unfold lowerCopy
  split
  · rename_i actual observed
    rw [observed]
    constructor
    · intro same
      cases same
      rfl
    · intro same
      have equality := Except.error.inj (congrArg Prod.fst same)
      cases equality
      rfl
  · rename_i values observed
    constructor
    · intro impossible
      cases impossible
    · intro impossible
      have wrong := congrArg Prod.fst impossible
      rw [observed] at wrong
      cases wrong
end Solidity.Backend.Aggregates.IntegerArrays
