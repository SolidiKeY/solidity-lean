import Solidity.Backend.Aggregates.ByteParameters
import Solidity.Source.CalldataCopyAccess

/-! G18.04/.05 bool-array value/frame consumers. Actual Source entry and
ordered validation derive the logical intrinsic allocation bound. Source
and target heaps/identities remain distinct. This is not an emitter, fetched
EVM simulation, or a producer of a general Source/runtime frame relation. -/
namespace Solidity.Backend.Aggregates.BoolArrays
open Solidity

abbrev boolR : RefTy := .array (.prim .bool)
abbrev sourceTy : Source.STy := .array .memory .bool none

/-- Extract the existing intrinsic Bool from an intrinsically typed Source
bool. Reference constructors at this type have contradictory locations. -/
def value {D : Source.Layout} : Source.Val D .bool → Bool
  | .bool b => b
  | .memRef impossible _ => nomatch impossible
  | .storRef impossible _ => nomatch impossible
  | .cdRef impossible _ _ => nomatch impossible

/-- Consume the real entry geometry through the published nested-region
law. The four selector bytes and array element stride are retained. -/
theorem entry_geometry (frame : Source.Fr) (selector data : Roadmap.Bytes)
    (selector_length : selector.length = 4) (input : frame.cd = selector ++ data)
    {index offset length : Nat} (entry : Source.cdTail data index 32 = .ok (offset,length)) :
    length < 2^64 ∧ offset+32*length ≤ frame.cd.length := by
  have dropped : frame.cd.drop 4 = data := by
    rw [input,← selector_length,List.drop_left]
  have nested : Source.cdNested frame 4 index 32 = .ok (offset,length) := by
    unfold Source.cdNested
    rw [dropped,entry]
    change (Except.ok (4+offset-4,length) : Source.R (Nat × Nat)) = _
    have shift : 4+offset-4 = offset := by omega
    rw [shift]
  obtain ⟨_,_,small,bounded⟩ := Source.cdNested_region frame 4 index 32 nested
  exact ⟨small,bounded⟩

/-- The target's real logical object capacity follows from BOTH actual ABI
entry and actual successful ordered validation; no capacity oracle. -/
theorem capacity {E : Source.Env} (frame : Source.Fr) (selector data : Roadmap.Bytes)
    (selector_length : selector.length = 4) (input : frame.cd = selector ++ data)
    {index offset length : Nat} (entry : Source.cdTail data index 32 = .ok (offset,length))
    {values : List (Source.Val E.layout .bool)}
    (validation : (List.range length).mapM (fun j =>
      Source.decodeWord E.layout (Source.cdWordAt frame (offset+32*j)) .bool) = .ok values) :
    (values.map value).length < 2^256 := by
  rw [List.length_map,Source.cdToMem_array_length frame .bool offset length validation]
  exact Nat.lt_trans (entry_geometry frame selector data selector_length input entry).1 (by decide)

def object {D : Source.Layout} (H : HTy) (values : List (Source.Val D .bool))
    (room : (values.map value).length < 2^256) : MObj H boolR := ⟨values.map value,room⟩

/-- Existing typed target allocation/frame extension at a real runtime
value, rather than a new untyped aggregate AST or a literal compiler. -/
def lower {D : Source.Layout} {C : Contract} {Γ : Ctx} (target : State C Γ)
    (values : List (Source.Val D .bool)) (room : (values.map value).length < 2^256) :
    State C (.mem boolR :: Γ) := target.allocPush (object target.H values room)

theorem target_contents {D : Source.Layout} {C : Contract} {Γ : Ctx} (target : State C Γ)
    (values : List (Source.Val D .bool)) (room : (values.map value).length < 2^256) :
    MObj.elems ArrTy.dyn ((lower target values room).heap.get
      (target.alloc (object target.H values room)).2) = values.map value := by
  unfold lower
  rw [State.allocPush_get]
  simp only [object,MObj.wk,MObj.elems_dyn,List.map_map]
  rfl

theorem target_old_heap {D : Source.Layout} {C : Contract} {Γ : Ctx} (target : State C Γ)
    (values : List (Source.Val D .bool)) (room : (values.map value).length < 2^256) :
    Heap.Keeps (List.prefix_append target.H [boolR]) target.heap (lower target values room).heap :=
  Heap.keeps_alloc target.heap _

theorem target_old_local {D : Source.Layout} {C : Contract} {Γ : Ctx} (target : State C Γ)
    (values : List (Source.Val D .bool)) (room : (values.map value).length < 2^256)
    {type : LTy} (index : Idx Γ type) :
    TEnv.get (.there index) (lower target values room).env =
      LTy.TDenote.wk (List.prefix_append target.H [boolR]) type (TEnv.get index target.env) :=
  TEnv.get_wk _ index target.env

theorem target_new_local {D : Source.Layout} {C : Contract} {Γ : Ctx} (target : State C Γ)
    (values : List (Source.Val D .bool)) (room : (values.map value).length < 2^256) :
    TEnv.get .here (lower target values room).env =
      some (target.alloc (object target.H values room)).2 := rfl

/-- Contents relation on the actual independent Source and intrinsic heaps.
Source physical ids are not identified with intrinsic HRef ids. -/
def Related {D : Source.Layout} (source : Source.Heap D) (address : Nat)
    {H : HTy} (target : Heap H) (reference : HRef H boolR) : Prop :=
  ∃ values : List (Source.Val D .bool),
    source.get address = some ⟨sourceTy,Source.Data.array values.length
      (fun _ h => nomatch h) (fun k => .val (values.get k))⟩ ∧
    MObj.elems ArrTy.dyn (target.get reference) = values.map value

theorem copy_related {E : Source.Env} {Λ : Source.RCtx} {C : Contract} {Γ : Ctx}
    (frame : Source.Fr) (selector data : Roadmap.Bytes)
    (selector_length : selector.length = 4) (input : frame.cd = selector ++ data)
    {index offset length : Nat} (entry : Source.cdTail data index 32 = .ok (offset,length))
    (source : Source.EMState E Λ) (target : State C Γ)
    {values : List (Source.Val E.layout .bool)}
    (validation : (List.range length).mapM (fun j =>
      Source.decodeWord E.layout (Source.cdWordAt frame (offset+32*j)) .bool) = .ok values) :
    let room := capacity frame selector data selector_length input entry validation
    Related ((Source.cdToMem frame sourceTy offset length).run source).2.2.heap source.2.heap.next
      (lower target values room).heap (target.alloc (object target.H values room)).2 := by
  dsimp only
  rw [(Source.cdToMem_array_run (σ := .bool)),validation]
  exact ⟨values,Source.Heap.alloc_get source.2.heap _,target_contents target values _⟩

/-- A total value/frame adapter OVER A SUCCESSFUL ABI ENTRY, using the actual Source word validator.
Its error channel is Source.Halt, NOT an EVM or intrinsic machine halt. -/
def lowerCopy {E : Source.Env} {C : Contract} {Γ : Ctx} (target : State C Γ)
    (frame : Source.Fr) (selector data : Roadmap.Bytes)
    (selector_length : selector.length = 4) (input : frame.cd = selector ++ data)
    {index offset length : Nat} (entry : Source.cdTail data index 32 = .ok (offset,length)) :
    Except Source.Halt (State C (.mem boolR :: Γ)) :=
  match validation : (List.range length).mapM (fun j =>
    Source.decodeWord E.layout (Source.cdWordAt frame (offset+32*j)) .bool) with
  | .error halt => .error halt
  | .ok values => .ok (lower target values
      (capacity frame selector data selector_length input entry validation))

theorem lowerCopy_success {E : Source.Env} {C : Contract} {Γ : Ctx} (target : State C Γ)
    (frame : Source.Fr) (selector data : Roadmap.Bytes)
    (selector_length : selector.length = 4) (input : frame.cd = selector ++ data)
    {index offset length : Nat} (entry : Source.cdTail data index 32 = .ok (offset,length))
    {values : List (Source.Val E.layout .bool)}
    (validation : (List.range length).mapM (fun j =>
      Source.decodeWord E.layout (Source.cdWordAt frame (offset+32*j)) .bool) = .ok values) :
    lowerCopy (E := E) target frame selector data selector_length input entry =
      .ok (lower target values (capacity frame selector data selector_length input entry validation)) := by
  unfold lowerCopy
  split
  · rename_i _ observed
    rw [validation] at observed
    cases observed
  · rename_i _ observed
    rw [validation] at observed
    cases observed
    rfl

theorem lowerCopy_failure {E : Source.Env} {C : Contract} {Γ : Ctx} (target : State C Γ)
    (frame : Source.Fr) (selector data : Roadmap.Bytes)
    (selector_length : selector.length = 4) (input : frame.cd = selector ++ data)
    {index offset length : Nat} (entry : Source.cdTail data index 32 = .ok (offset,length)) (halt : Source.Halt)
    (validation : (List.range length).mapM (fun j =>
      Source.decodeWord E.layout (Source.cdWordAt frame (offset+32*j)) .bool) = .error halt) :
    lowerCopy (E := E) target frame selector data selector_length input entry = .error halt := by
  unfold lowerCopy
  split
  · rename_i _ observed
    rw [validation] at observed
    cases observed
    rfl
  · rename_i _ observed
    rw [validation] at observed
    cases observed

/-- Actual Source copy/index and actual intrinsic Heap.readAddr agree on
bool values. Both the array capacity and exact uint index (no truncation)
are derived from the real entry and validation, with no desired run premise. -/
theorem copy_read_related {E : Source.Env} {Λ : Source.RCtx} {C : Contract} {Γ : Ctx}
    (frame : Source.Fr) (selector data : Roadmap.Bytes)
    (selector_length : selector.length = 4) (input : frame.cd = selector ++ data)
    {entryIndex offset length : Nat} (entry : Source.cdTail data entryIndex 32 = .ok (offset,length))
    (source : Source.EMState E Λ) (target : State C Γ)
    {values : List (Source.Val E.layout .bool)}
    (validation : (List.range length).mapM (fun j =>
      Source.decodeWord E.layout (Source.cdWordAt frame (offset+32*j)) .bool) = .ok values)
    (index : Fin length) :
    let room := capacity frame selector data selector_length input entry validation
    ∃ bound : index.val < values.length,
      ((do let _ ← Source.cdToMem frame sourceTy offset length
           Source.readLoc frame (.mem (τ := .bool) source.2.heap.next index.val)) : Source.EM E Λ _).run source =
        (.ok (values.get ⟨index.val,bound⟩),((Source.cdToMem frame sourceTy offset length).run source).2) ∧
      (lower target values room).heap.readAddr
        (.index (target.alloc (object target.H values room)).2 ArrTy.dyn (uintOfNat index.val)) =
          some (value (values.get ⟨index.val,bound⟩)) := by
  dsimp only
  obtain ⟨bound,_,_,actual⟩ := Source.cdToMem_array_read_run frame .bool offset length source validation index
  refine ⟨bound,actual,?_⟩
  have small : index.val < 2^256 := Nat.lt_trans
    (Nat.lt_trans index.isLt (entry_geometry frame selector data selector_length input entry).1) (by decide)
  simp only [Heap.readAddr,Heap.index,target_contents,uintOfNat_val small,Int.toNat_natCast,
    List.getElem?_map,List.getElem?_eq_getElem bound,Option.map_some,List.get_eq_getElem]

/-- Exact phase-error reflection against the actual Source copy, including
its full original caller state. This concerns the adapter's Source.Halt
channel; it is not a theorem about machine revert or physical exhaustion. -/
theorem phase_error_iff_copy_error {E : Source.Env} {Λ : Source.RCtx} {C : Contract} {Γ : Ctx}
    (source : Source.EMState E Λ) (target : State C Γ)
    (frame : Source.Fr) (selector data : Roadmap.Bytes)
    (selector_length : selector.length = 4) (input : frame.cd = selector ++ data)
    {index offset length : Nat} (entry : Source.cdTail data index 32 = .ok (offset,length)) (halt : Source.Halt) :
    lowerCopy (E := E) target frame selector data selector_length input entry = .error halt ↔
      (Source.cdToMem frame sourceTy offset length).run source = (.error halt,source) := by
  cases validation : (List.range length).mapM (fun j =>
    Source.decodeWord E.layout (Source.cdWordAt frame (offset+32*j)) .bool) with
  | error actual =>
    rw [lowerCopy_failure target frame selector data selector_length input entry actual validation,
      Source.cdToMem_array_failure frame .bool offset length source actual validation]
    constructor
    · intro same
      cases same
      rfl
    · intro same
      have equality := Except.error.inj (congrArg Prod.fst same)
      cases equality
      rfl
  | ok values =>
    rw [lowerCopy_success target frame selector data selector_length input entry validation]
    constructor
    · intro impossible
      cases impossible
    · intro impossible
      rw [(Source.cdToMem_array_run (σ := .bool)),validation] at impossible
      cases congrArg Prod.fst impossible

end Solidity.Backend.Aggregates.BoolArrays
