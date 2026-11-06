import Solidity.Source.Eval
import Solidity.Semantics.AllocBytes
import Solidity.Theory.Typed.Mem

/-! G18.04/.05 groundwork: a specification-level pairing of Source `cdArg`/`cdToMem`
for a `bytes`/`string` parameter with a typed target state that allocates the
payload bytes object. No target program or lowering run is related, and it is
not a literal emitter, decoder, source evaluator or fetched-EVM theorem.
`Related` is a single-object contents relation; `copy_related` holds for any
offset/length (it does not use the entry check). -/
namespace Solidity.Backend.Aggregates.ByteParameters
open Solidity

/-- The Source byte/string region read by cdToMem. -/
def payload (frame : Source.Fr) (offset length : Nat) : List UInt8 :=
  (frame.cd.drop offset).take length

theorem entry_length {data : Roadmap.Bytes} {index offset length : Nat}
    (entry : Source.cdTail data index 1 = .ok (offset,length)) : length < 2^64 := by
  unfold Source.cdTail at entry
  dsimp only at entry
  split at entry
  · cases entry
  · split at entry
    · cases entry
    · rename_i small
      split at entry
      · cases entry
        exact Nat.lt_of_not_ge small
      · cases entry

theorem payload_length (frame : Source.Fr) (offset length : Nat) :
    (payload frame offset length).length ≤ length := by
  exact List.length_take_le _ _

/-- Capacity is derived from the successful published entry check. -/
theorem entry_capacity (frame : Source.Fr) {data : Roadmap.Bytes} {index offset length : Nat}
    (entry : Source.cdTail data index 1 = .ok (offset,length)) :
    (payload frame offset length).length < 2^256 :=
  Nat.lt_trans (Nat.lt_of_le_of_lt (payload_length frame offset length) (entry_length entry))
    (by decide)

theorem entry_region {data : Roadmap.Bytes} {index offset length : Nat}
    (entry : Source.cdTail data index 1 = .ok (offset,length)) :
    ∃ relative, offset = 4+relative+32 ∧ relative+32+length ≤ data.length := by
  unfold Source.cdTail at entry
  dsimp only at entry
  split at entry
  · cases entry
  · split at entry
    · cases entry
    · split at entry
      · rename_i bounded
        cases entry
        exact ⟨_,rfl,by simpa only [Nat.one_mul] using bounded⟩
      · cases entry

theorem entry_payload_exact (frame : Source.Fr) (selector data : Roadmap.Bytes)
    (selector_length : selector.length = 4) (input : frame.cd = selector ++ data)
    {index offset length : Nat} (entry : Source.cdTail data index 1 = .ok (offset,length)) :
    (payload frame offset length).length = length := by
  obtain ⟨relative,position,bounded⟩ := entry_region entry
  have size : offset+length ≤ frame.cd.length := by
    rw [input,List.length_append,selector_length,position]
    omega
  simp only [payload,List.length_take,List.length_drop]
  omega

/-- Runtime value lowering; no source/target run is assumed. -/
def lower {C : Contract} {Γ : Ctx} (target : State C Γ) (frame : Source.Fr)
    (offset length : Nat) (capacity : (payload frame offset length).length < 2^256) :
    State C (.mem bytesR :: Γ) :=
  target.allocPush (bytesObj target.H (payload frame offset length) capacity)

theorem source_copy {E : Source.Env} {Γ : Source.RCtx} (frame : Source.Fr)
    (offset length : Nat) (before : Source.Locals E.layout Γ × Source.St E) :
    (Source.cdToMem frame (.bytes .memory) offset length).run before =
      (.ok (.val (.memRef rfl before.2.heap.next)),
        (before.1,{before.2 with heap :=
          (before.2.heap.alloc ⟨.bytes .memory,.bytes (payload frame offset length)⟩).1})) := rfl

theorem target_identity {C : Contract} {Γ : Ctx} (target : State C Γ) (frame : Source.Fr)
    (offset length : Nat) (capacity : (payload frame offset length).length < 2^256) :
    (target.alloc (bytesObj target.H (payload frame offset length) capacity)).2.id = target.H.length := rfl

theorem target_contents {C : Contract} {Γ : Ctx} (target : State C Γ) (frame : Source.Fr)
    (offset length : Nat) (capacity : (payload frame offset length).length < 2^256) :
    MObj.elems ArrTy.dyn ((lower target frame offset length capacity).heap.get
      (target.alloc (bytesObj target.H (payload frame offset length) capacity)).2) =
        (payload frame offset length).map byteWord := by
  unfold lower
  rw [State.allocPush_get]
  simp only [bytesObj,wordsObj,MObj.wk,MObj.elems_dyn,List.map_map]
  rfl

theorem target_old_heap {C : Contract} {Γ : Ctx} (target : State C Γ) (frame : Source.Fr)
    (offset length : Nat) (capacity : (payload frame offset length).length < 2^256) :
    Heap.Keeps (List.prefix_append target.H [bytesR]) target.heap
      (lower target frame offset length capacity).heap :=
  Heap.keeps_alloc target.heap _

/-- A single-object contents relation between the two distinct heaps, not a
second copy semantics or a desired execution premise. -/
def Related {D : Source.Layout} (source : Source.Heap D) (address : Nat)
    {H : HTy} (target : Heap H) (reference : HRef H bytesR) : Prop :=
  ∃ bytes : List UInt8, source.get address = some ⟨.bytes .memory,.bytes bytes⟩ ∧
    MObj.elems ArrTy.dyn (target.get reference) = bytes.map byteWord

theorem copy_related {E : Source.Env} {Λ : Source.RCtx} {C : Contract} {Γ : Ctx}
    (frame : Source.Fr) (offset length : Nat)
    (source : Source.Locals E.layout Λ × Source.St E) (target : State C Γ)
    (capacity : (payload frame offset length).length < 2^256) :
    Related ((Source.cdToMem frame (.bytes .memory) offset length).run source).2.2.heap
      source.2.heap.next (lower target frame offset length capacity).heap
      (target.alloc (bytesObj target.H (payload frame offset length) capacity)).2 := by
  rw [source_copy]
  exact ⟨payload frame offset length,Source.Heap.alloc_get source.2.heap _,
    target_contents target frame offset length capacity⟩

theorem old_local {C : Contract} {Γ : Ctx} (target : State C Γ) (frame : Source.Fr)
    (offset length : Nat) (capacity : (payload frame offset length).length < 2^256)
    {type : LTy} (index : Idx Γ type) :
    TEnv.get (.there index) (lower target frame offset length capacity).env =
      LTy.TDenote.wk (List.prefix_append target.H [bytesR]) type (TEnv.get index target.env) :=
  TEnv.get_wk _ index target.env

theorem new_local {C : Contract} {Γ : Ctx} (target : State C Γ) (frame : Source.Fr)
    (offset length : Nat) (capacity : (payload frame offset length).length < 2^256) :
    TEnv.get .here (lower target frame offset length capacity).env =
      some (target.alloc (bytesObj target.H (payload frame offset length) capacity)).2 := rfl

/-- Representation of the read-only Source calldata value, before
any optional Source memory copy. No Source heap allocation is asserted here. -/
def RefRelated {D : Source.Layout} (frame : Source.Fr)
    (value : Source.Val D (.bytes .calldata)) {H : HTy}
    (target : Heap H) (reference : HRef H bytesR) : Prop :=
  match value with
  | .cdRef _ offset length =>
      MObj.elems ArrTy.dyn (target.get reference) = (payload frame offset length).map byteWord
  | _ => False

theorem entry_value (D : Source.Layout) {data : Roadmap.Bytes} {index offset length : Nat}
    (entry : Source.cdTail data index 1 = .ok (offset,length)) :
    Source.cdArg D data index 1 (τ := .bytes .calldata) rfl =
      .ok (.cdRef rfl offset length) := by
  rw [Source.cdArg,entry]
  rfl

/-- Actual ABI reference production and target value import, with entry-derived
capacity and untruncated extent. The Source value stays a calldata reference. -/
theorem raw_parameter_related (D : Source.Layout) {C : Contract} {Γ : Ctx}
    (target : State C Γ) (frame : Source.Fr) (selector data : Roadmap.Bytes)
    (selector_length : selector.length = 4) (input : frame.cd = selector ++ data)
    {index offset length : Nat} (entry : Source.cdTail data index 1 = .ok (offset,length)) :
    ∃ value, Source.cdArg D data index 1 (τ := .bytes .calldata) rfl = .ok value ∧
      RefRelated frame value (lower target frame offset length (entry_capacity frame entry)).heap
        (target.alloc (bytesObj target.H (payload frame offset length) (entry_capacity frame entry))).2 ∧
      (payload frame offset length).length = length :=
  ⟨.cdRef rfl offset length,entry_value D entry,
    target_contents target frame offset length (entry_capacity frame entry),
    entry_payload_exact frame selector data selector_length input entry⟩

end Solidity.Backend.Aggregates.ByteParameters
