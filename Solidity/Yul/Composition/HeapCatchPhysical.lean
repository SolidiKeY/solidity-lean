import Solidity.Yul.Composition.AttemptPhysical

/-! Actual typed Source catch-byte allocation/readback; raw caller remains an
indexed companion. Logical heap indices are never identified with EVM pointers.
No general Source try dispatch/catch variable or raw Source frame is invented. -/
namespace Solidity.Yul.Composition.HeapCatchPhysical
open Solidity.Yul.Views Solidity.Yul.Views.Controls LocalPhysicalControls

/-- Actual allocRef and actual bytesOfRV/heapBytes, not a copied allocator. -/
def allocateRead {E Γ} (F : Source.Fr) (data : List UInt8) :
    Source.EM E Γ (Source.Val E.layout (.bytes .memory) × List UInt8) := do
  let ref ← Source.allocRef (Source.Data.bytes (l:=.memory) data)
  let bytes ← Source.bytesOfRV F 32 (.val ref)
  pure (ref,bytes)

theorem allocRef_run {E : Source.Env} {Γ : Source.RCtx} (data : List UInt8) (locals : Source.Locals E.layout Γ) (state : Source.St E) :
    (Source.allocRef (Source.Data.bytes (l:=.memory) data) : Source.EM E Γ _).run (locals,state) =
      (Except.ok (Source.Val.memRef (D:=E.layout) (τ:=.bytes .memory) rfl state.heap.next),(locals,{state with heap:=(state.heap.alloc ⟨.bytes .memory,.bytes data⟩).1})) := rfl

theorem bind_run {E Γ α β} (first : Source.EM E Γ α) (next : α → Source.EM E Γ β)
    (state : Source.EMState E Γ) :
    (first >>= next).run state = match first.run state with
      | (.ok value,post) => (next value).run post
      | (.error halt,post) => (.error halt,post) := Source.Hoare.run_bind first next state

theorem heapObj_run {E Γ} (address : Nat) (locals : Source.Locals E.layout Γ) (state : Source.St E) :
    (Source.heapObj address : Source.EM E Γ _).run (locals,state) =
      match state.heap.get address with
      | some object => (Except.ok object,(locals,state))
      | none => (Except.error (.stuck "dangling memory reference"),(locals,state)) := by
  unfold Source.heapObj
  rw [Source.Hoare.run_bind]
  have read_state : (Source.EM.st : Source.EM E Γ (Source.St E)).run (locals,state) = (Except.ok state,(locals,state)) := rfl
  rw [read_state]
  dsimp only
  cases state.heap.get address <;> rfl

theorem bytesOf_ref_run {E : Source.Env} {Γ : Source.RCtx} (F : Source.Fr) (address : Nat) (data : List UInt8)
    (locals : Source.Locals E.layout Γ) (state : Source.St E)
    (found : state.heap.get address = some ⟨.bytes .memory,.bytes data⟩) :
    (Source.bytesOfRV (E:=E) (Γ:=Γ) F 32 (.val (.memRef (D:=E.layout) (τ:=.bytes .memory) rfl address)) : Source.EM E Γ _).run (locals,state) =
      (Except.ok data,(locals,state)) := by
  unfold Source.bytesOfRV Source.heapBytes
  rw [bind_run,heapObj_run,found]
  rfl

theorem allocateRead_run {E : Source.Env} {Γ : Source.RCtx} (F : Source.Fr) (data : List UInt8)
    (locals : Source.Locals E.layout Γ) (state : Source.St E) :
    (allocateRead (E:=E) (Γ:=Γ) F data).run (locals,state) =
      (Except.ok (Source.Val.memRef (D:=E.layout) (τ:=.bytes .memory) rfl state.heap.next,data),
        (locals,{state with heap:=(state.heap.alloc ⟨.bytes .memory,.bytes data⟩).1})) := by
  unfold allocateRead
  rw [bind_run,allocRef_run]
  dsimp only
  rw [bind_run,bytesOf_ref_run F state.heap.next data locals _ (Source.Heap.alloc_get state.heap _)]
  rfl

/-- Uses the previous ACTUAL attempt capture, allocating only on revert. -/
def captureAllocate {α} (F : Source.Fr) (result : Except Source.Halt α) :
    Source.EM originEnv [] (α ⊕ (Source.Val originEnv.layout (.bytes .memory) × List UInt8)) :=
  match AttemptPhysical.classify result with
  | .ok (.ok value) => pure (.inl value)
  | .ok (.error bytes) => do let allocated ← allocateRead F bytes; pure (.inr allocated)
  | .error halt => Source.EM.halt halt

def afterCaptured (captured : Except Source.Halt (Except Source.Halt (List UInt8))) :=
  match captured with
  | .ok result => captureAllocate packedStepFrame result
  | .error halt => Source.EM.halt halt

def capture (result : Except Source.Halt (List UInt8)) :=
  let actual := AttemptPhysical.companion (AttemptPhysical.action result) .nil AttemptPhysical.input
  (actual,AttemptPhysical.companion (afterCaptured actual.1.1) .nil actual.2)

/-- Concrete byte allocation carrier; exposes actual typed reference/readback. -/
def capturedPost (result : Except Source.Halt (List UInt8)) :=
  (AttemptPhysical.companion (AttemptPhysical.action result) .nil AttemptPhysical.input).2

def allocated (data : List UInt8) := AttemptPhysical.companion (allocateRead packedStepFrame data : Source.EM originEnv [] _) .nil
  (capturedPost (.error (.revert data)))

theorem full_contents (data : List UInt8) :
    (allocated data).1.1 = .ok (.ok (.memRef rfl AttemptPhysical.input.2.heap.next,data)) := by
  unfold allocated AttemptPhysical.companion
  rw [AttemptPhysical.attempt_run,allocateRead_run]
  rfl

theorem allocated_heap (data : List UInt8) :
    (allocated data).2.2.heap = (AttemptPhysical.input.2.heap.alloc ⟨.bytes .memory,.bytes data⟩).1 := by
  unfold allocated AttemptPhysical.companion
  rw [AttemptPhysical.attempt_run,allocateRead_run]
  rfl

theorem full_frame (data : List UInt8) :
    (allocated data).2.2 = {(capturedPost (.error (.revert data))).2 with
      heap:=(AttemptPhysical.input.2.heap.alloc ⟨.bytes .memory,.bytes data⟩).1} := by
  unfold allocated AttemptPhysical.companion
  rw [AttemptPhysical.attempt_run,allocateRead_run]
  rfl

theorem raw_retained (data : List UInt8) : (allocated data).2.1 = AttemptPhysical.input.1 := rfl

theorem object_contents (data : List UInt8) :
    (allocated data).2.2.heap.get AttemptPhysical.input.2.heap.next = some ⟨.bytes .memory,.bytes data⟩ := by
  rw [allocated_heap]
  exact Source.Heap.alloc_get _ _

theorem fresh (data : List UInt8) : AttemptPhysical.input.2.heap.get AttemptPhysical.input.2.heap.next = none :=
  Source.Heap.alloc_fresh _ ⟨.bytes .memory,.bytes data⟩

theorem prior_object_retained (data : List UInt8) (address : Nat) (different : address ≠ AttemptPhysical.input.2.heap.next) :
    (allocated data).2.2.heap.get address = AttemptPhysical.input.2.heap.get address := by
  rw [allocated_heap]
  exact Source.Heap.alloc_other _ _ different

/-- Read bytes back from the actual allocated typed object before continuing. -/
def continued (data : List UInt8) (fuel : Nat) :=
  (allocated data).1.1.map fun outcome => outcome.map fun pair =>
    runLocalBlock ctx (AttemptPhysical.continuationCode pair.2) (AttemptPhysical.continuationPolicy pair.2) fuel (allocated data).2

theorem exact_readback_continuation (data : List UInt8) (fuel : Nat) :
    continued data fuel = .ok (.ok (runLocalBlock ctx (AttemptPhysical.continuationCode data)
      (AttemptPhysical.continuationPolicy data) fuel (allocated data).2)) := by
  unfold continued
  rw [full_contents]
  rfl

theorem completes : (runLocalBlock ctx (AttemptPhysical.continuationCode [0xde,0xad])
    (AttemptPhysical.continuationPolicy [0xde,0xad]) 32 (allocated [0xde,0xad]).2).isSome := by decide +kernel

def completed : LocalBlockOutcome ctx ⟨false,false⟩ := (runLocalBlock ctx (AttemptPhysical.continuationCode [0xde,0xad])
    (AttemptPhysical.continuationPolicy [0xde,0xad]) 32 (allocated [0xde,0xad]).2).get completes

theorem continued_words : snapshot completed.state =
    [2,2^256-1,2309737967,2307,22136,2^256-1,171*2^248] := by decide +kernel

theorem completed_source : completed.state.2 = (allocated [0xde,0xad]).2.2 :=
  runLocalBlock_world ctx _ _ 32 _ (Option.some_get completes).symm

theorem heap_readback : completed.state.2.heap.get 1 = some ⟨.bytes .memory,.bytes [0xde,0xad]⟩ := by
  rw [completed_source]
  exact object_contents _

theorem nonword_retained : completed.state.1.get memoryRef.index = (LocalValues.ofClean locals).get memoryRef.index := by
  have kept : completed.state.1.get memoryRef.index = (allocated [0xde,0xad]).2.1.get memoryRef.index :=
    runLocalBlock_nonword ctx _ _ 32 _ (Option.some_get completes).symm memoryRef memoryShape rfl
  exact kept.trans CatchFunctionPhysical.nonword_retained

theorem capture_revert_result (data : List UInt8) :
    (capture (.error (.revert data))).2.1.1 =
      .ok (.ok (.inr (.memRef rfl AttemptPhysical.input.2.heap.next,data))) := by
  unfold capture afterCaptured captureAllocate AttemptPhysical.classify
  change (AttemptPhysical.companion
    (do let allocated ← allocateRead packedStepFrame data; pure (Sum.inr allocated)) .nil (capturedPost (.error (.revert data)))).1.1 = _
  unfold AttemptPhysical.companion
  rw [AttemptPhysical.attempt_run,Source.Hoare.run_bind,allocateRead_run]
  rfl

theorem capture_revert_state (data : List UInt8) : (capture (.error (.revert data))).2.2 = (allocated data).2 := by
  unfold capture afterCaptured captureAllocate AttemptPhysical.classify
  change (AttemptPhysical.companion
    (do let allocated ← allocateRead packedStepFrame data; pure (Sum.inr allocated)) .nil (capturedPost (.error (.revert data)))).2 = _
  unfold AttemptPhysical.companion allocated
  rw [AttemptPhysical.attempt_run,Source.Hoare.run_bind,allocateRead_run]
  unfold AttemptPhysical.companion
  rw [AttemptPhysical.attempt_run,allocateRead_run]
  rfl

theorem capture_success (data : List UInt8) : (capture (.ok data)).2.1.1 = .ok (.ok (.inl data)) := rfl

theorem capture_timeout : (capture (.error .timeout)).2.1.1 = .ok (.error .timeout) := rfl

theorem capture_stuck (why : String) : (capture (.error (.stuck why))).2.1.1 = .ok (.error (.stuck why)) := rfl

theorem success_no_allocation (data : List UInt8) :
    (capture (.ok data)).2.2.2.heap = AttemptPhysical.input.2.heap := rfl

theorem timeout_no_allocation :
    (capture (.error .timeout)).2.2.2.heap = AttemptPhysical.input.2.heap := rfl

theorem capture_panic : (capture (Source.panic .assert)).2.1.1 =
    .ok (.ok (.inr (.memRef rfl AttemptPhysical.input.2.heap.next,Source.panicData .assert))) := capture_revert_result _

theorem continued_complete : continued [0xde,0xad] 32 = .ok (.ok (some completed)) := by
  rw [exact_readback_continuation]
  exact congrArg Except.ok (congrArg Except.ok (Option.some_get completes).symm)

theorem alias_zero (data : List UInt8) :
    (allocated data).2.2.heap.get 0 = some ⟨.bytes .memory,.bytes [0xaa,0xbb]⟩ := by
  rw [prior_object_retained data 0 (by decide)]
  rfl

theorem length_exact (data : List UInt8) :
    ((allocated data).1.1.map (fun outcome => outcome.map (fun pair=>pair.2.length))) = .ok (.ok data.length) := by
  rw [full_contents]
  rfl

theorem next_exact (data : List UInt8) : (allocated data).2.2.heap.next = AttemptPhysical.input.2.heap.next+1 := by
  rw [allocated_heap]
  rfl

theorem raw_not_clean : LocalState.clean? completed.state = none :=
  AttemptPhysical.continuation_raw _ 32 _ completed (Option.some_get completes).symm

theorem no_clean_resume (action : Source.EM originEnv ctx.tys Unit) :
    LocalState.runClean action completed.state = none := LocalState.runClean_refuses action _ raw_not_clean

theorem completed_unique (fuel : Nat) (result : LocalBlockOutcome ctx ⟨false,false⟩)
    (done : runLocalBlock ctx (AttemptPhysical.continuationCode [0xde,0xad]) (AttemptPhysical.continuationPolicy [0xde,0xad]) fuel (allocated [0xde,0xad]).2 = some result) : result=completed :=
  runLocalBlock_unique ctx _ _ _ done (Option.some_get completes).symm

/-- Actual allocRef rejects non-memory type AFTER allocating; no fake rollback. -/
def badAllocation := AttemptPhysical.companion
  (Source.allocRef (Source.Data.val (.bool false)) : Source.EM originEnv [] _) .nil AttemptPhysical.input

theorem bad_reference_type : badAllocation.1.1 = .ok (.error (.stuck "memory reference type")) := rfl

theorem bad_allocation_retained : badAllocation.2.2.heap.get 1 = some ⟨.bool,.val (.bool false)⟩ := rfl

theorem nonbyte_read_refused :
    (Source.heapBytes 1 : Source.EM originEnv [] _).run (.nil,badAllocation.2.2) =
      (Except.error (.stuck "not a bytes object"),(.nil,badAllocation.2.2)) := rfl

theorem dangling_read_refused :
    (Source.heapBytes 2 : Source.EM originEnv [] _).run (.nil,(allocated [0xde,0xad]).2.2) =
      (Except.error (.stuck "dangling memory reference"),(.nil,(allocated [0xde,0xad]).2.2)) := rfl

/-- Conditional physical image theorem: all real allocation/layout/window/range
premises retained. A logical heap index is NOT an EVM pointer. -/
theorem physical_window (data : List UInt8) (bound : data.length < 2^256)
    (placement : Placement (allocated data).2.2.heap)
    (memory : ByteView) (reserved : ReservedOK memory placement.free)
    (offset size destination : Nat) (selected : List UInt8)
    (window : Solidity.Yul.World.returnWindow data offset size = some selected)
    (caller : Solidity.Backend.Environment.Slice) (fits : destination+selected.length ≤ 2^256) :
    let image : MemoryImage placement (Source.Data.bytes (l:=.memory) data) := .bytes data bound
    let physical := image.encode memory (placement.address AttemptPhysical.input.2.heap.next)
    ReservedOK physical placement.free ∧
    Solidity.Backend.Environment.runData (Solidity.Backend.Environment.materialize destination selected) caller =
      some {caller with memory:=copyBytes caller.memory physical destination (placement.address AttemptPhysical.input.2.heap.next+32+offset) size} ∧
    ValidRange (placement.address AttemptPhysical.input.2.heap.next+32+offset) size :=
  allocated_bytes_window_target placement _ data bound (object_contents data) memory reserved offset size destination selected window caller fits

#print axioms allocateRead_run
#print axioms capture_revert_result
#print axioms capture_revert_state
#print axioms continued_complete
#print axioms bad_reference_type
#print axioms physical_window
end Solidity.Yul.Composition.HeapCatchPhysical
