import Solidity.Backend.Aggregates.BoolArrays

/-! G18.04/.05 entry-plus-validation consumers over actual Source decoding
and conversion. No entry success is assumed by the phase importer. Its
Source.Halt channel is not a machine-step/revert correspondence. -/
namespace Solidity.Backend.Aggregates.BoolArrayEntry
open Solidity BoolArrays

/-- The actual typed Source argument decoder followed by its existing
calldata-to-memory conversion. This is a client, not a new evaluator. -/
def sourceCopy {E : Source.Env} {Λ : Source.RCtx} (frame : Source.Fr)
    (data : Roadmap.Bytes) (index : Nat) : Source.EM E Λ (Source.RVal E.layout sourceTy) := do
  let argument ← Source.decodeArg data index (.array .calldata .bool none)
  Source.convRV frame 0 sourceTy (.val argument)

theorem sourceCopy_run {E : Source.Env} {Λ : Source.RCtx} (frame : Source.Fr)
    (data : Roadmap.Bytes) (index : Nat) (source : Source.EMState E Λ) :
    (sourceCopy frame data index).run source =
      match Source.cdTail data index 32 with
      | .error halt => (.error halt,source)
      | .ok (offset,length) => (Source.cdToMem frame sourceTy offset length).run source := by
  unfold sourceCopy
  rw [Source.Hoare.run_bind,Source.decodeArg_cdArray_run data index .bool rfl source]
  rw [Source.cdHeadBytes_of_word (τ := .bool) rfl]
  unfold Source.cdArg
  cases Source.cdTail data index 32 with
  | error halt => rfl
  | ok pair => cases pair; rfl

/-- Entry and word validation are both executed through existing Source
operations; no successful ABI-entry premise or manufactured capacity. -/
def lowerEntry {E : Source.Env} {C : Contract} {Γ : Ctx} (target : State C Γ)
    (frame : Source.Fr) (selector data : Roadmap.Bytes)
    (selector_length : selector.length = 4) (input : frame.cd = selector ++ data) (index : Nat) :
    Except Source.Halt (State C (.mem boolR :: Γ)) :=
  match entry : Source.cdTail data index 32 with
  | .error halt => .error halt
  | .ok (_offset,_length) => lowerCopy (E := E) target frame selector data selector_length input entry

theorem lowerEntry_of_ok {E : Source.Env} {C : Contract} {Γ : Ctx} (target : State C Γ)
    (frame : Source.Fr) (selector data : Roadmap.Bytes)
    (selector_length : selector.length = 4) (input : frame.cd = selector ++ data)
    {index offset length : Nat} (entry : Source.cdTail data index 32 = .ok (offset,length)) :
    lowerEntry (E := E) target frame selector data selector_length input index =
      lowerCopy (E := E) target frame selector data selector_length input entry := by
  unfold lowerEntry
  split
  · rename_i _ observed
    rw [entry] at observed
    cases observed
  · rename_i _ _ observed
    rw [entry] at observed
    cases observed
    rfl

theorem lowerEntry_of_error {E : Source.Env} {C : Contract} {Γ : Ctx} (target : State C Γ)
    (frame : Source.Fr) (selector data : Roadmap.Bytes)
    (selector_length : selector.length = 4) (input : frame.cd = selector ++ data)
    {index : Nat} {halt : Source.Halt} (entry : Source.cdTail data index 32 = .error halt) :
    lowerEntry (E := E) target frame selector data selector_length input index = .error halt := by
  unfold lowerEntry
  split
  · rename_i _ observed
    rw [entry] at observed
    cases observed
    rfl
  · rename_i _ _ observed
    rw [entry] at observed
    cases observed

/-- Error reflection for the complete actual argument decode/conversion
client, with no assumed entry success. This remains a Source diagnostic
phase theorem, not a physical machine failure theorem. -/
theorem entry_error_iff_source_error {E : Source.Env} {Λ : Source.RCtx} {C : Contract} {Γ : Ctx}
    (source : Source.EMState E Λ) (target : State C Γ) (frame : Source.Fr)
    (selector data : Roadmap.Bytes) (selector_length : selector.length = 4)
    (input : frame.cd = selector ++ data) (index : Nat) (halt : Source.Halt) :
    lowerEntry (E := E) target frame selector data selector_length input index = .error halt ↔
      (sourceCopy frame data index).run source = (.error halt,source) := by
  rw [sourceCopy_run]
  cases entry : Source.cdTail data index 32 with
  | error actual =>
    rw [lowerEntry_of_error target frame selector data selector_length input entry]
    constructor
    · intro same
      cases same
      rfl
    · intro same
      have equality := Except.error.inj (congrArg Prod.fst same)
      cases equality
      rfl
  | ok pair =>
    rcases pair with ⟨offset,length⟩
    rw [lowerEntry_of_ok target frame selector data selector_length input entry]
    exact phase_error_iff_copy_error source target frame selector data selector_length input entry halt

/-- A successful real entry/validation derives the actual argument-copy
result/state, typed target value/frame and independent heap contents.
The caller's worlds/physical frames are not identified by this relation. -/
theorem successful_import {E : Source.Env} {Λ : Source.RCtx} {C : Contract} {Γ : Ctx}
    (source : Source.EMState E Λ) (target : State C Γ) (frame : Source.Fr)
    (selector data : Roadmap.Bytes) (selector_length : selector.length = 4)
    (input : frame.cd = selector ++ data)
    {index offset length : Nat} (entry : Source.cdTail data index 32 = .ok (offset,length))
    {values : List (Source.Val E.layout .bool)}
    (validation : (List.range length).mapM (fun j =>
      Source.decodeWord E.layout (Source.cdWordAt frame (offset+32*j)) .bool) = .ok values) :
    let room := capacity frame selector data selector_length input entry validation
    lowerEntry (E := E) target frame selector data selector_length input index = .ok (lower target values room) ∧
    (sourceCopy frame data index).run source =
      (.ok (.val (.memRef rfl source.2.heap.next)),(source.1,{source.2 with heap :=
        (source.2.heap.alloc ⟨sourceTy,Source.Data.array values.length
          (fun _ h => nomatch h) (fun k => .val (values.get k))⟩).1})) ∧
    Related ((sourceCopy frame data index).run source).2.2.heap source.2.heap.next
      (lower target values room).heap (target.alloc (object target.H values room)).2 := by
  dsimp only
  refine ⟨?_,?_,?_⟩
  · rw [lowerEntry_of_ok target frame selector data selector_length input entry]
    exact lowerCopy_success target frame selector data selector_length input entry validation
  · simp only [sourceCopy_run,entry]
    rw [(Source.cdToMem_array_run (σ := .bool)),validation]
  · rw [sourceCopy_run,entry]
    exact copy_related frame selector data selector_length input entry source target validation

end Solidity.Backend.Aggregates.BoolArrayEntry
