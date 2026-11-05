import Solidity.Backend.MemoryOps.PhysicalByteStackExact

/-! Inhabited complete-byte observations for the real materializer. These two
backend byte APIs have no Source pipeline parameter. No Source execution,
physical allocation, gas, checked stack height or external EVM claim is made. -/
namespace Solidity.Backend.MemoryOps.Physical.MaterializeControls
open Evm
private def high : Fin W := ⟨2^255+9,by decide⟩
private def origin : Machine := {Machine.init with stack := [w[77],w[88]]}
private def machine := Memory.writeMachine origin 2 (.val high)
private def bytes : Environment.Memory := Environment.writeBytes (fun _ => 5) 64 (Semantics.wordBytes high.val)
private def payload : List UInt8 := [7,0,255]
private def reached := Environment.writeBytes bytes 31 payload
private def overlapping := Environment.writeBytes reached 32 [9]
private def a : Roadmap.Word := ⟨31,by decide⟩
private def n : Roadmap.Word := ⟨3,by decide⟩
private def tail : List Roadmap.Word := [⟨42,by decide⟩]
private def envTail : List Environment.Word := [lenU 42 (by decide)]
private theorem initial : WordFrame machine bytes (fun c => c=2) := by
  first
  | solve | simp only [] | omega
  | have empty : WordFrame origin (fun _ => 5) (fun _ => False) := ⟨fun _ h => h.elim,fun _ h => h.elim⟩
    have full := empty.write 2 high (by decide)
    exact ⟨fun c hc => full.fits c (Or.inr hc),fun c hc => full.cells c (Or.inr hc)⟩

/-- Nonzero offset, embedded zero, full-byte maximum, complete protected word
and caller stack. Both real byte APIs execute the same existing emitted code. -/
theorem populated (frame : Environment.Frame) (suffix : Backend.Program) :
    Environment.runSlice frame (Environment.materialize 31 payload) ⟨envTail,bytes⟩=some ⟨envTail,reached⟩ ∧
    Failure.Slice.run (Environment.materialize 31 payload++(.op .REVERT::suffix)) ⟨a::n::tail,bytes⟩=
      some (⟨tail,reached⟩,some (.revert payload)) ∧
    WordFrame machine reached (fun c => c=2) ∧
    Environment.readMemory bytes 30 6=[5,5,5,5,5,5] ∧
    Environment.readMemory reached 30 6=[5,7,0,255,5,5] ∧
    Environment.readMemory reached 64 32=Semantics.wordBytes high.val ∧
    [machine.mem 0,machine.mem 1,machine.mem 2]=[w[0],w[0],.val high] ∧ machine.stack=[w[77],w[88]] ∧
    (∀ j,j<31 ∨ 34≤j → reached j=bytes j) ∧
    Environment.readMemory reached 31 3≠Environment.readMemory bytes 31 3 := by
  first
  | solve | simp only [] | omega
  | obtain ⟨env,run,fr,outside⟩ := initial.materialize_revert frame a n payload tail envTail suffix rfl (by decide)
        (by intro c hc;subst c;decide)
    have complete : Environment.readMemory reached 64 32=Semantics.wordBytes high.val := by
      obtain ⟨w,hw,hb⟩ := fr.cells 2 rfl
      change Word.val high=Word.val w at hw
      rw [←Word.val.inj hw] at hb
      exact hb
    exact ⟨env,run,fr,by decide,by decide,complete,rfl,rfl,outside,by decide⟩

/-- A second overlapping emitted store consumes the first reached byte memory.
Reversing it is observably different; neither result is an assumed run. -/
theorem overlap (suffix : Backend.Program) :
    Failure.Slice.run (Environment.materialize 31 payload++Environment.materialize 32 [9]++(.op .REVERT::suffix))
      ⟨a::n::tail,bytes⟩=some (⟨tail,overlapping⟩,some (.revert [7,9,255])) ∧
    Failure.Slice.run (Environment.materialize 32 [9]++Environment.materialize 31 payload++(.op .REVERT::suffix))
      ⟨a::n::tail,bytes⟩=some (⟨tail,Environment.writeBytes (Environment.writeBytes bytes 32 [9]) 31 payload⟩,
        some (.revert [7,0,255])) ∧
    WordFrame machine overlapping (fun c => c=2) ∧
    Environment.readMemory overlapping 30 6=[5,7,9,255,5,5] ∧
    Environment.readMemory overlapping 64 32=Semantics.wordBytes high.val ∧
    Environment.readMemory (Environment.writeBytes (Environment.writeBytes bytes 32 [9]) 31 payload) 31 3=[7,0,255] ∧
    Environment.readMemory overlapping 31 3≠[7,0,255] := by
  first
  | solve | simp only [] | omega
  | have first := materialize_suffix payload 31 (a::n::tail) bytes
        (Environment.materialize 32 [9]++(.op .REVERT::suffix)) (by decide)
    have second := materialize_suffix [9] 32 (a::n::tail) reached (.op .REVERT::suffix) (by decide)
    have fr := (initial.materialize_outside 31 payload (by intro c hc;subst c;decide)).materialize_outside
        32 [9] (by intro c hc;subst c;decide)
    have complete : Environment.readMemory overlapping 64 32=Semantics.wordBytes high.val := by
      obtain ⟨w,hw,hb⟩ := fr.cells 2 rfl
      change Word.val high=Word.val w at hw
      rw [←Word.val.inj hw] at hb
      exact hb
    refine ⟨?_,?_,fr,by decide,complete,by decide,by decide⟩
    · rw [List.append_assoc,first]
      change Failure.Slice.run (Environment.materialize 32 [9]++(.op .REVERT::suffix)) ⟨a::n::tail,reached⟩=_
      rw [second,revert_live]
      rfl
    · rw [List.append_assoc,materialize_suffix [9] 32 (a::n::tail) bytes
        (Environment.materialize 31 payload++(.op .REVERT::suffix)) (by decide),
        materialize_suffix payload 31 (a::n::tail) (Environment.writeBytes bytes 32 [9])
          (.op .REVERT::suffix) (by decide),revert_live]
      rfl

/-- Empty materialization is a real no-op, while unsupported MLOAD after a
nonempty successful prefix fails without returning a fabricated final machine. -/
theorem boundaries (frame : Environment.Frame) :
    Environment.runSlice frame (Environment.materialize 31 []) ⟨envTail,bytes⟩=some ⟨envTail,bytes⟩ ∧
    Failure.Slice.run (Environment.materialize 31 []) ⟨tail,bytes⟩=some (⟨tail,bytes⟩,none) ∧
    Failure.Slice.run (Environment.materialize 31 payload++[.op .MLOAD]) ⟨tail,bytes⟩=none ∧
    Failure.Slice.run [ .op .MSTORE8 ] ⟨[],reached⟩=none := by
  first
  | solve | simp only [] | omega
  | refine ⟨rfl,rfl,?_,rfl⟩
    rw [materialize_suffix payload 31 tail bytes [.op .MLOAD] (by decide)]
    rfl

/-- info: 'Solidity.Backend.MemoryOps.Physical.MaterializeControls.populated' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms populated
/-- info: 'Solidity.Backend.MemoryOps.Physical.MaterializeControls.overlap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms overlap
/-- info: 'Solidity.Backend.MemoryOps.Physical.MaterializeControls.boundaries' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms boundaries
/-- Checked execution reaches the existing 1024-word peak and preserves all
caller words and the same populated byte/word footprint. One more input word
rejects checkedRun although unchecked run still returns the actual live bytes. -/
theorem stack_capacity (suffix : Backend.Program) :
    Failure.Slice.checkedRun (Environment.materialize 31 payload++(.op .REVERT::suffix))
      ⟨a::n::List.replicate 1020 (⟨42,by decide⟩ : Roadmap.Word),bytes⟩=
      some (⟨List.replicate 1020 (⟨42,by decide⟩ : Roadmap.Word),reached⟩,some (.revert payload)) ∧
    Failure.Slice.checkedRun (Environment.materialize 31 payload++(.op .REVERT::suffix))
      ⟨a::n::List.replicate 1021 (⟨42,by decide⟩ : Roadmap.Word),bytes⟩=none ∧
    Failure.Slice.run (Environment.materialize 31 payload++(.op .REVERT::suffix))
      ⟨a::n::List.replicate 1021 (⟨42,by decide⟩ : Roadmap.Word),bytes⟩=
      some (⟨List.replicate 1021 (⟨42,by decide⟩ : Roadmap.Word),reached⟩,some (.revert payload)) ∧
    WordFrame machine reached (fun c => c=2) ∧
    Environment.readMemory reached 30 6=[5,7,0,255,5,5] ∧
    Environment.readMemory reached 64 32=Semantics.wordBytes high.val := by
  first
  | solve | simp only [] | omega
  | have checked := materialize_checked_revert payload a n (List.replicate 1020 ⟨42,by decide⟩) bytes suffix
        rfl (by decide) (by simp only [List.length_replicate];decide)
    have rejected := materialize_stack_1023 7 [0,255] 31
        (a::n::List.replicate 1021 ⟨42,by decide⟩) bytes (.op .REVERT::suffix)
        (by simp only [List.length_cons,List.length_replicate])
    have unchecked := materialize_suffix payload 31 (a::n::List.replicate 1021 ⟨42,by decide⟩) bytes
        (.op .REVERT::suffix) (by decide)
    rw [revert_live] at unchecked
    have readback : Environment.readMemory reached a.val n.val=payload := by rfl
    change Failure.Slice.run _ _=some (⟨_,reached⟩,some (.revert (Environment.readMemory reached a.val n.val))) at unchecked
    rw [readback] at unchecked
    have fr := initial.materialize_outside 31 payload (by intro c hc;subst c;decide)
    have complete : Environment.readMemory reached 64 32=Semantics.wordBytes high.val := by
      obtain ⟨w,hw,hb⟩ := fr.cells 2 rfl
      change Word.val high=Word.val w at hw
      rw [←Word.val.inj hw] at hb
      exact hb
    exact ⟨checked.2,rejected.2,unchecked,fr,by decide,complete⟩

/-- Empty materialization has no transient PUSH peak: 1024 input words pass,
1025 fail the already-published initial stack guard. No Source admission claim. -/
theorem empty_stack_boundary :
    Failure.Slice.checkedRun (Environment.materialize 31 [])
      ⟨List.replicate 1024 (⟨42,by decide⟩ : Roadmap.Word),bytes⟩=
      some (⟨List.replicate 1024 (⟨42,by decide⟩ : Roadmap.Word),bytes⟩,none) ∧
    Failure.Slice.checkedRun (Environment.materialize 31 [])
      ⟨List.replicate 1025 (⟨42,by decide⟩ : Roadmap.Word),bytes⟩=none := by
  first
  | solve | simp only [Environment.materialize,Failure.Slice.checkedRun,Failure.Slice.stackSafe,
      List.length_replicate,Failure.Slice.run] | decide | omega
  | have pass : Failure.Slice.stackSafe [] ⟨List.replicate 1024 (⟨42,by decide⟩ : Roadmap.Word),bytes⟩=true := by
      change decide ((List.replicate 1024 (⟨42,by decide⟩ : Roadmap.Word)).length≤1024)=true
      rw [List.length_replicate]
      rfl
    have fail : Failure.Slice.stackSafe [] ⟨List.replicate 1025 (⟨42,by decide⟩ : Roadmap.Word),bytes⟩=false := by
      change decide ((List.replicate 1025 (⟨42,by decide⟩ : Roadmap.Word)).length≤1024)=false
      rw [List.length_replicate]
      rfl
    constructor
    · rw [Environment.materialize,Failure.Slice.checkedRun,if_pos pass]
      rfl
    · rw [Environment.materialize,Failure.Slice.checkedRun,fail]
      rfl

/-- info: 'Solidity.Backend.MemoryOps.Physical.MaterializeControls.stack_capacity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms stack_capacity
/-- info: 'Solidity.Backend.MemoryOps.Physical.MaterializeControls.empty_stack_boundary' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms empty_stack_boundary
/-- Classify EVERY runtime caller stack. A returned machine has the complete
populated frame and byte observations; rejection returns no machine at all.
Earlier finite boundary/empty/overlap observations are unchanged. -/
theorem all_stack_classified (caller : List Roadmap.Word) (suffix : Backend.Program) :
    Failure.Slice.checkedRun (Environment.materialize 31 payload++(.op .REVERT::suffix)) ⟨a::n::caller,bytes⟩=
      (if caller.length+4≤1024 then some (⟨caller,reached⟩,some (.revert payload)) else none) ∧
    (Failure.Slice.checkedRun (Environment.materialize 31 payload++(.op .REVERT::suffix)) ⟨a::n::caller,bytes⟩=none ↔
      1024<caller.length+4) ∧
    (∀ result,Failure.Slice.checkedRun (Environment.materialize 31 payload++(.op .REVERT::suffix)) ⟨a::n::caller,bytes⟩=some result →
      result=(⟨caller,reached⟩,some (.revert payload)) ∧
      WordFrame machine result.1.memory (fun c => c=2) ∧ result.1.stack=caller ∧
      Environment.readMemory result.1.memory 30 6=[5,7,0,255,5,5] ∧
      Environment.readMemory result.1.memory 64 32=Semantics.wordBytes high.val) := by
  first
  | solve | simp only [] | omega
  | have run := materialize_checked_revert_exact 7 [0,255] a n caller bytes suffix rfl (by decide)
    change Failure.Slice.checkedRun (Environment.materialize 31 payload++(.op .REVERT::suffix)) ⟨a::n::caller,bytes⟩=
      (if caller.length+4≤1024 then some (⟨caller,reached⟩,some (.revert payload)) else none) at run
    have frame := initial.materialize_outside 31 payload (by intro c hc;subst c;decide)
    have complete : Environment.readMemory reached 64 32=Semantics.wordBytes high.val := by
      obtain ⟨w,hw,hb⟩ := frame.cells 2 rfl
      change Word.val high=Word.val w at hw
      rw [←Word.val.inj hw] at hb
      exact hb
    refine ⟨run,?_,?_⟩
    · rw [run]
      by_cases room : caller.length+4≤1024
      · rw [if_pos room]
        constructor
        · intro impossible;cases impossible
        · intro impossible;omega
      · rw [if_neg room]
        exact ⟨fun _ => by omega,fun _ => rfl⟩
    · intro result returned
      rw [run] at returned
      by_cases room : caller.length+4≤1024
      · rw [if_pos room] at returned
        have resultEq := (Option.some.inj returned).symm
        refine ⟨resultEq,?_⟩
        rw [resultEq]
        exact ⟨frame,rfl,by change Environment.readMemory reached 30 6=[5,7,0,255,5,5];decide,complete⟩
      · rw [if_neg room] at returned
        cases returned

/-- info: 'Solidity.Backend.MemoryOps.Physical.MaterializeControls.all_stack_classified' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms all_stack_classified
end Solidity.Backend.MemoryOps.Physical.MaterializeControls
