import Solidity.Backend.MemoryOps.PhysicalByteMaterialize

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
end Solidity.Backend.MemoryOps.Physical.MaterializeControls
