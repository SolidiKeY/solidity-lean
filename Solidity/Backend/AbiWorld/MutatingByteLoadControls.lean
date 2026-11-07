import Solidity.Backend.AbiWorld.MutatingByteLoad
import Solidity.Backend.AbiWorld.MutatingWritePhysicalControls

/-! Actual inhabited STORE prefix, conditional store/load consumer and an
actual absent-MLOAD negative. NO ByteWorld producer instance is asserted. -/
namespace Solidity.Backend.AbiWorld.MutatingByteLoadControls
open Solidity Evm Evm.Memory
open Solidity.Backend.InternalFlow.RuntimeFrame
open RecursiveSource RecursiveActivation GuardedRecursion GuardedPrefixes CountdownWitness
open Solidity.Backend.MemoryOps.Physical
abbrev Initial := MutatingWritePhysicalControls.bytes
abbrev Image := MutatingWritePhysicalControls.image
abbrev Before := MutatingWritePhysicalControls.before

theorem conditional_application (code : Nat → Backend.Program) (producer : ByteWorld.Producer code)
 (frame : Environment.Frame) :
 Memory.compileStmt 2 F (MutatingActivation.write (C:=P.C))=some (MutatingActivation.selected 2 F) ∧
 (MutatingActivation.write (C:=P.C)).run callee=
  .ok ⟨MutatingActivation.changed callee P.r0 1,List.prefix_refl _⟩ ∧
 run (MutatingActivation.selected (C:=P.C) 2 F).code Before=.ok (writeMachine Before 18 w[2]) 0 ∧
 Environment.runSlice frame (.op .MSTORE::code 18)
  ⟨lenU 576 (by decide)::lenU 2 (by decide)::[lenU 77 (by decide)],Initial⟩=
 some ⟨lenU 2 (by decide)::[lenU 77 (by decide)],Image⟩ ∧
 Environment.readMemory Image 672 32=AbiEntry.wordBytes 4 := by
 first | (solve | rfl) | (solve | decide) | (solve | omega) | skip
 obtain ⟨selected,source,actual,repr,growth,footprint,physical,read,exterior,wordLoad,loaded,composed⟩ :=
  MutatingByteLoad.write_then_load callee 1 (by decide) P.r0 rfl rfl
   (by rw [HeapDomain.Checks.length_zero];decide) P.base Before ParentPrefixes.Checks.initial
   Initial MutatingWritePhysicalControls.live MutatingWritePhysicalControls.initial
   (by decide) code producer frame [lenU 77 (by decide)] (by decide)
 exact ⟨selected,source,actual,composed,MutatingWritePhysicalControls.applied.2.2.2.2.2.2⟩

theorem actual_prefix :
 Environment.cryptoStep (.op .MSTORE)
  ⟨lenU 576 (by decide)::lenU 2 (by decide)::[lenU 77 (by decide)],Initial⟩=
 some ⟨[lenU 77 (by decide)],Image⟩ ∧
 Environment.readMemory Image 576 32=AbiEntry.wordBytes 2 ∧
 Environment.readMemory Image 672 32=AbiEntry.wordBytes 4 :=
 MutatingWritePhysicalControls.applied.2.2.2.2

theorem actual_literal_load_absent (frame : Environment.Frame) :
 Environment.runSlice frame [.op .MLOAD] ⟨[lenU 576 (by decide)],Image⟩=none := by rfl

def concrete_frame : Environment.Frame :=
 { self := Environment.account (lenU 7 (by decide))
   sender := Environment.account (lenU 9 (by decide))
   value := lenU 11 (by decide)
   time := lenU 13 (by decide)
   funds := fun _ => lenU 17 (by decide) }

theorem concrete_literal_refusal :
 Environment.runSlice concrete_frame [.op .MLOAD] ⟨[lenU 576 (by decide)],Image⟩=none := rfl

theorem no_literal_producer (frame : Environment.Frame) :
 ¬ ByteWorld.Producer (fun _ => [.op .MLOAD]) := MutatingByteLoad.literal_mload_refused frame

theorem conditional_wrong_scale (code : Nat → Backend.Program) (producer : ByteWorld.Producer code)
 (frame : Environment.Frame) :
 Environment.runSlice frame (code 576) ⟨[lenU 77 (by decide)],Image⟩≠
 some ⟨lenU 2 (by decide)::[lenU 77 (by decide)],Image⟩ := by
 first | (solve | rfl) | (solve | decide) | (solve | omega) | skip
 have read : Environment.readMemory Image (32*576) 32=Semantics.wordBytes 0 := by decide +kernel
 have loaded := producer.load frame Image ⟨576,by decide⟩ ⟨0,by decide⟩ [lenU 77 (by decide)]
  (by decide) (by decide) read
 rw [loaded]
 intro wrong
 have stack := congrArg Environment.Slice.stack (Option.some.inj wrong)
 have values := congrArg (fun w : Environment.Word => w.val) (List.cons.inj stack).1
 change (0:Int)=2 at values
 omega

def render (bs : List UInt8) := "["++String.intercalate "," (bs.map (fun b=>toString b.toNat))++"]"
#eval IO.println (match Environment.cryptoStep (.op .MSTORE)
 ⟨lenU 576 (by decide)::lenU 2 (by decide)::[lenU 77 (by decide)],Initial⟩ with
 | some reached => "ACTUAL_STORE_CHANGED="++render (Environment.readMemory reached.memory 576 32)++
  "\nACTUAL_STORE_NEIGHBOR="++render (Environment.readMemory reached.memory 672 32)
 | none => "UNEXPECTED_STORE_REFUSAL")
/-- info: 'Solidity.Backend.AbiWorld.MutatingByteLoad.write_then_load' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MutatingByteLoad.write_then_load
/-- info: 'Solidity.Backend.AbiWorld.MutatingByteLoad.literal_mload_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MutatingByteLoad.literal_mload_refused
/-- info: 'Solidity.Backend.AbiWorld.MutatingByteLoadControls.conditional_application' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms conditional_application
/-- info: 'Solidity.Backend.AbiWorld.MutatingByteLoadControls.concrete_literal_refusal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms concrete_literal_refusal
/-- info: 'Solidity.Backend.AbiWorld.MutatingByteLoadControls.actual_prefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms actual_prefix
/-- info: 'Solidity.Backend.AbiWorld.MutatingByteLoadControls.actual_literal_load_absent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms actual_literal_load_absent
/-- info: 'Solidity.Backend.AbiWorld.MutatingByteLoadControls.no_literal_producer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms no_literal_producer
/-- info: 'Solidity.Backend.AbiWorld.MutatingByteLoadControls.conditional_wrong_scale' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms conditional_wrong_scale
end Solidity.Backend.AbiWorld.MutatingByteLoadControls
