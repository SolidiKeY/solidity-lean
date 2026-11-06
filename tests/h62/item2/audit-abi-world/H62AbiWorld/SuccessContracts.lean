import Solidity.Backend.AbiWorld.PacketPrefixControls
import Solidity.Backend.AbiWorld.CheckedAddArtifactControls
import Solidity.Backend.AbiWorld.PanicCallFrameControls

/-! Additional behavioral contracts for the actual supported packet programs.
These do not alter a frozen theorem or claim a general source-to-bytecode bridge.
Slice has no gas/fork semantics; those boundaries are independently replayed. -/
namespace H62.AbiWorld.Success
open Solidity Solidity.Backend Solidity.Backend.Failure Solidity.Backend.AbiWorld

local instance (a : Nat) (bs : List UInt8) : Decidable (Fits a bs) :=
  inferInstanceAs (Decidable (a<wordLimit ∧ bs.length<wordLimit ∧ a+bs.length≤wordLimit))

def compileReturn (a : Nat) (bs : List UInt8) : Option Program :=
  some (emit a (.returned bs))

def ReturnContract (compiler : Nat → List UInt8 → Option Program) : Prop :=
  ∀ a bs, Fits a bs → ∃ code, compiler a bs = some code ∧
    ∀ machine : Slice.Machine, machine.stack.length+2 ≤ 1024 →
      Slice.checkedRun code machine =
        some ({machine with memory := Slice.putBytes machine.memory a bs},some (.success bs))

theorem return_total : ReturnContract compileReturn := by
  intro a bs fits
  refine ⟨emit a (.returned bs),rfl,?_⟩
  intro machine stack
  simpa only [List.append_nil,Input.bytes,Input.observation] using
    checkedRun_emit_suffix a (.returned bs) [] machine fits stack

/-- A shared nonempty supported domain, independent of compiler/run success. -/
theorem supported_nonempty :
  Fits 8 [0,255] ∧ ErrorReadWindowControls.machine.stack.length+2 ≤ 1024 ∧
    ([0,255] : List UInt8) ≠ [] := by decide

theorem reject_all_fails : ¬ ReturnContract (fun _ _ => none) := by
  intro contract
  obtain ⟨code,compiled,_⟩ := contract 8 [0,255] supported_nonempty.1
  cases compiled

def alwaysRevert (a : Nat) (bs : List UInt8) : Option Program :=
  some (emit a (.custom bs))

theorem always_revert_fails : ¬ ReturnContract alwaysRevert := by
  intro contract
  obtain ⟨code,compiled,runs⟩ := contract 8 [0,255] supported_nonempty.1
  have same : emit 8 (.custom [0,255]) = code := Option.some.inj compiled
  subst code
  have success := runs ErrorReadWindowControls.machine supported_nonempty.2.1
  have failure := checkedRun_emit_suffix 8 (.custom [0,255]) []
    ErrorReadWindowControls.machine supported_nonempty.1 supported_nonempty.2.1
  have impossible := congrArg (fun r : Option (Slice.Machine × Option Roadmap.Outcome) => r.map Prod.snd)
    (success.symm.trans (by simpa only [List.append_nil,Input.bytes,Input.observation] using failure))
  simp only [Option.map_some,Option.some.injEq,reduceCtorEq] at impossible

/-- This is assembly totality and nonempty layout, not branch-execution correctness. -/
theorem checked_add_assembly_total (address base label : Nat) (bound : base+4092<256^32) :
  ∃ out, CheckedAddArtifact.compile address base label=some out ∧ out.code≠[] := by
  obtain ⟨out,assembled⟩ := Option.isSome_iff_exists.mp
    (CheckedAddArtifact.compiles_bounded address base label bound)
  refine ⟨out,assembled,?_⟩
  obtain ⟨j,imm,tag,dest,push,offset⟩ := CheckedAddArtifact.conditional_target address base label assembled
  intro empty
  rw [empty] at dest
  cases dest

/-- An actual complete typed catch program succeeds for every full-word Panic code. -/
theorem panic_handler_total (n : Nat) (bound : n<2^256) (suffix : List UInt8) :
  ∃ out, ((PanicCallFrameControls.attempt
      (PanicCallFrame.callee (Semantics.encodePanic n ++ suffix))).runR PanicCallFrameControls.caller)=.ok out ∧
    PanicCallFrameControls.observe out.st=((n:Int),77,1,[(0,[161,178]),(0,[161,178])]) := by
  have observed := PanicCallFrameControls.application n bound suffix
  cases actual : (PanicCallFrameControls.attempt
      (PanicCallFrame.callee (Semantics.encodePanic n ++ suffix))).runR PanicCallFrameControls.caller with
  | error failure =>
      rw [actual] at observed
      cases observed
  | ok out =>
      rw [actual] at observed
      exact ⟨out,rfl,Except.ok.inj observed⟩

/-- Concrete zero-receiver failure remains observable beside total handled success. -/
theorem zero_receiver_fails :
  ((PanicCallFrameControls.attempt (PanicCallFrame.callee (Semantics.encodePanic 300)) 0).runR
    PanicCallFrameControls.caller).halt? = some .revert :=
  PanicCallFrameControls.zero_receiver 300 []

end H62.AbiWorld.Success
#print axioms H62.AbiWorld.Success.return_total
#print axioms H62.AbiWorld.Success.supported_nonempty
#print axioms H62.AbiWorld.Success.reject_all_fails
#print axioms H62.AbiWorld.Success.always_revert_fails
#print axioms H62.AbiWorld.Success.checked_add_assembly_total
#print axioms H62.AbiWorld.Success.panic_handler_total
#print axioms H62.AbiWorld.Success.zero_receiver_fails
