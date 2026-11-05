import Solidity.Backend.AbiEntry.CoreJoinInterface
import Solidity.Backend.AbiEntry.ValueGateBody

/-! Existing core join proofs shared independently of selector/decoder imports.
Public names, statements and input/resource premises are unchanged.
Only an unused simp argument is removed from the moved proof. -/
namespace Solidity.Backend.AbiEntry.CoreJoin
open Solidity.Evm
variable {C : Contract} {Γ Δ : Ctx}

def compiled (base : Nat) (frag : Frag Γ) (body : Prog C Γ Δ) (outFrag : Frag Δ)
    (bodyCore : inFragP frag body=some outFrag) : Compiler.Compilation base frag body :=
  ValueGateBody.selectedBody base frag body outFrag bodyCore

theorem selected (base : Nat) (frag : Frag Γ) (body : Prog C Γ Δ) (outFrag : Frag Δ)
    (bodyCore : inFragP frag body=some outFrag) :
    Compiler.compile base frag body=some (compiled base frag body outFrag bodyCore) :=
  ValueGateBody.body_selected base frag body outFrag bodyCore

theorem core_join (L base : Nat) (frag : Frag Γ) (body : Prog C Γ Δ) (outFrag : Frag Δ)
    (bodyCore : inFragP frag body=some outFrag) (state : State C Γ) (machine : Machine)
    (represented : Sim C L base frag state machine) (room : L+Prog.pushes body≤Lmax)
    (rest : List Evm.Instr) :
    run (compileProg base body++[.jump rest.length]++rest) machine=run (compileProg base body) machine := by
  rcases compile_correct bodyCore represented room with
    ⟨_,next,_,returned,_,_⟩ | ⟨_,reverted⟩ | ⟨_,reverted,_⟩ | ⟨_,faulted | ⟨_,reverted⟩⟩
  · rw [List.append_assoc,run_append_ok returned,returned]
    simp only [List.cons_append,List.nil_append,run,exec_cons_zero,Instr.step,Out.bind,exec_length]
  · rw [List.append_assoc,run_append_revert reverted,reverted]
  · rw [List.append_assoc,run_append_revert reverted,reverted]
  · rw [List.append_assoc,run_append_fault faulted,faulted]
  · rw [List.append_assoc,run_append_revert reverted,reverted]

theorem joined (L base : Nat) (frag : Frag Γ) (body : Prog C Γ Δ) (outFrag : Frag Δ)
    (bodyCore : inFragP frag body=some outFrag) (result : Compiler.Compilation base frag body)
    (found : Compiler.compile base frag body=some result) (state : State C Γ) (machine : Machine)
    (represented : Sim C L base frag state machine) (room : L+Prog.pushes body≤Lmax) (rest : List Evm.Instr) :
    run (result.code++[.jump rest.length]++rest) machine=run result.code machine := by
  have same : result=compiled base frag body outFrag bodyCore :=
    Option.some.inj (found.symm.trans (selected base frag body outFrag bodyCore))
  rw [same]
  exact core_join L base frag body outFrag bodyCore state machine represented room rest


/-- info: 'Solidity.Backend.AbiEntry.CoreJoin.selected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms selected
/-- info: 'Solidity.Backend.AbiEntry.CoreJoin.core_join' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms core_join
/-- info: 'Solidity.Backend.AbiEntry.CoreJoin.joined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms joined
end Solidity.Backend.AbiEntry.CoreJoin
