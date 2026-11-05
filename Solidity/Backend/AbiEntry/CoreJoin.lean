import Solidity.Backend.AbiEntry.CoreJoinInterface

/-! Existing compiler correctness supplies normal return, revert or fault from
represented core inputs. The actual join therefore preserves the full outcome,
without a desired execution or normal-return premise. -/
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
    simp only [List.cons_append,List.nil_append,run,exec_cons_zero,Instr.step,Machine.next,Out.bind,exec_length]
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

/-- The earlier exact branch theorem now gives the whole selected body outcome
from the existing represented input and resource bound. -/
theorem branch_outcome {ΔT ΔF : Ctx} (L base : Nat) (frag : Frag Γ)
    (index : Idx Γ (.val .uint)) (tag : Fin W) (yes : Prog C Γ ΔT) (no : Prog C Γ ΔF)
    (yesFrag : Frag ΔT) (noFrag : Frag ΔF)
    (yesCore : inFragP frag yes=some yesFrag) (noCore : inFragP frag no=some noFrag)
    (whole : Compiler.Compilation base frag (SelectorBranches.program index tag yes no))
    (left : Compiler.Compilation base frag yes) (right : Compiler.Compilation base frag no)
    (wholeFound : Compiler.compile base frag (SelectorBranches.program index tag yes no)=some whole)
    (leftFound : Compiler.compile base frag yes=some left) (rightFound : Compiler.compile base frag no=some right)
    (state : State C Γ) (machine : Machine) (represented : Sim C L base frag state machine)
    (room : L+Prog.pushes yes≤Lmax) (selector : Fin W) (initial : machine.mem (cellOf base index)=.val selector) :
    run whole.code machine=if tag.val=selector.val then run left.code machine else run right.code machine := by
  rw [SelectorBranches.executed base frag index tag yes no yesFrag noFrag yesCore noCore whole left right
    wholeFound leftFound rightFound machine selector initial,
    joined L base frag yes yesFrag yesCore left leftFound state machine represented room right.code]

def certificate : Interface.CoreJoinCertificate where
  selected := fun base frag body outFrag bodyCore => ⟨compiled base frag body outFrag bodyCore,selected base frag body outFrag bodyCore⟩
  joined := joined

/-- info: 'Solidity.Backend.AbiEntry.CoreJoin.selected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms selected
/-- info: 'Solidity.Backend.AbiEntry.CoreJoin.core_join' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms core_join
/-- info: 'Solidity.Backend.AbiEntry.CoreJoin.joined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms joined
/-- info: 'Solidity.Backend.AbiEntry.CoreJoin.branch_outcome' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms branch_outcome
/-- info: 'Solidity.Backend.AbiEntry.CoreJoin.certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms certificate
end Solidity.Backend.AbiEntry.CoreJoin
