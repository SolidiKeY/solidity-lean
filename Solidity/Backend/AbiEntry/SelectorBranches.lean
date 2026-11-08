import Solidity.Backend.AbiEntry.SelectorBranchesInterface
import Solidity.Backend.AbiEntry.PayableRoutes

/-! Actual typed selector branching through the existing public compiler.
Exact join behavior is retained for arbitrary body outcomes, including skips;
no desired execution or normal-return premise is introduced. -/
namespace Solidity.Backend.AbiEntry.SelectorBranches
open Solidity.Evm
variable {C : Contract} {Γ ΔT ΔF : Ctx}

def program (index : Idx Γ (.val .uint)) (tag : Fin W)
    (yes : Prog C Γ ΔT) (no : Prog C Γ ΔF) : Prog C Γ Γ :=
  .cons (.ite (SelectorGateBody.condition index tag) yes no) .nil

theorem admitted (frag : Frag Γ) (index : Idx Γ (.val .uint)) (tag : Fin W)
    (yes : Prog C Γ ΔT) (no : Prog C Γ ΔF) (yesFrag : Frag ΔT) (noFrag : Frag ΔF)
    (yesCore : inFragP frag yes=some yesFrag) (noCore : inFragP frag no=some noFrag) :
    inFragP frag (program index tag yes no)=some ((yesFrag.restrict Γ).meet (noFrag.restrict Γ)) := by
  simp only [program,inFragP,inFrag,SelectorGateBody.condition,valIn,simpleIn,binInFrag,Bool.true_and,ite_true,yesCore,noCore]

def selectedWhole (base : Nat) (frag : Frag Γ) (index : Idx Γ (.val .uint)) (tag : Fin W)
    (yes : Prog C Γ ΔT) (no : Prog C Γ ΔF) (yesFrag : Frag ΔT) (noFrag : Frag ΔF)
    (yesCore : inFragP frag yes=some yesFrag) (noCore : inFragP frag no=some noFrag) :
    Compiler.Compilation base frag (program index tag yes no) :=
  .core ((yesFrag.restrict Γ).meet (noFrag.restrict Γ)) (admitted frag index tag yes no yesFrag noFrag yesCore noCore)

def selectedBranch (base : Nat) (frag : Frag Γ) (body : Prog C Γ ΔT) (outFrag : Frag ΔT)
    (bodyCore : inFragP frag body=some outFrag) : Compiler.Compilation base frag body :=
  ValueGateBody.selectedBody base frag body outFrag bodyCore

theorem whole_selected (base : Nat) (frag : Frag Γ) (index : Idx Γ (.val .uint)) (tag : Fin W)
    (yes : Prog C Γ ΔT) (no : Prog C Γ ΔF) (yesFrag : Frag ΔT) (noFrag : Frag ΔF)
    (yesCore : inFragP frag yes=some yesFrag) (noCore : inFragP frag no=some noFrag) :
    Compiler.compile base frag (program index tag yes no)=some (selectedWhole base frag index tag yes no yesFrag noFrag yesCore noCore) :=
  ValueGateBody.body_selected base frag _ _ (admitted frag index tag yes no yesFrag noFrag yesCore noCore)

theorem branch_selected (base : Nat) (frag : Frag Γ) (body : Prog C Γ ΔT) (outFrag : Frag ΔT)
    (bodyCore : inFragP frag body=some outFrag) :
    Compiler.compile base frag body=some (selectedBranch base frag body outFrag bodyCore) :=
  ValueGateBody.body_selected base frag body outFrag bodyCore

theorem code (base : Nat) (frag : Frag Γ) (index : Idx Γ (.val .uint)) (tag : Fin W)
    (yes : Prog C Γ ΔT) (no : Prog C Γ ΔF) (yesFrag : Frag ΔT) (noFrag : Frag ΔF)
    (yesCore : inFragP frag yes=some yesFrag) (noCore : inFragP frag no=some noFrag) :
    (selectedWhole base frag index tag yes no yesFrag noFrag yesCore noCore).code=
      [.mload (cellOf base index),.push (.val tag),.eq,.iszero,
        .jumpi ((selectedBranch base frag yes yesFrag yesCore).code.length+1)]++
      (selectedBranch base frag yes yesFrag yesCore).code++
      [.jump (selectedBranch base frag no noFrag noCore).code.length]++
      (selectedBranch base frag no noFrag noCore).code := by
  change compileProg base (program index tag yes no)=_
  simp only [program,compileProg,compileStmt,List.append_nil]
  rw [SelectorGateBody.condition_code]
  rfl

theorem executed (base : Nat) (frag : Frag Γ) (index : Idx Γ (.val .uint)) (tag : Fin W)
    (yes : Prog C Γ ΔT) (no : Prog C Γ ΔF) (yesFrag : Frag ΔT) (noFrag : Frag ΔF)
    (yesCore : inFragP frag yes=some yesFrag) (noCore : inFragP frag no=some noFrag)
    (whole : Compiler.Compilation base frag (program index tag yes no))
    (left : Compiler.Compilation base frag yes) (right : Compiler.Compilation base frag no)
    (wholeFound : Compiler.compile base frag (program index tag yes no)=some whole)
    (leftFound : Compiler.compile base frag yes=some left) (rightFound : Compiler.compile base frag no=some right)
    (machine : Machine) (selector : Fin W) (initial : machine.mem (cellOf base index)=.val selector) :
    run whole.code machine=if tag.val=selector.val then
      run (left.code++[.jump right.code.length]++right.code) machine else run right.code machine := by
  have sameWhole : whole=selectedWhole base frag index tag yes no yesFrag noFrag yesCore noCore :=
    Option.some.inj (wholeFound.symm.trans (whole_selected base frag index tag yes no yesFrag noFrag yesCore noCore))
  have sameLeft : left=selectedBranch base frag yes yesFrag yesCore :=
    Option.some.inj (leftFound.symm.trans (branch_selected base frag yes yesFrag yesCore))
  have sameRight : right=selectedBranch base frag no noFrag noCore :=
    Option.some.inj (rightFound.symm.trans (branch_selected base frag no noFrag noCore))
  rw [sameWhole,sameLeft,sameRight,code]
  exact PayableRoutes.test_run (cellOf base index) tag selector _ _ machine initial

/-- The real body outcome feeds the real join, with its skip retained. -/
theorem join_form (yes no : List Evm.Instr) (machine : Machine) :
    run (yes++[.jump no.length]++no) machine=
      (run yes machine).bind (fun next skip => exec ([.jump no.length]++no) skip next) := by
  rw [List.append_assoc]
  exact exec_append yes ([.jump no.length]++no) 0 machine

def certificate : Interface.SelectorBranchesCertificate program where
  selected := fun base frag index tag yes no yesFrag noFrag yesCore noCore =>
    ⟨selectedWhole base frag index tag yes no yesFrag noFrag yesCore noCore,
      selectedBranch base frag yes yesFrag yesCore,selectedBranch base frag no noFrag noCore,
      whole_selected base frag index tag yes no yesFrag noFrag yesCore noCore,
      branch_selected base frag yes yesFrag yesCore,branch_selected base frag no noFrag noCore⟩
  executed := executed

/-- info: 'Solidity.Backend.AbiEntry.SelectorBranches.admitted' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms admitted
/-- info: 'Solidity.Backend.AbiEntry.SelectorBranches.whole_selected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms whole_selected
/-- info: 'Solidity.Backend.AbiEntry.SelectorBranches.branch_selected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms branch_selected
/-- info: 'Solidity.Backend.AbiEntry.SelectorBranches.code' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms code
/-- info: 'Solidity.Backend.AbiEntry.SelectorBranches.executed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms executed
/-- info: 'Solidity.Backend.AbiEntry.SelectorBranches.join_form' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms join_form
/-- info: 'Solidity.Backend.AbiEntry.SelectorBranches.certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms certificate
end Solidity.Backend.AbiEntry.SelectorBranches
