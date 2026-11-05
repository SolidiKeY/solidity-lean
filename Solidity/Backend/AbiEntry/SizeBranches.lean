import Solidity.Backend.AbiEntry.SizeBranchesInterface

/-! Short/full branching uses an intrinsic uint size local and the existing
public compiler. Exact raw skips are retained; represented core inputs justify
join removal. No Source metadata or native calldata-size binding is supplied. -/
namespace Solidity.Backend.AbiEntry.SizeBranches
open Solidity.Evm
variable {C : Contract} {Γ ΔT ΔF : Ctx}

def condition (index : Idx Γ (.val .uint)) : Val C Γ .bool :=
  .binop .lt rfl rfl (.simple (.local index)) (.simple (.lit 4 rfl))

theorem condition_code (base : Nat) (index : Idx Γ (.val .uint)) :
    compileVal base (condition (C := C) index)=[.mload (cellOf base index),.push (.val (wmod 4)),.gt] := rfl

def program (index : Idx Γ (.val .uint))
    (yes : Prog C Γ ΔT) (no : Prog C Γ ΔF) : Prog C Γ Γ :=
  .cons (.ite (condition index) yes no) .nil

theorem admitted (frag : Frag Γ) (index : Idx Γ (.val .uint))
    (yes : Prog C Γ ΔT) (no : Prog C Γ ΔF) (yesFrag : Frag ΔT) (noFrag : Frag ΔF)
    (yesCore : inFragP frag yes=some yesFrag) (noCore : inFragP frag no=some noFrag) :
    inFragP frag (program index yes no)=some ((yesFrag.restrict Γ).meet (noFrag.restrict Γ)) := by
  have different : (PrimTy.uint != PrimTy.bool)=true := by decide
  simp only [program,inFragP,inFrag,condition,valIn,simpleIn,binInFrag,different,Bool.true_and,if_true,yesCore,noCore]

def selectedWhole (base : Nat) (frag : Frag Γ) (index : Idx Γ (.val .uint))
    (yes : Prog C Γ ΔT) (no : Prog C Γ ΔF) (yesFrag : Frag ΔT) (noFrag : Frag ΔF)
    (yesCore : inFragP frag yes=some yesFrag) (noCore : inFragP frag no=some noFrag) :
    Compiler.Compilation base frag (program index yes no) :=
  .core ((yesFrag.restrict Γ).meet (noFrag.restrict Γ)) (admitted frag index yes no yesFrag noFrag yesCore noCore)

def selectedBranch (base : Nat) (frag : Frag Γ) (body : Prog C Γ ΔT) (outFrag : Frag ΔT)
    (bodyCore : inFragP frag body=some outFrag) : Compiler.Compilation base frag body :=
  ValueGateBody.selectedBody base frag body outFrag bodyCore

theorem whole_selected (base : Nat) (frag : Frag Γ) (index : Idx Γ (.val .uint))
    (yes : Prog C Γ ΔT) (no : Prog C Γ ΔF) (yesFrag : Frag ΔT) (noFrag : Frag ΔF)
    (yesCore : inFragP frag yes=some yesFrag) (noCore : inFragP frag no=some noFrag) :
    Compiler.compile base frag (program index yes no)=some (selectedWhole base frag index yes no yesFrag noFrag yesCore noCore) :=
  ValueGateBody.body_selected base frag _ _ (admitted frag index yes no yesFrag noFrag yesCore noCore)

theorem branch_selected (base : Nat) (frag : Frag Γ) (body : Prog C Γ ΔT) (outFrag : Frag ΔT)
    (bodyCore : inFragP frag body=some outFrag) :
    Compiler.compile base frag body=some (selectedBranch base frag body outFrag bodyCore) :=
  ValueGateBody.body_selected base frag body outFrag bodyCore

theorem code (base : Nat) (frag : Frag Γ) (index : Idx Γ (.val .uint))
    (yes : Prog C Γ ΔT) (no : Prog C Γ ΔF) (yesFrag : Frag ΔT) (noFrag : Frag ΔF)
    (yesCore : inFragP frag yes=some yesFrag) (noCore : inFragP frag no=some noFrag) :
    (selectedWhole base frag index yes no yesFrag noFrag yesCore noCore).code=
      [.mload (cellOf base index),.push (.val (wmod 4)),.gt,.iszero,
        .jumpi ((selectedBranch base frag yes yesFrag yesCore).code.length+1)]++
      (selectedBranch base frag yes yesFrag yesCore).code++
      [.jump (selectedBranch base frag no noFrag noCore).code.length]++
      (selectedBranch base frag no noFrag noCore).code := by
  change compileProg base (program index yes no)=_
  simp only [program,compileProg,compileStmt,List.append_nil]
  rw [condition_code]
  rfl

theorem test_run (base : Nat) (size : Fin W) (yes no : List Evm.Instr) (machine : Machine)
    (initial : machine.mem base=.val size) :
    run ([.mload base,.push (.val (wmod 4)),.gt,.iszero,.jumpi (yes.length+1)]++yes++[.jump no.length]++no) machine=
      if size.val<4 then run (yes++[.jump no.length]++no) machine else run no machine := by
  by_cases small : size.val<4
  · simp only [run,List.cons_append,List.nil_append,List.append_assoc,exec_cons_zero,Instr.step,
      Machine.next,Out.bind,initial,wmod,Nat.mod_eq_of_lt (by decide : (4 : Nat)<W),small,decide_true,bword,if_true,if_false,
      Nat.one_ne_zero,decide_false,Bool.false_eq_true]
  · simp only [run,List.cons_append,List.nil_append,List.append_assoc,exec_cons_zero,Instr.step,
      Machine.next,Out.bind,initial,wmod,Nat.mod_eq_of_lt (by decide : (4 : Nat)<W),small,decide_false,decide_true,bword,if_true,if_false,
      Nat.one_ne_zero,Bool.false_eq_true,exec_skip_append,exec_cons_succ]


theorem executed (base : Nat) (frag : Frag Γ) (index : Idx Γ (.val .uint))
    (yes : Prog C Γ ΔT) (no : Prog C Γ ΔF) (yesFrag : Frag ΔT) (noFrag : Frag ΔF)
    (yesCore : inFragP frag yes=some yesFrag) (noCore : inFragP frag no=some noFrag)
    (whole : Compiler.Compilation base frag (program index yes no))
    (left : Compiler.Compilation base frag yes) (right : Compiler.Compilation base frag no)
    (wholeFound : Compiler.compile base frag (program index yes no)=some whole)
    (leftFound : Compiler.compile base frag yes=some left) (rightFound : Compiler.compile base frag no=some right)
    (machine : Machine) (size : Fin W) (initial : machine.mem (cellOf base index)=.val size) :
    run whole.code machine=if size.val<4 then
      run (left.code++[.jump right.code.length]++right.code) machine else run right.code machine := by
  have sameWhole : whole=selectedWhole base frag index yes no yesFrag noFrag yesCore noCore :=
    Option.some.inj (wholeFound.symm.trans (whole_selected base frag index yes no yesFrag noFrag yesCore noCore))
  have sameLeft : left=selectedBranch base frag yes yesFrag yesCore :=
    Option.some.inj (leftFound.symm.trans (branch_selected base frag yes yesFrag yesCore))
  have sameRight : right=selectedBranch base frag no noFrag noCore :=
    Option.some.inj (rightFound.symm.trans (branch_selected base frag no noFrag noCore))
  rw [sameWhole,sameLeft,sameRight,code]
  exact test_run (cellOf base index) size _ _ machine initial

theorem branch_outcome {ΔT ΔF : Ctx} (L base : Nat) (frag : Frag Γ)
    (index : Idx Γ (.val .uint)) (yes : Prog C Γ ΔT) (no : Prog C Γ ΔF)
    (yesFrag : Frag ΔT) (noFrag : Frag ΔF)
    (yesCore : inFragP frag yes=some yesFrag) (noCore : inFragP frag no=some noFrag)
    (whole : Compiler.Compilation base frag (program index yes no))
    (left : Compiler.Compilation base frag yes) (right : Compiler.Compilation base frag no)
    (wholeFound : Compiler.compile base frag (program index yes no)=some whole)
    (leftFound : Compiler.compile base frag yes=some left) (rightFound : Compiler.compile base frag no=some right)
    (state : State C Γ) (machine : Machine) (represented : Sim C L base frag state machine)
    (room : L+Prog.pushes yes≤Lmax) (size : Fin W) (initial : machine.mem (cellOf base index)=.val size) :
    run whole.code machine=if size.val<4 then run left.code machine else run right.code machine := by
  rw [executed base frag index yes no yesFrag noFrag yesCore noCore whole left right
    wholeFound leftFound rightFound machine size initial,
    CoreJoin.joined L base frag yes yesFrag yesCore left leftFound state machine represented room right.code]

def certificate : Interface.SizeBranchesCertificate program where
  selected := fun base frag index yes no yesFrag noFrag yesCore noCore =>
    ⟨selectedWhole base frag index yes no yesFrag noFrag yesCore noCore,
      selectedBranch base frag yes yesFrag yesCore,selectedBranch base frag no noFrag noCore,
      whole_selected base frag index yes no yesFrag noFrag yesCore noCore,
      branch_selected base frag yes yesFrag yesCore,branch_selected base frag no noFrag noCore⟩
  executed := executed
  body_outcome := branch_outcome

/-- info: 'Solidity.Backend.AbiEntry.SizeBranches.condition_code' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms condition_code
/-- info: 'Solidity.Backend.AbiEntry.SizeBranches.admitted' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms admitted
/-- info: 'Solidity.Backend.AbiEntry.SizeBranches.whole_selected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms whole_selected
/-- info: 'Solidity.Backend.AbiEntry.SizeBranches.branch_selected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms branch_selected
/-- info: 'Solidity.Backend.AbiEntry.SizeBranches.code' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms code
/-- info: 'Solidity.Backend.AbiEntry.SizeBranches.test_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms test_run
/-- info: 'Solidity.Backend.AbiEntry.SizeBranches.executed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms executed
/-- info: 'Solidity.Backend.AbiEntry.SizeBranches.branch_outcome' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms branch_outcome
/-- info: 'Solidity.Backend.AbiEntry.SizeBranches.certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms certificate
end Solidity.Backend.AbiEntry.SizeBranches
