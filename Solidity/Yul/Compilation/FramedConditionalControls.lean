import Solidity.Yul.Compilation.FramedConditional
import Solidity.Yul.Compilation.ComparisonBranchControls
import Solidity.Yul.Compilation.FramedBranchControls
/-! A genuine original intrinsic comparison/assignment branch consumes the
whole-conditional contract. Success and failure controls remain compiler-model
facts; no native/resource, logical Source/G24 or full admission follows. -/
namespace Solidity.Yul.Compilation.FramedConditional.Controls
open Backend Scalar Selection MachineAdapter
open ComparisonBranch

def condition : FramedLoweringCertificate [.dup 2,.dup 2,.lt]
 (.code [.op (.DUP 1),.op (.DUP 1),.op .LT]) :=
 FramedWordLowering.lowering _ _ (by rfl)
def arm : FramedLoweringCertificate [.push (coreWord dirty),.swap 2,.pop]
 (.code [pushWord dirty,.op (.SWAP 1),.op .POP]) :=
 FramedWordLowering.lowering _ _ (by rfl)
def emptyArm : FramedLoweringCertificate [] (.code []) :=
 FramedWordLowering.lowering [] [] rfl

/-- The supplied code/block are exactly the original visitor's emitted branch,
not a hand-picked alternative compiler. -/
def certificate : FramedLoweringCertificate model lowered :=
 conditional condition arm emptyArm

theorem successful (a b : Scalar.Word) (m : Evm.Machine) :
 Evm.run model {m with stack := irStack [a,b]} =
 .ok {m with stack := irStack [a,if a.toNat < b.toNat then dirty else b]} 0 := by
 simpa only [irStack_cons,List.append_nil] using model_run a b m []

/-- Every actual success, not just the successful witness above, yields a real
structured trace and exact full frame with zero pending skip. -/
theorem reflected (input : Stack) (m final : Evm.Machine) (skip : Nat)
 (ran : Evm.run model {m with stack := irStack input} = .ok final skip) :
 ∃ output : Stack, skip = 0 ∧ final = {m with stack := irStack output} ∧
 StructuredExec lowered input output := by
 simpa only [] using certificate.reflect input {m with stack := irStack input} final skip rfl ran

/-- Without a guard the actual conditional faults, despite both arms being
available as real certified code. -/
def noGuardCertificate : FramedLoweringCertificate
 (MachineControl.branchCode [] FramedBranch.Controls.yesModel FramedBranch.Controls.noModel)
 (.ite [] (.code FramedBranch.Controls.yesCode) (.code FramedBranch.Controls.noCode)) :=
 conditional emptyArm FramedBranch.Controls.left FramedBranch.Controls.right

theorem missing_guard (m : Evm.Machine) :
 Evm.run (MachineControl.branchCode [] FramedBranch.Controls.yesModel FramedBranch.Controls.noModel)
 {m with stack := []} = .fault := rfl

/-- A high-only original literal expression selects the successful arm in the
whole model conditional. The untaken SDIV arm faults on an empty stack by
`Solidity.Yul.Compilation.FramedBranch.Controls.empty_untaken_fault`. -/
def high : Scalar.Word := BitVec.ofNat 256 (2^200)
def highExpression := ProducerExpressions.literal 0 (n := 0) high.toFin
def highCode := (highExpression.lowered.code 0).get (by rfl)
def highModel := (SignedMachine.selectCode highCode).get (by rfl)
def highCondition : FramedLoweringCertificate highModel (.code highCode) :=
 FramedWordLowering.lowering highCode highModel (Option.some_get (by rfl)).symm

def highCertificate : FramedLoweringCertificate
 (MachineControl.branchCode highModel FramedBranch.Controls.yesModel FramedBranch.Controls.noModel)
 (.ite highCode (.code FramedBranch.Controls.yesCode) (.code FramedBranch.Controls.noCode)) :=
 conditional highCondition FramedBranch.Controls.left FramedBranch.Controls.right

theorem high_success (m : Evm.Machine) :
 Evm.run (MachineControl.branchCode highModel FramedBranch.Controls.yesModel FramedBranch.Controls.noModel)
 {m with stack := []} = .ok {m with stack := irStack [FramedBranch.Controls.dirty]} 0 := by
 apply (highCertificate.success [] [FramedBranch.Controls.dirty] {m with stack := []} rfl).mpr
 have guard : Scalar.run highCode [] = some [high] := by rfl
 have nonzero : high ≠ 0 := by decide
 exact StructuredExec.iteTrue guard nonzero (.code (by rfl))

#guard ComparisonBranch.Controls.sourceResult 1 3 = some (1,dirty.toNat,true)
#guard ComparisonBranch.Controls.sourceResult 3 1 = some (3,1,true)
#guard highExpression.value #v[] = high
#guard high.toNat % 256 = 0
/-- info: 'Solidity.Yul.Compilation.FramedConditional.Controls.condition' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms condition
/-- info: 'Solidity.Yul.Compilation.FramedConditional.Controls.arm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms arm
/-- info: 'Solidity.Yul.Compilation.FramedConditional.Controls.emptyArm' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms emptyArm
/-- info: 'Solidity.Yul.Compilation.FramedConditional.Controls.certificate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms certificate
/-- info: 'Solidity.Yul.Compilation.FramedConditional.Controls.successful' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms successful
/-- info: 'Solidity.Yul.Compilation.FramedConditional.Controls.reflected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms reflected
/-- info: 'Solidity.Yul.Compilation.FramedConditional.Controls.noGuardCertificate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms noGuardCertificate
/-- info: 'Solidity.Yul.Compilation.FramedConditional.Controls.missing_guard' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms missing_guard
/-- info: 'Solidity.Yul.Compilation.FramedConditional.Controls.highCondition' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms highCondition
/-- info: 'Solidity.Yul.Compilation.FramedConditional.Controls.highCertificate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms highCertificate
/-- info: 'Solidity.Yul.Compilation.FramedConditional.Controls.high_success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms high_success
end Solidity.Yul.Compilation.FramedConditional.Controls
