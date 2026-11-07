import Solidity.Yul.LocalDefaultPostRepresentation
import Solidity.Yul.Checks.LocalDefaultControlRepresentation
import Solidity.Yul.Checks.LocalBoolPostRepresentation

namespace Solidity.Yul.Checks.LocalDefaultPostRepresentation
export Solidity.Yul.Checks.LocalDefaultControlRepresentation
  (env state raw cleanFalse read stop setFalse yesGuard yesItems yesProof yesReached YesOut)
export Solidity.Yul.Checks.LocalBoolPostRepresentation (faultExpr fault cleanTrue)
def witness : Nonempty (LocalDefaultItems.Supported env [] false ⟨true,false⟩
    (yesItems ⟨true,false⟩)) := ⟨yesProof ⟨true,false⟩⟩
def concrete (fuel : Nat) (one two : LocalState env [.bool])
    (related : Solidity.Yul.LocalBoolRepresentation.State one two) :=
  Solidity.Yul.LocalDefaultPostRepresentation.noGuard env [] false false
    [.bool] YesOut faultExpr fault (yesItems ⟨true,false⟩) (yesProof ⟨true,false⟩)
    fuel one two related

theorem postWriteStopsGuard : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalDefaultPostRepresentation.env), Solidity.Yul.LocalDefaultPostIter.run Solidity.Yul.Checks.LocalDefaultPostRepresentation.read Solidity.Yul.Checks.LocalDefaultPostRepresentation.setFalse (Solidity.Yul.Checks.LocalDefaultPostRepresentation.yesProof ⟨true,false⟩) 6 (Solidity.Yul.Checks.LocalDefaultPostRepresentation.state (Solidity.Yul.Checks.LocalDefaultPostRepresentation.raw 1) world) = .normal (Solidity.Yul.Checks.LocalDefaultPostRepresentation.state Solidity.Yul.Checks.LocalDefaultPostRepresentation.cleanFalse world) := by
  intro world; rfl

theorem falsePostIgnored : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalDefaultPostRepresentation.env), Solidity.Yul.LocalDefaultPostIter.run Solidity.Yul.Checks.LocalDefaultPostRepresentation.read Solidity.Yul.Checks.LocalDefaultPostRepresentation.stop (Solidity.Yul.Checks.LocalDefaultPostRepresentation.yesProof ⟨true,false⟩) 6 (Solidity.Yul.Checks.LocalDefaultPostRepresentation.state (Solidity.Yul.Checks.LocalDefaultPostRepresentation.raw 1) world) = .halted .timeout (Solidity.Yul.Checks.LocalDefaultPostRepresentation.yesReached (Solidity.Yul.Checks.LocalDefaultPostRepresentation.raw 1) world) := by
  intro world; rfl

theorem truePostIgnored : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalDefaultPostRepresentation.env), Solidity.Yul.LocalDefaultPostIter.run Solidity.Yul.Checks.LocalDefaultPostRepresentation.read Solidity.Yul.Checks.LocalDefaultPostRepresentation.yesGuard (Solidity.Yul.Checks.LocalDefaultPostRepresentation.yesProof ⟨true,false⟩) 6 (Solidity.Yul.Checks.LocalDefaultPostRepresentation.state (Solidity.Yul.Checks.LocalDefaultPostRepresentation.raw 1) world) = .halted .timeout (Solidity.Yul.Checks.LocalDefaultPostRepresentation.yesReached (Solidity.Yul.Checks.LocalDefaultPostRepresentation.raw 1) world) := by
  intro world; rfl

theorem skippedPost : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalDefaultPostRepresentation.env), Solidity.Yul.LocalDefaultPostIter.run Solidity.Yul.Checks.LocalDefaultPostRepresentation.stop Solidity.Yul.Checks.LocalDefaultPostRepresentation.fault (Solidity.Yul.Checks.LocalDefaultPostRepresentation.yesProof ⟨true,false⟩) 2 (Solidity.Yul.Checks.LocalDefaultPostRepresentation.state (Solidity.Yul.Checks.LocalDefaultPostRepresentation.raw 1) world) = .normal (Solidity.Yul.Checks.LocalDefaultPostRepresentation.state (Solidity.Yul.Checks.LocalDefaultPostRepresentation.raw 1) world) := by
  intro world; rfl

theorem bodyHaltBeforePost : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalDefaultPostRepresentation.env), Solidity.Yul.LocalDefaultPostIter.run Solidity.Yul.Checks.LocalDefaultPostRepresentation.read Solidity.Yul.Checks.LocalDefaultPostRepresentation.fault (Solidity.Yul.Checks.LocalDefaultPostRepresentation.yesProof ⟨true,false⟩) 5 (Solidity.Yul.Checks.LocalDefaultPostRepresentation.state (Solidity.Yul.Checks.LocalDefaultPostRepresentation.raw 1) world) = .halted .timeout (Solidity.Yul.Checks.LocalDefaultPostRepresentation.yesReached (Solidity.Yul.Checks.LocalDefaultPostRepresentation.raw 1) world) := by
  intro world; rfl

theorem postHaltKeepsWrite : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalDefaultPostRepresentation.env), Solidity.Yul.LocalDefaultPostIter.run Solidity.Yul.Checks.LocalDefaultPostRepresentation.read Solidity.Yul.Checks.LocalDefaultPostRepresentation.fault (Solidity.Yul.Checks.LocalDefaultPostRepresentation.yesProof ⟨true,false⟩) 6 (Solidity.Yul.Checks.LocalDefaultPostRepresentation.state (Solidity.Yul.Checks.LocalDefaultPostRepresentation.raw 1) world) = .halted .timeout (Solidity.Yul.Checks.LocalDefaultPostRepresentation.state Solidity.Yul.Checks.LocalDefaultPostRepresentation.cleanTrue world) := by
  intro world; rfl

theorem omittedGuardContinues : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalDefaultPostRepresentation.env), Solidity.Yul.LocalDefaultNoGuard.run Solidity.Yul.Checks.LocalDefaultPostRepresentation.setFalse (Solidity.Yul.Checks.LocalDefaultPostRepresentation.yesProof ⟨true,false⟩) 6 (Solidity.Yul.Checks.LocalDefaultPostRepresentation.state (Solidity.Yul.Checks.LocalDefaultPostRepresentation.raw 1) world) = .halted .timeout (Solidity.Yul.Checks.LocalDefaultPostRepresentation.yesReached Solidity.Yul.Checks.LocalDefaultPostRepresentation.cleanFalse world) := by
  intro world; rfl

theorem omittedPostContinues : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalDefaultPostRepresentation.env), Solidity.Yul.LocalDefaultNoGuard.runNoPost (Solidity.Yul.Checks.LocalDefaultPostRepresentation.yesProof ⟨true,false⟩) 6 (Solidity.Yul.Checks.LocalDefaultPostRepresentation.state (Solidity.Yul.Checks.LocalDefaultPostRepresentation.raw 1) world) = .halted .timeout (Solidity.Yul.Checks.LocalDefaultPostRepresentation.yesReached (Solidity.Yul.Checks.LocalDefaultPostRepresentation.raw 1) world) := by
  intro world; rfl

theorem zeroFuel : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalDefaultPostRepresentation.env), Solidity.Yul.LocalDefaultNoGuard.runNoPost (Solidity.Yul.Checks.LocalDefaultPostRepresentation.yesProof ⟨true,false⟩) 0 (Solidity.Yul.Checks.LocalDefaultPostRepresentation.state (Solidity.Yul.Checks.LocalDefaultPostRepresentation.raw 1) world) = .halted .timeout (Solidity.Yul.Checks.LocalDefaultPostRepresentation.state (Solidity.Yul.Checks.LocalDefaultPostRepresentation.raw 1) world) := by
  intro world; rfl

theorem dirtyProjectionRefused : ∀ (world : Solidity.Source.St Solidity.Yul.Checks.LocalDefaultPostRepresentation.env), Solidity.Yul.LocalBoolItems.project [.bool] (Solidity.Yul.LocalDefaultPostIter.run Solidity.Yul.Checks.LocalDefaultPostRepresentation.stop Solidity.Yul.Checks.LocalDefaultPostRepresentation.fault (Solidity.Yul.Checks.LocalDefaultPostRepresentation.yesProof ⟨true,false⟩) 2 (Solidity.Yul.Checks.LocalDefaultPostRepresentation.state (Solidity.Yul.Checks.LocalDefaultPostRepresentation.raw 1) world)) = none := by
  intro world; rfl

#print axioms Solidity.Yul.LocalDefaultPostRepresentation.postIter
#print axioms Solidity.Yul.LocalDefaultPostRepresentation.noGuard
#print axioms Solidity.Yul.LocalDefaultPostRepresentation.noGuardNoPost
#print axioms postWriteStopsGuard
#print axioms falsePostIgnored
#print axioms truePostIgnored
#print axioms skippedPost
#print axioms bodyHaltBeforePost
#print axioms postHaltKeepsWrite
#print axioms omittedGuardContinues
#print axioms omittedPostContinues
#print axioms zeroFuel
#print axioms dirtyProjectionRefused

end Solidity.Yul.Checks.LocalDefaultPostRepresentation
