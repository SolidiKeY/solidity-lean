import Solidity.Backend.AbiEntry.CoreJoin.Shared
import Solidity.Backend.AbiEntry.SelectorBranches

/-! Existing compiler correctness supplies normal return, revert or fault from
represented core inputs. The actual join therefore preserves the full outcome,
without a desired execution or normal-return premise. -/
namespace Solidity.Backend.AbiEntry.CoreJoin
open Solidity.Evm
variable {C : Contract} {Γ Δ : Ctx}

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

/-- info: 'Solidity.Backend.AbiEntry.CoreJoin.branch_outcome' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms branch_outcome
/-- info: 'Solidity.Backend.AbiEntry.CoreJoin.certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms certificate
end Solidity.Backend.AbiEntry.CoreJoin
