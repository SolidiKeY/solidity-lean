import SolidityBridge.HashBridge.ThetaQueries
import SolidityBridge.HashBridge.XiControls

/-! Constructed public-message control. The actual initialized bare child fails
underflow; Theta handles it and retains the pre-message checkpoint. Transfer
value and transaction snapshot are arbitrary, not equated to the rollback map.
This is a kernel control, not a native/source or caller-funds-admission test. -/
namespace Solidity.HashBridge.ThetaControls
open EvmYul EvmYul.EVM EvmYul.EVM.DriverProof

theorem bare_code_handled (created : Batteries.RBSet AccountAddress compare)
    (genesis : BlockHeader) (blocks : ProcessedBlocks) (world snapshot : AccountMap .EVM)
    (accrued : Substate) (value : UInt256) :
    let env := XiControls.bareHashEnv
    ThetaCodeQueryReceipt 3 env.blobVersionedHashes created genesis blocks world snapshot accrued
      env.source env.sender env.codeOwner env.code (.ofNat 30) (.ofNat 0) value env.weiValue
      env.calldata env.depth env.header false []
      (.ok (created,world,.ofNat 0,accrued,false,.empty)) ∧
    Θ 3 env.blobVersionedHashes created genesis blocks world snapshot accrued
      env.source env.sender env.codeOwner (.Code env.code) (.ofNat 30) (.ofNat 0) value env.weiValue
      env.calldata env.depth env.header false =
      .ok (created,world,.ofNat 0,accrued,false,.empty) := by
  let env := XiControls.bareHashEnv
  let credited := match world.find? env.codeOwner with
    | none => if value != (⟨0⟩ : UInt256) then
        world.insert env.codeOwner {(default : Account .EVM) with balance := value} else world
    | some account => world.insert env.codeOwner {account with balance := account.balance + value}
  let debited := match credited.find? env.source with
    | none => credited
    | some account => credited.insert env.source {account with balance := account.balance - value}
  have child : XiQueryReceipt 2 created genesis blocks debited snapshot (.ofNat 30) accrued env []
      (.error .StackUnderflow) :=
    (XiControls.bare_hash_refused created genesis blocks debited snapshot accrued).1
  have receipt : ThetaCodeQueryReceipt 3 env.blobVersionedHashes created genesis blocks world snapshot accrued
      env.source env.sender env.codeOwner env.code (.ofNat 30) (.ofNat 0) value env.weiValue
      env.calldata env.depth env.header false []
      (.ok (created,world,.ofNat 0,accrued,false,.empty)) :=
    ⟨.error .StackUnderflow,child,rfl⟩
  exact ⟨receipt,ThetaCodeQueryReceipt.sound 3 env.blobVersionedHashes created genesis blocks world snapshot accrued
    env.source env.sender env.codeOwner env.code (.ofNat 30) (.ofNat 0) value env.weiValue
    env.calldata env.depth env.header false [] _ receipt⟩

end Solidity.HashBridge.ThetaControls
