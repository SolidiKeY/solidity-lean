import SolidityBridge.HashBridge.XiQueries

/-! Query refinement of the existing PUBLIC Theta CODE branch, including its
actual transfer preparation and failure/empty-map policy. Let expressions name
pinned terms in a Prop, not a second transfer/world/evaluator implementation.
Precompiled/native branches and descendant-query completeness are not claimed. -/
namespace Solidity.HashBridge
open EvmYul EvmYul.EVM EvmYul.EVM.DriverProof

def ThetaCodeQueryReceipt (fuel : Nat) (blobs : List ByteArray) (created : Batteries.RBSet AccountAddress compare)
    (genesis : BlockHeader) (blocks : ProcessedBlocks) (world snapshot : AccountMap .EVM)
    (accrued : Substate) (source origin recipient : AccountAddress) (code : ByteArray)
    (gas price value contextValue : UInt256) (data : ByteArray) (depth : Nat)
    (header : BlockHeader) (permission : Bool)
    (queries : List (List Nat)) (result : Except ExecutionException
      (Batteries.RBSet AccountAddress compare × AccountMap .EVM × UInt256 × Substate × Bool × ByteArray)) : Prop :=
  match fuel with
  | 0 => queries = [] ∧ result = .error .OutOfFuel
  | n+1 =>
    let credited := match world.find? recipient with
      | none => if value != (⟨0⟩ : UInt256) then
          world.insert recipient {(default : Account .EVM) with balance := value} else world
      | some account => world.insert recipient {account with balance := account.balance + value}
    let debited := match credited.find? source with
      | none => credited
      | some account => credited.insert source {account with balance := account.balance - value}
    let env : ExecutionEnv .EVM :=
      {codeOwner := recipient
       sender := origin
       gasPrice := price.toNat
       calldata := data
       source := source
       weiValue := contextValue
       depth := depth
       perm := permission
       code := code
       header := header
       blobVersionedHashes := blobs}
    ∃ child, XiQueryReceipt n created genesis blocks debited snapshot gas accrued env queries child ∧
      match child with
      | .error err => result = if err == .OutOfFuel then .error .OutOfFuel
          else .ok (created,world,.ofNat 0,accrued,false,.empty)
      | .ok (.revert refund bytes) => result = .ok (created,world,refund,accrued,false,bytes)
      | .ok (.success (childCreated,childWorld,refund,childAccrued) bytes) =>
          result = .ok (childCreated,(if childWorld == ∅ then world else childWorld),refund,
            (if childWorld == ∅ then accrued else childAccrued),true,bytes)
theorem ThetaCodeQueryReceipt.sound (fuel : Nat) (blobs : List ByteArray) (created : Batteries.RBSet AccountAddress compare)
    (genesis : BlockHeader) (blocks : ProcessedBlocks) (world snapshot : AccountMap .EVM)
    (accrued : Substate) (source origin recipient : AccountAddress) (code : ByteArray)
    (gas price value contextValue : UInt256) (data : ByteArray) (depth : Nat)
    (header : BlockHeader) (permission : Bool)
    (queries : List (List Nat)) (result : Except ExecutionException
      (Batteries.RBSet AccountAddress compare × AccountMap .EVM × UInt256 × Substate × Bool × ByteArray))
    (h : ThetaCodeQueryReceipt fuel blobs created genesis blocks world snapshot accrued
      source origin recipient code gas price value contextValue data depth header permission queries result) :
    Θ fuel blobs created genesis blocks world snapshot accrued source origin recipient (.Code code)
      gas price value contextValue data depth header permission = result := by
  cases fuel with
  | zero => exact h.2.symm
  | succ n =>
    obtain ⟨child,receipt,policy⟩ := h
    let credited := match world.find? recipient with
      | none => if value != (⟨0⟩ : UInt256) then
          world.insert recipient {(default : Account .EVM) with balance := value} else world
      | some account => world.insert recipient {account with balance := account.balance + value}
    let debited := match credited.find? source with
      | none => credited
      | some account => credited.insert source {account with balance := account.balance - value}
    let env : ExecutionEnv .EVM :=
      {codeOwner := recipient
       sender := origin
       gasPrice := price.toNat
       calldata := data
       source := source
       weiValue := contextValue
       depth := depth
       perm := permission
       code := code
       header := header
       blobVersionedHashes := blobs}
    have hrun : Ξ n created genesis blocks debited snapshot gas accrued env = child :=
      XiQueryReceipt.sound n created genesis blocks debited snapshot gas accrued env queries child receipt
    let finish : Except ExecutionException
        (ExecutionResult (Batteries.RBSet AccountAddress compare × AccountMap .EVM × UInt256 × Substate)) →
        Except ExecutionException (Batteries.RBSet AccountAddress compare × AccountMap .EVM × UInt256 × Substate × Bool × ByteArray) := fun out =>
      match out with
      | .error err => if err == .OutOfFuel then .error .OutOfFuel
          else .ok (created,world,UInt256.ofNat 0,accrued,false,ByteArray.empty)
      | .ok (.revert refund bytes) => .ok (created,world,refund,accrued,false,bytes)
      | .ok (.success (ca,cw,refund,aa) bytes) =>
          .ok (ca,(if cw == ∅ then world else cw),refund,(if cw == ∅ then accrued else aa),true,bytes)
    have actual : Θ (n+1) blobs created genesis blocks world snapshot accrued source origin recipient
        (.Code code) gas price value contextValue data depth header permission =
        finish (Ξ n created genesis blocks debited snapshot gas accrued env) := by
      simp only [Θ,Bind.bind,Except.bind,Pure.pure,Except.pure,ite_self]
      rfl
    rw [actual,hrun]
    cases child with
    | error err => exact policy.symm
    | ok outcome =>
      cases outcome with
      | revert refund bytes => exact policy.symm
      | success fields bytes =>
        rcases fields with ⟨ca,cw,refund,aa⟩
        exact policy.symm

/-- Produce the actual CODE receipt for every public fuel and child outcome.
No successful check, chosen Xi reply or destination membership is a premise. -/
theorem theta_code_queries (fuel : Nat) (blobs : List ByteArray) (created : Batteries.RBSet AccountAddress compare)
    (genesis : BlockHeader) (blocks : ProcessedBlocks) (world snapshot : AccountMap .EVM)
    (accrued : Substate) (source origin recipient : AccountAddress) (code : ByteArray)
    (gas price value contextValue : UInt256) (data : ByteArray) (depth : Nat)
    (header : BlockHeader) (permission : Bool) :
    ∃ queries, ThetaCodeQueryReceipt fuel blobs created genesis blocks world snapshot accrued
      source origin recipient code gas price value contextValue data depth header permission queries
      (Θ fuel blobs created genesis blocks world snapshot accrued source origin recipient (.Code code)
        gas price value contextValue data depth header permission) := by
  cases fuel with
  | zero => exact ⟨[],rfl,rfl⟩
  | succ n =>
    let credited := match world.find? recipient with
      | none => if value != (⟨0⟩ : UInt256) then
          world.insert recipient {(default : Account .EVM) with balance := value} else world
      | some account => world.insert recipient {account with balance := account.balance + value}
    let debited := match credited.find? source with
      | none => credited
      | some account => credited.insert source {account with balance := account.balance - value}
    let env : ExecutionEnv .EVM :=
      {codeOwner := recipient
       sender := origin
       gasPrice := price.toNat
       calldata := data
       source := source
       weiValue := contextValue
       depth := depth
       perm := permission
       code := code
       header := header
       blobVersionedHashes := blobs}
    let finish : Except ExecutionException
        (ExecutionResult (Batteries.RBSet AccountAddress compare × AccountMap .EVM × UInt256 × Substate)) →
        Except ExecutionException (Batteries.RBSet AccountAddress compare × AccountMap .EVM × UInt256 × Substate × Bool × ByteArray) := fun out =>
      match out with
      | .error err => if err == .OutOfFuel then .error .OutOfFuel
          else .ok (created,world,UInt256.ofNat 0,accrued,false,ByteArray.empty)
      | .ok (.revert refund bytes) => .ok (created,world,refund,accrued,false,bytes)
      | .ok (.success (ca,cw,refund,aa) bytes) =>
          .ok (ca,(if cw == ∅ then world else cw),refund,(if cw == ∅ then accrued else aa),true,bytes)
    let child := Ξ n created genesis blocks debited snapshot gas accrued env
    obtain ⟨queries,receipt⟩ := xi_queries n created genesis blocks debited snapshot gas accrued env
    have chosen : ThetaCodeQueryReceipt (n+1) blobs created genesis blocks world snapshot accrued
        source origin recipient code gas price value contextValue data depth header permission queries
        (finish child) := by
      refine ⟨child,receipt,?_⟩
      cases child with
      | error err => rfl
      | ok outcome =>
        cases outcome with
        | revert refund bytes => rfl
        | success fields bytes =>
          rcases fields with ⟨ca,cw,refund,aa⟩
          rfl
    refine ⟨queries,?_⟩
    rw [ThetaCodeQueryReceipt.sound (n+1) blobs created genesis blocks world snapshot accrued
      source origin recipient code gas price value contextValue data depth header permission queries
      (finish child) chosen]
    exact chosen

/-- Fixed message arguments and fuel determine the direct child-frame query
list even when different proof/result indices describe it. -/
theorem theta_code_query_unique (fuel : Nat) (blobs : List ByteArray) (created : Batteries.RBSet AccountAddress compare)
    (genesis : BlockHeader) (blocks : ProcessedBlocks) (world snapshot : AccountMap .EVM)
    (accrued : Substate) (source origin recipient : AccountAddress) (code : ByteArray)
    (gas price value contextValue : UInt256) (data : ByteArray) (depth : Nat)
    (header : BlockHeader) (permission : Bool)
    (queries queries' : List (List Nat)) (result result' : Except ExecutionException
      (Batteries.RBSet AccountAddress compare × AccountMap .EVM × UInt256 × Substate × Bool × ByteArray))
    (h : ThetaCodeQueryReceipt fuel blobs created genesis blocks world snapshot accrued
      source origin recipient code gas price value contextValue data depth header permission queries result)
    (h' : ThetaCodeQueryReceipt fuel blobs created genesis blocks world snapshot accrued
      source origin recipient code gas price value contextValue data depth header permission queries' result') :
    queries = queries' := by
  cases fuel with
  | zero => exact h.1.trans h'.1.symm
  | succ n =>
    obtain ⟨child,receipt,_⟩ := h
    obtain ⟨child',receipt',_⟩ := h'
    exact xi_query_receipt_unique n created genesis blocks _ snapshot gas accrued _
      queries queries' child child' receipt receipt'

end Solidity.HashBridge
