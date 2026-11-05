import SolidityBridge.HashBridge.XiContextRun
import SolidityBridge.HashBridge.ThetaQueries

/-! Public CODE-message client using the actual credited/debited world and
constructed environment. The named view below repeats Theta's input record,
not a transfer/world evaluator; receipt construction checks the match against
existing semantics. Source installation, call guards and native hashing are
separate. No supplied successful child result or prepared-world equality. -/
namespace Solidity.HashBridge.XiContext
open EvmYul EvmYul.EVM EvmYul.EVM.DriverProof

structure MessageInputs where
  blobs : List ByteArray
  created : Batteries.RBSet AccountAddress compare
  genesis : BlockHeader
  blocks : ProcessedBlocks
  world : AccountMap .EVM
  snapshot : AccountMap .EVM
  accrued : Substate
  source : AccountAddress
  origin : AccountAddress
  recipient : AccountAddress
  price : UInt256
  value : UInt256
  contextValue : UInt256
  data : ByteArray
  depth : Nat
  header : BlockHeader
  permission : Bool

def prepared (m : MessageInputs) : Inputs :=
  let credited := match m.world.find? m.recipient with
    | none => if m.value != (⟨0⟩ : UInt256) then
        m.world.insert m.recipient {(default : Account .EVM) with balance := m.value} else m.world
    | some account => m.world.insert m.recipient {account with balance := account.balance + m.value}
  let debited := match credited.find? m.source with
    | none => credited
    | some account => credited.insert m.source {account with balance := account.balance - m.value}
  {created := m.created
   genesis := m.genesis
   blocks := m.blocks
   world := debited
   snapshot := m.snapshot
   accrued := m.accrued
   environment :=
     {codeOwner := m.recipient
      sender := m.origin
      source := m.source
      gasPrice := m.price.toNat
      calldata := m.data
      weiValue := m.contextValue
      depth := m.depth
      perm := m.permission
      code := program
      header := m.header
      blobVersionedHashes := m.blobs}}

abbrev message (fuel : Nat) (m : MessageInputs) (gas : UInt256) :=
  Θ fuel m.blobs m.created m.genesis m.blocks m.world m.snapshot m.accrued
    m.source m.origin m.recipient (.Code program) gas m.price m.value m.contextValue
    m.data m.depth m.header m.permission

abbrev messageReceipt (fuel : Nat) (m : MessageInputs) (gas : UInt256)
    (queries : List (List Nat)) (result : Except ExecutionException
      (Batteries.RBSet AccountAddress compare × AccountMap .EVM × UInt256 × Substate × Bool × ByteArray)) :=
  ThetaCodeQueryReceipt fuel m.blobs m.created m.genesis m.blocks m.world m.snapshot m.accrued
    m.source m.origin m.recipient program gas m.price m.value m.contextValue
    m.data m.depth m.header m.permission queries result

def returnedWorld (m : MessageInputs) : AccountMap .EVM :=
  if (prepared m).world == ∅ then m.world else (prepared m).world

/-- All account lookup/value/same-account cases remain in the exact preparation
expression. The empty-map fallback is retained, never assumed false. This
selects CODE explicitly; it does not prove an installed account's toExecute. -/
theorem prepared_message (fuel : Nat) (m : MessageInputs) :
    messageReceipt (fuel+7) m (.ofNat 34) [query (prepared m)]
      (.ok (m.created,returnedWorld m,.ofNat 0,m.accrued,true,.empty)) ∧
      message (fuel+7) m (.ofNat 34) =
      .ok (m.created,returnedWorld m,.ofNat 0,m.accrued,true,.empty) := by
  have child : XiQueryReceipt (fuel+6) m.created m.genesis m.blocks (prepared m).world
      m.snapshot (.ofNat 34) m.accrued (prepared m).environment [query (prepared m)]
      (.ok (.success (m.created,(prepared m).world,.ofNat 0,m.accrued) .empty)) :=
    (completed_invocation fuel (prepared m) rfl).1
  have result : messageReceipt (fuel+7) m (.ofNat 34) [query (prepared m)]
      (.ok (m.created,returnedWorld m,.ofNat 0,m.accrued,true,.empty)) := by
    refine ⟨.ok (.success (m.created,(prepared m).world,UInt256.ofNat 0,m.accrued) .empty),child,?_⟩
    simp only [returnedWorld,ite_self]
  exact ⟨result,result.sound⟩
end Solidity.HashBridge.XiContext
