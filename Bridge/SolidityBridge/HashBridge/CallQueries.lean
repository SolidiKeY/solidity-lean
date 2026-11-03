import SolidityBridge.HashBridge.ThetaQueries

/-! Actual call-to-CODE query provenance. This Prop-only receipt observes
original call guards and reply installation; it is not an evaluator, transfer
implementation or caller admission judgment. CODE selection stays explicit.
The callee's full response is distinct from its min-sized output-memory copy. -/
namespace Solidity.HashBridge
open EvmYul EvmYul.EVM EvmYul.EVM.DriverProof

def CallCodeQueryReceipt (fuel cost : Nat) (blobs : List ByteArray)
    (requested source recipient target value contextValue inOffset inSize outOffset outSize : UInt256)
    (permission : Bool) (s : EVM.State) (code : ByteArray)
    (queries : List (List Nat)) (result : Except ExecutionException (UInt256 × EVM.State)) : Prop :=
  match fuel with
  | 0 => queries = [] ∧ result = .error .OutOfFuel
  | n+1 =>
    let callgas := Ccallgas (AccountAddress.ofUInt256 target) (AccountAddress.ofUInt256 recipient)
      value requested s.accountMap s.toMachineState s.substate
    let debited : EVM.State := {s with gasAvailable := s.gasAvailable - UInt256.ofNat cost}
    let accrued := (debited.addAccessedAccount (AccountAddress.ofUInt256 target)).substate
    let finish := fun (reply : Batteries.RBSet AccountAddress compare × AccountMap .EVM ×
        UInt256 × Substate × Bool × ByteArray) =>
      let (created,world,refund,substate,ok,bytes) := reply
      let written := writeBytes bytes 0 debited.toMachineState outOffset.toNat
        (min outSize (UInt256.ofNat bytes.size)).toNat
      let notEnoughFunds : Bool := value >
        (s.accountMap.find? debited.executionEnv.codeOwner |>.elim (UInt256.ofNat 0) (·.balance))
      let bit : UInt256 := if !ok || notEnoughFunds || debited.executionEnv.depth == 1024
        then ⟨0⟩ else ⟨1⟩
      let machine : MachineState := {written with
        returnData := bytes
        gasAvailable := written.gasAvailable + refund
        activeWords := .ofNat (MachineState.M
          (MachineState.M debited.activeWords.toNat inOffset.toNat inSize.toNat)
          outOffset.toNat outSize.toNat)}
      (bit,{{debited with accountMap := world, substate := substate, createdAccounts := created}
        with toMachineState := machine})
    if value ≤ (s.accountMap.find? s.executionEnv.codeOwner |>.option ⟨0⟩ (·.balance)) ∧
        s.executionEnv.depth < 1024 then
      ∃ reply, ThetaCodeQueryReceipt n blobs debited.createdAccounts debited.genesisBlockHeader debited.blocks
        s.accountMap debited.σ₀ accrued (AccountAddress.ofUInt256 source) debited.executionEnv.sender
        (AccountAddress.ofUInt256 recipient) code (.ofNat callgas) (.ofNat debited.executionEnv.gasPrice)
        value contextValue (debited.memory.readWithPadding inOffset.toNat inSize.toNat)
        (s.executionEnv.depth+1) debited.executionEnv.header permission queries reply ∧
        result = (do let value ← reply; pure (finish value))
    else queries = [] ∧ result = .ok (finish
      (debited.createdAccounts,debited.accountMap,.ofNat callgas,accrued,false,.empty))
theorem CallCodeQueryReceipt.sound (fuel cost : Nat) (blobs : List ByteArray)
    (requested source recipient target value contextValue inOffset inSize outOffset outSize : UInt256)
    (permission : Bool) (s : EVM.State) (code : ByteArray)
    (queries : List (List Nat)) (result : Except ExecutionException (UInt256 × EVM.State))
    (hc : toExecute .EVM s.accountMap (AccountAddress.ofUInt256 target) = .Code code)
    (h : CallCodeQueryReceipt fuel cost blobs requested source recipient target value contextValue
      inOffset inSize outOffset outSize permission s code queries result) :
    call fuel cost blobs requested source recipient target value contextValue
      inOffset inSize outOffset outSize permission s = result := by
  cases fuel with
  | zero => exact h.2.symm
  | succ n =>
    let callgas := Ccallgas (AccountAddress.ofUInt256 target) (AccountAddress.ofUInt256 recipient)
      value requested s.accountMap s.toMachineState s.substate
    let debited : EVM.State := {s with gasAvailable := s.gasAvailable - UInt256.ofNat cost}
    let accrued := (debited.addAccessedAccount (AccountAddress.ofUInt256 target)).substate
    let finish := fun (reply : Batteries.RBSet AccountAddress compare × AccountMap .EVM ×
        UInt256 × Substate × Bool × ByteArray) =>
      let (created,world,refund,substate,ok,bytes) := reply
      let written := writeBytes bytes 0 debited.toMachineState outOffset.toNat
        (min outSize (UInt256.ofNat bytes.size)).toNat
      let notEnoughFunds : Bool := value >
        (s.accountMap.find? debited.executionEnv.codeOwner |>.elim (UInt256.ofNat 0) (·.balance))
      let bit : UInt256 := if !ok || notEnoughFunds || debited.executionEnv.depth == 1024
        then ⟨0⟩ else ⟨1⟩
      let machine : MachineState := {written with
        returnData := bytes
        gasAvailable := written.gasAvailable + refund
        activeWords := .ofNat (MachineState.M
          (MachineState.M debited.activeWords.toNat inOffset.toNat inSize.toNat)
          outOffset.toNat outSize.toNat)}
      (bit,{{debited with accountMap := world, substate := substate, createdAccounts := created}
        with toMachineState := machine})
    by_cases guard : value ≤ (s.accountMap.find? s.executionEnv.codeOwner |>.option ⟨0⟩ (·.balance)) ∧
        s.executionEnv.depth < 1024
    · change (if _ then _ else _) at h
      rw [if_pos guard] at h
      obtain ⟨reply,receipt,project⟩ := h
      have hr : Θ n blobs debited.createdAccounts debited.genesisBlockHeader debited.blocks
        s.accountMap debited.σ₀ accrued (AccountAddress.ofUInt256 source) debited.executionEnv.sender
        (AccountAddress.ofUInt256 recipient) (.Code code) (.ofNat callgas) (.ofNat debited.executionEnv.gasPrice)
        value contextValue (debited.memory.readWithPadding inOffset.toNat inSize.toNat)
        (s.executionEnv.depth+1) debited.executionEnv.header permission = reply :=
        ThetaCodeQueryReceipt.sound n blobs debited.createdAccounts debited.genesisBlockHeader debited.blocks
        s.accountMap debited.σ₀ accrued (AccountAddress.ofUInt256 source) debited.executionEnv.sender
        (AccountAddress.ofUInt256 recipient) code (.ofNat callgas) (.ofNat debited.executionEnv.gasPrice)
        value contextValue (debited.memory.readWithPadding inOffset.toNat inSize.toNat)
        (s.executionEnv.depth+1) debited.executionEnv.header permission queries reply receipt
      have actual : call (n+1) cost blobs requested source recipient target value contextValue
          inOffset inSize outOffset outSize permission s = (do
            let reply ← Θ n blobs debited.createdAccounts debited.genesisBlockHeader debited.blocks
                s.accountMap debited.σ₀ accrued (AccountAddress.ofUInt256 source) debited.executionEnv.sender
                (AccountAddress.ofUInt256 recipient) (.Code code) (.ofNat callgas) (.ofNat debited.executionEnv.gasPrice)
                value contextValue (debited.memory.readWithPadding inOffset.toNat inSize.toNat)
                (s.executionEnv.depth+1) debited.executionEnv.header permission
            pure (finish reply)) := by
        simp only [call,if_pos guard,hc,Bind.bind,Except.bind,Pure.pure,Except.pure]
        rfl
      rw [actual,hr]
      exact project.symm
    · change (if _ then _ else _) at h
      rw [if_neg guard] at h
      have actual : call (n+1) cost blobs requested source recipient target value contextValue
          inOffset inSize outOffset outSize permission s = .ok (finish
            (debited.createdAccounts,debited.accountMap,.ofNat callgas,accrued,false,.empty)) := by
        simp only [call,if_neg guard,Bind.bind,Except.bind,Pure.pure,Except.pure]
        rfl
      exact actual.trans h.2.symm

/-- Actual call producer for every fuel and both funds/depth branches. CODE
selection is a raw account lookup premise, not source/child installation. -/
theorem call_code_queries (fuel cost : Nat) (blobs : List ByteArray)
    (requested source recipient target value contextValue inOffset inSize outOffset outSize : UInt256)
    (permission : Bool) (s : EVM.State) (code : ByteArray)
    (hc : toExecute .EVM s.accountMap (AccountAddress.ofUInt256 target) = .Code code) :
    ∃ queries, CallCodeQueryReceipt fuel cost blobs requested source recipient target value contextValue
      inOffset inSize outOffset outSize permission s code queries
      (call fuel cost blobs requested source recipient target value contextValue
        inOffset inSize outOffset outSize permission s) := by
  cases fuel with
  | zero => exact ⟨[],rfl,rfl⟩
  | succ n =>
    let callgas := Ccallgas (AccountAddress.ofUInt256 target) (AccountAddress.ofUInt256 recipient)
      value requested s.accountMap s.toMachineState s.substate
    let debited : EVM.State := {s with gasAvailable := s.gasAvailable - UInt256.ofNat cost}
    let accrued := (debited.addAccessedAccount (AccountAddress.ofUInt256 target)).substate
    let finish := fun (reply : Batteries.RBSet AccountAddress compare × AccountMap .EVM ×
        UInt256 × Substate × Bool × ByteArray) =>
      let (created,world,refund,substate,ok,bytes) := reply
      let written := writeBytes bytes 0 debited.toMachineState outOffset.toNat
        (min outSize (UInt256.ofNat bytes.size)).toNat
      let notEnoughFunds : Bool := value >
        (s.accountMap.find? debited.executionEnv.codeOwner |>.elim (UInt256.ofNat 0) (·.balance))
      let bit : UInt256 := if !ok || notEnoughFunds || debited.executionEnv.depth == 1024
        then ⟨0⟩ else ⟨1⟩
      let machine : MachineState := {written with
        returnData := bytes
        gasAvailable := written.gasAvailable + refund
        activeWords := .ofNat (MachineState.M
          (MachineState.M debited.activeWords.toNat inOffset.toNat inSize.toNat)
          outOffset.toNat outSize.toNat)}
      (bit,{{debited with accountMap := world, substate := substate, createdAccounts := created}
        with toMachineState := machine})
    by_cases guard : value ≤ (s.accountMap.find? s.executionEnv.codeOwner |>.option ⟨0⟩ (·.balance)) ∧
        s.executionEnv.depth < 1024
    · obtain ⟨queries,message⟩ := theta_code_queries n blobs debited.createdAccounts debited.genesisBlockHeader debited.blocks
        s.accountMap debited.σ₀ accrued (AccountAddress.ofUInt256 source) debited.executionEnv.sender
        (AccountAddress.ofUInt256 recipient) code (.ofNat callgas) (.ofNat debited.executionEnv.gasPrice)
        value contextValue (debited.memory.readWithPadding inOffset.toNat inSize.toNat)
        (s.executionEnv.depth+1) debited.executionEnv.header permission
      let reply := Θ n blobs debited.createdAccounts debited.genesisBlockHeader debited.blocks
        s.accountMap debited.σ₀ accrued (AccountAddress.ofUInt256 source) debited.executionEnv.sender
        (AccountAddress.ofUInt256 recipient) (.Code code) (.ofNat callgas) (.ofNat debited.executionEnv.gasPrice)
        value contextValue (debited.memory.readWithPadding inOffset.toNat inSize.toNat)
        (s.executionEnv.depth+1) debited.executionEnv.header permission
      have receipt : CallCodeQueryReceipt (n+1) cost blobs requested source recipient target value contextValue
          inOffset inSize outOffset outSize permission s code queries
          (do let value ← reply; pure (finish value)) := by
        change (if _ then _ else _)
        rw [if_pos guard]
        exact ⟨reply,message,rfl⟩
      refine ⟨queries,?_⟩
      rw [CallCodeQueryReceipt.sound (n+1) cost blobs requested source recipient target value contextValue
        inOffset inSize outOffset outSize permission s code queries _ hc receipt]
      exact receipt
    · have receipt : CallCodeQueryReceipt (n+1) cost blobs requested source recipient target value contextValue
          inOffset inSize outOffset outSize permission s code [] (.ok (finish
            (debited.createdAccounts,debited.accountMap,.ofNat callgas,accrued,false,.empty))) := by
        change (if _ then _ else _)
        rw [if_neg guard]
        exact ⟨rfl,rfl⟩
      refine ⟨[],?_⟩
      rw [CallCodeQueryReceipt.sound (n+1) cost blobs requested source recipient target value contextValue
        inOffset inSize outOffset outSize permission s code [] _ hc receipt]
      exact receipt

end Solidity.HashBridge
