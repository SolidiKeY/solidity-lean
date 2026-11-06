import SolidityBridge.HashBridge.CallQueries
import SolidityBridge.ExternalEvm.StaticcallDriver

/-! Query provenance for the existing fetched/checked STATICCALL boundary.
Child CODE-frame queries and subsequent caller-frame queries are SEPARATE
indices; this does not certify a complete flattened nested/global trace.
All actual checks, smaller fuels, effectful call states and terminal outcomes
come from the existing driver and call receipts, not a replacement evaluator. -/
namespace Solidity.HashBridge
open EvmYul EvmYul.EVM EvmYul.EVM.DriverProof

def StaticCodeQueryReceipt (fuel : Nat) (dest : Array UInt256) (s : EVM.State)
    (requested target inOffset inSize outOffset outSize : UInt256)
    (tail : Stack UInt256) (code : ByteArray)
    (childQueries callerQueries : List (List Nat))
    (result : Except ExecutionException (ExecutionResult EVM.State)) : Prop :=
  match fuel with
  | 0 => childQueries = [] ∧ callerQueries = [] ∧ result = .error .OutOfFuel
  | 1 => childQueries = [] ∧ callerQueries = [] ∧
      result = (do let _ ← staticGuard s; .error .OutOfFuel)
  | n+2 => match staticGuard s with
    | .error err => childQueries = [] ∧ callerQueries = [] ∧ result = .error err
    | .ok () => ∃ reply, CallCodeQueryReceipt n (staticCost s) s.executionEnv.blobVersionedHashes requested
            (.ofNat s.executionEnv.codeOwner) target target (.ofNat 0) (.ofNat 0)
            inOffset inSize outOffset outSize false
            {staticMemoryCharged s with execLength := s.execLength+1} code childQueries reply ∧
        match reply with
        | .error err => callerQueries = [] ∧ result = .error err
        | .ok (bit,out) => DriverQueryReceipt (n+1) dest (staticPost bit out tail) callerQueries result
theorem StaticCodeQueryReceipt.sound (fuel : Nat) (dest : Array UInt256) (s : EVM.State)
    (requested target inOffset inSize outOffset outSize : UInt256)
    (tail : Stack UInt256) (code : ByteArray)
    (childQueries callerQueries : List (List Nat))
    (result : Except ExecutionException (ExecutionResult EVM.State))
    (hf : fetched s = (.STATICCALL,none))
    (hs : s.stack = requested :: target :: inOffset :: inSize :: outOffset :: outSize :: tail)
    (hc : toExecute .EVM s.accountMap (AccountAddress.ofUInt256 target) = .Code code)
    (h : StaticCodeQueryReceipt fuel dest s requested target inOffset inSize outOffset outSize tail code
      childQueries callerQueries result) : X fuel dest s = result := by
  cases fuel with
  | zero => exact h.2.2.symm
  | succ f =>
    cases f with
    | zero =>
      rw [staticCut_exact 1 dest s hf]
      exact h.2.2.symm
    | succ n =>
      rw [staticCut_exact (n+2) dest s hf,
        staticCut_call n dest s requested target inOffset inSize outOffset outSize tail hs]
      cases hg : staticGuard s with
      | error err =>
        simp only [StaticCodeQueryReceipt,hg] at h
        simp only [Bind.bind,Except.bind]
        exact h.2.2.symm
      | ok tag =>
        cases tag
        simp only [StaticCodeQueryReceipt,hg] at h
        obtain ⟨reply,receipt,continuation⟩ := h
        have he : call n (staticCost s) s.executionEnv.blobVersionedHashes requested
            (.ofNat s.executionEnv.codeOwner) target target (.ofNat 0) (.ofNat 0)
            inOffset inSize outOffset outSize false
            {staticMemoryCharged s with execLength := s.execLength+1} = reply :=
          CallCodeQueryReceipt.sound n (staticCost s) s.executionEnv.blobVersionedHashes requested
            (.ofNat s.executionEnv.codeOwner) target target (.ofNat 0) (.ofNat 0)
            inOffset inSize outOffset outSize false
            {staticMemoryCharged s with execLength := s.execLength+1} code childQueries reply hc receipt
        simp only [Bind.bind,Except.bind]
        rw [he]
        cases reply with
        | error err => exact continuation.2.symm
        | ok pair =>
          rcases pair with ⟨bit,out⟩
          exact continuation.sound

/-- Public checked producer: no successful guard/call/step, chosen reply/world,
terminal certificate or table-membership premise. CODE selection stays raw. -/
theorem static_code_queries (fuel : Nat) (dest : Array UInt256) (s : EVM.State)
    (requested target inOffset inSize outOffset outSize : UInt256)
    (tail : Stack UInt256) (code : ByteArray)
    (hf : fetched s = (.STATICCALL,none))
    (hs : s.stack = requested :: target :: inOffset :: inSize :: outOffset :: outSize :: tail)
    (hc : toExecute .EVM s.accountMap (AccountAddress.ofUInt256 target) = .Code code) :
    ∃ childQueries callerQueries, StaticCodeQueryReceipt fuel dest s requested target
      inOffset inSize outOffset outSize tail code childQueries callerQueries (X fuel dest s) := by
  cases fuel with
  | zero => exact ⟨[],[],rfl,rfl,rfl⟩
  | succ f =>
    cases f with
    | zero => exact ⟨[],[],rfl,rfl,staticCut_exact 1 dest s hf⟩
    | succ n =>
      cases hg : staticGuard s with
      | error err =>
        have receipt : StaticCodeQueryReceipt (n+2) dest s requested target inOffset inSize
            outOffset outSize tail code [] [] (.error err) := by
          simp only [StaticCodeQueryReceipt,hg,true_and]
        refine ⟨[],[],?_⟩
        rw [StaticCodeQueryReceipt.sound (n+2) dest s requested target inOffset inSize outOffset
          outSize tail code [] [] _ hf hs hc receipt]
        exact receipt
      | ok tag =>
        cases tag
        obtain ⟨childQueries,child⟩ := call_code_queries n (staticCost s) s.executionEnv.blobVersionedHashes requested
            (.ofNat s.executionEnv.codeOwner) target target (.ofNat 0) (.ofNat 0)
            inOffset inSize outOffset outSize false
            {staticMemoryCharged s with execLength := s.execLength+1} code hc
        cases he : call n (staticCost s) s.executionEnv.blobVersionedHashes requested
            (.ofNat s.executionEnv.codeOwner) target target (.ofNat 0) (.ofNat 0)
            inOffset inSize outOffset outSize false
            {staticMemoryCharged s with execLength := s.execLength+1} with
        | error err =>
          rw [he] at child
          have receipt : StaticCodeQueryReceipt (n+2) dest s requested target inOffset inSize
              outOffset outSize tail code childQueries [] (.error err) := by
            simp only [StaticCodeQueryReceipt,hg]
            exact ⟨.error err,child,True.intro,rfl⟩
          refine ⟨childQueries,[],?_⟩
          rw [StaticCodeQueryReceipt.sound (n+2) dest s requested target inOffset inSize outOffset
            outSize tail code childQueries [] _ hf hs hc receipt]
          exact receipt
        | ok pair =>
          rcases pair with ⟨bit,out⟩
          rw [he] at child
          obtain ⟨callerQueries,continuation⟩ := driver_queries (n+1) dest (staticPost bit out tail)
          have receipt : StaticCodeQueryReceipt (n+2) dest s requested target inOffset inSize
              outOffset outSize tail code childQueries callerQueries
              (X (n+1) dest (staticPost bit out tail)) := by
            simp only [StaticCodeQueryReceipt,hg]
            exact ⟨.ok (bit,out),child,continuation⟩
          refine ⟨childQueries,callerQueries,?_⟩
          rw [StaticCodeQueryReceipt.sound (n+2) dest s requested target inOffset inSize outOffset
            outSize tail code childQueries callerQueries _ hf hs hc receipt]
          exact receipt

end Solidity.HashBridge
