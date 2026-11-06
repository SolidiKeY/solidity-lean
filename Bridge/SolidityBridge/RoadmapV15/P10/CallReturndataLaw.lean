import SolidityBridge.RoadmapV15.P10.FrozenWitness

/-! General post-CALL return-buffer law over the frozen P10 API.

`call_returnData` unfolds the pinned `EVM.call`: on success its result's return
buffer is either empty (the callee is not entered) or exactly the output of
`Θ` run on `toExecute .EVM σ t`, the callee's code in the caller's account map.
`fetched_call_returnData` lifts this through
`FrozenV1.api.charged.checked_call` to every fetched CALL site. The caller's
previous buffer is never kept. Nothing about the callee's execution, gas or
world adequacy is asserted; `Θ` stays unevaluated. -/
namespace SolidityBridge.RoadmapV15.P10.CallReturndataLaw
open Solidity Solidity.Backend EvmYul Solidity.Evm.External

/-- On success, the CALL result's return buffer is empty or the callee output
of `Θ` on the callee code `toExecute .EVM s.accountMap t`. -/
theorem call_returnData (fuel gasCost : Nat) (bvh : List ByteArray)
    (gas source recipient t value value' inOffset inSize outOffset outSize : UInt256)
    (perm : Bool) (s : EVM.State) (x : UInt256) (r : EVM.State)
    (h : EVM.call fuel gasCost bvh gas source recipient t value value' inOffset inSize
      outOffset outSize perm s = .ok (x, r)) :
    r.returnData = .empty ∨
      ∃ (f : Nat) (A : Substate) (src org rcpt : AccountAddress) (g p : UInt256) (d : ByteArray)
        (e : Nat) (H : BlockHeader) (cA : Batteries.RBSet AccountAddress compare)
        (σ' : AccountMap .EVM) (g' : UInt256) (A' : Substate) (z : Bool),
        fuel = f + 1 ∧
        EVM.Θ f bvh s.createdAccounts s.genesisBlockHeader s.blocks s.accountMap s.σ₀ A src org rcpt
          (toExecute .EVM s.accountMap (AccountAddress.ofUInt256 t)) g p value value' d e H perm =
          .ok (cA, σ', g', A', z, r.returnData) := by
  cases fuel with
  | zero => cases h
  | succ f =>
    simp only [EVM.call, bind, Except.bind, pure, Except.pure] at h
    split at h
    · split at h
      · cases h
      · rename_i res heq
        obtain ⟨cA,σ',g',A',z,o⟩ := res
        cases h
        exact .inr ⟨f,_,_,_,_,_,_,_,_,_,cA,σ',g',A',z,rfl,heq⟩
    · cases h
      exact .inl rfl

/-- Every fetched CALL step that succeeds leaves the callee's return buffer:
empty, or the `Θ` output for the callee code in the charged account map. -/
theorem fetched_call_returnData (site : Site .CALL) (valid : Array UInt256) (fuel : Nat)
    (next : EVM.State) (h : Assembly.driverSteps 1 (fuel+2) valid site.state = .ok next) :
    ∃ (charged : EVM.State) (cost : Nat) (tail : Stack UInt256)
      (gas recipient value inOffset inSize outOffset outSize : UInt256),
      Assembly.driverGate valid site.state .CALL = .ok (charged, cost) ∧
      charged.stack.pop7 = some (tail,gas,recipient,value,inOffset,inSize,outOffset,outSize) ∧
      (next.returnData = .empty ∨
        ∃ (f : Nat) (A : Substate) (src org rcpt : AccountAddress) (g p : UInt256)
          (d : ByteArray) (e : Nat) (H : BlockHeader)
          (cA : Batteries.RBSet AccountAddress compare)
          (σ' : AccountMap .EVM) (g' : UInt256) (A' : Substate) (z : Bool),
          EVM.Θ f charged.executionEnv.blobVersionedHashes charged.createdAccounts
            charged.genesisBlockHeader charged.blocks charged.accountMap charged.σ₀ A src org rcpt
            (toExecute .EVM charged.accountMap (AccountAddress.ofUInt256 recipient)) g p value value
            d e H charged.executionEnv.perm =
            .ok (cA, σ', g', A', z, next.returnData)) := by
  rw [FrozenV1.api.charged.checked_call] at h
  cases hg : Assembly.driverGate valid site.state .CALL with
  | error err => simp only [hg] at h; cases h
  | ok pair =>
    obtain ⟨charged,cost⟩ := pair
    cases hp : charged.stack.pop7 with
    | none => simp only [hg,hp] at h; cases h
    | some vals =>
      obtain ⟨tail,gas,recipient,value,inOffset,inSize,outOffset,outSize⟩ := vals
      simp only [hg,hp,Except.map] at h
      split at h
      · cases h
      · rename_i res heq
        obtain ⟨x,r⟩ := res
        cases h
        refine ⟨charged,cost,tail,gas,recipient,value,inOffset,inSize,outOffset,outSize,rfl,hp,?_⟩
        rcases call_returnData _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ heq with empty | ⟨f,A,src,org,rcpt,g,p,d,e,H,cA,σ',g',A',z,_,run⟩
        · exact .inl empty
        · exact .inr ⟨f,A,src,org,rcpt,g,p,d,e,H,cA,σ',g',A',z,run⟩

/-- info: 'SolidityBridge.RoadmapV15.P10.CallReturndataLaw.call_returnData' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms call_returnData
/-- info: 'SolidityBridge.RoadmapV15.P10.CallReturndataLaw.fetched_call_returnData' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms fetched_call_returnData

end SolidityBridge.RoadmapV15.P10.CallReturndataLaw
