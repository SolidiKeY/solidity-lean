import SolidityBridge.RoadmapV15.P10.FrozenWitness

/-! General post-CALL return-buffer law over the frozen P10 API.

`call_returnData` unfolds the pinned `EVM.call`. When it does not error, either
the entry condition `entered` holds (enough caller balance, depth below 1024)
and the result's return buffer is the sixth component of `calleeRun`, the exact
`Θ` invocation `EVM.call` makes, with every input pinned (callee code
`toExecute .EVM σ t`, substate with `t` accessed, source, origin, recipient,
`Ccallgas` gas, gas price, values, input window read with padding, depth + 1,
header and permission); or `entered` fails and the buffer is empty.
`fetched_call_returnData` lifts this through
`FrozenV1.api.charged.checked_call` to every fetched CALL site.

The conclusion is stated without reference to the caller's previous buffer.
`Θ` stays unevaluated: nothing about the callee's execution, its output being
nonempty, gas or world adequacy is asserted. -/
namespace SolidityBridge.RoadmapV15.P10.CallReturndataLaw
open Solidity Solidity.Backend EvmYul Solidity.Evm.External

/-- The caller state after the CALL's gas charge, as `EVM.call` builds it. -/
def callState (s : EVM.State) (gasCost : Nat) : EVM.State :=
  {s with gasAvailable := s.gasAvailable - UInt256.ofNat gasCost}

/-- `EVM.call`'s entry condition: enough caller balance and depth below 1024. -/
def entered (value : UInt256) (s : EVM.State) : Prop :=
  value ≤ (s.accountMap.find? s.executionEnv.codeOwner |>.option ⟨0⟩ (·.balance)) ∧
    s.executionEnv.depth < 1024

/-- The exact `Θ` invocation of `EVM.call (f+1)`. -/
def calleeRun (f gasCost : Nat) (bvh : List ByteArray)
    (gas source recipient t value value' inOffset inSize : UInt256) (perm : Bool)
    (s : EVM.State) :=
  EVM.Θ f bvh (callState s gasCost).createdAccounts (callState s gasCost).genesisBlockHeader
    (callState s gasCost).blocks s.accountMap (callState s gasCost).σ₀
    ((callState s gasCost).addAccessedAccount (AccountAddress.ofUInt256 t)).substate
    (AccountAddress.ofUInt256 source) (callState s gasCost).executionEnv.sender
    (AccountAddress.ofUInt256 recipient) (toExecute .EVM s.accountMap (AccountAddress.ofUInt256 t))
    (.ofNat (EVM.Ccallgas (AccountAddress.ofUInt256 t) (AccountAddress.ofUInt256 recipient)
      value gas s.accountMap s.toMachineState s.substate))
    (.ofNat (callState s gasCost).executionEnv.gasPrice) value value'
    ((callState s gasCost).memory.readWithPadding inOffset.toNat inSize.toNat)
    (s.executionEnv.depth + 1) (callState s gasCost).executionEnv.header perm

/-- A non-erroring CALL result's return buffer is the callee output of the
exact `Θ` run when `entered` holds, and empty otherwise. -/
theorem call_returnData (f gasCost : Nat) (bvh : List ByteArray)
    (gas source recipient t value value' inOffset inSize outOffset outSize : UInt256)
    (perm : Bool) (s : EVM.State) (x : UInt256) (r : EVM.State)
    (h : EVM.call (f+1) gasCost bvh gas source recipient t value value' inOffset inSize
      outOffset outSize perm s = .ok (x, r)) :
    (entered value s ∧
      ∃ (cA : Batteries.RBSet AccountAddress compare) (σ' : AccountMap .EVM) (g' : UInt256)
        (A' : Substate) (z : Bool),
        calleeRun f gasCost bvh gas source recipient t value value' inOffset inSize perm s =
          .ok (cA, σ', g', A', z, r.returnData)) ∨
    (¬ entered value s ∧ r.returnData = .empty) := by
  simp only [EVM.call, bind, Except.bind, pure, Except.pure] at h
  split at h
  · rename_i hcond
    split at h
    · cases h
    · rename_i res heq
      obtain ⟨cA,σ',g',A',z,o⟩ := res
      cases h
      exact .inl ⟨hcond,cA,σ',g',A',z,heq⟩
  · rename_i hcond
    cases h
    exact .inr ⟨hcond,rfl⟩

/-- Every non-erroring fetched CALL step: the actual gate and seven popped
operands, positive call fuel, and the return buffer given by `call_returnData`
on the state `EVM.call` receives. -/
theorem fetched_call_returnData (site : Site .CALL) (valid : Array UInt256) (fuel : Nat)
    (next : EVM.State) (h : Assembly.driverSteps 1 (fuel+2) valid site.state = .ok next) :
    ∃ (charged : EVM.State) (cost : Nat) (tail : Stack UInt256)
      (gas recipient value inOffset inSize outOffset outSize : UInt256) (f : Nat),
      Assembly.driverGate valid site.state .CALL = .ok (charged, cost) ∧
      charged.stack.pop7 = some (tail,gas,recipient,value,inOffset,inSize,outOffset,outSize) ∧
      fuel = f + 1 ∧
      ((entered value {charged with execLength := charged.execLength+1} ∧
        ∃ (cA : Batteries.RBSet AccountAddress compare) (σ' : AccountMap .EVM) (g' : UInt256)
          (A' : Substate) (z : Bool),
          calleeRun f cost charged.executionEnv.blobVersionedHashes gas
            (.ofNat charged.executionEnv.codeOwner) recipient recipient value value inOffset inSize
            charged.executionEnv.perm {charged with execLength := charged.execLength+1} =
            .ok (cA, σ', g', A', z, next.returnData)) ∨
       (¬ entered value {charged with execLength := charged.execLength+1} ∧
        next.returnData = .empty)) := by
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
        cases fuel with
        | zero => cases heq
        | succ f =>
          have law := call_returnData _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ heq
          exact ⟨charged,cost,tail,gas,recipient,value,inOffset,inSize,outOffset,outSize,f,rfl,hp,rfl,law⟩

/-- info: 'SolidityBridge.RoadmapV15.P10.CallReturndataLaw.call_returnData' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms call_returnData
/-- info: 'SolidityBridge.RoadmapV15.P10.CallReturndataLaw.fetched_call_returnData' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms fetched_call_returnData

end SolidityBridge.RoadmapV15.P10.CallReturndataLaw
