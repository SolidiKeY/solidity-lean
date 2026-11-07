import SolidityBridge.RoadmapV15.P10.CallReturndataLaw
import Solidity.Evm.MachineV2

/-! The core `CALLIN` return buffer (`Evm.callIn_returndata`, version-2 core
machine) against the reference `EVM.call` buffer
(`CallReturndataLaw.call_returnData`).

Both have the same shape: an entered call leaves the callee's output, a call
not entered leaves an empty buffer. They differ in three explicit places,
each a premise or a theorem here rather than an assumption:

* **Depth.** The reference enters only below depth 1024 (`entered`); the core
  has no depth. `callIn_agrees` takes `depth < 1024`; at depth 1024
  `reference_depth_limit` shows the reference buffer is empty while
  `core_ignores_depth` shows the core buffer is the oracle's reply.
* **Gas and world.** The reference output is the sixth component of the exact
  `Θ` run (`calleeRun`): it reads the forwarded `Ccallgas` gas, depth + 1,
  the account map, substate and header. The core output is
  `reply callee value input`, which reads none of them. `callIn_agrees`
  therefore asks the oracle to agree with that one `Θ` run (`hreply`); one
  oracle can serve several reference states only where their callee output
  coincides. No such uniformity is proved or assumed.
* **Balance and input.** The entry balances are related by the premise
  `hbal`; the core input (`readBytes` of whole cells) and the reference
  input (`readWithPadding` of the byte window) are related only through
  `hreply`.

The reference call's own errors (fuel, `Θ` failures) are excluded by its
`.ok` hypothesis; the core step never errors. No callee execution, Source
origin or compiler image is supplied. -/
namespace SolidityBridge.RoadmapV15.P10.CallInAgreement
open Solidity EvmYul SolidityBridge.RoadmapV15.P10.CallReturndataLaw

/-- **Transport.** Under matching entry balances, depth below 1024 and an
oracle that agrees with the exact `Θ` run, the core `CALLIN` buffer is the
reference CALL's buffer, byte for byte. -/
theorem callIn_agrees (m : Evm.MachineV2) (v a : Fin Evm.W) (input : List UInt8)
    (st : List Evm.Word) (f gasCost : Nat) (bvh : List ByteArray)
    (gas source recipient t value value' inOffset inSize outOffset outSize : UInt256)
    (perm : Bool) (s : EVM.State) (x : UInt256) (r : EVM.State)
    (hcall : EVM.call (f+1) gasCost bvh gas source recipient t value value' inOffset inSize
      outOffset outSize perm s = .ok (x, r))
    (hbal : v.1 ≤ m.base.bal m.base.self ↔
      value ≤ (s.accountMap.find? s.executionEnv.codeOwner |>.option ⟨0⟩ (·.balance)))
    (hdepth : s.executionEnv.depth < 1024)
    (hreply : ∀ (cA : Batteries.RBSet AccountAddress compare) (σ' : AccountMap .EVM)
      (g' : UInt256) (A' : Substate) (z : Bool) (o : ByteArray),
      calleeRun f gasCost bvh gas source recipient t value value' inOffset inSize perm s =
        .ok (cA, σ', g', A', z, o) → m.reply a v input = o.data.toList) :
    ∃ m', Evm.callInStep m v a input st = .ok m' 0 ∧ m'.returndata = r.returnData.data.toList := by
  obtain ⟨m', hstep, hcases, -⟩ := Evm.callIn_returndata m v a input st
  refine ⟨m', hstep, ?_⟩
  rcases call_returnData _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hcall with
    ⟨hent, cA, σ', g', A', z, hrun⟩ | ⟨hnot, hempty⟩
  · simp only [entered] at hent
    have hv : v.1 ≤ m.base.bal m.base.self := hbal.2 hent.1
    rcases hcases with ⟨_, hrd, _⟩ | ⟨hlt, _, _⟩
    · rw [hrd]
      exact hreply _ _ _ _ _ _ hrun
    · exact absurd hv (Nat.not_le.2 hlt)
  · simp only [entered] at hnot
    have hv : ¬ v.1 ≤ m.base.bal m.base.self := fun hv => hnot ⟨hbal.1 hv, hdepth⟩
    rcases hcases with ⟨hle, _, _⟩ | ⟨_, hrd, _⟩
    · exact absurd hle hv
    · rw [hrd, hempty]
      rfl

/-- **Depth, reference side.** At depth 1024 a non-erroring reference CALL
leaves an empty buffer, whatever the callee and balance. -/
theorem reference_depth_limit (f gasCost : Nat) (bvh : List ByteArray)
    (gas source recipient t value value' inOffset inSize outOffset outSize : UInt256)
    (perm : Bool) (s : EVM.State) (x : UInt256) (r : EVM.State)
    (hcall : EVM.call (f+1) gasCost bvh gas source recipient t value value' inOffset inSize
      outOffset outSize perm s = .ok (x, r))
    (hdepth : s.executionEnv.depth = 1024) :
    r.returnData = .empty := by
  rcases call_returnData _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hcall with
    ⟨hent, -⟩ | ⟨-, hempty⟩
  · simp only [entered] at hent
    omega
  · exact hempty

/-- **Depth, core side.** A covered core `CALLIN` leaves the oracle's reply,
with no depth condition. -/
theorem core_ignores_depth (m : Evm.MachineV2) (v a : Fin Evm.W) (input : List UInt8)
    (st : List Evm.Word) (hv : v.1 ≤ m.base.bal m.base.self) :
    ∃ m', Evm.callInStep m v a input st = .ok m' 0 ∧ m'.returndata = m.reply a v input := by
  obtain ⟨m', hstep, hcases, -⟩ := Evm.callIn_returndata m v a input st
  refine ⟨m', hstep, ?_⟩
  rcases hcases with ⟨_, hrd, _⟩ | ⟨hlt, _, _⟩
  · exact hrd
  · exact absurd hv (Nat.not_le.2 hlt)

/-- info: 'SolidityBridge.RoadmapV15.P10.CallInAgreement.callIn_agrees' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms callIn_agrees
/-- info: 'SolidityBridge.RoadmapV15.P10.CallInAgreement.reference_depth_limit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms reference_depth_limit
/-- info: 'SolidityBridge.RoadmapV15.P10.CallInAgreement.core_ignores_depth' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms core_ignores_depth

end SolidityBridge.RoadmapV15.P10.CallInAgreement
