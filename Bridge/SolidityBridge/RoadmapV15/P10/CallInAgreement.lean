import SolidityBridge.RoadmapV15.P10.CallReturndataLaw
import Solidity.Evm.MachineV2

/-! The core `CALLIN` return buffer (`Evm.callIn_returndata`, version-2 core
machine) against the reference `EVM.call` buffer
(`CallReturndataLaw.call_returnData`).

Both have the same shape: an entered call leaves the callee's output, a call
not entered leaves an empty buffer. `callIn_agrees` is a case alignment: under
`hbal` (the two entry tests coincide) and depth below 1024, the entered and
not-entered branches line up; in the entered branch the buffer equality is the
oracle premise `hreply` itself, and in the other branch both buffers are empty.

* **Depth.** The reference enters only below depth 1024 (`entered`); the core
  has no depth. `depth_disagreement` proves that at depth 1024, with a covered
  core value and a nonempty reply, the two buffers differ.
* **Gas and world.** The reference output is the sixth component of the exact
  `Θ` run (`calleeRun`): it reads the forwarded `Ccallgas` gas, depth + 1,
  the account map, substate and header. The core output is
  `reply callee value input`, which reads none of them. `hreply` is a premise
  about that one `Θ` run, only when the call is entered; no uniformity across
  states is proved or assumed.
* **Operands.** `hbal` relates only the entry tests (core `bal self` against
  `v`, reference `codeOwner` balance against `value`). The core value, callee
  and input bytes (`readBytes` of whole cells) are not tied to the reference
  `value`, `t`/`recipient` or `readWithPadding` window; that correspondence is
  carried entirely by `hreply`. The theorem holds for every `EVM.call` use
  (CALL, CALLCODE, DELEGATECALL, STATICCALL).
* **Not compared.** The pushed success flag (core `accepts`, reference `x`),
  post-call balances (the core pays nothing on a self-call; the reference
  moves value inside `Θ`), the core ghost journal `calls`, and gas.

The reference call's own errors (fuel, `Θ`) are excluded by its `.ok`
hypothesis. `callInStep` never errors; `InstrV2.callIn` itself faults when
`readBytes` fails, which is outside this theorem since `input` is given. No
callee execution, Source origin or compiler image is supplied. -/
namespace SolidityBridge.RoadmapV15.P10.CallInAgreement
open Solidity EvmYul SolidityBridge.RoadmapV15.P10.CallReturndataLaw

/-- **Case alignment.** When the two entry tests coincide, depth is below
1024 and, if the call is entered, the oracle reply equals the exact `Θ`
output, the core `CALLIN` buffer is the reference CALL's buffer, byte for
byte. -/
theorem callIn_agrees (m : Evm.MachineV2) (v a : Fin Evm.W) (input : List UInt8)
    (st : List Evm.Word) (f gasCost : Nat) (bvh : List ByteArray)
    (gas source recipient t value value' inOffset inSize outOffset outSize : UInt256)
    (perm : Bool) (s : EVM.State) (x : UInt256) (r : EVM.State)
    (hcall : EVM.call (f+1) gasCost bvh gas source recipient t value value' inOffset inSize
      outOffset outSize perm s = .ok (x, r))
    (hbal : v.1 ≤ m.base.bal m.base.self ↔
      value ≤ (s.accountMap.find? s.executionEnv.codeOwner |>.option ⟨0⟩ (·.balance)))
    (hdepth : s.executionEnv.depth < 1024)
    (hreply : entered value s → ∀ (cA : Batteries.RBSet AccountAddress compare) (σ' : AccountMap .EVM)
      (g' : UInt256) (A' : Substate) (z : Bool) (o : ByteArray),
      calleeRun f gasCost bvh gas source recipient t value value' inOffset inSize perm s =
        .ok (cA, σ', g', A', z, o) → m.reply a v input = o.data.toList) :
    ∃ m', Evm.callInStep m v a input st = .ok m' 0 ∧ m'.returndata = r.returnData.data.toList := by
  obtain ⟨m', hstep, hcases, -⟩ := Evm.callIn_returndata m v a input st
  refine ⟨m', hstep, ?_⟩
  rcases call_returnData _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hcall with
    ⟨hent, cA, σ', g', A', z, hrun⟩ | ⟨hnot, hempty⟩
  · have hrep := hreply hent
    simp only [entered] at hent
    have hv : v.1 ≤ m.base.bal m.base.self := hbal.2 hent.1
    rcases hcases with ⟨_, hrd, _⟩ | ⟨hlt, _, _⟩
    · rw [hrd]
      exact hrep _ _ _ _ _ _ hrun
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

/-- **Depth, core side.** A covered core `CALLIN` leaves the oracle's reply;
the core machine has no depth to test. -/
theorem core_ignores_depth (m : Evm.MachineV2) (v a : Fin Evm.W) (input : List UInt8)
    (st : List Evm.Word) (hv : v.1 ≤ m.base.bal m.base.self) :
    ∃ m', Evm.callInStep m v a input st = .ok m' 0 ∧ m'.returndata = m.reply a v input := by
  obtain ⟨m', hstep, hcases, -⟩ := Evm.callIn_returndata m v a input st
  refine ⟨m', hstep, ?_⟩
  rcases hcases with ⟨_, hrd, _⟩ | ⟨hlt, _, _⟩
  · exact hrd
  · exact absurd hv (Nat.not_le.2 hlt)

/-- **The depth difference.** At reference depth 1024, with a covered core
value and a nonempty reply, the core buffer differs from the reference buffer
of every non-erroring reference CALL. -/
theorem depth_disagreement (m : Evm.MachineV2) (v a : Fin Evm.W) (input : List UInt8)
    (st : List Evm.Word) (f gasCost : Nat) (bvh : List ByteArray)
    (gas source recipient t value value' inOffset inSize outOffset outSize : UInt256)
    (perm : Bool) (s : EVM.State) (x : UInt256) (r : EVM.State)
    (hcall : EVM.call (f+1) gasCost bvh gas source recipient t value value' inOffset inSize
      outOffset outSize perm s = .ok (x, r))
    (hdepth : s.executionEnv.depth = 1024) (hv : v.1 ≤ m.base.bal m.base.self)
    (hnonempty : m.reply a v input ≠ []) :
    ∃ m', Evm.callInStep m v a input st = .ok m' 0 ∧ m'.returndata ≠ r.returnData.data.toList := by
  obtain ⟨m', hstep, hrd⟩ := core_ignores_depth m v a input st hv
  refine ⟨m', hstep, ?_⟩
  rw [hrd, reference_depth_limit _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hcall hdepth]
  exact hnonempty

/-- info: 'SolidityBridge.RoadmapV15.P10.CallInAgreement.callIn_agrees' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms callIn_agrees
/-- info: 'SolidityBridge.RoadmapV15.P10.CallInAgreement.reference_depth_limit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms reference_depth_limit
/-- info: 'SolidityBridge.RoadmapV15.P10.CallInAgreement.core_ignores_depth' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms core_ignores_depth
/-- info: 'SolidityBridge.RoadmapV15.P10.CallInAgreement.depth_disagreement' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms depth_disagreement

end SolidityBridge.RoadmapV15.P10.CallInAgreement
