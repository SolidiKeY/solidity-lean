import Solidity.Backend.InternalFlow.RuntimeFrameP1BridgeV2
import Solidity.Evm.MachineV2Controls

/-! Witnesses and negative controls for `P1BridgeV2`.

* Both frame classes are inhabited by admitted inputs (`admitted_true`,
  `admitted_false`), for every contract, with the flag at cell `3`; the
  reverting one exits with the payload on both sides (`revert_witness`).
* The data is observed: the version-2 observation of the reverting input is
  not a bare revert (`not_bare`), and the source distinguishes a bare revert
  from a revert with data (`source_distinguishes`).
* A cell that does not represent the flag is refused (`refused_mismatch`).
* An image with another payload breaks the agreement on an admitted input
  (`other_payload_disagrees`), so the bridge is not insensitive to data.
* The target language shows call events: a version-2 run with a journaled
  `CALLIN` that then reverts shows the call and its answer before the
  revert (`events_observed`). -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.P1BridgeV2.Controls
open Evm P1LangV2 P1BridgeV2
open Solidity.Roadmap (Event Outcome Prefix)
open Solidity.Roadmap.G49Final (BridgeGoal)

/-- A caller whose flag is `b`. -/
def caller (C : Contract) (b : Bool) : State C Γ := (State.init C).push b

/-- A machine whose cell `3` holds the flag `b`. -/
def machine (b : Bool) : MachineV2 :=
  MachineV2.ofBase { Machine.init with mem := upd (fun _ => w[0]) 3 (.val (bword b)) }

def input (C : Contract) (b : Bool) : Input C Γ := ⟨0, 16, caller C b, fun _ => ⟨0, W_pos⟩, machine b, 10⟩

theorem admitted_input (C : Contract) (b : Bool) : admitted C 3 (input C b) :=
  ⟨by unfold W; decide, by simp only [ReprV, input, machine, MachineV2.ofBase, upd_same]; rfl⟩

theorem admitted_true (C : Contract) : (A C 3).Allowed (input C true) ∧ (B C 3).Allowed (input C true) :=
  ⟨admitted_input C true, admitted_input C true⟩

theorem admitted_false (C : Contract) :
    (A C 3).Allowed (input C false) ∧ (B C 3).Allowed (input C false) :=
  ⟨admitted_input C false, admitted_input C false⟩

/-- The reverting admitted input: both sides exit with the payload. -/
theorem revert_witness (C : Contract) :
    sourcePrefix ((guard C).run (input C false).caller) = ⟨[], some (.revert data)⟩ ∧
      targetSem (image 3) (input C false) = ⟨[], some (.revert data)⟩ :=
  ⟨source_false _ rfl, target_false _ (admitted_input C false) rfl⟩

/-- The succeeding admitted input. -/
theorem success_witness (C : Contract) :
    targetSem (image 3) (input C true) = ⟨[], some (.success [])⟩ :=
  target_true _ (admitted_input C true) rfl

/-- The observation is not the coarse one: the payload is shown. -/
theorem not_bare (C : Contract) :
    targetSem (image 3) (input C false) ≠ ⟨[], some (.revert [])⟩ := by
  rw [(revert_witness C).2]
  intro h
  cases h

/-- The source tells a bare revert from a revert with data. -/
theorem source_distinguishes {C : Contract} {Δ : Ctx} {H : HTy} :
    sourcePrefix (.error .revert : TRes (Solidity.Out C H Δ)) ≠
      sourcePrefix (.error (.revertWith data) : TRes (Solidity.Out C H Δ)) := by
  intro h
  cases h

/-- A cell that does not represent the flag is refused. -/
theorem refused_mismatch (C : Contract) :
    ¬ admitted C 3 ⟨0, 16, caller C true, fun _ => ⟨0, W_pos⟩, machine false, 10⟩ := by
  intro h
  have h2 := h.2
  have hf : TEnv.get .here (caller C true).env = true := rfl
  simp only [ReprV, machine, MachineV2.ofBase, upd_same, hf, Word.val.injEq, bword_inj] at h2
  cases h2

/-- An image with another payload: `0xdeadbeef`. -/
def otherImage (cell : Nat) : List InstrV2 :=
  [.base (.mload cell), .base (.jumpi 5),
   .base (.push (.val ⟨0xdeadbeef * 2 ^ 224, by unfold W; decide⟩)), .base (.mstore cell),
   .base (.push (.val ⟨4, by unfold W; decide⟩)), .base (.push (.val (wmod cell))), .revertData]

theorem other_payload_disagrees (C : Contract) :
    targetSem (otherImage 3) (input C false) ≠ sourcePrefix ((guard C).run (input C false).caller) := by
  rw [source_false _ rfl]
  have h : (runV2 (otherImage 3) (machine false)).revertView = some ([], [0xde, 0xad, 0xbe, 0xef]) := by
    decide +kernel
  have hr := OutV2.eq_revertView h
  intro e
  have hf := congrArg Prefix.final e
  simp only [targetSem, input, hr, targetPrefix, Option.some.injEq, Outcome.revert.injEq] at hf
  exact absurd hf (by decide)

/-- The contract's own address in the fixtures. -/
def self0 : Fin W := ⟨0, W_pos⟩

/-- Call events are observed, and kept across the revert that follows. -/
theorem events_observed :
    targetPrefix self0 0
        (runV2 MachineV2Controls.callThenRevert (MachineV2Controls.machineWith [1, 2, 3, 4])) =
      ⟨callEvents (MachineV2Controls.entry [1, 2, 3, 4]), some (.revert [1, 2, 3, 4])⟩ := by
  rw [MachineV2Controls.joint_witness]
  rfl

/-- **Journal offset**: from a machine that already journaled one call, only
the call made by this run is an event. -/
theorem offset_drops_old :
    targetPrefix self0 1 (runV2 MachineV2Controls.callThenRevert
        { MachineV2Controls.machineWith [1, 2, 3, 4] with
          calls := [MachineV2Controls.entry [9]] }) =
      ⟨callEvents (MachineV2Controls.entry [1, 2, 3, 4]), some (.revert [1, 2, 3, 4])⟩ := by
  have h : (runV2 MachineV2Controls.callThenRevert
      { MachineV2Controls.machineWith [1, 2, 3, 4] with
        calls := [MachineV2Controls.entry [9]] }).revertView =
      some ([MachineV2Controls.entry [9], MachineV2Controls.entry [1, 2, 3, 4]], [1, 2, 3, 4]) := by
    decide +kernel
  rw [OutV2.eq_revertView h]
  rfl

/-- **A self-call is no event**: the same run, observed as the contract at
the callee's address `7`, shows none. -/
theorem self_call_internal :
    (targetPrefix ⟨7, by unfold W; decide⟩ 0
        (runV2 MachineV2Controls.callThenRevert (MachineV2Controls.machineWith [1, 2, 3, 4]))).events =
      [] := by
  rw [MachineV2Controls.joint_witness]
  rfl

/-- A source panic shows `Panic(0x01)`'s data, not a bare revert. -/
theorem panic_data {C : Contract} {Δ : Ctx} {H : HTy} :
    sourcePrefix (.error .panic : TRes (Solidity.Out C H Δ)) =
      ⟨[], some (.revert (Semantics.encodePanic 1))⟩ ∧
    sourcePrefix (.error .panic : TRes (Solidity.Out C H Δ)) ≠
      sourcePrefix (.error .revert : TRes (Solidity.Out C H Δ)) := by
  refine ⟨rfl, ?_⟩
  intro h
  simp only [sourcePrefix, Prefix.mk.injEq, Option.some.injEq, Outcome.revert.injEq,
    true_and] at h
  cases h

/-- Joint satisfiability of the bridge with its `Local` for every contract. -/
theorem satisfiable (C : Contract) :
    Nonempty (BridgeGoal (A C 3) (B C 3) () () id (fun _ _ => ()) (Local C 3)) :=
  ⟨p1_frame_bridge C 3⟩

end Solidity.Backend.InternalFlow.RuntimeFrame.P1BridgeV2.Controls

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.P1BridgeV2.p1_frame_bridge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.P1BridgeV2.p1_frame_bridge
