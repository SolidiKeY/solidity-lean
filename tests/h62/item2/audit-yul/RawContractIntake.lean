import Solidity.Yul.RawCoherent

/-! Routed Raw contract intake: a pure Tier-A logical-local execution must
preserve every observation of its existing Source world, and completed results
must retain their full authoritative snapshot. These are conditional frame
laws, not physical-layout adequacy, dirty-frame coherence, memory/storage
execution or a physical/compiler adapter instance. -/
namespace Solidity.Yul.RawContractIntake

theorem world_observation_frame {ctx control α}
    (code : Stmt [] (localExternalTypes ctx) control 0)
    (policy : Policy.StmtP .A code) (fuel : Nat) (state : RawFrame.State ctx)
    (result : RawFrame.Outcome ctx control) (observe : Source.St ctx.env → α)
    (done : RawFrame.run code policy fuel state=some result) :
    observe result.state.world=observe state.world :=
  congrArg observe (RawFrame.preserves code policy fuel state done).2

theorem completed_materialized_snapshot {ctx control}
    (code : Stmt [] (localExternalTypes ctx) control 0)
    (policy : Policy.StmtP .A code) (fuel : Nat) (state : RawFrame.State ctx)
    (result : RawFrame.Outcome ctx control)
    (done : RawFrame.run code policy fuel state=some result) :
    RawFrame.capture result.state
      (localWordCells ctx (RawFrame.materialize result.state).1)=result.state := by
  rw [RawFrame.materialize_view]
  exact RawFrame.run_captured ctx control code policy fuel state result done

/-- Completion is exhibited for every supplied raw frame; the frame laws do
not certify an evaluator which rejects every pure skip program. -/
theorem skip_completes {ctx control} (state : RawFrame.State ctx) :
    ∃ result : RawFrame.Outcome ctx control,
      RawFrame.run (Stmt.skip : Stmt [] (localExternalTypes ctx) control 0)
        True.intro 1 state=some result := by
  exact ⟨_,rfl⟩

end Solidity.Yul.RawContractIntake
