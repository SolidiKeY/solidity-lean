import Solidity.Yul.Views.RetainedLoopRefresh
import Solidity.Yul.Views.RetainedLoopSourceSubControls

/-! Actual changed Source stores refresh the loop-derived inventory, including
a newly owned third payload cell. A later ordinary halt keeps this refresh.
Reusing the old inventory shape is rejected; no allocator/EVM adequacy is claimed. -/
namespace Solidity.Yul.Views.Controls

theorem rflrf_inventory (G : Source.Glob agEnv) (flag : Bool) :
    (rfliImage G flag).sourceInventory? (F:=packedStepFrame) (rflswRun G flag).2=
      some ((rfliImage G flag).snapshot rhNextRaw) :=
  RetainedLoopRefresh.source_snapshot packedStepFrame (rfliImage G flag) rhNextRaw (rflswState G flag)
    rhOp rfl (rflw_checked G flag) (rflw_prepared G flag)

theorem rflrf_halt_inventory (G : Source.Glob agEnv) (flag : Bool) :
    (rfliImage G flag).sourceInventory? (F:=packedStepFrame) (rflsubRun G flag).2=
      some ((rfliImage G flag).snapshot rhNextRaw) :=
  RetainedLoopRefresh.halt_snapshot packedStepFrame (rfliImage G flag) rhNextRaw agShrink.2.1 Source.Locals.nil
    (rflswState G flag).2 rhOp .timeout rfl (rflw_checked G flag) (rflw_prepared G flag)

theorem rflrf_unchanged (G : Source.Glob agEnv) (flag : Bool) :
    capturedSnapshotWriteback (rfliImage G flag) rhNextRaw ((rflswRun G flag).2.2.ex.world.accounts account).storage=
      some (((rflswRun G flag).2.2.ex.world.accounts account).storage,
        packedMask ((rfliImage G flag).snapshot rhNextRaw) rhNextRaw) :=
  RetainedLoopRefresh.source_unchanged packedStepFrame (rfliImage G flag) rhNextRaw (rflswState G flag)
    rhOp rfl (rflw_checked G flag) (rflw_prepared G flag)

theorem rflrf_counts (G : Source.Glob agEnv) (flag : Bool) :
    ((rfliImage G flag).snapshot rhRaw0).length=5 ∧ ((rfliImage G flag).snapshot rhNextRaw).length=6 := by
  exact ⟨rfl,rfl⟩

theorem rflrf_third (G : Source.Glob agEnv) (flag : Bool) :
    ∃ c∈(rfliImage G flag).snapshot rhNextRaw,
      c.path=(agInner 0).go (.index 2) ∧ c.slot=1000 ∧ c.field.offset=4 ∧ c.field.width=2 := by
  rw [rflw_next_snapshot]
  change ∃ c∈[_,_,_,_,_,_], _
  refine ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))), ?_⟩
  decide

theorem rflrf_shape_change (G : Source.Glob agEnv) (flag : Bool) :
    (rfliImage G flag).snapshot rhRaw0≠(rfliImage G flag).snapshot rhNextRaw := by
  intro same
  have size := congrArg List.length same
  have counts := rflrf_counts G flag
  rw [counts.1,counts.2] at size
  omega

theorem rflrf_stale_inventory (G : Source.Glob agEnv) (flag : Bool) :
    (rfliImage G flag).sourceInventory? (F:=packedStepFrame) (rflswRun G flag).2≠
      some ((rfliImage G flag).snapshot rhRaw0) := by
  rw [rflrf_inventory]
  intro same
  exact rflrf_shape_change G flag (Option.some.inj same).symm

end Solidity.Yul.Views.Controls
