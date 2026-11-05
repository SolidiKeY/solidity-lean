import Solidity.Yul.Views.RetainedLoopWriteback
import Solidity.Yul.Views.RetainedLoopImageControls

/-! The actual loop-derived image accepts a changed dormant-child snapshot.
The validated Source operation and pure writeback reconstruct the full changed
raw map; new payload ownership preserves high padding. This is finite agreement,
not allocator provenance, static authorization, or compiler execution adequacy. -/
namespace Solidity.Yul.Views.Controls

def rflwState (G : Source.Glob agEnv) (flag : Bool) := (rfliRun G flag).1.2.2.ex

theorem rflw_next_snapshot (G : Source.Glob agEnv) (flag : Bool) :
    (rfliImage G flag).snapshot rhNextRaw=rhNext := rfl

theorem rflw_checked (G : Source.Glob agEnv) (flag : Bool) :
    packedSeparationCheck ((rfliImage G flag).snapshot rhNextRaw)=true := rh_next_checked

theorem rflw_prepared (G : Source.Glob agEnv) (flag : Bool) :
    finiteAccountWrite? (T:=agEnv.lay) account ((rfliImage G flag).snapshot rhNextRaw) rhNextRaw=some rhOp :=
  Option.get_mem rh_op_ready

theorem rflw_connection (G : Source.Glob agEnv) (flag : Bool) :
    capturedSnapshotWriteback (rfliImage G flag) rhNextRaw ((rflwState G flag).world.accounts account).storage=
      some ((((rflwState G flag).apply rhOp).world.accounts account).storage,
        packedMask ((rfliImage G flag).snapshot rhNextRaw) rhNextRaw) :=
  RetainedLoopWriteback.account_connection (rfliImage G flag) rhNextRaw (rflwState G flag) rhOp
    (rflw_checked G flag) (rflw_prepared G flag)

theorem rflw_exists (G : Source.Glob agEnv) (flag : Bool) :
    (capturedSnapshotWriteback (rfliImage G flag) rhNextRaw ((rflwState G flag).world.accounts account).storage).isSome := by
  rfl

theorem rflw_reencode (G : Source.Glob agEnv) (flag : Bool) :
    finiteEncode ((rfliImage G flag).snapshot rhNextRaw)
      (((rflwState G flag).apply rhOp).world.accounts account).storage
      (packedMask ((rfliImage G flag).snapshot rhNextRaw) rhNextRaw)=some rhNextRaw :=
  RetainedLoopWriteback.account_reencode (rfliImage G flag) rhNextRaw (rflwState G flag) rhOp
    (rflw_checked G flag) (rflw_prepared G flag)

theorem rflw_changed : rhNextRaw≠rhRaw0 := by
  intro equal
  have at_slot := congrArg (fun raw : SlotView => (raw 101).val) equal
  change 3=2 at at_slot
  omega

theorem rflw_growth : rhRaw0 101=2 ∧ rhNextRaw 101=3 := by
  decide

/-- The third packed field becomes owned, while high padding remains residual. -/
theorem rflw_padding (G : Source.Glob agEnv) (flag : Bool) :
    packedMask ((rfliImage G flag).snapshot rhNextRaw) rhNextRaw 1000=⟨2^240,by decide⟩ := by
  rw [rflw_next_snapshot]
  decide

theorem rflw_stale_complement (G : Source.Glob agEnv) (flag : Bool) :
    packedMask rhOld rhRaw0 1000≠packedMask ((rfliImage G flag).snapshot rhNextRaw) rhNextRaw 1000 := by
  rw [rflw_next_snapshot]
  decide

end Solidity.Yul.Views.Controls
