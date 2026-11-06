import Solidity.Yul.Views.RetainedLoopSequence
import Solidity.Yul.Views.RetainedLoopFrameControls

/-! Fresh actual Source sequencing grows a dormant child2to3 then shrinks3to1.
Released payload bytes enter the new complement. Source cells outside the
second snapshot remain untouched; these facts do not form new references or
establish allocator/compiler adequacy. -/
namespace Solidity.Yul.Views.Controls

def rflqRaw := saveSlot rhNextRaw 101 1
def rflqSnapshot := rhImage.snapshot rflqRaw

theorem rflq_checked : packedSeparationCheck rflqSnapshot=true := by
  decide

theorem rflq_ready : (finiteAccountWrite? (T:=agEnv.lay) account rflqSnapshot rflqRaw).isSome := by
  decide

def rflqOp : Source.Op agEnv.layout agEnv.lay agEnv.lay :=
  (finiteAccountWrite? (T:=agEnv.lay) account rflqSnapshot rflqRaw).get rflq_ready

def rflqRun (G : Source.Glob agEnv) (flag : Bool) :=
  (RetainedLoopSequence.writeTwiceThenHalt (E:=agEnv) (Γ:=[]) packedStepFrame rhOp rflqOp .timeout).run
    (rflswState G flag)

def rflqStatic (G : Source.Glob agEnv) (flag : Bool) :=
  (RetainedLoopSequence.writeTwiceThenHalt (E:=agEnv) (Γ:=[]) rflswStaticFrame rhOp rflqOp .timeout).run
    (rflswState G flag)

theorem rflq_prepared (G : Source.Glob agEnv) (flag : Bool) :
    finiteAccountWrite? (T:=agEnv.lay) account ((rfliImage G flag).snapshot rflqRaw) rflqRaw=some rflqOp :=
  Option.get_mem rflq_ready

theorem rflq_result (G : Source.Glob agEnv) (flag : Bool) :
    rflqRun G flag=(.error .timeout,((rflswState G flag).1,
      {(rflswState G flag).2 with ex := ((rflswState G flag).2.ex.apply rhOp).apply rflqOp})) :=
  RetainedLoopSequence.run packedStepFrame rhOp rflqOp (rflswState G flag) .timeout rfl

theorem rflq_reencode (G : Source.Glob agEnv) (flag : Bool) :
    finiteEncode ((rfliImage G flag).snapshot rflqRaw) ((rflqRun G flag).2.2.ex.world.accounts account).storage
      (packedMask ((rfliImage G flag).snapshot rflqRaw) rflqRaw)=some rflqRaw :=
  RetainedLoopSequence.final_reencode packedStepFrame (rfliImage G flag) rflqRaw (rflswState G flag)
    rhOp rflqOp .timeout rfl rflq_checked (rflq_prepared G flag)

theorem rflq_inventory (G : Source.Glob agEnv) (flag : Bool) :
    (rfliImage G flag).sourceInventory? (F:=packedStepFrame) (rflqRun G flag).2=
      some ((rfliImage G flag).snapshot rflqRaw) :=
  RetainedLoopSequence.final_inventory packedStepFrame (rfliImage G flag) rflqRaw (rflswState G flag)
    rhOp rflqOp .timeout rfl rflq_checked (rflq_prepared G flag)

theorem rflq_journal (G : Source.Glob agEnv) (flag : Bool) :
    (rflqRun G flag).2.2.ex.journal.length=(rflswState G flag).2.ex.journal.length+2 := by
  rfl

theorem rflq_lengths : rhRaw0 101=2 ∧ rhNextRaw 101=3 ∧ rflqRaw 101=1 := by
  decide

theorem rflq_count (G : Source.Glob agEnv) (flag : Bool) :
    ((rfliImage G flag).snapshot rflqRaw).length=4 := by
  rfl

theorem rflq_released (G : Source.Glob agEnv) (flag : Bool) :
    packedMask ((rfliImage G flag).snapshot rflqRaw) rflqRaw 1000=⟨88*65536+77*2^32+2^240,by decide⟩ := by
  change packedMask rflqSnapshot rflqRaw 1000=⟨88*65536+77*2^32+2^240,by decide⟩
  decide

theorem rflq_stale_complement (G : Source.Glob agEnv) (flag : Bool) :
    packedMask ((rfliImage G flag).snapshot rhNextRaw) rhNextRaw 1000≠
      packedMask ((rfliImage G flag).snapshot rflqRaw) rflqRaw 1000 := by
  change packedMask rhNext rhNextRaw 1000≠packedMask rflqSnapshot rflqRaw 1000
  decide

theorem rflq_static (G : Source.Glob agEnv) (flag : Bool) :
    rflqStatic G flag=(.error (.revert []),rflswState G flag) := by
  rfl

/-- The removed third payload is outside the final four-entry snapshot. -/
theorem rflq_removed_unselected (G : Source.Glob agEnv) (flag : Bool) :
    ∀ c∈(rfliImage G flag).snapshot rflqRaw, (agInner 0).go (.index 2)≠c.path := by
  intro c member
  change c∈[_,_,_,_] at member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl <;> decide

/-- Stored payload survives shrink; this does not grant a live index access. -/
theorem rflq_retained_cell (G : Source.Glob agEnv) (flag : Bool) :
    ((rflqRun G flag).2.2.ex.world.accounts account).storage.cell ((agInner 0).go (.index 2))=
      ((rflswRun G flag).2.2.ex.world.accounts account).storage.cell ((agInner 0).go (.index 2)) := by
  have preserved := finiteAccountWrite_other account ((rfliImage G flag).snapshot rflqRaw) rflqRaw
    ((rflswState G flag).2.ex.apply rhOp) rflqOp (rflq_prepared G flag)
    ((agInner 0).go (.index 2)) (rflq_removed_unselected G flag)
  simpa only [rflq_result,rflsw_success] using preserved

end Solidity.Yul.Views.Controls
