import Solidity.Yul.Adapters.P6CopyHistory
import Solidity.Yul.Adapters.P6CopySourceControls

/-! Real typed copy sequences refresh Source after each accepted copy. A failed
canonical preparation retains its already-copied overlapping bytes and prior
Source prefix; blindly replaying pending is intentionally NOT a resume API. -/
namespace Solidity.Yul.Adapters.P6CopyHistory.Controls
open Solidity.Yul.Views Solidity.Yul.Views.NominalInventory
open Solidity.Backend Solidity.Backend.MemoryOps.Physical Solidity.Evm.TryByteImage
open P6CopyPreparation.Controls

def owned : SpanPair 512 := ⟨src,⟨dst,rfl⟩⟩
def dirty : SpanPair 512 :=
  ⟨⟨lenU 127 (by decide),lenU 64 (by decide),Or.inr (by decide)⟩,
    ⟨⟨lenU 128 (by decide),lenU 64 (by decide),Or.inr (by decide)⟩,rfl⟩⟩
def later : SpanPair 512 :=
  ⟨⟨lenU 128 (by decide),lenU 32 (by decide),Or.inr (by decide)⟩,
    ⟨⟨lenU 300 (by decide),lenU 32 (by decide),Or.inr (by decide)⟩,rfl⟩⟩
def stopped := run UnchangedControls.placement 512 UnchangedControls.state
  SnapshotControls.mixedCursor image rfl [owned,dirty,later]
def reversed := run UnchangedControls.placement 512 UnchangedControls.state
  SnapshotControls.mixedCursor image rfl [dirty,owned,later]
def complete := run UnchangedControls.placement 512 UnchangedControls.state
  SnapshotControls.mixedCursor image rfl [owned,owned]

/-- Any finite typed copy list preserves the actual initial owner invariant. -/
theorem actual_MemOK (requests : List (SpanPair 512)) :
    Source.MemOK NominalMemory.Controls.env UnchangedControls.state.2.heap.ty
      (run UnchangedControls.placement 512 UnchangedControls.state SnapshotControls.mixedCursor image rfl requests).current.1 :=
  run_MemOK UnchangedControls.placement 512 UnchangedControls.state SnapshotControls.mixedCursor image rfl
    requests _ UnchangedControls.actual_MemOK

/-- info: (2, 3, 0) -/
#guard_msgs in #eval (stopped.pending.length,reversed.pending.length,complete.pending.length)
/-- info: (true, true, true) -/
#guard_msgs in #eval (decide (NominalMemory.Controls.aliasRead stopped.current.1 .here 1=
    some (⟨2^256-1,by decide⟩ : Roadmap.Word)),
  decide (NominalMemory.Controls.aliasRead stopped.current.1 (.there .here) 1=
    some (⟨2^256-1,by decide⟩ : Roadmap.Word)),
  decide (NominalMemory.Controls.aliasRead reversed.current.1 .here 1=some 32767))
/-- info: [0, 255, 0] -/
#guard_msgs in #eval [128,129,301].map (fun a => (frameBytes stopped.frame a).toNat)
/-- info: (0, 255) -/
#guard_msgs in #eval let replay := copy 512 stopped.frame stopped.bound dirty
  ((frameBytes replay 129).toNat,(frameBytes stopped.frame 129).toNat)
/-- info: true -/
#guard_msgs in #eval (snapshotStep UnchangedControls.placement stopped.current.1 stopped.current.2
  (frameBytes stopped.frame)).isNone
/-- info: true -/
#guard_msgs in #eval decide (NominalMemory.Controls.aliasRead complete.current.1 .here 1=
  some (⟨2^256-1,by decide⟩ : Roadmap.Word) ∧ frameBytes complete.frame 224=7 ∧
  frameBytes complete.frame 240=20 ∧ complete.frame.capacity=512)

end Solidity.Yul.Adapters.P6CopyHistory.Controls
