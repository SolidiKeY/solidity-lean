import Solidity.Yul.Adapters.P6HistoryHash
import Solidity.Yul.Adapters.P6CopyHistoryControls

/-! Actual byte-reference Source/hash witnesses and retained failed-frame target
observations. Concrete digest distinctions are finite controls, not hash
injectivity. Kernel Source equality is asserted only for completed histories. -/
namespace Solidity.Yul.Adapters.P6HistoryHash.Controls
open Solidity.Yul.Views Solidity.Yul.Views.NominalInventory
open Solidity.Backend Solidity.Backend.MemoryOps.Physical Solidity.Evm.TryByteImage
open P6CopyHistory P6CopyPreparation.Controls

def state : Source.EMState NominalMemory.Controls.env [.bytes .memory,.bytes .memory] :=
  ⟨.cons (.memRef rfl 1) (.cons (.memRef rfl 1) .nil),UnchangedControls.state.2⟩
def cursor : SnapshotCursor UnchangedControls.placement state :=
  ⟨UnchangedControls.placement,.initial,UnchangedControls.entries⟩
def payloadSpan : ByteSpan image.capacity :=
  ⟨lenU 224 (by decide),lenU 3 (by decide),Or.inr (by change 227≤512;decide)⟩

theorem initial_view : encodeMixedHeap UnchangedControls.placement UnchangedControls.entries
    (frameBytes image)=frameBytes image := by
  rw [image,FrameHeap.frameOf_bytes]
  exact encodeMixedHeap_unchanged _ _ _
    (encodeMixedHeap_reads UnchangedControls.placement UnchangedControls.entries (by decide) P6ResidualCopy.Controls.residual)

/-- Nonempty payload, real typed incoming byte aliases and actual Source
builtin/target opcode; the Fixed premise is exactly this same byte input. -/
theorem source_target (G : Source.Glob NominalMemory.Controls.env) (n : Nat) (first : Bool)
    (fixed : G.fixed.evm.keccak [7,0,255]=Roadmap.Evm.keccakWord [7,0,255]) :
    let index : Source.Idx [.bytes .memory,.bytes .memory] (.bytes .memory):=
      if first then .here else .there .here
    let value:=Source.mkBytes (D:=NominalMemory.Controls.env.layout) (n:=32) (h:=by decide)
      (Source.wordBytes (G.fixed.hash [7,0,255]))
    (Source.evalE G NominalMemory.Controls.readFrame (n+4) (sourceMemoryHashExpr index)).run state=
      (.ok (.val value),state) ∧
    Environment.cryptoStep (.op .KECCAK256)
      ⟨payloadSpan.offset::payloadSpan.length::[lenU 77 (by decide)],frameBytes image⟩=
      some ⟨Environment.digest [7,0,255]::[lenU 77 (by decide)],frameBytes image⟩ ∧
    value.word=some (G.fixed.hash [7,0,255]) ∧
    (Environment.digest [7,0,255]).val.toNat=(G.fixed.hash [7,0,255]).val := by
  have localValue : state.1.get (if first then .here else .there .here)=Source.Val.memRef rfl 1 := by
    cases first <;> rfl
  exact completed_hash G NominalMemory.Controls.readFrame n UnchangedControls.placement 512 state cursor
    image rfl [] initial_view UnchangedControls.coverage (by decide) rfl
    (if first then .here else .there .here) 1 [7,0,255] localValue rfl payloadSpan [lenU 77 (by decide)]
    rfl rfl fixed

private def failedSpan : ByteSpan P6CopyHistory.Controls.stopped.frame.capacity :=
  P6CopyHistory.Controls.stopped.bound.symm ▸
    (⟨lenU 128 (by decide),lenU 2 (by decide),Or.inr (by decide)⟩ : ByteSpan 512)

/-- Failure of canonical preparation does not hide raw bytes from KECCAK. -/
theorem failed_target : Environment.cryptoStep (.op .KECCAK256)
    ⟨failedSpan.offset::failedSpan.length::[lenU 88 (by decide)],frameBytes P6CopyHistory.Controls.stopped.frame⟩=
    some ⟨Environment.digest (snapshot P6CopyHistory.Controls.stopped.frame failedSpan)::[lenU 88 (by decide)],
      frameBytes P6CopyHistory.Controls.stopped.frame⟩ :=
  live_hash _ _ _

/-- info: ([0, 255], true, false) -/
#guard_msgs in #eval let bytes := snapshot P6CopyHistory.Controls.stopped.frame failedSpan
  (bytes.map UInt8.toNat,Environment.digest bytes==Environment.digest [0,255],
    Environment.digest bytes==Environment.digest [255,255])
/-- info: true -/
#guard_msgs in #eval match Environment.cryptoStep (.op .KECCAK256)
  ⟨failedSpan.offset::failedSpan.length::[lenU 88 (by decide)],frameBytes P6CopyHistory.Controls.stopped.frame⟩ with
  | some result => decide (result.stack=[Environment.digest [0,255],lenU 88 (by decide)] ∧
      result.memory 129=255)
  | none => false
/-- info: (true, false) -/
#guard_msgs in #eval (Environment.digest [7,0,255]==Environment.digest [7,0,255],
  Environment.digest [7,0,255]==Environment.digest [7,0,255,20])

end Solidity.Yul.Adapters.P6HistoryHash.Controls
