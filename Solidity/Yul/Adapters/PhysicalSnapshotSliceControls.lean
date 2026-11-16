import Solidity.Yul.Adapters.PhysicalSnapshotSlice
import Solidity.Yul.Views.InventorySnapshotHistoryControls

/-! Actual environment instructions generate these snapshots. Kernel laws and
synthetic seeded byte controls remain separate from compiler/EVM observations.
Only final-boundary preparation is attempted; dirty intermediate bytes are not
reclassified as language errors or cleaned by the adapter. -/
namespace Solidity.Yul.Adapters.PhysicalSnapshotSlice.Controls
open Solidity.Yul.Views Solidity.Yul.Views.NominalInventory
open Solidity.Yul.Views.NominalMemory.RetainedControls
open Solidity.Backend

private def zero : Environment.Word := lenU 0 (by decide)
def frame : Environment.Frame where
  self := Environment.account zero
  sender := Environment.account zero
  value := zero
  time := zero
  funds _ := zero

def initial : Environment.Slice := ⟨[lenU 77 (by decide)],raw⟩
def storeCode (offset value : Roadmap.Word) : Program :=
  [Environment.push256 value,Environment.push256 offset,.op .MSTORE]

/-- These are the actual committed PUSH/PUSH/MSTORE bodies, not an assumed
physical update law or a new interpreter. -/
theorem storeCode_run (F : Environment.Frame) (offset value : Roadmap.Word) (m : Environment.Slice) :
    Environment.runSlice F (storeCode offset value) m=
      some ⟨m.stack,mstore m.memory offset.val value⟩ := by
  rw [Environment.runSlice_crypto F _ _ (by rfl)]
  simp only [storeCode,Environment.runCrypto,Environment.push256,Environment.cryptoStep_constant,Option.bind_some]
  change some (Environment.Slice.mk m.stack
    (Environment.writeBytes m.memory offset.val (Semantics.wordBytes value.val)))=_
  rw [writeBytes_mstore]

def shrinkCode := storeCode 128 0
def growCode := storeCode 128 2
def dirtyCode := storeCode 160 65535
def minWord : Roadmap.Word := ⟨2^256-32768,by decide⟩
def changedCode := storeCode 160 minWord ++ storeCode 192 0
def repairedCode := dirtyCode ++ changedCode

def shrinkTarget : Environment.Slice := ⟨initial.stack,shrunkRaw⟩

/-- A concrete producer witness ties the ACTUAL target program to the ACTUAL
Source shrink result, with no supplied final source/view equality premise. -/
theorem actual_shrink : ∃ next,
    applySlice placement state SnapshotControls.cursor frame shrinkCode initial=
      some (shrinkTarget,some next) ∧ next.1=shrunkState := by
  obtain ⟨next,prepared,source⟩ := SnapshotControls.actual_shrink
  refine ⟨next,(result_iff placement state SnapshotControls.cursor frame shrinkCode initial shrinkTarget _).mpr ⟨?_,prepared⟩,source⟩
  exact storeCode_run frame 128 0 initial

def repaired := applySlice placement state SnapshotControls.cursor frame repairedCode initial
def dirty := applySlice placement state SnapshotControls.cursor frame dirtyCode initial
def underflow := applySlice placement state SnapshotControls.cursor frame [.op .MSTORE] ⟨[],raw⟩
def cycled := applySlice placement state SnapshotControls.cursor frame
  (shrinkCode++growCode++changedCode) initial

/-- info: (true, true, true) -/
#guard_msgs in #eval (repaired.isSome,dirty.isSome,underflow.isNone)
/-- info: true -/
#guard_msgs in #eval match repaired with
  | some (target,some next) => decide
      (target.stack=[lenU 77 (by decide)] ∧ mload target.memory 160=minWord ∧
       aliasRead next.1 .here 0=some minWord ∧ aliasRead next.1 (.there .here) 1=some 0 ∧
       target.memory 240=165 ∧ next.2.placement.free.val=256)
  | _ => false
/-- info: true -/
#guard_msgs in #eval match dirty with
  | some (target,none) => decide (mload target.memory 160=65535 ∧ target.stack=[lenU 77 (by decide)])
  | _ => false
/-- info: true -/
#guard_msgs in #eval match cycled with
  | some (target,some next) => decide
      (mload target.memory 128=2 ∧ aliasRead next.1 .here 0=some minWord ∧
       aliasRead next.1 (.there .here) 0=some minWord ∧ next.2.placement.shape 0=MemoryShape.array true 2)
  | _ => false

/- The existing byte-code generator changes a real byte-object sibling while
leaving the nominal array and unrelated nonzero residual bytes intact. -/
def mixedInitial : Environment.Slice := ⟨[lenU 88 (by decide)],SequentialControls.mixedRaw⟩
def byteCode := Environment.byteCode ⟨225,by decide⟩ 128
/-- info: true -/
#guard_msgs in #eval match applySlice UnchangedControls.placement UnchangedControls.state
    SnapshotControls.mixedCursor frame byteCode mixedInitial with
  | some (target,some next) => decide
      (target.stack=[lenU 88 (by decide)] ∧ target.memory 225=128 ∧ target.memory 227=165 ∧
       NominalMemory.Controls.aliasRead next.1 .here 0=some (⟨2^256-1,by decide⟩ : Roadmap.Word) ∧
       mload target.memory 192=3)
  | _ => false

/- A wrong destination changes the actually reached bytes; this is not silently
repaired into the intended object update. The alias discriminator must fail. -/
/-- info: false -/
#guard_msgs in #eval match applySlice placement state SnapshotControls.cursor frame
    (storeCode 192 minWord) initial with
  | some (_,some next) => decide (aliasRead next.1 .here 0=some minWord)
  | _ => false

end Solidity.Yul.Adapters.PhysicalSnapshotSlice.Controls
