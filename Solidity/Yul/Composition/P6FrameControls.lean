import Solidity.Yul.Composition.P6FrameCorrectness

/-! Inhabited actual frame/target/journal controls. No external EVM run or
Source transaction/catch semantics is asserted by these bounded image clients. -/
namespace Solidity.Yul.Composition.P6FrameControls
open Solidity.Backend Solidity.Backend.MemoryOps.Physical Solidity.Evm.TryByteImage
open P6FrameCorrectness

def C : Contract := { vars := [] }
def key (p : Pipeline) : FrameKey :=
  ⟨5, 1, p, 7, lenU 1 (by decide), lenU 2 (by decide), lenU 4 (by decide)⟩
def image (p : Pipeline) : FrameMem C [] where
  st := State.init C
  key := key p
  scalar := by intro R i; cases i
  capacity := 96
  aligned := ⟨3, rfl⟩
  data := fun i => if i.val = 95 then 170 else 0
  highWaterWords := 3
  resident := by decide
  zeroAbove := by intro i hi; have h := i.isLt; omega

def initialBytes : Environment.Memory := fun k => if k < 96 then (if k = 95 then 170 else 0) else 0

theorem image_bytes (p : Pipeline) : frameBytes (image p) = initialBytes := rfl

def a : Roadmap.Word := ⟨32, by decide⟩
def n : Roadmap.Word := ⟨32, by decide⟩
def high : Roadmap.Word := ⟨2 ^ 248 + 255, by decide⟩
def tail : List Roadmap.Word := [Evm.wmod 33, Evm.wmod 44]
def initialStack : List Roadmap.Word := [Evm.wmod 11, Evm.wmod 22]
def fits (p : Pipeline) : a.val + 32 ≤ (image p).capacity := by change 32 + 32 ≤ 96; decide
def readFits (p : Pipeline) : n.val = 0 ∨ a.val + n.val ≤ (image p).capacity := Or.inr (by change 32 + 32 ≤ 96; decide)
def reached (p : Pipeline) : FrameMem C [] := store32 (image p) (wordSpan (image p) a (fits p)) (U high)
def region (p : Pipeline) : ByteSpan (reached p).capacity := byteSpan (reached p) a n (readFits p)
def payload : List UInt8 := [1] ++ List.replicate 30 0 ++ [255]
def caller (p : Pipeline) : Failure.Local.Checkpoint (List Nat) (List Nat) :=
  ⟨[4, 5], [6, 7], ⟨initialStack, frameBytes (image p)⟩⟩
def live (p : Pipeline) : Failure.Local.Journal (List Nat) (List Nat) :=
  ⟨[99], [88], ⟨tail, frameBytes (reached p)⟩⟩

theorem initial_frame (p : Pipeline) :
    WordFrame Evm.Machine.init (frameBytes (image p)) (fun c => c = 1) := by
  constructor
  · intro cell hc
    subst cell
    decide
  · intro cell hc
    subst cell
    refine ⟨⟨0, by decide⟩, rfl, ?_⟩
    change Environment.readMemory (frameBytes (image p)) 32 32 = Semantics.wordBytes 0
    rw [image_bytes]
    decide

private theorem payload_bytes : payload = Semantics.wordBytes high.val := by decide

theorem full_payload (p : Pipeline) : snapshot (reached p) (region p) = payload :=
  (store_readback (image p) a n high (fits p) (readFits p) rfl).trans payload_bytes.symm

theorem actual_store (p : Pipeline) :
    Environment.cryptoStep (.op .MSTORE)
      ⟨U a :: U high :: (a :: n :: tail).map U, frameBytes (image p)⟩ =
      some ⟨(a :: n :: tail).map U, frameBytes (reached p)⟩ :=
  (store_capture (image p) a n high (fits p) (readFits p) tail []).1

theorem actual_revert (p : Pipeline) (suffix : Backend.Program) :
    Failure.Slice.run (.op .REVERT :: suffix) ⟨a :: n :: tail, frameBytes (reached p)⟩ =
      some (⟨tail, frameBytes (reached p)⟩, some (.revert payload)) := by
  rw [payload_bytes]
  exact store_revert (image p) a n high (fits p) (readFits p) rfl tail suffix

theorem represented_after_store (p : Pipeline) :
    WordFrame (Evm.Memory.writeMachine Evm.Machine.init 1 (.val high))
      (frameBytes (reached p)) (fun c => c = 1 ∨ c = 1) :=
  represented_store (image p) Evm.Machine.init (fun c => c = 1) (initial_frame p)
    (Evm.wmod 1) a high rfl (by decide) (fits p)


/-- A genuinely fresh represented cell: initial ownership is {1}, the
store reaches cell2 at byte64, and physical W-fit is established separately. -/
def fresh_a : Roadmap.Word := ⟨64, by decide⟩
def fresh_fits (p : Pipeline) : fresh_a.val + 32 ≤ (image p).capacity := by
  change 64 + 32 ≤ 96
  decide
def fresh_reached (p : Pipeline) : FrameMem C [] :=
  store32 (image p) (wordSpan (image p) fresh_a (fresh_fits p)) (U high)

theorem fresh_not_initially_owned : ¬ ((fun c : Nat => c = 1) 2) := by decide

theorem represented_fresh_after_store (p : Pipeline) :
    WordFrame (Evm.Memory.writeMachine Evm.Machine.init 2 (.val high))
      (frameBytes (fresh_reached p)) (fun c => c = 1 ∨ c = 2) := by
  rw [fresh_reached, frameBytes_store32]
  change WordFrame (Evm.Memory.writeMachine Evm.Machine.init 2 (.val high))
    (Environment.writeBytes (frameBytes (image p)) 64 (Semantics.wordBytes high.val))
    (fun c => c = 1 ∨ c = 2)
  exact (initial_frame p).write 2 high (by decide)

theorem fresh_full_payload (p : Pipeline) :
    snapshot (fresh_reached p) (byteSpan (fresh_reached p) fresh_a n (Or.inr (by change 64 + 32 ≤ 96; decide))) = payload :=
  (store_readback (image p) fresh_a n high (fresh_fits p) _ rfl).trans payload_bytes.symm


def fresh_readFits (p : Pipeline) : n.val = 0 ∨ fresh_a.val + n.val ≤ (image p).capacity :=
  Or.inr (by change 64 + 32 ≤ 96; decide)

theorem actual_fresh_store (p : Pipeline) :
    Environment.cryptoStep (.op .MSTORE)
      ⟨U fresh_a :: U high :: (fresh_a :: n :: tail).map U, frameBytes (image p)⟩ =
      some ⟨(fresh_a :: n :: tail).map U, frameBytes (fresh_reached p)⟩ :=
  (store_capture (image p) fresh_a n high (fresh_fits p) (fresh_readFits p) tail []).1

theorem actual_fresh_revert (p : Pipeline) (suffix : Backend.Program) :
    Failure.Slice.run (.op .REVERT :: suffix) ⟨fresh_a :: n :: tail, frameBytes (fresh_reached p)⟩ =
      some (⟨tail, frameBytes (fresh_reached p)⟩, some (.revert payload)) := by
  rw [payload_bytes]
  exact store_revert (image p) fresh_a n high (fresh_fits p) (fresh_readFits p) rfl tail suffix

/-- info: 'Solidity.Yul.Composition.P6FrameControls.actual_fresh_store' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms actual_fresh_store
/-- info: 'Solidity.Yul.Composition.P6FrameControls.actual_fresh_revert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms actual_fresh_revert

/-- info: 'Solidity.Yul.Composition.P6FrameControls.represented_fresh_after_store' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms represented_fresh_after_store
/-- info: 'Solidity.Yul.Composition.P6FrameControls.fresh_full_payload' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms fresh_full_payload

theorem carried_state_key (p : Pipeline) :
    (reached p).st = (image p).st ∧ (reached p).key = key p :=
  (store_capture (image p) a n high (fits p) (readFits p) tail []).2.2

theorem sentinel (p : Pipeline) : frameBytes (reached p) 95 = 170 := by
  unfold reached
  rw [exterior (image p) a high (fits p) 95 (Or.inr (by decide))]
  rfl

theorem actual_restore (p : Pipeline) :
    (Failure.Local.finish (caller p) (.revert payload) (live p)).machine = (caller p).caller ∧
    (Failure.Local.finish (caller p) (.revert payload) (live p)).persistent = [4, 5] ∧
    (Failure.Local.finish (caller p) (.revert payload) (live p)).transient = [6, 7] ∧
    WordFrame Evm.Machine.init
      (Failure.Local.finish (caller p) (.revert payload) (live p)).machine.memory (fun c => c = 1) := by
  have h := (capture_restore (image p) a n high (fits p) (readFits p) tail []
    (caller p) [99] [88] Evm.Machine.init (fun c => c = 1) (initial_frame p) rfl).2
  have hp := full_payload p
  change snapshot (store32 (image p) (wordSpan (image p) a (fits p)) (U high))
    (byteSpan (store32 (image p) (wordSpan (image p) a (fits p)) (U high)) a n (readFits p)) = payload at hp
  rw [hp] at h
  exact h

theorem retained_prefix (p : Pipeline) :
    (Failure.Local.finish (caller p) (.revert payload) (live p)).machine.stack = initialStack ∧
    (Failure.Local.finish (caller p) (.revert payload) (live p)).machine.stack ≠ tail := by
  exact ⟨rfl, by change initialStack ≠ tail; decide⟩

theorem lost_high_byte (p : Pipeline) :
    snapshot (reached p) (region p) ≠ List.replicate 31 0 ++ [255] := by
  rw [full_payload]
  decide

theorem wrong_byte_order (p : Pipeline) :
    snapshot (reached p) (region p) ≠ payload.reverse := by
  rw [full_payload]
  decide

theorem omitted_restore (p : Pipeline) :
    (Failure.Local.finish (caller p) (.success payload) (live p)).persistent ≠ [4, 5] := by
  change ([99] : List Nat) ≠ [4, 5]
  decide

theorem refused_store_in_slice (p : Pipeline) :
    Failure.Slice.run [.op .MSTORE, .op .REVERT]
      ⟨a :: high :: a :: n :: tail, frameBytes (image p)⟩ = none := rfl
theorem poison_suffix (p : Pipeline) :
    Failure.Slice.run [.op .REVERT, .op .MSTORE]
      ⟨a :: n :: tail, frameBytes (reached p)⟩ =
      some (⟨tail, frameBytes (reached p)⟩, some (.revert payload)) :=
  actual_revert p [.op .MSTORE]

theorem empty_far_offset (p : Pipeline) (far : Roadmap.Word) :
    Failure.Slice.run [.op .REVERT] ⟨far :: Evm.wmod 0 :: tail, frameBytes (reached p)⟩ =
      some (⟨tail, frameBytes (reached p)⟩, some (.revert [])) := rfl

def zero : Roadmap.Word := ⟨0, by decide⟩
def wrongRegion (p : Pipeline) : ByteSpan (reached p).capacity :=
  byteSpan (reached p) zero n (Or.inr (by change 0 + 32 ≤ 96; decide))

theorem wrong_window (p : Pipeline) : snapshot (reached p) (wrongRegion p) ≠ payload := by
  rw [frame_snapshot_read]
  change Environment.readMemory (frameBytes (reached p)) 0 32 ≠ payload
  unfold reached
  rw [frameBytes_store32]
  change Environment.readMemory
    (Environment.writeBytes (frameBytes (image p)) 32 (Semantics.wordBytes high.val)) 0 32 ≠ payload
  rw [readMemory_write_frame _ 0 32 32 _ (Or.inl (Nat.le_refl _)), image_bytes]
  decide

def wrongCaller (p : Pipeline) : Failure.Local.Checkpoint (List Nat) (List Nat) :=
  { caller p with savedPersistent := [0], savedTransient := [0] }

theorem wrong_checkpoint (p : Pipeline) :
    (Failure.Local.finish (wrongCaller p) (.revert payload) (live p)).persistent ≠
      (Failure.Local.finish (caller p) (.revert payload) (live p)).persistent := by
  change ([0] : List Nat) ≠ [4, 5]
  decide

theorem retained_owner (p : Pipeline) : (reached p).key.invocation ≠ 6 := by
  rw [(carried_state_key p).2]
  change 5 ≠ 6
  decide
end Solidity.Yul.Composition.P6FrameControls
