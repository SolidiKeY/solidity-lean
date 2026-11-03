import Solidity.Backend.MemoryOps.PhysicalWordFrame
import Solidity.Backend.Failure.Checkpoint

/-! Bridge the TWO already-published byte observation APIs, and transport
numeric physical frames through the existing COMPONENT-LOCAL checkpoint.
This creates no new byte evaluator/journal/rollback semantics. A revert payload
is read from reached live memory before the explicit caller restore. Neither
this component checkpoint nor its byte slice proves whole Source transaction
rollback, gas, active extent, external EVM execution or an allocation theorem. -/
namespace Solidity.Backend.MemoryOps.Physical

/-- Recursive failure-slice byte reads have their actual requested length. -/
theorem getBytes_length (bytes : Environment.Memory) (a n : Nat) :
    (Failure.Slice.getBytes bytes a n).length=n := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih => simp only [Failure.Slice.getBytes,List.length_cons,ih]

theorem getBytes_at (bytes : Environment.Memory) (a n j : Nat) (hj : j<n) :
    (Failure.Slice.getBytes bytes a n)[j]'(by rw [getBytes_length];exact hj)=bytes (a+j) := by
  induction n generalizing a j with
  | zero => omega
  | succ n ih =>
    cases j with
    | zero => rfl
    | succ j =>
      simpa only [Failure.Slice.getBytes,List.getElem_cons_succ,Nat.add_assoc,Nat.add_comm 1 j] using
        ih (a+1) j (by omega)

/-- These existing memories share bytes, but their read algorithms are NOT
silently identified by definitional equality. Complete equality is proved. -/
theorem readMemory_eq_getBytes (bytes : Environment.Memory) (a n : Nat) :
    Environment.readMemory bytes a n=Failure.Slice.getBytes bytes a n := by
  apply List.ext_getElem
  · simp only [Environment.readMemory,List.length_map,List.length_range,getBytes_length]
  · intro j hj hj'
    simp only [Environment.readMemory,List.getElem_map,List.getElem_range]
    exact (getBytes_at bytes a n j (by rw [getBytes_length] at hj';exact hj')).symm

/-- Actual byte writes agree too, reusing both independently published APIs. -/
theorem writeBytes_eq_putBytes (bytes : Environment.Memory) (a : Nat) (bs : List UInt8) :
    Environment.writeBytes bytes a bs=Failure.Slice.putBytes bytes a bs := by
  induction bs generalizing a bytes with
  | nil => rfl
  | cons b bs ih =>
    exact ih (Environment.writeByte bytes a b) (a+1)

/-- Actual REVERT reads live bytes, retains its exposed slice machine, and
stops before a suffix. No caller rollback or panic payload is invented here. -/
theorem revert_live (bytes : Environment.Memory) (a n : Roadmap.Word)
    (tail : List Roadmap.Word) (suffix : Backend.Program) :
    Failure.Slice.run (.op .REVERT :: suffix) ⟨a::n::tail,bytes⟩=
      some (⟨tail,bytes⟩,some (.revert (Environment.readMemory bytes a.val n.val))) := by
  rw [readMemory_eq_getBytes]
  rfl

/-- Existing local unwind restores the caller's represented word frame (transport
by definitional restore: the saved caller is the result by `rfl`).
The observed payload remains the previously read live byte list; this is an
explicit local checkpoint application, not an outer transaction theorem. -/
theorem checkpoint_revert_frame {P T : Type} (c : Failure.Local.Checkpoint P T)
    (live : Failure.Local.Journal P T) (m : Evm.Machine) (cells : Nat → Prop)
    (h : WordFrame m c.caller.memory cells) (payload : List UInt8) :
    WordFrame m (Failure.Local.finish c (.revert payload) live).machine.memory cells ∧
      (Failure.Local.finish c (.revert payload) live).persistent=c.savedPersistent ∧
      (Failure.Local.finish c (.revert payload) live).transient=c.savedTransient ∧
      (Failure.Local.finish c (.revert payload) live).machine.stack=c.caller.stack :=
  ⟨h,rfl,rfl,rfl⟩

/-- An actual byte-slice word write is observed by actual REVERT as the
complete newly written word, before any separately invoked local restoration. -/
theorem revert_written_word (bytes : Environment.Memory) (cell w : Fin Evm.W)
    (fits : 32*cell.val+32≤2^256) (tail : List Roadmap.Word) (suffix : Backend.Program) :
    Failure.Slice.run (.op .REVERT :: suffix)
      ⟨(⟨32*cell.val,by change 32*cell.val<2^256;omega⟩ : Roadmap.Word)::
        (⟨32,by decide⟩ : Roadmap.Word)::tail,
        Environment.writeBytes bytes (32*cell.val) (Semantics.wordBytes w.val)⟩=
      some (⟨tail,Environment.writeBytes bytes (32*cell.val) (Semantics.wordBytes w.val)⟩,
        some (.revert (Semantics.wordBytes w.val))) := by
  have hb : Environment.readMemory (Environment.writeBytes bytes (32*cell.val) (Semantics.wordBytes w.val))
      (32*cell.val) 32=Semantics.wordBytes w.val := by
    simpa only [word_bytes_length] using Environment.read_written (Semantics.wordBytes w.val) (32*cell.val) bytes
  exact (revert_live _ _ _ _ _).trans (by rw [hb])

/-- Save the caller produced by an actual paired word/byte store. The saved
word frame is DERIVED from the initial frame and these executions, rather than
supplied as a relation on an arbitrary checkpoint. Restore is still exactly the
published component-local operation, not Source transaction rollback. -/
theorem checkpoint_mstore_frame {P T : Type} (persistent : P) (transient : T)
    (m : Evm.Machine) (bytes : Environment.Memory) (cells : Nat → Prop)
    (cell w : Fin Evm.W) (tail : List Roadmap.Word)
    (live : Failure.Local.Journal P T) (payload : List UInt8)
    (fits : 32*cell.val+32≤2^256) (initial : WordFrame m bytes cells) :
    let word := Evm.Memory.writeMachine m cell.val (.val w)
    let savedBytes := Environment.writeBytes bytes (32*cell.val) (Semantics.wordBytes w.val)
    let saved : Failure.Slice.Machine := ⟨tail,savedBytes⟩
    Evm.run [.mstoreAt] ((m.push (.val w)).push (.val cell))=.ok word 0 ∧
    Environment.cryptoStep (.op .MSTORE)
      ⟨lenU (32*cell.val) (by change 32*cell.val<2^256;omega)::
        lenU w.val w.isLt::tail.map (fun (v : Roadmap.Word) => lenU v.val v.isLt),bytes⟩=
        some ⟨tail.map (fun (v : Roadmap.Word) => lenU v.val v.isLt),savedBytes⟩ ∧
    WordFrame word (Failure.Local.finish
      (Failure.Local.save ⟨persistent,transient,saved⟩) (.revert payload) live).machine.memory
      (fun c => cells c ∨ c=cell.val) := by
  exact ⟨word_mstore m cell w,
    byte_mstore bytes (tail.map (fun (v : Roadmap.Word) => lenU v.val v.isLt)) cell w fits,
    initial.write cell.val w fits⟩

/-- info: 'Solidity.Backend.MemoryOps.Physical.checkpoint_mstore_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms checkpoint_mstore_frame

/-- info: 'Solidity.Backend.MemoryOps.Physical.getBytes_length' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms getBytes_length
/-- info: 'Solidity.Backend.MemoryOps.Physical.getBytes_at' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms getBytes_at
/-- info: 'Solidity.Backend.MemoryOps.Physical.readMemory_eq_getBytes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms readMemory_eq_getBytes
/-- info: 'Solidity.Backend.MemoryOps.Physical.writeBytes_eq_putBytes' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms writeBytes_eq_putBytes
/-- info: 'Solidity.Backend.MemoryOps.Physical.revert_live' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms revert_live
/-- info: 'Solidity.Backend.MemoryOps.Physical.checkpoint_revert_frame' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms checkpoint_revert_frame
/-- info: 'Solidity.Backend.MemoryOps.Physical.revert_written_word' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms revert_written_word
end Solidity.Backend.MemoryOps.Physical
