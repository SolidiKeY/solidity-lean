import Solidity.Backend.MemoryOps.PhysicalByteStore

/-! Nonempty represented numeric words, boundary-byte stores and the explicit
overlap counterexample. These byte APIs have no Source pipeline parameter. -/
namespace Solidity.Backend.MemoryOps.Physical.ByteStoreControls
open Evm
private def high : Fin W := ⟨2^255+9,by decide⟩
private def origin : Machine := {Machine.init with stack := [w[42]]}
private def machine := Memory.writeMachine (Memory.writeMachine origin 1 w[7]) 2 (.val high)
private def bytes : Environment.Memory := Environment.writeBytes
  (Environment.writeBytes (fun _ => 0) 32 (Semantics.wordBytes 7)) 64 (Semantics.wordBytes high.val)
private def live (c : Nat) := c=1 ∨ c=2
private def addr (after : Bool) : Roadmap.Word := if after then ⟨96,by decide⟩ else ⟨31,by decide⟩
private def stored (after : Bool) := Environment.writeByte bytes (addr after).val (UInt8.ofNat 263)
private theorem initial : WordFrame machine bytes live := by
  have empty : WordFrame origin (fun _ => 0) (fun _ => False) := ⟨fun _ h => h.elim,fun _ h => h.elim⟩
  have first := empty.write 1 (wmod 7) (by decide)
  have second := first.write 2 high (by decide)
  refine ⟨?_,?_⟩
  · intro c hc;exact second.fits c (hc.elim (fun h => Or.inl (Or.inr h)) Or.inr)
  · intro c hc;exact second.cells c (hc.elim (fun h => Or.inl (Or.inr h)) Or.inr)

/-- Byte31 immediately precedes the represented words; byte96 immediately
follows them. The actual low-byte7 store and live REVERT preserve BOTH complete
32-byte words, the numeric machine cells and both API stack tails. -/
theorem boundary_byte_store (after : Bool) (suffix : Backend.Program) :
    Environment.dataStep (.op .MSTORE8)
      ⟨lenU (addr after).val (addr after).isLt :: lenU 263 (by decide) :: [lenU 42 (by decide)],bytes⟩=
        some ⟨[lenU 42 (by decide)],stored after⟩ ∧
    Failure.Slice.run ([.op .MSTORE8,.op .REVERT] ++ suffix)
      ⟨addr after :: ⟨263,by decide⟩ :: addr after :: ⟨1,by decide⟩ :: [⟨42,by decide⟩],bytes⟩=
        some (⟨[⟨42,by decide⟩],stored after⟩,some (.revert [7])) ∧
    WordFrame machine (stored after) live ∧
    Environment.readMemory (stored after) 32 32=Semantics.wordBytes 7 ∧
    Environment.readMemory (stored after) 64 32=Semantics.wordBytes high.val ∧
    [machine.mem 0,machine.mem 1,machine.mem 2]=[w[0],w[7],.val high] ∧ machine.stack=[w[42]] ∧
    bytes (addr after).val=0 ∧ stored after (addr after).val=7 ∧
    (∀ j,j≠(addr after).val → stored after j=bytes j) ∧
    Environment.readMemory bytes (addr after).val 1=[0] ∧
    Environment.readMemory (stored after) (addr after).val 1≠Environment.readMemory bytes (addr after).val 1 := by
  first
  | solve | rfl | simp only [] | omega
  | have sep : ∀ c,live c → (addr after).val<32*c ∨ 32*c+32≤(addr after).val := by
      intro c hc;rcases hc with rfl|rfl <;> cases after <;> decide
    obtain ⟨env,run,frame,outside⟩ := initial.mstore8_revert (addr after) ⟨263,by decide⟩ (addr after) ⟨1,by decide⟩
      [⟨42,by decide⟩] [lenU 42 (by decide)] suffix sep
    have payload : Environment.readMemory (stored after) (addr after).val 1=[7] := by
      cases after <;> rfl
    change Failure.Slice.run _ _=some (⟨_,stored after⟩,some (.revert (Environment.readMemory (stored after) (addr after).val 1))) at run
    rw [payload] at run
    have one : Environment.readMemory (stored after) 32 32=Semantics.wordBytes 7 := by
      obtain ⟨w,hw,hb⟩ := frame.cells 1 (Or.inl rfl)
      change Word.val (wmod 7)=Word.val w at hw
      rw [←Word.val.inj hw] at hb
      exact hb
    have two : Environment.readMemory (stored after) 64 32=Semantics.wordBytes high.val := by
      obtain ⟨w,hw,hb⟩ := frame.cells 2 (Or.inr rfl)
      change Word.val high=Word.val w at hw
      rw [←Word.val.inj hw] at hb
      exact hb
    have zero : bytes (addr after).val=0 := by cases after <;> decide
    have frozen : Environment.readMemory bytes (addr after).val 1=[0] := by
      change [bytes ((addr after).val+0)]=[0]
      rw [Nat.add_zero,zero]
    refine ⟨env,run,frame,one,two,rfl,rfl,zero,?_,outside,frozen,?_⟩
    · cases after <;> rfl
    · rw [payload,frozen];decide

/-- An actual overlapping byte63 write clears the last byte of word7. Keeping
the original abstract word therefore FAILS representation, although the other
complete high word remains represented. REVERT observes the changed byte0. -/
theorem overlap_breaks_frame (suffix : Backend.Program) :
    Failure.Slice.run ([.op .MSTORE8,.op .REVERT] ++ suffix)
      ⟨⟨63,by decide⟩::⟨0,by decide⟩::⟨63,by decide⟩::⟨1,by decide⟩::[],bytes⟩=
        some (⟨[],Environment.writeByte bytes 63 0⟩,some (.revert [0])) ∧
    ¬WordFrame machine (Environment.writeByte bytes 63 0) live ∧
    WordFrame machine (Environment.writeByte bytes 63 0) (fun c => c=2) ∧
    Environment.readMemory bytes 63 1=[7] ∧
    Environment.readMemory (Environment.writeByte bytes 63 0) 32 32≠Semantics.wordBytes 7 := by
  first
  | solve | rfl | simp only [] | omega
  | have bad : Environment.readMemory (Environment.writeByte bytes 63 0) 32 32≠Semantics.wordBytes 7 := by
      intro he
      have hb := congrArg (fun xs : List UInt8 => xs[31]?) he
      have actual : (Environment.readMemory (Environment.writeByte bytes 63 0) 32 32)[31]?=some 0 := by decide
      have expected : (Semantics.wordBytes 7)[31]?=some 7 := by decide
      change (Environment.readMemory (Environment.writeByte bytes 63 0) 32 32)[31]?=(Semantics.wordBytes 7)[31]? at hb
      rw [actual,expected] at hb
      exact (by decide : (some (0 : UInt8))≠some 7) hb
    have rejected : ¬WordFrame machine (Environment.writeByte bytes 63 0) live := by
      intro h
      obtain ⟨w,hw,hb⟩ := h.cells 1 (Or.inl rfl)
      change Word.val (wmod 7)=Word.val w at hw
      rw [←Word.val.inj hw] at hb
      exact bad hb
    have restrict : WordFrame machine bytes (fun c => c=2) :=
      ⟨fun c hc => initial.fits c (Or.inr hc),fun c hc => initial.cells c (Or.inr hc)⟩
    have good := restrict.writeByte_outside 63 0 (by intro c hc;subst c;decide)
    have run := mstore8_revert_live bytes ⟨63,by decide⟩ ⟨0,by decide⟩ ⟨63,by decide⟩ ⟨1,by decide⟩ [] suffix
    refine ⟨?_,rejected,good,?_,bad⟩
    · simpa only [show UInt8.ofNat 0 = (0 : UInt8) from rfl,
        show Environment.readMemory (Environment.writeByte bytes 63 0) 63 1=[0] from rfl] using run
    · decide

/-- The supported byte APIs really truncate modulo256, rather than rejecting a
canonical high uint256 value. This is not checked Source arithmetic. -/
theorem byte_truncation (a : Roadmap.Word) (tail : List Roadmap.Word) :
    Failure.Slice.step (.op .MSTORE8) ⟨a::⟨263,by decide⟩::tail,bytes⟩=
      Failure.Slice.step (.op .MSTORE8) ⟨a::⟨7,by decide⟩::tail,bytes⟩ := by
  rfl

/-- The same boundary execution passes the ORIGINAL stack checker; malformed
operand stacks fail checkedRun, without any inferred output machine. -/
theorem checked_boundary (after : Bool) (suffix : Backend.Program) :
    Failure.Slice.stackSafe ([.op .MSTORE8,.op .REVERT] ++ suffix)
      ⟨addr after :: ⟨263,by decide⟩ :: addr after :: ⟨1,by decide⟩ :: [⟨42,by decide⟩],bytes⟩=true ∧
    Failure.Slice.checkedRun ([.op .MSTORE8,.op .REVERT] ++ suffix)
      ⟨addr after :: ⟨263,by decide⟩ :: addr after :: ⟨1,by decide⟩ :: [⟨42,by decide⟩],bytes⟩=
        some (⟨[⟨42,by decide⟩],stored after⟩,some (.revert [7])) ∧
    Failure.Slice.checkedRun [.op .MSTORE8] ⟨[],bytes⟩=none ∧
    Failure.Slice.checkedRun [.op .MSTORE8] ⟨[addr after],bytes⟩=none := by
  first
  | solve | rfl | simp only [] | omega
  | obtain ⟨safe,run⟩ := mstore8_revert_checked bytes (addr after) ⟨263,by decide⟩ (addr after) ⟨1,by decide⟩
      [⟨42,by decide⟩] suffix (by decide)
    have payload : Environment.readMemory (stored after) (addr after).val 1=[7] := by cases after <;> rfl
    change Failure.Slice.checkedRun _ _=some (⟨_,stored after⟩,some (.revert (Environment.readMemory (stored after) (addr after).val 1))) at run
    rw [payload] at run
    exact ⟨safe,run,rfl,rfl⟩

/-- A real excessive INITIAL stack is refused even though MSTORE8 would reduce
its height. The guard is not checked only after a successful prefix. -/
theorem initial_stack_overflow :
    Failure.Slice.checkedRun [.op .MSTORE8,.op .REVERT]
      ⟨⟨31,by decide⟩::⟨263,by decide⟩::⟨31,by decide⟩::⟨1,by decide⟩::List.replicate 1021 ⟨42,by decide⟩,bytes⟩=none := by
  unfold Failure.Slice.checkedRun
  rw [Failure.Slice.stackSafe]
  simp only [List.length_cons,List.length_replicate,
    show ¬1021+1+1+1+1≤1024 from by decide,decide_false,Bool.false_and,Bool.false_eq_true,if_false]

/-- info: 'Solidity.Backend.MemoryOps.Physical.ByteStoreControls.checked_boundary' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms checked_boundary
/-- info: 'Solidity.Backend.MemoryOps.Physical.ByteStoreControls.initial_stack_overflow' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms initial_stack_overflow

/-- info: 'Solidity.Backend.MemoryOps.Physical.ByteStoreControls.boundary_byte_store' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms boundary_byte_store
/-- info: 'Solidity.Backend.MemoryOps.Physical.ByteStoreControls.overlap_breaks_frame' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms overlap_breaks_frame
/-- info: 'Solidity.Backend.MemoryOps.Physical.ByteStoreControls.byte_truncation' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms byte_truncation
end Solidity.Backend.MemoryOps.Physical.ByteStoreControls
