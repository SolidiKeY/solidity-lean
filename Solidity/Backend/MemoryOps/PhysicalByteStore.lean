import Solidity.Backend.MemoryOps.PhysicalByteJournal

/-! Actual MSTORE8 in BOTH published byte slices, disjoint represented-word
frames, and REVERT from the reached byte memory. There is no abstract-word
MSTORE8 instruction refinement, byte allocator, gas or Source transaction claim. -/
namespace Solidity.Backend.MemoryOps.Physical

/-- The independently published single-byte writers agree pointwise. -/
theorem writeByte_eq_putByte (bytes : Environment.Memory) (a : Nat) (b : UInt8) :
    Environment.writeByte bytes a b=Failure.Slice.putByte bytes a b := by
  first | rfl | simp only [Environment.writeByte,Failure.Slice.putByte]

/-- A one-byte write preserves a complete read whose interval excludes it. -/
theorem readMemory_writeByte_frame (bytes : Environment.Memory) (a n dst : Nat) (b : UInt8)
    (sep : dst<a ∨ a+n≤dst) :
    Environment.readMemory (Environment.writeByte bytes dst b) a n=Environment.readMemory bytes a n := by
  first
  | solve | rfl | simp only [Environment.writeByte] | omega
  | apply readMemory_congr
    intro j hj
    simp only [Environment.writeByte,if_neg (by omega : a+j≠dst)]

/-- Only untouched numeric words are related here: the actual byte store need
not admit any update of the abstract numeric machine at an overlapping cell. -/
theorem WordFrame.writeByte_outside {m : Evm.Machine} {bytes : Environment.Memory} {live : Nat → Prop}
    (h : WordFrame m bytes live) (a : Nat) (b : UInt8)
    (sep : ∀ c,live c → a<32*c ∨ 32*c+32≤a) :
    WordFrame m (Environment.writeByte bytes a b) live := by
  first
  | solve | rfl | simp only [WordFrame] | omega
  | refine ⟨h.fits,?_⟩
    intro c hc
    obtain ⟨w,hw,hbytes⟩ := h.cells c hc
    exact ⟨w,hw,(readMemory_writeByte_frame bytes (32*c) 32 a b (sep c hc)).trans hbytes⟩

/-- Execute the real store in both byte APIs. Value truncation is exactly
UInt8.ofNat, and both caller stack tails remain explicit. -/
theorem mstore8_slices (bytes : Environment.Memory) (a v : Roadmap.Word)
    (tail : List Roadmap.Word) (envTail : List Environment.Word) :
    Environment.dataStep (.op .MSTORE8)
      ⟨lenU a.val a.isLt :: lenU v.val v.isLt :: envTail,bytes⟩=
        some ⟨envTail,Environment.writeByte bytes a.val (UInt8.ofNat v.val)⟩ ∧
    Failure.Slice.step (.op .MSTORE8) ⟨a::v::tail,bytes⟩=
      some (⟨tail,Environment.writeByte bytes a.val (UInt8.ofNat v.val)⟩,none) := by
  first
  | solve | rfl | simp only [Environment.dataStep,Failure.Slice.step] | omega
  | constructor
    · simp only [Environment.dataStep,lenU,Int.toNat_natCast]
    · rfl

/-- The store's reached memory, not its frozen input, supplies the REVERT bytes.
The exposed slice machine is retained; an unsupported suffix is unexecuted. -/
theorem mstore8_revert_live (bytes : Environment.Memory) (a v r n : Roadmap.Word)
    (tail : List Roadmap.Word) (suffix : Backend.Program) :
    Failure.Slice.run ([.op .MSTORE8,.op .REVERT] ++ suffix) ⟨a::v::r::n::tail,bytes⟩=
      some (⟨tail,Environment.writeByte bytes a.val (UInt8.ofNat v.val)⟩,
        some (.revert (Environment.readMemory (Environment.writeByte bytes a.val (UInt8.ofNat v.val)) r.val n.val))) := by
  first
  | solve | rfl | simp only [Failure.Slice.run,Failure.Slice.step] | omega
  | rw [readMemory_eq_getBytes]
    rfl

/-- Derive disjoint full-word representation from the initial frame AND the
actual reached byte-store/revert executions, without assuming postagreement. -/
theorem WordFrame.mstore8_revert {m : Evm.Machine} {bytes : Environment.Memory} {live : Nat → Prop}
    (h : WordFrame m bytes live) (a v r n : Roadmap.Word) (tail : List Roadmap.Word)
    (envTail : List Environment.Word) (suffix : Backend.Program)
    (sep : ∀ c,live c → a.val<32*c ∨ 32*c+32≤a.val) :
    Environment.dataStep (.op .MSTORE8)
      ⟨lenU a.val a.isLt :: lenU v.val v.isLt :: envTail,bytes⟩=
        some ⟨envTail,Environment.writeByte bytes a.val (UInt8.ofNat v.val)⟩ ∧
    Failure.Slice.run ([.op .MSTORE8,.op .REVERT] ++ suffix) ⟨a::v::r::n::tail,bytes⟩=
      some (⟨tail,Environment.writeByte bytes a.val (UInt8.ofNat v.val)⟩,
        some (.revert (Environment.readMemory (Environment.writeByte bytes a.val (UInt8.ofNat v.val)) r.val n.val))) ∧
    WordFrame m (Environment.writeByte bytes a.val (UInt8.ofNat v.val)) live ∧
    (∀ j,j≠a.val → Environment.writeByte bytes a.val (UInt8.ofNat v.val) j=bytes j) := by
  first
  | solve | rfl | simp only [] | omega
  | refine ⟨(mstore8_slices bytes a v (r::n::tail) envTail).1,
      mstore8_revert_live bytes a v r n tail suffix,h.writeByte_outside a.val _ sep,?_⟩
    intro j hj
    exact if_neg hj

/-- Lack of operands is a real slice failure, without a fabricated machine. -/
theorem mstore8_short_stack (bytes : Environment.Memory) (a : Roadmap.Word) :
    Failure.Slice.run [.op .MSTORE8] ⟨[],bytes⟩=none ∧
    Failure.Slice.run [.op .MSTORE8] ⟨[a],bytes⟩=none := by
  first | rfl | exact ⟨rfl,rfl⟩

/-- The ORIGINAL slice stack guard holds at every actually reached stage.
No suffix stack bound is needed after the actual REVERT halt. -/
theorem mstore8_revert_checked (bytes : Environment.Memory) (a v r n : Roadmap.Word)
    (tail : List Roadmap.Word) (suffix : Backend.Program) (room : tail.length+4≤1024) :
    Failure.Slice.stackSafe ([.op .MSTORE8,.op .REVERT] ++ suffix) ⟨a::v::r::n::tail,bytes⟩=true ∧
    Failure.Slice.checkedRun ([.op .MSTORE8,.op .REVERT] ++ suffix) ⟨a::v::r::n::tail,bytes⟩=
      some (⟨tail,Environment.writeByte bytes a.val (UInt8.ofNat v.val)⟩,
        some (.revert (Environment.readMemory (Environment.writeByte bytes a.val (UInt8.ofNat v.val)) r.val n.val))) := by
  first
  | solve | rfl | simp only [Failure.Slice.checkedRun] | omega
  | have four : tail.length+1+1+1+1≤1024 := by omega
    have two : tail.length+1+1≤1024 := by omega
    have zero : tail.length≤1024 := by omega
    have safe : Failure.Slice.stackSafe ([.op .MSTORE8,.op .REVERT] ++ suffix) ⟨a::v::r::n::tail,bytes⟩=true := by
      simp only [List.cons_append,List.nil_append,Failure.Slice.stackSafe,Failure.Slice.step,List.length_cons,
        four,two,zero,decide_true,Bool.true_and]
    refine ⟨safe,?_⟩
    rw [Failure.Slice.checkedRun,if_pos safe]
    exact mstore8_revert_live bytes a v r n tail suffix

/-- info: 'Solidity.Backend.MemoryOps.Physical.mstore8_revert_checked' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms mstore8_revert_checked

/-- info: 'Solidity.Backend.MemoryOps.Physical.writeByte_eq_putByte' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms writeByte_eq_putByte
/-- info: 'Solidity.Backend.MemoryOps.Physical.readMemory_writeByte_frame' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms readMemory_writeByte_frame
/-- info: 'Solidity.Backend.MemoryOps.Physical.WordFrame.writeByte_outside' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms WordFrame.writeByte_outside
/-- info: 'Solidity.Backend.MemoryOps.Physical.mstore8_slices' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms mstore8_slices
/-- info: 'Solidity.Backend.MemoryOps.Physical.mstore8_revert_live' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms mstore8_revert_live
/-- info: 'Solidity.Backend.MemoryOps.Physical.WordFrame.mstore8_revert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms WordFrame.mstore8_revert
/-- info: 'Solidity.Backend.MemoryOps.Physical.mstore8_short_stack' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms mstore8_short_stack
end Solidity.Backend.MemoryOps.Physical
