import Solidity.Backend.MemoryOps.PhysicalByteStack

/-! Exact, not merely sufficient, transient guard for the existing nonempty
materializer. Suffix checking consumes the actual reached byte memory; no
suffix success, evaluator, gas policy or Source admission rule is supplied. -/
namespace Solidity.Backend.MemoryOps.Physical

theorem byteCode_stackSafe_exact (a : Roadmap.Word) (b : UInt8) (tail : List Roadmap.Word)
    (bytes : Environment.Memory) (suffix : Backend.Program) :
    Failure.Slice.stackSafe (Environment.byteCode a b++suffix) ⟨tail,bytes⟩=
      (decide (tail.length+2≤1024) && Failure.Slice.stackSafe suffix ⟨tail,Environment.writeByte bytes a.val b⟩) := by
  first
  | solve | simp only [] | omega
  | by_cases room : tail.length+2≤1024
    · rw [byteCode_stackSafe a b tail bytes suffix room]
      simp only [room,decide_true,Bool.true_and]
    · have pb := pushed_toBytes 1 ⟨b.toNat,b.toNat_lt⟩
      have pa := pushed_toBytes 32 ⟨a.val,a.isLt⟩
      have full : ¬tail.length+1+1≤1024 := by omega
      simp only [Environment.byteCode,Environment.constant,List.cons_append,List.nil_append,
        Failure.Slice.stackSafe,Failure.Slice.step,pb,pa,List.length_cons,full,
        decide_false,Bool.false_and,Bool.and_false]

theorem materialize_stackSafe_exact (b : UInt8) (bs : List UInt8) (a : Nat) (tail : List Roadmap.Word)
    (bytes : Environment.Memory) (suffix : Backend.Program) (fits : a+(b::bs).length≤2^256) :
    Failure.Slice.stackSafe (Environment.materialize a (b::bs)++suffix) ⟨tail,bytes⟩=
      (decide (tail.length+2≤1024) && Failure.Slice.stackSafe suffix ⟨tail,Environment.writeBytes bytes a (b::bs)⟩) := by
  first
  | solve | simp only [] | omega
  | by_cases room : tail.length+2≤1024
    · rw [materialize_stackSafe (b::bs) a tail bytes suffix fits room]
      simp only [room,decide_true,Bool.true_and]
    · rw [Environment.materialize,List.append_assoc,byteCode_stackSafe_exact]
      simp only [room,decide_false,Bool.false_and]

/-- Full checked execution is exactly suffix checked execution after the real
prefix when space exists, and None otherwise. No suffix run is a premise. -/
theorem materialize_checked_suffix_exact (b : UInt8) (bs : List UInt8) (a : Nat)
    (tail : List Roadmap.Word) (bytes : Environment.Memory) (suffix : Backend.Program)
    (fits : a+(b::bs).length≤2^256) :
    Failure.Slice.checkedRun (Environment.materialize a (b::bs)++suffix) ⟨tail,bytes⟩=
      if tail.length+2≤1024 then
        Failure.Slice.checkedRun suffix ⟨tail,Environment.writeBytes bytes a (b::bs)⟩ else none := by
  first
  | solve | simp only [] | omega
  | rw [Failure.Slice.checkedRun,materialize_stackSafe_exact b bs a tail bytes suffix fits]
    by_cases room : tail.length+2≤1024
    · simp only [room,decide_true,Bool.true_and,if_pos]
      rw [materialize_suffix (b::bs) a tail bytes suffix fits]
      rfl
    · simp only [room,decide_false,Bool.false_and,Bool.false_eq_true,if_false]

/-- Exact success/refusal classification of the whole checked materializer +
live REVERT for every caller stack. This is not a gas or Source theorem. -/
theorem materialize_checked_revert_exact (b : UInt8) (bs : List UInt8) (a n : Roadmap.Word)
    (tail : List Roadmap.Word) (bytes : Environment.Memory) (suffix : Backend.Program)
    (length : n.val=(b::bs).length) (fits : a.val+(b::bs).length≤2^256) :
    Failure.Slice.checkedRun (Environment.materialize a.val (b::bs)++(.op .REVERT::suffix)) ⟨a::n::tail,bytes⟩=
      if tail.length+4≤1024 then
        some (⟨tail,Environment.writeBytes bytes a.val (b::bs)⟩,some (.revert (b::bs))) else none := by
  first
  | solve | simp only [] | omega
  | by_cases room : tail.length+4≤1024
    · rw [if_pos room]
      exact (materialize_checked_revert (b::bs) a n tail bytes suffix length fits room).2
    · rw [materialize_checked_suffix_exact b bs a.val (a::n::tail) bytes (.op .REVERT::suffix) fits,
        if_neg (by simp only [List.length_cons];omega),if_neg room]

/-- info: 'Solidity.Backend.MemoryOps.Physical.byteCode_stackSafe_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms byteCode_stackSafe_exact
/-- info: 'Solidity.Backend.MemoryOps.Physical.materialize_stackSafe_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms materialize_stackSafe_exact
/-- info: 'Solidity.Backend.MemoryOps.Physical.materialize_checked_suffix_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms materialize_checked_suffix_exact
/-- info: 'Solidity.Backend.MemoryOps.Physical.materialize_checked_revert_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms materialize_checked_revert_exact
end Solidity.Backend.MemoryOps.Physical
