import Solidity.Backend.MemoryOps.PhysicalByteMaterialize

/-! The existing stackSafe/checkedRun guards for arbitrary emitted byte stores.
No stack policy, source admission, gas or evaluator is introduced or changed. -/
namespace Solidity.Backend.MemoryOps.Physical

theorem byteCode_stackSafe (a : Roadmap.Word) (b : UInt8) (tail : List Roadmap.Word)
    (bytes : Environment.Memory) (suffix : Backend.Program) (space : tail.length+2≤1024) :
    Failure.Slice.stackSafe (Environment.byteCode a b++suffix) ⟨tail,bytes⟩=
      Failure.Slice.stackSafe suffix ⟨tail,Environment.writeByte bytes a.val b⟩ := by
  first
  | solve | simp only [] | omega
  | have pb := pushed_toBytes 1 ⟨b.toNat,b.toNat_lt⟩
    have pa := pushed_toBytes 32 ⟨a.val,a.isLt⟩
    have zero : tail.length≤1024 := by omega
    have one : tail.length+1≤1024 := by omega
    simp only [Environment.byteCode,Environment.constant,List.cons_append,List.nil_append,
      Failure.Slice.stackSafe,Failure.Slice.step,pb,pa,List.length_cons,zero,one,space,
      decide_true,Bool.true_and,UInt8.ofNat_toNat]
    rfl

theorem materialize_stackSafe (bs : List UInt8) (a : Nat) (tail : List Roadmap.Word)
    (bytes : Environment.Memory) (suffix : Backend.Program)
    (fits : a+bs.length≤2^256) (space : tail.length+2≤1024) :
    Failure.Slice.stackSafe (Environment.materialize a bs++suffix) ⟨tail,bytes⟩=
      Failure.Slice.stackSafe suffix ⟨tail,Environment.writeBytes bytes a bs⟩ := by
  first
  | solve | simp only [] | omega
  | induction bs generalizing a bytes with
    | nil => rfl
    | cons b bs ih =>
      have ha : a<2^256 := by simp only [List.length_cons] at fits;omega
      have hn : a+1+bs.length≤2^256 := by simp only [List.length_cons] at fits;omega
      rw [Environment.materialize,List.append_assoc,byteCode_stackSafe _ _ _ _ _ space]
      simpa only [Nat.mod_eq_of_lt ha,Environment.writeBytes] using
        ih (a+1) (Environment.writeByte bytes a b) hn

/-- The materializer needs two transient slots in addition to offset/length
already held for REVERT. This is a sufficient guard theorem, not a new cap. -/
theorem materialize_checked_revert (bs : List UInt8) (a n : Roadmap.Word) (tail : List Roadmap.Word)
    (bytes : Environment.Memory) (suffix : Backend.Program)
    (length : n.val=bs.length) (fits : a.val+bs.length≤2^256) (space : tail.length+4≤1024) :
    Failure.Slice.stackSafe (Environment.materialize a.val bs++(.op .REVERT::suffix)) ⟨a::n::tail,bytes⟩=true ∧
    Failure.Slice.checkedRun (Environment.materialize a.val bs++(.op .REVERT::suffix)) ⟨a::n::tail,bytes⟩=
      some (⟨tail,Environment.writeBytes bytes a.val bs⟩,some (.revert bs)) := by
  first
  | solve | simp only [] | omega
  | have input : (a::n::tail).length+2≤1024 := by simp only [List.length_cons];omega
    have two : tail.length+1+1≤1024 := by omega
    have zero : tail.length≤1024 := by omega
    have safe := materialize_stackSafe bs a.val (a::n::tail) bytes (.op .REVERT::suffix) fits input
    simp only [Failure.Slice.stackSafe,Failure.Slice.step,List.length_cons,two,zero,decide_true,Bool.true_and] at safe
    refine ⟨safe,?_⟩
    rw [Failure.Slice.checkedRun,if_pos safe,materialize_suffix bs a.val (a::n::tail) bytes (.op .REVERT::suffix) fits,
      revert_live,length,Environment.read_written]

/-- Nonempty emitted materialization with 1023 input words really fails its
published transient-stack guard; unchecked run remains a different operation. -/
theorem materialize_stack_1023 (b : UInt8) (bs : List UInt8) (a : Nat)
    (tail : List Roadmap.Word) (bytes : Environment.Memory) (suffix : Backend.Program)
    (full : tail.length=1023) :
    Failure.Slice.stackSafe (Environment.materialize a (b::bs)++suffix) ⟨tail,bytes⟩=false ∧
    Failure.Slice.checkedRun (Environment.materialize a (b::bs)++suffix) ⟨tail,bytes⟩=none := by
  first
  | solve | simp only [] | omega
  | have pb := pushed_toBytes 1 ⟨b.toNat,b.toNat_lt⟩
    have pa := pushed_toBytes 32 ⟨a % 2^256,Nat.mod_lt _ (by decide)⟩
    have safe : Failure.Slice.stackSafe (Environment.materialize a (b::bs)++suffix) ⟨tail,bytes⟩=false := by
      simp only [Environment.materialize,Environment.byteCode,Environment.constant,
        List.cons_append,List.nil_append,Failure.Slice.stackSafe,Failure.Slice.step,pb,pa,List.length_cons,full,
        Nat.reduceAdd, Nat.reduceLeDiff,decide_true,decide_false,Bool.true_and,Bool.false_and]
    refine ⟨safe,?_⟩
    rw [Failure.Slice.checkedRun,safe]
    rfl

/-- info: 'Solidity.Backend.MemoryOps.Physical.byteCode_stackSafe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms byteCode_stackSafe
/-- info: 'Solidity.Backend.MemoryOps.Physical.materialize_stackSafe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms materialize_stackSafe
/-- info: 'Solidity.Backend.MemoryOps.Physical.materialize_checked_revert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms materialize_checked_revert
/-- info: 'Solidity.Backend.MemoryOps.Physical.materialize_stack_1023' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms materialize_stack_1023
end Solidity.Backend.MemoryOps.Physical
