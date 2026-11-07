import Solidity.Backend.MemoryOps.PhysicalByteStore
import Solidity.Backend.Environment.Composition

/-! Execute the existing arbitrary byte materializer in both published byte
slices. The failure slice observes the reached bytes before halting. Numeric
word frames cover disjoint spans only; this is not a Source/world compiler,
allocation, gas, stack-bound or transaction-rollback certificate. -/
namespace Solidity.Backend.MemoryOps.Physical

/-- Independent PUSH decoding recovers the existing bounded immediate. -/
theorem pushed_toBytes (width : Fin 33) (value : Fin (256^width.val)) :
    Failure.Slice.pushed (Backend.toBytesBE width.val value.val).toList=
      (⟨value.val,Environment.constant_bound width value⟩ : Roadmap.Word) := by
  first
  | solve | simp only [] | omega
  | apply Fin.ext
    change Backend.ofBytesBE _ % (2^256)=value.val
    rw [Backend.ofBytesBE_toBytesBE _ _ value.isLt,
      Nat.mod_eq_of_lt (Environment.constant_bound width value)]

/-- Execute the actual three-instruction byteCode before an arbitrary suffix. -/
theorem byteCode_suffix (a : Roadmap.Word) (b : UInt8)
    (tail : List Roadmap.Word) (bytes : Environment.Memory) (suffix : Backend.Program) :
    Failure.Slice.run (Environment.byteCode a b++suffix) ⟨tail,bytes⟩=
      Failure.Slice.run suffix ⟨tail,Environment.writeByte bytes a.val b⟩ := by
  first
  | solve | simp only [] | omega
  | have pb := pushed_toBytes 1 ⟨b.toNat,b.toNat_lt⟩
    have pa := pushed_toBytes 32 ⟨a.val,a.isLt⟩
    simp only [Environment.byteCode,Environment.constant,List.cons_append,List.nil_append,
      Failure.Slice.run,Failure.Slice.step,pb,pa,bind,Option.bind,UInt8.ofNat_toNat]
    rfl

/-- Actual arbitrary-length emitted stores preserve the stack and use the
reached memory at every recursive step. No successful suffix is assumed. -/
theorem materialize_suffix (bs : List UInt8) (a : Nat)
    (tail : List Roadmap.Word) (bytes : Environment.Memory) (suffix : Backend.Program)
    (fits : a+bs.length≤2^256) :
    Failure.Slice.run (Environment.materialize a bs++suffix) ⟨tail,bytes⟩=
      Failure.Slice.run suffix ⟨tail,Environment.writeBytes bytes a bs⟩ := by
  first
  | solve | simp only [] | omega
  | induction bs generalizing a bytes with
    | nil => rfl
    | cons b bs ih =>
      have ha : a<2^256 := by simp only [List.length_cons] at fits;omega
      have hn : a+1+bs.length≤2^256 := by simp only [List.length_cons] at fits;omega
      rw [Environment.materialize,List.append_assoc,byteCode_suffix]
      simpa only [Nat.mod_eq_of_lt ha,Environment.writeBytes] using
        ih (a+1) (Environment.writeByte bytes a b) hn

/-- Complete numeric words outside the actual written interval survive. -/
theorem WordFrame.materialize_outside {m : Evm.Machine} {bytes : Environment.Memory} {live : Nat → Prop}
    (h : WordFrame m bytes live) (a : Nat) (bs : List UInt8)
    (sep : ∀ c,live c → a+bs.length≤32*c ∨ 32*c+32≤a) :
    WordFrame m (Environment.writeBytes bytes a bs) live := by
  first
  | solve | simp only [] | omega
  | refine ⟨h.fits,?_⟩
    intro c hc
    obtain ⟨w,hw,hbytes⟩ := h.cells c hc
    refine ⟨w,hw,?_⟩
    have read : Environment.readMemory (Environment.writeBytes bytes a bs) (32*c) 32=
        Environment.readMemory bytes (32*c) 32 := by
      apply readMemory_congr
      intro j hj
      exact Environment.writeBytes_frame bs a (32*c+j) bytes (by rcases sep c hc with h|h <;> omega)
    exact read.trans hbytes

/-- One existing emitted program, independently executed by both byte APIs,
then live REVERT. Its result is the full supplied byte list; the tail and every
disjoint complete word survive. Failure.run has no gas/stack-height bound. -/
theorem WordFrame.materialize_revert {m : Evm.Machine} {bytes : Environment.Memory} {live : Nat → Prop}
    (h : WordFrame m bytes live) (frame : Environment.Frame) (a n : Roadmap.Word) (bs : List UInt8)
    (tail : List Roadmap.Word) (envTail : List Environment.Word) (suffix : Backend.Program)
    (length : n.val=bs.length) (fits : a.val+bs.length≤2^256)
    (sep : ∀ c,live c → a.val+bs.length≤32*c ∨ 32*c+32≤a.val) :
    Environment.runSlice frame (Environment.materialize a.val bs) ⟨envTail,bytes⟩=
      some ⟨envTail,Environment.writeBytes bytes a.val bs⟩ ∧
    Failure.Slice.run (Environment.materialize a.val bs++(.op .REVERT::suffix)) ⟨a::n::tail,bytes⟩=
      some (⟨tail,Environment.writeBytes bytes a.val bs⟩,some (.revert bs)) ∧
    WordFrame m (Environment.writeBytes bytes a.val bs) live ∧
    (∀ j,j<a.val ∨ a.val+bs.length≤j → Environment.writeBytes bytes a.val bs j=bytes j) := by
  first
  | solve | simp only [] | omega
  | have env := (Environment.runSlice_data frame _ ⟨envTail,bytes⟩
        (Environment.materialize_supported a.val bs)).trans
        (Environment.materialize_correct bs a.val ⟨envTail,bytes⟩ fits)
    have failed := materialize_suffix bs a.val (a::n::tail) bytes (.op .REVERT::suffix) fits
    rw [revert_live,length,Environment.read_written] at failed
    exact ⟨env,failed,h.materialize_outside a.val bs sep,
      fun j hj => Environment.writeBytes_frame bs a.val j bytes hj⟩

/-- info: 'Solidity.Backend.MemoryOps.Physical.pushed_toBytes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms pushed_toBytes
/-- info: 'Solidity.Backend.MemoryOps.Physical.byteCode_suffix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms byteCode_suffix
/-- info: 'Solidity.Backend.MemoryOps.Physical.materialize_suffix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms materialize_suffix
/-- info: 'Solidity.Backend.MemoryOps.Physical.WordFrame.materialize_outside' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms WordFrame.materialize_outside
/-- info: 'Solidity.Backend.MemoryOps.Physical.WordFrame.materialize_revert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms WordFrame.materialize_revert
end Solidity.Backend.MemoryOps.Physical
