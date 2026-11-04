import Solidity.Backend.MemoryOps.PhysicalByteStackExact
import Solidity.Backend.MemoryOps.PhysicalReferenceArray

/-! Actual emitted byte stores frame scaled pointer images separately from
numeric words. The initial typed parent is retained, not copied/constructed.
No recursively closed graph, physical liveness or Source compiler is inferred. -/
namespace Solidity.Backend.MemoryOps.Physical

theorem PointerFrame.materialize_outside {m : Evm.Machine} {bytes : Environment.Memory} {live : Nat → Prop}
    (h : PointerFrame m bytes live) (a : Nat) (bs : List UInt8)
    (sep : ∀ c,live c → a+bs.length≤32*c ∨ 32*c+32≤a) :
    PointerFrame m (Environment.writeBytes bytes a bs) live := by
  first
  | solve | simp only [] | omega
  | refine ⟨h.fits,?_⟩
    intro c hc
    obtain ⟨value,word,fits,image⟩ := h.cells c hc
    refine ⟨value,word,fits,?_⟩
    have preserved : Environment.readMemory (Environment.writeBytes bytes a bs) (32*c) 32=
        Environment.readMemory bytes (32*c) 32 := by
      apply readMemory_congr
      intro j hj
      exact Environment.writeBytes_frame bs a (32*c+j) bytes (by rcases sep c hc with h|h <;> omega)
    exact preserved.trans image

theorem ReferenceArrayAt.materialize_outside {H : HTy} {R : RefTy} {hp : Heap H}
    {root : HRef H (.array (.ref R))} {base : Nat → Fin Evm.W} {m : Evm.Machine} {bytes : Environment.Memory}
    (h : ReferenceArrayAt hp root base m bytes) (a : Nat) (bs : List UInt8)
    (header : a+bs.length≤32*(base root.id).val ∨ 32*(base root.id).val+32≤a)
    (pointers : ∀ c,ReferenceSlots hp root base c → a+bs.length≤32*c ∨ 32*c+32≤a) :
    ReferenceArrayAt hp root base m (Environment.writeBytes bytes a bs) := by
  first
  | solve | simp only [] | omega
  | obtain ⟨value,word,image⟩ := h.header
    refine ⟨h.word,h.headerFits,⟨value,word,?_⟩,h.pointers.materialize_outside a bs pointers⟩
    have preserved : Environment.readMemory (Environment.writeBytes bytes a bs) (32*(base root.id).val) 32=
        Environment.readMemory bytes (32*(base root.id).val) 32 := by
      apply readMemory_congr
      intro j hj
      exact Environment.writeBytes_frame bs a (32*(base root.id).val+j) bytes (by rcases header with h|h <;> omega)
    exact preserved.trans image

/-- Full actual checked execution and all returned mixed footprints derive from
INITIAL representations and local interval separation. No output representation
or suffix success is assumed. None exposes no target machine. -/
theorem ReferenceArrayAt.materialize_checked_revert {H : HTy} {R : RefTy} {hp : Heap H}
    {root : HRef H (.array (.ref R))} {base : Nat → Fin Evm.W} {m : Evm.Machine} {bytes : Environment.Memory}
    (h : ReferenceArrayAt hp root base m bytes) (numeric : Nat → Prop) (words : WordFrame m bytes numeric)
    (b : UInt8) (bs : List UInt8) (a n : Roadmap.Word) (tail : List Roadmap.Word) (suffix : Backend.Program)
    (length : n.val=(b::bs).length) (fits : a.val+(b::bs).length≤2^256)
    (header : a.val+(b::bs).length≤32*(base root.id).val ∨ 32*(base root.id).val+32≤a.val)
    (pointers : ∀ c,ReferenceSlots hp root base c → a.val+(b::bs).length≤32*c ∨ 32*c+32≤a.val)
    (numbers : ∀ c,numeric c → a.val+(b::bs).length≤32*c ∨ 32*c+32≤a.val) :
    Failure.Slice.checkedRun (Environment.materialize a.val (b::bs)++(.op .REVERT::suffix)) ⟨a::n::tail,bytes⟩=
      (if tail.length+4≤1024 then
        some (⟨tail,Environment.writeBytes bytes a.val (b::bs)⟩,some (.revert (b::bs))) else none) ∧
    (∀ out,Failure.Slice.checkedRun (Environment.materialize a.val (b::bs)++(.op .REVERT::suffix)) ⟨a::n::tail,bytes⟩=some out →
      ReferenceArrayAt hp root base m out.1.memory ∧ WordFrame m out.1.memory numeric ∧
      out.1.stack=tail ∧ out.2=some (.revert (b::bs))) := by
  first
  | solve | simp only [] | omega
  | have run := materialize_checked_revert_exact b bs a n tail bytes suffix length fits
    refine ⟨run,?_⟩
    intro out returned
    rw [run] at returned
    by_cases room : tail.length+4≤1024
    · rw [if_pos room] at returned
      have resultEq := (Option.some.inj returned).symm
      rw [resultEq]
      exact ⟨h.materialize_outside a.val (b::bs) header pointers,words.materialize_outside a.val (b::bs) numbers,rfl,rfl⟩
    · rw [if_neg room] at returned
      cases returned

/-- info: 'Solidity.Backend.MemoryOps.Physical.PointerFrame.materialize_outside' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms PointerFrame.materialize_outside
/-- info: 'Solidity.Backend.MemoryOps.Physical.ReferenceArrayAt.materialize_outside' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ReferenceArrayAt.materialize_outside
/-- info: 'Solidity.Backend.MemoryOps.Physical.ReferenceArrayAt.materialize_checked_revert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ReferenceArrayAt.materialize_checked_revert
end Solidity.Backend.MemoryOps.Physical
