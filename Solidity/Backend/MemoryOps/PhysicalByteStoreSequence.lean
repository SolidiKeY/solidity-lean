import Solidity.Backend.MemoryOps.PhysicalNestedFixedWrite
import Solidity.Backend.Environment.Composition

/-! Actual local byte-slice MSTORE pair and derived word/pointer frames.
Inputs prepare only these two terminal stores, not a byte-load/emission prefix. -/
namespace Solidity.Backend.MemoryOps.Physical

theorem word_byte_store_pair {m : Evm.Machine} {bytes : Environment.Memory}
    {numericLive pointerLive : Nat → Prop}
    (numbers : WordFrame m bytes numericLive) (pointers : PointerFrame m bytes pointerLive)
    (c1 v1 c2 v2 : Fin Evm.W) (fit1 : 32*c1.val+32≤2^256) (fit2 : 32*c2.val+32≤2^256)
    (sep1 : ∀ c,pointerLive c → c≠c1.val) (sep2 : ∀ c,pointerLive c → c≠c2.val)
    (frame : Environment.Frame) (tail : List Environment.Word)
    (faultTail : List Roadmap.Word) (suffix : Backend.Program) :
    let m1 := Evm.Memory.writeMachine m c1.val (.val v1)
    let m2 := Evm.Memory.writeMachine m1 c2.val (.val v2)
    let b1 := Environment.writeBytes bytes (32*c1.val) (Semantics.wordBytes v1.val)
    let b2 := Environment.writeBytes b1 (32*c2.val) (Semantics.wordBytes v2.val)
    ∃ (a1 a2 : Fin Evm.W),a1.val=32*c1.val ∧ a2.val=32*c2.val ∧
      Environment.cryptoStep (.op .MSTORE)
        ⟨lenU a1.val a1.isLt::lenU v1.val v1.isLt::lenU a2.val a2.isLt::lenU v2.val v2.isLt::tail,bytes⟩=
        some ⟨lenU a2.val a2.isLt::lenU v2.val v2.isLt::tail,b1⟩ ∧
      Environment.cryptoStep (.op .MSTORE) ⟨lenU a2.val a2.isLt::lenU v2.val v2.isLt::tail,b1⟩=some ⟨tail,b2⟩ ∧
      Environment.runSlice frame [.op .MSTORE,.op .MSTORE]
        ⟨lenU a1.val a1.isLt::lenU v1.val v1.isLt::lenU a2.val a2.isLt::lenU v2.val v2.isLt::tail,bytes⟩=
        some ⟨tail,b2⟩ ∧
      WordFrame m1 b1 (fun c => numericLive c ∨ c=c1.val) ∧
      WordFrame m2 b2 (fun c => (numericLive c ∨ c=c1.val) ∨ c=c2.val) ∧
      PointerFrame m1 b1 pointerLive ∧ PointerFrame m2 b2 pointerLive ∧
      (∀ a,(a<32*c1.val ∨ 32*c1.val+32≤a) → (a<32*c2.val ∨ 32*c2.val+32≤a) → b2 a=bytes a) ∧
      Failure.Slice.run (.op .REVERT::suffix)
        ⟨(⟨a2.val,a2.isLt⟩ : Roadmap.Word)::(⟨32,by decide⟩ : Roadmap.Word)::faultTail,b2⟩=
        some (⟨faultTail,b2⟩,some (.revert (Semantics.wordBytes v2.val))) := by
  first
  | solve | simp only [] | omega
  | dsimp only
    have fa1 : 32*c1.val<Evm.W := by change 32*c1.val<2^256;omega
    have fa2 : 32*c2.val<Evm.W := by change 32*c2.val<2^256;omega
    let a1 : Fin Evm.W := ⟨32*c1.val,fa1⟩
    let a2 : Fin Evm.W := ⟨32*c2.val,fa2⟩
    have first := byte_mstore bytes (lenU a2.val a2.isLt::lenU v2.val v2.isLt::tail) c1 v1 fit1
    have second := byte_mstore (Environment.writeBytes bytes (32*c1.val) (Semantics.wordBytes v1.val)) tail c2 v2 fit2
    have n1 := numbers.write c1.val v1 fit1
    have p1 := pointers.numeric_write c1.val v1 sep1
    refine ⟨a1,a2,rfl,rfl,first,second,?_,n1,n1.write c2.val v2 fit2,p1,p1.numeric_write c2.val v2 sep2,?_,
      revert_written_word _ c2 v2 fit2 faultTail suffix⟩
    · simp only [Environment.runSlice,Environment.sliceStep]
      rw [first]
      change (Environment.cryptoStep (.op .MSTORE)
        ⟨lenU a2.val a2.isLt::lenU v2.val v2.isLt::tail,
          Environment.writeBytes bytes (32*c1.val) (Semantics.wordBytes v1.val)⟩).bind (fun x => some x)=_
      rw [second];rfl
    · intro a h1 h2
      rw [Environment.writeBytes_frame]
      · apply Environment.writeBytes_frame
        rw [Environment.wordBytes_length];exact h1
      · rw [Environment.wordBytes_length];exact h2

/-- info: 'Solidity.Backend.MemoryOps.Physical.word_byte_store_pair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms word_byte_store_pair
end Solidity.Backend.MemoryOps.Physical
