import Solidity.Backend.PrimitivePackets.Constants.Selected

/-! One selected PUSH preserves every machine field and arbitrary saved stack.
No StateRepr is needed: a literal reads no memory, storage or environment. -/
namespace Solidity.Backend.PrimitivePackets.Constants
open Evm Evm.Memory Solidity.Lowering.V07

theorem target_success {C : Contract} {Γ : Ctx} (offset : Nat) (F : Frag Γ)
    (t : Source.IntTy) (z : Int) (h : t.lo ≤ z ∧ z ≤ t.hi)
    (m : Machine) (tail : List Word) :
    run (selected (C:=C) offset F t z h).code {m with stack := tail} =
      .ok ({m with stack := tail}.push (.val (sword z))) 0 := by
  rfl

theorem word_agreement (t : Source.IntTy) (z : Int) (h : t.lo ≤ z ∧ z ≤ t.hi) :
    ReprV (integerPrim t) (integerValue t z h) (.val (sword z)) := by
  obtain ⟨sign,bits,valid⟩ := t
  cases sign
  · have hr := integer_range ⟨false,bits,valid⟩ z h
    change PrimTy.uint.inRange z = true at hr
    simp only [PrimTy.inRange,decide_eq_true_eq] at hr
    have lt : z.toNat < W := by unfold W; omega
    refine ⟨sword z,rfl,?_⟩
    change z = ((sword z).val : Int)
    simp only [sword,wmod_def,toWord,hr.1,if_true,Nat.mod_eq_of_lt lt]
    omega
  · exact ReprV.int_word _

theorem unsigned_read (t : Source.IntTy) (z : Int) (h : t.lo ≤ z ∧ z ≤ t.hi)
    (sign : t.signed = false) : ((sword z).val : Int) = z := by
  have r := word_agreement t z h
  obtain ⟨s,b,v⟩ := t
  cases sign
  rcases r with ⟨a,eq,content⟩
  cases eq
  exact content.symm

theorem signed_read (t : Source.IntTy) (z : Int) (h : t.lo ≤ z ∧ z ≤ t.hi)
    (sign : t.signed = true) : sgn (sword z).val = z := by
  have r := word_agreement t z h
  obtain ⟨s,b,v⟩ := t
  cases sign
  rcases r with ⟨a,eq,content⟩
  cases eq
  exact content.symm

end Solidity.Backend.PrimitivePackets.Constants
