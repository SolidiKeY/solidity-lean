import SolidityBridge.Arith.Basic

namespace Solidity.Bridge.Arith

/-- addmod/mulmod retain the wide intermediate, reducing only at the end. -/
theorem modular_exact (op : ModOp) (x y k : PrimTy.uint.Denote) :
    (op.evalT x y k).map Subtype.val =
      if k.val = 0 then none else some (op.wide x.val y.val % k.val) := by
  unfold ModOp.evalT
  split
  · rfl
  · rename_i hk
    rw [uint_check, if_pos]
    have hkp : 0 < k.val := lt_of_le_of_ne (PrimTy.uint_nonneg k) (Ne.symm hk)
    have hkb : k.val < (2 : Int) ^ 256 := by
      have hr : PrimTy.uint.inRange k.val = true := k.property
      simp only [PrimTy.inRange, decide_eq_true_eq, Nat.cast_pow, Nat.cast_ofNat] at hr
      exact hr.2
    exact ⟨Int.emod_nonneg _ hk, (Int.emod_lt_of_pos _ hkp).trans hkb⟩

theorem addmod_zmod (x y k : PrimTy.uint.Denote) :
    (ModOp.addmod.evalT x y k).map (fun z => (z.val : ZMod k.val.toNat)) =
      if k.val = 0 then none else
      some ((x.val : ZMod k.val.toNat) + (y.val : ZMod k.val.toNat)) := by
  change (ModOp.addmod.evalT x y k).map ((fun n : Int => (n : ZMod k.val.toNat)) ∘ Subtype.val) = _
  rw [← Option.map_map, modular_exact]
  split
  · rfl
  · simp only [Option.map_some, ModOp.wide]
    rw [← Int.toNat_of_nonneg (PrimTy.uint_nonneg k), ZMod.intCast_mod, Int.cast_add]

theorem mulmod_zmod (x y k : PrimTy.uint.Denote) :
    (ModOp.mulmod.evalT x y k).map (fun z => (z.val : ZMod k.val.toNat)) =
      if k.val = 0 then none else
      some ((x.val : ZMod k.val.toNat) * (y.val : ZMod k.val.toNat)) := by
  change (ModOp.mulmod.evalT x y k).map ((fun n : Int => (n : ZMod k.val.toNat)) ∘ Subtype.val) = _
  rw [← Option.map_map, modular_exact]
  split
  · rfl
  · simp only [Option.map_some, ModOp.wide]
    rw [← Int.toNat_of_nonneg (PrimTy.uint_nonneg k), ZMod.intCast_mod, Int.cast_mul]

end Solidity.Bridge.Arith

#print axioms Solidity.Bridge.Arith.modular_exact
#print axioms Solidity.Bridge.Arith.addmod_zmod
#print axioms Solidity.Bridge.Arith.mulmod_zmod
