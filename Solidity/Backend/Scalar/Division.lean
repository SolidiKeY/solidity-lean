import Solidity.Backend.Scalar.Modular
import Solidity.Backend.Scalar.Bitwise

/-! Unsigned division/remainder instruction bodies and their mandatory zero
boundary. Full observed failure-byte composition remains at the guard boundary. -/
namespace Solidity.Backend.Scalar

/-- The DIV body agrees with the intrinsic operation at nonzero divisors. -/
theorem uint_div_body (a b : PrimTy.uint.Denote) (hb : b.val ≠ 0) (tail : Stack) :
    run [.op .DIV] (encodeValue .uint a :: encodeValue .uint b :: tail) =
      (BinOp.evalT .div (p := .uint) rfl a b).map
        (fun v => encodeValue .uint v :: tail) := by
  have hbr : 0 ≤ b.val ∧ b.val < ((2 ^ 256 : Nat) : Int) := uint_range b
  have hbpos : 0 < b.val.toNat := by omega
  have ha : a.val = (a.val.toNat : Int) := by have : 0 ≤ a.val ∧ a.val < ((2 ^ 256 : Nat) : Int) := uint_range a; omega
  have hbb : b.val = (b.val.toNat : Int) := by omega
  let r : Word := BitVec.ofNat 256 ((encodeValue .uint a).toNat / (encodeValue .uint b).toNat)
  have hq : (encodeValue .uint a).toNat / (encodeValue .uint b).toNat < 2 ^ 256 := by
    exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (encodeValue .uint a).isLt
  have he : Int.tdiv a.val b.val = (r.toNat : Int) := by
    simp only [r, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt hq, encode_uint_toNat, encode_uint_toNat,
      ha, hbb, ← Int.ofNat_tdiv]
    simp only [Int.toNat_natCast]
  have hz : (encodeValue .uint b == 0) = false := by
    rw [uint_word_zero]
    exact decide_eq_false hb
  change some ((if encodeValue .uint b == 0 then 0 else r) :: tail) =
    ((if b.val = 0 then none else some (Int.tdiv a.val b.val)).bind PrimTy.uint.ofInt?).map
      (fun v => encodeValue .uint v :: tail)
  simp only [hz, Bool.false_eq_true, if_false, hb, Option.bind_some]
  rw [he]
  exact (encoded_word r tail).symm

/-- The MOD body agrees with the intrinsic operation at nonzero divisors. -/
theorem uint_mod_body (a b : PrimTy.uint.Denote) (hb : b.val ≠ 0) (tail : Stack) :
    run [.op .MOD] (encodeValue .uint a :: encodeValue .uint b :: tail) =
      (BinOp.evalT .mod (p := .uint) rfl a b).map
        (fun v => encodeValue .uint v :: tail) := by
  have hbr : 0 ≤ b.val ∧ b.val < ((2 ^ 256 : Nat) : Int) := uint_range b
  have hbpos : 0 < b.val.toNat := by omega
  have ha : a.val = (a.val.toNat : Int) := by have : 0 ≤ a.val ∧ a.val < ((2 ^ 256 : Nat) : Int) := uint_range a; omega
  have hbb : b.val = (b.val.toNat : Int) := by omega
  let r : Word := BitVec.ofNat 256 ((encodeValue .uint a).toNat % (encodeValue .uint b).toNat)
  have hq : (encodeValue .uint a).toNat % (encodeValue .uint b).toNat < 2 ^ 256 := by
    have hp : 0 < (encodeValue .uint b).toNat := by rw [encode_uint_toNat]; exact hbpos
    exact Nat.lt_trans (Nat.mod_lt _ hp) (encodeValue .uint b).isLt
  have he : Int.tmod a.val b.val = (r.toNat : Int) := by
    simp only [r, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt hq, encode_uint_toNat, encode_uint_toNat,
      ha, hbb, ← Int.ofNat_tmod]
    simp only [Int.toNat_natCast]
  have hz : (encodeValue .uint b == 0) = false := by
    rw [uint_word_zero]
    exact decide_eq_false hb
  change some ((if encodeValue .uint b == 0 then 0 else r) :: tail) =
    ((if b.val = 0 then none else some (Int.tmod a.val b.val)).bind PrimTy.uint.ofInt?).map
      (fun v => encodeValue .uint v :: tail)
  simp only [hz, Bool.false_eq_true, if_false, hb, Option.bind_some]
  rw [he]
  exact (encoded_word r tail).symm

/-- EVM zero is not used as a surrogate for the source failure. -/
theorem uint_div_zero (a : Word) (tail : Stack) :
    guarded (zeroTest ⟨1, by decide⟩) [.op .DIV] divisionFailure (a :: 0 :: tail) =
      some (.error divisionFailure) := by
  rw [guarded_zero ⟨1, by decide⟩ _ (0 : Word) _ _ rfl]
  rfl

theorem uint_mod_zero (a : Word) (tail : Stack) :
    guarded (zeroTest ⟨1, by decide⟩) [.op .MOD] divisionFailure (a :: 0 :: tail) =
      some (.error divisionFailure) := by
  rw [guarded_zero ⟨1, by decide⟩ _ (0 : Word) _ _ rfl]
  rfl


/-- Source-result adapter for the division/remainder failure class. This is
not the generic Val halt-to-panic composition theorem. -/
def divisionOutcome (p : PrimTy) (res : Option p.Denote) (tail : Stack) :
    Except (List UInt8) Stack :=
  res.elim (.error divisionFailure) (fun v => .ok (encodeValue p v :: tail))

private theorem map_outcome (p : PrimTy) (res : Option p.Denote) (tail : Stack)
    (hs : res.isSome = true) :
    (res.map (fun v => encodeValue p v :: tail)).map Except.ok =
      some (divisionOutcome p res tail) := by
  cases res with
  | none => contradiction
  | some v => rfl

theorem uint_div_correct (a b : PrimTy.uint.Denote) (tail : Stack) :
    guarded (zeroTest ⟨1, by decide⟩) [.op .DIV] divisionFailure
      (encodeValue .uint a :: encodeValue .uint b :: tail) =
      some (divisionOutcome .uint (BinOp.evalT .div (p := .uint) rfl a b) tail) := by
  rw [guarded_zero ⟨1, by decide⟩ _ (encodeValue .uint b) _ _ rfl, uint_word_zero]
  by_cases hb : b.val = 0
  · simp only [hb, decide_true, if_true]
    simp only [divisionOutcome, BinOp.evalT, BinOp.evalNum, BinOp.arithInt, hb, if_true, Option.bind_none]
    rfl
  · simp only [hb, decide_false, Bool.false_eq_true, if_false]
    have he : run [Instr.op Op.DIV] (encodeValue PrimTy.uint a :: encodeValue PrimTy.uint b :: tail) =
        Option.map (fun v => encodeValue PrimTy.uint v :: tail) (BinOp.div.evalT rfl a b) := uint_div_body a b hb tail
    have hs : (BinOp.evalT .div (p := .uint) rfl a b).isSome = true := by
      have hh : (run [Instr.op Op.DIV] (encodeValue PrimTy.uint a :: encodeValue PrimTy.uint b :: tail)).isSome =
          (Option.map (fun v => encodeValue PrimTy.uint v :: tail) (BinOp.div.evalT rfl a b)).isSome := congrArg Option.isSome he
      have hleft : (run [.op .DIV] (encodeValue .uint a :: encodeValue .uint b :: tail)).isSome = true := rfl
      rw [hleft, Option.isSome_map] at hh
      exact hh.symm
    rw [he]
    exact map_outcome .uint _ tail hs

theorem uint_mod_correct (a b : PrimTy.uint.Denote) (tail : Stack) :
    guarded (zeroTest ⟨1, by decide⟩) [.op .MOD] divisionFailure
      (encodeValue .uint a :: encodeValue .uint b :: tail) =
      some (divisionOutcome .uint (BinOp.evalT .mod (p := .uint) rfl a b) tail) := by
  rw [guarded_zero ⟨1, by decide⟩ _ (encodeValue .uint b) _ _ rfl, uint_word_zero]
  by_cases hb : b.val = 0
  · simp only [hb, decide_true, if_true]
    simp only [divisionOutcome, BinOp.evalT, BinOp.evalNum, BinOp.arithInt, hb, if_true, Option.bind_none]
    rfl
  · simp only [hb, decide_false, Bool.false_eq_true, if_false]
    have he : run [Instr.op Op.MOD] (encodeValue PrimTy.uint a :: encodeValue PrimTy.uint b :: tail) =
        Option.map (fun v => encodeValue PrimTy.uint v :: tail) (BinOp.mod.evalT rfl a b) := uint_mod_body a b hb tail
    have hs : (BinOp.evalT .mod (p := .uint) rfl a b).isSome = true := by
      have hh : (run [Instr.op Op.MOD] (encodeValue PrimTy.uint a :: encodeValue PrimTy.uint b :: tail)).isSome =
          (Option.map (fun v => encodeValue PrimTy.uint v :: tail) (BinOp.mod.evalT rfl a b)).isSome := congrArg Option.isSome he
      have hleft : (run [.op .MOD] (encodeValue .uint a :: encodeValue .uint b :: tail)).isSome = true := rfl
      rw [hleft, Option.isSome_map] at hh
      exact hh.symm
    rw [he]
    exact map_outcome .uint _ tail hs

#print axioms uint_div_correct
#print axioms uint_mod_correct

#print axioms uint_div_body
#print axioms uint_mod_body
#print axioms uint_div_zero
#print axioms uint_mod_zero

end Solidity.Backend.Scalar
