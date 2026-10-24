import SolidityBridge.Arith.NarrowDivision

namespace Solidity.Bridge.Arith

def intOne : PrimTy.int.Denote := ⟨1, by decide⟩
def intMinusOne : PrimTy.int.Denote := ⟨-1, by decide⟩
def uintOne : PrimTy.uint.Denote := ⟨1, by decide⟩
def uintMax : PrimTy.uint.Denote := ⟨Semantics.uintBound - 1, by decide⟩

theorem int_self_check (x : PrimTy.int.Denote) : PrimTy.int.ofInt? x.val = some x := by
  apply Option.map_injective Subtype.val_injective
  rw [int_check_bitvec, if_pos (int_decode x).symm]
  rfl

def signedScaleW (q : PrimTy.int.Denote) (k : PrimTy.uint.Denote) : Option PrimTy.int.Denote := do
  let a ← UnOp.toUint.evalT rfl q
  let r ← BinOp.mulW.evalT rfl a k
  UnOp.toInt.evalT rfl r

theorem signedScaleW_word (q : PrimTy.int.Denote) (k : PrimTy.uint.Denote) :
    (signedScaleW q k).map Subtype.val =
      some ((BitVec.ofInt 256 q.val * BitVec.ofInt 256 k.val).toInt) := by
  obtain ⟨a, ha, hea⟩ := toUint_word q
  obtain ⟨r, hr, her⟩ := uint_mulW_word a k
  unfold signedScaleW
  rw [ha]
  dsimp only [bind, Option.bind]
  rw [hr]
  dsimp only [Option.bind]
  rw [toInt_word, her, hea]

/-- The full-width source rewrite's conditional denominator and modular sign correction. -/
def signedDivW256 (x y : PrimTy.int.Denote) : Option PrimTy.int.Denote := do
  let d ← if y.val = -1 then UnOp.neg.evalT rfl y else some y
  let q ← BinOp.div.evalT rfl x d
  signedScaleW q (if y.val = -1 then uintMax else uintOne)

theorem signedDivW256_bitvec (x y : BitVec 256) :
    (signedDivW256 (signed x) (signed y)).map Subtype.val =
      if y.toInt = 0 then none else some ((x.sdiv y).toInt) := by
  by_cases hy : y.toInt = -1
  · have hey : signed y = intMinusOne := Subtype.ext hy
    have hneg : UnOp.neg.evalT rfl intMinusOne = some intOne := by decide +kernel
    have hdiv : BinOp.div.evalT rfl (signed x) intOne = some (signed x) := by
      change PrimTy.int.ofInt? (x.toInt.tdiv 1) = _
      rw [Int.tdiv_one]
      exact int_self_check (signed x)
    have hm : BitVec.ofInt 256 uintMax.val = -1#256 := by
      apply BitVec.eq_of_toNat_eq
      decide +kernel
    have hys : y = -1#256 := by
      apply BitVec.eq_of_toInt_eq
      simpa only [(show ((-1#256).toInt) = -1 by decide)] using hy
    unfold signedDivW256
    have hy' : (signed y).val = -1 := hy
    simp only [if_pos hy']
    rw [hey, hneg]
    dsimp only [bind, Option.bind]
    rw [hdiv]
    dsimp only [bind, Option.bind]
    rw [signedScaleW_word, hm, if_neg (by omega)]
    simp only [signed, BitVec.ofInt_toInt, BitVec.mul_neg, BitVec.mul_one]
    congr 1
    rw [BitVec.toInt_sdiv, hy, Int.tdiv_neg, Int.tdiv_one, BitVec.toInt_neg]
  · have hword : y ≠ -1#256 := by
      intro he
      apply hy
      rw [he, (show ((-1#256).toInt) = -1 by decide)]
    have he : (BinOp.div.evalT rfl (signed x) (signed y)).map Subtype.val =
        if y.toInt = 0 then none else some (x.sdiv y).toInt := by
      rw [int_div_exact]
      by_cases hz : y.toInt = 0
      · rw [if_pos hz, if_pos hz]
      · rw [if_neg hz, if_neg hz,
          if_pos (BitVec.toInt_sdiv_of_ne_or_ne x y (Or.inr hword)).symm]
        rw [BitVec.toInt_sdiv_of_ne_or_ne x y (Or.inr hword)]
    unfold signedDivW256
    have hy' : ¬ (signed y).val = -1 := hy
    simp only [if_neg hy']
    dsimp only [bind, Option.bind]
    cases hq : BinOp.div.evalT rfl (signed x) (signed y) with
    | none =>
      rw [hq, Option.map_none] at he
      exact he
    | some q =>
      rw [hq, Option.map_some] at he
      rw [signedScaleW_word]
      have hone : BitVec.ofInt 256 uintOne.val = 1#256 := rfl
      rw [hone, BitVec.mul_one, int_decode]
      exact he

open Widths

/-- The actual signed cast pipeline, at any target width. -/
def readSignedN (n : Nat) (q : PrimTy.int.Denote) : Option PrimTy.int.Denote := do
  let a ← UnOp.toUint.evalT rfl q
  if h : n < 256 then
    signedWord n (pow_uint_range (n - 1) (by omega)) (pow_uint_range n h) a
  else UnOp.toInt.evalT rfl a

theorem readSignedN_correct (n : Nat) (hn0 : 0 < n) (hn : n ≤ 256) (q : PrimTy.int.Denote) :
    (readSignedN n q).map Subtype.val = some (BitVec.ofInt n q.val).toInt := by
  obtain ⟨a, ha, hea⟩ := toUint_word q
  unfold readSignedN
  rw [ha]
  dsimp only [bind, Option.bind]
  split
  · rename_i h
    rw [signedWord_correct n hn0 h]
    have he : BitVec.ofInt n a.val = BitVec.ofInt n q.val := by
      have hc : (BitVec.ofInt 256 a.val).setWidth n = (BitVec.ofInt 256 q.val).setWidth n :=
        congrArg (BitVec.setWidth n) hea
      simpa only [setWidth_full_word n hn] using hc
    rw [he]
  · have he : n = 256 := by omega
    subst n
    rw [toInt_word, hea]

theorem signedN_not_intMin {n : Nat} (hn : n < 256) (x : BitVec n) :
    x.signExtend 256 ≠ BitVec.intMin 256 := by
  intro h
  have he : (x.signExtend 256).toInt = (BitVec.intMin 256).toInt := congrArg BitVec.toInt h
  rw [BitVec.toInt_signExtend_of_le (Nat.le_of_lt hn), BitVec.toInt_intMin_of_pos (by decide)] at he
  have hx : -(2 : Int) ^ (n - 1) ≤ x.toInt := BitVec.le_toInt x
  have hp : (2 : Int) ^ (n - 1) ≤ 2 ^ 254 := by
    have hp' : (2 : Nat) ^ (n - 1) ≤ 2 ^ 254 :=
      Nat.pow_le_pow_right (by decide) (show n - 1 ≤ 254 by omega)
    exact_mod_cast hp'
  simp only [Nat.reduceSub] at he
  omega

/-- The intermediate quotient of genuine narrow operands cannot overflow int256. -/
theorem int_div_narrow (n : Nat) (hn : n < 256) (x y : BitVec n) :
    (BinOp.div.evalT rfl (signedN (Nat.le_of_lt hn) x) (signedN (Nat.le_of_lt hn) y)).map
      Subtype.val = if y.toInt = 0 then none else some (x.toInt.tdiv y.toInt) := by
  rw [← signedN_extend (Nat.le_of_lt hn) x, ← signedN_extend (Nat.le_of_lt hn) y, int_div_exact]
  simp only [BitVec.toInt_signExtend_of_le (Nat.le_of_lt hn)]
  by_cases hz : y.toInt = 0
  · rw [if_pos hz, if_pos hz]
  · rw [if_neg hz, if_neg hz]
    have he : ((x.signExtend 256).sdiv (y.signExtend 256)).toInt = x.toInt.tdiv y.toInt := by
      rw [BitVec.toInt_sdiv_of_ne_or_ne _ _ (Or.inl (signedN_not_intMin hn x)),
        BitVec.toInt_signExtend_of_le (Nat.le_of_lt hn),
        BitVec.toInt_signExtend_of_le (Nat.le_of_lt hn)]
    rw [he, if_pos rfl]

/-- Precisely the two source strategies: narrow quotient then cast, or the full-width correction. -/
def signedDivWrap (n : Nat) (x y : PrimTy.int.Denote) : Option PrimTy.int.Denote :=
  if n < 256 then (BinOp.div.evalT rfl x y).bind (readSignedN n)
  else signedDivW256 x y

theorem int_divW_all_widths {n : Nat} (hn0 : 0 < n) (hn : n ≤ 256) (x y : BitVec n) :
    (signedDivWrap n (signedN hn x) (signedN hn y)).map Subtype.val =
      if y.toInt = 0 then none else some (x.sdiv y).toInt := by
  unfold signedDivWrap
  split
  · rename_i hw
    have he : (BinOp.div.evalT rfl (signedN hn x) (signedN hn y)).map Subtype.val =
        if y.toInt = 0 then none else some (x.toInt.tdiv y.toInt) := int_div_narrow n hw x y
    cases hq : BinOp.div.evalT rfl (signedN hn x) (signedN hn y) with
    | none =>
      rw [hq, Option.map_none] at he
      by_cases hz : y.toInt = 0
      · rw [if_pos hz]
        rfl
      · rw [if_neg hz] at he
        cases he
    | some q =>
      rw [hq, Option.map_some] at he
      by_cases hz : y.toInt = 0
      · rw [if_pos hz] at he
        cases he
      · rw [if_neg hz] at he
        dsimp only [Option.bind]
        rw [readSignedN_correct n hn0 hn, Option.some.inj he, if_neg hz,
          BitVec.toInt_ofInt, BitVec.toInt_sdiv]
  · have hw : n = 256 := by omega
    subst n
    exact signedDivW256_bitvec x y

end Solidity.Bridge.Arith

#print axioms Solidity.Bridge.Arith.signedScaleW_word
#print axioms Solidity.Bridge.Arith.signedDivW256_bitvec

#print axioms Solidity.Bridge.Arith.readSignedN_correct
#print axioms Solidity.Bridge.Arith.int_div_narrow
#print axioms Solidity.Bridge.Arith.int_divW_all_widths
