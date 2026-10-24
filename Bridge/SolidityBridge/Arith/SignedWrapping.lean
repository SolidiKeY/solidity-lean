import SolidityBridge.Arith.Casts
import SolidityBridge.Arith.Wrapping
import Mathlib.Data.Option.Basic

set_option maxRecDepth 2048

namespace Solidity.Bridge.Arith

theorem toUint_signed (x : BitVec 256) :
    UnOp.toUint.evalT rfl (signed x) = some (unsigned x) := by
  apply Option.map_injective Subtype.val_injective
  simpa only [signed, unsigned, BitVec.ofInt_toInt] using int_toUint_bitvec (signed x)

theorem toInt_unsigned (x : BitVec 256) :
    UnOp.toInt.evalT rfl (unsigned x) = some (signed x) := by
  apply Option.map_injective Subtype.val_injective
  exact uint_toInt_bitvec x

/-- Core casts and wrapping operation, exactly the full-width signed lowering. -/
def signedAddW (x y : PrimTy.int.Denote) : Option PrimTy.int.Denote := do
  let a ← UnOp.toUint.evalT rfl x
  let b ← UnOp.toUint.evalT rfl y
  let r ← BinOp.addW.evalT rfl a b
  UnOp.toInt.evalT rfl r

def signedSubW (x y : PrimTy.int.Denote) : Option PrimTy.int.Denote := do
  let a ← UnOp.toUint.evalT rfl x
  let b ← UnOp.toUint.evalT rfl y
  let r ← BinOp.subW.evalT rfl a b
  UnOp.toInt.evalT rfl r

def signedMulW (x y : PrimTy.int.Denote) : Option PrimTy.int.Denote := do
  let a ← UnOp.toUint.evalT rfl x
  let b ← UnOp.toUint.evalT rfl y
  let r ← BinOp.mulW.evalT rfl a b
  UnOp.toInt.evalT rfl r

theorem toUint_word (x : PrimTy.int.Denote) :
    ∃ a : PrimTy.uint.Denote, UnOp.toUint.evalT rfl x = some a ∧
      BitVec.ofInt 256 a.val = BitVec.ofInt 256 x.val := by
  have he : (UnOp.toUint.evalT rfl x).map Subtype.val =
      some ((BitVec.ofInt 256 x.val).toNat : Int) := int_toUint_bitvec x
  cases h : UnOp.toUint.evalT rfl x with
  | none => rw [h] at he; cases he
  | some a =>
    rw [h, Option.map_some] at he
    refine ⟨a, rfl, ?_⟩
    rw [Option.some.inj he, BitVec.ofInt_natCast, BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem toInt_word (x : PrimTy.uint.Denote) :
    (UnOp.toInt.evalT rfl x).map Subtype.val = some (BitVec.ofInt 256 x.val).toInt := by
  have hx : unsigned (BitVec.ofInt 256 x.val) = x := Subtype.ext (uint_decode x)
  simpa only [hx] using uint_toInt_bitvec (BitVec.ofInt 256 x.val)

theorem uint_addW_word (x y : PrimTy.uint.Denote) :
    ∃ r : PrimTy.uint.Denote, BinOp.addW.evalT rfl x y = some r ∧
      BitVec.ofInt 256 r.val = BitVec.ofInt 256 x.val + BitVec.ofInt 256 y.val := by
  have he : (BinOp.addW.evalT rfl x y).map Subtype.val =
      some ((BitVec.ofInt 256 x.val + BitVec.ofInt 256 y.val).toNat : Int) := uint_addW_bitvec x y
  cases h : BinOp.addW.evalT rfl x y with
  | none => rw [h] at he; cases he
  | some r =>
    rw [h, Option.map_some] at he
    refine ⟨r, rfl, ?_⟩
    rw [Option.some.inj he, BitVec.ofInt_natCast, BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem signed_addW_bitvec (x y : PrimTy.int.Denote) :
    (signedAddW x y).map Subtype.val =
      some ((BitVec.ofInt 256 x.val + BitVec.ofInt 256 y.val).toInt) := by
  obtain ⟨a, ha, hea⟩ := toUint_word x
  obtain ⟨b, hb, heb⟩ := toUint_word y
  obtain ⟨r, hr, her⟩ := uint_addW_word a b
  unfold signedAddW
  rw [ha, hb]
  dsimp only [bind, Option.bind]
  rw [hr]
  dsimp only [Option.bind]
  rw [toInt_word, her, hea, heb]

theorem uint_subW_word (x y : PrimTy.uint.Denote) :
    ∃ r : PrimTy.uint.Denote, BinOp.subW.evalT rfl x y = some r ∧
      BitVec.ofInt 256 r.val = BitVec.ofInt 256 x.val - BitVec.ofInt 256 y.val := by
  have he : (BinOp.subW.evalT rfl x y).map Subtype.val =
      some ((BitVec.ofInt 256 x.val - BitVec.ofInt 256 y.val).toNat : Int) := uint_subW_bitvec x y
  cases h : BinOp.subW.evalT rfl x y with
  | none => rw [h] at he; cases he
  | some r =>
    rw [h, Option.map_some] at he
    refine ⟨r, rfl, ?_⟩
    rw [Option.some.inj he, BitVec.ofInt_natCast, BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem signed_subW_bitvec (x y : PrimTy.int.Denote) :
    (signedSubW x y).map Subtype.val =
      some ((BitVec.ofInt 256 x.val - BitVec.ofInt 256 y.val).toInt) := by
  obtain ⟨a, ha, hea⟩ := toUint_word x
  obtain ⟨b, hb, heb⟩ := toUint_word y
  obtain ⟨r, hr, her⟩ := uint_subW_word a b
  unfold signedSubW
  rw [ha, hb]
  dsimp only [bind, Option.bind]
  rw [hr]
  dsimp only [Option.bind]
  rw [toInt_word, her, hea, heb]

theorem uint_mulW_word (x y : PrimTy.uint.Denote) :
    ∃ r : PrimTy.uint.Denote, BinOp.mulW.evalT rfl x y = some r ∧
      BitVec.ofInt 256 r.val = BitVec.ofInt 256 x.val * BitVec.ofInt 256 y.val := by
  have he : (BinOp.mulW.evalT rfl x y).map Subtype.val =
      some ((BitVec.ofInt 256 x.val * BitVec.ofInt 256 y.val).toNat : Int) := uint_mulW_bitvec x y
  cases h : BinOp.mulW.evalT rfl x y with
  | none => rw [h] at he; cases he
  | some r =>
    rw [h, Option.map_some] at he
    refine ⟨r, rfl, ?_⟩
    rw [Option.some.inj he, BitVec.ofInt_natCast, BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem signed_mulW_bitvec (x y : PrimTy.int.Denote) :
    (signedMulW x y).map Subtype.val =
      some ((BitVec.ofInt 256 x.val * BitVec.ofInt 256 y.val).toInt) := by
  obtain ⟨a, ha, hea⟩ := toUint_word x
  obtain ⟨b, hb, heb⟩ := toUint_word y
  obtain ⟨r, hr, her⟩ := uint_mulW_word a b
  unfold signedMulW
  rw [ha, hb]
  dsimp only [bind, Option.bind]
  rw [hr]
  dsimp only [Option.bind]
  rw [toInt_word, her, hea, heb]
def signedPowW (x : PrimTy.int.Denote) (y : PrimTy.uint.Denote) : Option PrimTy.int.Denote := do
  let a ← UnOp.toUint.evalT rfl x
  let r ← BinOp.powW.evalT rfl a y
  UnOp.toInt.evalT rfl r

theorem uint_powW_word (x y : PrimTy.uint.Denote) :
    ∃ r : PrimTy.uint.Denote, BinOp.powW.evalT rfl x y = some r ∧
      BitVec.ofInt 256 r.val = (BitVec.ofInt 256 x.val) ^ y.val.toNat := by
  have he : (BinOp.powW.evalT rfl x y).map Subtype.val =
      some (((BitVec.ofInt 256 x.val) ^ y.val.toNat).toNat : Int) := uint_powW_bitvec x y
  cases h : BinOp.powW.evalT rfl x y with
  | none => rw [h] at he; cases he
  | some r =>
    rw [h, Option.map_some] at he
    refine ⟨r, rfl, ?_⟩
    rw [Option.some.inj he, BitVec.ofInt_natCast, BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem signed_powW_bitvec (x : PrimTy.int.Denote) (y : PrimTy.uint.Denote) :
    (signedPowW x y).map Subtype.val =
      some (((BitVec.ofInt 256 x.val) ^ y.val.toNat).toInt) := by
  obtain ⟨a, ha, hea⟩ := toUint_word x
  obtain ⟨r, hr, her⟩ := uint_powW_word a y
  unfold signedPowW
  rw [ha]
  dsimp only [bind, Option.bind]
  rw [hr]
  dsimp only [Option.bind]
  rw [toInt_word, her, hea]

/-- The exact 0 -% uint(x), cast back, used for signed unchecked negation. -/
def signedNegW (x : PrimTy.int.Denote) : Option PrimTy.int.Denote :=
  signedSubW PrimTy.int.dflt x

theorem signed_negW_bitvec (x : PrimTy.int.Denote) :
    (signedNegW x).map Subtype.val = some (-BitVec.ofInt 256 x.val).toInt := by
  simpa only [signedNegW, PrimTy.dflt, BitVec.ofInt_ofNat, BitVec.zero_sub] using
    signed_subW_bitvec PrimTy.int.dflt x


end Solidity.Bridge.Arith

#print axioms Solidity.Bridge.Arith.signed_addW_bitvec
#print axioms Solidity.Bridge.Arith.signed_subW_bitvec
#print axioms Solidity.Bridge.Arith.signed_mulW_bitvec

#print axioms Solidity.Bridge.Arith.signed_powW_bitvec
#print axioms Solidity.Bridge.Arith.signed_negW_bitvec
