import Solidity.Backend.Scalar.WidthGuards

/-! All byte-width wrapping arithmetic laws over the pinned intrinsic numeric
carriers. Signed operands use their signed integer readings; emitted arithmetic
is ADD/SUB/MUL followed by the proven width cleanup. These are scalar slice
contracts, not a theorem about the frontend's unchecked rewriting pass. -/
namespace Solidity.Backend.Scalar

def widthResidue (w : Fin 32) (n : Int) : Nat := (n % ((2^widthBits w:Nat):Int)).toNat

def wrapUnsigned (w : Fin 32) (n : Int) : Word := BitVec.ofNat 256 (widthResidue w n)
def wrapSigned (w : Fin 32) (n : Int) : Word :=
  let r := widthResidue w n
  BitVec.ofInt 256 (if r<2^(widthBits w-1) then (r:Int) else (r:Int)-((2^widthBits w:Nat):Int))

theorem ofInt_low (w : Fin 32) (n : Int) :
    (BitVec.ofInt 256 n).toNat % 2^widthBits w = widthResidue w n := by
  have hW : (0:Int)<((2^256:Nat):Int) := by decide
  have hd : ((2^widthBits w:Nat):Int) ∣ ((2^256:Nat):Int) :=
    Int.natCast_dvd_natCast.mpr (Nat.pow_dvd_pow 2 (widthBits_bounds w).2)
  have hn : 0 ≤ n % ((2 ^ 256 : Nat) : Int) := Int.emod_nonneg n (show ((2^256:Nat):Int) ≠ 0 by omega)
  rw [BitVec.toNat_ofInt]
  change (n % ((2^256:Nat):Int)).toNat % 2^widthBits w = _
  calc
    (n % ((2^256:Nat):Int)).toNat % 2^widthBits w =
        ((n % ((2^256:Nat):Int)) % ((2^widthBits w:Nat):Int)).toNat :=
      (Int.toNat_emod hn (Int.natCast_nonneg (2^widthBits w))).symm
    _ = widthResidue w n := congrArg Int.toNat (Int.emod_emod_of_dvd n hd)

theorem clean_ofInt_unsigned (w : Fin 32) (n : Int) :
    unsignedClean w (BitVec.ofInt 256 n) = wrapUnsigned w n := by
  simp only [unsignedClean, ofInt_low, wrapUnsigned]

theorem clean_ofInt_signed (w : Fin 32) (n : Int) :
    signedClean w (BitVec.ofInt 256 n) = wrapSigned w n := by
  simp only [signedClean, ofInt_low, wrapSigned]

def unsigned_addAt (w : Fin 32) : Program := [.op .ADD] ++ unsignedCode w

theorem unsigned_addAt_correct (w : Fin 32) (a b : PrimTy.uint.Denote) (tail : Stack) :
    run (unsigned_addAt w) (encodeValue .uint a::encodeValue .uint b::tail) =
      some (wrapUnsigned w (a.val + b.val)::tail) := by
  apply run_comp (p := [.op .ADD]) (q := unsignedCode w)
    (t := (BitVec.ofInt 256 (a.val + b.val))::tail)
  · change some ((BitVec.ofInt 256 a.val + BitVec.ofInt 256 b.val)::tail) = _
    rw [← BitVec.ofInt_add]
  · rw [unsigned_correct, clean_ofInt_unsigned]

#print axioms unsigned_addAt_correct

def unsigned_subAt (w : Fin 32) : Program := [.op .SUB] ++ unsignedCode w

theorem unsigned_subAt_correct (w : Fin 32) (a b : PrimTy.uint.Denote) (tail : Stack) :
    run (unsigned_subAt w) (encodeValue .uint a::encodeValue .uint b::tail) =
      some (wrapUnsigned w (a.val - b.val)::tail) := by
  apply run_comp (p := [.op .SUB]) (q := unsignedCode w)
    (t := (BitVec.ofInt 256 (a.val - b.val))::tail)
  · change some ((BitVec.ofInt 256 a.val - BitVec.ofInt 256 b.val)::tail) = _
    rw [Int.sub_eq_add_neg, BitVec.ofInt_add, BitVec.ofInt_neg, BitVec.sub_eq_add_neg]
  · rw [unsigned_correct, clean_ofInt_unsigned]

#print axioms unsigned_subAt_correct

def unsigned_mulAt (w : Fin 32) : Program := [.op .MUL] ++ unsignedCode w

theorem unsigned_mulAt_correct (w : Fin 32) (a b : PrimTy.uint.Denote) (tail : Stack) :
    run (unsigned_mulAt w) (encodeValue .uint a::encodeValue .uint b::tail) =
      some (wrapUnsigned w (a.val * b.val)::tail) := by
  apply run_comp (p := [.op .MUL]) (q := unsignedCode w)
    (t := (BitVec.ofInt 256 (a.val * b.val))::tail)
  · change some ((BitVec.ofInt 256 a.val * BitVec.ofInt 256 b.val)::tail) = _
    rw [← BitVec.ofInt_mul]
  · rw [unsigned_correct, clean_ofInt_unsigned]

#print axioms unsigned_mulAt_correct

def signed_addAt (w : Fin 32) : Program := [.op .ADD] ++ signedCode w

theorem signed_addAt_correct (w : Fin 32) (a b : PrimTy.int.Denote) (tail : Stack) :
    run (signed_addAt w) (encodeValue .int a::encodeValue .int b::tail) =
      some (wrapSigned w (a.val + b.val)::tail) := by
  apply run_comp (p := [.op .ADD]) (q := signedCode w)
    (t := (BitVec.ofInt 256 (a.val + b.val))::tail)
  · change some ((BitVec.ofInt 256 a.val + BitVec.ofInt 256 b.val)::tail) = _
    rw [← BitVec.ofInt_add]
  · rw [signed_correct, clean_ofInt_signed]

#print axioms signed_addAt_correct

def signed_subAt (w : Fin 32) : Program := [.op .SUB] ++ signedCode w

theorem signed_subAt_correct (w : Fin 32) (a b : PrimTy.int.Denote) (tail : Stack) :
    run (signed_subAt w) (encodeValue .int a::encodeValue .int b::tail) =
      some (wrapSigned w (a.val - b.val)::tail) := by
  apply run_comp (p := [.op .SUB]) (q := signedCode w)
    (t := (BitVec.ofInt 256 (a.val - b.val))::tail)
  · change some ((BitVec.ofInt 256 a.val - BitVec.ofInt 256 b.val)::tail) = _
    rw [Int.sub_eq_add_neg, BitVec.ofInt_add, BitVec.ofInt_neg, BitVec.sub_eq_add_neg]
  · rw [signed_correct, clean_ofInt_signed]

#print axioms signed_subAt_correct

def signed_mulAt (w : Fin 32) : Program := [.op .MUL] ++ signedCode w

theorem signed_mulAt_correct (w : Fin 32) (a b : PrimTy.int.Denote) (tail : Stack) :
    run (signed_mulAt w) (encodeValue .int a::encodeValue .int b::tail) =
      some (wrapSigned w (a.val * b.val)::tail) := by
  apply run_comp (p := [.op .MUL]) (q := signedCode w)
    (t := (BitVec.ofInt 256 (a.val * b.val))::tail)
  · change some ((BitVec.ofInt 256 a.val * BitVec.ofInt 256 b.val)::tail) = _
    rw [← BitVec.ofInt_mul]
  · rw [signed_correct, clean_ofInt_signed]

#print axioms signed_mulAt_correct

example : run (unsigned_subAt ⟨0, by decide⟩) [0,1,99] = some [255,99] := by decide +kernel
example : run (signed_addAt ⟨0, by decide⟩) [127,1,99] =
    some [BitVec.ofInt 256 (-128),99] := by decide +kernel
example : run (signed_mulAt ⟨0, by decide⟩) [BitVec.ofInt 256 (-128),2,99] = some [0,99] := by decide +kernel


/-- Raw EVM zero is explicit; source zero-divisor rejection is proved in Division/SignedGuards. -/
def unsigned_divAt (w : Fin 32) : Program := [.op .DIV] ++ unsignedCode w

theorem unsigned_divAt_correct (w : Fin 32) (a b : PrimTy.uint.Denote) (tail : Stack) :
    run (unsigned_divAt w) (encodeValue .uint a::encodeValue .uint b::tail) =
      some (wrapUnsigned w (if b.val=0 then 0 else (((a.val.toNat / b.val.toNat):Nat):Int))::tail) := by
  apply run_comp (p := [.op .DIV]) (q := unsignedCode w)
    (t := (BitVec.ofInt 256 (if b.val=0 then 0 else (((a.val.toNat / b.val.toNat):Nat):Int)))::tail)
  · change some ((if encodeValue .uint b == 0 then 0 else BitVec.ofNat 256 ((encodeValue .uint a).toNat / (encodeValue .uint b).toNat))::tail) = _
    rw [uint_word_zero]
    rw [encode_uint_toNat, encode_uint_toNat]
    by_cases hb : b.val=0
    · simp only [hb, decide_true, if_true]
      rfl
    · simp only [hb, decide_false, Bool.false_eq_true, if_false]
      exact congrArg (fun r : Word => some (r::tail)) (BitVec.ofInt_natCast 256 _).symm
  · rw [unsigned_correct, clean_ofInt_unsigned]

#print axioms unsigned_divAt_correct

/-- Raw EVM zero is explicit; source zero-divisor rejection is proved in Division/SignedGuards. -/
def unsigned_modAt (w : Fin 32) : Program := [.op .MOD] ++ unsignedCode w

theorem unsigned_modAt_correct (w : Fin 32) (a b : PrimTy.uint.Denote) (tail : Stack) :
    run (unsigned_modAt w) (encodeValue .uint a::encodeValue .uint b::tail) =
      some (wrapUnsigned w (if b.val=0 then 0 else (((a.val.toNat % b.val.toNat):Nat):Int))::tail) := by
  apply run_comp (p := [.op .MOD]) (q := unsignedCode w)
    (t := (BitVec.ofInt 256 (if b.val=0 then 0 else (((a.val.toNat % b.val.toNat):Nat):Int)))::tail)
  · change some ((if encodeValue .uint b == 0 then 0 else BitVec.ofNat 256 ((encodeValue .uint a).toNat % (encodeValue .uint b).toNat))::tail) = _
    rw [uint_word_zero]
    rw [encode_uint_toNat, encode_uint_toNat]
    by_cases hb : b.val=0
    · simp only [hb, decide_true, if_true]
      rfl
    · simp only [hb, decide_false, Bool.false_eq_true, if_false]
      exact congrArg (fun r : Word => some (r::tail)) (BitVec.ofInt_natCast 256 _).symm
  · rw [unsigned_correct, clean_ofInt_unsigned]

#print axioms unsigned_modAt_correct

/-- Raw EVM zero is explicit; source zero-divisor rejection is proved in Division/SignedGuards. -/
def signed_divAt (w : Fin 32) : Program := [.op .SDIV] ++ signedCode w

theorem signed_divAt_correct (w : Fin 32) (a b : PrimTy.int.Denote) (tail : Stack) :
    run (signed_divAt w) (encodeValue .int a::encodeValue .int b::tail) =
      some (wrapSigned w (if b.val=0 then 0 else a.val.tdiv b.val)::tail) := by
  apply run_comp (p := [.op .SDIV]) (q := signedCode w)
    (t := (BitVec.ofInt 256 (if b.val=0 then 0 else a.val.tdiv b.val))::tail)
  · change some ((if encodeValue .int b == 0 then 0 else BitVec.ofInt 256 ((encodeValue .int a).toInt.tdiv (encodeValue .int b).toInt))::tail) = _
    rw [int_word_zero]
    rw [encode_int_toInt, encode_int_toInt]
    by_cases hb : b.val=0
    · simp only [hb, decide_true, if_true]
      rfl
    · simp only [hb, decide_false, Bool.false_eq_true, if_false]
  · rw [signed_correct, clean_ofInt_signed]

#print axioms signed_divAt_correct

/-- Raw EVM zero is explicit; source zero-divisor rejection is proved in Division/SignedGuards. -/
def signed_modAt (w : Fin 32) : Program := [.op .SMOD] ++ signedCode w

theorem signed_modAt_correct (w : Fin 32) (a b : PrimTy.int.Denote) (tail : Stack) :
    run (signed_modAt w) (encodeValue .int a::encodeValue .int b::tail) =
      some (wrapSigned w (if b.val=0 then 0 else a.val.tmod b.val)::tail) := by
  apply run_comp (p := [.op .SMOD]) (q := signedCode w)
    (t := (BitVec.ofInt 256 (if b.val=0 then 0 else a.val.tmod b.val))::tail)
  · change some ((if encodeValue .int b == 0 then 0 else BitVec.ofInt 256 ((encodeValue .int a).toInt.tmod (encodeValue .int b).toInt))::tail) = _
    rw [int_word_zero]
    rw [encode_int_toInt, encode_int_toInt]
    by_cases hb : b.val=0
    · simp only [hb, decide_true, if_true]
      rfl
    · simp only [hb, decide_false, Bool.false_eq_true, if_false]
  · rw [signed_correct, clean_ofInt_signed]

#print axioms signed_modAt_correct


def unsigned_powAt (w : Fin 32) : Program := [.op .EXP] ++ unsignedCode w

theorem unsigned_powAt_correct (w : Fin 32) (a b : PrimTy.uint.Denote) (tail : Stack) :
    run (unsigned_powAt w) (encodeValue .uint a::encodeValue .uint b::tail) =
      some (wrapUnsigned w (a.val^b.val.toNat)::tail) := by
  apply run_comp (p := [.op .EXP]) (q := unsignedCode w)
    (t := (BitVec.ofInt 256 (a.val^b.val.toNat))::tail)
  · change some (BitVec.ofNat 256
      ((encodeValue .uint a).toNat^(encodeValue .uint b).toNat)::tail) = _
    rw [encode_uint_toNat, encode_uint_toNat]
    have ha : a.val=(a.val.toNat:Int) := by have : 0 ≤ a.val ∧ a.val < ((2 ^ 256 : Nat) : Int) := uint_range a; omega
    rw [ha, ← Int.natCast_pow, BitVec.ofInt_natCast]
    simp only [Int.toNat_natCast]
  · rw [unsigned_correct, clean_ofInt_unsigned]

#print axioms unsigned_powAt_correct

#print axioms ofInt_low
end Solidity.Backend.Scalar
