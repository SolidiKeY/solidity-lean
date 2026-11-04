import Solidity.Backend.PrimitivePackets.UnsignedDiv.Data

/-! Numeric transport consumes the published universal unsigned DIV/MOD body
laws. It does not prove a second arithmetic interpreter or assume a result. -/
namespace Solidity.Backend.PrimitivePackets.UnsignedDiv

private theorem value_of_some {n : Int} {v : Uint}
    (h : PrimTy.uint.ofInt? n = some v) : v.val = n := by
  dsimp only [PrimTy.ofInt?] at h
  split at h
  · exact (congrArg Subtype.val (Option.some.inj h)).symm
  · cases h

theorem div_result (a d : Uint) (hd : d.val ≠ 0) :
    ∃ v : Uint, BinOp.div.evalT rfl a d = some v ∧ v.val = a.val.tdiv d.val := by
  have hc : Scalar.run [.op .DIV]
      [Scalar.encodeValue .uint a, Scalar.encodeValue .uint d] =
      (BinOp.div.evalT rfl a d).map (fun v => [Scalar.encodeValue .uint v]) :=
    Scalar.uint_div_body a d hd []
  cases hv : BinOp.div.evalT rfl a d with
  | none => rw [hv] at hc; cases hc
  | some v =>
    refine ⟨v, rfl, ?_⟩
    apply value_of_some
    simpa only [BinOp.evalT, BinOp.evalNum, BinOp.arithInt, hd, if_false,
      Option.bind_some] using hv

theorem mod_result (a d : Uint) (hd : d.val ≠ 0) :
    ∃ v : Uint, BinOp.mod.evalT rfl a d = some v ∧ v.val = a.val.tmod d.val := by
  have hc : Scalar.run [.op .MOD]
      [Scalar.encodeValue .uint a, Scalar.encodeValue .uint d] =
      (BinOp.mod.evalT rfl a d).map (fun v => [Scalar.encodeValue .uint v]) :=
    Scalar.uint_mod_body a d hd []
  cases hv : BinOp.mod.evalT rfl a d with
  | none => rw [hv] at hc; cases hc
  | some v =>
    refine ⟨v, rfl, ?_⟩
    apply value_of_some
    simpa only [BinOp.evalT, BinOp.evalNum, BinOp.arithInt, hd, if_false,
      Option.bind_some] using hv

private theorem source_int_result (D : Source.Layout) (c : Bool) (v : Uint) :
    Source.intRes Source.IntTy.u256 c v.val = .ok (sourceUInt D v) := by
  have hr : 0 ≤ v.val ∧ v.val < ((2 ^ 256 : Nat) : Int) := Scalar.uint_range v
  have bound : Source.IntTy.u256.lo ≤ v.val ∧ v.val ≤ Source.IntTy.u256.hi := by
    change 0 ≤ v.val ∧ v.val ≤ (2 ^ 256 : Nat) - 1
    omega
  simp only [Source.intRes, bound]
  rfl

theorem source_div_result (D : Source.Layout) (c : Bool) (a d v : Uint)
    (hd : d.val ≠ 0) (hv : v.val = a.val.tdiv d.val) :
    Source.intBin Source.IntTy.u256 c .div a.val d.val = .ok (sourceUInt D v) := by
  simp only [Source.intBin, hd, if_false]
  rw [← hv]
  exact source_int_result D c v

theorem source_mod_result (D : Source.Layout) (c : Bool) (a d v : Uint)
    (hd : d.val ≠ 0) (hv : v.val = a.val.tmod d.val) :
    Source.intBin Source.IntTy.u256 c .mod a.val d.val = .ok (sourceUInt D v) := by
  simp only [Source.intBin, hd, if_false]
  rw [← hv]
  exact source_int_result D c v

/-- Payload agreement belongs to the published scalar guard component. The
symbolic compiler's `Out.revert` has no payload; it is not this byte list. -/
theorem scalar_panic_bytes : Scalar.divisionFailure = Source.panicData .divZero := by
  decide

end Solidity.Backend.PrimitivePackets.UnsignedDiv
