import Solidity.Lowering.V07.SourceReads
import Solidity.Lowering.V07.ContextMapWrite
import Solidity.Yul.Views.ScalarCodecs

/-! Same-width bytesN local transport. Existing big-endian source values and
native UInt carriers are reused; no storage layout or ABI encoding is selected. -/
namespace Solidity.Lowering.V07.FixedBytesAssignment

theorem range (n : Nat) (width : 1 ≤ n ∧ n ≤ 32) (bs : List UInt8) (length : bs.length = n) :
    Source.IntTy.u256.lo ≤ (Source.bytesNat bs : Int) ∧
    (Source.bytesNat bs : Int) ≤ Source.IntTy.u256.hi := by
  have raw := Yul.Views.scalar_beValue_bound bs
  rw [length] at raw
  have cap : 256 ^ n ≤ 2 ^ 256 := by
    calc 256 ^ n ≤ 256 ^ 32 := Nat.pow_le_pow_right (by decide) width.2
         _ = 2 ^ 256 := by decide
  change Source.bytesNat bs < 256 ^ n at raw
  change 0 ≤ (Source.bytesNat bs : Int) ∧ (Source.bytesNat bs : Int) ≤ ((2^256-1 : Nat) : Int)
  omega

def value (n : Nat) (width : 1 ≤ n ∧ n ≤ 32) (bs : List UInt8) (length : bs.length = n) :
    PrimTy.uint.Denote := integerValue .u256 (Source.bytesNat bs) (range n width bs length)
def Rel {D : Source.Layout} (n : Nat) (width : 1 ≤ n ∧ n ≤ 32)
    (source : Source.Val D (.fixedBytes n width)) (target : PrimTy.uint.Denote) : Prop :=
  source.key = PrimTy.num? target

theorem related {D : Source.Layout} (n : Nat) (width : 1 ≤ n ∧ n ≤ 32)
    (bs : List UInt8) (length : bs.length = n) :
    Rel n width (.fixedBytes bs length : Source.Val D (.fixedBytes n width)) (value n width bs length) := by
  rfl

theorem read_value {D : Source.Layout} (n : Nat) (width : 1 ≤ n ∧ n ≤ 32)
    (bs : List UInt8) (length : bs.length = n) (v : PrimTy.uint.Denote)
    (agrees : Rel n width (.fixedBytes bs length : Source.Val D (.fixedBytes n width)) v) :
    v = value n width bs length := by
  apply Subtype.ext
  change some (Source.bytesNat bs : Int) = some v.val at agrees
  exact (Option.some.inj agrees).symm

theorem decode_value (n : Nat) (width : 1 ≤ n ∧ n ≤ 32) (bs : List UInt8) (length : bs.length = n) :
    Source.beBytes n (value n width bs length).val.toNat = bs := by
  change Source.beBytes n (Source.bytesNat bs) = bs
  simpa only [Source.bytesNat,length] using Yul.Views.scalar_beBytes_value bs

theorem contents_reflect (n : Nat) (width : 1 ≤ n ∧ n ≤ 32) (xs ys : List UInt8)
    (hx : xs.length = n) (hy : ys.length = n) (same : value n width xs hx = value n width ys hy) : xs = ys := by
  have encoded : Source.bytesNat xs = Source.bytesNat ys := by
    have h := congrArg Subtype.val same
    change (Source.bytesNat xs : Int) = (Source.bytesNat ys : Int) at h
    exact Int.ofNat.inj h
  have xi := Yul.Views.scalar_beBytes_value xs
  have yi := Yul.Views.scalar_beBytes_value ys
  rw [hx] at xi
  rw [hy] at yi
  exact xi.symm.trans ((congrArg (Source.beBytes n) encoded).trans yi)

theorem transport {E : Source.Env} {srcΓ : Source.RCtx} {C : Contract} {Γ : Ctx}
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat) (source : Source.EMState E srcΓ) (target : State C Γ)
    (n : Nat) (width : 1 ≤ n ∧ n ≤ 32) (m : ContextMap srcΓ Γ)
    (R : (τ : Source.STy) → (u : LTy) → Source.Val E.layout τ → u.TDenote C target.H → Prop)
    (aligned : m.Related R source.1 target.env)
    (reflect : ∀ (v : Source.Val E.layout (.fixedBytes n width)) (x : PrimTy.uint.Denote),
      R (.fixedBytes n width) (.val .uint) v x → Rel n width v x)
    (i r : Source.Idx srcΓ (.fixedBytes n width)) (j k : Idx Γ (.val .uint))
    (writeMap : m.slot i = ⟨.val .uint,j⟩) (readMap : m.slot r = ⟨.val .uint,k⟩)
    (bs : List UInt8) (length : bs.length = n) (read : source.1.get r = .fixedBytes bs length) :
    (Source.evalE G F (fuel+2) (.assign (.local i) (.local r))).run source =
      (.ok (.val (.fixedBytes bs length)),(source.1.set i (.fixedBytes bs length),source.2)) ∧
    (assignLocalOperand j k).run target =
      .ok (⟨target.setLocal j (value n width bs length),List.prefix_refl _⟩,.prim (value n width bs length)) ∧
    Rel n width (.fixedBytes bs length : Source.Val E.layout (.fixedBytes n width)) (value n width bs length) ∧
    m.Related R (source.1.set i (.fixedBytes bs length)) (TEnv.set j (value n width bs length) target.env) := by
  have point := reflect _ _ (ContextMap.value_at m R source.1 target.env aligned r k readMap)
  rw [read] at point
  have targetRead := read_value n width bs length _ point
  have post : m.Related R (source.1.set i (source.1.get r))
      (TEnv.set j (TEnv.get k target.env) target.env) :=
    ContextMap.related_assign m R source.1 target.env aligned i r j k writeMap readMap
  rw [read,targetRead] at post
  exact ⟨source_assign_local_run G F fuel source i r (.fixedBytes bs length) read,
    assign_local_operand_run target j k _ targetRead,related n width bs length,post⟩
/-- info: 'Solidity.Lowering.V07.FixedBytesAssignment.range' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.FixedBytesAssignment.range

/-- info: 'Solidity.Lowering.V07.FixedBytesAssignment.related' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.FixedBytesAssignment.related

/-- info: 'Solidity.Lowering.V07.FixedBytesAssignment.read_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.FixedBytesAssignment.read_value

/-- info: 'Solidity.Lowering.V07.FixedBytesAssignment.decode_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.FixedBytesAssignment.decode_value

/-- info: 'Solidity.Lowering.V07.FixedBytesAssignment.contents_reflect' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.FixedBytesAssignment.contents_reflect

/-- info: 'Solidity.Lowering.V07.FixedBytesAssignment.transport' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.FixedBytesAssignment.transport

end Solidity.Lowering.V07.FixedBytesAssignment
