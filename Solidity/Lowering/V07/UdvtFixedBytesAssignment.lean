import Solidity.Lowering.V07.UdvtAssignment
import Solidity.Lowering.V07.FixedBytesAssignment

/-! Same-tag UDVT assignment with fixed-byte underlying values.
Value construction below is not execution of Source wrap/unwrap syntax. -/
namespace Solidity.Lowering.V07.UdvtFixedBytesAssignment

def value {D : Source.Layout} (d : Source.DeclName) (n : Nat) (width : 1 ≤ n ∧ n ≤ 32)
    (underlying : D.underlying d = .fixedBytes n width) (bs : List UInt8) (length : bs.length = n) :
    Source.Val D (.udvt d) :=
  .udvt (underlying.symm ▸ (.fixedBytes bs length : Source.Val D (.fixedBytes n width)))
def Rel {D : Source.Layout} (d : Source.DeclName)
    (source : Source.Val D (.udvt d)) (target : PrimTy.uint.Denote) : Prop :=
  source.key = PrimTy.num? target

theorem value_key {D : Source.Layout} (d : Source.DeclName) (n : Nat) (width : 1 ≤ n ∧ n ≤ 32)
    (underlying : D.underlying d = .fixedBytes n width) (bs : List UInt8) (length : bs.length = n) :
    (value d n width underlying bs length).key = some (Source.bytesNat bs : Int) := by
  change (underlying.symm ▸ (.fixedBytes bs length : Source.Val D (.fixedBytes n width))).key = _
  rw [UdvtAssignment.key_cast]
  rfl

theorem value_related {D : Source.Layout} (d : Source.DeclName) (n : Nat) (width : 1 ≤ n ∧ n ≤ 32)
    (underlying : D.underlying d = .fixedBytes n width) (bs : List UInt8) (length : bs.length = n) :
    Rel d (value d n width underlying bs length) (FixedBytesAssignment.value n width bs length) := by
  exact value_key d n width underlying bs length

theorem read_value {D : Source.Layout} (d : Source.DeclName) (n : Nat) (width : 1 ≤ n ∧ n ≤ 32)
    (underlying : D.underlying d = .fixedBytes n width) (bs : List UInt8) (length : bs.length = n)
    (v : PrimTy.uint.Denote) (agrees : Rel d (value d n width underlying bs length) v) :
    v = FixedBytesAssignment.value n width bs length := by
  apply Subtype.ext
  change (value d n width underlying bs length).key = some v.val at agrees
  rw [value_key] at agrees
  exact (Option.some.inj agrees).symm

theorem contents_observe {D : Source.Layout} (d : Source.DeclName) (n : Nat) (width : 1 ≤ n ∧ n ≤ 32)
    (underlying : D.underlying d = .fixedBytes n width) (bs : List UInt8) (length : bs.length = n)
    (v : PrimTy.uint.Denote) (agrees : Rel d (value d n width underlying bs length) v) :
    Source.beBytes n v.val.toNat = bs := by
  rw [read_value d n width underlying bs length v agrees]
  exact FixedBytesAssignment.decode_value n width bs length

theorem transport {E : Source.Env} {srcΓ : Source.RCtx} {C : Contract} {Γ : Ctx}
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat) (source : Source.EMState E srcΓ) (target : State C Γ)
    (d : Source.DeclName) (n : Nat) (width : 1 ≤ n ∧ n ≤ 32)
    (underlying : E.layout.underlying d = .fixedBytes n width) (m : ContextMap srcΓ Γ)
    (R : (τ : Source.STy) → (u : LTy) → Source.Val E.layout τ → u.TDenote C target.H → Prop)
    (aligned : m.Related R source.1 target.env)
    (reflect : ∀ (v : Source.Val E.layout (.udvt d)) (x : PrimTy.uint.Denote),
      R (.udvt d) (.val .uint) v x → Rel d v x)
    (i r : Source.Idx srcΓ (.udvt d)) (j k : Idx Γ (.val .uint))
    (writeMap : m.slot i = ⟨.val .uint,j⟩) (readMap : m.slot r = ⟨.val .uint,k⟩)
    (bs : List UInt8) (length : bs.length = n) (read : source.1.get r = value d n width underlying bs length) :
    (Source.evalE G F (fuel+3) (.conv (.assign (.local i) (.local r)) (Or.inr rfl))).run source =
      (.ok (.val (value d n width underlying bs length)),
        (source.1.set i (value d n width underlying bs length),source.2)) ∧
    (assignLocalOperand j k).run target =
      .ok (⟨target.setLocal j (FixedBytesAssignment.value n width bs length),List.prefix_refl _⟩,
        .prim (FixedBytesAssignment.value n width bs length)) ∧
    Source.beBytes n (FixedBytesAssignment.value n width bs length).val.toNat = bs ∧
    m.Related R (source.1.set i (value d n width underlying bs length))
      (TEnv.set j (FixedBytesAssignment.value n width bs length) target.env) := by
  have point := reflect _ _ (ContextMap.value_at m R source.1 target.env aligned r k readMap)
  rw [read] at point
  have targetRead := read_value d n width underlying bs length _ point
  have post : m.Related R (source.1.set i (source.1.get r))
      (TEnv.set j (TEnv.get k target.env) target.env) :=
    ContextMap.related_assign m R source.1 target.env aligned i r j k writeMap readMap
  rw [read,targetRead] at post
  exact ⟨UdvtAssignment.source_assignment G F fuel source d i r _ read,
    assign_local_operand_run target j k _ targetRead,FixedBytesAssignment.decode_value n width bs length,post⟩
/-- info: 'Solidity.Lowering.V07.UdvtFixedBytesAssignment.value_key' does not depend on any axioms -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UdvtFixedBytesAssignment.value_key

/-- info: 'Solidity.Lowering.V07.UdvtFixedBytesAssignment.value_related' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UdvtFixedBytesAssignment.value_related

/-- info: 'Solidity.Lowering.V07.UdvtFixedBytesAssignment.read_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UdvtFixedBytesAssignment.read_value

/-- info: 'Solidity.Lowering.V07.UdvtFixedBytesAssignment.contents_observe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UdvtFixedBytesAssignment.contents_observe

/-- info: 'Solidity.Lowering.V07.UdvtFixedBytesAssignment.transport' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UdvtFixedBytesAssignment.transport

end Solidity.Lowering.V07.UdvtFixedBytesAssignment
