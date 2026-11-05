import Solidity.Lowering.V07.UdvtAssignment
import Solidity.Lowering.V07.AddressConversions

/-! Address-underlying UDVT local assignment over existing typed carriers.
Nominal compatibility stays in Source indices; numeric observation is not a runtime tag. -/
namespace Solidity.Lowering.V07.UdvtAddressAssignment
open AddressConversions (addressValue)

def value {D : Source.Layout} (d : Source.DeclName) (payable : Bool)
    (underlying : D.underlying d = .address payable) (a : Roadmap.Address) : Source.Val D (.udvt d) :=
  .udvt (underlying.symm ▸ (.address a : Source.Val D (.address payable)))
def Rel {D : Source.Layout} (d : Source.DeclName)
    (source : Source.Val D (.udvt d)) (target : PrimTy.uint.Denote) : Prop :=
  source.key = PrimTy.num? target

theorem value_key {D : Source.Layout} (d : Source.DeclName) (p : Bool)
    (underlying : D.underlying d = .address p) (a : Roadmap.Address) :
    (value d p underlying a).key = some (a.val : Int) := by
  change (underlying.symm ▸ (.address a : Source.Val D (.address p))).key = _
  rw [UdvtAssignment.key_cast]
  rfl

theorem value_related {D : Source.Layout} (d : Source.DeclName) (p : Bool)
    (underlying : D.underlying d = .address p) (a : Roadmap.Address) :
    Rel d (value d p underlying a) (addressValue a) := by
  exact value_key d p underlying a

theorem read_value {D : Source.Layout} (d : Source.DeclName) (p : Bool)
    (underlying : D.underlying d = .address p) (a : Roadmap.Address) (n : PrimTy.uint.Denote)
    (related : Rel d (value d p underlying a) n) : n = addressValue a := by
  apply Subtype.ext
  change (value d p underlying a).key = some n.val at related
  rw [value_key] at related
  exact (Option.some.inj related).symm

theorem transport {E : Source.Env} {srcΓ : Source.RCtx} {C : Contract} {Γ : Ctx}
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat) (source : Source.EMState E srcΓ) (target : State C Γ)
    (d : Source.DeclName) (p : Bool) (underlying : E.layout.underlying d = .address p)
    (m : ContextMap srcΓ Γ)
    (R : (τ : Source.STy) → (u : LTy) → Source.Val E.layout τ → u.TDenote C target.H → Prop)
    (aligned : m.Related R source.1 target.env)
    (reflect : ∀ (v : Source.Val E.layout (.udvt d)) (n : PrimTy.uint.Denote),
      R (.udvt d) (.val .uint) v n → Rel d v n)
    (i r : Source.Idx srcΓ (.udvt d)) (j k : Idx Γ (.val .uint))
    (writeMap : m.slot i = ⟨.val .uint,j⟩) (readMap : m.slot r = ⟨.val .uint,k⟩)
    (a : Roadmap.Address) (read : source.1.get r = value d p underlying a) :
    (Source.evalE G F (fuel+3) (.conv (.assign (.local i) (.local r)) (Or.inr rfl))).run source =
      (.ok (.val (value d p underlying a)),(source.1.set i (value d p underlying a),source.2)) ∧
    (assignLocalOperand j k).run target =
      .ok (⟨target.setLocal j (addressValue a),List.prefix_refl _⟩,.prim (addressValue a)) ∧
    Rel d (value d p underlying a) (addressValue a) ∧
    m.Related R (source.1.set i (value d p underlying a)) (TEnv.set j (addressValue a) target.env) := by
  have point := reflect _ _ (ContextMap.value_at m R source.1 target.env aligned r k readMap)
  rw [read] at point
  have targetRead := read_value d p underlying a _ point
  have post : m.Related R (source.1.set i (source.1.get r))
      (TEnv.set j (TEnv.get k target.env) target.env) :=
    ContextMap.related_assign m R source.1 target.env aligned i r j k writeMap readMap
  rw [read,targetRead] at post
  exact ⟨UdvtAssignment.source_assignment G F fuel source d i r _ read,
    assign_local_operand_run target j k _ targetRead,value_related d p underlying a,post⟩
/-- info: 'Solidity.Lowering.V07.UdvtAddressAssignment.value_key' does not depend on any axioms -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UdvtAddressAssignment.value_key

/-- info: 'Solidity.Lowering.V07.UdvtAddressAssignment.value_related' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UdvtAddressAssignment.value_related

/-- info: 'Solidity.Lowering.V07.UdvtAddressAssignment.read_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UdvtAddressAssignment.read_value

/-- info: 'Solidity.Lowering.V07.UdvtAddressAssignment.transport' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UdvtAddressAssignment.transport

end Solidity.Lowering.V07.UdvtAddressAssignment
