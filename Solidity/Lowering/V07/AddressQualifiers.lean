import Solidity.Lowering.V07.AddressConversions

/-! Existing Source payable/erasure clauses over the existing address/uint
carriers. These certificates do not select a frontend clause or admit syntax.
Canonical initial value agreement is required; there is no native truncation. -/
namespace Solidity.Lowering.V07.AddressQualifiers
open AddressConversions

theorem allowed_erase (E : Source.Env) (p : Bool) :
    (Source.STy.address p).explicit E.isBase E.mapFree (.address false) = true := by
  cases p <;> rfl

theorem erase_value {D : Source.Layout} (p : Bool) (a : Roadmap.Address) :
    Source.convExplicitVal (.address false) (.address a : Source.Val D (.address p)) = .ok (.address a) := rfl

theorem payable_run {E : Source.Env} {Γ : Source.RCtx}
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat) (source mid : Source.EMState E Γ)
    (p : Bool) (e : Source.RExpr E Γ (.address p)) (a : Roadmap.Address)
    (read : (Source.evalE G F fuel e).run source = (.ok (.val (.address a)),mid)) :
    (Source.evalE G F (fuel+1) (.payable e)).run source = (.ok (.val (.address a)),mid) := by
  rw [Source.evalE,Source.Hoare.run_bind,read]
  rfl

theorem erase_run {E : Source.Env} {Γ : Source.RCtx}
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat) (source mid : Source.EMState E Γ)
    (p : Bool) (e : Source.RExpr E Γ (.address p)) (a : Roadmap.Address)
    (read : (Source.evalE G F fuel e).run source = (.ok (.val (.address a)),mid)) :
    (Source.evalE G F (fuel+1) (.convExplicit (τ := .address false) e (allowed_erase E p))).run source =
      (.ok (.val (.address a)),mid) := by
  rw [Source.evalE,Source.Hoare.run_bind,read]
  rfl

theorem payable_assignment {E : Source.Env} {Γ : Source.RCtx}
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat) (source : Source.EMState E Γ)
    (p : Bool) (i r : Source.Idx Γ (.address p)) (a : Roadmap.Address)
    (read : source.1.get r = .address a) :
    (Source.evalE G F (fuel+3) (.payable (.assign (.local i) (.local r)))).run source =
      (.ok (.val (.address a)),(source.1.set i (.address a),source.2)) :=
  payable_run G F (fuel+2) source _ p _ a (source_assign_local_run G F fuel source i r (.address a) read)

theorem erase_assignment {E : Source.Env} {Γ : Source.RCtx}
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat) (source : Source.EMState E Γ)
    (p : Bool) (i r : Source.Idx Γ (.address p)) (a : Roadmap.Address)
    (read : source.1.get r = .address a) :
    (Source.evalE G F (fuel+3) (.convExplicit (τ := .address false)
      (.assign (.local i) (.local r)) (allowed_erase E p))).run source =
      (.ok (.val (.address a)),(source.1.set i (.address a),source.2)) :=
  erase_run G F (fuel+2) source _ p _ a (source_assign_local_run G F fuel source i r (.address a) read)

/-- Both qualifier clauses share the same actual copy operand and reached caller
relation, derived from initial values and mapped binding identities. -/
theorem copy_alignment {E : Source.Env} {srcΓ : Source.RCtx} {C : Contract} {Γ : Ctx}
    (source : Source.EMState E srcΓ) (target : State C Γ) (p : Bool)
    (m : ContextMap srcΓ Γ)
    (R : (τ : Source.STy) → (u : LTy) → Source.Val E.layout τ → u.TDenote C target.H → Prop)
    (aligned : m.Related R source.1 target.env)
    (reflect : ∀ (v : Source.Val E.layout (.address p)) (n : PrimTy.uint.Denote),
      R (.address p) (.val .uint) v n → AddressRel p v n)
    (i r : Source.Idx srcΓ (.address p)) (j k : Idx Γ (.val .uint))
    (writeMap : m.slot i = ⟨.val .uint,j⟩) (readMap : m.slot r = ⟨.val .uint,k⟩)
    (a : Roadmap.Address) (read : source.1.get r = .address a) :
    (assignLocalOperand j k).run target =
      .ok (⟨target.setLocal j (addressValue a),List.prefix_refl _⟩,.prim (addressValue a)) ∧
    m.Related R (source.1.set i (.address a)) (TEnv.set j (addressValue a) target.env) := by
  have point := reflect _ _ (ContextMap.value_at m R source.1 target.env aligned r k readMap)
  rw [read] at point
  have targetRead := address_read p a _ point
  have post : m.Related R (source.1.set i (source.1.get r)) (TEnv.set j (TEnv.get k target.env) target.env) :=
    ContextMap.related_assign m R source.1 target.env aligned i r j k writeMap readMap
  rw [read,targetRead] at post
  exact ⟨assign_local_operand_run target j k _ targetRead,post⟩

theorem payable_transport {E : Source.Env} {srcΓ : Source.RCtx} {C : Contract} {Γ : Ctx}
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat)
    (source : Source.EMState E srcΓ) (target : State C Γ) (p : Bool)
    (m : ContextMap srcΓ Γ)
    (R : (τ : Source.STy) → (u : LTy) → Source.Val E.layout τ → u.TDenote C target.H → Prop)
    (aligned : m.Related R source.1 target.env)
    (reflect : ∀ (v : Source.Val E.layout (.address p)) (n : PrimTy.uint.Denote),
      R (.address p) (.val .uint) v n → AddressRel p v n)
    (i r : Source.Idx srcΓ (.address p)) (j k : Idx Γ (.val .uint))
    (writeMap : m.slot i = ⟨.val .uint,j⟩) (readMap : m.slot r = ⟨.val .uint,k⟩)
    (a : Roadmap.Address) (read : source.1.get r = .address a) :
    (Source.evalE G F (fuel+3) (.payable (.assign (.local i) (.local r)))).run source =
      (.ok (.val (.address a)),(source.1.set i (.address a),source.2)) ∧
    (assignLocalOperand j k).run target =
      .ok (⟨target.setLocal j (addressValue a),List.prefix_refl _⟩,.prim (addressValue a)) ∧
    AddressRel true (.address a : Source.Val E.layout (.address true)) (addressValue a) ∧
    m.Related R (source.1.set i (.address a)) (TEnv.set j (addressValue a) target.env) := by
  have reached := copy_alignment source target p m R aligned reflect i r j k writeMap readMap a read
  exact ⟨payable_assignment G F fuel source p i r a read,reached.1,address_related true a,reached.2⟩

theorem erase_transport {E : Source.Env} {srcΓ : Source.RCtx} {C : Contract} {Γ : Ctx}
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat)
    (source : Source.EMState E srcΓ) (target : State C Γ) (p : Bool)
    (m : ContextMap srcΓ Γ)
    (R : (τ : Source.STy) → (u : LTy) → Source.Val E.layout τ → u.TDenote C target.H → Prop)
    (aligned : m.Related R source.1 target.env)
    (reflect : ∀ (v : Source.Val E.layout (.address p)) (n : PrimTy.uint.Denote),
      R (.address p) (.val .uint) v n → AddressRel p v n)
    (i r : Source.Idx srcΓ (.address p)) (j k : Idx Γ (.val .uint))
    (writeMap : m.slot i = ⟨.val .uint,j⟩) (readMap : m.slot r = ⟨.val .uint,k⟩)
    (a : Roadmap.Address) (read : source.1.get r = .address a) :
    (Source.evalE G F (fuel+3) (.convExplicit (τ := .address false) (.assign (.local i) (.local r)) (allowed_erase E p))).run source =
      (.ok (.val (.address a)),(source.1.set i (.address a),source.2)) ∧
    (assignLocalOperand j k).run target =
      .ok (⟨target.setLocal j (addressValue a),List.prefix_refl _⟩,.prim (addressValue a)) ∧
    AddressRel false (.address a : Source.Val E.layout (.address false)) (addressValue a) ∧
    m.Related R (source.1.set i (.address a)) (TEnv.set j (addressValue a) target.env) := by
  have reached := copy_alignment source target p m R aligned reflect i r j k writeMap readMap a read
  exact ⟨erase_assignment G F fuel source p i r a read,reached.1,address_related false a,reached.2⟩
end Solidity.Lowering.V07.AddressQualifiers

/-- info: 'Solidity.Lowering.V07.AddressQualifiers.allowed_erase' does not depend on any axioms -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.AddressQualifiers.allowed_erase

/-- info: 'Solidity.Lowering.V07.AddressQualifiers.erase_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.AddressQualifiers.erase_value

/-- info: 'Solidity.Lowering.V07.AddressQualifiers.payable_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.AddressQualifiers.payable_run

/-- info: 'Solidity.Lowering.V07.AddressQualifiers.erase_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.AddressQualifiers.erase_run

/-- info: 'Solidity.Lowering.V07.AddressQualifiers.payable_assignment' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.AddressQualifiers.payable_assignment

/-- info: 'Solidity.Lowering.V07.AddressQualifiers.erase_assignment' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.AddressQualifiers.erase_assignment

/-- info: 'Solidity.Lowering.V07.AddressQualifiers.copy_alignment' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.AddressQualifiers.copy_alignment

/-- info: 'Solidity.Lowering.V07.AddressQualifiers.payable_transport' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.AddressQualifiers.payable_transport

/-- info: 'Solidity.Lowering.V07.AddressQualifiers.erase_transport' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.AddressQualifiers.erase_transport
