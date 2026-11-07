import Solidity.Lowering.V07.UnsignedNarrowing
import Solidity.Lowering.V07.ContextMapWrite

/-! Address certificates use the existing Source Fin160 and intrinsic uint
carriers (AST.PrimTy.ofName?). No representation, typing or profile is changed. -/
namespace Solidity.Lowering.V07.AddressConversions

def ty := UnsignedNarrowing.ty 160 (by decide)

theorem address_range (a : Roadmap.Address) : ty.lo ≤ (a.val : Int) ∧ (a.val : Int) ≤ ty.hi := by
  have bound := a.isLt
  change 0 ≤ (a.val : Int) ∧ (a.val : Int) ≤ ((2^160-1 : Nat) : Int)
  omega

def addressOfInteger (x : Int) (hx : ty.lo ≤ x ∧ x ≤ ty.hi) : Roadmap.Address :=
  ⟨x.toNat,by
    change 0 ≤ x ∧ x ≤ ((2^160-1 : Nat) : Int) at hx
    omega⟩

theorem addressOfInteger_observe (x : Int) (hx : ty.lo ≤ x ∧ x ≤ ty.hi) :
    ((addressOfInteger x hx).val : Int) = x := by
  change (x.toNat : Int) = x
  change 0 ≤ x ∧ x ≤ ((2^160-1 : Nat) : Int) at hx
  omega

def addressValue (a : Roadmap.Address) : PrimTy.uint.Denote := integerValue ty a.val (address_range a)
def AddressRel {D : Source.Layout} (p : Bool)
    (source : Source.Val D (.address p)) (target : PrimTy.uint.Denote) : Prop :=
  source.key = PrimTy.num? target

theorem address_related {D : Source.Layout} (p : Bool) (a : Roadmap.Address) :
    AddressRel p (.address a : Source.Val D (.address p)) (addressValue a) := rfl

theorem address_read {D : Source.Layout} (p : Bool) (a : Roadmap.Address) (v : PrimTy.uint.Denote)
    (related : AddressRel p (.address a : Source.Val D (.address p)) v) : v = addressValue a := by
  apply Subtype.ext
  change some (a.val : Int) = some v.val at related
  exact (Option.some.inj related).symm

theorem integer_read {D : Source.Layout} (x : Int) (hx : ty.lo ≤ x ∧ x ≤ ty.hi)
    (v : PrimTy.uint.Denote) (related : IntValueRel ty (.int x hx : Source.Val D (.int ty)) v) :
    v = integerValue ty x hx := by
  apply Subtype.ext
  change some x = some v.val at related
  exact (Option.some.inj related).symm

theorem from_uint_related {D : Source.Layout} (x : Int) (hx : ty.lo ≤ x ∧ x ≤ ty.hi) :
    AddressRel false (.address (addressOfInteger x hx) : Source.Val D (.address false))
      (integerValue ty x hx) := by
  change some ((addressOfInteger x hx).val : Int) = some x
  rw [addressOfInteger_observe]

theorem direct_int_rule (E : Source.Env) (t : Source.IntTy) (p : Bool) :
    (Source.STy.int t).explicit E.isBase E.mapFree (.address p) = (!p && !t.signed && t.bits == 160) := rfl

theorem allowed_from (E : Source.Env) : (Source.STy.int ty).explicit E.isBase E.mapFree (.address false) = true := rfl
theorem allowed_to (E : Source.Env) : (Source.STy.address false).explicit E.isBase E.mapFree (.int ty) = true := rfl

theorem source_from_uint {D : Source.Layout} (x : Int) (hx : ty.lo ≤ x ∧ x ≤ ty.hi) :
    Source.convExplicitVal (.address false) (.int x hx : Source.Val D (.int ty)) =
      .ok (.address (addressOfInteger x hx)) := by
  have wrapped := UnsignedNarrowing.wrap_of_range 160 (by decide) x hx
  change Source.wrapBits false 160 x = x at wrapped
  change (Except.ok (Source.Val.address ⟨(Source.wrapBits false 160 x).toNat % 2^160,by omega⟩) :
    Source.R (Source.Val D (.address false))) = _
  apply congrArg Except.ok
  apply congrArg Source.Val.address
  apply Fin.ext
  change (Source.wrapBits false 160 x).toNat % 2^160 = x.toNat
  rw [wrapped]
  exact Nat.mod_eq_of_lt (show x.toNat < 2^160 from (addressOfInteger x hx).isLt)

theorem source_to_uint {D : Source.Layout} (a : Roadmap.Address) :
    Source.convExplicitVal (.int ty) (.address a : Source.Val D (.address false)) =
      .ok (.int a.val (address_range a)) := by
  have wrapped : ty.wrap (a.val : Int) = (a.val : Int) :=
    UnsignedNarrowing.wrap_of_range 160 (by decide) (a.val : Int) (address_range a)
  change Except.ok (Source.intWrap ty (a.val : Int)) = _
  simp only [Source.intWrap,wrapped]

theorem addressValue_injective (a b : Roadmap.Address) (same : addressValue a = addressValue b) : a = b := by
  apply Fin.ext
  have values := congrArg Subtype.val same
  change (a.val : Int) = (b.val : Int) at values
  omega

theorem source_from_run {E : Source.Env} {Γ : Source.RCtx}
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat) (source mid : Source.EMState E Γ)
    (e : Source.RExpr E Γ (.int ty)) (x : Int) (hx : ty.lo ≤ x ∧ x ≤ ty.hi)
    (read : (Source.evalE G F fuel e).run source = (.ok (.val (.int x hx)),mid)) :
    (Source.evalE G F (fuel+1) (.convExplicit (τ := .address false) e (allowed_from E))).run source =
      (.ok (.val (.address (addressOfInteger x hx))),mid) := by
  rw [Source.evalE,Source.Hoare.run_bind,read]
  change (do
    let v ← Source.EM.lift (Source.convExplicitVal (.address false) (.int x hx : Source.Val E.layout (.int ty)))
    pure (Source.RVal.val v)).run mid = _
  rw [source_from_uint]
  rfl

theorem source_to_run {E : Source.Env} {Γ : Source.RCtx}
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat) (source mid : Source.EMState E Γ)
    (e : Source.RExpr E Γ (.address false)) (a : Roadmap.Address)
    (read : (Source.evalE G F fuel e).run source = (.ok (.val (.address a)),mid)) :
    (Source.evalE G F (fuel+1) (.convExplicit (τ := .int ty) e (allowed_to E))).run source =
      (.ok (.val (.int a.val (address_range a))),mid) := by
  rw [Source.evalE,Source.Hoare.run_bind,read]
  change (do
    let v ← Source.EM.lift (Source.convExplicitVal (.int ty) (.address a : Source.Val E.layout (.address false)))
    pure (Source.RVal.val v)).run mid = _
  rw [source_to_uint]
  rfl

theorem source_from_local {E : Source.Env} {Γ : Source.RCtx}
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat) (source : Source.EMState E Γ)
    (i : Source.Idx Γ (.int ty)) (x : Int) (hx : ty.lo ≤ x ∧ x ≤ ty.hi)
    (read : source.1.get i = .int x hx) :
    (Source.evalE G F (fuel+2) (.convExplicit (τ := .address false) (.local i) (allowed_from E))).run source =
      (.ok (.val (.address (addressOfInteger x hx))),source) := by
  apply source_from_run G F (fuel+1) source source (.local i) x hx
  change (Except.ok (Source.RVal.val (source.1.get i)),source) = _
  rw [read]

theorem source_to_local {E : Source.Env} {Γ : Source.RCtx}
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat) (source : Source.EMState E Γ)
    (i : Source.Idx Γ (.address false)) (a : Roadmap.Address)
    (read : source.1.get i = .address a) :
    (Source.evalE G F (fuel+2) (.convExplicit (τ := .int ty) (.local i) (allowed_to E))).run source =
      (.ok (.val (.int a.val (address_range a))),source) := by
  apply source_to_run G F (fuel+1) source source (.local i) a
  change (Except.ok (Source.RVal.val (source.1.get i)),source) = _
  rw [read]

theorem from_local_transport {E : Source.Env} {srcΓ : Source.RCtx} {C : Contract} {Γ : Ctx}
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat) (source : Source.EMState E srcΓ) (target : State C Γ)
    (i : Source.Idx srcΓ (.int ty)) (j : Idx Γ (.val .uint))
    (x : Int) (hx : ty.lo ≤ x ∧ x ≤ ty.hi) (read : source.1.get i = .int x hx)
    (related : IntValueRel ty (source.1.get i) (TEnv.get j target.env)) :
    (Source.evalE G F (fuel+2) (.convExplicit (τ := .address false) (.local i) (allowed_from E))).run source =
      (.ok (.val (.address (addressOfInteger x hx))),source) ∧
    (DeferredSource.Operand.ofSrc (.val (.simple (.local j)))).run target =
      .ok (⟨target,List.prefix_refl _⟩,.prim (integerValue ty x hx)) ∧
    AddressRel false (.address (addressOfInteger x hx) : Source.Val E.layout (.address false))
      (integerValue ty x hx) := by
  rw [read] at related
  exact ⟨source_from_local G F fuel source i x hx read,
    local_operand_run target j _ (integer_read x hx _ related),from_uint_related x hx⟩

theorem to_local_transport {E : Source.Env} {srcΓ : Source.RCtx} {C : Contract} {Γ : Ctx}
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat) (source : Source.EMState E srcΓ) (target : State C Γ)
    (i : Source.Idx srcΓ (.address false)) (j : Idx Γ (.val .uint)) (a : Roadmap.Address)
    (read : source.1.get i = .address a)
    (related : AddressRel false (source.1.get i) (TEnv.get j target.env)) :
    (Source.evalE G F (fuel+2) (.convExplicit (τ := .int ty) (.local i) (allowed_to E))).run source =
      (.ok (.val (.int a.val (address_range a))),source) ∧
    (DeferredSource.Operand.ofSrc (.val (.simple (.local j)))).run target =
      .ok (⟨target,List.prefix_refl _⟩,.prim (addressValue a)) ∧
    IntValueRel ty (.int a.val (address_range a) : Source.Val E.layout (.int ty)) (addressValue a) := by
  rw [read] at related
  exact ⟨source_to_local G F fuel source i a read,
    local_operand_run target j _ (address_read false a _ related),integer_related ty _ _⟩

theorem source_from_assignment {E : Source.Env} {Γ : Source.RCtx}
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat) (source : Source.EMState E Γ)
    (i a : Source.Idx Γ (.int ty)) (x : Int) (hx : ty.lo ≤ x ∧ x ≤ ty.hi)
    (read : source.1.get a = .int x hx) :
    (Source.evalE G F (fuel+3) (.convExplicit (τ := .address false)
      (.assign (.local i) (.local a)) (allowed_from E))).run source =
      (.ok (.val (.address (addressOfInteger x hx))),(source.1.set i (.int x hx),source.2)) := by
  exact source_from_run G F (fuel+2) source _ (.assign (.local i) (.local a)) x hx
    (source_assign_local_run G F fuel source i a (.int x hx) read)

theorem from_assignment_transport {E : Source.Env} {srcΓ : Source.RCtx} {C : Contract} {Γ : Ctx} {ι : Type}
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat) (source : Source.EMState E srcΓ) (target : State C Γ)
    (si : ι → Source.Idx srcΓ (.int ty)) (ti : ι → Idx Γ (.val .uint))
    (family : IntegerLocalFamily ty si ti source.1 target.env) (i a : ι)
    (x : Int) (hx : ty.lo ≤ x ∧ x ≤ ty.hi) (read : source.1.get (si a) = .int x hx) :
    (Source.evalE G F (fuel+3) (.convExplicit (τ := .address false)
      (.assign (.local (si i)) (.local (si a))) (allowed_from E))).run source =
      (.ok (.val (.address (addressOfInteger x hx))),(source.1.set (si i) (.int x hx),source.2)) ∧
    (assignLocalOperand (ti i) (ti a)).run target =
      .ok (⟨target.setLocal (ti i) (integerValue ty x hx),List.prefix_refl _⟩,.prim (integerValue ty x hx)) ∧
    AddressRel false (.address (addressOfInteger x hx) : Source.Val E.layout (.address false)) (integerValue ty x hx) ∧
    IntegerLocalFamily ty si ti (source.1.set (si i) (.int x hx))
      (TEnv.set (ti i) (integerValue ty x hx) target.env) := by
  refine ⟨source_from_assignment G F fuel source (si i) (si a) x hx read,
    assign_local_operand_run target (ti i) (ti a) _ (family.read a x hx read),from_uint_related x hx,?_⟩
  have post := family.write i a
  rw [read,family.read a x hx read] at post
  exact post

theorem source_to_assignment {E : Source.Env} {Γ : Source.RCtx}
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat) (source : Source.EMState E Γ)
    (i r : Source.Idx Γ (.address false)) (a : Roadmap.Address)
    (read : source.1.get r = .address a) :
    (Source.evalE G F (fuel+3) (.convExplicit (τ := .int ty)
      (.assign (.local i) (.local r)) (allowed_to E))).run source =
      (.ok (.val (.int a.val (address_range a))),(source.1.set i (.address a),source.2)) := by
  exact source_to_run G F (fuel+2) source _ (.assign (.local i) (.local r)) a
    (source_assign_local_run G F fuel source i r (.address a) read)

theorem to_assignment_transport {E : Source.Env} {srcΓ : Source.RCtx} {C : Contract} {Γ : Ctx}
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat) (source : Source.EMState E srcΓ) (target : State C Γ)
    (m : ContextMap srcΓ Γ)
    (R : (τ : Source.STy) → (u : LTy) → Source.Val E.layout τ → u.TDenote C target.H → Prop)
    (aligned : m.Related R source.1 target.env)
    (addressReflect : ∀ (v : Source.Val E.layout (.address false)) (n : PrimTy.uint.Denote),
      R (.address false) (.val .uint) v n → AddressRel false v n)
    (i r : Source.Idx srcΓ (.address false)) (j b : Idx Γ (.val .uint))
    (writeMap : m.slot i = ⟨.val .uint,j⟩) (readMap : m.slot r = ⟨.val .uint,b⟩)
    (a : Roadmap.Address) (read : source.1.get r = .address a) :
    (Source.evalE G F (fuel+3) (.convExplicit (τ := .int ty)
      (.assign (.local i) (.local r)) (allowed_to E))).run source =
      (.ok (.val (.int a.val (address_range a))),(source.1.set i (.address a),source.2)) ∧
    (assignLocalOperand j b).run target =
      .ok (⟨target.setLocal j (addressValue a),List.prefix_refl _⟩,.prim (addressValue a)) ∧
    IntValueRel ty (.int a.val (address_range a) : Source.Val E.layout (.int ty)) (addressValue a) ∧
    m.Related R (source.1.set i (.address a)) (TEnv.set j (addressValue a) target.env) := by
  have point := addressReflect _ _ (ContextMap.value_at m R source.1 target.env aligned r b readMap)
  rw [read] at point
  have targetRead := address_read false a _ point
  have post : m.Related R (source.1.set i (source.1.get r)) (TEnv.set j (TEnv.get b target.env) target.env) :=
    ContextMap.related_assign m R source.1 target.env aligned i r j b writeMap readMap
  rw [read,targetRead] at post
  exact ⟨source_to_assignment G F fuel source i r a read,
    assign_local_operand_run target j b _ targetRead,integer_related ty _ _,post⟩
end Solidity.Lowering.V07.AddressConversions

/-- info: 'Solidity.Lowering.V07.AddressConversions.address_range' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.AddressConversions.address_range

/-- info: 'Solidity.Lowering.V07.AddressConversions.addressOfInteger_observe' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.AddressConversions.addressOfInteger_observe

/-- info: 'Solidity.Lowering.V07.AddressConversions.address_related' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.AddressConversions.address_related

/-- info: 'Solidity.Lowering.V07.AddressConversions.address_read' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.AddressConversions.address_read

/-- info: 'Solidity.Lowering.V07.AddressConversions.integer_read' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.AddressConversions.integer_read

/-- info: 'Solidity.Lowering.V07.AddressConversions.from_uint_related' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.AddressConversions.from_uint_related

/-- info: 'Solidity.Lowering.V07.AddressConversions.direct_int_rule' does not depend on any axioms -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.AddressConversions.direct_int_rule

/-- info: 'Solidity.Lowering.V07.AddressConversions.allowed_from' does not depend on any axioms -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.AddressConversions.allowed_from

/-- info: 'Solidity.Lowering.V07.AddressConversions.allowed_to' does not depend on any axioms -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.AddressConversions.allowed_to

/-- info: 'Solidity.Lowering.V07.AddressConversions.source_from_uint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.AddressConversions.source_from_uint

/-- info: 'Solidity.Lowering.V07.AddressConversions.source_to_uint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.AddressConversions.source_to_uint

/-- info: 'Solidity.Lowering.V07.AddressConversions.addressValue_injective' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.AddressConversions.addressValue_injective

/-- info: 'Solidity.Lowering.V07.AddressConversions.source_from_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.AddressConversions.source_from_run

/-- info: 'Solidity.Lowering.V07.AddressConversions.source_to_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.AddressConversions.source_to_run

/-- info: 'Solidity.Lowering.V07.AddressConversions.source_from_local' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.AddressConversions.source_from_local

/-- info: 'Solidity.Lowering.V07.AddressConversions.source_to_local' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.AddressConversions.source_to_local

/-- info: 'Solidity.Lowering.V07.AddressConversions.from_local_transport' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.AddressConversions.from_local_transport

/-- info: 'Solidity.Lowering.V07.AddressConversions.to_local_transport' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.AddressConversions.to_local_transport

/-- info: 'Solidity.Lowering.V07.AddressConversions.source_from_assignment' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.AddressConversions.source_from_assignment

/-- info: 'Solidity.Lowering.V07.AddressConversions.from_assignment_transport' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.AddressConversions.from_assignment_transport

/-- info: 'Solidity.Lowering.V07.AddressConversions.source_to_assignment' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.AddressConversions.source_to_assignment

/-- info: 'Solidity.Lowering.V07.AddressConversions.to_assignment_transport' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.AddressConversions.to_assignment_transport
