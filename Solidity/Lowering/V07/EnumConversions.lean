import Solidity.Lowering.V07.AddressConversions

/-! Enum/uint256 clauses over the existing Fin enum and intrinsic uint carriers.
The capacity obligation is the existing GraphTypeRel.enum representation bound,
not a Source exclusion or a concrete declaration-admission certificate. -/
namespace Solidity.Lowering.V07.EnumConversions

theorem enum_range {D : Source.Layout} (d : Source.DeclName) (capacity : D.enumSize d ≤ 2^256)
    (i : Fin (D.enumSize d)) : Source.IntTy.u256.lo ≤ (i.val : Int) ∧ (i.val : Int) ≤ Source.IntTy.u256.hi := by
  have bound := i.isLt
  change 0 ≤ (i.val : Int) ∧ (i.val : Int) ≤ ((2^256-1 : Nat) : Int)
  omega

def enumValue {D : Source.Layout} (d : Source.DeclName) (capacity : D.enumSize d ≤ 2^256)
    (i : Fin (D.enumSize d)) : PrimTy.uint.Denote := integerValue .u256 i.val (enum_range d capacity i)

def EnumRel {D : Source.Layout} (d : Source.DeclName)
    (source : Source.Val D (.enum d)) (target : PrimTy.uint.Denote) : Prop :=
  source.key = PrimTy.num? target

theorem enum_related {D : Source.Layout} (d : Source.DeclName) (capacity : D.enumSize d ≤ 2^256)
    (i : Fin (D.enumSize d)) : EnumRel d (.enum i : Source.Val D (.enum d)) (enumValue d capacity i) := rfl

theorem enum_read {D : Source.Layout} (d : Source.DeclName) (capacity : D.enumSize d ≤ 2^256)
    (i : Fin (D.enumSize d)) (v : PrimTy.uint.Denote)
    (related : EnumRel d (.enum i : Source.Val D (.enum d)) v) : v = enumValue d capacity i := by
  apply Subtype.ext
  change some (i.val : Int) = some v.val at related
  exact (Option.some.inj related).symm

theorem allowed_from (E : Source.Env) (d : Source.DeclName) :
    (Source.STy.int .u256).explicit E.isBase E.mapFree (.enum d) = true := rfl

theorem allowed_to (E : Source.Env) (d : Source.DeclName) :
    (Source.STy.enum d).explicit E.isBase E.mapFree (.int .u256) = true := rfl

theorem source_from_uint {D : Source.Layout} (d : Source.DeclName) (x : Int)
    (hx : Source.IntTy.u256.lo ≤ x ∧ x ≤ Source.IntTy.u256.hi)
    (valid : 0 ≤ x ∧ x.toNat < D.enumSize d) :
    Source.convExplicitVal (.enum d) (.int x hx : Source.Val D (.int .u256)) =
      .ok (.enum ⟨x.toNat,valid.2⟩) := by
  change Source.enumOfInt (D := D) d x = _
  unfold Source.enumOfInt
  split
  · rfl
  · rename_i refused
    exact False.elim (refused valid)

theorem source_to_uint {D : Source.Layout} (d : Source.DeclName) (capacity : D.enumSize d ≤ 2^256)
    (i : Fin (D.enumSize d)) :
    Source.convExplicitVal (.int .u256) (.enum i : Source.Val D (.enum d)) =
      .ok (.int i.val (enum_range d capacity i)) := by
  have wrapped : Source.IntTy.u256.wrap (i.val : Int) = (i.val : Int) :=
    UnsignedNarrowing.wrap_of_range 256 (by decide) i.val (enum_range d capacity i)
  change Except.ok (Source.intWrap .u256 (i.val : Int)) = _
  simp only [Source.intWrap,wrapped]

theorem from_related {D : Source.Layout} (d : Source.DeclName) (x : Int)
    (hx : Source.IntTy.u256.lo ≤ x ∧ x ≤ Source.IntTy.u256.hi)
    (valid : 0 ≤ x ∧ x.toNat < D.enumSize d) :
    EnumRel d (.enum ⟨x.toNat,valid.2⟩ : Source.Val D (.enum d)) (integerValue .u256 x hx) := by
  change some (x.toNat : Int) = some x
  congr 1
  omega

theorem source_to_run {E : Source.Env} {Γ : Source.RCtx}
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat) (source mid : Source.EMState E Γ)
    (d : Source.DeclName) (capacity : E.layout.enumSize d ≤ 2^256)
    (e : Source.RExpr E Γ (.enum d)) (i : Fin (E.layout.enumSize d))
    (read : (Source.evalE G F fuel e).run source = (.ok (.val (.enum i)),mid)) :
    (Source.evalE G F (fuel+1) (.convExplicit (τ := .int .u256) e (allowed_to E d))).run source =
      (.ok (.val (.int i.val (enum_range d capacity i))),mid) := by
  rw [Source.evalE,Source.Hoare.run_bind,read]
  change (do
    let v ← Source.EM.lift (Source.convExplicitVal (.int .u256) (.enum i : Source.Val E.layout (.enum d)))
    pure (Source.RVal.val v)).run mid = _
  rw [source_to_uint d capacity i]
  rfl

theorem source_from_run {E : Source.Env} {Γ : Source.RCtx}
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat) (source mid : Source.EMState E Γ)
    (d : Source.DeclName) (e : Source.RExpr E Γ (.int .u256)) (x : Int)
    (hx : Source.IntTy.u256.lo ≤ x ∧ x ≤ Source.IntTy.u256.hi)
    (valid : 0 ≤ x ∧ x.toNat < E.layout.enumSize d)
    (read : (Source.evalE G F fuel e).run source = (.ok (.val (.int x hx)),mid)) :
    (Source.evalE G F (fuel+1) (.convExplicit (τ := .enum d) e (allowed_from E d))).run source =
      (.ok (.val (.enum ⟨x.toNat,valid.2⟩)),mid) := by
  rw [Source.evalE,Source.Hoare.run_bind,read]
  change (do
    let v ← Source.EM.lift (Source.convExplicitVal (.enum d) (.int x hx : Source.Val E.layout (.int .u256)))
    pure (Source.RVal.val v)).run mid = _
  rw [source_from_uint d x hx valid]
  rfl

theorem from_assignment_transport {E : Source.Env} {srcΓ : Source.RCtx} {C : Contract} {Γ : Ctx} {ι : Type}
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat) (source : Source.EMState E srcΓ) (target : State C Γ)
    (d : Source.DeclName) (si : ι → Source.Idx srcΓ (.int .u256)) (ti : ι → Idx Γ (.val .uint))
    (family : IntegerLocalFamily .u256 si ti source.1 target.env) (i r : ι) (x : Int)
    (hx : Source.IntTy.u256.lo ≤ x ∧ x ≤ Source.IntTy.u256.hi)
    (valid : 0 ≤ x ∧ x.toNat < E.layout.enumSize d) (read : source.1.get (si r) = .int x hx) :
    (Source.evalE G F (fuel+3) (.convExplicit (τ := .enum d)
      (.assign (.local (si i)) (.local (si r))) (allowed_from E d))).run source =
      (.ok (.val (.enum ⟨x.toNat,valid.2⟩)),(source.1.set (si i) (.int x hx),source.2)) ∧
    (assignLocalOperand (ti i) (ti r)).run target =
      .ok (⟨target.setLocal (ti i) (integerValue .u256 x hx),List.prefix_refl _⟩,.prim (integerValue .u256 x hx)) ∧
    EnumRel d (.enum ⟨x.toNat,valid.2⟩ : Source.Val E.layout (.enum d)) (integerValue .u256 x hx) ∧
    IntegerLocalFamily .u256 si ti (source.1.set (si i) (.int x hx))
      (TEnv.set (ti i) (integerValue .u256 x hx) target.env) := by
  have post := family.write i r
  rw [read,family.read r x hx read] at post
  exact ⟨source_from_run G F (fuel+2) source _ d _ x hx valid
    (source_assign_local_run G F fuel source (si i) (si r) (.int x hx) read),
    assign_local_operand_run target (ti i) (ti r) _ (family.read r x hx read),from_related d x hx valid,post⟩

theorem to_assignment_transport {E : Source.Env} {srcΓ : Source.RCtx} {C : Contract} {Γ : Ctx}
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat) (source : Source.EMState E srcΓ) (target : State C Γ)
    (d : Source.DeclName) (capacity : E.layout.enumSize d ≤ 2^256)
    (m : ContextMap srcΓ Γ)
    (R : (τ : Source.STy) → (u : LTy) → Source.Val E.layout τ → u.TDenote C target.H → Prop)
    (aligned : m.Related R source.1 target.env)
    (reflect : ∀ (v : Source.Val E.layout (.enum d)) (n : PrimTy.uint.Denote),
      R (.enum d) (.val .uint) v n → EnumRel d v n)
    (i r : Source.Idx srcΓ (.enum d)) (j k : Idx Γ (.val .uint))
    (writeMap : m.slot i = ⟨.val .uint,j⟩) (readMap : m.slot r = ⟨.val .uint,k⟩)
    (a : Fin (E.layout.enumSize d)) (read : source.1.get r = .enum a) :
    (Source.evalE G F (fuel+3) (.convExplicit (τ := .int .u256)
      (.assign (.local i) (.local r)) (allowed_to E d))).run source =
      (.ok (.val (.int a.val (enum_range d capacity a))),(source.1.set i (.enum a),source.2)) ∧
    (assignLocalOperand j k).run target =
      .ok (⟨target.setLocal j (enumValue d capacity a),List.prefix_refl _⟩,.prim (enumValue d capacity a)) ∧
    IntValueRel .u256 (.int a.val (enum_range d capacity a) : Source.Val E.layout (.int .u256)) (enumValue d capacity a) ∧
    m.Related R (source.1.set i (.enum a)) (TEnv.set j (enumValue d capacity a) target.env) := by
  have point := reflect _ _ (ContextMap.value_at m R source.1 target.env aligned r k readMap)
  rw [read] at point
  have targetRead := enum_read d capacity a _ point
  have post : m.Related R (source.1.set i (source.1.get r)) (TEnv.set j (TEnv.get k target.env) target.env) :=
    ContextMap.related_assign m R source.1 target.env aligned i r j k writeMap readMap
  rw [read,targetRead] at post
  exact ⟨source_to_run G F (fuel+2) source _ d capacity _ a
    (source_assign_local_run G F fuel source i r (.enum a) read),
    assign_local_operand_run target j k _ targetRead,integer_related .u256 _ _,post⟩

/-- This Source-only failure clause does not certify a native enum guard. -/
theorem source_from_uint_refused {D : Source.Layout} (d : Source.DeclName) (x : Int)
    (hx : Source.IntTy.u256.lo ≤ x ∧ x ≤ Source.IntTy.u256.hi)
    (invalid : ¬ (0 ≤ x ∧ x.toNat < D.enumSize d)) :
    Source.convExplicitVal (.enum d) (.int x hx : Source.Val D (.int .u256)) =
      .error (.revert (Source.panicData .enumConv)) := by
  change Source.enumOfInt (D := D) d x = _
  unfold Source.enumOfInt
  split
  · rename_i valid
    exact False.elim (invalid valid)
  · rfl

theorem source_from_refused_run {E : Source.Env} {Γ : Source.RCtx}
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat) (source mid : Source.EMState E Γ)
    (d : Source.DeclName) (e : Source.RExpr E Γ (.int .u256)) (x : Int)
    (hx : Source.IntTy.u256.lo ≤ x ∧ x ≤ Source.IntTy.u256.hi)
    (invalid : ¬ (0 ≤ x ∧ x.toNat < E.layout.enumSize d))
    (read : (Source.evalE G F fuel e).run source = (.ok (.val (.int x hx)),mid)) :
    (Source.evalE G F (fuel+1) (.convExplicit (τ := .enum d) e (allowed_from E d))).run source =
      (.error (.revert (Source.panicData .enumConv)),mid) := by
  rw [Source.evalE,Source.Hoare.run_bind,read]
  change (do
    let v ← Source.EM.lift (Source.convExplicitVal (.enum d) (.int x hx : Source.Val E.layout (.int .u256)))
    pure (Source.RVal.val v)).run mid = _
  rw [source_from_uint_refused d x hx invalid]
  rfl

theorem source_from_refused_assignment {E : Source.Env} {Γ : Source.RCtx}
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat) (source : Source.EMState E Γ)
    (d : Source.DeclName) (i r : Source.Idx Γ (.int .u256)) (x : Int)
    (hx : Source.IntTy.u256.lo ≤ x ∧ x ≤ Source.IntTy.u256.hi)
    (invalid : ¬ (0 ≤ x ∧ x.toNat < E.layout.enumSize d)) (read : source.1.get r = .int x hx) :
    (Source.evalE G F (fuel+3) (.convExplicit (τ := .enum d)
      (.assign (.local i) (.local r)) (allowed_from E d))).run source =
      (.error (.revert (Source.panicData .enumConv)),(source.1.set i (.int x hx),source.2)) :=
  source_from_refused_run G F (fuel+2) source _ d _ x hx invalid
    (source_assign_local_run G F fuel source i r (.int x hx) read)
end Solidity.Lowering.V07.EnumConversions

/-- info: 'Solidity.Lowering.V07.EnumConversions.enum_range' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.EnumConversions.enum_range

/-- info: 'Solidity.Lowering.V07.EnumConversions.enum_related' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.EnumConversions.enum_related

/-- info: 'Solidity.Lowering.V07.EnumConversions.enum_read' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.EnumConversions.enum_read

/-- info: 'Solidity.Lowering.V07.EnumConversions.allowed_from' does not depend on any axioms -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.EnumConversions.allowed_from

/-- info: 'Solidity.Lowering.V07.EnumConversions.allowed_to' does not depend on any axioms -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.EnumConversions.allowed_to

/-- info: 'Solidity.Lowering.V07.EnumConversions.source_from_uint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.EnumConversions.source_from_uint

/-- info: 'Solidity.Lowering.V07.EnumConversions.source_to_uint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.EnumConversions.source_to_uint

/-- info: 'Solidity.Lowering.V07.EnumConversions.from_related' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.EnumConversions.from_related

/-- info: 'Solidity.Lowering.V07.EnumConversions.source_to_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.EnumConversions.source_to_run

/-- info: 'Solidity.Lowering.V07.EnumConversions.source_from_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.EnumConversions.source_from_run

/-- info: 'Solidity.Lowering.V07.EnumConversions.from_assignment_transport' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.EnumConversions.from_assignment_transport

/-- info: 'Solidity.Lowering.V07.EnumConversions.to_assignment_transport' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.EnumConversions.to_assignment_transport

/-- info: 'Solidity.Lowering.V07.EnumConversions.source_from_uint_refused' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.EnumConversions.source_from_uint_refused

/-- info: 'Solidity.Lowering.V07.EnumConversions.source_from_refused_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.EnumConversions.source_from_refused_run

/-- info: 'Solidity.Lowering.V07.EnumConversions.source_from_refused_assignment' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.EnumConversions.source_from_refused_assignment
