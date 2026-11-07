import Solidity.Lowering.V07.EnumConversions
import Solidity.Lowering.V07.WordCasts

/-! Enum-to-int256 transport reuses the existing word-sign conversion.
Caller enum/uint bindings retain original ordinals; only the result is signed.
Capacity is the existing representation obligation, not Source admission. -/
namespace Solidity.Lowering.V07.EnumSignedWord
open WordCasts (signed)

theorem allowed (E : Source.Env) (d : Source.DeclName) :
    (Source.STy.enum d).explicit E.isBase E.mapFree (.int signed) = true := rfl

theorem source_value {D : Source.Layout} (d : Source.DeclName) (i : Fin (D.enumSize d)) :
    Source.convExplicitVal (.int signed) (.enum i : Source.Val D (.enum d)) =
      .ok (Source.intWrap signed i.val) := rfl

theorem source_run {E : Source.Env} {Γ : Source.RCtx} (G : Source.Glob E) (F : Source.Fr)
    (fuel : Nat) (source mid : Source.EMState E Γ) (d : Source.DeclName)
    (expr : Source.RExpr E Γ (.enum d)) (i : Fin (E.layout.enumSize d))
    (read : (Source.evalE G F fuel expr).run source = (.ok (.val (.enum i)),mid)) :
    (Source.evalE G F (fuel+1) (.convExplicit (τ := .int signed) expr (allowed E d))).run source =
      (.ok (.val (Source.intWrap signed i.val)),mid) := by
  rw [Source.evalE,Source.Hoare.run_bind,read]
  rfl

theorem source_assignment {E : Source.Env} {Γ : Source.RCtx} (G : Source.Glob E) (F : Source.Fr)
    (fuel : Nat) (source : Source.EMState E Γ) (d : Source.DeclName)
    (i r : Source.Idx Γ (.enum d)) (a : Fin (E.layout.enumSize d)) (read : source.1.get r = .enum a) :
    (Source.evalE G F (fuel+3) (.convExplicit (τ := .int signed)
      (.assign (.local i) (.local r)) (allowed E d))).run source =
      (.ok (.val (Source.intWrap signed a.val)),(source.1.set i (.enum a),source.2)) :=
  source_run G F (fuel+2) source _ d _ a (source_assign_local_run G F fuel source i r (.enum a) read)

theorem value_run {D : Source.Layout} {C : Contract} {Γ : Ctx} (target : State C Γ)
    (d : Source.DeclName) (capacity : D.enumSize d ≤ 2^256) (value : Val C Γ .uint)
    (a : Fin (D.enumSize d)) (read : value.evalT target = .ok (EnumConversions.enumValue d capacity a)) :
    (Val.unop .toInt rfl rfl value).evalT target =
      .ok (integerValue signed (signed.wrap a.val) (signed.wrap_mem a.val)) :=
  WordCasts.to_int_run target value a.val (EnumConversions.enum_range d capacity a) read

theorem value_related {D : Source.Layout} (d : Source.DeclName) (a : Fin (D.enumSize d)) :
    IntValueRel signed (Source.intWrap signed a.val : Source.Val D (.int signed))
      (integerValue signed (signed.wrap a.val) (signed.wrap_mem a.val)) :=
  integer_related _ _ _

theorem transport {E : Source.Env} {srcΓ : Source.RCtx} {C : Contract} {Γ : Ctx}
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat) (source : Source.EMState E srcΓ) (target : State C Γ)
    (d : Source.DeclName) (capacity : E.layout.enumSize d ≤ 2^256) (m : ContextMap srcΓ Γ)
    (R : (τ : Source.STy) → (u : LTy) → Source.Val E.layout τ → u.TDenote C target.H → Prop)
    (aligned : m.Related R source.1 target.env)
    (reflect : ∀ (v : Source.Val E.layout (.enum d)) (n : PrimTy.uint.Denote),
      R (.enum d) (.val .uint) v n → EnumConversions.EnumRel d v n)
    (i r : Source.Idx srcΓ (.enum d)) (j k : Idx Γ (.val .uint))
    (writeMap : m.slot i = ⟨.val .uint,j⟩) (readMap : m.slot r = ⟨.val .uint,k⟩)
    (a : Fin (E.layout.enumSize d)) (read : source.1.get r = .enum a) :
    (Source.evalE G F (fuel+3) (.convExplicit (τ := .int signed)
      (.assign (.local i) (.local r)) (allowed E d))).run source =
      (.ok (.val (Source.intWrap signed a.val)),(source.1.set i (.enum a),source.2)) ∧
    (WordCasts.assignedToInt j k).run target =
      .ok (⟨target.setLocal j (EnumConversions.enumValue d capacity a),List.prefix_refl _⟩,
        .prim (integerValue signed (signed.wrap a.val) (signed.wrap_mem a.val))) ∧
    IntValueRel signed (Source.intWrap signed a.val : Source.Val E.layout (.int signed))
      (integerValue signed (signed.wrap a.val) (signed.wrap_mem a.val)) ∧
    m.Related R (source.1.set i (.enum a)) (TEnv.set j (EnumConversions.enumValue d capacity a) target.env) := by
  have point := reflect _ _ (ContextMap.value_at m R source.1 target.env aligned r k readMap)
  rw [read] at point
  have targetRead := EnumConversions.enum_read d capacity a _ point
  have post : m.Related R (source.1.set i (source.1.get r)) (TEnv.set j (TEnv.get k target.env) target.env) :=
    ContextMap.related_assign m R source.1 target.env aligned i r j k writeMap readMap
  rw [read,targetRead] at post
  exact ⟨source_assignment G F fuel source d i r a read,
    WordCasts.assigned_to_int_run target j k a.val (EnumConversions.enum_range d capacity a) targetRead,
    value_related d a,post⟩


/-- info: 'Solidity.Lowering.V07.EnumSignedWord.allowed' does not depend on any axioms -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.EnumSignedWord.allowed

/-- info: 'Solidity.Lowering.V07.EnumSignedWord.source_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.EnumSignedWord.source_value

/-- info: 'Solidity.Lowering.V07.EnumSignedWord.source_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.EnumSignedWord.source_run

/-- info: 'Solidity.Lowering.V07.EnumSignedWord.source_assignment' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.EnumSignedWord.source_assignment

/-- info: 'Solidity.Lowering.V07.EnumSignedWord.value_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.EnumSignedWord.value_run

/-- info: 'Solidity.Lowering.V07.EnumSignedWord.value_related' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.EnumSignedWord.value_related

/-- info: 'Solidity.Lowering.V07.EnumSignedWord.transport' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.EnumSignedWord.transport

end Solidity.Lowering.V07.EnumSignedWord
