import Solidity.Lowering.V07.EnumGuard
import Solidity.Lowering.V07.UnsignedWidthCasts

/-! Approved unsigned widths reuse the same typed native enum guard. Existing
widening/range laws discharge word representation obligations; no opcode
compiler, Source evaluator, admission/profile or guard limit is introduced. -/
namespace Solidity.Lowering.V07.UnsignedEnumGuard
open UnsignedNarrowing (ty)

theorem word_value (bits : Nat) (width : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256) (x : Int)
    (hx : (ty bits width).lo ≤ x ∧ x ≤ (ty bits width).hi) :
    integerValue (ty bits width) x hx =
      integerValue .u256 x (UnsignedWidthCasts.word_range bits width x hx) := by
  apply Subtype.ext
  rfl

theorem value_bridge {D : Source.Layout} (d : Source.DeclName) (bits : Nat)
    (width : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256) (x : Int)
    (hx : (ty bits width).lo ≤ x ∧ x ≤ (ty bits width).hi) :
    Source.convExplicitVal (.enum d) (.int x hx : Source.Val D (.int (ty bits width))) =
      Source.convExplicitVal (.enum d)
        (.int x (UnsignedWidthCasts.word_range bits width x hx) : Source.Val D (.int .u256)) := rfl

theorem allowed (E : Source.Env) (d : Source.DeclName) (bits : Nat)
    (width : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256) :
    (Source.STy.int (ty bits width)).explicit E.isBase E.mapFree (.enum d) = true := rfl

theorem source_value {D : Source.Layout} (d : Source.DeclName) (bits : Nat)
    (width : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256) (x : Int)
    (hx : (ty bits width).lo ≤ x ∧ x ≤ (ty bits width).hi)
    (valid : 0 ≤ x ∧ x.toNat < D.enumSize d) :
    Source.convExplicitVal (.enum d) (.int x hx : Source.Val D (.int (ty bits width))) =
      .ok (.enum ⟨x.toNat,valid.2⟩) := by
  rw [value_bridge d bits width x hx]
  exact EnumConversions.source_from_uint d x (UnsignedWidthCasts.word_range bits width x hx) valid

theorem source_value_failure {D : Source.Layout} (d : Source.DeclName) (bits : Nat)
    (width : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256) (x : Int)
    (hx : (ty bits width).lo ≤ x ∧ x ≤ (ty bits width).hi)
    (invalid : ¬ (0 ≤ x ∧ x.toNat < D.enumSize d)) :
    Source.convExplicitVal (.enum d) (.int x hx : Source.Val D (.int (ty bits width))) =
      .error (.revert (Source.panicData .enumConv)) := by
  rw [value_bridge d bits width x hx]
  exact EnumConversions.source_from_uint_refused d x (UnsignedWidthCasts.word_range bits width x hx) invalid

theorem source_run {E : Source.Env} {Γ : Source.RCtx} (G : Source.Glob E) (F : Source.Fr)
    (fuel : Nat) (source mid : Source.EMState E Γ) (d : Source.DeclName) (bits : Nat)
    (width : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256)
    (e : Source.RExpr E Γ (.int (ty bits width))) (x : Int)
    (hx : (ty bits width).lo ≤ x ∧ x ≤ (ty bits width).hi)
    (valid : 0 ≤ x ∧ x.toNat < E.layout.enumSize d)
    (read : (Source.evalE G F fuel e).run source = (.ok (.val (.int x hx)),mid)) :
    (Source.evalE G F (fuel+1) (.convExplicit (τ := .enum d) e (allowed E d bits width))).run source =
      (.ok (.val (.enum ⟨x.toNat,valid.2⟩)),mid) := by
  rw [Source.evalE,Source.Hoare.run_bind,read]
  change (do
    let v ← Source.EM.lift (Source.convExplicitVal (.enum d) (.int x hx : Source.Val E.layout (.int (ty bits width))))
    pure (Source.RVal.val v)).run mid = _
  rw [source_value d bits width x hx valid]
  rfl

theorem source_failed_run {E : Source.Env} {Γ : Source.RCtx} (G : Source.Glob E) (F : Source.Fr)
    (fuel : Nat) (source mid : Source.EMState E Γ) (d : Source.DeclName) (bits : Nat)
    (width : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256)
    (e : Source.RExpr E Γ (.int (ty bits width))) (x : Int)
    (hx : (ty bits width).lo ≤ x ∧ x ≤ (ty bits width).hi)
    (invalid : ¬ (0 ≤ x ∧ x.toNat < E.layout.enumSize d))
    (read : (Source.evalE G F fuel e).run source = (.ok (.val (.int x hx)),mid)) :
    (Source.evalE G F (fuel+1) (.convExplicit (τ := .enum d) e (allowed E d bits width))).run source =
      (.error (.revert (Source.panicData .enumConv)),mid) := by
  rw [Source.evalE,Source.Hoare.run_bind,read]
  change (do
    let v ← Source.EM.lift (Source.convExplicitVal (.enum d) (.int x hx : Source.Val E.layout (.int (ty bits width))))
    pure (Source.RVal.val v)).run mid = _
  rw [source_value_failure d bits width x hx invalid]
  rfl

theorem enum_related {D : Source.Layout} (d : Source.DeclName) (bits : Nat)
    (width : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256) (x : Int)
    (hx : (ty bits width).lo ≤ x ∧ x ≤ (ty bits width).hi)
    (valid : 0 ≤ x ∧ x.toNat < D.enumSize d) :
    EnumConversions.EnumRel d (.enum ⟨x.toNat,valid.2⟩ : Source.Val D (.enum d))
      (integerValue (ty bits width) x hx) := by
  rw [word_value bits width x hx]
  exact EnumConversions.from_related d x (UnsignedWidthCasts.word_range bits width x hx) valid

theorem transport_success {E : Source.Env} {srcΓ : Source.RCtx} {C : Contract} {Γ : Ctx} {ι : Type}
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat) (source : Source.EMState E srcΓ) (target : State C Γ)
    (d : Source.DeclName) (capacity : E.layout.enumSize d ≤ 2^256) (bits : Nat)
    (width : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256)
    (si : ι → Source.Idx srcΓ (.int (ty bits width))) (ti : ι → Idx Γ (.val .uint))
    (family : IntegerLocalFamily (ty bits width) si ti source.1 target.env) (i r : ι) (x : Int)
    (hx : (ty bits width).lo ≤ x ∧ x ≤ (ty bits width).hi)
    (valid : 0 ≤ x ∧ x.toNat < E.layout.enumSize d) (read : source.1.get (si r) = .int x hx) :
    (Source.evalE G F (fuel+3) (.convExplicit (τ := .enum d)
      (.assign (.local (si i)) (.local (si r))) (allowed E d bits width))).run source =
      (.ok (.val (.enum ⟨x.toNat,valid.2⟩)),(source.1.set (si i) (.int x hx),source.2)) ∧
    (EnumGuard.operand (E.layout.enumSize d) capacity (ti i) (ti r)).run target =
      .ok (⟨target.setLocal (ti i) (integerValue (ty bits width) x hx),List.prefix_refl _⟩,
        .prim (integerValue (ty bits width) x hx)) ∧
    EnumConversions.EnumRel d (.enum ⟨x.toNat,valid.2⟩ : Source.Val E.layout (.enum d)) (integerValue (ty bits width) x hx) ∧
    IntegerLocalFamily (ty bits width) si ti (source.1.set (si i) (.int x hx))
      (TEnv.set (ti i) (integerValue (ty bits width) x hx) target.env) := by
  have post := family.write i r
  rw [read,family.read r x hx read] at post
  exact ⟨source_run G F (fuel+2) source _ d bits width _ x hx valid
    (source_assign_local_run G F fuel source (si i) (si r) (.int x hx) read),
    EnumGuard.operand_success target _ capacity (ti i) (ti r) _ (family.read r x hx read) valid.2,
    enum_related d bits width x hx valid,post⟩

theorem transport_failure {E : Source.Env} {srcΓ : Source.RCtx} {C : Contract} {Γ : Ctx} {ι : Type}
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat) (source : Source.EMState E srcΓ) (target : State C Γ)
    (d : Source.DeclName) (capacity : E.layout.enumSize d ≤ 2^256) (bits : Nat)
    (width : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256)
    (si : ι → Source.Idx srcΓ (.int (ty bits width))) (ti : ι → Idx Γ (.val .uint))
    (family : IntegerLocalFamily (ty bits width) si ti source.1 target.env) (i r : ι) (x : Int)
    (hx : (ty bits width).lo ≤ x ∧ x ≤ (ty bits width).hi)
    (invalid : ¬ (0 ≤ x ∧ x.toNat < E.layout.enumSize d)) (read : source.1.get (si r) = .int x hx) :
    (Source.evalE G F (fuel+3) (.convExplicit (τ := .enum d)
      (.assign (.local (si i)) (.local (si r))) (allowed E d bits width))).run source =
      (.error (.revert (Source.panicData .enumConv)),(source.1.set (si i) (.int x hx),source.2)) ∧
    (EnumGuard.operand (E.layout.enumSize d) capacity (ti i) (ti r)).run target =
      .error (THalt.ofData (Source.panicData .enumConv)) ∧
    (Stmt.assignLocal (ti i) (.simple (.local (ti r)))).run target =
      .ok (⟨target.setLocal (ti i) (integerValue (ty bits width) x hx),List.prefix_refl _⟩ : Out C target.H Γ) ∧
    Backend.Failure.HaltObserves (THalt.ofData (Source.panicData .enumConv)) (.revert (Source.panicData .enumConv)) := by
  have nonnegative : 0 ≤ x := hx.1
  have outside : ¬ x.toNat < E.layout.enumSize d := by omega
  exact ⟨source_failed_run G F (fuel+2) source _ d bits width _ x hx invalid
    (source_assign_local_run G F fuel source (si i) (si r) (.int x hx) read),
    EnumGuard.operand_failure target _ capacity (ti i) (ti r) _ (family.read r x hx read) outside,
    EnumGuard.assignment_run target (ti i) (ti r) _ (family.read r x hx read),Backend.Failure.ofData_observes _⟩
end Solidity.Lowering.V07.UnsignedEnumGuard

/-- info: 'Solidity.Lowering.V07.UnsignedEnumGuard.word_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UnsignedEnumGuard.word_value

/-- info: 'Solidity.Lowering.V07.UnsignedEnumGuard.value_bridge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UnsignedEnumGuard.value_bridge

/-- info: 'Solidity.Lowering.V07.UnsignedEnumGuard.allowed' does not depend on any axioms -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UnsignedEnumGuard.allowed

/-- info: 'Solidity.Lowering.V07.UnsignedEnumGuard.source_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UnsignedEnumGuard.source_value

/-- info: 'Solidity.Lowering.V07.UnsignedEnumGuard.source_value_failure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UnsignedEnumGuard.source_value_failure

/-- info: 'Solidity.Lowering.V07.UnsignedEnumGuard.source_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UnsignedEnumGuard.source_run

/-- info: 'Solidity.Lowering.V07.UnsignedEnumGuard.source_failed_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UnsignedEnumGuard.source_failed_run

/-- info: 'Solidity.Lowering.V07.UnsignedEnumGuard.enum_related' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UnsignedEnumGuard.enum_related

/-- info: 'Solidity.Lowering.V07.UnsignedEnumGuard.transport_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UnsignedEnumGuard.transport_success

/-- info: 'Solidity.Lowering.V07.UnsignedEnumGuard.transport_failure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.UnsignedEnumGuard.transport_failure
