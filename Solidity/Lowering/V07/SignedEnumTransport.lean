import Solidity.Lowering.V07.SignedEnumGuard

/-! Actual signed-input enum assignment transport. Negative inputs are refused
before unsigned membership checks. No Source admission/compiler is assumed. -/
namespace Solidity.Lowering.V07.SignedEnumTransport
open SignedWidthCasts (ty)

theorem word_value (bits : Nat) (width : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256) (x : Int)
    (hx : (ty bits width).lo ≤ x ∧ x ≤ (ty bits width).hi) :
    integerValue (ty bits width) x hx =
      integerValue WordCasts.signed x (SignedWidthCasts.word_range bits width x hx) := by
  apply Subtype.ext
  rfl

theorem allowed (E : Source.Env) (d : Source.DeclName) (bits : Nat)
    (width : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256) :
    (Source.STy.int (ty bits width)).explicit E.isBase E.mapFree (.enum d) = true := rfl

theorem source_value {D : Source.Layout} (d : Source.DeclName) (bits : Nat)
    (width : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256) (x : Int)
    (hx : (ty bits width).lo ≤ x ∧ x ≤ (ty bits width).hi)
    (valid : 0 ≤ x ∧ x.toNat < D.enumSize d) :
    Source.convExplicitVal (.enum d) (.int x hx : Source.Val D (.int (ty bits width))) =
      .ok (.enum ⟨x.toNat,valid.2⟩) := by
  change Source.enumOfInt d x = _
  simp only [Source.enumOfInt,dif_pos valid]
  rfl

theorem source_value_failure {D : Source.Layout} (d : Source.DeclName) (bits : Nat)
    (width : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256) (x : Int)
    (hx : (ty bits width).lo ≤ x ∧ x ≤ (ty bits width).hi)
    (invalid : ¬ (0 ≤ x ∧ x.toNat < D.enumSize d)) :
    Source.convExplicitVal (.enum d) (.int x hx : Source.Val D (.int (ty bits width))) =
      .error (.revert (Source.panicData .enumConv)) := by
  change Source.enumOfInt d x = _
  simp only [Source.enumOfInt,dif_neg invalid]
  rfl

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
      (integerValue .u256 x (SignedEnumGuard.uint_range x (SignedWidthCasts.word_range bits width x hx) valid.1)) :=
  EnumConversions.from_related d x (SignedEnumGuard.uint_range x (SignedWidthCasts.word_range bits width x hx) valid.1) valid

theorem transport_success {E : Source.Env} {srcΓ : Source.RCtx} {C : Contract} {Γ : Ctx} {ι : Type}
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat) (source : Source.EMState E srcΓ) (target : State C Γ)
    (d : Source.DeclName) (capacity : E.layout.enumSize d ≤ 2^256) (bits : Nat)
    (width : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256)
    (si : ι → Source.Idx srcΓ (.int (ty bits width))) (ti : ι → Idx Γ (.val .int))
    (family : IntegerLocalFamily (ty bits width) si ti source.1 target.env) (i r : ι) (x : Int)
    (hx : (ty bits width).lo ≤ x ∧ x ≤ (ty bits width).hi)
    (valid : 0 ≤ x ∧ x.toNat < E.layout.enumSize d) (read : source.1.get (si r) = .int x hx) :
    (Source.evalE G F (fuel+3) (.convExplicit (τ := .enum d)
      (.assign (.local (si i)) (.local (si r))) (allowed E d bits width))).run source =
      (.ok (.val (.enum ⟨x.toNat,valid.2⟩)),(source.1.set (si i) (.int x hx),source.2)) ∧
    (SignedEnumGuard.operand (E.layout.enumSize d) capacity (ti i) (ti r)).run target =
      .ok (⟨target.setLocal (ti i) (integerValue (ty bits width) x hx),List.prefix_refl _⟩,
        .prim (integerValue .u256 x (SignedEnumGuard.uint_range x (SignedWidthCasts.word_range bits width x hx) valid.1))) ∧
    EnumConversions.EnumRel d (.enum ⟨x.toNat,valid.2⟩ : Source.Val E.layout (.enum d)) (integerValue .u256 x (SignedEnumGuard.uint_range x (SignedWidthCasts.word_range bits width x hx) valid.1)) ∧
    IntegerLocalFamily (ty bits width) si ti (source.1.set (si i) (.int x hx))
      (TEnv.set (ti i) (integerValue (ty bits width) x hx) target.env) := by
  have post := family.write i r
  rw [read,family.read r x hx read] at post
  have nativeRead : TEnv.get (ti r) target.env =
      integerValue WordCasts.signed x (SignedWidthCasts.word_range bits width x hx) := by
    rw [family.read r x hx read,word_value bits width x hx]
  have native := SignedEnumGuard.operand_success target _ capacity (ti i) (ti r) x
    (SignedWidthCasts.word_range bits width x hx) nativeRead valid
  rw [←word_value bits width x hx] at native
  exact ⟨source_run G F (fuel+2) source _ d bits width _ x hx valid
    (source_assign_local_run G F fuel source (si i) (si r) (.int x hx) read),
    native,enum_related d bits width x hx valid,post⟩

theorem transport_failure {E : Source.Env} {srcΓ : Source.RCtx} {C : Contract} {Γ : Ctx} {ι : Type}
    (G : Source.Glob E) (F : Source.Fr) (fuel : Nat) (source : Source.EMState E srcΓ) (target : State C Γ)
    (d : Source.DeclName) (capacity : E.layout.enumSize d ≤ 2^256) (bits : Nat)
    (width : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256)
    (si : ι → Source.Idx srcΓ (.int (ty bits width))) (ti : ι → Idx Γ (.val .int))
    (family : IntegerLocalFamily (ty bits width) si ti source.1 target.env) (i r : ι) (x : Int)
    (hx : (ty bits width).lo ≤ x ∧ x ≤ (ty bits width).hi)
    (invalid : ¬ (0 ≤ x ∧ x.toNat < E.layout.enumSize d)) (read : source.1.get (si r) = .int x hx) :
    (Source.evalE G F (fuel+3) (.convExplicit (τ := .enum d)
      (.assign (.local (si i)) (.local (si r))) (allowed E d bits width))).run source =
      (.error (.revert (Source.panicData .enumConv)),(source.1.set (si i) (.int x hx),source.2)) ∧
    (SignedEnumGuard.operand (E.layout.enumSize d) capacity (ti i) (ti r)).run target =
      .error (THalt.ofData (Source.panicData .enumConv)) ∧
    (Stmt.assignLocal (ti i) (.simple (.local (ti r)))).run target =
      .ok (⟨target.setLocal (ti i) (integerValue (ty bits width) x hx),List.prefix_refl _⟩ : Out C target.H Γ) ∧
    Backend.Failure.HaltObserves (THalt.ofData (Source.panicData .enumConv)) (.revert (Source.panicData .enumConv)) := by
  have nativeRead : TEnv.get (ti r) target.env =
      integerValue WordCasts.signed x (SignedWidthCasts.word_range bits width x hx) := by
    rw [family.read r x hx read,word_value bits width x hx]
  have assigned := SignedEnumGuard.assignment_run target (ti i) (ti r) x
    (SignedWidthCasts.word_range bits width x hx) nativeRead
  rw [←word_value bits width x hx] at assigned
  exact ⟨source_failed_run G F (fuel+2) source _ d bits width _ x hx invalid
    (source_assign_local_run G F fuel source (si i) (si r) (.int x hx) read),
    SignedEnumGuard.operand_failure target _ capacity (ti i) (ti r) x
      (SignedWidthCasts.word_range bits width x hx) nativeRead invalid,
    assigned,Backend.Failure.ofData_observes _⟩


/-- info: 'Solidity.Lowering.V07.SignedEnumTransport.word_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.SignedEnumTransport.word_value

/-- info: 'Solidity.Lowering.V07.SignedEnumTransport.allowed' does not depend on any axioms -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.SignedEnumTransport.allowed

/-- info: 'Solidity.Lowering.V07.SignedEnumTransport.source_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.SignedEnumTransport.source_value

/-- info: 'Solidity.Lowering.V07.SignedEnumTransport.source_value_failure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.SignedEnumTransport.source_value_failure

/-- info: 'Solidity.Lowering.V07.SignedEnumTransport.source_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.SignedEnumTransport.source_run

/-- info: 'Solidity.Lowering.V07.SignedEnumTransport.source_failed_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.SignedEnumTransport.source_failed_run

/-- info: 'Solidity.Lowering.V07.SignedEnumTransport.enum_related' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.SignedEnumTransport.enum_related

/-- info: 'Solidity.Lowering.V07.SignedEnumTransport.transport_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.SignedEnumTransport.transport_success

/-- info: 'Solidity.Lowering.V07.SignedEnumTransport.transport_failure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V07.SignedEnumTransport.transport_failure

end Solidity.Lowering.V07.SignedEnumTransport
