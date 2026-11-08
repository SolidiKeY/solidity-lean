import Solidity.Lowering.V07.UnsignedQuotRemGuard

/-! Shared operational guard lemma for G16 scalar families. It preserves the
published panic bytes, without asserting rollback or a session projection. -/
namespace Solidity.Lowering.G16.PanicGuard

/-- The existing intrinsic panic statement at the existing Source panic code. -/
def code {C : Contract} {Γ : Ctx} (panic : Source.PanicCode)
    (condition : Val C Γ .bool) : Stmt C Γ Γ := panicStmt panic.code condition

/-- Compose an independently established guard test with the actual panic
statement. Both successful and failing tests are included. -/
theorem run {C : Contract} {Γ : Ctx} (target : State C Γ)
    (panic : Source.PanicCode) (condition : Val C Γ .bool) (answer : Bool)
    (computed : condition.evalT target = .ok answer) :
    (code panic condition).run target =
      if answer then .ok (⟨target,List.prefix_refl _⟩ : Out C target.H Γ)
      else .error (THalt.ofData (Source.panicData panic)) := by
  cases answer with
  | true =>
    change TRun.ite condition _ _ _ _ target = _
    simp only [TRun.ite,computed,boolT,TRun.nil]
    rfl
  | false =>
    change TRun.ite condition _ _ _ _ target = _
    have literal := Backend.Failure.revert_bytes_intrinsic target (Semantics.encodePanic panic.code)
    simp only [TRun.ite,computed,boolT,ok_bind,Bool.false_eq_true,if_false,TRun.seq,literal]
    rw [Solidity.Lowering.V08.panicData_transport]
    rfl

/-- Guards against making a false scalar panic test a successful no-op. The
constant condition is inhabited and evaluated by the actual guard runner. -/
theorem false_guard_not_success {C : Contract} {Γ : Ctx} (target : State C Γ)
    (panic : Source.PanicCode) :
    (code panic (.simple (.bool false))).run target ≠
      .ok (⟨target,List.prefix_refl _⟩ : Out C target.H Γ) := by
  rw [run target panic (.simple (.bool false)) false rfl]
  intro impossible
  cases impossible

end Solidity.Lowering.G16.PanicGuard

/-- info: 'Solidity.Lowering.G16.PanicGuard.run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Lowering.G16.PanicGuard.run
/-- info: 'Solidity.Lowering.G16.PanicGuard.false_guard_not_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Lowering.G16.PanicGuard.false_guard_not_success
