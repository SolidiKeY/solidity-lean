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


/-- Internal target composition toward `Solidity.Goals.lowerLoopsCorrect`; no Source producer is supplied. -/
def checkedOperand {C : Contract} {Γ : Ctx} {p : PrimTy}
    (panic : Source.PanicCode) (checked : Bool) (condition : Val C Γ .bool)
    (value : Val C Γ p) : DeferredSource.Operand C Γ (.prim p) :=
  ⟨Γ,(if checked then .cons (code panic condition) .nil else .nil),.val value⟩

/-- Compose independently computed test/value results; a checked false test retains exact panic bytes. -/
theorem checkedOperand_run {C : Contract} {Γ : Ctx} {p : PrimTy}
    (target : State C Γ) (panic : Source.PanicCode) (checked : Bool)
    (condition : Val C Γ .bool) (value : Val C Γ p) (answer : Bool) (result : p.Denote)
    (test : condition.evalT target = .ok answer) (computed : value.evalT target = .ok result) :
    (checkedOperand panic checked condition value).run target =
      if checked = true ∧ answer = false then .error (THalt.ofData (Source.panicData panic))
      else .ok (⟨target,List.prefix_refl _⟩,.prim result) := by
  let steps : Prog C Γ Γ := if checked then .cons (code panic condition) .nil else .nil
  have prefixRun : steps.run target =
      if checked = true ∧ answer = false then .error (THalt.ofData (Source.panicData panic))
      else .ok (⟨target,List.prefix_refl _⟩ : Out C target.H Γ) := by
    cases checked with
    | false => simp only [steps,Bool.false_eq_true,if_false,false_and,Prog.run_nil]
    | true =>
      cases answer with
      | false =>
        have failed := run target panic condition false test
        simp only [Bool.false_eq_true,if_false] at failed
        change TRun.seq (code panic condition).runR _ target = _
        simp only [TRun.seq,show (code panic condition).runR target =
          .error (THalt.ofData (Source.panicData panic)) from failed,true_and,if_true]
      | true =>
        have passed := run target panic condition true test
        simp only [if_true] at passed
        change (Prog.cons _ Prog.nil).run target = _
        rw [Prog.run_cons_ok passed,Prog.run_nil]
        rfl
  change (DeferredSource.Operand.run ⟨Γ,steps,.val value⟩ target) = _
  unfold DeferredSource.Operand.run
  rw [prefixRun]
  by_cases failed : checked = true ∧ answer = false
  · simp only [if_pos failed]
    rfl
  · simp only [if_neg failed]
    rw [Ext.eq_of_depth steps.ext Ext.refl]
    simp only [bind,Except.bind,Src.valueT]
    rw [computed]
    rfl

/-- Reject erasing a checked false guard in the composed operand; both literal evaluations are inhabited. -/
theorem checked_false_rejected {C : Contract} {Γ : Ctx} (target : State C Γ)
    (panic : Source.PanicCode) :
    (checkedOperand panic true (.simple (.bool false)) (.simple (.bool true))).run target ≠
      .ok (⟨target,List.prefix_refl _⟩,.prim true) := by
  rw [checkedOperand_run target panic true (.simple (.bool false)) (.simple (.bool true)) false true rfl rfl]
  intro impossible
  cases impossible

end Solidity.Lowering.G16.PanicGuard

/-- info: 'Solidity.Lowering.G16.PanicGuard.run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Lowering.G16.PanicGuard.run
/-- info: 'Solidity.Lowering.G16.PanicGuard.false_guard_not_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Lowering.G16.PanicGuard.false_guard_not_success

/-- info: 'Solidity.Lowering.G16.PanicGuard.checkedOperand_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Lowering.G16.PanicGuard.checkedOperand_run
/-- info: 'Solidity.Lowering.G16.PanicGuard.checked_false_rejected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Lowering.G16.PanicGuard.checked_false_rejected
