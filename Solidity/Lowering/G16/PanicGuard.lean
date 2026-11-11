import Solidity.Lowering.V07.UnsignedQuotRemGuard

/-! Shared operational guard lemma for G16 scalar families. It preserves the published panic bytes, without asserting rollback or a session projection. -/
namespace Solidity.Lowering.G16.PanicGuard

/-- The existing intrinsic panic statement at the existing Source panic code. -/
def code {C : Contract} {Γ : Ctx} (panic : Source.PanicCode)
    (condition : Val C Γ .bool) : Stmt C Γ Γ := panicStmt panic.code condition

/-- Compose an independently established guard test with the actual panic statement. Both successful and failing tests are included. -/
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

/-- Guards against making a false scalar panic test a successful no-op. The constant condition is inhabited and evaluated by the actual guard runner. -/
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

/-- Existing steps followed by a checked scalar guard; the value is read before steps locals are dropped. -/
def afterPrefix {C : Contract} {Γ Δ : Ctx} {p : PrimTy} (steps : Prog C Γ Δ)
    (panic : Source.PanicCode) (checked : Bool) (condition : Val C Δ .bool)
    (value : Val C Δ p) : DeferredSource.Operand C Γ (.prim p) :=
  ⟨Δ,steps.join (if checked then .cons (code panic condition) .nil else .nil),.val value⟩

/-- Compose independent steps/test/value computations, preserving exact panic bytes and reached caller effects. -/
theorem afterPrefix_run {C : Contract} {Γ Δ : Ctx} {p : PrimTy}
    (target : State C Γ) (steps : Prog C Γ Δ) (reached : State C Δ)
    (heap : List.IsPrefix target.H reached.H)
    (prefixRun : steps.run target = .ok ⟨reached,heap⟩)
    (panic : Source.PanicCode) (checked : Bool) (condition : Val C Δ .bool)
    (value : Val C Δ p) (answer : Bool) (result : p.Denote)
    (test : condition.evalT reached = .ok answer) (computed : value.evalT reached = .ok result) :
    (afterPrefix steps panic checked condition value).run target =
      if checked = true ∧ answer = false then .error (THalt.ofData (Source.panicData panic))
      else .ok (⟨reached.drop steps.ext,heap⟩,.prim result) := by
  have inner := checkedOperand_run reached panic checked condition value answer result test computed
  let suffix : Prog C Δ Δ := if checked then .cons (code panic condition) .nil else .nil
  have ext : (steps.join suffix).ext = steps.ext := by
    exact Ext.eq_of_depth _ _
  unfold afterPrefix DeferredSource.Operand.run
  change (do let out ← (steps.join suffix).run target
             let v ← (Src.val value).valueT out.st
             pure ((⟨out.st.drop (steps.join suffix).ext,out.ext⟩ : Out C target.H Γ),v)) = _
  rw [DeferredSource.join_run]
  change (do let out ← TRun.seq steps.runR suffix.runR target
             let v ← (Src.val value).valueT out.st
             pure ((⟨out.st.drop (steps.join suffix).ext,out.ext⟩ : Out C target.H Γ),v)) = _
  simp only [TRun.seq,show steps.runR target = .ok ⟨reached,heap⟩ from prefixRun]
  unfold checkedOperand DeferredSource.Operand.run at inner
  change (do let out ← suffix.run reached
             let v ← (Src.val value).valueT out.st
             pure ((⟨out.st.drop suffix.ext,out.ext⟩ : Out C reached.H Δ),v)) = _ at inner
  rw [Ext.eq_of_depth suffix.ext Ext.refl] at inner
  rw [ext]
  simp only [Prog.run] at inner
  generalize suffix.runR reached = next at inner ⊢
  cases next with
  | error failure =>
    change Except.error failure = _ at inner
    change Except.error failure = _
    by_cases failed : checked = true ∧ answer = false
    · simp only [if_pos failed] at inner ⊢
      exact congrArg Except.error (Except.error.inj inner)
    · simp only [if_neg failed] at inner
      cases inner
  | ok out =>
    dsimp only [Except.map,bind,Except.bind] at inner ⊢
    generalize (Src.val value).valueT out.st = observed at inner ⊢
    cases observed with
    | error failure =>
      by_cases failed : checked = true ∧ answer = false
      · simp only [if_pos failed] at inner ⊢
        exact congrArg Except.error (Except.error.inj inner)
      · simp only [if_neg failed] at inner
        cases inner
    | ok v =>
      by_cases failed : checked = true ∧ answer = false
      · simp only [if_pos failed] at inner
        cases inner
      · simp only [if_neg failed] at inner ⊢
        have same := Except.ok.inj inner
        exact congrArg (fun r : Out C reached.H Δ × SVal (.prim p) =>
          (Except.ok ((⟨r.1.st.drop steps.ext,heap.trans r.1.ext⟩ : Out C target.H Γ),r.2) :
            TRes (Out C target.H Γ × SVal (.prim p)))) same

/-- Reject erasing a failing guard after an inhabited empty steps. -/
theorem afterPrefix_false_rejected {C : Contract} {Γ : Ctx} (target : State C Γ)
    (panic : Source.PanicCode) :
    (afterPrefix (Prog.nil : Prog C Γ Γ) panic true (.simple (.bool false))
      (.simple (.bool true))).run target ≠ .ok (⟨target,List.prefix_refl _⟩,.prim true) := by
  rw [afterPrefix_run target .nil target (List.prefix_refl _) (Prog.run_nil _) panic true
    (.simple (.bool false)) (.simple (.bool true)) false true rfl rfl]
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

/-- info: 'Solidity.Lowering.G16.PanicGuard.afterPrefix_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Lowering.G16.PanicGuard.afterPrefix_run
/-- info: 'Solidity.Lowering.G16.PanicGuard.afterPrefix_false_rejected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Lowering.G16.PanicGuard.afterPrefix_false_rejected
