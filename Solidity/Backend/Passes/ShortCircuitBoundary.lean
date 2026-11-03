import Solidity.Backend.Passes.ValueCertificate

/-! Exact runtime short-circuit pass boundaries for existing intrinsic Boolean
values. A skipped RHS needs no source run premise. This is not effectful Source
call lowering or a new numeric/target evaluator. -/
namespace Solidity.Backend.Passes.ShortCircuitBoundary
open Evm Evm.Memory
variable {C : Contract} {Γ : Ctx}
def expression (skip : Bool) (left right : Val C Γ .bool) : Val C Γ .bool :=
  if skip then .binop .or rfl rfl left right else .binop .and rfl rfl left right
def compiled {b : Nat} {F : Frag Γ} (skip : Bool) {left right : Val C Γ .bool}
    (lc : CompiledVal b F left) (rc : CompiledVal b F right) :
    CompiledVal b F (expression skip left right) :=
  match skip with
  | true => ⟨_,.binary .or rfl rfl _ _ _ _ lc.cert rc.cert⟩
  | false => ⟨_,.binary .and rfl rfl _ _ _ _ lc.cert rc.cert⟩
theorem source (skip : Bool) (left right : Val C Γ .bool) (state : State C Γ)
    (a : Bool) (evaluated : left.evalT state = .ok a) :
    (expression skip left right).evalT state =
      if a = skip then .ok skip else right.evalT state := by
  cases skip <;> cases a <;>
    simp only [expression,Val.evalT,evaluated,BinOp.shortT,boolT,bind,Except.bind,
      pure,Except.pure,Bool.false_eq_true,Bool.true_eq_false,ite_false,ite_true]
  all_goals
    cases h : right.evalT state with
    | error e => rfl
    | ok v => cases v <;> rfl

theorem execution {b L frame : Nat} {F : Frag Γ} (skip : Bool)
    {left right : Val C Γ .bool} (lc : CompiledVal b F left) (rc : CompiledVal b F right)
    {state : State C Γ} {base : Nat → Fin W} {machine : Machine}
    (represented : StateRepr L b frame F state base machine)
    (a : Bool) (evaluated : left.evalT state = .ok a) :
    ∀ tail,
      run lc.code {machine with stack := tail} =
        .ok ({machine with stack := tail}.push (.val (bword a))) 0 ∧
      run (compiled skip lc rc).code {machine with stack := tail} =
        if a = skip then .ok ({machine with stack := tail}.push (.val (bword skip))) 0
        else run rc.code {machine with stack := tail} := by
  intro tail
  obtain ⟨word,wordRep,leftRun⟩ := value_success_tail lc represented evaluated tail
  have canonical : word = .val (bword a) := wordRep
  subst word
  refine ⟨leftRun,?_⟩
  by_cases stopped : a = skip
  · have wholeSource : (expression skip left right).evalT state = .ok skip := by
      rw [source skip left right state a evaluated,if_pos stopped]
    obtain ⟨word,repr,target⟩ :=
      value_success_tail (compiled skip lc rc) represented wholeSource tail
    have wordEq : word = .val (bword skip) := repr
    subst word
    rw [if_pos stopped]
    exact target
  · rw [if_neg stopped]
    rcases rc.cert.correct (represented.stack tail) with
      ⟨value,word,valueRun,repr,target⟩ | ⟨failed,target⟩
    · have wholeSource : (expression skip left right).evalT state = .ok value := by
        rw [source skip left right state a evaluated,if_neg stopped,valueRun]
      obtain ⟨wholeWord,wholeRep,wholeRun⟩ :=
        value_success_tail (compiled skip lc rc) represented wholeSource tail
      have rightEq : word = .val (bword value) := repr
      have wholeEq : wholeWord = .val (bword value) := wholeRep
      rw [wholeRun,target,rightEq,wholeEq]
    · have wholeSource : (expression skip left right).evalT state = .error .revert := by
        rw [source skip left right state a evaluated,if_neg stopped,failed]
      rw [(value_revert_iff (compiled skip lc rc) represented tail).mpr wholeSource,target]

theorem revert_iff {b L frame : Nat} {F : Frag Γ} (skip : Bool)
    {left right : Val C Γ .bool} (lc : CompiledVal b F left) (rc : CompiledVal b F right)
    {state : State C Γ} {base : Nat → Fin W} {machine : Machine}
    (represented : StateRepr L b frame F state base machine) (tail : List Word) :
    run (compiled skip lc rc).code {machine with stack := tail} = .revert ↔
      left.evalT state = .error .revert ∨
      ∃ a, left.evalT state = .ok a ∧ a ≠ skip ∧ right.evalT state = .error .revert := by
  rcases lc.cert.correct (represented.stack tail) with
    ⟨a,word,ha,repr,leftRun⟩ | ⟨leftFailed,leftTarget⟩
  · have whole := (execution skip lc rc represented a ha tail).2
    constructor
    · intro failed
      by_cases stopped : a = skip
      · rw [if_pos stopped] at whole
        rw [whole] at failed
        cases failed
      · rw [if_neg stopped] at whole
        exact .inr ⟨a,ha,stopped,(value_revert_iff rc represented tail).mp (whole.symm.trans failed)⟩
    · rintro (immediate | ⟨actual,evaluated,notStopped,failed⟩)
      · rw [ha] at immediate
        cases immediate
      · have same : actual = a := Except.ok.inj (evaluated.symm.trans ha)
        subst actual
        rw [whole,if_neg notStopped]
        exact (value_revert_iff rc represented tail).mpr failed
  · have wholeSource : (expression skip left right).evalT state = .error .revert := by
      cases skip <;> simp only [expression,Bool.false_eq_true,ite_false,ite_true,
        Val.evalT,leftFailed,bind,Except.bind]
    have wholeTarget : run (compiled skip lc rc).code {machine with stack := tail} = .revert :=
      (value_revert_iff (compiled skip lc rc) represented tail).mpr wholeSource
    exact ⟨fun _ => .inl leftFailed,fun _ => wholeTarget⟩

end Solidity.Backend.Passes.ShortCircuitBoundary
/-- info: 'Solidity.Backend.Passes.ShortCircuitBoundary.source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.ShortCircuitBoundary.source
/-- info: 'Solidity.Backend.Passes.ShortCircuitBoundary.execution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.ShortCircuitBoundary.execution
/-- info: 'Solidity.Backend.Passes.ShortCircuitBoundary.revert_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Backend.Passes.ShortCircuitBoundary.revert_iff
