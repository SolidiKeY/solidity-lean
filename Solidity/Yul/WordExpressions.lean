import Solidity.Yul.WordArguments

/-! Closed expression reductions over actual words and lexical functions.
Feed preserves caller words while passing typed values to the postcondition. -/
namespace Solidity.Yul.Logic
open Solidity.Yul.Closed
open Solidity (Modality)

def Term.literal {F n} (value : Word) : Term F n 1 := ⟨.literal value,True.intro⟩
def Term.readLocal {F n} (position : Fin n) : Term F n 1 := ⟨.local position,True.intro⟩

def Term.builtin {F n a r} {builtin : Builtin a r} (admitted : WordBuiltinD builtin)
    (args : Fin a → Term F n 1) : Term F n r :=
  ⟨.builtin builtin (fun i => (args i).code),
    ⟨by rw [admitted.complete]; rfl,fun i => (args i).words⟩⟩

def Term.call {F n sig} (function : Member F sig) (args : Fin sig.args → Term F n 1) :
    Term F n sig.rets :=
  ⟨.call function (fun i => (args i).code),fun i => (args i).words⟩

theorem modal_literal {F n} (mode : Modality) (model : Model F) (value : Word)
    (post : Values 1 → Fml n) (vars : Values n) :
    (Fml.termModal mode model (Term.literal value) post).holds vars ↔
      (post (fun _ => value)).holds vars :=
  term_completed mode model (Term.literal value) post vars (fun _ => value) (fuel := 1) rfl

theorem modal_local {F n} (mode : Modality) (model : Model F) (position : Fin n)
    (post : Values 1 → Fml n) (vars : Values n) :
    (Fml.termModal mode model (Term.readLocal position) post).holds vars ↔
      (Fml.feed (fun vars => fun _ : Fin 1 => vars position) post).holds vars :=
  term_completed mode model (Term.readLocal position) post vars (fun _ => vars position) (fuel := 1) rfl

theorem eval_builtin_term (fuel : Nat) {F n a r} (model : Model F) {builtin : Builtin a r}
    (admitted : WordBuiltinD builtin) (args : Fin a → Term F n 1) (vars : Values n) :
    evalExpr (fuel+1) model.environment model.words (Term.builtin admitted args).code
      (Term.builtin admitted args).words vars =
      (evalArgs fuel model a args vars).map admitted.eval := by
  rw [Option.map_eq_bind]
  cases admitted <;> rfl

/-- Arbitrary typed operands, not only literals. Both modalities agree with
right-to-left operand formulas, with no caller-completion premise. -/
theorem modal_builtin {F n a r} (mode : Modality) (model : Model F) {builtin : Builtin a r}
    (admitted : WordBuiltinD builtin) (args : Fin a → Term F n 1)
    (post : Values r → Fml n) (vars : Values n) :
    (Fml.termModal mode model (Term.builtin admitted args) post).holds vars ↔
      (argsModal mode model a args (fun inputs => post (admitted.eval inputs))).holds vars := by
  apply Iff.trans ?_ (args_modal_iff a mode model vars args (fun inputs => post (admitted.eval inputs)))
  cases mode with
  | box =>
    constructor
    · intro all fuel inputs ran
      exact all (fuel+1) (admitted.eval inputs) (by rw [eval_builtin_term,ran]; rfl)
    · intro all fuel result ran
      cases fuel with
      | zero => cases ran
      | succ fuel =>
        rw [eval_builtin_term] at ran
        cases argsRan : evalArgs fuel model a args vars with
        | none => rw [argsRan] at ran; cases ran
        | some inputs =>
          rw [argsRan] at ran
          cases Option.some.inj ran
          exact all fuel inputs argsRan
  | diamond =>
    constructor
    · rintro ⟨fuel,result,ran,after⟩
      cases fuel with
      | zero => cases ran
      | succ fuel =>
        rw [eval_builtin_term] at ran
        cases argsRan : evalArgs fuel model a args vars with
        | none => rw [argsRan] at ran; cases ran
        | some inputs =>
          rw [argsRan] at ran
          cases Option.some.inj ran
          exact ⟨fuel,inputs,argsRan,after⟩
    · rintro ⟨fuel,inputs,ran,after⟩
      exact ⟨fuel+1,admitted.eval inputs,(by rw [eval_builtin_term,ran]; rfl),after⟩


def calledModel {F sig} (model : Model F) (function : Member F sig) :
    Model (lookup model.environment function).functions :=
  ⟨(lookup model.environment function).environment,
    (lookup_profile model.environment model.words function).1⟩

def calledProgram {F sig} (model : Model F) (function : Member F sig) :
    Program (lookup model.environment function).functions ⟨true,false⟩ (sig.args+sig.rets) :=
  ⟨(lookup model.environment function).body,
    (lookup_profile model.environment model.words function).2⟩

/-- Caller words are saved for the LOGICAL postcondition, not captured by the
callee code. Actual callee locals contain only arguments and zero return slots. -/
def callFrame {F n sig} (mode : Modality) (model : Model F) (function : Member F sig)
    (post : Values sig.rets → Fml n) (inputs : Values sig.args) : Fml n :=
  .feed (fun vars : Values n => vars) (fun caller =>
    .subst (fun _ : Values n => extendValues inputs (fun _ : Fin sig.rets => word 0))
      (.modal mode (calledModel model function) (calledProgram model function) (fun _ =>
        .feed (dropValues sig.args) (fun returned =>
          .subst (fun _ : Values (sig.args+sig.rets) => caller) (post returned)))))

def FrameHolds {F n sig} (mode : Modality) (model : Model F) (function : Member F sig)
    (inputs : Values sig.args) (post : Values sig.rets → Fml n) (vars : Values n) : Prop :=
  match mode with
  | .box => ∀ fuel result,
      evalStmt fuel (calledModel model function).environment (calledModel model function).words
        (calledProgram model function).code (calledProgram model function).words
        (extendValues inputs (fun _ : Fin sig.rets => word 0)) = some result →
          (post (dropValues sig.args result.vars)).holds vars
  | .diamond => ∃ fuel result,
      evalStmt fuel (calledModel model function).environment (calledModel model function).words
        (calledProgram model function).code (calledProgram model function).words
        (extendValues inputs (fun _ : Fin sig.rets => word 0)) = some result ∧
          (post (dropValues sig.args result.vars)).holds vars

theorem callFrame_iff {F n sig} (mode : Modality) (model : Model F) (function : Member F sig)
    (inputs : Values sig.args) (post : Values sig.rets → Fml n) (vars : Values n) :
    (callFrame mode model function post inputs).holds vars ↔
      FrameHolds mode model function inputs post vars := by
  cases mode <;> rfl

theorem eval_call_term (fuel : Nat) {F n sig} (model : Model F) (function : Member F sig)
    (args : Fin sig.args → Term F n 1) (vars : Values n) :
    evalExpr (fuel+1) model.environment model.words (Term.call function args).code
      (Term.call function args).words vars =
    (do let inputs ← evalArgs fuel model sig.args args vars
        let result ← evalStmt fuel (calledModel model function).environment (calledModel model function).words
          (calledProgram model function).code (calledProgram model function).words
          (extendValues inputs (fun _ : Fin sig.rets => word 0))
        pure (dropValues sig.args result.vars)) := rfl

theorem call_completed {F n sig lo hi} (model : Model F) (function : Member F sig)
    (args : Fin sig.args → Term F n 1) (vars : Values n) (inputs : Values sig.args)
    (result : Outcome ⟨true,false⟩ (sig.args+sig.rets))
    (arguments : evalArgs lo model sig.args args vars = some inputs)
    (bodyRan : evalStmt hi (calledModel model function).environment (calledModel model function).words
      (calledProgram model function).code (calledProgram model function).words
      (extendValues inputs (fun _ : Fin sig.rets => word 0)) = some result) :
    evalExpr (max lo hi+1) model.environment model.words (Term.call function args).code
      (Term.call function args).words vars = some (dropValues sig.args result.vars) := by
  rw [eval_call_term,evalArgs_stable (Nat.le_max_left lo hi) model sig.args args vars arguments]
  change (do let actual ← evalStmt (max lo hi)
              (calledModel model function).environment (calledModel model function).words
              (calledProgram model function).code (calledProgram model function).words
              (extendValues inputs (fun _ : Fin sig.rets => word 0))
             pure (dropValues sig.args actual.vars)) = _
  rw [evalStmt_stable (Nat.le_max_right lo hi)
    (calledModel model function).environment (calledModel model function).words
    (calledProgram model function).code (calledProgram model function).words
    (extendValues inputs (fun _ : Fin sig.rets => word 0)) bodyRan]
  rfl

/-- Arguments and actual lexical body runs compose at synchronized horizons.
The final call rule has no caller-success or callee-termination premise. -/
theorem modal_call {F n sig} (mode : Modality) (model : Model F) (function : Member F sig)
    (args : Fin sig.args → Term F n 1) (post : Values sig.rets → Fml n) (vars : Values n) :
    (Fml.termModal mode model (Term.call function args) post).holds vars ↔
      (argsModal mode model sig.args args (callFrame mode model function post)).holds vars := by
  apply Iff.trans ?_ (args_modal_iff sig.args mode model vars args (callFrame mode model function post))
  cases mode with
  | box =>
    constructor
    · intro all lo inputs arguments
      apply (callFrame_iff .box model function inputs post vars).mpr
      intro hi result bodyRan
      exact all (max lo hi+1) _ (call_completed model function args vars inputs result arguments bodyRan)
    · intro all fuel result ran
      cases fuel with
      | zero => cases ran
      | succ fuel =>
        rw [eval_call_term] at ran
        cases arguments : evalArgs fuel model sig.args args vars with
        | none => rw [arguments] at ran; cases ran
        | some inputs =>
          rw [arguments] at ran
          change (do let actual ← evalStmt fuel
                      (calledModel model function).environment (calledModel model function).words
                      (calledProgram model function).code (calledProgram model function).words
                      (extendValues inputs (fun _ : Fin sig.rets => word 0))
                     pure (dropValues sig.args actual.vars)) = _ at ran
          cases bodyRan : evalStmt fuel
            (calledModel model function).environment (calledModel model function).words
            (calledProgram model function).code (calledProgram model function).words
            (extendValues inputs (fun _ : Fin sig.rets => word 0)) with
          | none => rw [bodyRan] at ran; cases ran
          | some actual =>
            rw [bodyRan] at ran
            cases Option.some.inj ran
            exact ((callFrame_iff .box model function inputs post vars).mp (all fuel inputs arguments))
              fuel actual bodyRan
  | diamond =>
    constructor
    · rintro ⟨fuel,result,ran,after⟩
      cases fuel with
      | zero => cases ran
      | succ fuel =>
        rw [eval_call_term] at ran
        cases arguments : evalArgs fuel model sig.args args vars with
        | none => rw [arguments] at ran; cases ran
        | some inputs =>
          rw [arguments] at ran
          change (do let actual ← evalStmt fuel
                      (calledModel model function).environment (calledModel model function).words
                      (calledProgram model function).code (calledProgram model function).words
                      (extendValues inputs (fun _ : Fin sig.rets => word 0))
                     pure (dropValues sig.args actual.vars)) = _ at ran
          cases bodyRan : evalStmt fuel
            (calledModel model function).environment (calledModel model function).words
            (calledProgram model function).code (calledProgram model function).words
            (extendValues inputs (fun _ : Fin sig.rets => word 0)) with
          | none => rw [bodyRan] at ran; cases ran
          | some actual =>
            rw [bodyRan] at ran
            cases Option.some.inj ran
            refine ⟨fuel,inputs,arguments,?_⟩
            exact (callFrame_iff .diamond model function inputs post vars).mpr ⟨fuel,actual,bodyRan,after⟩
    · rintro ⟨lo,inputs,arguments,frame⟩
      rcases (callFrame_iff .diamond model function inputs post vars).mp frame with ⟨hi,result,bodyRan,after⟩
      exact ⟨max lo hi+1,_,call_completed model function args vars inputs result arguments bodyRan,after⟩


/-- Finite frame witnesses may use this helper; the unconditional modal_call
proof above does not assume a body result or use this completion premise. -/
theorem frame_completed {F n sig fuel} (mode : Modality) (model : Model F) (function : Member F sig)
    (inputs : Values sig.args) (post : Values sig.rets → Fml n) (vars : Values n)
    (result : Outcome ⟨true,false⟩ (sig.args+sig.rets))
    (done : evalStmt fuel (calledModel model function).environment (calledModel model function).words
      (calledProgram model function).code (calledProgram model function).words
      (extendValues inputs (fun _ : Fin sig.rets => word 0)) = some result) :
    (callFrame mode model function post inputs).holds vars ↔
      (post (dropValues sig.args result.vars)).holds vars := by
  rw [callFrame_iff]
  cases mode with
  | box =>
    constructor
    · intro all; exact all fuel result done
    · intro after other actual ran
      have same := evalStmt_completed_unique (calledModel model function).environment
        (calledModel model function).words (calledProgram model function).code (calledProgram model function).words
        (extendValues inputs (fun _ : Fin sig.rets => word 0)) done ran
      cases same
      exact after
  | diamond =>
    constructor
    · rintro ⟨other,actual,ran,after⟩
      have same := evalStmt_completed_unique (calledModel model function).environment
        (calledModel model function).words (calledProgram model function).code (calledProgram model function).words
        (extendValues inputs (fun _ : Fin sig.rets => word 0)) done ran
      cases same
      exact after
    · intro after; exact ⟨fuel,result,done,after⟩

end Solidity.Yul.Logic
