import Solidity.Yul.WordUpdates
import Solidity.Yul.ClosedHorizon
import Solidity.Update

/-! Closed-word dynamic logic over the ACTUAL evaluator. Formula/term/program
contexts stay intrinsic. This is a Lean-only Yul extension, not a SolKey taclet,
Source dirty-word embedding, or full Y09 coverage. The box quantifies over
completed horizons; the diamond requires a concrete completion. -/
namespace Solidity.Yul.Logic
open Solidity.Yul.Closed
open Solidity (Modality)

structure Model (F : List Sig) where
  environment : FunctionEnv F
  words : EnvWordP environment

structure Term (F : List Sig) (n r : Nat) where
  code : Expr F [] n r
  words : ExprWordP code

structure Program (F : List Sig) (control : Control) (n : Nat) where
  code : Stmt F [] control n
  words : StmtWordP code

def Program.skip {F c n} : Program F c n := ⟨.skip, True.intro⟩

def Program.literalAssignment {F c n} (target : Fin n) (value : Word) : Program F c n :=
  ⟨.assign (fun _ : Fin 1 => .local target) (.literal value),
    (WordStmtD.assign WordExprD.literal).profile⟩

def Program.pureAssignment {F c n a} (target : Fin n) (op : Pure a) (inputs : Values a) :
    Program F c n :=
  ⟨.assign (fun _ : Fin 1 => .local target)
      (.builtin (.pure op) (fun i => .literal (inputs i))),
    (WordStmtD.assign (WordExprD.builtin (.pure op) (fun _ => .literal))).profile⟩


def Program.leave {F loop n} : Program F ⟨true,loop⟩ n := ⟨.leave, True.intro⟩
def Program.break_ {F fn n} : Program F ⟨fn,true⟩ n := ⟨.break_, True.intro⟩
def Program.continue_ {F fn n} : Program F ⟨fn,true⟩ n := ⟨.continue_, True.intro⟩

def Model.group {F} (model : Model F) (signatures : List Sig)
    (bodies : Bodies (signatures ++ F) [] signatures) (words : BodiesWordP bodies) :
    Model (signatures ++ F) :=
  ⟨.group signatures model.environment bodies, ⟨model.words, words⟩⟩

def Program.functions {F c n} (signatures : List Sig)
    (bodies : Bodies (signatures ++ F) [] signatures) (words : BodiesWordP bodies)
    (rest : Program (signatures ++ F) c n) : Program F c n :=
  ⟨.functions signatures bodies rest.code, ⟨words,rest.words⟩⟩

/-- Predicates read exactly the indexed word context; modal postconditions can
distinguish every legal control transfer. Only closed word contexts occur;
Source/world observations are outside this logic. -/
inductive Fml : Nat → Type where
  | atom {n} (predicate : Values n → Prop) : Fml n
  | and_ {n} : Fml n → Fml n → Fml n
  | implies {n} : Fml n → Fml n → Fml n
  | subst {n m} : (Values n → Values m) → Fml m → Fml n
  | modal {n F c} (mode : Modality) : Model F → Program F c n →
      (Flow c → Fml n) → Fml n
  | feed {n r} : (Values n → Values r) → (Values r → Fml n) → Fml n
  | termModal {n F r} (mode : Modality) : Model F → Term F n r →
      (Values r → Fml n) → Fml n
  | loopModal {n F} (control : Control) (mode : Modality) : Model F → Term F n 1 →
      Program F ⟨control.function,false⟩ n → Program F ⟨control.function,true⟩ n →
      (Flow control → Fml n) → Fml n

def Fml.holds {n} (formula : Fml n) : Values n → Prop := by
  apply Fml.rec (motive := fun n _ => Values n → Prop) (t := formula)
  case atom => intro n predicate; exact predicate
  case and_ => intro n first second hf hs; exact fun vars => hf vars ∧ hs vars
  case implies => intro n first second hf hs; exact fun vars => hf vars → hs vars
  case subst => intro n m update post ih; exact fun vars => ih (update vars)
  case modal =>
    intro n F c mode model program post ih
    exact fun vars => match mode with
      | .box => ∀ fuel result,
          evalStmt fuel model.environment model.words program.code program.words vars = some result →
            ih result.flow result.vars
      | .diamond => ∃ fuel result,
          evalStmt fuel model.environment model.words program.code program.words vars = some result ∧
            ih result.flow result.vars

  case feed =>
    intro n r read post ih
    exact fun vars => ih (read vars) vars

  case termModal =>
    intro n F r mode model term post ih
    exact fun vars => match mode with
      | .box => ∀ fuel result,
          evalExpr fuel model.environment model.words term.code term.words vars = some result →
            ih result vars
      | .diamond => ∃ fuel result,
          evalExpr fuel model.environment model.words term.code term.words vars = some result ∧
            ih result vars

  case loopModal =>
    intro n F control mode model condition step body post ih
    exact fun vars => match mode with
      | .box => ∀ fuel result,
          evalLoop fuel model.environment model.words condition.code condition.words
            step.code step.words body.code body.words vars = some result →
              ih result.flow result.vars
      | .diamond => ∃ fuel result,
          evalLoop fuel model.environment model.words condition.code condition.words
            step.code step.words body.code body.words vars = some result ∧
              ih result.flow result.vars

/-- Completed-result uniqueness is the ACTUAL closed horizon theorem. The
completion hypothesis is real; concrete assignment rules below discharge it. -/
theorem modal_completed {F c n fuel} (mode : Modality) (model : Model F)
    (program : Program F c n) (post : Flow c → Fml n) (vars : Values n)
    (result : Outcome c n)
    (completed : evalStmt fuel model.environment model.words program.code program.words vars = some result) :
    (Fml.modal mode model program post).holds vars ↔
      (post result.flow).holds result.vars := by
  cases mode with
  | box =>
    constructor
    · intro all
      exact all fuel result completed
    · intro after other actual ran
      have same := evalStmt_completed_unique model.environment model.words program.code
        program.words vars completed ran
      cases same
      exact after
  | diamond =>
    constructor
    · rintro ⟨other, actual, ran, after⟩
      have same := evalStmt_completed_unique model.environment model.words program.code
        program.words vars completed ran
      cases same
      exact after
    · intro after
      exact ⟨fuel, result, completed, after⟩


/-- Opening a whole function group keeps the actual lexical closure environment,
including recursive/mutual calls. It consumes one horizon step, not a proof
assumption about function results or termination. -/
theorem modal_functions {F c n} (mode : Modality) (model : Model F)
    (signatures : List Sig) (bodies : Bodies (signatures ++ F) [] signatures)
    (words : BodiesWordP bodies) (rest : Program (signatures ++ F) c n)
    (post : Flow c → Fml n) (vars : Values n) :
    (Fml.modal mode model (Program.functions signatures bodies words rest) post).holds vars ↔
      (Fml.modal mode (model.group signatures bodies words) rest post).holds vars := by
  cases mode with
  | box =>
    constructor
    · intro all fuel result ran
      exact all (fuel+1) result ran
    · intro all fuel result ran
      cases fuel with
      | zero => cases ran
      | succ fuel => exact all fuel result ran
  | diamond =>
    constructor
    · rintro ⟨fuel,result,ran,after⟩
      cases fuel with
      | zero => cases ran
      | succ fuel => exact ⟨fuel,result,ran,after⟩
    · rintro ⟨fuel,result,ran,after⟩
      exact ⟨fuel+1,result,ran,after⟩


def Program.sequence {F c n} (first second : Program F c n) : Program F c n :=
  ⟨.seq first.code second.code, ⟨first.words,second.words⟩⟩

def sequencePost {F c n} (mode : Modality) (model : Model F) (second : Program F c n)
    (post : Flow c → Fml n) : Flow c → Fml n
  | .normal => .modal mode model second post
  | flow => post flow

theorem eval_sequence (fuel : Nat) {F c n} (model : Model F)
    (first second : Program F c n) (vars : Values n) :
    evalStmt (fuel+1) model.environment model.words (first.sequence second).code
      (first.sequence second).words vars =
      (do let result ← evalStmt fuel model.environment model.words first.code first.words vars
          match result.flow with
          | .normal => evalStmt fuel model.environment model.words second.code second.words result.vars
          | _ => some result) := rfl

theorem sequence_normal {F c n lo hi} (model : Model F) (first second : Program F c n)
    (vars middle : Values n) (result : Outcome c n)
    (one : evalStmt lo model.environment model.words first.code first.words vars = some ⟨middle,.normal⟩)
    (two : evalStmt hi model.environment model.words second.code second.words middle = some result) :
    evalStmt (max lo hi+1) model.environment model.words (first.sequence second).code
      (first.sequence second).words vars = some result := by
  rw [eval_sequence, evalStmt_stable (Nat.le_max_left lo hi)
    model.environment model.words first.code first.words vars one]
  exact evalStmt_stable (Nat.le_max_right lo hi)
    model.environment model.words second.code second.words middle two

theorem sequence_transfer {F c n fuel} (model : Model F) (first second : Program F c n)
    (vars : Values n) (result : Outcome c n)
    (one : evalStmt fuel model.environment model.words first.code first.words vars = some result)
    (transfer : result.flow.isNormal = false) :
    evalStmt (fuel+1) model.environment model.words (first.sequence second).code
      (first.sequence second).words vars = some result := by
  rw [eval_sequence, one]
  rcases result with ⟨middle,flow⟩
  cases flow <;> first | rfl | cases transfer

/-- General sequence composition preserves nonlocal control and synchronizes
actual horizons by max/stability. Neither component is assumed to terminate. -/
theorem modal_sequence {F c n} (mode : Modality) (model : Model F)
    (first second : Program F c n) (post : Flow c → Fml n) (vars : Values n) :
    (Fml.modal mode model (first.sequence second) post).holds vars ↔
      (Fml.modal mode model first (sequencePost mode model second post)).holds vars := by
  cases mode with
  | box =>
    constructor
    · intro all fuel mid ran
      rcases mid with ⟨middle,flow⟩
      cases flow with
      | normal =>
        intro nextFuel result next
        exact all (max fuel nextFuel+1) result (sequence_normal model first second vars middle result ran next)
      | leave_ proof => exact all (fuel+1) _ (sequence_transfer model first second vars _ ran rfl)
      | break_ proof => exact all (fuel+1) _ (sequence_transfer model first second vars _ ran rfl)
      | continue_ proof => exact all (fuel+1) _ (sequence_transfer model first second vars _ ran rfl)
    · intro all fuel result ran
      cases fuel with
      | zero => cases ran
      | succ fuel =>
        rw [eval_sequence] at ran
        cases firstRun : evalStmt fuel model.environment model.words first.code first.words vars with
        | none => rw [firstRun] at ran; cases ran
        | some mid =>
          rw [firstRun] at ran
          have after := all fuel mid firstRun
          rcases mid with ⟨middle,flow⟩
          cases flow with
          | normal => exact after fuel result ran
          | leave_ proof => cases Option.some.inj ran; exact after
          | break_ proof => cases Option.some.inj ran; exact after
          | continue_ proof => cases Option.some.inj ran; exact after
  | diamond =>
    constructor
    · rintro ⟨fuel,result,ran,done⟩
      cases fuel with
      | zero => cases ran
      | succ fuel =>
        rw [eval_sequence] at ran
        cases firstRun : evalStmt fuel model.environment model.words first.code first.words vars with
        | none => rw [firstRun] at ran; cases ran
        | some mid =>
          rw [firstRun] at ran
          refine ⟨fuel,mid,firstRun,?_⟩
          rcases mid with ⟨middle,flow⟩
          cases flow with
          | normal => exact ⟨fuel,result,ran,done⟩
          | leave_ proof => cases Option.some.inj ran; exact done
          | break_ proof => cases Option.some.inj ran; exact done
          | continue_ proof => cases Option.some.inj ran; exact done
    · rintro ⟨fuel,mid,ran,after⟩
      rcases mid with ⟨middle,flow⟩
      cases flow with
      | normal =>
        rcases after with ⟨nextFuel,result,next,done⟩
        exact ⟨max fuel nextFuel+1,result,
          sequence_normal model first second vars middle result ran next,done⟩
      | leave_ proof => exact ⟨fuel+1,_,sequence_transfer model first second vars _ ran rfl,after⟩
      | break_ proof => exact ⟨fuel+1,_,sequence_transfer model first second vars _ ran rfl,after⟩
      | continue_ proof => exact ⟨fuel+1,_,sequence_transfer model first second vars _ ran rfl,after⟩

end Solidity.Yul.Logic
