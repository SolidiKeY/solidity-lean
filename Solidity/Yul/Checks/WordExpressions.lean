import Solidity.Yul.WordCoverage
import Solidity.Yul.Checks.WordTerms
import Solidity.Yul.Checks.ClosedRun
namespace Solidity.Yul.Checks.WordExpressions
open Solidity.Yul.Closed Solidity.Yul.Logic
open Solidity (Modality)
open scoped Solidity.Yul.Logic

def feed : Nat := 13
example : feed = 13 := rfl
def caller : Values 3 := fun i => if i=0 then word 257 else if i=1 then word 2 else word (2^256-1)
def empty : Model [] := ⟨.nil,True.intro⟩
example (mode : Modality) :
    (Fml.termModal mode empty (Term.readLocal 0)
      (fun values => .atom fun vars => values 0 = word 257 ∧ vars = caller)).holds caller := by
  apply (Rule.sound (.yulLocal mode empty 0 _) caller).mpr
  exact ⟨rfl,rfl⟩
example (mode : Modality) :
    ¬ (Fml.termModal mode empty (Term.readLocal 0)
      (fun values => .atom fun _ => values 0 = word 1)).holds caller := by
  intro actual
  have wrong := (Rule.sound (.yulLocal mode empty 0 _) caller).mp actual
  exact (by decide : word 257 ≠ word 1) wrong
example (mode : Modality) :
    (Fml.termModal mode empty (Term.literal (word (2^256-1)))
      (fun values => .atom fun vars => values 0 = word (2^256-1) ∧ vars = caller)).holds caller :=
  (Rule.sound (.yulLiteral mode empty (word (2^256-1)) _) caller).mpr ⟨rfl,rfl⟩

/-- All26 pure operations accept arbitrary raw local operands without cleaning. -/
example {arity} (mode : Modality) (op : Pure arity) (inputs : Values arity) :
    (Fml.termModal mode empty (Term.builtin (.pure op) (fun i => Term.readLocal i))
      (fun values => .atom fun vars => values 0 = op.eval inputs ∧ vars = inputs)).holds inputs := by
  have done : evalArgs 1 empty arity (fun i => Term.readLocal i) inputs = some inputs := by
    change collectValues arity (fun i => some (inputs i)) = some inputs
    exact collectValues_allSome arity inputs
  apply (term_completed mode empty (Term.builtin (.pure op) (fun i => Term.readLocal i)) _ inputs
    (fun _ => op.eval inputs) (fuel := 2) ?_).mpr
  · exact ⟨rfl,rfl⟩
  · rw [eval_builtin_term,done]
    rfl

abbrev sig : Sig := ⟨0,1⟩
def oldCaller : Stmt [sig,sig] [] ⟨true,false⟩ 1 :=
  .assign (fun _ => .local 0) (.call (.there .here) Fin.elim0)
def oldCallerD : WordStmtD oldCaller := .assign (.call (.there .here) (fun i => Fin.elim0 i))
def oldHelper : Stmt [sig,sig] [] ⟨true,false⟩ 1 := .assign (fun _ => .local 0) (.literal (word 7))
def oldHelperD : WordStmtD oldHelper := .assign .literal
def older : FunctionEnv [sig,sig] := .group [sig,sig] .nil (.cons oldCaller (.cons oldHelper .nil))
def olderD : WordEnvD older := .group .nil (.cons oldCallerD (.cons oldHelperD .nil))
def newerBody : Stmt [sig,sig,sig] [] ⟨true,false⟩ 1 := .assign (fun _ => .local 0) (.literal (word 99))
def newerBodyD : WordStmtD newerBody := .assign .literal
def newer : FunctionEnv [sig,sig,sig] := .group [sig] older (.cons newerBody .nil)
def newerD : WordEnvD newer := .group olderD (.cons newerBodyD .nil)
def lexical : Model [sig,sig,sig] := ⟨newer,newerD.profile⟩
def oldFunction : Member [sig,sig,sig] sig := .there .here
example : (calledModel lexical oldFunction).environment = older := rfl
example : (calledProgram lexical oldFunction).code = oldCaller := rfl
example : (calledModel lexical (.here : Member [sig,sig,sig] sig)).environment = newer := rfl
def oldResult : Outcome ⟨true,false⟩ 1 :=
  (evalStmt 6 (calledModel lexical oldFunction).environment (calledModel lexical oldFunction).words
    (calledProgram lexical oldFunction).code (calledProgram lexical oldFunction).words
    (extendValues Fin.elim0 (fun _ : Fin 1 => word 0))).get (by decide)
theorem oldDone :
    evalStmt 6 (calledModel lexical oldFunction).environment (calledModel lexical oldFunction).words
      (calledProgram lexical oldFunction).code (calledProgram lexical oldFunction).words
      (extendValues Fin.elim0 (fun _ : Fin 1 => word 0)) = some oldResult :=
  (Option.some_get (by decide)).symm
example (mode : Modality) :
    (Fml.termModal mode lexical (Term.call oldFunction Fin.elim0)
      (fun values => .atom fun vars => values 0 = word 7 ∧ vars = caller)).holds caller := by
  apply (Rule.sound (.yulCall mode lexical oldFunction Fin.elim0 _) caller).mpr
  apply (frame_completed mode lexical oldFunction Fin.elim0 _ caller oldResult (fuel := 6) oldDone).mpr
  exact ⟨by decide,rfl⟩
def newestTerm : Term [sig,sig,sig] 3 1 := Term.call .here Fin.elim0
example : (evalExpr 7 lexical.environment lexical.words (Term.call oldFunction Fin.elim0 (n := 3)).code
    (Term.call oldFunction Fin.elim0 (n := 3)).words caller).map (fun values => (values 0).val) = some 7 := by decide
example : (evalExpr 7 lexical.environment lexical.words newestTerm.code
    newestTerm.words caller).map (fun values => (values 0).val) = some 99 := by decide

abbrev multiSig : Sig := ⟨2,3⟩
def multiBody : Stmt [multiSig] [] ⟨true,false⟩ 5 :=
  .seq (.assign (fun _ => .local 2) (.local 1))
    (.seq (.assign (fun _ => .local 3) (.local 0))
      (.seq .leave (.assign (fun _ => .local 4) (.literal (word 99)))))
def multiBodyD : WordStmtD multiBody :=
  .seq (.assign (.local 1)) (.seq (.assign (.local 0)) (.seq .leave (.assign .literal)))
def multiEnv : FunctionEnv [multiSig] := .group [multiSig] .nil (.cons multiBody .nil)
def multiEnvD : WordEnvD multiEnv := .group .nil (.cons multiBodyD .nil)
def multi : Model [multiSig] := ⟨multiEnv,multiEnvD.profile⟩
def multiPost (inputs : Values 2) (original : Values 3) (returned : Values 3) : Solidity.Yul.Logic.Fml 3 :=
  .atom fun vars => returned 0 = inputs 1 ∧ returned 1 = inputs 0 ∧ returned 2 = word 0 ∧ vars = original
def multiResult (inputs : Values 2) : Outcome ⟨true,false⟩ 5 :=
  (evalStmt 8 (calledModel multi .here).environment (calledModel multi .here).words
    (calledProgram multi .here).code (calledProgram multi .here).words
    (extendValues inputs (fun _ : Fin 3 => word 0))).get (by rfl)
theorem multiDone (inputs : Values 2) :
    evalStmt 8 (calledModel multi .here).environment (calledModel multi .here).words
      (calledProgram multi .here).code (calledProgram multi .here).words
      (extendValues inputs (fun _ : Fin 3 => word 0)) = some (multiResult inputs) :=
  (Option.some_get (by rfl)).symm
example (inputs : Values 2) : (multiResult inputs).flow = .leave_ rfl := rfl
theorem multiFrame (mode : Modality) (inputs : Values 2) (original : Values 3) :
    (callFrame mode multi .here (multiPost inputs original) inputs).holds original := by
  apply (frame_completed mode multi .here _ _ original (multiResult inputs) (fuel := 8) (multiDone inputs)).mpr
  exact ⟨rfl,rfl,rfl,rfl⟩

def simpleArgs : Fin 2 → Term [multiSig] 3 1 := fun i =>
  if i=0 then Term.readLocal 0 else Term.readLocal 1
def simpleInputs : Values 2 := appendArg (word 2) (appendArg (word 257) Fin.elim0)
def simpleTerm : Term [multiSig] 3 3 := Term.call .here simpleArgs
example (mode : Modality) :
    (Fml.termModal mode multi simpleTerm (multiPost simpleInputs caller)).holds caller := by
  apply (Rule.sound (.yulCall mode multi .here simpleArgs _) caller).mpr
  change (Fml.termModal mode multi (Term.readLocal 1) _).holds caller
  apply (Rule.sound (.yulLocal mode multi 1 _) caller).mpr
  change (Fml.termModal mode multi (Term.readLocal 0)
    (fun first => callFrame mode multi .here (multiPost simpleInputs caller)
      (appendArg (word 2) (appendArg (first 0) Fin.elim0)))).holds caller
  apply (Rule.sound (.yulLocal mode multi 0 _) caller).mpr
  exact multiFrame mode simpleInputs caller
example : (evalExpr 10 multi.environment multi.words simpleTerm.code
    simpleTerm.words caller).map
    (fun values => ((values 0).val,(values 1).val,(values 2).val)) = some (2,257,0) := by decide

/-- Noncommutative nested operand plus literal: genuinely different horizons. -/
def mixedArgs : Fin 2 → Term [multiSig] 3 1 := fun i =>
  if i=0 then Term.builtin (.pure .sub) (fun j => Term.readLocal j.castSucc)
  else Term.literal (word 17)
def mixedTerm : Term [multiSig] 3 3 := Term.call .here mixedArgs
def mixedInputs : Values 2 := (evalArgs 2 multi 2 mixedArgs caller).get (by decide)
theorem mixedDone : evalArgs 2 multi 2 mixedArgs caller = some mixedInputs :=
  (Option.some_get (by decide)).symm
example : (evalArgs 1 multi 2 mixedArgs caller).isNone = true := by decide
example : (mixedInputs 0).val = 255 := by decide
example : (mixedInputs 1).val = 17 := by decide
example (mode : Modality) :
    (Fml.termModal mode multi mixedTerm (multiPost mixedInputs caller)).holds caller := by
  apply (Rule.sound (.yulCall mode multi .here mixedArgs _) caller).mpr
  apply (args_modal_iff 2 mode multi caller mixedArgs _).mp
  cases mode with
  | box =>
    intro fuel inputs ran
    have one := evalArgs_stable (Nat.le_max_left 2 fuel) multi 2 mixedArgs caller mixedDone
    have two := evalArgs_stable (Nat.le_max_right 2 fuel) multi 2 mixedArgs caller ran
    have same := Option.some.inj (one.symm.trans two)
    cases same
    exact multiFrame .box mixedInputs caller
  | diamond => exact ⟨2,mixedInputs,mixedDone,multiFrame .diamond mixedInputs caller⟩
example : (evalExpr 12 multi.environment multi.words mixedTerm.code
    mixedTerm.words caller).map
    (fun values => ((values 0).val,(values 1).val,(values 2).val)) = some (17,255,0) := by decide

def voidModel : Model [ClosedRun.divergeSig] := ⟨ClosedRun.voidEnv,ClosedRun.voidEnvD.profile⟩
def voidResult : Outcome ⟨true,false⟩ 0 :=
  (evalStmt 1 (calledModel voidModel .here).environment (calledModel voidModel .here).words
    (calledProgram voidModel .here).code (calledProgram voidModel .here).words
    (extendValues Fin.elim0 (fun _ : Fin 0 => word 0))).get (by rfl)
theorem voidDone :
    evalStmt 1 (calledModel voidModel .here).environment (calledModel voidModel .here).words
      (calledProgram voidModel .here).code (calledProgram voidModel .here).words
      (extendValues Fin.elim0 (fun _ : Fin 0 => word 0)) = some voidResult :=
  (Option.some_get (by rfl)).symm
example (mode : Modality) :
    (Fml.termModal mode voidModel (Term.call .here Fin.elim0)
      (fun _ => .atom fun vars => vars = caller)).holds caller := by
  apply (Rule.sound (.yulCall mode voidModel .here Fin.elim0 _) caller).mpr
  apply (frame_completed mode voidModel .here Fin.elim0 _ caller voidResult (fuel := 1) voidDone).mpr
  rfl

theorem recursive_body_none (fuel : Nat) (vars : Values 1) :
    evalStmt fuel WordTerms.recursiveEnv WordTerms.recursiveEnvD.profile
      WordTerms.recursiveBody WordTerms.recursiveBodyD.profile vars = none := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
    change Option.bind (evalExpr fuel WordTerms.recursiveEnv WordTerms.recursiveEnvD.profile
      WordTerms.recursiveCall WordTerms.recursiveCallD.profile vars) _ = none
    rw [WordTerms.recursive_all]
    rfl
example : (Fml.termModal .box WordTerms.recursiveModel (Term.call .here Fin.elim0)
    (fun _ => .atom fun _ => False)).holds (caller : Values 3) := by
  apply (Rule.sound (.yulCall .box WordTerms.recursiveModel .here Fin.elim0 _) caller).mpr
  apply (callFrame_iff .box WordTerms.recursiveModel .here Fin.elim0 _ caller).mpr
  intro fuel result ran
  change evalStmt fuel WordTerms.recursiveEnv WordTerms.recursiveEnvD.profile
    WordTerms.recursiveBody WordTerms.recursiveBodyD.profile
    (extendValues Fin.elim0 (fun _ : Fin 1 => word 0)) = some result at ran
  rw [recursive_body_none] at ran
  cases ran
example : ¬ (Fml.termModal .diamond WordTerms.recursiveModel (Term.call .here Fin.elim0)
    (fun _ => .atom fun _ => True)).holds caller := by
  intro actual
  have frame := (Rule.sound (.yulCall .diamond WordTerms.recursiveModel .here Fin.elim0 _) caller).mp actual
  rcases (callFrame_iff .diamond WordTerms.recursiveModel .here Fin.elim0 _ caller).mp frame with ⟨fuel,result,ran,_⟩
  change evalStmt fuel WordTerms.recursiveEnv WordTerms.recursiveEnvD.profile
    WordTerms.recursiveBody WordTerms.recursiveBodyD.profile
    (extendValues Fin.elim0 (fun _ : Fin 1 => word 0)) = some result at ran
  rw [recursive_body_none] at ran
  cases ran

example (reference : ExternalRef [] false) : False := by cases reference.index
example : (checkWordBuiltin Builtin.mload).isNone = true := rfl
example : ruleIds.length = 20 := ruleIds_count
example {F n r} (mode : Modality) (model : Model F) (term : Term F n r)
    (post : Values r → Solidity.Yul.Logic.Fml n) :
    ∃ premise, Nonempty (Rule (Fml.termModal mode model term post) premise) :=
  term_rule_exists mode model term post


def subtractArgs : Fin 2 → Term [] 3 1 := fun i => Term.readLocal i.castSucc
def subtract : Term [] 3 1 := Term.builtin (.pure .sub) subtractArgs
def subtractPost (values : Values 1) : Solidity.Yul.Logic.Fml 3 :=
  .atom fun vars => values 0 = word 255 ∧ vars = caller
example (mode : Modality) : (Fml.termModal mode empty subtract subtractPost).holds caller := by
  apply (Rule.sound (.yulBuiltin mode empty (.pure .sub) (.pure .sub) subtractArgs subtractPost) caller).mpr
  change (Fml.termModal mode empty (Term.readLocal 1) _).holds caller
  apply (Rule.sound (.yulLocal mode empty 1 _) caller).mpr
  change (Fml.termModal mode empty (Term.readLocal 0)
    (fun first => subtractPost ((WordBuiltinD.pure Pure.sub).eval
      (appendArg (word 2) (appendArg (first 0) Fin.elim0))))).holds caller
  apply (Rule.sound (.yulLocal mode empty 0 _) caller).mpr
  exact ⟨by decide,rfl⟩

def popArgs : Fin 1 → Term [] 3 1 := fun _ => Term.readLocal 0
example (mode : Modality) :
    (Fml.termModal mode empty (Term.builtin WordBuiltinD.pop popArgs)
      (fun _ => .atom fun vars => vars = caller)).holds caller := by
  apply (Rule.sound (.yulBuiltin mode empty .pop .pop popArgs _) caller).mpr
  change (Fml.termModal mode empty (Term.readLocal 0) _).holds caller
  apply (Rule.sound (.yulLocal mode empty 0 _) caller).mpr
  rfl

def signedZeroArgs : Fin 2 → Term [] 3 1 := fun i =>
  if i=0 then Term.readLocal 2 else Term.literal (word 0)
example (mode : Modality) :
    (Fml.termModal mode empty (Term.builtin (.pure .sdiv) signedZeroArgs)
      (fun values => .atom fun vars => values 0 = word 0 ∧ vars = caller)).holds caller := by
  apply (Rule.sound (.yulBuiltin mode empty (.pure .sdiv) (.pure .sdiv) signedZeroArgs _) caller).mpr
  change (Fml.termModal mode empty (Term.literal (word 0)) _).holds caller
  apply (Rule.sound (.yulLiteral mode empty (word 0) _) caller).mpr
  change (Fml.termModal mode empty (Term.readLocal 2) _).holds caller
  apply (Rule.sound (.yulLocal mode empty 2 _) caller).mpr
  exact ⟨rfl,rfl⟩

/-- Either operand can diverge. Universal incompletion is separately proved
from the actual recursive expression, not inferred from one small horizon. -/
def badArgs (position : Fin 2) : Fin 2 → Term [WordTerms.sig] 3 1 := fun i =>
  if i=position then WordTerms.recursiveTerm else Term.literal (word 7)
theorem badArgs_all (position : Fin 2) (fuel : Nat) :
    evalArgs fuel WordTerms.recursiveModel 2 (badArgs position) caller = none := by
  apply evalArgs_none_at fuel WordTerms.recursiveModel (badArgs position) caller position
  simp only [badArgs]
  exact WordTerms.recursive_all fuel caller
theorem badBuiltin_all (position : Fin 2) (fuel : Nat) :
    evalExpr fuel WordTerms.recursiveModel.environment WordTerms.recursiveModel.words
      (Term.builtin (.pure .sub) (badArgs position)).code
      (Term.builtin (.pure .sub) (badArgs position)).words caller = none := by
  cases fuel with
  | zero => rfl
  | succ fuel => rw [eval_builtin_term,badArgs_all]; rfl
example (position : Fin 2) :
    (Fml.termModal .box WordTerms.recursiveModel (Term.builtin (.pure .sub) (badArgs position))
      (fun _ => .atom fun _ => False)).holds caller := by
  apply (Rule.sound (.yulBuiltin .box WordTerms.recursiveModel (.pure .sub) (.pure .sub) (badArgs position) _) caller).mpr
  apply (args_modal_iff 2 .box WordTerms.recursiveModel caller (badArgs position) _).mp
  intro fuel inputs ran
  rw [badArgs_all] at ran
  cases ran
example (position : Fin 2) :
    ¬ (Fml.termModal .diamond WordTerms.recursiveModel (Term.builtin (.pure .sub) (badArgs position))
      (fun _ => .atom fun _ => True)).holds caller := by
  intro actual
  have operands := (Rule.sound (.yulBuiltin .diamond WordTerms.recursiveModel (.pure .sub) (.pure .sub)
    (badArgs position) _) caller).mp actual
  rcases (args_modal_iff 2 .diamond WordTerms.recursiveModel caller (badArgs position) _).mpr operands with
    ⟨fuel,inputs,ran,_⟩
  rw [badArgs_all] at ran
  cases ran

example {n r} (read : Values n → Values r) (post : Values r → Solidity.Yul.Logic.Fml n) :
    (dl{ yul feed read | post }) = Fml.feed read post := rfl

end Solidity.Yul.Checks.WordExpressions
