import Solidity.Yul.WordExpressions

namespace Solidity.Yul.Logic
open Solidity.Yul.Closed
open Solidity (Modality)
open scoped Solidity.Yul.Logic

/-- One constructor per Lean-only rule, parameterized by modality. The
rule-map registration and notation live in their separate extension layer. -/
inductive Rule : {n : Nat} → Fml n → Fml n → Type where
  | yulSkip {F c n} (mode : Modality) (model : Model F) (post : Flow c → Fml n) :
      dl{ yul (dl{ yul mode ; model ; (Program.skip (c := c)) ; post }) ⇝ (post .normal) }
  | yulLocalLiteralAssign {F c n} (mode : Modality) (model : Model F)
      (target : Fin n) (value : Word) (post : Flow c → Fml n) :
      dl{ yul (dl{ yul mode ; model ; (Program.literalAssignment target value) ; post }) ⇝
        (dl{ yul subst (writeTarget (.local target) value) ; (post .normal) }) }
  | yulPureLiteralAssign {F c n a} (mode : Modality) (model : Model F)
      (target : Fin n) (op : Pure a) (inputs : Values a) (post : Flow c → Fml n) :
      dl{ yul (dl{ yul mode ; model ; (Program.pureAssignment target op inputs) ; post }) ⇝
        (dl{ yul subst (writeTarget (.local target) (op.eval inputs)) ; (post .normal) }) }


  | yulLeave {F loop n} (mode : Modality) (model : Model F)
      (post : Flow ⟨true,loop⟩ → Fml n) :
      dl{ yul (dl{ yul mode ; model ; Program.leave ; post }) ⇝ (post (.leave_ rfl)) }
  | yulBreak {F fn n} (mode : Modality) (model : Model F)
      (post : Flow ⟨fn,true⟩ → Fml n) :
      dl{ yul (dl{ yul mode ; model ; Program.break_ ; post }) ⇝ (post (.break_ rfl)) }
  | yulContinue {F fn n} (mode : Modality) (model : Model F)
      (post : Flow ⟨fn,true⟩ → Fml n) :
      dl{ yul (dl{ yul mode ; model ; Program.continue_ ; post }) ⇝ (post (.continue_ rfl)) }
  | yulFunctionScope {F c n} (mode : Modality) (model : Model F)
      (signatures : List Sig) (bodies : Bodies (signatures ++ F) [] signatures)
      (words : BodiesWordP bodies) (rest : Program (signatures ++ F) c n)
      (post : Flow c → Fml n) :
      dl{ yul (dl{ yul mode ; model ; (Program.functions signatures bodies words rest) ; post }) ⇝
        (dl{ yul mode ; (model.group signatures bodies words) ; rest ; post }) }


  | yulSequence {F c n} (mode : Modality) (model : Model F)
      (first second : Program F c n) (post : Flow c → Fml n) :
      dl{ yul (dl{ yul mode ; model ; (first.sequence second) ; post }) ⇝
        (dl{ yul mode ; model ; first ; (sequencePost mode model second post) }) }

  | yulAssign {F c n r} (mode : Modality) (model : Model F)
      (targets : Fin r → Target [] n) (term : Term F n r) (post : Flow c → Fml n) :
      dl{ yul (dl{ yul mode ; model ; (Program.assignment targets term) ; post }) ⇝
        (dl{ yul eval mode ; model ; term => (assignmentPost targets post) }) }
  | yulDiscard {F c n} (mode : Modality) (model : Model F)
      (term : Term F n 0) (post : Flow c → Fml n) :
      dl{ yul (dl{ yul mode ; model ; (Program.discard term) ; post }) ⇝
        (dl{ yul eval mode ; model ; term => (fun _ => post .normal) }) }

  | yulIf {F c n} (mode : Modality) (model : Model F)
      (condition : Term F n 1) (body : Program F c n) (post : Flow c → Fml n) :
      dl{ yul (dl{ yul mode ; model ; (Program.if_ condition body) ; post }) ⇝
        (dl{ yul eval mode ; model ; condition => (ifPost mode model body post) }) }
  | yulZero {F c n} (mode : Modality) (model : Model F) (count : Nat)
      (body : Program F c (count+n)) (post : Flow c → Fml n) :
      dl{ yul (dl{ yul mode ; model ; (Program.zero count body) ; post }) ⇝
        (dl{ yul subst (extendValues (fun _ : Fin count => word 0)) ;
          (dl{ yul mode ; model ; body ; (dropPost count post) }) }) }
  | yulLet {F c n r} (mode : Modality) (model : Model F)
      (term : Term F n r) (body : Program F c (r+n)) (post : Flow c → Fml n) :
      dl{ yul (dl{ yul mode ; model ; (Program.let_ term body) ; post }) ⇝
        (dl{ yul eval mode ; model ; term => (letPost mode model body post) }) }

  | yulSwitch {F c n} (mode : Modality) (model : Model F) (condition : Term F n 1)
      (arms : Cases F [] c n) (words : CasesWordP arms) (fallback : Program F c n)
      (post : Flow c → Fml n) :
      dl{ yul (dl{ yul mode ; model ; (Program.switch condition arms words fallback) ; post }) ⇝
        (dl{ yul eval mode ; model ; condition => (switchPost mode model arms words fallback post) }) }

  | yulFor {F c n} (mode : Modality) (model : Model F)
      (pre : Program F ⟨c.function,false⟩ n) (condition : Term F n 1)
      (step : Program F ⟨c.function,false⟩ n) (body : Program F ⟨c.function,true⟩ n)
      (post : Flow c → Fml n) :
      dl{ yul (dl{ yul mode ; model ; (Program.for_ pre condition step body) ; post }) ⇝
        (dl{ yul mode ; model ; pre ; (loopPrePost mode model condition step body post) }) }
  | yulLoop {F c n} (mode : Modality) (model : Model F) (condition : Term F n 1)
      (step : Program F ⟨c.function,false⟩ n) (body : Program F ⟨c.function,true⟩ n)
      (post : Flow c → Fml n) :
      dl{ yul (dl{ yul loop c ; mode ; model ; condition ; step ; body ; post }) ⇝
        (dl{ yul eval mode ; model ; condition => (loopConditionPost mode model condition step body post) }) }

  | yulLiteral {F n} (mode : Modality) (model : Model F) (value : Word)
      (post : Values 1 → Fml n) :
      dl{ yul (dl{ yul eval mode ; model ; (Term.literal value) => post }) ⇝
        (post (fun _ : Fin 1 => value)) }
  | yulLocal {F n} (mode : Modality) (model : Model F) (position : Fin n)
      (post : Values 1 → Fml n) :
      dl{ yul (dl{ yul eval mode ; model ; (Term.readLocal position) => post }) ⇝
        (dl{ yul feed (fun vars : Values n => fun _ : Fin 1 => vars position) | post }) }
  | yulBuiltin {F n a r} (mode : Modality) (model : Model F) (builtin : Builtin a r)
      (admitted : WordBuiltinD builtin) (args : Fin a → Term F n 1) (post : Values r → Fml n) :
      dl{ yul (dl{ yul eval mode ; model ; (Term.builtin admitted args) => post }) ⇝
        (argsModal mode model a args (fun inputs => post (admitted.eval inputs))) }
  | yulCall {F n sig} (mode : Modality) (model : Model F) (function : Member F sig)
      (args : Fin sig.args → Term F n 1) (post : Values sig.rets → Fml n) :
      dl{ yul (dl{ yul eval mode ; model ; (Term.call function args) => post }) ⇝
        (argsModal mode model sig.args args (callFrame mode model function post)) }

/-- Each concrete rule is equivalent to its displayed premise in both
modalities, against actual complete runs, without a caller success premise.
For example, assembly { x := add(1,2) } substitutes the exact word3. -/
theorem Rule.sound {n first second} (rule : @Rule n first second) (vars : Values n) :
    first.holds vars ↔ second.holds vars := by
  cases rule with
  | yulSkip mode model post =>
    exact modal_completed mode model .skip post vars ⟨vars,.normal⟩ (fuel := 1) rfl
  | yulLocalLiteralAssign mode model target value post =>
    exact modal_completed mode model (Program.literalAssignment target value) post vars
      ⟨writeTarget (.local target) value vars,.normal⟩ (fuel := 2)
      (evalStmt_assign_literal 0 model.environment model.words target value _ vars)
  | yulPureLiteralAssign mode model target op inputs post =>
    exact modal_completed mode model (Program.pureAssignment target op inputs) post vars
      ⟨writeTarget (.local target) (op.eval inputs) vars,.normal⟩ (fuel := 3)
      (evalStmt_assign_pure_literals 0 model.environment model.words target op inputs _ vars)


  | yulLeave mode model post =>
    exact modal_completed mode model Program.leave post vars ⟨vars,.leave_ rfl⟩ (fuel := 1) rfl
  | yulBreak mode model post =>
    exact modal_completed mode model Program.break_ post vars ⟨vars,.break_ rfl⟩ (fuel := 1) rfl
  | yulContinue mode model post =>
    exact modal_completed mode model Program.continue_ post vars ⟨vars,.continue_ rfl⟩ (fuel := 1) rfl
  | yulFunctionScope mode model signatures bodies words rest post =>
    exact modal_functions mode model signatures bodies words rest post vars


  | yulSequence mode model first second post =>
    exact modal_sequence mode model first second post vars

  | yulAssign mode model targets term post =>
    exact modal_assignment mode model targets term post vars
  | yulDiscard mode model term post =>
    exact modal_discard mode model term post vars

  | yulIf mode model condition body post =>
    exact modal_if mode model condition body post vars
  | yulZero mode model count body post =>
    exact modal_zero mode model count body post vars
  | yulLet mode model term body post =>
    exact modal_let mode model term body post vars

  | yulSwitch mode model condition arms words fallback post =>
    exact modal_switch mode model condition arms words fallback post vars

  | yulFor mode model pre condition step body post =>
    exact modal_for mode model pre condition step body post vars
  | yulLoop mode model condition step body post =>
    exact modal_loop mode model condition step body post vars

  | yulLiteral mode model value post => exact modal_literal mode model value post vars
  | yulLocal mode model position post => exact modal_local mode model position post vars
  | yulBuiltin mode model builtin admitted args post => exact modal_builtin mode model admitted args post vars
  | yulCall mode model function args post => exact modal_call mode model function args post vars

inductive RuleId where
  | yulSkip | yulLocalLiteralAssign | yulPureLiteralAssign
  | yulLeave | yulBreak | yulContinue | yulFunctionScope | yulSequence
  | yulAssign | yulDiscard | yulIf | yulZero | yulLet | yulSwitch | yulFor | yulLoop
  | yulLiteral | yulLocal | yulBuiltin | yulCall
  deriving DecidableEq, Repr

def ruleIds : List RuleId :=
  [.yulSkip,.yulLocalLiteralAssign,.yulPureLiteralAssign,.yulLeave,.yulBreak,
   .yulContinue,.yulFunctionScope,.yulSequence,.yulAssign,.yulDiscard,.yulIf,.yulZero,.yulLet,.yulSwitch,.yulFor,.yulLoop,.yulLiteral,.yulLocal,.yulBuiltin,.yulCall]

def Rule.id {n first second} (rule : @Rule n first second) : RuleId := by
  apply Rule.casesOn (motive := fun {n} _ _ _ => RuleId) rule
  case yulSkip => intros; exact .yulSkip
  case yulLocalLiteralAssign => intros; exact .yulLocalLiteralAssign
  case yulPureLiteralAssign => intros; exact .yulPureLiteralAssign
  case yulLeave => intros; exact .yulLeave
  case yulBreak => intros; exact .yulBreak
  case yulContinue => intros; exact .yulContinue
  case yulFunctionScope => intros; exact .yulFunctionScope
  case yulSequence => intros; exact .yulSequence
  case yulAssign => intros; exact .yulAssign
  case yulDiscard => intros; exact .yulDiscard
  case yulIf => intros; exact .yulIf
  case yulZero => intros; exact .yulZero
  case yulLet => intros; exact .yulLet
  case yulSwitch => intros; exact .yulSwitch
  case yulFor => intros; exact .yulFor
  case yulLoop => intros; exact .yulLoop
  case yulLiteral => intros; exact .yulLiteral
  case yulLocal => intros; exact .yulLocal
  case yulBuiltin => intros; exact .yulBuiltin
  case yulCall => intros; exact .yulCall

/-- Metadata covers these constructors only; it does not assert a rule exists
for every program form or a terminating unrestricted rewrite strategy. -/
theorem Rule.id_mem {n first second} (rule : @Rule n first second) : rule.id ∈ ruleIds := by
  cases rule <;> dsimp only [Rule.id] <;> decide

theorem ruleIds_nodup : ruleIds.Nodup := by decide
theorem ruleIds_count : ruleIds.length = 20 := rfl

end Solidity.Yul.Logic
