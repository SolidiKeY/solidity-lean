import Solidity.Yul.WordRules
import Solidity.Yul.WordAgreement
import Solidity.Yul.Checks.ClosedRun
set_option Elab.async false

namespace Solidity.Yul.Checks.WordLogic
open Solidity.Yul.Closed Solidity.Yul.Logic
open Solidity (Modality)
open scoped Solidity.Yul.Logic

/-- Nonreserved notation words stay ordinary Lean identifiers. -/
def program : Nat := 7
def atom : Nat := 9
def yul : Nat := 11
example : program + atom + yul = 27 := rfl

def empty : Model [] := ⟨.nil,True.intro⟩
def zero : Values 1 := fun _ => word 0
def nine : Values 1 := fun _ => word 9
def normalIs (w : Word) : Flow ⟨false,false⟩ → Solidity.Yul.Logic.Fml 1 :=
  fun flow => .atom (fun vars => flow.isNormal = true ∧ vars 0 = w)

example (mode : Modality) :
    (dl{ yul mode ; empty ; (Program.literalAssignment 0 (word 257)) ; (normalIs (word 257)) }).holds zero :=
  (Rule.sound (.yulLocalLiteralAssign mode empty 0 (word 257) _) zero).mpr ⟨rfl,rfl⟩

example (mode : Modality) :
    (dl{ yul mode ; empty ; (Program.skip (c := ⟨false,false⟩)) ; (normalIs (word 0)) }).holds zero :=
  (Rule.sound (.yulSkip mode empty (normalIs (word 0))) zero).mpr ⟨rfl,rfl⟩

/-- A nearby false assertion remains false: no uint8-style cleanup of Yul locals. -/
example (mode : Modality) :
    ¬ (dl{ yul mode ; empty ; (Program.literalAssignment 0 (word 257)) ; (normalIs (word 1)) }).holds zero := by
  intro actual
  have wrong := (Rule.sound (.yulLocalLiteralAssign mode empty 0 (word 257) (normalIs (word 1))) zero).mp actual
  exact (by decide : word 257 ≠ word 1) wrong.2

example (mode : Modality) {a} (op : Pure a) (inputs : Values a) :
    (dl{ yul mode ; empty ; (Program.pureAssignment 0 op inputs) ; (normalIs (op.eval inputs)) }).holds zero :=
  (Rule.sound (.yulPureLiteralAssign mode empty 0 op inputs _) zero).mpr ⟨rfl,rfl⟩

def transferPost {c} : Flow c → Solidity.Yul.Logic.Fml 1 :=
  fun flow => .atom (fun vars => flow.isNormal = false ∧ vars 0 = word 9)
example (mode : Modality) :
    (dl{ yul mode ; empty ; (Program.leave (loop := false)) ; transferPost }).holds nine :=
  (Rule.sound (.yulLeave mode empty transferPost) nine).mpr ⟨rfl,rfl⟩
example (mode : Modality) :
    (dl{ yul mode ; empty ; (Program.break_ (fn := false)) ; transferPost }).holds nine :=
  (Rule.sound (.yulBreak mode empty transferPost) nine).mpr ⟨rfl,rfl⟩
example (mode : Modality) :
    (dl{ yul mode ; empty ; (Program.continue_ (fn := false)) ; transferPost }).holds nine :=
  (Rule.sound (.yulContinue mode empty transferPost) nine).mpr ⟨rfl,rfl⟩

/-- Each transfer suppresses the following write. -/
example (mode : Modality) :
    (dl{ yul mode ; empty ;
      (Program.sequence (Program.leave (loop := false)) (Program.literalAssignment 0 (word 257))) ;
      transferPost }).holds nine := by
  apply (Rule.sound (.yulSequence mode empty _ _ transferPost) nine).mpr
  apply (Rule.sound (.yulLeave mode empty _) nine).mpr
  exact ⟨rfl,rfl⟩
example (mode : Modality) :
    (dl{ yul mode ; empty ;
      (Program.sequence (Program.break_ (fn := false)) (Program.literalAssignment 0 (word 257))) ;
      transferPost }).holds nine := by
  apply (Rule.sound (.yulSequence mode empty _ _ transferPost) nine).mpr
  apply (Rule.sound (.yulBreak mode empty _) nine).mpr
  exact ⟨rfl,rfl⟩
example (mode : Modality) :
    (dl{ yul mode ; empty ;
      (Program.sequence (Program.continue_ (fn := false)) (Program.literalAssignment 0 (word 257))) ;
      transferPost }).holds nine := by
  apply (Rule.sound (.yulSequence mode empty _ _ transferPost) nine).mpr
  apply (Rule.sound (.yulContinue mode empty _) nine).mpr
  exact ⟨rfl,rfl⟩

/-- Ordinary sequence lands at the second update. -/
example (mode : Modality) :
    (dl{ yul mode ; empty ;
      (Program.sequence (Program.literalAssignment 0 (word 9)) (Program.literalAssignment 0 (word 257))) ;
      (normalIs (word 257)) }).holds zero := by
  apply (Rule.sound (.yulSequence mode empty _ _ _) zero).mpr
  apply (Rule.sound (.yulLocalLiteralAssign mode empty 0 (word 9) _) zero).mpr
  change (Solidity.Yul.Logic.Fml.modal mode empty (Program.literalAssignment 0 (word 257))
    (normalIs (word 257))).holds (writeTarget (.local 0) (word 9) zero)
  apply (Rule.sound (.yulLocalLiteralAssign mode empty 0 (word 257) _) _).mpr
  exact ⟨rfl,rfl⟩

def recModel : Model [ClosedRun.divergeSig] := ⟨ClosedRun.divergeEnv,ClosedRun.divergeEnvD.profile⟩
def recProgram : Program [ClosedRun.divergeSig] ⟨false,false⟩ 0 :=
  ⟨.discard ClosedRun.divergeCall,ClosedRun.divergeCallD.profile⟩
def falsePost {c n} : Flow c → Solidity.Yul.Logic.Fml n := fun _ => .atom (fun _ => False)

theorem forever (fuel : Nat) (vars : Values 0) :
    evalStmt fuel recModel.environment recModel.words recProgram.code recProgram.words vars = none := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
    change evalStmt (fuel+1) ClosedRun.divergeEnv ClosedRun.divergeEnvD.profile
      (Stmt.discard ClosedRun.divergeCall) ClosedRun.divergeCallD.profile vars = none
    rw [evalStmt_discard, ClosedRun.diverge_all]
    rfl

theorem recBox :
    (dl{ yul Modality.box ; recModel ; recProgram ; falsePost }).holds Fin.elim0 := by
  intro fuel result completed
  rw [forever] at completed
  cases completed
theorem recNotDiamond :
    ¬ (dl{ yul Modality.diamond ; recModel ; recProgram ; falsePost }).holds Fin.elim0 := by
  rintro ⟨fuel,result,completed,after⟩
  rw [forever] at completed
  cases completed


/-- A diverging first program, or a normally completing first followed by
divergence, gives divergence in the tested sequence. Transfers can suppress it. -/
example :
    (dl{ yul Modality.box ; recModel ;
      (Program.sequence recProgram Program.skip) ; falsePost }).holds Fin.elim0 := by
  apply (Rule.sound (.yulSequence .box recModel recProgram Program.skip falsePost) Fin.elim0).mpr
  intro fuel result completed
  rw [forever] at completed
  cases completed
example :
    ¬ (dl{ yul Modality.diamond ; recModel ;
      (Program.sequence recProgram Program.skip) ; falsePost }).holds Fin.elim0 := by
  intro actual
  rcases (Rule.sound (.yulSequence .diamond recModel recProgram Program.skip falsePost) Fin.elim0).mp actual with
    ⟨fuel,result,completed,after⟩
  rw [forever] at completed
  cases completed
example :
    (dl{ yul Modality.box ; recModel ;
      (Program.sequence Program.skip recProgram) ; falsePost }).holds Fin.elim0 := by
  apply (Rule.sound (.yulSequence .box recModel Program.skip recProgram falsePost) Fin.elim0).mpr
  apply (Rule.sound (.yulSkip .box recModel _) Fin.elim0).mpr
  exact recBox
example :
    ¬ (dl{ yul Modality.diamond ; recModel ;
      (Program.sequence Program.skip recProgram) ; falsePost }).holds Fin.elim0 := by
  intro actual
  have first := (Rule.sound (.yulSequence .diamond recModel Program.skip recProgram falsePost) Fin.elim0).mp actual
  exact recNotDiamond ((Rule.sound (.yulSkip .diamond recModel _) Fin.elim0).mp first)


/-- A legal leave suppresses a following recursive divergence. -/
def recursiveTail : Program [ClosedRun.divergeSig] ⟨true,false⟩ 0 :=
  ⟨.discard ClosedRun.divergeCall,ClosedRun.divergeCallD.profile⟩
example (mode : Modality) :
    (dl{ yul mode ; recModel ; (Program.sequence Program.leave recursiveTail) ;
      (fun flow => Solidity.Yul.Logic.Fml.atom (fun _ => flow.isNormal = false)) }).holds Fin.elim0 := by
  apply (Rule.sound (.yulSequence mode recModel Program.leave recursiveTail _) Fin.elim0).mpr
  apply (Rule.sound (.yulLeave mode recModel _) Fin.elim0).mpr
  rfl

def recBodies : Bodies [ClosedRun.divergeSig] [] [ClosedRun.divergeSig] :=
  .cons ClosedRun.divergeBody .nil
def recBodiesP : BodiesWordP recBodies := ⟨ClosedRun.divergeBodyD.profile,True.intro⟩
example : (dl{ yul Modality.box ; empty ;
    (Program.functions [ClosedRun.divergeSig] recBodies recBodiesP recProgram) ;
    falsePost }).holds Fin.elim0 :=
  (Rule.sound (.yulFunctionScope (F := []) (c := ⟨false,false⟩) (n := 0) .box empty [ClosedRun.divergeSig] recBodies recBodiesP recProgram falsePost) Fin.elim0).mpr recBox
example : ¬ (dl{ yul Modality.diamond ; empty ;
    (Program.functions [ClosedRun.divergeSig] recBodies recBodiesP recProgram) ;
    falsePost }).holds Fin.elim0 := by
  intro actual
  exact recNotDiamond ((Rule.sound
    (.yulFunctionScope (F := []) (c := ⟨false,false⟩) (n := 0) .diamond empty [ClosedRun.divergeSig] recBodies recBodiesP recProgram falsePost) Fin.elim0).mp actual)

example : Run recModel recProgram Fin.elim0 (.error .diverge) := .diverge (fun fuel => forever fuel _)
example : ∀ bound, Solidity.Source.firstDone
    (fun fuel => sourceResult (evalStmt fuel recModel.environment recModel.words
      recProgram.code recProgram.words Fin.elim0)) bound = none :=
  (diverge_iff_firstDone recModel recProgram Fin.elim0).mp (.diverge (fun fuel => forever fuel _))

def loop : Program [] ⟨false,false⟩ 1 :=
  ⟨Static.loop,ClosedPure.loopD.profile⟩
def loopResult := (evalStmt 6 empty.environment empty.words loop.code loop.words zero).get (by decide)
theorem loopComplete :
    evalStmt 6 empty.environment empty.words loop.code loop.words zero = some loopResult :=
  (Option.some_get (by decide)).symm
example (mode : Modality) :
    (dl{ yul mode ; empty ; loop ; (normalIs (word 1)) }).holds zero :=
  (modal_completed mode empty loop _ zero loopResult loopComplete).mpr (by
    change loopResult.flow.isNormal = true ∧ loopResult.vars 0 = word 1
    decide)
example (mode : Modality) :
    (dl{ yul mode ; empty ; loop ; (normalIs (word 1)) }).holds zero ↔
      mode.afterRunTR (fun out => (normalIs (word 1) out.flow).holds out.vars) (.ok loopResult) :=
  modal_agrees mode _ (.complete 6 loopResult loopComplete)

/-- Notation builds exactly the typed core terms and programs. -/
example {F n r} (e : Expr F [] n r) (h : ExprWordP e) :
    (tm{ yul e | h } : Term F n r) = ⟨e,h⟩ := rfl
example {F c n} (s : Stmt F [] c n) (h : StmtWordP s) :
    (dl{ yul program s | h } : Program F c n) = ⟨s,h⟩ := rfl
example {F c n} (mode : Modality) (model : Model F) (program : Program F c n) (post : Flow c → Solidity.Yul.Logic.Fml n) :
    (dl{ yul mode ; model ; program ; post }) = Solidity.Yul.Logic.Fml.modal mode model program post := rfl
example {n} (first second : Solidity.Yul.Logic.Fml n) :
    (dl{ yul first ⇝ second }) = Rule first second := rfl
example {n m} (update : Values n → Values m) (post : Solidity.Yul.Logic.Fml m) :
    (dl{ yul subst update ; post }) = Solidity.Yul.Logic.Fml.subst update post := rfl
example {n} (predicate : Values n → Prop) :
    (dl{ yul atom predicate }) = Solidity.Yul.Logic.Fml.atom predicate := rfl

example : ruleIds.length = 20 := ruleIds_count
example : ruleIds.Nodup := ruleIds_nodup

end Solidity.Yul.Checks.WordLogic
