import SolidityBridge.Yul.SwitchCompilation
/-! Original-Yul sequence/conditional composition of the concrete switch
compiler. Certificates remain indexed by the original statement and source
horizon. Switch arms/scopes retain their existing RecursiveScopes domain;
this is not a general Source/G24/native or early-control compiler. -/
namespace SolidityBridge.Yul.SwitchControl
open Solidity Backend Scalar Selection
open Solidity.Yul Solidity.Yul.Closed Solidity.Yul.Compilation

inductive Derivation (c : Control) (n : Nat) : Nat → Stmt [] [] c n → Type where
  | normal {fuel stmt} (body : RecursiveScopes.Derivation c n fuel stmt) : Derivation c n fuel stmt
  | dispatch {fuel expression cases fallback}
      (body : @SwitchCompilation.Compiled c n fuel expression cases fallback) :
      Derivation c n (fuel+1) (.switch expression cases fallback)
  | seq {fuel a b} (first : Derivation c n fuel a) (second : Derivation c n fuel b) :
      Derivation c n (fuel+1) (.seq a b)
  | branch {fuel test stmt} (condition : ProducerExpressions.Compiled fuel test)
      (body : Derivation c n fuel stmt) : Derivation c n (fuel+1) (.if_ test stmt)

def Derivation.profile {c n fuel stmt} (compiled : Derivation c n fuel stmt) : StmtWordP stmt := by
  apply Derivation.casesOn (motive := fun _ stmt _ => StmtWordP stmt) compiled
  case normal => intro fuel stmt body; exact body.profile
  case dispatch => intro fuel expression cases fallback body; exact body.profile
  case seq => intro fuel a b first second; exact ⟨first.profile,second.profile⟩
  case branch => intro fuel test stmt condition body; exact ⟨condition.profile,body.profile⟩
termination_by structural compiled

def Derivation.update {c n fuel stmt} (compiled : Derivation c n fuel stmt) :
    Vector Scalar.Word n → Vector Scalar.Word n := by
  apply Derivation.casesOn (motive := fun _ _ _ => Vector Scalar.Word n → Vector Scalar.Word n) compiled
  case normal => intro fuel stmt body; exact body.update
  case dispatch => intro fuel expression cases fallback body; exact body.update
  case seq => intro fuel a b first second locals; exact second.update (first.update locals)
  case branch => intro fuel test stmt condition body locals
                 exact if condition.value locals = 0 then locals else body.update locals
termination_by structural compiled

def Derivation.emit {c n fuel stmt} (compiled : Derivation c n fuel stmt) : Option Backend.Block := by
  apply Derivation.casesOn (motive := fun _ _ _ => Option Backend.Block) compiled
  case normal => intro fuel stmt body; exact body.emit
  case dispatch => intro fuel expression cases fallback body; exact body.emit
  case seq => intro fuel a b first second; exact do pure (.seq (← first.emit) (← second.emit))
  case branch => intro fuel test stmt condition body
                 exact do pure (.ite (← condition.lowered.code 0) (← body.emit) (.code []))
termination_by structural compiled

/-- Visitor over the original sequence/conditional/switch constructors.
Lexical scopes and case bodies retain the existing normal compiler domain. -/
def compile {c n} (fuel : Nat) (stmt : Stmt [] [] c n) : Option (Derivation c n fuel stmt) :=
  match fuel with
  | 0 => none
  | fuel+1 => by
      apply Stmt.casesOn (motive_1 := fun F X c n stmt =>
        match F,X with
        | [],[] => Option (Derivation c n (fuel+1) stmt)
        | _,_ => Unit) stmt
      case seq =>
        intro F X c n a b
        cases F <;> cases X
        · exact do pure (.seq (← compile fuel a) (← compile fuel b))
        all_goals exact ()
      case if_ =>
        intro F X c n test body
        cases F <;> cases X
        · exact do pure (.branch (← PureExpressions.compile fuel test) (← compile fuel body))
        all_goals exact ()
      case switch =>
        intro F X c n expression cases fallback
        cases F <;> cases X
        · exact (SwitchCompilation.compile fuel expression cases fallback).map Derivation.dispatch
        all_goals exact ()
      all_goals intro F X; cases F <;> cases X <;> intros <;>
        first | exact (RecursiveScopes.compile (fuel+1) _).map Derivation.normal | exact ()
termination_by structural fuel


/-- Exact composition over actual original-statement producer executions. -/
theorem Derivation.source :
∀ {c : Control} {n fuel : Nat} {stmt : Stmt [] [] c n}
 (compiled : Derivation c n fuel stmt) (locals : Vector Scalar.Word n),
 evalStmt fuel .nil True.intro stmt compiled.profile (ProducerExpressions.sourceLocals locals) =
 some ⟨ProducerExpressions.sourceLocals (compiled.update locals),.normal⟩ := by
  intro c n fuel stmt compiled locals
  induction compiled generalizing locals with
  | normal leaf => exact leaf.source locals
  | dispatch body => exact body.source locals
  | seq first second ihFirst ihSecond =>
    change (do
      let result ← evalStmt _ .nil True.intro _ first.profile (ProducerExpressions.sourceLocals locals)
      match result.flow with
      | .normal => evalStmt _ .nil True.intro _ second.profile result.vars
      | _ => pure result) = _
    rw [ihFirst]
    exact ihSecond (first.update locals)
  | branch condition arm ih =>
    change (do
      let result ← evalExpr _ .nil True.intro _ condition.profile (ProducerExpressions.sourceLocals locals)
      if (result 0).val = 0 then pure (⟨ProducerExpressions.sourceLocals locals,.normal⟩ : Outcome _ _)
      else evalStmt _ .nil True.intro _ arm.profile (ProducerExpressions.sourceLocals locals)) = _
    rw [condition.source]
    change (if (condition.value locals).toNat = 0 then _ else _) = _
    have truth : (condition.value locals).toNat = 0 ↔ condition.value locals = 0 :=
      ⟨fun h => BitVec.eq_of_toNat_eq h,fun h => congrArg BitVec.toNat h⟩
    change _ = some (⟨ProducerExpressions.sourceLocals (if condition.value locals = 0 then locals else arm.update locals),.normal⟩ : Outcome _ _)
    by_cases zero : condition.value locals = 0
    · rw [if_pos (truth.mpr zero)]
      simp only [if_pos zero]
      rfl
    · rw [if_neg (fun h => zero (truth.mp h)),ih]
      simp only [if_neg zero]


/-- Exact composition over actual original-statement producer executions. -/
theorem Derivation.structured :
∀ {c : Control} {n fuel : Nat} {stmt : Stmt [] [] c n}
 (compiled : Derivation c n fuel stmt) (block : Backend.Block),
 compiled.emit = some block → ∀ (locals : Vector Scalar.Word n) (tail : Scalar.Stack),
 StructuredExec block (locals.toList ++ tail) ((compiled.update locals).toList ++ tail) := by
  intro c n fuel stmt compiled block emitted locals tail
  induction compiled generalizing block locals with
  | normal leaf => exact leaf.structured block emitted locals tail
  | dispatch body => exact body.structured block emitted locals tail
  | seq first second ihFirst ihSecond =>
    change (do
      let a ← first.emit
      let b ← second.emit
      pure (Backend.Block.seq a b)) = some block at emitted
    cases ha : first.emit with
    | none => simp only [ha] at emitted; cases emitted
    | some a =>
      cases hb : second.emit with
      | none => simp only [ha,hb] at emitted; cases emitted
      | some b =>
        simp only [ha,hb] at emitted
        have same : Backend.Block.seq a b = block := Option.some.inj emitted
        subst block
        exact StructuredExec.seq (ihFirst a ha locals) (ihSecond b hb (first.update locals))
  | branch condition arm ih =>
    change (do
      let cc ← condition.lowered.code 0
      let bb ← arm.emit
      pure (Backend.Block.ite cc bb (.code []))) = some block at emitted
    cases hc : condition.lowered.code 0 with
    | none => simp only [hc] at emitted; cases emitted
    | some cc =>
      cases hb : arm.emit with
      | none => simp only [hc,hb] at emitted; cases emitted
      | some bb =>
        simp only [hc,hb] at emitted
        have same : Backend.Block.ite cc bb (.code []) = block := Option.some.inj emitted
        subst block
        have test := condition.lowered.correct 0 cc hc locals #v[] tail
        simp only [Vector.toList_empty,List.nil_append] at test
        by_cases zero : condition.value locals = 0
        · change StructuredExec (.ite cc bb (.code [])) _
            ((if condition.value locals = 0 then locals else arm.update locals).toList ++ tail)
          rw [if_pos zero]
          apply StructuredExec.iteFalse
          · simpa only [zero] using test
          · exact StructuredExec.code rfl
        · change StructuredExec (.ite cc bb (.code [])) _
            ((if condition.value locals = 0 then locals else arm.update locals).toList ++ tail)
          rw [if_neg zero]
          exact StructuredExec.iteTrue test zero (ih bb hb locals)

/-- info: 'SolidityBridge.Yul.SwitchControl.Derivation.source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Derivation.source

/-- info: 'SolidityBridge.Yul.SwitchControl.Derivation.structured' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Derivation.structured
end SolidityBridge.Yul.SwitchControl
