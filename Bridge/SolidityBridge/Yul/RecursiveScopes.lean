import SolidityBridge.Yul.ScopedControl
/-! Recursive scope/control compiler evidence indexed by the ORIGINAL Yul
statement, context and horizon. Existing normal compilation supplies leaves.
No new source AST, state or function convention; emission is at temporary
depth zero. Capacity, early control, functions, loops, physical/G24/native
adequacy and Solidity admission remain separate obligations. -/
namespace SolidityBridge.Yul.RecursiveScopes
open Solidity Backend Scalar Selection
open Solidity.Yul Solidity.Yul.Closed Solidity.Yul.Compilation

inductive Derivation (c : Control) : (n fuel : Nat) → Stmt [] [] c n → Type where
  | normal {n fuel stmt} (leaf : NormalControl.Derivation fuel stmt) : Derivation c n fuel stmt
  | seq {n fuel} {a b : Stmt [] [] c n}
      (first : Derivation c n fuel a) (second : Derivation c n fuel b) :
      Derivation c n (fuel+1) (.seq a b)
  | branch {n fuel} {test : Expr [] [] n 1} {stmt : Stmt [] [] c n}
      (condition : ProducerExpressions.Compiled fuel test) (body : Derivation c n fuel stmt) :
      Derivation c n (fuel+1) (.if_ test stmt)
  | letOne {n fuel} {rhs : Expr [] [] n 1} {stmt : Stmt [] [] c (1+n)}
      (initializer : ProducerExpressions.Compiled fuel rhs) (body : Derivation c (1+n) fuel stmt) :
      Derivation c n (fuel+1) (.let_ 1 rhs stmt)
  | zero (fresh : Nat) {n fuel} {stmt : Stmt [] [] c (fresh+n)}
      (body : Derivation c (fresh+n) fuel stmt) : Derivation c n (fuel+1) (.zero fresh stmt)

def Derivation.profile {c n fuel stmt} (compiled : Derivation c n fuel stmt) : StmtWordP stmt := by
  apply Derivation.casesOn (motive := fun _ _ stmt _ => StmtWordP stmt) compiled
  case normal => intro n fuel stmt leaf; exact leaf.profile
  case seq => intro n fuel a b first second; exact ⟨first.profile,second.profile⟩
  case branch => intro n fuel test stmt condition body; exact ⟨condition.profile,body.profile⟩
  case letOne => intro n fuel rhs stmt initializer body; exact ⟨initializer.profile,body.profile⟩
  case zero => intro fresh n fuel stmt body; exact body.profile
termination_by structural compiled

def Derivation.update {c n fuel stmt} (compiled : Derivation c n fuel stmt) :
    Vector Scalar.Word n → Vector Scalar.Word n := by
  apply Derivation.casesOn (motive := fun n _ _ _ => Vector Scalar.Word n → Vector Scalar.Word n) compiled
  case normal => intro n fuel stmt leaf; exact leaf.update
  case seq => intro n fuel a b first second locals; exact second.update (first.update locals)
  case branch =>
    intro n fuel test stmt condition body locals
    exact if condition.value locals = 0 then locals else body.update locals
  case letOne =>
    intro n fuel rhs stmt initializer body locals
    exact outerLocals (body.update (#v[initializer.value locals] ++ locals))
  case zero =>
    intro fresh n fuel stmt body locals
    exact outerLocals (body.update (Vector.replicate fresh (0 : Scalar.Word) ++ locals))
termination_by structural compiled

def Derivation.emit {c n fuel stmt} (compiled : Derivation c n fuel stmt) : Option Backend.Block := by
  apply Derivation.casesOn (motive := fun _ _ _ _ => Option Backend.Block) compiled
  case normal => intro n fuel stmt leaf; exact leaf.emit 0
  case seq =>
    intro n fuel a b first second
    exact do pure (.seq (← first.emit) (← second.emit))
  case branch =>
    intro n fuel test stmt condition body
    exact do pure (.ite (← condition.lowered.code 0) (← body.emit) (.code []))
  case letOne =>
    intro n fuel rhs stmt initializer body
    exact do pure (.seq (.code (← initializer.lowered.code 0)) (.seq (← body.emit) (.code (popPrefix 1))))
  case zero =>
    intro fresh n fuel stmt body
    exact do pure (.seq (.code (pushPrefix (Vector.replicate fresh (0 : Scalar.Word)).toList))
      (.seq (← body.emit) (.code (popPrefix fresh))))
termination_by structural compiled

/-- Real visitor on original scope/sequence/conditional constructors. Other
forms retain the existing normal compiler's exact supported/refusal domain. -/
def compile {c : Control} {n : Nat} (fuel : Nat) (stmt : Stmt [] [] c n) :
    Option (Derivation c n fuel stmt) :=
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
      case let_ =>
        intro F X c n r rhs body
        cases F <;> cases X
        · cases r with
          | zero => exact none
          | succ r =>
            cases r with
            | zero => exact do pure (.letOne (← PureExpressions.compile fuel rhs) (← compile fuel body))
            | succ _ => exact none
        all_goals exact ()
      case zero =>
        intro F X c n fresh body
        cases F <;> cases X
        · exact (compile fuel body).map (.zero fresh)
        all_goals exact ()
      all_goals intro F X; cases F <;> cases X <;> intros <;>
        first | exact (NormalControl.compile (fuel+1) _).map Derivation.normal | exact ()
termination_by structural fuel

/-- Actual original evaluator/structured execution at the same source horizon. -/
theorem Derivation.source :
∀ {c : Control} {n fuel : Nat} {stmt : Stmt [] [] c n}
 (compiled : Derivation c n fuel stmt) (locals : Vector Scalar.Word n),
 evalStmt fuel .nil True.intro stmt compiled.profile (ProducerExpressions.sourceLocals locals) =
 some ⟨ProducerExpressions.sourceLocals (compiled.update locals),.normal⟩ := by
  intro c n fuel stmt compiled locals
  induction compiled with
  | normal leaf => exact leaf.source locals
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
  
  | letOne initializer body ih =>
    change (do
      let values ← evalExpr _ .nil True.intro _ initializer.profile (ProducerExpressions.sourceLocals locals)
      let result ← evalStmt _ .nil True.intro _ body.profile
        (extendValues values (ProducerExpressions.sourceLocals locals))
      pure (⟨dropValues 1 result.vars,result.flow⟩ : Outcome _ _)) = _
    rw [initializer.source]
    have initial : (fun _ : Fin 1 => (initializer.value locals).toFin) =
        ProducerExpressions.sourceLocals #v[initializer.value locals] := by
      funext i
      have equal : i = 0 := by omega
      subst i
      rfl
    rw [initial]
    change (do
      let result ← evalStmt _ .nil True.intro _ body.profile
        (extendValues (ProducerExpressions.sourceLocals #v[initializer.value locals])
          (ProducerExpressions.sourceLocals locals))
      pure (⟨dropValues 1 result.vars,result.flow⟩ : Outcome _ _)) = _
    rw [← ScopedStatements.locals_append,ih]
    change some (⟨dropValues 1 (ProducerExpressions.sourceLocals _),.normal⟩ : Outcome _ _) = _
    rw [← ScopedStatements.locals_outer]
    rfl
  | zero fresh body ih =>
    change (do
      let result ← evalStmt _ .nil True.intro _ body.profile
        (extendValues (fun _ : Fin fresh => word 0) (ProducerExpressions.sourceLocals locals))
      pure (⟨dropValues fresh result.vars,result.flow⟩ : Outcome _ _)) = _
    have initial : (fun _ : Fin fresh => word 0) =
        ProducerExpressions.sourceLocals (Vector.replicate fresh (0 : Scalar.Word)) := by
      funext i
      simp only [ProducerExpressions.sourceLocals,Vector.getElem_replicate]
      rfl
    rw [initial,← ScopedStatements.locals_append,ih]
    change some (⟨dropValues fresh (ProducerExpressions.sourceLocals _),.normal⟩ : Outcome _ _) = _
    rw [← ScopedStatements.locals_outer]
    rfl

/-- Actual original evaluator/structured execution at the same source horizon. -/
theorem Derivation.structured :
∀ {c : Control} {n fuel : Nat} {stmt : Stmt [] [] c n}
 (compiled : Derivation c n fuel stmt) (block : Backend.Block),
 compiled.emit = some block → ∀ (locals : Vector Scalar.Word n) (tail : Scalar.Stack),
 StructuredExec block (locals.toList ++ tail) ((compiled.update locals).toList ++ tail) := by
  intro c n fuel stmt compiled block emitted locals tail
  induction compiled generalizing block with
  | normal leaf =>
    simpa only [Vector.toList_empty,List.nil_append] using
      StructuredSource.structured leaf 0 block emitted locals #v[] tail
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
  | letOne initializer body ih =>
    change (do
      let a ← initializer.lowered.code 0
      let b ← body.emit
      pure (Backend.Block.seq (.code a) (.seq b (.code (popPrefix 1))))) = some block at emitted
    cases ha : initializer.lowered.code 0 with
    | none => simp only [ha] at emitted; cases emitted
    | some a =>
      cases hb : body.emit with
      | none => simp only [ha,hb] at emitted; cases emitted
      | some b =>
        simp only [ha,hb] at emitted
        cases emitted
        have first := initializer.lowered.correct 0 a ha locals #v[] tail
        change Scalar.run a (locals.toList ++ tail) =
          some (initializer.value locals :: (locals.toList ++ tail)) at first
        have initialList : (#v[initializer.value locals] ++ locals).toList ++ tail =
            initializer.value locals :: (locals.toList ++ tail) := by
          rw [Vector.toList_append]
          rfl
        have entered : Scalar.run a (locals.toList ++ tail) =
            some ((#v[initializer.value locals] ++ locals).toList ++ tail) := by
          rw [initialList]
          exact first
        have middle := ih b hb (#v[initializer.value locals] ++ locals)
        exact StructuredExec.seq (.code entered)
          (.seq middle (.code (popFresh_run (body.update (#v[initializer.value locals] ++ locals)) tail)))
  | zero fresh body ih =>
    change (do
      let b ← body.emit
      pure (Backend.Block.seq (.code (pushPrefix (Vector.replicate fresh (0 : Scalar.Word)).toList))
        (.seq b (.code (popPrefix fresh))))) = some block at emitted
    cases hb : body.emit with
    | none => simp only [hb] at emitted; cases emitted
    | some b =>
      simp only [hb] at emitted
      cases emitted
      have entered : Scalar.run (pushPrefix (Vector.replicate fresh (0 : Scalar.Word)).toList)
          (locals.toList ++ tail) =
          some ((Vector.replicate fresh (0 : Scalar.Word) ++ locals).toList ++ tail) := by
        simpa only [Vector.toList_append,List.append_assoc] using
          pushPrefix_run (Vector.replicate fresh (0 : Scalar.Word)).toList (locals.toList ++ tail)
      have middle := ih b hb (Vector.replicate fresh (0 : Scalar.Word) ++ locals)
      exact StructuredExec.seq (.code entered)
        (.seq middle (.code (popFresh_run (body.update (Vector.replicate fresh (0 : Scalar.Word) ++ locals)) tail)))

/-- info: 'SolidityBridge.Yul.RecursiveScopes.Derivation.source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Derivation.source
/-- info: 'SolidityBridge.Yul.RecursiveScopes.Derivation.structured' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Derivation.structured
end SolidityBridge.Yul.RecursiveScopes
