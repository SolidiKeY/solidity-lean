import Solidity.Yul.Compilation.ScopedStatements
import SolidityBridge.Yul.StructuredSource
import SolidityBridge.Yul.LoopSelection
/-! Actual original Yul scope/structured-body composition. The existing local
initializer compiler, normal-control derivation and structured relation are
reused; there is no replacement AST/state or V12 function convention. Scope
entry/exit select only at temporary depth zero. Capacity, source attachment,
native execution and general Source/G24/views remain separate obligations. -/
namespace SolidityBridge.Yul.ScopedControl
open Solidity Backend Scalar Selection
open Solidity.Yul Solidity.Yul.Closed Solidity.Yul.Compilation

def letOneEmit {fuel c n} {rhs : Expr [] [] n 1} {stmt : Stmt [] [] c (1+n)}
    (initializer : ProducerExpressions.Compiled fuel rhs)
    (body : NormalControl.Derivation fuel stmt) : Option Backend.Block := do
  let first ← initializer.lowered.code 0
  let after ← body.emit 0
  pure (.seq (.code first) (.seq after (.code (popPrefix 1))))

def letOneUpdate {fuel c n} {rhs : Expr [] [] n 1} {stmt : Stmt [] [] c (1+n)}
    (initializer : ProducerExpressions.Compiled fuel rhs)
    (body : NormalControl.Derivation fuel stmt) (locals : Vector Scalar.Word n) : Vector Scalar.Word n :=
  outerLocals (body.update (#v[initializer.value locals] ++ locals))

def zeroEmit {fuel c n fresh} {stmt : Stmt [] [] c (fresh+n)}
    (body : NormalControl.Derivation fuel stmt) : Option Backend.Block := do
  let after ← body.emit 0
  pure (.seq (.code (pushPrefix (Vector.replicate fresh (0 : Scalar.Word)).toList))
    (.seq after (.code (popPrefix fresh))))

def zeroUpdate {fuel c n fresh} {stmt : Stmt [] [] c (fresh+n)}
    (body : NormalControl.Derivation fuel stmt) (locals : Vector Scalar.Word n) : Vector Scalar.Word n :=
  outerLocals (body.update (Vector.replicate fresh (0 : Scalar.Word) ++ locals))

/-- Concrete original source/target scope composition; capacity is separate. -/
theorem letOne_source :
∀ {fuel : Nat} {c : Control} {n : Nat}
 {rhs : Expr [] [] n 1} {stmt : Stmt [] [] c (1+n)}
 (initializer : ProducerExpressions.Compiled fuel rhs)
 (body : NormalControl.Derivation fuel stmt) (locals : Vector Scalar.Word n),
 evalStmt (fuel+1) .nil True.intro (.let_ 1 rhs stmt) ⟨initializer.profile,body.profile⟩
   (ProducerExpressions.sourceLocals locals) =
   some ⟨ProducerExpressions.sourceLocals (letOneUpdate initializer body locals),.normal⟩ := by
  intro fuel c n rhs stmt initializer body locals
  change (do
    let values ← evalExpr fuel .nil True.intro rhs initializer.profile (ProducerExpressions.sourceLocals locals)
    let result ← evalStmt fuel .nil True.intro stmt body.profile
      (extendValues values (ProducerExpressions.sourceLocals locals))
    pure (⟨dropValues 1 result.vars,result.flow⟩ : Outcome c n)) = _
  rw [initializer.source]
  have initial : (fun _ : Fin 1 => (initializer.value locals).toFin) =
      ProducerExpressions.sourceLocals #v[initializer.value locals] := by
    funext i
    have equal : i = 0 := by omega
    subst i
    rfl
  rw [initial]
  change (do
    let result ← evalStmt fuel .nil True.intro stmt body.profile
      (extendValues (ProducerExpressions.sourceLocals #v[initializer.value locals])
        (ProducerExpressions.sourceLocals locals))
    pure (⟨dropValues 1 result.vars,result.flow⟩ : Outcome c n)) = _
  rw [← ScopedStatements.locals_append,body.source]
  change some (⟨dropValues 1 (ProducerExpressions.sourceLocals _),.normal⟩ : Outcome c n) = _
  rw [← ScopedStatements.locals_outer]
  rfl

/-- Concrete original source/target scope composition; capacity is separate. -/
theorem letOne_structured :
∀ {fuel : Nat} {c : Control} {n : Nat}
 {rhs : Expr [] [] n 1} {stmt : Stmt [] [] c (1+n)}
 (initializer : ProducerExpressions.Compiled fuel rhs)
 (body : NormalControl.Derivation fuel stmt) (block : Backend.Block),
 letOneEmit initializer body = some block →
 ∀ (locals : Vector Scalar.Word n) (tail : Scalar.Stack),
 StructuredExec block (locals.toList ++ tail)
   ((letOneUpdate initializer body locals).toList ++ tail) := by
  intro fuel c n rhs stmt initializer body block emitted locals tail
  unfold letOneEmit at emitted
  cases ha : initializer.lowered.code 0 with
  | none => simp only [ha] at emitted; cases emitted
  | some a =>
    cases hb : body.emit 0 with
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
      have middle := StructuredSource.structured body 0 b hb
        (#v[initializer.value locals] ++ locals) #v[] tail
      simp only [Vector.toList_empty,List.nil_append] at middle
      exact StructuredExec.seq (.code entered)
        (.seq middle (.code (popFresh_run (body.update (#v[initializer.value locals] ++ locals)) tail)))

/-- Concrete original source/target scope composition; capacity is separate. -/
theorem zero_source :
∀ {fuel : Nat} {c : Control} {n fresh : Nat}
 {stmt : Stmt [] [] c (fresh+n)} (body : NormalControl.Derivation fuel stmt)
 (locals : Vector Scalar.Word n),
 evalStmt (fuel+1) .nil True.intro (.zero fresh stmt) body.profile
   (ProducerExpressions.sourceLocals locals) =
   some ⟨ProducerExpressions.sourceLocals (zeroUpdate body locals),.normal⟩ := by
  intro fuel c n fresh stmt body locals
  change (do
    let result ← evalStmt fuel .nil True.intro stmt body.profile
      (extendValues (fun _ : Fin fresh => word 0) (ProducerExpressions.sourceLocals locals))
    pure (⟨dropValues fresh result.vars,result.flow⟩ : Outcome c n)) = _
  have initial : (fun _ : Fin fresh => word 0) =
      ProducerExpressions.sourceLocals (Vector.replicate fresh (0 : Scalar.Word)) := by
    funext i
    simp only [ProducerExpressions.sourceLocals,Vector.getElem_replicate]
    rfl
  rw [initial,← ScopedStatements.locals_append,body.source]
  change some (⟨dropValues fresh (ProducerExpressions.sourceLocals _),.normal⟩ : Outcome c n) = _
  rw [← ScopedStatements.locals_outer]
  rfl

/-- Concrete original source/target scope composition; capacity is separate. -/
theorem zero_structured :
∀ {fuel : Nat} {c : Control} {n fresh : Nat}
 {stmt : Stmt [] [] c (fresh+n)} (body : NormalControl.Derivation fuel stmt)
 (block : Backend.Block), zeroEmit body = some block →
 ∀ (locals : Vector Scalar.Word n) (tail : Scalar.Stack),
 StructuredExec block (locals.toList ++ tail) ((zeroUpdate body locals).toList ++ tail) := by
  intro fuel c n fresh stmt body block emitted locals tail
  unfold zeroEmit at emitted
  cases hb : body.emit 0 with
  | none => simp only [hb] at emitted; cases emitted
  | some b =>
    simp only [hb] at emitted
    cases emitted
    have entered : Scalar.run (pushPrefix (Vector.replicate fresh (0 : Scalar.Word)).toList)
        (locals.toList ++ tail) =
        some ((Vector.replicate fresh (0 : Scalar.Word) ++ locals).toList ++ tail) := by
      simpa only [Vector.toList_append,List.append_assoc] using
        pushPrefix_run (Vector.replicate fresh (0 : Scalar.Word)).toList (locals.toList ++ tail)
    have middle := StructuredSource.structured body 0 b hb
      (Vector.replicate fresh (0 : Scalar.Word) ++ locals) #v[] tail
    simp only [Vector.toList_empty,List.nil_append] at middle
    exact StructuredExec.seq (.code entered)
      (.seq middle (.code (popFresh_run (body.update (Vector.replicate fresh (0 : Scalar.Word) ++ locals)) tail)))

/-- info: 'SolidityBridge.Yul.ScopedControl.letOne_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms letOne_source
/-- info: 'SolidityBridge.Yul.ScopedControl.letOne_structured' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms letOne_structured
/-- info: 'SolidityBridge.Yul.ScopedControl.zero_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms zero_source
/-- info: 'SolidityBridge.Yul.ScopedControl.zero_structured' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms zero_structured
end SolidityBridge.Yul.ScopedControl
