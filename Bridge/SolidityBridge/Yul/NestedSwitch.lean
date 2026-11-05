import SolidityBridge.Yul.ScopedSwitch
/-! Proof-carrying composition over ORIGINAL closed Yul statements/cases.
The concrete visitor below constructs these certificates from actual child
compilers; no new source AST/state, assumed simulation or V12 convention.
Normal flow/pure-word subset only; admission/capacity/Source/G24/native remain
separate obligations. -/
namespace SolidityBridge.Yul.NestedSwitch
open Solidity Backend Scalar Selection
open Solidity.Yul Solidity.Yul.Closed Solidity.Yul.Compilation

structure Compiled {c n} (fuel : Nat) (stmt : Stmt [] [] c n) where
  profile : StmtWordP stmt
  update : Vector Scalar.Word n → Vector Scalar.Word n
  emit : Option Backend.Block
  source : ∀ locals, evalStmt fuel .nil True.intro stmt profile
    (ProducerExpressions.sourceLocals locals) =
    some ⟨ProducerExpressions.sourceLocals (update locals),.normal⟩
  structured : ∀ block, emit = some block → ∀ locals tail,
    StructuredExec block (locals.toList ++ tail) ((update locals).toList ++ tail)

structure CompiledCases {c n} (fuel : Nat) (cases : Cases [] [] c n) where
  profile : CasesWordP cases
  choose : Scalar.Word → Vector Scalar.Word n → Option (Vector Scalar.Word n)
  emit : Backend.Block → Option Backend.Block
  source : ∀ selector locals,
    evalCases fuel .nil True.intro cases profile selector.toFin
      (ProducerExpressions.sourceLocals locals) =
    some ((choose selector locals).map
      (fun out => (⟨ProducerExpressions.sourceLocals out,.normal⟩ : Outcome c n)))
  structured : ∀ {defaultFuel} {fallback : Stmt [] [] c n}
    (defaultBody : Compiled defaultFuel fallback) fallbackBlock,
    defaultBody.emit = some fallbackBlock → ∀ block,
    emit fallbackBlock = some block → ∀ selector locals tail,
    StructuredExec block (selector :: (locals.toList ++ tail))
      (((choose selector locals).getD (defaultBody.update locals)).toList ++ tail)

def ofScoped {c n fuel} {stmt : Stmt [] [] c n}
    (body : ScopedSwitch.Derivation c n fuel stmt) : Compiled fuel stmt :=
  ⟨body.profile,body.update,body.emit,body.source,body.structured⟩

def sequence {c n fuel} {a b : Stmt [] [] c n}
    (first : Compiled fuel a) (second : Compiled fuel b) : Compiled (fuel+1) (.seq a b) where
  profile := ⟨first.profile,second.profile⟩
  update := fun locals => second.update (first.update locals)
  emit := do pure (.seq (← first.emit) (← second.emit))
  source := by
    intro locals
    change (do
      let result ← evalStmt _ .nil True.intro _ first.profile (ProducerExpressions.sourceLocals locals)
      match result.flow with
      | .normal => evalStmt _ .nil True.intro _ second.profile result.vars
      | _ => pure result) = _
    rw [first.source]
    exact second.source (first.update locals)
  structured := by
    intro block emitted locals tail
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
        exact StructuredExec.seq (first.structured a ha locals tail) (second.structured b hb (first.update locals) tail)

def branch {c n fuel} {test : Expr [] [] n 1} {stmt : Stmt [] [] c n}
    (condition : ProducerExpressions.Compiled fuel test) (body : Compiled fuel stmt) :
    Compiled (fuel+1) (.if_ test stmt) where
  profile := ⟨condition.profile,body.profile⟩
  update := fun locals => if condition.value locals = 0 then locals else body.update locals
  emit := do pure (.ite (← condition.lowered.code 0) (← body.emit) (.code []))
  source := by
    intro locals
    change (do
      let result ← evalExpr _ .nil True.intro _ condition.profile (ProducerExpressions.sourceLocals locals)
      if (result 0).val = 0 then pure (⟨ProducerExpressions.sourceLocals locals,.normal⟩ : Outcome _ _)
      else evalStmt _ .nil True.intro _ body.profile (ProducerExpressions.sourceLocals locals)) = _
    rw [condition.source]
    change (if (condition.value locals).toNat = 0 then _ else _) = _
    have truth : (condition.value locals).toNat = 0 ↔ condition.value locals = 0 :=
      ⟨fun h => BitVec.eq_of_toNat_eq h,fun h => congrArg BitVec.toNat h⟩
    change _ = some (⟨ProducerExpressions.sourceLocals (if condition.value locals = 0 then locals else body.update locals),.normal⟩ : Outcome _ _)
    by_cases zero : condition.value locals = 0
    · rw [if_pos (truth.mpr zero)]
      simp only [if_pos zero]
      rfl
    · rw [if_neg (fun h => zero (truth.mp h)),body.source]
      simp only [if_neg zero]
  structured := by
    intro block emitted locals tail
    change (do
      let cc ← condition.lowered.code 0
      let bb ← body.emit
      pure (Backend.Block.ite cc bb (.code []))) = some block at emitted
    cases hc : condition.lowered.code 0 with
    | none => simp only [hc] at emitted; cases emitted
    | some cc =>
      cases hb : body.emit with
      | none => simp only [hc,hb] at emitted; cases emitted
      | some bb =>
        simp only [hc,hb] at emitted
        have same : Backend.Block.ite cc bb (.code []) = block := Option.some.inj emitted
        subst block
        have test := condition.lowered.correct 0 cc hc locals #v[] tail
        simp only [Vector.toList_empty,List.nil_append] at test
        by_cases zero : condition.value locals = 0
        · change StructuredExec (.ite cc bb (.code [])) _
            ((if condition.value locals = 0 then locals else body.update locals).toList ++ tail)
          rw [if_pos zero]
          apply StructuredExec.iteFalse
          · simpa only [zero] using test
          · exact StructuredExec.code rfl
        · change StructuredExec (.ite cc bb (.code [])) _
            ((if condition.value locals = 0 then locals else body.update locals).toList ++ tail)
          rw [if_neg zero]
          exact StructuredExec.iteTrue test zero (body.structured bb hb locals tail)

def letOne {c n fuel} {rhs : Expr [] [] n 1} {stmt : Stmt [] [] c (1+n)}
    (initializer : ProducerExpressions.Compiled fuel rhs) (body : Compiled fuel stmt) :
    Compiled (fuel+1) (.let_ 1 rhs stmt) where
  profile := ⟨initializer.profile,body.profile⟩
  update := fun locals => outerLocals (body.update (#v[initializer.value locals] ++ locals))
  emit := do pure (.seq (.code (← initializer.lowered.code 0))
    (.seq (← body.emit) (.code (popPrefix 1))))
  source := by
    intro locals
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
    rw [← ScopedStatements.locals_append,body.source]
    change some (⟨dropValues 1 (ProducerExpressions.sourceLocals _),.normal⟩ : Outcome _ _) = _
    rw [← ScopedStatements.locals_outer]
  structured := by
    intro block emitted locals tail
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
        have middle := body.structured b hb (#v[initializer.value locals] ++ locals) tail
        exact StructuredExec.seq (.code entered)
          (.seq middle (.code (popFresh_run (body.update (#v[initializer.value locals] ++ locals)) tail)))

def zero (fresh : Nat) {c n fuel} {stmt : Stmt [] [] c (fresh+n)}
    (body : Compiled fuel stmt) : Compiled (fuel+1) (.zero fresh stmt) where
  profile := body.profile
  update := fun locals => outerLocals (body.update (Vector.replicate fresh (0 : Scalar.Word) ++ locals))
  emit := do pure (.seq (.code (pushPrefix (Vector.replicate fresh (0 : Scalar.Word)).toList))
    (.seq (← body.emit) (.code (popPrefix fresh))))
  source := by
    intro locals
    change (do
      let result ← evalStmt _ .nil True.intro _ body.profile
        (extendValues (fun _ : Fin fresh => word 0) (ProducerExpressions.sourceLocals locals))
      pure (⟨dropValues fresh result.vars,result.flow⟩ : Outcome _ _)) = _
    have initial : (fun _ : Fin fresh => word 0) =
        ProducerExpressions.sourceLocals (Vector.replicate fresh (0 : Scalar.Word)) := by
      funext i
      simp only [ProducerExpressions.sourceLocals,Vector.getElem_replicate]
      rfl
    rw [initial,← ScopedStatements.locals_append,body.source]
    change some (⟨dropValues fresh (ProducerExpressions.sourceLocals _),.normal⟩ : Outcome _ _) = _
    rw [← ScopedStatements.locals_outer]
  structured := by
    intro block emitted locals tail
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
      have middle := body.structured b hb (Vector.replicate fresh (0 : Scalar.Word) ++ locals) tail
      exact StructuredExec.seq (.code entered)
        (.seq middle (.code (popFresh_run (body.update (Vector.replicate fresh (0 : Scalar.Word) ++ locals)) tail)))

def nil (fuel : Nat) (c : Control) (n : Nat) : CompiledCases (fuel+1) (.nil : Cases [] [] c n) where
  profile := True.intro
  choose := fun _ _ => none
  emit := fun fallback => some (.seq (.code [.op .POP]) fallback)
  source := by intro selector locals; rfl
  structured := by
    intro defaultFuel fallback defaultBody fallbackBlock defaultEmitted block emitted selector locals tail
    change some (Backend.Block.seq (.code [.op .POP]) fallbackBlock) = some block at emitted
    cases emitted
    exact StructuredExec.seq (.code rfl) (defaultBody.structured fallbackBlock defaultEmitted locals tail)


def cons {c n fuel value} {body : Stmt [] [] c n} {rest : Cases [] [] c n}
    (arm : Compiled fuel body) (suffix : CompiledCases fuel rest) :
    CompiledCases (fuel+1) (.cons value body rest) where
  profile := ⟨arm.profile,suffix.profile⟩
  choose := fun selector locals => if selector.toFin = value then some (arm.update locals)
    else suffix.choose selector locals
  emit := fun fallback => do
    let body ← arm.emit
    let rest ← suffix.emit fallback
    pure (.ite (SwitchCompilation.compareCode value) (.seq (.code [.op .POP]) body) rest)
  source := by
    intro selector locals
    change (if selector.toFin = value then
      (evalStmt fuel .nil True.intro body arm.profile (ProducerExpressions.sourceLocals locals)).map some
      else evalCases fuel .nil True.intro rest suffix.profile selector.toFin
        (ProducerExpressions.sourceLocals locals)) = _
    change _ = some ((if selector.toFin = value then some (arm.update locals)
      else suffix.choose selector locals).map
        (fun out => (⟨ProducerExpressions.sourceLocals out,.normal⟩ : Outcome c n)))
    by_cases same : selector.toFin = value
    · rw [if_pos same,arm.source]
      simp only [if_pos same,Option.map_some]
    · rw [if_neg same,suffix.source]
      simp only [if_neg same]
  structured := by
    intro defaultFuel fallback defaultBody fallbackBlock defaultEmitted block emitted selector locals tail
    change (do
      let b ← arm.emit
      let r ← suffix.emit fallbackBlock
      pure (Backend.Block.ite (SwitchCompilation.compareCode value) (.seq (.code [.op .POP]) b) r)) = some block at emitted
    cases hb : arm.emit with
    | none => simp only [hb] at emitted; cases emitted
    | some b =>
      cases hr : suffix.emit fallbackBlock with
      | none => simp only [hb,hr] at emitted; cases emitted
      | some r =>
        simp only [hb,hr] at emitted
        cases emitted
        change StructuredExec (.ite (SwitchCompilation.compareCode value) (.seq (.code [.op .POP]) b) r)
          (selector :: (locals.toList ++ tail))
          (((if selector.toFin = value then some (arm.update locals)
            else suffix.choose selector locals).getD (defaultBody.update locals)).toList ++ tail)
        by_cases same : selector.toFin = value
        · rw [if_pos same]
          apply StructuredExec.iteTrue (w:=1)
          · simpa only [if_pos same] using SwitchCompilation.compare_run value selector (locals.toList ++ tail)
          · decide
          · exact StructuredExec.seq (.code rfl) (arm.structured b hb locals tail)
        · rw [if_neg same]
          exact StructuredExec.iteFalse
            (by simpa only [if_neg same] using SwitchCompilation.compare_run value selector (locals.toList ++ tail))
            (suffix.structured defaultBody fallbackBlock defaultEmitted r hr selector locals tail)

def dispatch {c n fuel} {expression : Expr [] [] n 1} {cases : Cases [] [] c n}
    {fallback : Stmt [] [] c n} (selector : ProducerExpressions.Compiled fuel expression)
    (arms : CompiledCases fuel cases) (defaultBody : Compiled fuel fallback) :
    Compiled (fuel+1) (.switch expression cases fallback) where
  profile := ⟨selector.profile,arms.profile,defaultBody.profile⟩
  update := fun locals => match arms.choose (selector.value locals) locals with
    | some updated => updated | none => defaultBody.update locals
  emit := do
    let code ← selector.lowered.code 0
    let fallback ← defaultBody.emit
    let dispatch ← arms.emit fallback
    pure (.seq (.code code) dispatch)
  source := by
    intro locals
    change (do
      let value ← evalExpr fuel .nil True.intro expression selector.profile (ProducerExpressions.sourceLocals locals)
      let result ← evalCases fuel .nil True.intro cases arms.profile (value 0) (ProducerExpressions.sourceLocals locals)
      match result with
      | some out => pure out
      | none => evalStmt fuel .nil True.intro fallback defaultBody.profile (ProducerExpressions.sourceLocals locals)) = _
    rw [selector.source]
    change (do
      let result ← evalCases fuel .nil True.intro cases arms.profile
        (selector.value locals).toFin (ProducerExpressions.sourceLocals locals)
      match result with
      | some out => pure out
      | none => evalStmt fuel .nil True.intro fallback defaultBody.profile (ProducerExpressions.sourceLocals locals)) = _
    rw [arms.source]
    cases chosen : arms.choose (selector.value locals) locals with
    | none =>
      simp only [Option.map_none]
      exact defaultBody.source locals
    | some updated =>
      simp only [Option.map_some]
      rfl
  structured := by
    intro block emitted locals tail
    change (do
      let code ← selector.lowered.code 0
      let fallback ← defaultBody.emit
      let dispatch ← arms.emit fallback
      pure (Backend.Block.seq (.code code) dispatch)) = some block at emitted
    obtain ⟨code,hs,afterSelector⟩ := Option.bind_eq_some_iff.mp emitted
    obtain ⟨defaultBlock,hd,afterDefault⟩ := Option.bind_eq_some_iff.mp afterSelector
    obtain ⟨dispatch,hc,finished⟩ := Option.bind_eq_some_iff.mp afterDefault
    change some (Backend.Block.seq (.code code) dispatch) = some block at finished
    have same : Backend.Block.seq (.code code) dispatch = block := Option.some.inj finished
    subst block
    have selected := selector.lowered.correct 0 code hs locals #v[] tail
    simp only [Vector.toList_empty,List.nil_append] at selected
    have dispatched := arms.structured defaultBody defaultBlock hd
      dispatch hc (selector.value locals) locals tail
    have joined := StructuredExec.seq (.code selected) dispatched
    cases chosen : arms.choose (selector.value locals) locals with
    | none => simpa only [chosen,Option.getD_none] using joined
    | some updated => simpa only [chosen,Option.getD_some] using joined


mutual
/-- Concrete mutually recursive visitor on original statements and cases.
Only actual constructed source/target certificates can be returned. -/
def compile {c n} (fuel : Nat) (stmt : Stmt [] [] c n) : Option (Compiled fuel stmt) :=
  match fuel with
  | 0 => none
  | fuel+1 => by
      apply Stmt.casesOn (motive_1 := fun F X c n stmt =>
        match F,X with
        | [],[] => Option (Compiled (fuel+1) stmt)
        | _,_ => Unit) stmt
      case seq =>
        intro F X c n a b
        cases F <;> cases X
        · exact do pure (sequence (← compile fuel a) (← compile fuel b))
        all_goals exact ()
      case if_ =>
        intro F X c n test body
        cases F <;> cases X
        · exact do pure (branch (← PureExpressions.compile fuel test) (← compile fuel body))
        all_goals exact ()
      case let_ =>
        intro F X c n r rhs body
        cases F <;> cases X
        · cases r with
          | zero => exact none
          | succ r =>
            cases r with
            | zero => exact do pure (letOne (← PureExpressions.compile fuel rhs) (← compile fuel body))
            | succ _ => exact none
        all_goals exact ()
      case zero =>
        intro F X c n fresh body
        cases F <;> cases X
        · exact (compile fuel body).map (zero fresh)
        all_goals exact ()
      case switch =>
        intro F X c n expression cases fallback
        cases F <;> cases X
        · exact do pure (dispatch (← PureExpressions.compile fuel expression)
            (← compileArms fuel cases) (← compile fuel fallback))
        all_goals exact ()
      all_goals intro F X; cases F <;> cases X <;> intros <;>
        first | exact (ScopedSwitch.compile (fuel+1) _).map ofScoped | exact ()
termination_by structural fuel

def compileArms {c n} (fuel : Nat) (cases : Cases [] [] c n) : Option (CompiledCases fuel cases) :=
  match fuel with
  | 0 => none
  | fuel+1 => by
      apply Cases.casesOn (motive_2 := fun F X c n cases =>
        match F,X with
        | [],[] => Option (CompiledCases (fuel+1) cases)
        | _,_ => Unit) cases
      case nil => intro F X c n; cases F <;> cases X
                  · exact some (NestedSwitch.nil fuel c n)
                  all_goals exact ()
      case cons =>
        intro F X c n value body rest
        cases F <;> cases X
        · exact do pure (NestedSwitch.cons (← compile fuel body) (← compileArms fuel rest))
        all_goals exact ()
termination_by structural fuel
end

/-- info: 'SolidityBridge.Yul.NestedSwitch.sequence' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms sequence
/-- info: 'SolidityBridge.Yul.NestedSwitch.branch' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms branch
/-- info: 'SolidityBridge.Yul.NestedSwitch.letOne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms letOne
/-- info: 'SolidityBridge.Yul.NestedSwitch.zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms zero
/-- info: 'SolidityBridge.Yul.NestedSwitch.nil' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms nil
/-- info: 'SolidityBridge.Yul.NestedSwitch.cons' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cons
/-- info: 'SolidityBridge.Yul.NestedSwitch.dispatch' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms dispatch
/-- info: 'SolidityBridge.Yul.NestedSwitch.compile' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms compile
/-- info: 'SolidityBridge.Yul.NestedSwitch.compileArms' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms compileArms
end SolidityBridge.Yul.NestedSwitch
