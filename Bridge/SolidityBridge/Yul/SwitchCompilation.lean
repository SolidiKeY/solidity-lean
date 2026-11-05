import SolidityBridge.Yul.RecursiveScopes
/-! Original Yul switch compilation: evaluate the selector once, retain its
full word while comparing case labels, retire it before the chosen body or
fallback. Existing source cases, scoped body compiler and target blocks are
reused. Depth-zero/model component only; no admission/native/G24 claim. -/
namespace SolidityBridge.Yul.SwitchCompilation
open Solidity Backend Scalar Selection
open Solidity.Yul Solidity.Yul.Closed Solidity.Yul.Compilation

def labelWord (label : Solidity.Yul.Word) : Scalar.Word := BitVec.ofFin label

def compareCode (label : Solidity.Yul.Word) : Backend.Program :=
  [pushWord (labelWord label),.op (.DUP ⟨1,by decide⟩),.op .EQ]

inductive Arms (c : Control) (n : Nat) : Nat → Cases [] [] c n → Type where
  | nil (fuel : Nat) : Arms c n (fuel+1) .nil
  | cons {fuel value body rest} (arm : RecursiveScopes.Derivation c n fuel body)
      (suffix : Arms c n fuel rest) : Arms c n (fuel+1) (.cons value body rest)

def Arms.profile {c n fuel cases} (compiled : Arms c n fuel cases) : CasesWordP cases := by
  apply Arms.casesOn (motive := fun _ cases _ => CasesWordP cases) compiled
  case nil => intro fuel; exact True.intro
  case cons => intro fuel value body rest arm suffix; exact ⟨arm.profile,suffix.profile⟩
termination_by structural compiled

def Arms.choose {c n fuel cases} (compiled : Arms c n fuel cases) :
    Scalar.Word → Vector Scalar.Word n → Option (Vector Scalar.Word n) := by
  apply Arms.casesOn (motive := fun _ _ _ =>
    Scalar.Word → Vector Scalar.Word n → Option (Vector Scalar.Word n)) compiled
  case nil => intro fuel selector locals; exact none
  case cons =>
    intro fuel value body rest arm suffix selector locals
    exact if selector.toFin = value then some (arm.update locals) else suffix.choose selector locals
termination_by structural compiled

def Arms.emit {c n fuel cases} (compiled : Arms c n fuel cases) (fallback : Backend.Block) :
    Option Backend.Block := by
  apply Arms.casesOn (motive := fun _ _ _ => Option Backend.Block) compiled
  case nil => intro fuel; exact some (.seq (.code [.op .POP]) fallback)
  case cons =>
    intro fuel value body rest arm suffix
    exact do
      let body ← arm.emit
      let rest ← suffix.emit fallback
      pure (.ite (compareCode value) (.seq (.code [.op .POP]) body) rest)
termination_by structural compiled

def compileArms {c n} (fuel : Nat) (cases : Cases [] [] c n) : Option (Arms c n fuel cases) :=
  match fuel with
  | 0 => none
  | fuel+1 => by
      apply Cases.casesOn (motive_2 := fun F X c n cases =>
        match F,X with
        | [],[] => Option (Arms c n (fuel+1) cases)
        | _,_ => Unit) cases
      case nil => intro F X c n; cases F <;> cases X
                  · exact some (.nil fuel)
                  all_goals exact ()
      case cons =>
        intro F X c n value body rest
        cases F <;> cases X
        · exact do pure (.cons (← RecursiveScopes.compile fuel body) (← compileArms fuel rest))
        all_goals exact ()
termination_by structural fuel

structure Compiled {c n fuel} (expression : Expr [] [] n 1) (cases : Cases [] [] c n)
    (fallback : Stmt [] [] c n) where
  selector : ProducerExpressions.Compiled fuel expression
  arms : Arms c n fuel cases
  defaultBody : RecursiveScopes.Derivation c n fuel fallback

def Compiled.profile {c n fuel expression cases fallback}
    (compiled : @Compiled c n fuel expression cases fallback) :
    StmtWordP (.switch expression cases fallback) :=
  ⟨compiled.selector.profile,compiled.arms.profile,compiled.defaultBody.profile⟩

def Compiled.update {c n fuel expression cases fallback}
    (compiled : @Compiled c n fuel expression cases fallback) (locals : Vector Scalar.Word n) :
    Vector Scalar.Word n :=
  match compiled.arms.choose (compiled.selector.value locals) locals with
  | some updated => updated
  | none => compiled.defaultBody.update locals

def Compiled.emit {c n fuel expression cases fallback}
    (compiled : @Compiled c n fuel expression cases fallback) : Option Backend.Block := do
  let selector ← compiled.selector.lowered.code 0
  let fallback ← compiled.defaultBody.emit
  let dispatch ← compiled.arms.emit fallback
  pure (.seq (.code selector) dispatch)

def compile {c n} (fuel : Nat) (expression : Expr [] [] n 1) (cases : Cases [] [] c n)
    (fallback : Stmt [] [] c n) : Option (@Compiled c n fuel expression cases fallback) := do
  pure ⟨← PureExpressions.compile fuel expression,← compileArms fuel cases,
    ← RecursiveScopes.compile fuel fallback⟩

/-- Actual PUSH/DUP2/EQ execution retains the original selector. -/
theorem compare_run :
∀ (label : Solidity.Yul.Word) (selector : Scalar.Word) (tail : Scalar.Stack),
 Scalar.run (compareCode label) (selector :: tail) =
 some ((if selector.toFin = label then 1 else 0) :: selector :: tail) := by
  intro label selector tail
  simp only [compareCode,Scalar.run,Scalar.step_pushWord,Option.bind_some]
  change some (Scalar.flag (selector == labelWord label) :: selector :: tail) = _
  by_cases same : selector.toFin = label
  · have words : selector = labelWord label := BitVec.eq_of_toFin_eq same
    rw [words]
    simp only [labelWord,BitVec.toFin_ofFin,beq_self_eq_true,Scalar.flag,ite_true]
  · have words : selector ≠ labelWord label := fun h => same (congrArg BitVec.toFin h)
    simp only [beq_eq_false_iff_ne.mpr words,Scalar.flag,Bool.false_eq_true,ite_false,if_neg same]

/-- Actual case evaluation/dispatch, retaining real producer horizons and caller tails. -/
theorem Arms.source :
∀ {c : Control} {n fuel : Nat} {cases : Cases [] [] c n}
 (compiled : Arms c n fuel cases) (selector : Scalar.Word) (locals : Vector Scalar.Word n),
 evalCases fuel .nil True.intro cases compiled.profile selector.toFin
   (ProducerExpressions.sourceLocals locals) =
 some ((compiled.choose selector locals).map
   (fun out => (⟨ProducerExpressions.sourceLocals out,.normal⟩ : Outcome c n))) := by
  intro c n fuel cases compiled selector locals
  induction compiled with
  | nil fuel => rfl
  | @cons fuel value body rest arm suffix ih =>
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
    · rw [if_neg same,ih]
      simp only [if_neg same]

/-- Actual case evaluation/dispatch, retaining real producer horizons and caller tails. -/
theorem Arms.structured :
∀ {c : Control} {n fuel : Nat} {cases : Cases [] [] c n}
 (compiled : Arms c n fuel cases) {defaultFuel : Nat} {fallback : Stmt [] [] c n}
 (defaultBody : RecursiveScopes.Derivation c n defaultFuel fallback) (fallbackBlock : Backend.Block),
 defaultBody.emit = some fallbackBlock → ∀ (block : Backend.Block),
 compiled.emit fallbackBlock = some block →
 ∀ (selector : Scalar.Word) (locals : Vector Scalar.Word n) (tail : Scalar.Stack),
 StructuredExec block (selector :: (locals.toList ++ tail))
   (((compiled.choose selector locals).getD (defaultBody.update locals)).toList ++ tail) := by
  intro c n fuel cases compiled defaultFuel fallback defaultBody fallbackBlock defaultEmitted
  intro block emitted selector locals tail
  induction compiled generalizing block with
  | nil fuel =>
    change some (Backend.Block.seq (.code [.op .POP]) fallbackBlock) = some block at emitted
    cases emitted
    exact StructuredExec.seq (.code rfl) (defaultBody.structured fallbackBlock defaultEmitted locals tail)
  | @cons fuel value body rest arm suffix ih =>
    change (do
      let b ← arm.emit
      let r ← suffix.emit fallbackBlock
      pure (Backend.Block.ite (compareCode value) (.seq (.code [.op .POP]) b) r)) = some block at emitted
    cases hb : arm.emit with
    | none => simp only [hb] at emitted; cases emitted
    | some b =>
      cases hr : suffix.emit fallbackBlock with
      | none => simp only [hb,hr] at emitted; cases emitted
      | some r =>
        simp only [hb,hr] at emitted
        cases emitted
        change StructuredExec (.ite (compareCode value) (.seq (.code [.op .POP]) b) r)
          (selector :: (locals.toList ++ tail))
          (((if selector.toFin = value then some (arm.update locals)
            else suffix.choose selector locals).getD (defaultBody.update locals)).toList ++ tail)
        by_cases same : selector.toFin = value
        · rw [if_pos same]
          apply StructuredExec.iteTrue (w:=1)
          · simpa only [if_pos same] using compare_run value selector (locals.toList ++ tail)
          · decide
          · exact StructuredExec.seq (.code rfl) (arm.structured b hb locals tail)
        · rw [if_neg same]
          exact StructuredExec.iteFalse
            (by simpa only [if_neg same] using compare_run value selector (locals.toList ++ tail))
            (ih r hr)

/-- Exact whole-switch composition from actual source/target producer facts. -/
theorem Compiled.source :
∀ {c : Control} {n fuel : Nat} {expression : Expr [] [] n 1}
 {cases : Cases [] [] c n} {fallback : Stmt [] [] c n}
 (compiled : @Compiled c n fuel expression cases fallback) (locals : Vector Scalar.Word n),
 evalStmt (fuel+1) .nil True.intro (.switch expression cases fallback) compiled.profile
   (ProducerExpressions.sourceLocals locals) =
 some ⟨ProducerExpressions.sourceLocals (compiled.update locals),.normal⟩ := by
  intro c n fuel expression cases fallback compiled locals
  change (do
    let value ← evalExpr fuel .nil True.intro expression compiled.selector.profile (ProducerExpressions.sourceLocals locals)
    let result ← evalCases fuel .nil True.intro cases compiled.arms.profile (value 0) (ProducerExpressions.sourceLocals locals)
    match result with
    | some out => pure out
    | none => evalStmt fuel .nil True.intro fallback compiled.defaultBody.profile (ProducerExpressions.sourceLocals locals)) = _
  rw [compiled.selector.source]
  change (do
    let result ← evalCases fuel .nil True.intro cases compiled.arms.profile
      (compiled.selector.value locals).toFin (ProducerExpressions.sourceLocals locals)
    match result with
    | some out => pure out
    | none => evalStmt fuel .nil True.intro fallback compiled.defaultBody.profile (ProducerExpressions.sourceLocals locals)) = _
  rw [compiled.arms.source]
  cases chosen : compiled.arms.choose (compiled.selector.value locals) locals with
  | none =>
    simp only [Option.map_none]
    change _ = some (⟨ProducerExpressions.sourceLocals
      (match compiled.arms.choose (compiled.selector.value locals) locals with
       | some updated => updated | none => compiled.defaultBody.update locals),.normal⟩ : Outcome c n)
    rw [chosen]
    exact compiled.defaultBody.source locals
  | some updated =>
    simp only [Option.map_some]
    change _ = some (⟨ProducerExpressions.sourceLocals
      (match compiled.arms.choose (compiled.selector.value locals) locals with
       | some updated => updated | none => compiled.defaultBody.update locals),.normal⟩ : Outcome c n)
    rw [chosen]
    rfl

/-- Exact whole-switch composition from actual source/target producer facts. -/
theorem Compiled.structured :
∀ {c : Control} {n fuel : Nat} {expression : Expr [] [] n 1}
 {cases : Cases [] [] c n} {fallback : Stmt [] [] c n}
 (compiled : @Compiled c n fuel expression cases fallback) (block : Backend.Block),
 compiled.emit = some block → ∀ (locals : Vector Scalar.Word n) (tail : Scalar.Stack),
 StructuredExec block (locals.toList ++ tail) ((compiled.update locals).toList ++ tail) := by
  intro c n fuel expression cases fallback compiled block emitted locals tail
  unfold Compiled.emit at emitted
  obtain ⟨code,hs,afterSelector⟩ := Option.bind_eq_some_iff.mp emitted
  obtain ⟨defaultBlock,hd,afterDefault⟩ := Option.bind_eq_some_iff.mp afterSelector
  obtain ⟨dispatch,hc,finished⟩ := Option.bind_eq_some_iff.mp afterDefault
  change some (Backend.Block.seq (.code code) dispatch) = some block at finished
  have same : Backend.Block.seq (.code code) dispatch = block := Option.some.inj finished
  subst block
  have selected := compiled.selector.lowered.correct 0 code hs locals #v[] tail
  simp only [Vector.toList_empty,List.nil_append] at selected
  have dispatched := compiled.arms.structured compiled.defaultBody defaultBlock hd
    dispatch hc (compiled.selector.value locals) locals tail
  have joined := StructuredExec.seq (.code selected) dispatched
  cases chosen : compiled.arms.choose (compiled.selector.value locals) locals with
  | none => simpa only [Compiled.update,chosen,Option.getD_none] using joined
  | some updated => simpa only [Compiled.update,chosen,Option.getD_some] using joined

/-- info: 'SolidityBridge.Yul.SwitchCompilation.compare_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms compare_run
/-- info: 'SolidityBridge.Yul.SwitchCompilation.Arms.source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Arms.source
/-- info: 'SolidityBridge.Yul.SwitchCompilation.Arms.structured' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Arms.structured
/-- info: 'SolidityBridge.Yul.SwitchCompilation.Compiled.source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Compiled.source
/-- info: 'SolidityBridge.Yul.SwitchCompilation.Compiled.structured' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Compiled.structured
end SolidityBridge.Yul.SwitchCompilation
