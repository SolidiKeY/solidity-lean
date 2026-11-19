import Solidity.Yul.Compilation.WhileWordExecution
import Solidity.Yul.Compilation.ProducerStatements
import Solidity.Yul.Compilation.CompletionControls
import Solidity.Yul.ClosedHorizon
/-! Finite original Yul loop-phase completion and matching compiled model loop.
Actual intrinsic condition/body/post compiler certificates supply all component
laws. Reached guards and a stopping guard are real explicit premises, not a
termination oracle or a substitute for full source/G24/native adequacy. -/
namespace Solidity.Yul.Compilation.SourceLoop
open Backend Scalar MachineAdapter Solidity.Yul.Closed
open ProducerExpressions

variable {c : Solidity.Yul.Control} {n fc fp fb : Nat}
 {test : Solidity.Yul.Expr [] [] n 1}
 {step : Solidity.Yul.Stmt [] [] ⟨c.function,false⟩ n}
 {work : Solidity.Yul.Stmt [] [] ⟨c.function,true⟩ n}

/-- Actual component contracts and shared sequence transport in both directions. -/
abbrev SourceModel {c : Control} {n : Nat} (stmt : Stmt [] [] c n)
 (profile : StmtWordP stmt) (code : List Evm.Instr) (m : Evm.Machine) (caller : List Evm.Word) :=
 ∀ (horizon : Nat) (locals : Vector Scalar.Word n) (result : Outcome c n),
 evalStmt horizon .nil True.intro stmt profile (sourceLocals locals) = some result →
 ∃ out : Vector Scalar.Word n, result = ⟨sourceLocals out,.normal⟩ ∧
 Evm.run code {m with stack := locals.toList.map coreWord++caller} =
 .ok {m with stack := out.toList.map coreWord++caller} 0

theorem seq_forward {c : Control} {n : Nat} {a b : Stmt [] [] c n}
 (leftProfile : StmtWordP a) (rightProfile : StmtWordP b) (qa qb : List Evm.Instr)
 (m : Evm.Machine) (caller : List Evm.Word)
 (leftLaw : SourceModel a leftProfile qa m caller) (rightLaw : SourceModel b rightProfile qb m caller) :
 SourceModel (.seq a b) ⟨leftProfile,rightProfile⟩ (qa++qb) m caller := by
 intro horizon locals result ran
 cases horizon with
 | zero => cases ran
 | succ horizon =>
   change Option.bind (evalStmt horizon .nil True.intro _ leftProfile (sourceLocals locals)) _ = some result at ran
   obtain ⟨middle,first,remaining⟩ := Option.bind_eq_some_iff.mp ran
   obtain ⟨mid,same,firstRun⟩ := leftLaw horizon locals middle first
   subst middle
   change evalStmt horizon .nil True.intro _ rightProfile (sourceLocals mid) = some result at remaining
   obtain ⟨out,same,lastRun⟩ := rightLaw horizon mid result remaining
   refine ⟨out,same,?_⟩
   rw [Evm.run_append_ok firstRun]
   exact lastRun

abbrev ModelSource {c : Control} {n : Nat} (stmt : Stmt [] [] c n)
 (profile : StmtWordP stmt) (code : List Evm.Instr) (caller : List Evm.Word) :=
 ∀ (locals : Vector Scalar.Word n) (m final : Evm.Machine) (skip : Nat),
 Evm.run code {m with stack := locals.toList.map coreWord++caller} = .ok final skip →
 ∃ (horizon : Nat) (out : Vector Scalar.Word n),
 evalStmt horizon .nil True.intro stmt profile (sourceLocals locals) = some ⟨sourceLocals out,.normal⟩ ∧
 skip = 0 ∧ final = {m with stack := out.toList.map coreWord++caller}

theorem seq_reflect {c : Control} {n : Nat} {a b : Stmt [] [] c n}
 (leftProfile : StmtWordP a) (rightProfile : StmtWordP b) (qa qb : List Evm.Instr)
 (caller : List Evm.Word)
 (leftLaw : ModelSource a leftProfile qa caller) (rightLaw : ModelSource b rightProfile qb caller) :
 ModelSource (.seq a b) ⟨leftProfile,rightProfile⟩ (qa++qb) caller := by
 intro locals m final skip ran
 have whole : (Evm.run qa {m with stack := locals.toList.map coreWord++caller}).bind
   (fun mid pending => Evm.exec qb pending mid) = .ok final skip := by
   simpa only [Evm.run,Evm.exec_append] using ran
 cases actual : Evm.run qa {m with stack := locals.toList.map coreWord++caller} with
 | revert => rw [actual] at whole; cases whole
 | fault => rw [actual] at whole; cases whole
 | ok mid pending =>
   obtain ⟨lo,intermediate,leftSource,done,frame⟩ := leftLaw locals m mid pending actual
   rw [actual,done,frame] at whole
   change Evm.run qb {m with stack := intermediate.toList.map coreWord++caller} = .ok final skip at whole
   obtain ⟨hi,out,rightSource,done,frame⟩ := rightLaw intermediate m final skip whole
   have first : evalStmt (max lo hi) .nil True.intro _ leftProfile (sourceLocals locals) =
     some ⟨sourceLocals intermediate,.normal⟩ := CompletionControls.completed_horizon
     (fun fuel => evalStmt fuel .nil True.intro _ leftProfile (sourceLocals locals))
     (fun fuel extra => evalStmt_refines_add fuel extra .nil True.intro _ leftProfile (sourceLocals locals))
     (Nat.le_max_left lo hi) leftSource
   have last : evalStmt (max lo hi) .nil True.intro _ rightProfile (sourceLocals intermediate) =
     some ⟨sourceLocals out,.normal⟩ := CompletionControls.completed_horizon
     (fun fuel => evalStmt fuel .nil True.intro _ rightProfile (sourceLocals intermediate))
     (fun fuel extra => evalStmt_refines_add fuel extra .nil True.intro _ rightProfile (sourceLocals intermediate))
     (Nat.le_max_right lo hi) rightSource
   have source : evalStmt (max lo hi+1) .nil True.intro (.seq a b)
       ⟨leftProfile,rightProfile⟩ (sourceLocals locals) = some ⟨sourceLocals out,.normal⟩ := by
     change Option.bind (evalStmt (max lo hi) .nil True.intro a leftProfile (sourceLocals locals)) _ = _
     rw [first]
     exact last
   exact ⟨max lo hi+1,out,source,done,frame⟩

/-- Existing component updates composed in the actual Yul body-then-post order. -/
abbrev next (body : ProducerStatements.Compiled fb work) (post : ProducerStatements.Compiled fp step) :
 Vector Scalar.Word n → Vector Scalar.Word n := fun locals => post.update (body.update locals)

private theorem repeat_shift {α : Type} (f : α → α) (count : Nat) (a : α) :
 Nat.repeat f count (f a) = Nat.repeat f (count+1) a :=
  WhileWordExecution.repeat_shift f count a

/-- The SOURCE horizon is constructed from the component horizons and actual
finite turn count. It is not a proof/fuel-budget increase or an assertion that
the loop terminates on other inputs. All source control indices stay original. -/
theorem finite (condition : ProducerExpressions.Compiled fc test)
 (post : ProducerStatements.Compiled fp step) (body : ProducerStatements.Compiled fb work)
 (count : Nat) (locals : Vector Scalar.Word n)
 (running : ∀ j, j < count → condition.value (Nat.repeat (next body post) j locals) ≠ 0)
 (stopped : condition.value (Nat.repeat (next body post) count locals) = 0) :
 evalLoop (c := c) (max fc (max fp fb)+count+1) .nil True.intro
  test condition.profile step post.profile work body.profile (sourceLocals locals) =
 some ⟨sourceLocals (Nat.repeat (next body post) count locals),.normal⟩ := by
 have hc : fc ≤ max fc (max fp fb) := Nat.le_max_left _ _
 have hp : fp ≤ max fc (max fp fb) := Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)
 have hb : fb ≤ max fc (max fp fb) := Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)
 induction count generalizing locals with
 | zero =>
   change condition.value locals = 0 at stopped
   have tested := evalExpr_stable hc .nil True.intro test condition.profile (sourceLocals locals) (condition.source locals)
   rewrite [evalLoop,tested]
   change (if (condition.value locals).toNat = 0 then _ else _) = _
   have zero : (condition.value locals).toNat = 0 := congrArg BitVec.toNat stopped
   rewrite [if_pos zero]
   rfl
 | succ count ih =>
   have nonzero : condition.value locals ≠ 0 := running 0 (by omega)
   have runningNext : ∀ j, j < count → condition.value (Nat.repeat (next body post) j (next body post locals)) ≠ 0 := by
     intro j bound
     rewrite [repeat_shift]
     exact running (j+1) (by omega)
   have stoppedNext : condition.value (Nat.repeat (next body post) count (next body post locals)) = 0 := by
     rewrite [repeat_shift]
     exact stopped
   have completed := ih (next body post locals) runningNext stoppedNext
   have tested := evalExpr_stable (show fc ≤ max fc (max fp fb)+count+1 by omega)
     .nil True.intro test condition.profile (sourceLocals locals) (condition.source locals)
   have worked := evalStmt_stable (show fb ≤ max fc (max fp fb)+count+1 by omega)
     .nil True.intro work body.profile (sourceLocals locals) (body.source locals)
   have stepped := evalStmt_stable (show fp ≤ max fc (max fp fb)+count+1 by omega)
     .nil True.intro step post.profile (sourceLocals (body.update locals)) (post.source (body.update locals))
   change evalLoop (c := c) (max fc (max fp fb)+count+1+1) .nil True.intro
    test condition.profile step post.profile work body.profile (sourceLocals locals) = _
   rewrite [evalLoop,tested]
   change (if (condition.value locals).toNat = 0 then _ else _) = _
   have nz : (condition.value locals).toNat ≠ 0 := fun h => nonzero (BitVec.eq_of_toNat_eq h)
   change applyStmtRun (evalStmtNode (max fc (max fp fb)+count+1) work) .nil True.intro
    body.profile (sourceLocals locals) = some ⟨sourceLocals (body.update locals),.normal⟩ at worked
   change applyStmtRun (evalStmtNode (max fc (max fp fb)+count+1) step) .nil True.intro
    post.profile (sourceLocals (body.update locals)) =
      some ⟨sourceLocals (post.update (body.update locals)),.normal⟩ at stepped
   rewrite [if_neg nz,worked]
   change Option.bind (applyStmtRun (evalStmtNode (max fc (max fp fb)+count+1) step)
    .nil True.intro post.profile (sourceLocals (body.update locals))) _ = _
   rewrite [stepped]
   simpa only [Option.bind_some,repeat_shift] using completed

/-- Actual finite source-loop completion transports through concrete body and
post execution laws. The original horizon and body-before-post order are kept. -/
theorem finite_components (condition : ProducerExpressions.Compiled fc test)
 (postProfile : StmtWordP step) (bodyProfile : StmtWordP work)
 (postCode bodyCode : List Evm.Instr) (p : Backend.Program) (q : List Evm.Instr)
 (emitted : condition.lowered.code 0 = some p) (selected : WordMachine.selectCode p = some q)
 (m : Evm.Machine) (caller : List Evm.Word)
 (postLaw : ∀ (horizon : Nat) (locals : Vector Scalar.Word n) (result : Outcome ⟨c.function,false⟩ n),
   evalStmt horizon .nil True.intro step postProfile (sourceLocals locals) = some result →
   ∃ out : Vector Scalar.Word n, result = ⟨sourceLocals out,.normal⟩ ∧
   Evm.run postCode {m with stack := locals.toList.map coreWord++caller} =
     .ok {m with stack := out.toList.map coreWord++caller} 0)
 (bodyLaw : ∀ (horizon : Nat) (locals : Vector Scalar.Word n) (result : Outcome ⟨c.function,true⟩ n),
   evalStmt horizon .nil True.intro work bodyProfile (sourceLocals locals) = some result →
   ∃ out : Vector Scalar.Word n, result = ⟨sourceLocals out,.normal⟩ ∧
   Evm.run bodyCode {m with stack := locals.toList.map coreWord++caller} =
     .ok {m with stack := out.toList.map coreWord++caller} 0)
 (horizon : Nat) (locals : Vector Scalar.Word n) (result : Outcome c n)
 (ran : evalLoop horizon .nil True.intro test condition.profile step postProfile
   work bodyProfile (sourceLocals locals) = some result) :
 ∃ out : Vector Scalar.Word n, result = ⟨sourceLocals out,.normal⟩ ∧
 Evm.loopIterN (Evm.run q) (Evm.run (bodyCode++postCode)) horizon
   {m with stack := locals.toList.map coreWord++caller} =
 .inr (.ok {m with stack := out.toList.map coreWord++caller} 0) := by
 induction horizon generalizing locals result with
 | zero => cases ran
 | succ horizon ih =>
   change Option.bind (evalExpr horizon .nil True.intro test condition.profile (sourceLocals locals)) _ = some result at ran
   obtain ⟨values,tested,remaining⟩ := Option.bind_eq_some_iff.mp ran
   have same := evalExpr_completed_unique .nil True.intro test condition.profile (sourceLocals locals)
     tested (condition.source locals)
   subst values
   change (if (condition.value locals).toNat = 0 then
     some (⟨sourceLocals locals,.normal⟩ : Outcome c n) else _) = some result at remaining
   have testedTarget : Evm.run q {m with stack := locals.toList.map coreWord++caller} =
     .ok {m with stack := coreWord (condition.value locals)::(locals.toList.map coreWord++caller)} 0 := by
     simpa only [Vector.toList_empty,List.nil_append] using
       WordExecution.loweredExpr_machine condition.lowered 0 p q emitted selected locals #v[] m caller
   by_cases zero : condition.value locals = 0
   · have zn : (condition.value locals).toNat = 0 := congrArg BitVec.toNat zero
     rw [if_pos zn] at remaining
     refine ⟨locals,(Option.some.inj remaining).symm,?_⟩
     rw [Evm.loopIterN,Evm.loopTurn,testedTarget,zero]
     rfl
   · have nz : (condition.value locals).toNat ≠ 0 := fun h => zero (BitVec.eq_of_toNat_eq h)
     rw [if_neg nz] at remaining
     change Option.bind (evalStmt horizon .nil True.intro work bodyProfile (sourceLocals locals)) _ = some result at remaining
     obtain ⟨afterBody,bodySource,remaining⟩ := Option.bind_eq_some_iff.mp remaining
     obtain ⟨mid,same,bodyTarget⟩ := bodyLaw horizon locals afterBody bodySource
     subst afterBody
     change Option.bind (evalStmt horizon .nil True.intro step postProfile (sourceLocals mid)) _ = some result at remaining
     obtain ⟨afterPost,postSource,remaining⟩ := Option.bind_eq_some_iff.mp remaining
     obtain ⟨next,same,postTarget⟩ := postLaw horizon mid afterPost postSource
     subst afterPost
     change evalLoop horizon .nil True.intro test condition.profile step postProfile
       work bodyProfile (sourceLocals next) = some result at remaining
     obtain ⟨out,same,completed⟩ := ih next result remaining
     have iteration : Evm.run (bodyCode++postCode) {m with stack := locals.toList.map coreWord++caller} =
       .ok {m with stack := next.toList.map coreWord++caller} 0 := by
       rw [Evm.run_append_ok bodyTarget]
       exact postTarget
     refine ⟨out,same,?_⟩
     rw [Evm.loopIterN,Evm.loopTurn,testedTarget]
     change (match (if (condition.value locals).toNat = 0 then
       .inr (.ok {m with stack := locals.toList.map coreWord++caller} 0)
       else match Evm.run (bodyCode++postCode) {m with stack := locals.toList.map coreWord++caller} with
        | .ok updated 0 => .inl updated
        | .ok _ (_+1) => .inr .fault
        | result => .inr result : Evm.Machine ⊕ Evm.Out) with
      | .inl updated => Evm.loopIterN (Evm.run q) (Evm.run (bodyCode++postCode)) horizon updated
      | .inr result => .inr result) = _
     rw [if_neg nz,iteration]
     exact completed

/-- A genuine original for with skip initialization reduces to its existing
loop phase. This changes no source evaluator or control-flow observation. -/
theorem for_skip (fuel : Nat) (condition : ProducerExpressions.Compiled fc test)
 (post : ProducerStatements.Compiled fp step) (body : ProducerStatements.Compiled fb work)
 (vars : Values n) :
 evalStmt (fuel+2) .nil True.intro (Solidity.Yul.Stmt.for_ (c := c) .skip test step work)
  ⟨True.intro,condition.profile,post.profile,body.profile⟩ vars =
 evalLoop (c := c) (fuel+1) .nil True.intro test condition.profile step post.profile work body.profile vars := rfl

/-- Exact finite original for completion; no full-language admission follows. -/
theorem for_finite (condition : ProducerExpressions.Compiled fc test)
 (post : ProducerStatements.Compiled fp step) (body : ProducerStatements.Compiled fb work)
 (count : Nat) (locals : Vector Scalar.Word n)
 (running : ∀ j, j < count → condition.value (Nat.repeat (next body post) j locals) ≠ 0)
 (stopped : condition.value (Nat.repeat (next body post) count locals) = 0) :
 evalStmt (max fc (max fp fb)+count+2) .nil True.intro
  (Solidity.Yul.Stmt.for_ (c := c) .skip test step work) ⟨True.intro,condition.profile,post.profile,body.profile⟩
  (sourceLocals locals) = some ⟨sourceLocals (Nat.repeat (next body post) count locals),.normal⟩ := by
 rewrite [for_skip _ condition post body]
 exact finite condition post body count locals running stopped

/-- Source and target agree at the same actual finite turn sequence. Actual
emission/selection equations and reached guards remain explicit, while BOTH
source completion and model execution are proved from concrete components. -/
theorem source_model (condition : ProducerExpressions.Compiled fc test)
 (post : ProducerStatements.Compiled fp step) (body : ProducerStatements.Compiled fb work)
 (depth : Nat) (cc bb : Backend.Program) (qc qb : List Evm.Instr)
 (hc : condition.lowered.code depth = some cc)
 (hb : (lowerSeq body.lowered post.lowered).code depth = some bb)
 (sc : WordMachine.selectCode cc = some qc) (sb : WordMachine.selectCode bb = some qb)
 (count : Nat) (locals : Vector Scalar.Word n) (newer : Vector Scalar.Word depth)
 (m : Evm.Machine) (caller : List Evm.Word)
 (running : ∀ j, j < count → condition.value (Nat.repeat (next body post) j locals) ≠ 0)
 (stopped : condition.value (Nat.repeat (next body post) count locals) = 0) :
 (evalStmt (max fc (max fp fb)+count+2) .nil True.intro
  (Solidity.Yul.Stmt.for_ (c := c) .skip test step work) ⟨True.intro,condition.profile,post.profile,body.profile⟩
  (sourceLocals locals) = some ⟨sourceLocals (Nat.repeat (next body post) count locals),.normal⟩) ∧
 Evm.run [.loop qc qb] {m with stack := (newer.toList++locals.toList).map coreWord++caller} =
 .ok {m with stack := (newer.toList++(Nat.repeat (next body post) count locals).toList).map coreWord++caller} 0 := by
 constructor
 · exact for_finite condition post body count locals running stopped
 · have completed := WhileWordExecution.finite condition.lowered (lowerSeq body.lowered post.lowered)
    cc bb qc qb hc hb sc sb count locals newer m caller running stopped
   change (Evm.loopRun (Evm.run qc) (Evm.run qb)
    {m with stack := (newer.toList++locals.toList).map coreWord++caller}).bind
    (fun next pending => Evm.exec [] pending next) = _
   rewrite [Evm.loopRun_of_iterN completed]
   rfl

/-- info: 'Solidity.Yul.Compilation.SourceLoop.finite' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms finite
/-- info: 'Solidity.Yul.Compilation.SourceLoop.for_skip' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms for_skip
/-- info: 'Solidity.Yul.Compilation.SourceLoop.for_finite' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms for_finite
/-- info: 'Solidity.Yul.Compilation.SourceLoop.source_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms source_model

/-- Concrete lowering of this original normal for form reuses the existing
while emitter; source body and post compile in their actual intrinsic controls. -/
def emit (condition : ProducerExpressions.Compiled fc test)
 (post : ProducerStatements.Compiled fp step) (body : ProducerStatements.Compiled fb work)
 (depth : Nat) : Option Backend.Block :=
 lowerWhile condition.lowered (lowerSeq body.lowered post.lowered) depth

/-- Whole emitted/selected artifacts derive the component code equations.
Callers provide actual compiler results and reached guards, not desired source
or target execution. This is finite normal-for correspondence, not admission. -/
theorem compiled_finite (condition : ProducerExpressions.Compiled fc test)
 (post : ProducerStatements.Compiled fp step) (body : ProducerStatements.Compiled fb work)
 (depth : Nat) (block : Backend.Block) (code : List Evm.Instr)
 (emitted : emit condition post body depth = some block)
 (selected : WordControl.blockCode block = some code)
 (count : Nat) (locals : Vector Scalar.Word n) (newer : Vector Scalar.Word depth)
 (m : Evm.Machine) (caller : List Evm.Word)
 (running : ∀ j, j < count → condition.value (Nat.repeat (next body post) j locals) ≠ 0)
 (stopped : condition.value (Nat.repeat (next body post) count locals) = 0) :
 (evalStmt (max fc (max fp fb)+count+2) .nil True.intro
  (Solidity.Yul.Stmt.for_ (c := c) .skip test step work) ⟨True.intro,condition.profile,post.profile,body.profile⟩
  (sourceLocals locals) = some ⟨sourceLocals (Nat.repeat (next body post) count locals),.normal⟩) ∧
 Evm.run code {m with stack := (newer.toList++locals.toList).map coreWord++caller} =
 .ok {m with stack := (newer.toList++(Nat.repeat (next body post) count locals).toList).map coreWord++caller} 0 := by
 change (condition.lowered.code depth).bind (fun cc =>
  (lowerSeq body.lowered post.lowered).code depth |>.map (fun bb => Backend.Block.loop cc (.code bb))) = some block at emitted
 obtain ⟨cc,hc,rest⟩ := Option.bind_eq_some_iff.mp emitted
 obtain ⟨bb,hb,same⟩ := Option.map_eq_some_iff.mp rest
 subst block
 obtain ⟨qc,sc,rest⟩ := Option.bind_eq_some_iff.mp selected
 obtain ⟨qb,sb,same⟩ := Option.map_eq_some_iff.mp rest
 subst code
 exact source_model condition post body depth cc bb qc qb hc hb sc sb count locals newer m caller running stopped

/-- info: 'Solidity.Yul.Compilation.SourceLoop.emit' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms emit
/-- info: 'Solidity.Yul.Compilation.SourceLoop.compiled_finite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms compiled_finite
end Solidity.Yul.Compilation.SourceLoop
