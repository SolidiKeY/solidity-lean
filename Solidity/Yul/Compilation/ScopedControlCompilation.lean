import Solidity.Yul.Compilation.LetScopeCompilation
import Solidity.Yul.Compilation.ZeroLoopScope
import Solidity.Yul.Compilation.FramedBranch
import Solidity.Yul.Compilation.CompletionControls
/-! Original-AST compiler certificates indexed by the varying local context.
Recursive seq/if/zero/single-word let nodes emit existing Backend.Block;
existing concrete LoopControl artifacts are leaves. No alternative source
syntax/state, primitive semantics or runtime calling convention is introduced. -/
namespace Solidity.Yul.Compilation.ScopedControlCompilation
open Backend Scalar MachineAdapter Solidity.Yul.Closed ProducerExpressions

inductive Compiled (c : Control) : {n : Nat} → Nat → Stmt [] [] c n → Type where
 | base {n fuel : Nat} {stmt : Stmt [] [] c n}
     (artifact : LoopControlCompilation.Artifact fuel stmt 0) : Compiled c fuel stmt
 | seq {n fuel : Nat} {a b : Stmt [] [] c n}
     (left : Compiled c fuel a) (right : Compiled c fuel b) : Compiled c (fuel+1) (.seq a b)
 | branch {n fuel : Nat} {test : Expr [] [] n 1} {body : Stmt [] [] c n}
     (condition : ProducerExpressions.Compiled fuel test) (arm : Compiled c fuel body) :
     Compiled c (fuel+1) (.if_ test body)
 | zero {n fuel fresh : Nat} {body : Stmt [] [] c (fresh+n)}
     (scope : Compiled c fuel body) : Compiled c (fuel+1) (.zero fresh body)
 | letOne {n fuel : Nat} {rhs : Expr [] [] n 1} {body : Stmt [] [] c (1+n)}
     (initializer : ProducerExpressions.Compiled fuel rhs) (scope : Compiled c fuel body) :
     Compiled c (fuel+1) (.let_ 1 rhs body)

def Compiled.profile {c n fuel} {stmt : Stmt [] [] c n}
 (compiled : Compiled c fuel stmt) : StmtWordP stmt := by
 apply Compiled.casesOn (motive := fun {n} fuel stmt _ => StmtWordP stmt) compiled
 case base => intro n fuel stmt artifact; exact artifact.compiled.profile
 case seq => intro n fuel a b left right; exact ⟨left.profile,right.profile⟩
 case branch => intro n fuel test body condition arm; exact ⟨condition.profile,arm.profile⟩
 case zero => intro n fuel fresh body scope; exact scope.profile
 case letOne => intro n fuel rhs body initializer scope; exact ⟨initializer.profile,scope.profile⟩
termination_by structural compiled

def Compiled.emit {c n fuel} {stmt : Stmt [] [] c n}
 (compiled : Compiled c fuel stmt) : Option Backend.Block := by
 apply Compiled.casesOn (motive := fun {_} _ _ _ => Option Backend.Block) compiled
 case base => intro n fuel stmt artifact; exact some artifact.block
 case seq =>
   intro n fuel a b left right
   exact do
     let a ← left.emit
     let b ← right.emit
     pure (.seq a b)
 case branch =>
   intro n fuel test body condition arm
   exact do
     let p ← condition.lowered.code 0
     let b ← arm.emit
     pure (.ite p b (.code []))
 case zero =>
   intro n fuel fresh body scope
   exact do
     let b ← scope.emit
     pure (.seq (.code (ZeroLoopScope.entry fresh)) (.seq b (.code (popPrefix fresh))))
 case letOne =>
   intro n fuel rhs body initializer scope
   exact do
     let p ← initializer.lowered.code 0
     let b ← scope.emit
     pure (.seq (.code p) (.seq b (.code (popPrefix 1))))
termination_by structural compiled

/-- Actual intrinsic visitor. Binder recursion changes the context index;
only the existing single-result expression compiler is accepted for let. -/
def compile {c : Control} {n : Nat} (fuel : Nat) (stmt : Stmt [] [] c n) : Option (Compiled c fuel stmt) :=
 match fuel with
 | 0 => none
 | fuel+1 => by
   apply Stmt.casesOn (motive_1 := fun F X c n stmt =>
     match F,X with
     | [],[] => Option (Compiled c (fuel+1) stmt)
     | _,_ => Unit) stmt
   case seq =>
     intro F X c n a b
     cases F <;> cases X
     · exact do
         let left ← compile fuel a
         let right ← compile fuel b
         pure (.seq left right)
     all_goals exact ()
   case if_ =>
     intro F X c n test body
     cases F <;> cases X
     · exact do
         let condition ← PureExpressions.compile fuel test
         let arm ← compile fuel body
         pure (.branch condition arm)
     all_goals exact ()
   case zero =>
     intro F X c n fresh body
     cases F <;> cases X
     · exact (compile fuel body).map Compiled.zero
     all_goals exact ()
   case let_ =>
     intro F X c n arity rhs body
     cases F <;> cases X
     · cases arity with
       | zero => exact none
       | succ rest =>
         cases rest with
         | zero => exact do
             let initializer ← PureExpressions.compile fuel rhs
             let scope ← compile fuel body
             pure (.letOne initializer scope)
         | succ _ => exact none
     all_goals exact ()
   all_goals intro F X; cases F <;> cases X <;> intros <;>
     first | exact (LoopControlCompilation.lower (fuel+1) _ 0).map Compiled.base | exact ()
termination_by structural fuel

structure Artifact {c : Control} {n : Nat} (fuel : Nat) (stmt : Stmt [] [] c n) where
 compiled : Compiled c fuel stmt
 block : Backend.Block
 code : List Evm.Instr
 emitted : compiled.emit = some block
 selected : WordControl.blockCode block = some code

def lower {c : Control} {n : Nat} (fuel : Nat) (stmt : Stmt [] [] c n) : Option (Artifact fuel stmt) := do
 let compiled ← compile fuel stmt
 match emitted : compiled.emit with
 | none => none
 | some block =>
   match selected : WordControl.blockCode block with
   | none => none
   | some code => some ⟨compiled,block,code,emitted,selected⟩

/-- Extract actual selected prefix/body/suffix code from the existing Block
selector; this is an equation decomposition, not an execution assumption. -/
theorem scope_selected (entry exit : Backend.Program) (body : Backend.Block) (code : List Evm.Instr)
 (selected : WordControl.blockCode (.seq (.code entry) (.seq body (.code exit))) = some code) :
 ∃ begin middle finish, WordMachine.selectCode entry = some begin ∧
 WordControl.blockCode body = some middle ∧ WordMachine.selectCode exit = some finish ∧
 code = begin ++ (middle ++ finish) := by
 change (WordMachine.selectCode entry).bind (fun a =>
   (WordControl.blockCode (.seq body (.code exit))).map (fun rest => a++rest)) = some code at selected
 obtain ⟨begin,he,rest⟩ := Option.bind_eq_some_iff.mp selected
 obtain ⟨remaining,hr,same⟩ := Option.map_eq_some_iff.mp rest
 change (WordControl.blockCode body).bind (fun mid => (WordMachine.selectCode exit).map (fun last => mid++last)) = some remaining at hr
 obtain ⟨middle,hm,rest⟩ := Option.bind_eq_some_iff.mp hr
 obtain ⟨finish,hf,last⟩ := Option.map_eq_some_iff.mp rest
 subst remaining
 subst code
 exact ⟨begin,middle,finish,he,hm,hf,rfl⟩

/-- Source completion transported by an actual component proof, with a fixed
machine and caller frame. This is not stored in compiler certificates. -/
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

theorem branch_forward {c : Control} {n fuel : Nat} {test : Expr [] [] n 1} {body : Stmt [] [] c n}
 (condition : ProducerExpressions.Compiled fuel test) (armProfile : StmtWordP body)
 (p : Backend.Program) (q qb : List Evm.Instr)
 (hp : condition.lowered.code 0 = some p) (sq : WordMachine.selectCode p = some q)
 (m : Evm.Machine) (caller : List Evm.Word) (armLaw : SourceModel body armProfile qb m caller) :
 SourceModel (.if_ test body) ⟨condition.profile,armProfile⟩ (MachineControl.branchCode q qb []) m caller := by
 intro horizon locals result ran
 have testedTarget : Evm.run q {m with stack := locals.toList.map coreWord++caller} =
   .ok {m with stack := coreWord (condition.value locals)::(locals.toList.map coreWord++caller)} 0 := by
   simpa only [Vector.toList_empty,List.nil_append] using
     WordExecution.loweredExpr_machine condition.lowered 0 p q hp sq locals #v[] m caller
 cases horizon with
 | zero => cases ran
 | succ horizon =>
   change Option.bind (evalExpr horizon .nil True.intro _ condition.profile (sourceLocals locals)) _ = some result at ran
   obtain ⟨values,tested,remaining⟩ := Option.bind_eq_some_iff.mp ran
   have same := evalExpr_completed_unique .nil True.intro _ condition.profile (sourceLocals locals)
     tested (condition.source locals)
   subst values
   change (if (condition.value locals).toNat = 0 then
     some (⟨sourceLocals locals,.normal⟩ : Outcome _ _)
     else evalStmt horizon .nil True.intro _ armProfile (sourceLocals locals)) = some result at remaining
   by_cases zero : condition.value locals = 0
   · have zn : (condition.value locals).toNat = 0 := congrArg BitVec.toNat zero
     rw [if_pos zn] at remaining
     refine ⟨locals,(Option.some.inj remaining).symm,?_⟩
     rw [MachineControl.branchCode,Evm.run_append_ok testedTarget,zero]
     change Evm.exec qb qb.length {m with stack := locals.toList.map coreWord++caller} = _
     exact Evm.exec_length qb _
   · have nz : (condition.value locals).toNat ≠ 0 := fun h => zero (BitVec.eq_of_toNat_eq h)
     rw [if_neg nz] at remaining
     obtain ⟨out,same,armRun⟩ := armLaw horizon locals result remaining
     refine ⟨out,same,?_⟩
     rw [MachineControl.branchCode,Evm.run_append_ok testedTarget]
     rw [FramedBranch.nonzero_tail (condition.value locals) qb []
       {m with stack := locals.toList.map coreWord++caller} zero]
     exact armRun

theorem zero_forward {c : Control} {n fresh : Nat} {bodyStmt : Stmt [] [] c (fresh+n)}
 (bodyProfile : StmtWordP bodyStmt) (begin middle finish : List Evm.Instr)
 (hs : WordMachine.selectCode (ZeroLoopScope.entry fresh) = some begin)
 (hf : WordMachine.selectCode (popPrefix fresh) = some finish)
 (m : Evm.Machine) (caller : List Evm.Word)
 (bodyLaw : SourceModel bodyStmt bodyProfile middle m caller) :
 SourceModel (.zero fresh bodyStmt) bodyProfile (begin++(middle++finish)) m caller := by
 intro horizon locals result ran
 cases horizon with
 | zero => cases ran
 | succ horizon =>
   change Option.bind (evalStmt horizon .nil True.intro bodyStmt bodyProfile
     (extendValues (fun _ : Fin fresh => word 0) (sourceLocals locals))) _ = some result at ran
   rw [←ZeroLoopScope.initial_values] at ran
   obtain ⟨mid,bodySource,remaining⟩ := Option.bind_eq_some_iff.mp ran
   obtain ⟨out,same,bodyRun⟩ := bodyLaw horizon (Vector.replicate fresh (0 : Scalar.Word) ++ locals) mid bodySource
   subst mid
   have projected : result = ⟨sourceLocals (outerLocals out),.normal⟩ := by
     have same := (Option.some.inj remaining).symm
     rw [←ScopedStatements.locals_outer] at same
     exact same
   have entering := WordExecution.run (ZeroLoopScope.entry fresh) begin hs locals.toList
     ((Vector.replicate fresh (0 : Scalar.Word)).toList++locals.toList) (pushPrefix_run _ _) m caller
   have bodyRun' : Evm.run middle
     {m with stack := ((Vector.replicate fresh (0 : Scalar.Word)).toList++locals.toList).map coreWord++caller} =
     .ok {m with stack := out.toList.map coreWord++caller} 0 := by
     simpa only [Vector.toList_append] using bodyRun
   have exitScalar : Scalar.run (popPrefix fresh) out.toList = some (outerLocals out).toList := by
     simpa only [List.append_nil] using popFresh_run out []
   have exiting := WordExecution.run (popPrefix fresh) finish hf out.toList (outerLocals out).toList exitScalar m caller
   refine ⟨outerLocals out,projected,?_⟩
   rw [Evm.run_append_ok entering,Evm.run_append_ok bodyRun']
   exact exiting

theorem let_forward {c : Control} {n fuel : Nat} {rhs : Expr [] [] n 1} {bodyStmt : Stmt [] [] c (1+n)}
 (initializer : ProducerExpressions.Compiled fuel rhs) (bodyProfile : StmtWordP bodyStmt)
 (p : Backend.Program) (begin middle finish : List Evm.Instr)
 (hp : initializer.lowered.code 0 = some p) (hs : WordMachine.selectCode p = some begin)
 (hf : WordMachine.selectCode (popPrefix 1) = some finish)
 (m : Evm.Machine) (caller : List Evm.Word)
 (bodyLaw : SourceModel bodyStmt bodyProfile middle m caller) :
 SourceModel (.let_ 1 rhs bodyStmt) ⟨initializer.profile,bodyProfile⟩ (begin++(middle++finish)) m caller := by
 intro horizon locals result ran
 cases horizon with
 | zero => cases ran
 | succ horizon =>
   change (do
     let values ← evalExpr horizon .nil True.intro rhs initializer.profile (sourceLocals locals)
     let mid ← evalStmt horizon .nil True.intro bodyStmt bodyProfile (extendValues values (sourceLocals locals))
     pure (⟨dropValues 1 mid.vars,mid.flow⟩ : Outcome c n)) = some result at ran
   obtain ⟨values,tested,rest⟩ := Option.bind_eq_some_iff.mp ran
   have same := evalExpr_completed_unique .nil True.intro rhs initializer.profile (sourceLocals locals)
     tested (initializer.source locals)
   subst values
   rw [LetScopeCompilation.initial_values] at rest
   obtain ⟨mid,bodySource,remaining⟩ := Option.bind_eq_some_iff.mp rest
   obtain ⟨out,same,bodyRun⟩ := bodyLaw horizon (#v[initializer.value locals] ++ locals) mid bodySource
   subst mid
   have projected : result = ⟨sourceLocals (outerLocals out),.normal⟩ := by
     have same := (Option.some.inj remaining).symm
     rw [←ScopedStatements.locals_outer] at same
     exact same
   have initScalar : Scalar.run p locals.toList = some (initializer.value locals :: locals.toList) := by
     simpa only [Vector.toList_empty,List.nil_append,List.append_nil] using
       initializer.lowered.correct 0 p hp locals #v[] []
   have entering := WordExecution.run p begin hs locals.toList (initializer.value locals::locals.toList) initScalar m caller
   have bodyRun' : Evm.run middle
     {m with stack := (initializer.value locals::locals.toList).map coreWord++caller} =
     .ok {m with stack := out.toList.map coreWord++caller} 0 := by
     simpa only [Vector.toList_append,Vector.toList_singleton,List.singleton_append] using bodyRun
   have exitScalar : Scalar.run (popPrefix 1) out.toList = some (outerLocals out).toList := by
     simpa only [List.append_nil] using popFresh_run out []
   have exiting := WordExecution.run (popPrefix 1) finish hf out.toList (outerLocals out).toList exitScalar m caller
   refine ⟨outerLocals out,projected,?_⟩
   rw [Evm.run_append_ok entering,Evm.run_append_ok bodyRun']
   exact exiting

/-- Actual original source completion derives intermediate vectors, selected
arms and binder retirement against the emitted existing compiler Block. -/
theorem source_to_model {c : Control} {n fuel : Nat} {stmt : Stmt [] [] c n}
 (compiled : Compiled c fuel stmt) (block : Backend.Block) (code : List Evm.Instr)
 (emitted : compiled.emit = some block) (selected : WordControl.blockCode block = some code)
 (horizon : Nat) (locals : Vector Scalar.Word n) (result : Outcome c n)
 (ran : evalStmt horizon .nil True.intro stmt compiled.profile (sourceLocals locals) = some result)
 (m : Evm.Machine) (caller : List Evm.Word) :
 ∃ out : Vector Scalar.Word n, result = ⟨sourceLocals out,.normal⟩ ∧
 Evm.run code {m with stack := locals.toList.map coreWord++caller} =
 .ok {m with stack := out.toList.map coreWord++caller} 0 := by
 induction compiled generalizing block code horizon with
 | base artifact =>
   change some artifact.block = some block at emitted
   cases Option.some.inj emitted
   have equal : code = artifact.code := Option.some.inj (selected.symm.trans artifact.selected)
   subst code
   simpa only [Vector.toList_empty,List.nil_append] using
     artifact.source_to_model horizon locals result ran #v[] m caller
 | seq left right ihLeft ihRight =>
   change (left.emit).bind (fun a => (right.emit).bind (fun b => some (Backend.Block.seq a b))) = some block at emitted
   obtain ⟨a,ha,rest⟩ := Option.bind_eq_some_iff.mp emitted
   obtain ⟨b,hb,same⟩ := Option.bind_eq_some_iff.mp rest
   cases Option.some.inj same
   change (WordControl.blockCode a).bind (fun qa => (WordControl.blockCode b).map (fun qb => qa++qb)) = some code at selected
   obtain ⟨qa,sa,rest⟩ := Option.bind_eq_some_iff.mp selected
   obtain ⟨qb,sb,same⟩ := Option.map_eq_some_iff.mp rest
   subst code
   exact seq_forward left.profile right.profile qa qb m caller (ihLeft a qa ha sa) (ihRight b qb hb sb) horizon locals result ran
 | branch condition arm ih =>
   change (condition.lowered.code 0).bind (fun p => (arm.emit).bind (fun b =>
     some (Backend.Block.ite p b (.code [])))) = some block at emitted
   obtain ⟨p,hp,rest⟩ := Option.bind_eq_some_iff.mp emitted
   obtain ⟨b,hb,same⟩ := Option.bind_eq_some_iff.mp rest
   cases Option.some.inj same
   change (WordMachine.selectCode p).bind (fun q => (WordControl.blockCode b).bind (fun qb =>
     some (MachineControl.branchCode q qb []))) = some code at selected
   obtain ⟨q,sq,rest⟩ := Option.bind_eq_some_iff.mp selected
   obtain ⟨qb,sb,same⟩ := Option.bind_eq_some_iff.mp rest
   cases Option.some.inj same
   exact branch_forward condition arm.profile p q qb hp sq m caller (ih b qb hb sb) horizon locals result ran
 | @zero n fuel fresh bodyStmt scope ih =>
   change (scope.emit).bind (fun b => some (Backend.Block.seq (.code (ZeroLoopScope.entry fresh))
     (.seq b (.code (popPrefix fresh))))) = some block at emitted
   obtain ⟨b,hb,same⟩ := Option.bind_eq_some_iff.mp emitted
   cases Option.some.inj same
   obtain ⟨begin,middle,finish,hs,hm,hf,same⟩ := scope_selected _ _ _ _ selected
   subst code
   exact zero_forward scope.profile begin middle finish hs hf m caller (ih b middle hb hm) horizon locals result ran
 | @letOne n fuel rhs bodyStmt initializer scope ih =>
   change (initializer.lowered.code 0).bind (fun p => (scope.emit).bind (fun b =>
     some (Backend.Block.seq (.code p) (.seq b (.code (popPrefix 1)))))) = some block at emitted
   obtain ⟨p,hp,rest⟩ := Option.bind_eq_some_iff.mp emitted
   obtain ⟨b,hb,same⟩ := Option.bind_eq_some_iff.mp rest
   cases Option.some.inj same
   obtain ⟨begin,middle,finish,hs,hm,hf,same⟩ := scope_selected _ _ _ _ selected
   subst code
   exact let_forward initializer scope.profile p begin middle finish hp hs hf m caller (ih b middle hb hm) horizon locals result ran

/-- Actual emitted Block and selected-code projection; no simulation law is
stored in the artifact. -/
theorem Artifact.source_to_model {c : Control} {n fuel : Nat} {stmt : Stmt [] [] c n}
 (artifact : Artifact fuel stmt) (horizon : Nat) (locals : Vector Scalar.Word n) (result : Outcome c n)
 (ran : evalStmt horizon .nil True.intro stmt artifact.compiled.profile (sourceLocals locals) = some result)
 (m : Evm.Machine) (caller : List Evm.Word) :
 ∃ out : Vector Scalar.Word n, result = ⟨sourceLocals out,.normal⟩ ∧
 Evm.run artifact.code {m with stack := locals.toList.map coreWord++caller} =
 .ok {m with stack := out.toList.map coreWord++caller} 0 :=
 ScopedControlCompilation.source_to_model artifact.compiled artifact.block artifact.code artifact.emitted artifact.selected
   horizon locals result ran m caller

theorem Artifact.normal_to_model {c : Control} {n fuel : Nat} {stmt : Stmt [] [] c n}
 (artifact : Artifact fuel stmt) (horizon : Nat) (locals out : Vector Scalar.Word n)
 (ran : evalStmt horizon .nil True.intro stmt artifact.compiled.profile (sourceLocals locals) =
   some ⟨sourceLocals out,.normal⟩) (m : Evm.Machine) (caller : List Evm.Word) :
 Evm.run artifact.code {m with stack := locals.toList.map coreWord++caller} =
 .ok {m with stack := out.toList.map coreWord++caller} 0 := by
 exact CompletionControls.normal_output out _
   (artifact.source_to_model horizon locals ⟨sourceLocals out,.normal⟩ ran m caller)

/-- info: 'Solidity.Yul.Compilation.ScopedControlCompilation.scope_selected' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms scope_selected
/-- info: 'Solidity.Yul.Compilation.ScopedControlCompilation.source_to_model' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms source_to_model
/-- info: 'Solidity.Yul.Compilation.ScopedControlCompilation.Artifact.source_to_model' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Artifact.source_to_model
/-- info: 'Solidity.Yul.Compilation.ScopedControlCompilation.Artifact.normal_to_model' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Artifact.normal_to_model
/-- info: 'Solidity.Yul.Compilation.ScopedControlCompilation.compile' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms compile
/-- info: 'Solidity.Yul.Compilation.ScopedControlCompilation.lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms lower
end Solidity.Yul.Compilation.ScopedControlCompilation
