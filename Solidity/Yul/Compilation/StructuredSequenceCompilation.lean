import Solidity.Yul.Compilation.SequenceCompilation
import Solidity.Yul.Compilation.CompletionControls
/-! Recursive original-AST sequence/if/zero/single-result-let lowering around
actual accepted sequence/switch leaves. Original context indices change under
binders; no new syntax, state, layout or runtime convention is introduced.
Only source normal completion is transported here. Switch arm visitors, loop
producers, native capacity and logical Source/G24 keep their existing limits. -/
namespace Solidity.Yul.Compilation.StructuredSequenceCompilation
open Backend Scalar MachineAdapter Solidity.Yul.Closed ProducerExpressions

inductive Compiled (c : Control) : {n : Nat} → Nat → Stmt [] [] c n → Type where
 | base {n fuel : Nat} {stmt : Stmt [] [] c n}
     (artifact : SequenceCompilation.Artifact fuel stmt) : Compiled c fuel stmt
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
     first | exact (SequenceCompilation.lower (fuel+1) _).map Compiled.base | exact ()
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
   exact SequenceCompilation.source_to_model artifact.compiled artifact.block artifact.code artifact.emitted
     artifact.selected horizon locals result ran m caller
 | seq left right ihLeft ihRight =>
   change (left.emit).bind (fun a => (right.emit).bind (fun b => some (Backend.Block.seq a b))) = some block at emitted
   obtain ⟨a,ha,rest⟩ := Option.bind_eq_some_iff.mp emitted
   obtain ⟨b,hb,same⟩ := Option.bind_eq_some_iff.mp rest
   cases Option.some.inj same
   change (WordControl.blockCode a).bind (fun qa => (WordControl.blockCode b).map (fun qb => qa++qb)) = some code at selected
   obtain ⟨qa,sa,rest⟩ := Option.bind_eq_some_iff.mp selected
   obtain ⟨qb,sb,same⟩ := Option.map_eq_some_iff.mp rest
   subst code
   exact ScopedControlCompilation.seq_forward left.profile right.profile qa qb m caller (ihLeft a qa ha sa) (ihRight b qb hb sb) horizon locals result ran
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
   exact ScopedControlCompilation.branch_forward condition arm.profile p q qb hp sq m caller (ih b qb hb sb) horizon locals result ran
 | @zero n fuel fresh bodyStmt scope ih =>
   change (scope.emit).bind (fun b => some (Backend.Block.seq (.code (ZeroLoopScope.entry fresh))
     (.seq b (.code (popPrefix fresh))))) = some block at emitted
   obtain ⟨b,hb,same⟩ := Option.bind_eq_some_iff.mp emitted
   cases Option.some.inj same
   obtain ⟨begin,middle,finish,hs,hm,hf,same⟩ := ScopedControlCompilation.scope_selected _ _ _ _ selected
   subst code
   exact ScopedControlCompilation.zero_forward scope.profile begin middle finish hs hf m caller (ih b middle hb hm) horizon locals result ran
 | @letOne n fuel rhs bodyStmt initializer scope ih =>
   change (initializer.lowered.code 0).bind (fun p => (scope.emit).bind (fun b =>
     some (Backend.Block.seq (.code p) (.seq b (.code (popPrefix 1)))))) = some block at emitted
   obtain ⟨p,hp,rest⟩ := Option.bind_eq_some_iff.mp emitted
   obtain ⟨b,hb,same⟩ := Option.bind_eq_some_iff.mp rest
   cases Option.some.inj same
   obtain ⟨begin,middle,finish,hs,hm,hf,same⟩ := ScopedControlCompilation.scope_selected _ _ _ _ selected
   subst code
   exact ScopedControlCompilation.let_forward initializer scope.profile p begin middle finish hp hs hf m caller (ih b middle hb hm) horizon locals result ran

theorem Artifact.source_to_model {c : Control} {n fuel : Nat} {stmt : Stmt [] [] c n}
 (artifact : Artifact fuel stmt) (horizon : Nat) (locals : Vector Scalar.Word n) (result : Outcome c n)
 (ran : evalStmt horizon .nil True.intro stmt artifact.compiled.profile (sourceLocals locals) = some result)
 (m : Evm.Machine) (caller : List Evm.Word) :
 ∃ out : Vector Scalar.Word n, result = ⟨sourceLocals out,.normal⟩ ∧
 Evm.run artifact.code {m with stack := locals.toList.map coreWord++caller} =
 .ok {m with stack := out.toList.map coreWord++caller} 0 :=
 StructuredSequenceCompilation.source_to_model artifact.compiled artifact.block artifact.code artifact.emitted artifact.selected
   horizon locals result ran m caller

theorem Artifact.normal_to_model {c : Control} {n fuel : Nat} {stmt : Stmt [] [] c n}
 (artifact : Artifact fuel stmt) (horizon : Nat) (locals out : Vector Scalar.Word n)
 (ran : evalStmt horizon .nil True.intro stmt artifact.compiled.profile (sourceLocals locals) =
   some ⟨sourceLocals out,.normal⟩) (m : Evm.Machine) (caller : List Evm.Word) :
 Evm.run artifact.code {m with stack := locals.toList.map coreWord++caller} =
 .ok {m with stack := out.toList.map coreWord++caller} 0 := by
 exact CompletionControls.normal_output out _
   (artifact.source_to_model horizon locals ⟨sourceLocals out,.normal⟩ ran m caller)

/-- info: 'Solidity.Yul.Compilation.StructuredSequenceCompilation.source_to_model' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms source_to_model
/-- info: 'Solidity.Yul.Compilation.StructuredSequenceCompilation.Artifact.source_to_model' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Artifact.source_to_model
/-- info: 'Solidity.Yul.Compilation.StructuredSequenceCompilation.Artifact.normal_to_model' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Artifact.normal_to_model
/-- info: 'Solidity.Yul.Compilation.StructuredSequenceCompilation.compile' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms compile
/-- info: 'Solidity.Yul.Compilation.StructuredSequenceCompilation.lower' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms lower
end Solidity.Yul.Compilation.StructuredSequenceCompilation
