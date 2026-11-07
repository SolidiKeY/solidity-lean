import Solidity.Yul.Compilation.ForCompilation
import Solidity.Yul.Compilation.NormalWordTransport
import Solidity.Yul.Compilation.FramedBranch
/-! Original-AST compiler evidence for sequences and branches containing actual
for leaves. This is not a source AST/state/evaluator; actual normal and for
visitors remain the leaves. No early-control or nested for-body extension. -/
namespace Solidity.Yul.Compilation.LoopControlCompilation
open Backend Scalar MachineAdapter Solidity.Yul.Closed ProducerExpressions

inductive Compiled {c : Control} {n : Nat} : Nat → Stmt [] [] c n → Type where
 | normal {fuel : Nat} {stmt : Stmt [] [] c n}
     (leaf : NormalControl.Derivation fuel stmt) : Compiled fuel stmt
 | loop {fuel : Nat} {stmt : Stmt [] [] c n}
     (leaf : ForCompilation.Compiled fuel stmt) : Compiled fuel stmt
 | seq {fuel : Nat} {a b : Stmt [] [] c n}
     (left : Compiled fuel a) (right : Compiled fuel b) : Compiled (fuel+1) (.seq a b)
 | branch {fuel : Nat} {test : Expr [] [] n 1} {body : Stmt [] [] c n}
     (condition : ProducerExpressions.Compiled fuel test) (arm : Compiled fuel body) :
     Compiled (fuel+1) (.if_ test body)

def Compiled.profile {c n fuel} {stmt : Stmt [] [] c n}
 (compiled : Compiled fuel stmt) : StmtWordP stmt := by
 apply Compiled.casesOn (motive := fun _ stmt _ => StmtWordP stmt) compiled
 case normal => intro fuel stmt leaf; exact leaf.profile
 case loop => intro fuel stmt leaf; exact leaf.profile
 case seq => intro fuel a b left right; exact ⟨left.profile,right.profile⟩
 case branch => intro fuel test body condition arm; exact ⟨condition.profile,arm.profile⟩
termination_by structural compiled

def Compiled.emit {c n fuel} {stmt : Stmt [] [] c n}
 (compiled : Compiled fuel stmt) (depth : Nat) : Option Backend.Block := by
 apply Compiled.casesOn (motive := fun _ _ _ => Option Backend.Block) compiled
 case normal => intro fuel stmt leaf; exact leaf.emit depth
 case loop => intro fuel stmt leaf; exact leaf.emit depth
 case seq =>
   intro fuel a b left right
   exact do
     let a ← left.emit depth
     let b ← right.emit depth
     pure (.seq a b)
 case branch =>
   intro fuel test body condition arm
   exact do
     let p ← condition.lowered.code depth
     let b ← arm.emit depth
     pure (.ite p b (.code []))
termination_by structural compiled

/-- Real structural visitor over the original source. Compiler recursion fuel
is not a uniform source execution horizon for the accepted for leaves. -/
def compile {c : Control} {n : Nat} (fuel : Nat) (stmt : Stmt [] [] c n) :
 Option (Compiled fuel stmt) :=
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
   case for_ =>
     intro F X c n pre test post body
     cases F <;> cases X
     · exact (ForCompilation.compile (fuel+1) (.for_ pre test post body)).map Compiled.loop
     all_goals exact ()
   all_goals intro F X; cases F <;> cases X <;> intros <;>
     first | exact (NormalControl.compile (fuel+1) _).map Compiled.normal | exact ()
termination_by structural fuel

structure Artifact {c : Control} {n : Nat} (fuel : Nat) (stmt : Stmt [] [] c n) (depth : Nat) where
 compiled : Compiled fuel stmt
 block : Backend.Block
 code : List Evm.Instr
 emitted : compiled.emit depth = some block
 selected : WordControl.blockCode block = some code

def lower {c : Control} {n : Nat} (fuel : Nat) (stmt : Stmt [] [] c n) (depth : Nat) :
 Option (Artifact fuel stmt depth) := do
 let compiled ← compile fuel stmt
 match emitted : compiled.emit depth with
 | none => none
 | some block =>
   match selected : WordControl.blockCode block with
   | none => none
   | some code => some ⟨compiled,block,code,emitted,selected⟩

/-- Completed original source evaluation derives every intermediate vector,
guard and selected-arm run. This is forward normal-success transport for the
real recursive compiler, with no chosen source horizon/count/target oracle. -/
theorem source_to_model {c : Control} {n fuel : Nat} {stmt : Stmt [] [] c n}
 (compiled : Compiled fuel stmt) (depth : Nat) (block : Backend.Block) (code : List Evm.Instr)
 (emitted : compiled.emit depth = some block) (selected : WordControl.blockCode block = some code)
 (horizon : Nat) (locals : Vector Scalar.Word n) (result : Outcome c n)
 (ran : evalStmt horizon .nil True.intro stmt compiled.profile (sourceLocals locals) = some result)
 (newer : Vector Scalar.Word depth) (m : Evm.Machine) (caller : List Evm.Word) :
 ∃ out : Vector Scalar.Word n, result = ⟨sourceLocals out,.normal⟩ ∧
 Evm.run code {m with stack := (newer.toList++locals.toList).map coreWord++caller} =
 .ok {m with stack := (newer.toList++out.toList).map coreWord++caller} 0 := by
 induction compiled generalizing block code horizon locals result with
 | normal leaf =>
   have same : result = ⟨sourceLocals (leaf.update locals),.normal⟩ :=
     evalStmt_completed_unique .nil True.intro _ leaf.profile (sourceLocals locals) ran (leaf.source locals)
   exact ⟨leaf.update locals,same,
     NormalWordTransport.machine leaf depth block code emitted selected locals newer m caller⟩
 | loop leaf =>
   cases leaf with
   | loop initializer condition step work =>
     exact SourceLoopInitializer.source_to_model initializer condition step work depth block code
       emitted selected horizon locals result ran newer m caller
 | seq left right ihLeft ihRight =>
   change (left.emit depth).bind (fun a => (right.emit depth).bind (fun b =>
     some (Backend.Block.seq a b))) = some block at emitted
   obtain ⟨a,ha,rest⟩ := Option.bind_eq_some_iff.mp emitted
   obtain ⟨b,hb,same⟩ := Option.bind_eq_some_iff.mp rest
   cases Option.some.inj same
   obtain ⟨qa,sa,rest⟩ := Option.bind_eq_some_iff.mp selected
   obtain ⟨qb,sb,same⟩ := Option.map_eq_some_iff.mp rest
   subst code
   cases horizon with
   | zero => cases ran
   | succ horizon =>
     change Option.bind (evalStmt horizon .nil True.intro _ left.profile (sourceLocals locals)) _ = some result at ran
     obtain ⟨middle,first,remaining⟩ := Option.bind_eq_some_iff.mp ran
     obtain ⟨mid,same,firstRun⟩ := ihLeft a qa ha sa horizon locals middle first
     subst middle
     change evalStmt horizon .nil True.intro _ right.profile (sourceLocals mid) = some result at remaining
     obtain ⟨out,same,lastRun⟩ := ihRight b qb hb sb horizon mid result remaining
     refine ⟨out,same,?_⟩
     rw [Evm.run_append_ok firstRun]
     exact lastRun
 | branch condition arm ih =>
   change (condition.lowered.code depth).bind (fun p => (arm.emit depth).bind (fun b =>
     some (Backend.Block.ite p b (.code [])))) = some block at emitted
   obtain ⟨p,hp,rest⟩ := Option.bind_eq_some_iff.mp emitted
   obtain ⟨b,hb,same⟩ := Option.bind_eq_some_iff.mp rest
   cases Option.some.inj same
   change (WordMachine.selectCode p).bind (fun q => (WordControl.blockCode b).bind (fun qb =>
     some (MachineControl.branchCode q qb []))) = some code at selected
   obtain ⟨q,sq,rest⟩ := Option.bind_eq_some_iff.mp selected
   obtain ⟨qb,sb,same⟩ := Option.bind_eq_some_iff.mp rest
   cases Option.some.inj same
   have testedTarget := WordExecution.loweredExpr_machine condition.lowered depth p q hp sq locals newer m caller
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
       else evalStmt horizon .nil True.intro _ arm.profile (sourceLocals locals)) = some result at remaining
     by_cases zero : condition.value locals = 0
     · have zn : (condition.value locals).toNat = 0 := congrArg BitVec.toNat zero
       rw [if_pos zn] at remaining
       refine ⟨locals,(Option.some.inj remaining).symm,?_⟩
       rw [MachineControl.branchCode,Evm.run_append_ok testedTarget,zero]
       change Evm.exec qb qb.length {m with stack := (newer.toList++locals.toList).map coreWord++caller} = _
       exact Evm.exec_length qb _
     · have nz : (condition.value locals).toNat ≠ 0 := fun h => zero (BitVec.eq_of_toNat_eq h)
       rw [if_neg nz] at remaining
       obtain ⟨out,same,armRun⟩ := ih b qb hb sb horizon locals result remaining
       refine ⟨out,same,?_⟩
       rw [MachineControl.branchCode,Evm.run_append_ok testedTarget]
       rw [FramedBranch.nonzero_tail (condition.value locals) qb []
         {m with stack := (newer.toList++locals.toList).map coreWord++caller} zero]
       exact armRun

/-- Concrete selected artifact transport. Real emission and selection are
stored by lower, not assumed as a blanket compiler simulation law. -/
theorem Artifact.source_to_model {c : Control} {n fuel depth : Nat} {stmt : Stmt [] [] c n}
 (artifact : Artifact fuel stmt depth) (horizon : Nat) (locals : Vector Scalar.Word n) (result : Outcome c n)
 (ran : evalStmt horizon .nil True.intro stmt artifact.compiled.profile (sourceLocals locals) = some result)
 (newer : Vector Scalar.Word depth) (m : Evm.Machine) (caller : List Evm.Word) :
 ∃ out : Vector Scalar.Word n, result = ⟨sourceLocals out,.normal⟩ ∧
 Evm.run artifact.code {m with stack := (newer.toList++locals.toList).map coreWord++caller} =
 .ok {m with stack := (newer.toList++out.toList).map coreWord++caller} 0 :=
 LoopControlCompilation.source_to_model artifact.compiled depth artifact.block artifact.code artifact.emitted artifact.selected
   horizon locals result ran newer m caller

/-- Actual normal source completions compose at the SAME child horizon;
the caller must discharge both run premises, never assume a compiler law. -/
theorem sequence_source {c : Control} {n : Nat} (a b : Stmt [] [] c n) (ha : StmtWordP a) (hb : StmtWordP b)
 (horizon : Nat) (input middle output : Values n)
 (first : evalStmt horizon .nil True.intro a ha input = some (⟨middle,.normal⟩ : Outcome c n))
 (last : evalStmt horizon .nil True.intro b hb middle = some (⟨output,.normal⟩ : Outcome c n)) :
 evalStmt (horizon+1) .nil True.intro (.seq a b) ⟨ha,hb⟩ input = some ⟨output,.normal⟩ := by
 change Option.bind (evalStmt horizon .nil True.intro a ha input) _ = _
 rw [first]
 exact last

/-- info: 'Solidity.Yul.Compilation.LoopControlCompilation.sequence_source' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms sequence_source
/-- info: 'Solidity.Yul.Compilation.LoopControlCompilation.compile' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms compile
/-- info: 'Solidity.Yul.Compilation.LoopControlCompilation.lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms lower
/-- info: 'Solidity.Yul.Compilation.LoopControlCompilation.source_to_model' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms source_to_model
/-- info: 'Solidity.Yul.Compilation.LoopControlCompilation.Artifact.source_to_model' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Artifact.source_to_model
end Solidity.Yul.Compilation.LoopControlCompilation
