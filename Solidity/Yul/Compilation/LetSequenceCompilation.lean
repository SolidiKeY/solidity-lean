import Solidity.Yul.Compilation.LetScopeCompilation
/-! Actual original-AST sequencing of accepted let scope artifacts. Compiler
evidence stays indexed by the existing statement; no new source representation
or source-admission rule. Body visitors retain their exact existing domain. -/
namespace Solidity.Yul.Compilation.LetSequenceCompilation
open Backend Scalar MachineAdapter Solidity.Yul.Closed ProducerExpressions

inductive Compiled {c : Control} {n : Nat} : Nat → Stmt [] [] c n → Type where
 | scope {fuel : Nat} {stmt : Stmt [] [] c n}
     (artifact : LetScopeCompilation.Artifact fuel stmt) : Compiled fuel stmt
 | seq {fuel : Nat} {a b : Stmt [] [] c n}
     (left : Compiled fuel a) (right : Compiled fuel b) : Compiled (fuel+1) (.seq a b)

def Compiled.profile {c n fuel} {stmt : Stmt [] [] c n}
 (compiled : Compiled fuel stmt) : StmtWordP stmt := by
 apply Compiled.casesOn (motive := fun _ stmt _ => StmtWordP stmt) compiled
 case scope => intro fuel stmt artifact; exact artifact.compiled.profile
 case seq => intro fuel a b left right; exact ⟨left.profile,right.profile⟩
termination_by structural compiled

def Compiled.code {c n fuel} {stmt : Stmt [] [] c n}
 (compiled : Compiled fuel stmt) : Option (List Evm.Instr) := by
 apply Compiled.casesOn (motive := fun _ _ _ => Option (List Evm.Instr)) compiled
 case scope => intro fuel stmt artifact; exact some artifact.code
 case seq =>
   intro fuel a b left right
   exact do
     let a ← left.code
     let b ← right.code
     pure (a++b)
termination_by structural compiled

/-- Recursively inspect original sequence nodes; all other forms delegate to
actual let lowering, preserving its initializer/body/selection refusals. -/
def compile {c : Control} {n : Nat} (fuel : Nat) (stmt : Stmt [] [] c n) : Option (Compiled fuel stmt) :=
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
   all_goals intro F X; cases F <;> cases X <;> intros <;>
     first | exact (LetScopeCompilation.lower (fuel+1) _).map Compiled.scope | exact ()
termination_by structural fuel

structure Artifact {c : Control} {n : Nat} (fuel : Nat) (stmt : Stmt [] [] c n) where
 compiled : Compiled fuel stmt
 code : List Evm.Instr
 lowered : compiled.code = some code

def lower {c : Control} {n : Nat} (fuel : Nat) (stmt : Stmt [] [] c n) : Option (Artifact fuel stmt) := do
 let compiled ← compile fuel stmt
 match lowered : compiled.code with
 | none => none
 | some code => some ⟨compiled,code,lowered⟩

/-- Actual source completion supplies each intermediate local vector and
normal flow before selected instruction concatenation is executed. No desired
child run or intermediate state is a caller premise. -/
theorem source_to_model {c : Control} {n fuel : Nat} {stmt : Stmt [] [] c n}
 (compiled : Compiled fuel stmt) (code : List Evm.Instr) (lowered : compiled.code = some code)
 (horizon : Nat) (locals : Vector Scalar.Word n) (result : Outcome c n)
 (ran : evalStmt horizon .nil True.intro stmt compiled.profile (sourceLocals locals) = some result)
 (m : Evm.Machine) (caller : List Evm.Word) :
 ∃ out : Vector Scalar.Word n, result = ⟨sourceLocals out,.normal⟩ ∧
 Evm.run code {m with stack := locals.toList.map coreWord++caller} =
 .ok {m with stack := out.toList.map coreWord++caller} 0 := by
 induction compiled generalizing code horizon locals result with
 | scope artifact =>
   change some artifact.code = some code at lowered
   cases Option.some.inj lowered
   exact artifact.source_to_model horizon locals result ran m caller
 | seq left right ihLeft ihRight =>
   change (left.code).bind (fun a => (right.code).bind (fun b => some (a++b))) = some code at lowered
   obtain ⟨a,ha,rest⟩ := Option.bind_eq_some_iff.mp lowered
   obtain ⟨b,hb,same⟩ := Option.bind_eq_some_iff.mp rest
   cases Option.some.inj same
   cases horizon with
   | zero => cases ran
   | succ horizon =>
     change Option.bind (evalStmt horizon .nil True.intro _ left.profile (sourceLocals locals)) _ = some result at ran
     obtain ⟨middle,first,remaining⟩ := Option.bind_eq_some_iff.mp ran
     obtain ⟨mid,same,firstRun⟩ := ihLeft a ha horizon locals middle first
     subst middle
     change evalStmt horizon .nil True.intro _ right.profile (sourceLocals mid) = some result at remaining
     obtain ⟨out,same,lastRun⟩ := ihRight b hb horizon mid result remaining
     refine ⟨out,same,?_⟩
     rw [Evm.run_append_ok firstRun]
     exact lastRun

/-- Concrete artifact transport with no stored execution or simulation law. -/
theorem Artifact.source_to_model {c : Control} {n fuel : Nat} {stmt : Stmt [] [] c n}
 (artifact : Artifact fuel stmt) (horizon : Nat) (locals : Vector Scalar.Word n) (result : Outcome c n)
 (ran : evalStmt horizon .nil True.intro stmt artifact.compiled.profile (sourceLocals locals) = some result)
 (m : Evm.Machine) (caller : List Evm.Word) :
 ∃ out : Vector Scalar.Word n, result = ⟨sourceLocals out,.normal⟩ ∧
 Evm.run artifact.code {m with stack := locals.toList.map coreWord++caller} =
 .ok {m with stack := out.toList.map coreWord++caller} 0 :=
 LetSequenceCompilation.source_to_model artifact.compiled artifact.code artifact.lowered horizon locals result ran m caller

theorem Artifact.normal_to_model {c : Control} {n fuel : Nat} {stmt : Stmt [] [] c n}
 (artifact : Artifact fuel stmt) (horizon : Nat) (locals out : Vector Scalar.Word n)
 (ran : evalStmt horizon .nil True.intro stmt artifact.compiled.profile (sourceLocals locals) =
   some ⟨sourceLocals out,.normal⟩) (m : Evm.Machine) (caller : List Evm.Word) :
 Evm.run artifact.code {m with stack := locals.toList.map coreWord++caller} =
 .ok {m with stack := out.toList.map coreWord++caller} 0 := by
 obtain ⟨actual,same,target⟩ := artifact.source_to_model horizon locals ⟨sourceLocals out,.normal⟩ ran m caller
 have equal : out = actual := SourceLoopCompletion.sourceLocals_injective (congrArg Outcome.vars same)
 cases equal
 exact target

/-- info: 'Solidity.Yul.Compilation.LetSequenceCompilation.source_to_model' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms source_to_model
/-- info: 'Solidity.Yul.Compilation.LetSequenceCompilation.Artifact.source_to_model' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Artifact.source_to_model
/-- info: 'Solidity.Yul.Compilation.LetSequenceCompilation.Artifact.normal_to_model' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Artifact.normal_to_model
/-- info: 'Solidity.Yul.Compilation.LetSequenceCompilation.compile' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms compile
/-- info: 'Solidity.Yul.Compilation.LetSequenceCompilation.lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms lower
end Solidity.Yul.Compilation.LetSequenceCompilation
