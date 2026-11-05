import Solidity.Yul.Compilation.ZeroScopeCompletion
/-! Actual original-source zero-binder visitor and selected artifact. Delegates
the structured body to the existing compiler at its explicit depth0 domain;
compiler evidence is indexed by the existing statement, not another AST. -/
namespace Solidity.Yul.Compilation.ZeroScopeCompilation
open Backend Scalar MachineAdapter Solidity.Yul.Closed ProducerExpressions

inductive Compiled {c : Control} {n : Nat} (fuel : Nat) : Stmt [] [] c n → Type where
 | scope {fresh : Nat} {body : Stmt [] [] c (fresh+n)}
     (artifact : LoopControlCompilation.Artifact fuel body 0) : Compiled fuel (.zero fresh body)

def Compiled.profile {c n fuel} {stmt : Stmt [] [] c n}
 (compiled : Compiled fuel stmt) : StmtWordP stmt :=
 Compiled.casesOn (motive := fun stmt _ => StmtWordP stmt) compiled
   (fun artifact => artifact.compiled.profile)

def Compiled.code {c n fuel} {stmt : Stmt [] [] c n}
 (compiled : Compiled fuel stmt) : Option (List Evm.Instr) :=
 Compiled.casesOn (motive := fun _ _ => Option (List Evm.Instr)) compiled
   (fun {fresh} {_body} artifact => ZeroLoopScope.lower fresh (n := n) artifact)

/-- Read the real zero constructor and pass its actual extended-context body
through the real recursive compiler, including actual selection. Unsupported
forms refuse locally, without changing Solidity admission. -/
def compile {c : Control} {n : Nat} (fuel : Nat) (stmt : Stmt [] [] c n) : Option (Compiled fuel stmt) := by
 apply Stmt.casesOn (motive_1 := fun F X c n stmt =>
   match F,X with
   | [],[] => Option (Compiled fuel stmt)
   | _,_ => Unit) stmt
 case zero =>
   intro F X c n fresh body
   cases F <;> cases X
   · exact (LoopControlCompilation.lower fuel body 0).map (fun artifact => Compiled.scope (fresh := fresh) artifact)
   all_goals exact ()
 all_goals intro F X; cases F <;> cases X <;> intros <;> first | exact none | exact ()

/-- Real selected output; no stored execution or source simulation law. Generic
certified data does not assert visitor origin, while lower actually visits. -/
structure Artifact {c : Control} {n : Nat} (fuel : Nat) (stmt : Stmt [] [] c n) where
 compiled : Compiled fuel stmt
 code : List Evm.Instr
 lowered : compiled.code = some code

def lower {c : Control} {n : Nat} (fuel : Nat) (stmt : Stmt [] [] c n) : Option (Artifact fuel stmt) := do
 let compiled ← compile fuel stmt
 match lowered : compiled.code with
 | none => none
 | some code => some ⟨compiled,code,lowered⟩

/-- Exact normal-success correspondence for the selected original zero scope.
The compiler search fuel bounds the body compiler; execution uses an existential
source horizon. Neither model success nor this law asserts native capacity. -/
theorem Artifact.completion_iff {c : Control} {n fuel : Nat} {stmt : Stmt [] [] c n}
 (artifact : Artifact fuel stmt) (locals out : Vector Scalar.Word n)
 (m : Evm.Machine) (caller : List Evm.Word) :
 (∃ horizon, evalStmt horizon .nil True.intro stmt artifact.compiled.profile (sourceLocals locals) =
   some ⟨sourceLocals out,.normal⟩) ↔
 Evm.run artifact.code {m with stack := locals.toList.map coreWord++caller} =
 .ok {m with stack := out.toList.map coreWord++caller} 0 := by
 rcases artifact with ⟨compiled,code,lowered⟩
 cases compiled with
 | scope body => exact ZeroScopeCompletion.completion_iff body code lowered locals out m caller

/-- Whole selected success determines an actual source completion, zero pending
skip and the exact caller/nonstack frame; no desired source result is assumed. -/
theorem Artifact.reflected {c : Control} {n fuel : Nat} {stmt : Stmt [] [] c n}
 (artifact : Artifact fuel stmt) (locals : Vector Scalar.Word n)
 (m final : Evm.Machine) (caller : List Evm.Word) (skip : Nat)
 (ran : Evm.run artifact.code {m with stack := locals.toList.map coreWord++caller} = .ok final skip) :
 ∃ (horizon : Nat) (out : Vector Scalar.Word n),
 evalStmt horizon .nil True.intro stmt artifact.compiled.profile (sourceLocals locals) =
 some ⟨sourceLocals out,.normal⟩ ∧ skip = 0 ∧ final = {m with stack := out.toList.map coreWord++caller} := by
 rcases artifact with ⟨compiled,code,lowered⟩
 cases compiled with
 | scope body => exact ZeroScopeCompletion.model_to_source body code lowered locals m final caller skip ran

/-- info: 'Solidity.Yul.Compilation.ZeroScopeCompilation.Artifact.completion_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Artifact.completion_iff
/-- info: 'Solidity.Yul.Compilation.ZeroScopeCompilation.Artifact.reflected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Artifact.reflected
/-- info: 'Solidity.Yul.Compilation.ZeroScopeCompilation.compile' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms compile
/-- info: 'Solidity.Yul.Compilation.ZeroScopeCompilation.lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms lower
end Solidity.Yul.Compilation.ZeroScopeCompilation
