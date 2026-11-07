import Solidity.Yul.Compilation.MultiSwitchCompilation
/-! Original-AST recursive sequence lowering with existing scoped-control and
finite-switch compilation leaves. This outer visitor avoids the dependency
cycle of teaching the scoped compiler its own switch consumer. No source AST,
state, runtime convention or leaf producer is duplicated. Only normal source
completion is transported; general nested control and native/G24 remain open. -/
namespace Solidity.Yul.Compilation.SequenceCompilation
open Backend Scalar MachineAdapter Solidity.Yul.Closed ProducerExpressions

inductive Compiled (c : Control) : {n : Nat} → Nat → Stmt [] [] c n → Type where
 | scopeLeaf {n fuel} {stmt : Stmt [] [] c n}
     (artifact : ScopedControlCompilation.Artifact fuel stmt) : Compiled c fuel stmt
 | switch_ {n fuel} {stmt : Stmt [] [] c n}
     (artifact : MultiSwitchCompilation.Artifact fuel stmt) : Compiled c fuel stmt
 | seq {n fuel} {a b : Stmt [] [] c n}
     (left : Compiled c fuel a) (right : Compiled c fuel b) : Compiled c (fuel+1) (.seq a b)

def Compiled.profile {c n fuel} {stmt : Stmt [] [] c n} (compiled : Compiled c fuel stmt) : StmtWordP stmt := by
 apply Compiled.casesOn (motive := fun _ stmt _ => StmtWordP stmt) compiled
 case scopeLeaf => intro fuel stmt artifact; exact artifact.compiled.profile
 case switch_ => intro fuel stmt artifact; exact artifact.compiled.profile
 case seq => intro fuel a b left right; exact ⟨left.profile,right.profile⟩
termination_by structural compiled

def Compiled.emit {c n fuel} {stmt : Stmt [] [] c n} (compiled : Compiled c fuel stmt) : Option Backend.Block := by
 apply Compiled.casesOn (motive := fun _ _ _ => Option Backend.Block) compiled
 case scopeLeaf => intro fuel stmt artifact; exact some artifact.block
 case switch_ => intro fuel stmt artifact; exact some artifact.block
 case seq =>
   intro fuel a b left right
   exact do
     let a ← left.emit
     let b ← right.emit
     pure (.seq a b)
termination_by structural compiled

def compileLeaf {c n} (fuel : Nat) (stmt : Stmt [] [] c n) : Option (Compiled c fuel stmt) :=
 match ScopedControlCompilation.lower fuel stmt with
 | some artifact => some (.scopeLeaf artifact)
 | none => (MultiSwitchCompilation.lower fuel stmt).map Compiled.switch_

/-- Every original sequence node recurses on compiler fuel, using index-general
casesOn rather than indexed pattern compilation. Other nodes reuse real leaves. -/
def compile {c n} (fuel : Nat) (stmt : Stmt [] [] c n) : Option (Compiled c fuel stmt) :=
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
   all_goals intro F X; cases F <;> cases X <;> intros <;>
     first | exact compileLeaf (fuel+1) _ | exact ()
termination_by structural fuel

structure Artifact {c n} (fuel : Nat) (stmt : Stmt [] [] c n) where
 compiled : Compiled c fuel stmt
 block : Backend.Block
 code : List Evm.Instr
 emitted : compiled.emit = some block
 selected : WordControl.blockCode block = some code

def lower {c n} (fuel : Nat) (stmt : Stmt [] [] c n) : Option (Artifact fuel stmt) := do
 let compiled ← compile fuel stmt
 match emitted : compiled.emit with
 | none => none
 | some block =>
   match selected : WordControl.blockCode block with
   | none => none
   | some code => some ⟨compiled,block,code,emitted,selected⟩

theorem source_to_model {c n fuel} {stmt : Stmt [] [] c n} (compiled : Compiled c fuel stmt)
 (block : Backend.Block) (code : List Evm.Instr)
 (emitted : compiled.emit = some block) (selected : WordControl.blockCode block = some code)
 (horizon : Nat) (locals : Vector Scalar.Word n) (result : Outcome c n)
 (ran : evalStmt horizon .nil True.intro stmt compiled.profile (sourceLocals locals) = some result)
 (m : Evm.Machine) (caller : List Evm.Word) :
 ∃ out : Vector Scalar.Word n, result = ⟨sourceLocals out,.normal⟩ ∧
 Evm.run code {m with stack := locals.toList.map coreWord++caller} =
 .ok {m with stack := out.toList.map coreWord++caller} 0 := by
 induction compiled generalizing block code horizon locals result m caller with
 | scopeLeaf artifact =>
   cases Option.some.inj emitted
   have same : code = artifact.code := Option.some.inj (selected.symm.trans artifact.selected)
   subst code
   exact ScopedControlCompilation.source_to_model artifact.compiled artifact.block artifact.code
     artifact.emitted artifact.selected horizon locals result ran m caller
 | switch_ artifact =>
   cases Option.some.inj emitted
   have same : code = artifact.code := Option.some.inj (selected.symm.trans artifact.selected)
   subst code
   exact artifact.source_to_model horizon locals result ran m caller
 | seq left right ihLeft ihRight =>
   change (left.emit).bind (fun a => (right.emit).bind (fun b => some (Backend.Block.seq a b))) = some block at emitted
   obtain ⟨a,ha,rest⟩ := Option.bind_eq_some_iff.mp emitted
   obtain ⟨b,hb,same⟩ := Option.bind_eq_some_iff.mp rest
   cases Option.some.inj same
   change (WordControl.blockCode a).bind (fun qa => (WordControl.blockCode b).map (fun qb => qa++qb)) = some code at selected
   obtain ⟨qa,sa,rest⟩ := Option.bind_eq_some_iff.mp selected
   obtain ⟨qb,sb,same⟩ := Option.map_eq_some_iff.mp rest
   subst code
   cases horizon with
   | zero => cases ran
   | succ horizon =>
     change Option.bind (evalStmt horizon .nil True.intro _ left.profile (sourceLocals locals)) _ = some result at ran
     obtain ⟨middle,first,remaining⟩ := Option.bind_eq_some_iff.mp ran
     obtain ⟨mid,same,firstRun⟩ := ihLeft a qa ha sa horizon locals middle first m caller
     subst middle
     change evalStmt horizon .nil True.intro _ right.profile (sourceLocals mid) = some result at remaining
     obtain ⟨out,same,lastRun⟩ := ihRight b qb hb sb horizon mid result remaining
       {m with stack := mid.toList.map coreWord++caller} caller
     refine ⟨out,same,?_⟩
     rw [Evm.run_append_ok firstRun]
     exact lastRun

theorem Artifact.normal_to_model {c n fuel} {stmt : Stmt [] [] c n}
 (artifact : Artifact fuel stmt) (horizon : Nat) (locals out : Vector Scalar.Word n)
 (ran : evalStmt horizon .nil True.intro stmt artifact.compiled.profile (sourceLocals locals) =
   some ⟨sourceLocals out,.normal⟩) (m : Evm.Machine) (caller : List Evm.Word) :
 Evm.run artifact.code {m with stack := locals.toList.map coreWord++caller} =
 .ok {m with stack := out.toList.map coreWord++caller} 0 := by
 obtain ⟨actual,same,target⟩ := source_to_model artifact.compiled artifact.block artifact.code artifact.emitted
   artifact.selected horizon locals ⟨sourceLocals out,.normal⟩ ran m caller
 have equal : out = actual := SourceLoopCompletion.sourceLocals_injective (congrArg Outcome.vars same)
 cases equal
 exact target

/-- info: 'Solidity.Yul.Compilation.SequenceCompilation.compile' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms compile
/-- info: 'Solidity.Yul.Compilation.SequenceCompilation.source_to_model' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms source_to_model
/-- info: 'Solidity.Yul.Compilation.SequenceCompilation.Artifact.normal_to_model' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Artifact.normal_to_model
end Solidity.Yul.Compilation.SequenceCompilation
