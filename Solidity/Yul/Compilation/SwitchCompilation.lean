import Solidity.Yul.Compilation.ScopedControlCompilation
/-! Actual one-case/default original switch lowering. The selector is computed
once, retained during full-word comparison, and popped before either scoped
arm. This is normal-source/model transport, not admission/native/G24 closure. -/
namespace Solidity.Yul.Compilation.SwitchCompilation
open Backend Scalar MachineAdapter Solidity.Yul.Closed ProducerExpressions

def comparison (label : Solidity.Yul.Word) :
 LoweredExpr 1 (fun words => WordExpressions.selectEq.value words[0] (BitVec.ofFin label)) :=
 lowerBinary WordExpressions.selectEq (lowerLocal 0) (lowerLiteral (BitVec.ofFin label))

theorem comparison_value (label : Solidity.Yul.Word) (word : Scalar.Word) :
 WordExpressions.selectEq.value word (BitVec.ofFin label) = if word.toFin = label then 1 else 0 := by
 by_cases same : word.toFin = label
 · have equal : word = BitVec.ofFin label := by
     simpa only [BitVec.ofFin_toFin] using congrArg BitVec.ofFin same
   subst word
   simp only [WordExpressions.selectEq,Scalar.binary,Option.getD_some,beq_self_eq_true,
     Scalar.flag,ite_true]
 · have ne : word ≠ BitVec.ofFin label := fun h => same (congrArg BitVec.toFin h)
   simp only [WordExpressions.selectEq,Scalar.binary,Option.getD_some,beq_eq_false_iff_ne.mpr ne,
     Scalar.flag,Bool.false_eq_true,ite_false,same]

inductive Compiled {c : Control} {n : Nat} (fuel : Nat) : Stmt [] [] c n → Type where
 | one {test : Expr [] [] n 1} {label : Solidity.Yul.Word} {arm fallback : Stmt [] [] c n}
     (condition : ProducerExpressions.Compiled fuel test)
     (yes : ScopedControlCompilation.Artifact fuel arm)
     (no : ScopedControlCompilation.Artifact fuel fallback) :
     Compiled fuel (.switch test (.cons label arm .nil) fallback)

def Compiled.profile {c n fuel} {stmt : Stmt [] [] c n} (compiled : Compiled fuel stmt) : StmtWordP stmt :=
 Compiled.casesOn (motive := fun stmt _ => StmtWordP stmt) compiled
   (fun condition yes no => ⟨condition.profile,⟨yes.compiled.profile,True.intro⟩,no.compiled.profile⟩)

def Compiled.emit {c n fuel} {stmt : Stmt [] [] c n} (compiled : Compiled fuel stmt) : Option Backend.Block :=
 Compiled.casesOn (motive := fun _ _ => Option Backend.Block) compiled
   (fun {_test label _arm _fallback} condition yes no => do
     let p ← condition.lowered.code 0
     let q ← (comparison label).code 0
     pure (.seq (.code p) (.ite q (.seq (.code (popPrefix 1)) yes.block)
       (.seq (.code (popPrefix 1)) no.block))))

/-- Generalized original case recursor: only an empty tail is accepted. -/
def compileTail {c : Control} {n : Nat} (fuel : Nat) (rest : Cases [] [] c n) :
 (label : Solidity.Yul.Word) → (arm : Stmt [] [] c n) → (test : Expr [] [] n 1) → (fallback : Stmt [] [] c n) →
 Option (Compiled fuel (.switch test (.cons label arm rest) fallback)) := by
 apply Cases.casesOn (motive_2 := fun F X c n rest =>
   match F,X with
   | [],[] => (label : Solidity.Yul.Word) → (arm : Stmt [] [] c n) → (test : Expr [] [] n 1) → (fallback : Stmt [] [] c n) →
       Option (Compiled fuel (.switch test (.cons label arm rest) fallback))
   | _,_ => Unit) rest
 case nil =>
   intro F X c n
   cases F <;> cases X
   · intro label arm test fallback
     exact do
       let condition ← PureExpressions.compile fuel test
       let yes ← ScopedControlCompilation.lower fuel arm
       let no ← ScopedControlCompilation.lower fuel fallback
       pure (.one condition yes no)
   all_goals exact ()
 case cons =>
   intro F X c n label arm rest
   cases F <;> cases X
   · exact fun _ _ _ _ => none
   all_goals exact ()

def compileCases {c : Control} {n : Nat} (fuel : Nat) (arms : Cases [] [] c n) :
 (test : Expr [] [] n 1) → (fallback : Stmt [] [] c n) → Option (Compiled fuel (.switch test arms fallback)) := by
 apply Cases.casesOn (motive_2 := fun F X c n arms =>
   match F,X with
   | [],[] => (test : Expr [] [] n 1) → (fallback : Stmt [] [] c n) → Option (Compiled fuel (.switch test arms fallback))
   | _,_ => Unit) arms
 case nil =>
   intro F X c n
   cases F <;> cases X
   · exact fun _ _ => none
   all_goals exact ()
 case cons =>
   intro F X c n label arm rest
   cases F <;> cases X
   · exact fun test fallback => compileTail fuel rest label arm test fallback
   all_goals exact ()

/-- Original constructor inspection accepts exactly one case and a default;
multiple/zero cases refuse locally without altering the static checker. -/
def compile {c : Control} {n : Nat} (fuel : Nat) (stmt : Stmt [] [] c n) : Option (Compiled fuel stmt) := by
 apply Stmt.casesOn (motive_1 := fun F X c n stmt =>
   match F,X with
   | [],[] => Option (Compiled fuel stmt)
   | _,_ => Unit) stmt
 case switch =>
   intro F X c n test arms fallback
   cases F <;> cases X
   · exact compileCases fuel arms test fallback
   all_goals exact ()
 all_goals intro F X; cases F <;> cases X <;> intros <;> first | exact none | exact ()

structure Artifact {c : Control} {n : Nat} (fuel : Nat) (stmt : Stmt [] [] c n) where
 compiled : Compiled fuel stmt
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

/-- Original case selection transports a genuine matching-arm completion;
no default-arm run is required. -/
theorem source_match {c : Control} {n fc : Nat} {test : Expr [] [] n 1}
 {arm fallback : Stmt [] [] c n} (condition : ProducerExpressions.Compiled fc test)
 (label : Solidity.Yul.Word) (ha : StmtWordP arm) (hf : StmtWordP fallback)
 (horizon : Nat) (locals out : Vector Scalar.Word n) (bound : fc ≤ horizon+1)
 (equal : (condition.value locals).toFin = label)
 (ran : evalStmt horizon .nil True.intro arm ha (sourceLocals locals) = some ⟨sourceLocals out,.normal⟩) :
 evalStmt (horizon+2) .nil True.intro (.switch test (.cons label arm .nil) fallback)
   ⟨condition.profile,⟨ha,True.intro⟩,hf⟩ (sourceLocals locals) = some ⟨sourceLocals out,.normal⟩ := by
 have tested := evalExpr_stable bound .nil True.intro test condition.profile (sourceLocals locals) (condition.source locals)
 change Option.bind (evalExpr (horizon+1) .nil True.intro test condition.profile (sourceLocals locals)) _ = _
 rw [tested]
 change Option.bind (if (condition.value locals).toFin = label then
   (evalStmt horizon .nil True.intro arm ha (sourceLocals locals)).map some
   else evalCases horizon .nil True.intro .nil True.intro (condition.value locals).toFin (sourceLocals locals)) _ = _
 rw [if_pos equal,ran]
 rfl

/-- Original default selection consumes the actual empty case tail. The
untaken matching arm need not complete at this source horizon. -/
theorem source_default {c : Control} {n fc : Nat} {test : Expr [] [] n 1}
 {arm fallback : Stmt [] [] c n} (condition : ProducerExpressions.Compiled fc test)
 (label : Solidity.Yul.Word) (ha : StmtWordP arm) (hf : StmtWordP fallback)
 (horizon : Nat) (locals out : Vector Scalar.Word n) (bound : fc ≤ horizon+2)
 (different : (condition.value locals).toFin ≠ label)
 (ran : evalStmt (horizon+2) .nil True.intro fallback hf (sourceLocals locals) = some ⟨sourceLocals out,.normal⟩) :
 evalStmt (horizon+3) .nil True.intro (.switch test (.cons label arm .nil) fallback)
   ⟨condition.profile,⟨ha,True.intro⟩,hf⟩ (sourceLocals locals) = some ⟨sourceLocals out,.normal⟩ := by
 have tested := evalExpr_stable bound .nil True.intro test condition.profile (sourceLocals locals) (condition.source locals)
 change Option.bind (evalExpr (horizon+2) .nil True.intro test condition.profile (sourceLocals locals)) _ = _
 rw [tested]
 change Option.bind (if (condition.value locals).toFin = label then
   (evalStmt (horizon+1) .nil True.intro arm ha (sourceLocals locals)).map some
   else some none) _ = _
 rw [if_neg different]
 exact ran

theorem Artifact.source_to_model {c : Control} {n fuel : Nat} {stmt : Stmt [] [] c n}
 (artifact : Artifact fuel stmt) (horizon : Nat) (locals : Vector Scalar.Word n) (result : Outcome c n)
 (ran : evalStmt horizon .nil True.intro stmt artifact.compiled.profile (sourceLocals locals) = some result)
 (m : Evm.Machine) (caller : List Evm.Word) :
 ∃ out : Vector Scalar.Word n, result = ⟨sourceLocals out,.normal⟩ ∧
 Evm.run artifact.code {m with stack := locals.toList.map coreWord++caller} =
 .ok {m with stack := out.toList.map coreWord++caller} 0 := by
 rcases artifact with ⟨compiled,block,code,emitted,selected⟩
 cases compiled with
 | @one test label arm fallback condition yes no =>
   change (condition.lowered.code 0).bind (fun p => ((comparison label).code 0).map (fun r =>
     Backend.Block.seq (.code p) (.ite r (.seq (.code (popPrefix 1)) yes.block)
       (.seq (.code (popPrefix 1)) no.block)))) = some block at emitted
   obtain ⟨p,hp,rest⟩ := Option.bind_eq_some_iff.mp emitted
   obtain ⟨r,hr,same⟩ := Option.map_eq_some_iff.mp rest
   subst block
   have yesSelected : WordControl.blockCode (.seq (.code (popPrefix 1)) yes.block) = some (.pop::yes.code) := by
     change (WordMachine.selectCode (popPrefix 1)).bind (fun a => (WordControl.blockCode yes.block).map (fun b => a++b)) = _
     rw [yes.selected]
     rfl
   have noSelected : WordControl.blockCode (.seq (.code (popPrefix 1)) no.block) = some (.pop::no.code) := by
     change (WordMachine.selectCode (popPrefix 1)).bind (fun a => (WordControl.blockCode no.block).map (fun b => a++b)) = _
     rw [no.selected]
     rfl
   change (WordMachine.selectCode p).bind (fun ps =>
     ((WordMachine.selectCode r).bind (fun rs =>
       ((WordControl.blockCode (.seq (.code (popPrefix 1)) yes.block)).bind (fun ys =>
         (WordControl.blockCode (.seq (.code (popPrefix 1)) no.block)).map
           (fun ns => MachineControl.branchCode rs ys ns))))).map (fun tail => ps++tail)) = some code at selected
   rw [yesSelected,noSelected] at selected
   simp only [Option.bind_some,Option.map_some] at selected
   obtain ⟨ps,sp,rest⟩ := Option.bind_eq_some_iff.mp selected
   obtain ⟨tail,tailSelected,same⟩ := Option.map_eq_some_iff.mp rest
   obtain ⟨rs,sr,tailSame⟩ := Option.bind_eq_some_iff.mp tailSelected
   cases Option.some.inj tailSame
   subst code
   have selectorTarget : Evm.run ps {m with stack := locals.toList.map coreWord++caller} =
     .ok {m with stack := coreWord (condition.value locals)::(locals.toList.map coreWord++caller)} 0 := by
     simpa only [Vector.toList_empty,List.nil_append] using
       WordExecution.loweredExpr_machine condition.lowered 0 p ps hp sp locals #v[] m caller
   have comparedTarget : Evm.run rs
     {m with stack := coreWord (condition.value locals)::(locals.toList.map coreWord++caller)} =
     .ok {m with stack := (coreWord (WordExpressions.selectEq.value (condition.value locals) (BitVec.ofFin label))::
       coreWord (condition.value locals)::(locals.toList.map coreWord++caller))} 0 := by
     simpa only [Vector.toList_empty,Vector.toList_singleton,List.nil_append,List.map_cons,List.map_nil,List.singleton_append] using
       WordExecution.loweredExpr_machine (comparison label) 0 r rs hr sr #v[condition.value locals] #v[] m
         (locals.toList.map coreWord++caller)
   have popped : Evm.run [.pop] {m with stack := coreWord (condition.value locals)::(locals.toList.map coreWord++caller)} =
     .ok {m with stack := locals.toList.map coreWord++caller} 0 := by rfl
   have execute (out : Vector Scalar.Word n)
     (chosen : if (condition.value locals).toFin = label then
       Evm.run yes.code {m with stack := locals.toList.map coreWord++caller} = .ok {m with stack := out.toList.map coreWord++caller} 0
       else Evm.run no.code {m with stack := locals.toList.map coreWord++caller} = .ok {m with stack := out.toList.map coreWord++caller} 0) :
     Evm.run (ps++MachineControl.branchCode rs (.pop::yes.code) (.pop::no.code))
       {m with stack := locals.toList.map coreWord++caller} = .ok {m with stack := out.toList.map coreWord++caller} 0 := by
     rw [Evm.run_append_ok selectorTarget,MachineControl.branchCode,Evm.run_append_ok comparedTarget,comparison_value]
     by_cases equal : (condition.value locals).toFin = label
     · rw [if_pos equal] at chosen ⊢
       rw [FramedBranch.nonzero_tail 1 (.pop::yes.code) (.pop::no.code)
         {m with stack := coreWord (condition.value locals)::(locals.toList.map coreWord++caller)} (by decide)]
       change Evm.run ([.pop]++yes.code) _ = _
       rw [Evm.run_append_ok popped]
       exact chosen
     · rw [if_neg equal] at chosen ⊢
       have taken : Evm.run (.pop::no.code) {m with stack := coreWord (condition.value locals)::(locals.toList.map coreWord++caller)} =
         .ok {m with stack := out.toList.map coreWord++caller} 0 := by
         change Evm.run ([.pop]++no.code) _ = _
         rw [Evm.run_append_ok popped]
         exact chosen
       change Evm.run ((.pop::no.code)++(.jump ((.pop::yes.code).length)::(.pop::yes.code)))
         {m with stack := coreWord (condition.value locals)::(locals.toList.map coreWord++caller)} =
         .ok {m with stack := out.toList.map coreWord++caller} 0
       rw [Evm.run_append_ok taken]
       exact Evm.exec_length (.pop::yes.code) _
   cases horizon with
   | zero => cases ran
   | succ horizon =>
     change Option.bind (evalExpr horizon .nil True.intro test condition.profile (sourceLocals locals)) _ = some result at ran
     obtain ⟨values,tested,remaining⟩ := Option.bind_eq_some_iff.mp ran
     have same := evalExpr_completed_unique .nil True.intro test condition.profile (sourceLocals locals)
       tested (condition.source locals)
     subst values
     change Option.bind (evalCases horizon .nil True.intro (.cons label arm .nil)
       ⟨yes.compiled.profile,True.intro⟩ (condition.value locals).toFin (sourceLocals locals)) _ = some result at remaining
     cases horizon with
     | zero => cases remaining
     | succ horizon =>
       change Option.bind (if (condition.value locals).toFin = label then
         (evalStmt horizon .nil True.intro arm yes.compiled.profile (sourceLocals locals)).map some
         else evalCases horizon .nil True.intro .nil True.intro (condition.value locals).toFin (sourceLocals locals)) _ = some result at remaining
       by_cases equal : (condition.value locals).toFin = label
       · rw [if_pos equal] at remaining
         obtain ⟨choice,selectedSource,rest⟩ := Option.bind_eq_some_iff.mp remaining
         obtain ⟨actual,armSource,same⟩ := Option.map_eq_some_iff.mp selectedSource
         subst choice
         change some actual = some result at rest
         cases Option.some.inj rest
         obtain ⟨out,same,target⟩ := yes.source_to_model horizon locals result armSource m caller
         refine ⟨out,same,execute out ?_⟩
         rw [if_pos equal]
         exact target
       · rw [if_neg equal] at remaining
         cases horizon with
         | zero => cases remaining
         | succ more =>
           change evalStmt (more+2) .nil True.intro fallback no.compiled.profile (sourceLocals locals) = some result at remaining
           obtain ⟨out,same,target⟩ := no.source_to_model (more+2) locals result remaining m caller
           refine ⟨out,same,execute out ?_⟩
           rw [if_neg equal]
           exact target

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



/-- info: 'Solidity.Yul.Compilation.SwitchCompilation.source_match' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms source_match
/-- info: 'Solidity.Yul.Compilation.SwitchCompilation.source_default' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms source_default
/-- info: 'Solidity.Yul.Compilation.SwitchCompilation.comparison_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms comparison_value
/-- info: 'Solidity.Yul.Compilation.SwitchCompilation.compile' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms compile
/-- info: 'Solidity.Yul.Compilation.SwitchCompilation.lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms lower
/-- info: 'Solidity.Yul.Compilation.SwitchCompilation.Artifact.source_to_model' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Artifact.source_to_model
/-- info: 'Solidity.Yul.Compilation.SwitchCompilation.Artifact.normal_to_model' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Artifact.normal_to_model
end Solidity.Yul.Compilation.SwitchCompilation
