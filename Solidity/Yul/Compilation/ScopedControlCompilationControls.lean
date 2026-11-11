import Solidity.Yul.Compilation.ScopedControlCompilation
import Solidity.Yul.Compilation.SourceLoopControls
import Solidity.Yul.Compilation.LetControlCompletion
/-! Inhabited recursive binders over the original source AST and actual
compiler blocks. These are kernel source/model witnesses, not native EVM,
resource-validity, admission or logical Source/G24 adequacy claims. -/
namespace Solidity.Yul.Compilation.ScopedControlCompilation.Controls
open Backend Scalar MachineAdapter Solidity.Yul.Closed ProducerExpressions
open SourceLoop.Controls (root dirty)

def source : Solidity.Yul.Stmt [] [] root 2 :=
 .let_ 1 (.local 0) (.zero 2 (.let_ 1 (.local 2)
  (.seq
   (.assign (fun _ : Fin 1 => .local 4)
    (.builtin (.pure .add) (Fin.cases (.local 0) (fun _ => .literal dirty.toFin))))
   (.seq
    (.assign (fun _ : Fin 1 => .local 1) (.literal dirty.toFin))
    (.assign (fun _ : Fin 1 => .local 0) (.literal dirty.toFin))))))
def artifact := (lower 10 source).get (by rfl)
def reference : ProducerStatements.Compiled 10 source :=
 ScopedStatements.letOne (localExpr 8 0)
  (ScopedStatements.zero (ScopedStatements.letOne (localExpr 6 2)
   (ProducerStatements.seq
    (ProducerStatements.assign 4 (binary addBridge (localExpr 3 0) (literal 3 dirty.toFin)))
    (ProducerStatements.seq
     (ProducerStatements.assign 1 (literal 3 dirty.toFin))
     (ProducerStatements.assign 0 (literal 3 dirty.toFin))))))
def update (b : Scalar.Word) : Scalar.Word := b+dirty
private theorem literal_dirty : BitVec.ofFin dirty.toFin = dirty := by rfl

theorem source_done (b c : Scalar.Word) :
 evalStmt 10 .nil True.intro source artifact.compiled.profile (sourceLocals #v[b,c]) =
 some ⟨sourceLocals #v[update b,c],.normal⟩ := by
 have same : reference.update #v[b,c] = #v[update b,c] := by
  apply Vector.toList_inj.mp
  simp only [reference,ScopedStatements.letOne,ScopedStatements.zero,ProducerStatements.seq,
    ProducerStatements.assign,outerLocals_toList]
  simp only [localExpr,literal,ProducerExpressions.binary,addBridge,selectAdd,
    Vector.toList_set,Vector.toList_append,Vector.toList_replicate,
    Vector.getElem_append,Vector.getElem_singleton,Vector.getElem_replicate
    ]
  simp only [show (2 : Fin 5).val = 2 from rfl,show (0 : Fin 2).val = 0 from rfl,
    show (0 : Fin 6).val = 0 from rfl,show (4 : Fin 6).val = 4 from rfl,
    show (1 : Fin 6).val = 1 from rfl,Nat.reduceLT,Nat.reduceSub,dite_true,dite_false]
  simp only [literal_dirty]
  rfl
 simpa only [same] using reference.source #v[b,c]

theorem target_done (b c : Scalar.Word) (m : Evm.Machine) (caller : List Evm.Word) :
 Evm.run artifact.code {m with stack := coreWord b::coreWord c::caller} =
 .ok {m with stack := coreWord (update b)::coreWord c::caller} 0 := by
 exact CompletionControls.normal_output (c := root) #v[update b,c]
   (fun actual => Evm.run artifact.code {m with stack := coreWord b::coreWord c::caller} =
     .ok {m with stack := actual.toList.map coreWord++caller} 0)
   (artifact.source_to_model 10 #v[b,c] ⟨sourceLocals #v[update b,c],.normal⟩ (source_done b c) m caller)

/-- A dynamic branch contains the whole recursively changing-context scope. -/
def branchSource : Solidity.Yul.Stmt [] [] root 2 := .if_ (.local 1) source
def branchArtifact := (lower 11 branchSource).get (by rfl)
def condition := (PureExpressions.compile 10 (Solidity.Yul.Expr.local (F := []) (X := []) (n := 2) 1)).get (by rfl)

theorem branch_true (b c : Scalar.Word) (nonzero : c ≠ 0) :
 evalStmt 11 .nil True.intro branchSource branchArtifact.compiled.profile (sourceLocals #v[b,c]) =
 some ⟨sourceLocals #v[update b,c],.normal⟩ :=
 LetControlCompletion.source_true condition artifact.compiled.profile 10 #v[b,c] #v[update b,c] nonzero (source_done b c)

theorem branch_false (b : Scalar.Word) :
 evalStmt 11 .nil True.intro branchSource branchArtifact.compiled.profile (sourceLocals #v[b,0]) =
 some ⟨sourceLocals #v[b,0],.normal⟩ :=
 LetControlCompletion.source_false condition artifact.compiled.profile #v[b,0] (by rfl)

theorem branch_target_true (b c : Scalar.Word) (nonzero : c ≠ 0) (m : Evm.Machine) (caller : List Evm.Word) :
 Evm.run branchArtifact.code {m with stack := coreWord b::coreWord c::caller} =
 .ok {m with stack := coreWord (update b)::coreWord c::caller} 0 :=
 branchArtifact.normal_to_model 11 #v[b,c] #v[update b,c] (branch_true b c nonzero) m caller

theorem branch_target_false (b : Scalar.Word) (m : Evm.Machine) (caller : List Evm.Word) :
 Evm.run branchArtifact.code {m with stack := coreWord b::coreWord 0::caller} =
 .ok {m with stack := coreWord b::coreWord 0::caller} 0 :=
 branchArtifact.normal_to_model 11 #v[b,0] #v[b,0] (branch_false b) m caller

/-- Last accessible live slot under a recursively emitted zero prefix. -/
def lastSource : Solidity.Yul.Stmt [] [] root 1 :=
 .zero 14 (.let_ 1 (.local 14) (.assign (fun _ : Fin 1 => .local 15) (.local 0)))
def lastArtifact := (lower 5 lastSource).get (by rfl)
def lastReference : ProducerStatements.Compiled 5 lastSource :=
 ScopedStatements.zero (ScopedStatements.letOne (localExpr 2 14)
  (ProducerStatements.assign 15 (localExpr 1 0)))

theorem last_source (b : Scalar.Word) :
 evalStmt 5 .nil True.intro lastSource lastArtifact.compiled.profile (sourceLocals #v[b]) =
 some ⟨sourceLocals #v[b],.normal⟩ := by
 have same : lastReference.update #v[b] = #v[b] := by
  apply Vector.toList_inj.mp
  simp only [lastReference,ScopedStatements.zero,ScopedStatements.letOne,ProducerStatements.assign,
    outerLocals_toList]
  simp only [localExpr,
    Vector.toList_set,Vector.toList_append,Vector.toList_replicate,
    Vector.getElem_append,Vector.getElem_singleton,Vector.getElem_replicate
    ]
  rfl
 simpa only [same] using lastReference.source #v[b]

theorem last_target (b : Scalar.Word) (m : Evm.Machine) (caller : List Evm.Word) :
 Evm.run lastArtifact.code {m with stack := coreWord b::caller} =
 .ok {m with stack := coreWord b::caller} 0 :=
 lastArtifact.normal_to_model 5 #v[b] #v[b] (last_source b) m caller

def beyondSource : Solidity.Yul.Stmt [] [] root 1 :=
 .zero 15 (.let_ 1 (.local 15) (.assign (fun _ : Fin 1 => .local 16) (.local 0)))
#guard (lower 5 beyondSource).isNone
#guard (lower 0 source).isNone
#guard (LetControlCompilation.lower 10 source).isNone
#guard (evalStmt 0 .nil True.intro source artifact.compiled.profile (sourceLocals #v[dirty,dirty])).isNone
#guard update dirty = BitVec.ofNat 256 (2*2^200+514)
#guard (Scalar.run (popPrefix 1) []).isNone
#guard (Scalar.run [Backend.Instr.op (.DUP 0)] []).isNone
#guard Scalar.stackBound (ZeroLoopScope.entry 14) (1024 : Int) = false
-- Model success quantifies arbitrary callers; it does not establish capacity.
theorem oversized_model (m : Evm.Machine) :
 Evm.run artifact.code {m with stack := coreWord dirty::coreWord dirty::List.replicate 1030 (coreWord 0)} =
 .ok {m with stack := coreWord (update dirty)::coreWord dirty::List.replicate 1030 (coreWord 0)} 0 :=
 target_done dirty dirty m _

/-- info: 'Solidity.Yul.Compilation.ScopedControlCompilation.Controls.source_done' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms source_done
/-- info: 'Solidity.Yul.Compilation.ScopedControlCompilation.Controls.target_done' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms target_done
/-- info: 'Solidity.Yul.Compilation.ScopedControlCompilation.Controls.branch_true' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms branch_true
/-- info: 'Solidity.Yul.Compilation.ScopedControlCompilation.Controls.branch_false' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms branch_false
/-- info: 'Solidity.Yul.Compilation.ScopedControlCompilation.Controls.branch_target_true' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms branch_target_true
/-- info: 'Solidity.Yul.Compilation.ScopedControlCompilation.Controls.branch_target_false' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms branch_target_false
/-- info: 'Solidity.Yul.Compilation.ScopedControlCompilation.Controls.last_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms last_source
/-- info: 'Solidity.Yul.Compilation.ScopedControlCompilation.Controls.last_target' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms last_target
/-- info: 'Solidity.Yul.Compilation.ScopedControlCompilation.Controls.oversized_model' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms oversized_model
end Solidity.Yul.Compilation.ScopedControlCompilation.Controls
