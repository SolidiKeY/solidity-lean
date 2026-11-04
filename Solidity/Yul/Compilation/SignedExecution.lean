import Solidity.Yul.Compilation.WordExecution
import Solidity.Yul.Compilation.SignedMachine
import Solidity.Yul.Compilation.SignedComparisonMachine
import Solidity.Yul.EvmSigned
/-! General execution for the existing SignedMachine selector. Actual published
signed producers supply four added rows; prior word execution supplies the rest.
No new signed semantics, selector/admission or Source/G24/native adequacy. -/
namespace Solidity.Yul.Compilation.SignedExecution
open Backend Scalar MachineAdapter

private theorem sdiv_step (a b : Scalar.Word) (m : Evm.Machine) (tail : List Evm.Word) :
 Evm.Instr.step .sdiv {m with stack := coreWord a::coreWord b::tail} =
 .ok {m with stack := coreWord ((Scalar.binary .SDIV).getD (fun _ _ => 0) a b)::tail} 0 := by
 have producer := Solidity.Yul.EvmSigned.step_sdiv m a.toFin b.toFin tail
 have result : Solidity.Yul.Pure.eval .sdiv (Solidity.Yul.EvmSigned.args a.toFin b.toFin) =
     ((Scalar.binary .SDIV).getD (fun _ _ => 0) a b).toFin :=
   (SignedExpressions.sdivBridge.agrees a b).symm
 rw [result] at producer
 exact producer

private theorem smod_step (a b : Scalar.Word) (m : Evm.Machine) (tail : List Evm.Word) :
 Evm.Instr.step .smod {m with stack := coreWord a::coreWord b::tail} =
 .ok {m with stack := coreWord ((Scalar.binary .SMOD).getD (fun _ _ => 0) a b)::tail} 0 := by
 have producer := Solidity.Yul.EvmSigned.step_smod m a.toFin b.toFin tail
 have result : Solidity.Yul.Pure.eval .smod (Solidity.Yul.EvmSigned.args a.toFin b.toFin) =
     ((Scalar.binary .SMOD).getD (fun _ _ => 0) a b).toFin :=
   (SignedExpressions.smodBridge.agrees a b).symm
 rw [result] at producer
 exact producer

private theorem slt_step (a b : Scalar.Word) (m : Evm.Machine) (tail : List Evm.Word) :
 Evm.Instr.step .slt {m with stack := coreWord a::coreWord b::tail} =
 .ok {m with stack := coreWord ((Scalar.binary .SLT).getD (fun _ _ => 0) a b)::tail} 0 := by
 cases test : decide (a.toInt < b.toInt) <;>
   simp only [Evm.Instr.step,Evm.Machine.next,coreWord,SignedComparisonMachine.reading,
     Scalar.binary,Scalar.flag,Evm.bword,Option.getD_some,test,↓reduceIte] <;> rfl

private theorem sgt_step (a b : Scalar.Word) (m : Evm.Machine) (tail : List Evm.Word) :
 Evm.Instr.step .sgt {m with stack := coreWord a::coreWord b::tail} =
 .ok {m with stack := coreWord ((Scalar.binary .SGT).getD (fun _ _ => 0) a b)::tail} 0 := by
 cases test : decide (b.toInt < a.toInt) <;>
   simp only [Evm.Instr.step,Evm.Machine.next,coreWord,SignedComparisonMachine.reading,
     Scalar.binary,Scalar.flag,Evm.bword,Option.getD_some,test,↓reduceIte] <;> rfl

private theorem binary_transport (i : Backend.Instr) (j : Evm.Instr)
    (f : Scalar.Word → Scalar.Word → Scalar.Word)
    (scalarRow : ∀ xs, Scalar.step i xs = applyBinary f xs)
    (modelRow : ∀ (a b : Scalar.Word) (m : Evm.Machine) (tail : List Evm.Word), j.step {m with stack := coreWord a::coreWord b::tail} =
      .ok {m with stack := coreWord (f a b)::tail} 0)
    (xs ys : Stack) (executed : Scalar.step i xs = some ys)
    (m : Evm.Machine) (tail : List Evm.Word) :
    j.step {m with stack := xs.map coreWord++tail} =
      .ok {m with stack := ys.map coreWord++tail} 0 := by
  rw [scalarRow] at executed
  cases xs with
  | nil => cases executed
  | cons a xs =>
    cases xs with
    | nil => cases executed
    | cons b xs =>
      cases executed
      exact modelRow a b m (xs.map coreWord++tail)



/-- The actual successful scalar step supplies both operands. -/
theorem step (i : Backend.Instr) (j : Evm.Instr)
    (selected : SignedMachine.selectInstr i = some j) (xs ys : Stack)
    (executed : Scalar.step i xs = some ys) (m : Evm.Machine) (tail : List Evm.Word) :
    j.step {m with stack := xs.map coreWord++tail} =
      .ok {m with stack := ys.map coreWord++tail} 0 := by
  cases i with
  | push width bytes => exact WordExecution.step (.push width bytes) j selected xs ys executed m tail
  | op opcode =>
    cases opcode <;> try (refine WordExecution.step _ j ?_ xs ys executed m tail; exact selected)
    all_goals cases selected
    case op.SDIV.refl => exact binary_transport _ _ _ (fun _ => rfl) sdiv_step xs ys executed m tail
    case op.SMOD.refl => exact binary_transport _ _ _ (fun _ => rfl) smod_step xs ys executed m tail
    case op.SLT.refl => exact binary_transport _ _ _ (fun _ => rfl) slt_step xs ys executed m tail
    case op.SGT.refl => exact binary_transport _ _ _ (fun _ => rfl) sgt_step xs ys executed m tail

/-- Whole selected straight-line program; intermediate stacks derive from the
actual scalar execution, not a list of assumed target transitions. -/
theorem run (p : Backend.Program) (q : List Evm.Instr)
    (selected : SignedMachine.selectCode p = some q) (xs ys : Stack)
    (executed : Scalar.run p xs = some ys) (m : Evm.Machine) (tail : List Evm.Word) :
    Evm.run q {m with stack := xs.map coreWord++tail} =
      .ok {m with stack := ys.map coreWord++tail} 0 := by
  induction p generalizing q xs ys with
  | nil => cases selected; cases executed; rfl
  | cons i p ih =>
    obtain ⟨j,hi,rest⟩ := Option.bind_eq_some_iff.mp selected
    obtain ⟨target,hp,same⟩ := Option.map_eq_some_iff.mp rest
    subst q
    cases hs : Scalar.step i xs with
    | none => simp only [Scalar.run,hs,Option.bind_none,reduceCtorEq] at executed
    | some zs =>
      simp only [Scalar.run,hs,Option.bind_some] at executed
      rw [Evm.run,Evm.exec_cons_zero,step i j hi xs zs hs m tail,Evm.Out.ok_bind]
      exact ih target hp zs ys executed

/-- Real compiler certificate supplies the scalar run; no chosen execution
is a premise. Selection still uses exactly the original SignedMachine table. -/
theorem loweredExpr_machine {n : Nat} {value : Vector Scalar.Word n → Scalar.Word}
    (compiled : LoweredExpr n value) (depth : Nat) (p : Backend.Program) (q : List Evm.Instr)
    (emitted : compiled.code depth = some p) (translated : SignedMachine.selectCode p = some q)
    (locals : Vector Scalar.Word n) (newer : Vector Scalar.Word depth)
    (m : Evm.Machine) (tail : List Evm.Word) :
    Evm.run q {m with stack := (newer.toList++locals.toList).map coreWord++tail} =
      .ok {m with stack := coreWord (value locals)::((newer.toList++locals.toList).map coreWord++tail)} 0 := by
  have scalar : Scalar.run p (newer.toList++locals.toList) =
      some (value locals::(newer.toList++locals.toList)) := by
    simpa only [List.append_nil] using compiled.correct depth p emitted locals newer []
  simpa only [List.map_cons,List.cons_append] using run p q translated _ _ scalar m tail

theorem loweredStmt_machine {n : Nat} {update : Vector Scalar.Word n → Vector Scalar.Word n}
    (compiled : LoweredStmt n update) (depth : Nat) (p : Backend.Program) (q : List Evm.Instr)
    (emitted : compiled.code depth = some p) (translated : SignedMachine.selectCode p = some q)
    (locals : Vector Scalar.Word n) (newer : Vector Scalar.Word depth)
    (m : Evm.Machine) (tail : List Evm.Word) :
    Evm.run q {m with stack := (newer.toList++locals.toList).map coreWord++tail} =
      .ok {m with stack := (newer.toList++(update locals).toList).map coreWord++tail} 0 := by
  have scalar : Scalar.run p (newer.toList++locals.toList) =
      some (newer.toList++(update locals).toList) := by
    simpa only [List.append_nil] using compiled.correct depth p emitted locals newer []
  exact run p q translated _ _ scalar m tail

/-- Original closed-Yul source and actual compiler-machine run share the same
raw result. This is not native bytes/gas or logical Solidity Source/G24. -/
theorem expression {fuel n r : Nat} (expr : Solidity.Yul.Expr [] [] n r)
    (compiled : ProducerExpressions.Compiled fuel expr)
    (_visited : PureExpressions.compile fuel expr = some compiled)
    (depth : Nat) (p : Backend.Program) (q : List Evm.Instr)
    (emitted : compiled.lowered.code depth = some p) (translated : SignedMachine.selectCode p = some q)
    (locals : Vector Scalar.Word n) (newer : Vector Scalar.Word depth)
    (m : Evm.Machine) (tail : List Evm.Word) :
    (Solidity.Yul.Closed.evalExpr fuel .nil True.intro expr compiled.profile (ProducerExpressions.sourceLocals locals) =
      some (fun _ => (compiled.value locals).toFin)) ∧
    Evm.run q {m with stack := (newer.toList++locals.toList).map coreWord++tail} =
      .ok {m with stack := coreWord (compiled.value locals)::((newer.toList++locals.toList).map coreWord++tail)} 0 :=
  ⟨compiled.source locals,loweredExpr_machine compiled.lowered depth p q emitted translated locals newer m tail⟩

theorem statement {fuel n : Nat} {c : Solidity.Yul.Control} (stmt : Solidity.Yul.Stmt [] [] c n)
    (compiled : ProducerStatements.Compiled fuel stmt)
    (_visited : ScopedStatements.compile fuel stmt = some compiled)
    (depth : Nat) (p : Backend.Program) (q : List Evm.Instr)
    (emitted : compiled.lowered.code depth = some p) (translated : SignedMachine.selectCode p = some q)
    (locals : Vector Scalar.Word n) (newer : Vector Scalar.Word depth)
    (m : Evm.Machine) (tail : List Evm.Word) :
    (Solidity.Yul.Closed.evalStmt fuel .nil True.intro stmt compiled.profile (ProducerExpressions.sourceLocals locals) =
      some ⟨ProducerExpressions.sourceLocals (compiled.update locals),.normal⟩) ∧
    Evm.run q {m with stack := (newer.toList++locals.toList).map coreWord++tail} =
      .ok {m with stack := (newer.toList++(compiled.update locals).toList).map coreWord++tail} 0 :=
  ⟨compiled.source locals,loweredStmt_machine compiled.lowered depth p q emitted translated locals newer m tail⟩



/-- info: 'Solidity.Yul.Compilation.SignedExecution.step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms step

/-- info: 'Solidity.Yul.Compilation.SignedExecution.run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms run

/-- info: 'Solidity.Yul.Compilation.SignedExecution.loweredExpr_machine' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms loweredExpr_machine

/-- info: 'Solidity.Yul.Compilation.SignedExecution.loweredStmt_machine' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms loweredStmt_machine

/-- info: 'Solidity.Yul.Compilation.SignedExecution.expression' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms expression

/-- info: 'Solidity.Yul.Compilation.SignedExecution.statement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms statement
end Solidity.Yul.Compilation.SignedExecution
