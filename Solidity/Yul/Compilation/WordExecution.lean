import Solidity.Yul.Compilation.NumericExecution
import Solidity.Yul.Compilation.WordMachine
/-! Execution transport for the unchanged WordMachine selector. Reuses actual
numeric execution; derives operands for its six additional word operations.
No source admission, native bytes/gas/capacity or Source/G24 adequacy change. -/
namespace Solidity.Yul.Compilation.WordExecution
open Backend Scalar MachineAdapter

private theorem exp_step (a b : Scalar.Word) (m : Evm.Machine) (tail : List Evm.Word) :
 Evm.Instr.step .exp {m with stack := coreWord a :: coreWord b :: tail} =
 .ok {m with stack := coreWord ((Scalar.binary .EXP).getD (fun _ _ => 0) a b) :: tail} 0 := by
  simp only [Evm.Instr.step,Evm.Machine.next,
    coreWord,Scalar.binary,Option.getD_some,BitVec.toNat_ofNat,Evm.W]
  rfl

private theorem lt_step (a b : Scalar.Word) (m : Evm.Machine) (tail : List Evm.Word) :
 Evm.Instr.step .lt {m with stack := coreWord a :: coreWord b :: tail} =
 .ok {m with stack := coreWord ((Scalar.binary .LT).getD (fun _ _ => 0) a b) :: tail} 0 := by
  cases test : decide (a.toNat < b.toNat) <;>
    simp only [Evm.Instr.step,Evm.Machine.next,
      coreWord,Scalar.binary,Scalar.flag,Evm.bword,Option.getD_some,test,↓reduceIte] <;> rfl

private theorem gt_step (a b : Scalar.Word) (m : Evm.Machine) (tail : List Evm.Word) :
 Evm.Instr.step .gt {m with stack := coreWord a :: coreWord b :: tail} =
 .ok {m with stack := coreWord ((Scalar.binary .GT).getD (fun _ _ => 0) a b) :: tail} 0 := by
  cases test : decide (b.toNat < a.toNat) <;>
    simp only [Evm.Instr.step,Evm.Machine.next,
      coreWord,Scalar.binary,Scalar.flag,Evm.bword,Option.getD_some,test,↓reduceIte] <;> rfl

private theorem eq_step (a b : Scalar.Word) (m : Evm.Machine) (tail : List Evm.Word) :
 Evm.Instr.step .eq {m with stack := coreWord a :: coreWord b :: tail} =
 .ok {m with stack := coreWord ((Scalar.binary .EQ).getD (fun _ _ => 0) a b) :: tail} 0 := by
  by_cases z : a = b
  · subst b
    simp only [Evm.Instr.step,Evm.Machine.next,
      coreWord,Scalar.binary,Scalar.flag,Evm.bword,Option.getD_some,
      beq_self_eq_true,decide_true,↓reduceIte] <;> rfl
  · have nz : a.toNat ≠ b.toNat := fun h => z (BitVec.eq_of_toNat_eq h)
    simp only [Evm.Instr.step,Evm.Machine.next,
      coreWord,Scalar.binary,Scalar.flag,Evm.bword,Option.getD_some,
      beq_eq_false_iff_ne.mpr z,decide_eq_false_iff_not.mpr nz,Bool.false_eq_true,↓reduceIte] <;> rfl

private theorem iszero_step (a : Scalar.Word) (m : Evm.Machine) (tail : List Evm.Word) :
 Evm.Instr.step .iszero {m with stack := coreWord a :: tail} =
 .ok {m with stack := coreWord ((Scalar.unary .ISZERO).getD (fun _ => 0) a) :: tail} 0 := by
  by_cases z : a = 0
  · subst a
    rfl
  · have nz : a.toNat ≠ 0 := fun h => z (BitVec.eq_of_toNat_eq h)
    simp only [Evm.Instr.step,Evm.Machine.next,
      coreWord,Scalar.unary,Scalar.flag,Evm.bword,Option.getD_some,
      beq_eq_false_iff_ne.mpr z,decide_eq_false_iff_not.mpr nz,Bool.false_eq_true,↓reduceIte]
    rfl

private theorem not_step (a : Scalar.Word) (m : Evm.Machine) (tail : List Evm.Word) :
 Evm.Instr.step .not {m with stack := coreWord a :: tail} =
 .ok {m with stack := coreWord ((Scalar.unary .NOT).getD (fun _ => 0) a) :: tail} 0 := by
  simp only [Evm.Instr.step,Evm.Machine.next,
    coreWord,Scalar.unary,Option.getD_some,BitVec.toNat_not,Evm.W]

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


private theorem unary_transport (i : Backend.Instr) (j : Evm.Instr)
    (f : Scalar.Word → Scalar.Word)
    (scalarRow : ∀ xs, Scalar.step i xs = applyUnary f xs)
    (modelRow : ∀ (a : Scalar.Word) (m : Evm.Machine) (tail : List Evm.Word),
      j.step {m with stack := coreWord a::tail} = .ok {m with stack := coreWord (f a)::tail} 0)
    (xs ys : Stack) (executed : Scalar.step i xs = some ys)
    (m : Evm.Machine) (tail : List Evm.Word) :
    j.step {m with stack := xs.map coreWord++tail} =
      .ok {m with stack := ys.map coreWord++tail} 0 := by
  rw [scalarRow] at executed
  cases xs with
  | nil => cases executed
  | cons a xs =>
    cases executed
    exact modelRow a m (xs.map coreWord++tail)

/-- General success transport; operands derive from actual scalar success.
Actual compiler endpoints below discharge that run premise. -/
theorem step (i : Backend.Instr) (j : Evm.Instr)
    (selected : WordMachine.selectInstr i = some j) (xs ys : Stack)
    (executed : Scalar.step i xs = some ys) (m : Evm.Machine) (tail : List Evm.Word) :
    j.step {m with stack := xs.map coreWord++tail} =
      .ok {m with stack := ys.map coreWord++tail} 0 := by
  cases i with
  | push width bytes => exact NumericExecution.step (.push width bytes) j selected xs ys executed m tail
  | op opcode =>
    cases opcode <;> try (refine NumericExecution.step _ j ?_ xs ys executed m tail; exact selected)
    all_goals cases selected
    case op.EXP.refl => exact binary_transport _ _ _ (fun _ => rfl) exp_step xs ys executed m tail
    case op.LT.refl => exact binary_transport _ _ _ (fun _ => rfl) lt_step xs ys executed m tail
    case op.GT.refl => exact binary_transport _ _ _ (fun _ => rfl) gt_step xs ys executed m tail
    case op.EQ.refl => exact binary_transport _ _ _ (fun _ => rfl) eq_step xs ys executed m tail
    case op.ISZERO.refl => exact unary_transport _ _ _ (fun _ => rfl) iszero_step xs ys executed m tail
    case op.NOT.refl => exact unary_transport _ _ _ (fun _ => rfl) not_step xs ys executed m tail

/-- Whole selected straight-line program; intermediate stacks derive from the
actual scalar execution, not a list of assumed target transitions. -/
theorem run (p : Backend.Program) (q : List Evm.Instr)
    (selected : WordMachine.selectCode p = some q) (xs ys : Stack)
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
is a premise. Selection still uses exactly the original WordMachine table. -/
theorem loweredExpr_machine {n : Nat} {value : Vector Scalar.Word n → Scalar.Word}
    (compiled : LoweredExpr n value) (depth : Nat) (p : Backend.Program) (q : List Evm.Instr)
    (emitted : compiled.code depth = some p) (translated : WordMachine.selectCode p = some q)
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
    (emitted : compiled.code depth = some p) (translated : WordMachine.selectCode p = some q)
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
    (emitted : compiled.lowered.code depth = some p) (translated : WordMachine.selectCode p = some q)
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
    (emitted : compiled.lowered.code depth = some p) (translated : WordMachine.selectCode p = some q)
    (locals : Vector Scalar.Word n) (newer : Vector Scalar.Word depth)
    (m : Evm.Machine) (tail : List Evm.Word) :
    (Solidity.Yul.Closed.evalStmt fuel .nil True.intro stmt compiled.profile (ProducerExpressions.sourceLocals locals) =
      some ⟨ProducerExpressions.sourceLocals (compiled.update locals),.normal⟩) ∧
    Evm.run q {m with stack := (newer.toList++locals.toList).map coreWord++tail} =
      .ok {m with stack := (newer.toList++(compiled.update locals).toList).map coreWord++tail} 0 :=
  ⟨compiled.source locals,loweredStmt_machine compiled.lowered depth p q emitted translated locals newer m tail⟩


/-- info: 'Solidity.Yul.Compilation.WordExecution.step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms step

/-- info: 'Solidity.Yul.Compilation.WordExecution.run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms run

/-- info: 'Solidity.Yul.Compilation.WordExecution.loweredExpr_machine' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms loweredExpr_machine

/-- info: 'Solidity.Yul.Compilation.WordExecution.loweredStmt_machine' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms loweredStmt_machine

/-- info: 'Solidity.Yul.Compilation.WordExecution.expression' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms expression

/-- info: 'Solidity.Yul.Compilation.WordExecution.statement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms statement
end Solidity.Yul.Compilation.WordExecution
