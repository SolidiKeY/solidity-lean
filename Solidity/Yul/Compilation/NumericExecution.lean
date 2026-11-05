import Solidity.Yul.Compilation.ArithmeticMachine
import Solidity.Yul.Compilation.ScopedStatements

/-! Execution transport for the EXISTING ten-operator NumericMachine selector.
No selector, target machine or source semantics changes. Symbolic caller words
and all nonstack machine fields are preserved. PUSH widths/bytes/PC/gas/native
and logical Source/G24/physical correspondence remain separate obligations. -/
namespace Solidity.Yul.Compilation.NumericExecution
open Backend Scalar MachineAdapter

private theorem sub_step (a b : Scalar.Word) (m : Evm.Machine) (tail : List Evm.Word) :
    Evm.Instr.step .sub {m with stack := coreWord a::coreWord b::tail} =
      .ok {m with stack := coreWord (a-b)::tail} 0 := by
  simp only [Evm.Instr.step,coreWord,BitVec.toNat_sub,Evm.W,Nat.add_comm]
  rfl

private theorem and_step (a b : Scalar.Word) (m : Evm.Machine) (tail : List Evm.Word) :
    Evm.Instr.step .and {m with stack := coreWord a::coreWord b::tail} =
      .ok {m with stack := coreWord (a &&& b)::tail} 0 := by rfl
private theorem or_step (a b : Scalar.Word) (m : Evm.Machine) (tail : List Evm.Word) :
    Evm.Instr.step .or {m with stack := coreWord a::coreWord b::tail} =
      .ok {m with stack := coreWord (a ||| b)::tail} 0 := by rfl
private theorem xor_step (a b : Scalar.Word) (m : Evm.Machine) (tail : List Evm.Word) :
    Evm.Instr.step .xor {m with stack := coreWord a::coreWord b::tail} =
      .ok {m with stack := coreWord (a ^^^ b)::tail} 0 := by rfl

private theorem div_step (a b : Scalar.Word) (m : Evm.Machine) (tail : List Evm.Word) :
    Evm.Instr.step .div {m with stack := coreWord a::coreWord b::tail} =
      .ok {m with stack := coreWord ((Scalar.binary .DIV).getD (fun _ _ => 0) a b)::tail} 0 := by
  by_cases zero : b = 0
  · subst b; rfl
  · have nonzero : b.toNat ≠ 0 := fun h => zero (BitVec.eq_of_toNat_eq h)
    simp only [Evm.Instr.step,Evm.Machine.next,coreWord,Scalar.binary,Option.getD_some,
      beq_eq_false_iff_ne.mpr zero,Bool.false_eq_true,if_neg nonzero,↓reduceIte,
      BitVec.toNat_ofNat,Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self a.toNat b.toNat) a.isLt)]

private theorem mod_step (a b : Scalar.Word) (m : Evm.Machine) (tail : List Evm.Word) :
    Evm.Instr.step .mod {m with stack := coreWord a::coreWord b::tail} =
      .ok {m with stack := coreWord ((Scalar.binary .MOD).getD (fun _ _ => 0) a b)::tail} 0 := by
  by_cases zero : b = 0
  · subst b; rfl
  · have nonzero : b.toNat ≠ 0 := fun h => zero (BitVec.eq_of_toNat_eq h)
    simp only [Evm.Instr.step,Evm.Machine.next,coreWord,Scalar.binary,Option.getD_some,
      beq_eq_false_iff_ne.mpr zero,Bool.false_eq_true,if_neg nonzero,↓reduceIte,
      BitVec.toNat_ofNat,Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.mod_le a.toNat b.toNat) a.isLt)]

private theorem shl_step (a b : Scalar.Word) (m : Evm.Machine) (tail : List Evm.Word) :
    Evm.Instr.step .shl {m with stack := coreWord a::coreWord b::tail} =
      .ok {m with stack := coreWord ((Scalar.binary .SHL).getD (fun _ _ => 0) a b)::tail} 0 := by
  by_cases small : a.toNat < 256 <;>
    simp only [Evm.Instr.step,Evm.Machine.next,coreWord,Scalar.binary,Option.getD_some,small,↓reduceIte,
      BitVec.toNat_shiftLeft,Nat.shiftLeft_eq,Evm.wmod,Evm.W] <;> rfl
private theorem shr_step (a b : Scalar.Word) (m : Evm.Machine) (tail : List Evm.Word) :
    Evm.Instr.step .shr {m with stack := coreWord a::coreWord b::tail} =
      .ok {m with stack := coreWord ((Scalar.binary .SHR).getD (fun _ _ => 0) a b)::tail} 0 := by
  by_cases small : a.toNat < 256 <;>
    simp only [Evm.Instr.step,Evm.Machine.next,coreWord,Scalar.binary,Option.getD_some,small,↓reduceIte,
      BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow,Evm.W] <;> rfl

/-- Derive the two operands from the real successful scalar step. Both dispatch
and model agreement are actual laws, discharged for every selected operator. -/
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

/-- General one-step transport for exactly the unchanged numeric selector.
A successful scalar step is explicit here; real compiler consumers discharge it. -/
theorem step (i : Backend.Instr) (j : Evm.Instr)
    (selected : NumericMachine.selectInstr i = some j) (xs ys : Stack)
    (executed : Scalar.step i xs = some ys) (m : Evm.Machine) (tail : List Evm.Word) :
    j.step {m with stack := xs.map coreWord++tail} =
      .ok {m with stack := ys.map coreWord++tail} 0 := by
  cases i with
  | push width bytes => exact MachineAdapter.stack_step (.push width bytes) j selected xs ys executed m tail
  | op opcode =>
    cases opcode <;> try (refine MachineAdapter.stack_step _ j ?_ xs ys executed m tail; exact selected)
    all_goals cases selected
    case op.ADD.refl => exact binary_transport _ _ (·+·) (fun _ => rfl) ArithmeticMachine.add_step xs ys executed m tail
    case op.SUB.refl => exact binary_transport _ _ (·-·) (fun _ => rfl) sub_step xs ys executed m tail
    case op.MUL.refl => exact binary_transport _ _ (·*·) (fun _ => rfl) ArithmeticMachine.mul_step xs ys executed m tail
    case op.DIV.refl => exact binary_transport _ _ _ (fun _ => rfl) div_step xs ys executed m tail
    case op.MOD.refl => exact binary_transport _ _ _ (fun _ => rfl) mod_step xs ys executed m tail
    case op.AND.refl => exact binary_transport _ _ (· &&& ·) (fun _ => rfl) and_step xs ys executed m tail
    case op.OR.refl => exact binary_transport _ _ (· ||| ·) (fun _ => rfl) or_step xs ys executed m tail
    case op.XOR.refl => exact binary_transport _ _ (· ^^^ ·) (fun _ => rfl) xor_step xs ys executed m tail
    case op.SHL.refl => exact binary_transport _ _ _ (fun _ => rfl) shl_step xs ys executed m tail
    case op.SHR.refl => exact binary_transport _ _ _ (fun _ => rfl) shr_step xs ys executed m tail

/-- Whole selected straight-line program; intermediate stacks derive from the
actual scalar execution, not a list of assumed target transitions. -/
theorem run (p : Backend.Program) (q : List Evm.Instr)
    (selected : NumericMachine.selectCode p = some q) (xs ys : Stack)
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
is a premise. Selection still uses exactly the original NumericMachine table. -/
theorem loweredExpr_machine {n : Nat} {value : Vector Scalar.Word n → Scalar.Word}
    (compiled : LoweredExpr n value) (depth : Nat) (p : Backend.Program) (q : List Evm.Instr)
    (emitted : compiled.code depth = some p) (translated : NumericMachine.selectCode p = some q)
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
    (emitted : compiled.code depth = some p) (translated : NumericMachine.selectCode p = some q)
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
    (emitted : compiled.lowered.code depth = some p) (translated : NumericMachine.selectCode p = some q)
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
    (emitted : compiled.lowered.code depth = some p) (translated : NumericMachine.selectCode p = some q)
    (locals : Vector Scalar.Word n) (newer : Vector Scalar.Word depth)
    (m : Evm.Machine) (tail : List Evm.Word) :
    (Solidity.Yul.Closed.evalStmt fuel .nil True.intro stmt compiled.profile (ProducerExpressions.sourceLocals locals) =
      some ⟨ProducerExpressions.sourceLocals (compiled.update locals),.normal⟩) ∧
    Evm.run q {m with stack := (newer.toList++locals.toList).map coreWord++tail} =
      .ok {m with stack := (newer.toList++(compiled.update locals).toList).map coreWord++tail} 0 :=
  ⟨compiled.source locals,loweredStmt_machine compiled.lowered depth p q emitted translated locals newer m tail⟩

/-- info: 'Solidity.Yul.Compilation.NumericExecution.step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms step
/-- info: 'Solidity.Yul.Compilation.NumericExecution.run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms run
/-- info: 'Solidity.Yul.Compilation.NumericExecution.loweredExpr_machine' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms loweredExpr_machine
/-- info: 'Solidity.Yul.Compilation.NumericExecution.loweredStmt_machine' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms loweredStmt_machine
/-- info: 'Solidity.Yul.Compilation.NumericExecution.expression' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms expression
/-- info: 'Solidity.Yul.Compilation.NumericExecution.statement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms statement

end Solidity.Yul.Compilation.NumericExecution
