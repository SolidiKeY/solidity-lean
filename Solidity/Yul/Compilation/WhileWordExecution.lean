import Solidity.Yul.Compilation.WordExecution
import Solidity.Yul.Compilation.WordControl
/-! Concrete existing word-selector loop execution. Actual compiler certificates
supply condition/body runs; guards describe reached iterations explicitly.
No new loop evaluator, source AST, selector, runtime convention or G24 theorem.
Model fault for endless prefixes is not a source/native divergence equivalence. -/
namespace Solidity.Yul.Compilation.WhileWordExecution
open Backend Scalar MachineAdapter

private theorem repeat_shift {α : Type} (f : α → α) (count : Nat) (a : α) :
    Nat.repeat f count (f a) = Nat.repeat f (count+1) a := by
  induction count with
  | zero => rfl
  | succ count ih => exact congrArg f ih

variable {n depth : Nat} {condition : Vector Scalar.Word n → Scalar.Word}
  {update : Vector Scalar.Word n → Vector Scalar.Word n}

/-- One concrete turn, including the consumed full-word guard. Every condition
and body run is derived from actual emitted and selected compiler programs. -/
theorem turn (c : LoweredExpr n condition) (b : LoweredStmt n update)
    (cc bb : Backend.Program) (qc qb : List Evm.Instr)
    (hc : c.code depth = some cc) (hb : b.code depth = some bb)
    (sc : WordMachine.selectCode cc = some qc) (sb : WordMachine.selectCode bb = some qb)
    (locals : Vector Scalar.Word n) (newer : Vector Scalar.Word depth)
    (m : Evm.Machine) (caller : List Evm.Word) :
    Evm.loopTurn (Evm.run qc) (Evm.run qb)
      {m with stack := (newer.toList++locals.toList).map coreWord++caller} =
      if condition locals = 0 then
        .inr (.ok {m with stack := (newer.toList++locals.toList).map coreWord++caller} 0)
      else .inl {m with stack := (newer.toList++(update locals).toList).map coreWord++caller} := by
  rw [Evm.loopTurn,WordExecution.loweredExpr_machine c depth cc qc hc sc locals newer m caller]
  change ((if (condition locals).toNat = 0 then
    .inr (.ok {m with stack := (newer.toList++locals.toList).map coreWord++caller} 0)
    else match Evm.run qb {m with stack := (newer.toList++locals.toList).map coreWord++caller} with
      | .ok next 0 => .inl next
      | .ok _ (_+1) => .inr .fault
      | result => .inr result) : Evm.Machine ⊕ Evm.Out) = _
  rw [WordExecution.loweredStmt_machine b depth bb qb hb sb locals newer m caller]
  have truth : (condition locals).toNat = 0 ↔ condition locals = 0 :=
    ⟨fun h => BitVec.eq_of_toNat_eq h,fun h => congrArg BitVec.toNat h⟩
  by_cases zero : condition locals = 0
  · rw [if_pos (truth.mpr zero),if_pos zero]
  · rw [if_neg (fun h => zero (truth.mp h)),if_neg zero]

/-- Exactly count successful turns; no termination bound or desired model
prefix is assumed. Only the guards actually reached before count are required. -/
theorem running_prefix (c : LoweredExpr n condition) (b : LoweredStmt n update)
    (cc bb : Backend.Program) (qc qb : List Evm.Instr)
    (hc : c.code depth = some cc) (hb : b.code depth = some bb)
    (sc : WordMachine.selectCode cc = some qc) (sb : WordMachine.selectCode bb = some qb)
    (count : Nat) (locals : Vector Scalar.Word n) (newer : Vector Scalar.Word depth)
    (m : Evm.Machine) (caller : List Evm.Word)
    (running : ∀ j, j < count → condition (Nat.repeat update j locals) ≠ 0) :
    Evm.loopIterN (Evm.run qc) (Evm.run qb) count
      {m with stack := (newer.toList++locals.toList).map coreWord++caller} =
      .inl {m with stack := (newer.toList++(Nat.repeat update count locals).toList).map coreWord++caller} := by
  induction count generalizing locals with
  | zero => rfl
  | succ count ih =>
    have nonzero : condition locals ≠ 0 := running 0 (by omega)
    have restRunning : ∀ j, j < count → condition (Nat.repeat update j (update locals)) ≠ 0 := by
      intro j bound
      rw [repeat_shift]
      exact running (j+1) (by omega)
    rw [Evm.loopIterN,turn c b cc bb qc qb hc hb sc sb locals newer m caller,if_neg nonzero]
    simpa only [repeat_shift] using ih (update locals) restRunning

/-- count body runs and the final zero-guard turn. This is a finite model
exit theorem, not source termination or a resource/capacity proof. -/
theorem finite (c : LoweredExpr n condition) (b : LoweredStmt n update)
    (cc bb : Backend.Program) (qc qb : List Evm.Instr)
    (hc : c.code depth = some cc) (hb : b.code depth = some bb)
    (sc : WordMachine.selectCode cc = some qc) (sb : WordMachine.selectCode bb = some qb)
    (count : Nat) (locals : Vector Scalar.Word n) (newer : Vector Scalar.Word depth)
    (m : Evm.Machine) (caller : List Evm.Word)
    (running : ∀ j, j < count → condition (Nat.repeat update j locals) ≠ 0)
    (stopped : condition (Nat.repeat update count locals) = 0) :
    Evm.loopIterN (Evm.run qc) (Evm.run qb) (count+1)
      {m with stack := (newer.toList++locals.toList).map coreWord++caller} =
      .inr (.ok {m with stack := (newer.toList++(Nat.repeat update count locals).toList).map coreWord++caller} 0) := by
  induction count generalizing locals with
  | zero =>
    change condition locals = 0 at stopped
    simp only [Evm.loopIterN,turn c b cc bb qc qb hc hb sc sb locals newer m caller,
      stopped,ite_true,Nat.repeat]
  | succ count ih =>
    have nonzero : condition locals ≠ 0 := running 0 (by omega)
    have restRunning : ∀ j, j < count → condition (Nat.repeat update j (update locals)) ≠ 0 := by
      intro j bound
      rw [repeat_shift]
      exact running (j+1) (by omega)
    have restStopped : condition (Nat.repeat update count (update locals)) = 0 := by
      rw [repeat_shift]
      exact stopped
    rw [Evm.loopIterN,turn c b cc bb qc qb hc hb sc sb locals newer m caller,if_neg nonzero]
    simpa only [repeat_shift] using ih (update locals) restRunning restStopped

/-- Actual whole model loop execution, with compiler facts replacing the
previous abstract selected-realization/desired-run premise. -/
theorem model (c : LoweredExpr n condition) (b : LoweredStmt n update)
    (cc bb : Backend.Program) (qc qb : List Evm.Instr)
    (hc : c.code depth = some cc) (hb : b.code depth = some bb)
    (sc : WordMachine.selectCode cc = some qc) (sb : WordMachine.selectCode bb = some qb)
    (count : Nat) (locals : Vector Scalar.Word n) (newer : Vector Scalar.Word depth)
    (m : Evm.Machine) (caller : List Evm.Word)
    (running : ∀ j, j < count → condition (Nat.repeat update j locals) ≠ 0)
    (stopped : condition (Nat.repeat update count locals) = 0) :
    Evm.run [.loop qc qb] {m with stack := (newer.toList++locals.toList).map coreWord++caller} =
      .ok {m with stack := (newer.toList++(Nat.repeat update count locals).toList).map coreWord++caller} 0 := by
  have finished := Evm.loopRun_of_iterN (finite c b cc bb qc qb hc hb sc sb count locals newer m caller running stopped)
  change (Evm.loopRun (Evm.run qc) (Evm.run qb) _).bind (fun next pending => Evm.exec [] pending next) = _
  rw [finished]
  rfl

/-- In this existing model, a loop with all guards nonzero has only running
finite prefixes and faults. This does not equate source divergence with faults. -/
theorem all_prefixes_fault (c : LoweredExpr n condition) (b : LoweredStmt n update)
    (cc bb : Backend.Program) (qc qb : List Evm.Instr)
    (hc : c.code depth = some cc) (hb : b.code depth = some bb)
    (sc : WordMachine.selectCode cc = some qc) (sb : WordMachine.selectCode bb = some qb)
    (locals : Vector Scalar.Word n) (newer : Vector Scalar.Word depth)
    (m : Evm.Machine) (caller : List Evm.Word)
    (running : ∀ j, condition (Nat.repeat update j locals) ≠ 0) :
    Evm.run [.loop qc qb] {m with stack := (newer.toList++locals.toList).map coreWord++caller} = .fault := by
  have forever := Evm.loopRun_of_forall (rc := Evm.run qc) (rb := Evm.run qb)
    (m := {m with stack := (newer.toList++locals.toList).map coreWord++caller}) (by
      intro count
      exact ⟨_,running_prefix c b cc bb qc qb hc hb sc sb count locals newer m caller (fun j _ => running j)⟩)
  change (Evm.loopRun (Evm.run qc) (Evm.run qb) _).bind (fun next pending => Evm.exec [] pending next) = _
  rw [forever]
  rfl

/-- Recover actual emitted condition/body programs and their concrete selected
model code from the existing lowerWhile/WordControl success equations. -/
theorem selected_parts (c : LoweredExpr n condition) (b : LoweredStmt n update)
    (block : Backend.Block) (code : List Evm.Instr)
    (emitted : lowerWhile c b depth = some block)
    (selected : WordControl.blockCode block = some code) :
    ∃ cc bb qc qb, c.code depth = some cc ∧ b.code depth = some bb ∧
      WordMachine.selectCode cc = some qc ∧ WordMachine.selectCode bb = some qb ∧
      code = [.loop qc qb] := by
  unfold lowerWhile at emitted
  cases hc : c.code depth with
  | none => simp only [hc,Option.bind_none] at emitted; cases emitted
  | some cc =>
    cases hb : b.code depth with
    | none => simp only [hc,hb,Option.bind_some,Option.map_none] at emitted; cases emitted
    | some bb =>
      simp only [hc,hb,Option.bind_some,Option.map_some,Option.some.injEq] at emitted
      subst block
      change ((WordMachine.selectCode cc).bind (fun qc =>
        (WordMachine.selectCode bb).map (fun qb => [Evm.Instr.loop qc qb]))) = some code at selected
      cases sc : WordMachine.selectCode cc with
      | none => simp only [sc,Option.bind_none] at selected; cases selected
      | some qc =>
        cases sb : WordMachine.selectCode bb with
        | none => simp only [sc,sb,Option.bind_some,Option.map_none] at selected; cases selected
        | some qb =>
          simp only [sc,sb,Option.bind_some,Option.map_some,Option.some.injEq] at selected
          exact ⟨cc,bb,qc,qb,rfl,rfl,sc,sb,selected.symm⟩

/-- Whole execution for actual lowerWhile emission/selection, not a separately
assumed realization. Finite guard hypotheses remain explicit; capacity is a
separate obligation. -/
theorem lowered (c : LoweredExpr n condition) (b : LoweredStmt n update)
    (block : Backend.Block) (code : List Evm.Instr)
    (emitted : lowerWhile c b depth = some block)
    (selected : WordControl.blockCode block = some code)
    (count : Nat) (locals : Vector Scalar.Word n) (newer : Vector Scalar.Word depth)
    (m : Evm.Machine) (caller : List Evm.Word)
    (running : ∀ j, j < count → condition (Nat.repeat update j locals) ≠ 0)
    (stopped : condition (Nat.repeat update count locals) = 0) :
    Evm.run code {m with stack := (newer.toList++locals.toList).map coreWord++caller} =
      .ok {m with stack := (newer.toList++(Nat.repeat update count locals).toList).map coreWord++caller} 0 := by
  obtain ⟨cc,bb,qc,qb,hc,hb,sc,sb,rfl⟩ := selected_parts c b block code emitted selected
  exact model c b cc bb qc qb hc hb sc sb count locals newer m caller running stopped

/-- info: 'Solidity.Yul.Compilation.WhileWordExecution.selected_parts' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms selected_parts
/-- info: 'Solidity.Yul.Compilation.WhileWordExecution.lowered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms lowered
/-- info: 'Solidity.Yul.Compilation.WhileWordExecution.turn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms turn
/-- info: 'Solidity.Yul.Compilation.WhileWordExecution.running_prefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms running_prefix
/-- info: 'Solidity.Yul.Compilation.WhileWordExecution.finite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms finite
/-- info: 'Solidity.Yul.Compilation.WhileWordExecution.model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms model
/-- info: 'Solidity.Yul.Compilation.WhileWordExecution.all_prefixes_fault' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms all_prefixes_fault
end Solidity.Yul.Compilation.WhileWordExecution
