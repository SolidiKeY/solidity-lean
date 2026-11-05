import SolidityBridge.Yul.OccurrenceControl
/-! Target-only loop execution over existing StructuredExec/loopIterN semantics.
No source loop AST/evaluator/horizon or native resource convention is added.
Current automatic selectors still refuse loops. -/
namespace SolidityBridge.Yul.LoopRealization
open Solidity Backend Scalar Selection
open Solidity.Yul.Compilation MachineAdapter
open ControlRealization

theorem turn_done :
∀ (c : Solidity.Backend.Program) (b : Solidity.Backend.Block)
 (test : SolidityBridge.Yul.OccurrenceSelection.Slice c)
 (body : SolidityBridge.Yul.ControlRealization.Realization b)
 (input output : Solidity.Backend.Scalar.Stack) (m : Solidity.Evm.Machine),
 m.stack = Solidity.Backend.Selection.irStack input →
 Solidity.Backend.Scalar.run c input = some (0::output) →
 Solidity.Evm.loopTurn (Solidity.Evm.run test.ir) (Solidity.Evm.run body.ir) m =
 .inr (.ok {m with stack := Solidity.Backend.Selection.irStack output} 0) := by
  intro c b test body input output m represented condition
  have law := ((SolidityBridge.Yul.OccurrenceSelection.lowering c test).success input (0::output) m represented).mpr
    (Solidity.Backend.Selection.StructuredExec.code condition)
  rw [SolidityBridge.Yul.QuotientSelection.stack_cons] at law
  rw [Solidity.Evm.loopTurn,law] <;> rfl

theorem turn_more :
∀ (c : Solidity.Backend.Program) (b : Solidity.Backend.Block)
 (test : SolidityBridge.Yul.OccurrenceSelection.Slice c)
 (body : SolidityBridge.Yul.ControlRealization.Realization b)
 (input middle output : Solidity.Backend.Scalar.Stack) (w : Solidity.Backend.Scalar.Word) (m : Solidity.Evm.Machine),
 m.stack = Solidity.Backend.Selection.irStack input →
 Solidity.Backend.Scalar.run c input = some (w::middle) → w ≠ 0 →
 Solidity.Backend.Selection.StructuredExec b middle output →
 Solidity.Evm.loopTurn (Solidity.Evm.run test.ir) (Solidity.Evm.run body.ir) m =
 .inl {m with stack := Solidity.Backend.Selection.irStack output} := by
  intro c b test body input middle output w m represented condition nonzero executed
  have law := ((SolidityBridge.Yul.OccurrenceSelection.lowering c test).success input (w::middle) m represented).mpr
    (Solidity.Backend.Selection.StructuredExec.code condition)
  rw [SolidityBridge.Yul.QuotientSelection.stack_cons] at law
  have nz : w.toNat ≠ 0 := fun h => nonzero (BitVec.eq_of_toNat_eq h)
  have ran := body.execute middle output {m with stack := Solidity.Backend.Selection.irStack middle} rfl executed
  simp only [Solidity.Evm.loopTurn,law,Solidity.Yul.Compilation.MachineAdapter.coreWord,nz,ite_false,ran]

private theorem finiteAux (block : Backend.Block) (input output : Scalar.Stack)
    (executed : StructuredExec block input output) :
    ∀ (c : Backend.Program) (b : Backend.Block), block = .loop c b →
    ∀ (test : OccurrenceSelection.Slice c) (body : Realization b)
      (m : Evm.Machine), m.stack = irStack input →
    ∃ turns : Nat, Evm.loopIterN (Evm.run test.ir) (Evm.run body.ir) turns m =
      .inr (.ok {m with stack := irStack output} 0) := by
  induction executed with
  | code run => intro c b same; cases same
  | seq first second ihFirst ihSecond => intro c b same; cases same
  | iteTrue condition nonzero body ih => intro c b same; cases same
  | iteFalse condition body ih => intro c b same; cases same
  | @loopDone cc bb input output condition =>
    intro c b same test body m represented
    obtain ⟨rfl,rfl⟩ := Backend.Block.loop.inj same
    refine ⟨1,?_⟩
    simp only [Evm.loopIterN,turn_done cc bb test body input output m represented condition]
  | @loopMore cc bb input middle after output w condition nonzero bodyExec rest ihBody ihRest =>
    intro c b same test body m represented
    obtain ⟨rfl,rfl⟩ := Backend.Block.loop.inj same
    obtain ⟨turns,law⟩ := ihRest cc bb rfl test body {m with stack := irStack after} rfl
    refine ⟨turns+1,?_⟩
    simpa only [Evm.loopIterN,
      turn_more cc bb test body input middle after w m represented condition nonzero bodyExec] using law

/-- Every actual finite structured loop execution gives an actual finite
model iteration witness. The internal generalized block index is specialized
by reflexivity; no model run or source horizon is assumed. -/
theorem finite_prefix (c : Backend.Program) (b : Backend.Block)
    (test : OccurrenceSelection.Slice c) (body : Realization b)
    {input output : Scalar.Stack} (executed : StructuredExec (.loop c b) input output)
    (m : Evm.Machine) (represented : m.stack = irStack input) :
    ∃ turns : Nat, Evm.loopIterN (Evm.run test.ir) (Evm.run body.ir) turns m =
      .inr (.ok {m with stack := irStack output} 0) :=
  finiteAux (.loop c b) input output executed c b rfl test body m represented

/-- Forward only: finite StructuredExec is the real premise. This does not
supply whole-iff loop classification or change the existing loop refusal. -/
def realization (c : Backend.Program) (b : Backend.Block)
    (test : OccurrenceSelection.Slice c) (body : Realization b) : Realization (.loop c b) := by
  refine ⟨[.loop test.ir body.ir],?_⟩
  intro input output m represented executed
  obtain ⟨turns,law⟩ := SolidityBridge.Yul.LoopRealization.finite_prefix c b test body executed m represented
  have finished := Solidity.Evm.loopRun_of_iterN law
  change (Solidity.Evm.loopRun (Solidity.Evm.run test.ir) (Solidity.Evm.run body.ir) m).bind
    (fun next pending => Solidity.Evm.exec [] pending next) = .ok {m with stack := Solidity.Backend.Selection.irStack output} 0
  rw [finished] <;> rfl

def alwaysCondition : List Evm.Instr := [.push (coreWord (1 : Scalar.Word))]
def alwaysBody : List Evm.Instr := []

theorem always_turn (m : Evm.Machine) :
    Evm.loopTurn (Evm.run alwaysCondition) (Evm.run alwaysBody) m = .inl m := by
  rfl

theorem always_prefix :
∀ (turns : Nat) (m : Solidity.Evm.Machine),
 Solidity.Evm.loopIterN (Solidity.Evm.run SolidityBridge.Yul.LoopRealization.alwaysCondition)
 (Solidity.Evm.run SolidityBridge.Yul.LoopRealization.alwaysBody) turns m = .inl m := by
  intro turns
  induction turns with
  | zero => intro m; rfl
  | succ turns ih =>
    intro m
    simp only [Solidity.Evm.loopIterN,SolidityBridge.Yul.LoopRealization.always_turn,ih]

def counterCondition : Backend.Program := [.op (.DUP 0)]
def counterBodyCode : Backend.Program := [pushByte 1,.op (.SWAP 0),.op .SUB]
def counterBlock : Backend.Block := .loop counterCondition (.code counterBodyCode)
def counterTest := (OccurrenceSelection.selectCode counterCondition).get (by rfl)
def counterBodySelected := (OccurrenceControl.selectBlock (.code counterBodyCode)).get (by rfl)
def counterBody := counterBodySelected.realization
def counterRealization := realization counterCondition (.code counterBodyCode) counterTest counterBody

/-- A genuinely executed two-turn countdown, preserving an arbitrary full-word suffix. -/
theorem counter_two :
∀ tail : Solidity.Backend.Scalar.Stack,
 Solidity.Backend.Selection.StructuredExec SolidityBridge.Yul.LoopRealization.counterBlock (2::tail) (0::tail)
 := by
  intro tail
  refine Solidity.Backend.Selection.StructuredExec.loopMore (w := 2) (u := 2::tail) (v := 1::tail)
    (by rfl) (by decide) (Solidity.Backend.Selection.StructuredExec.code (Solidity.Backend.Scalar.run_frame (p := SolidityBridge.Yul.LoopRealization.counterBodyCode) (s := [2]) (t := [1]) (by decide) tail)) ?_
  refine Solidity.Backend.Selection.StructuredExec.loopMore (w := 1) (u := 1::tail) (v := 0::tail)
    (by rfl) (by decide) (Solidity.Backend.Selection.StructuredExec.code (Solidity.Backend.Scalar.run_frame (p := SolidityBridge.Yul.LoopRealization.counterBodyCode) (s := [1]) (t := [0]) (by decide) tail)) ?_
  exact Solidity.Backend.Selection.StructuredExec.loopDone (by rfl)

/-- The mathematical model returns fault when no finite iteration ends.
This theorem does not evaluate the runtime implementation of an infinite loop,
and is not a gas, fuel, timeout or source divergence correspondence claim. -/
theorem always_no_finite_outcome :
∀ m : Solidity.Evm.Machine,
 Solidity.Evm.loopRun (Solidity.Evm.run SolidityBridge.Yul.LoopRealization.alwaysCondition)
 (Solidity.Evm.run SolidityBridge.Yul.LoopRealization.alwaysBody) m = .fault
 := by
  intro m
  exact Solidity.Evm.loopRun_of_forall (fun turns => ⟨m,SolidityBridge.Yul.LoopRealization.always_prefix turns m⟩)

end SolidityBridge.Yul.LoopRealization

