import SolidityBridge.Yul.LoopRealization
/-! Reverse finite target-loop classification over existing model iterations.
No source AST, execution semantics, admission or native runtime is introduced.
Iterations use existing denotational child runs: nested divergence may yield
mathematical fault in one macro-turn. These are not native instruction prefixes. -/
namespace SolidityBridge.Yul.LoopClassification
open Solidity Backend Scalar Selection
open SolidityBridge.Yul ControlRealization ControlCompleteness

/-- Actual one-turn outcomes, including concrete condition/body evidence
for a continuation. This is a proposition over existing states and runs. -/
def TurnCases (c : Backend.Program) (b : Backend.Block)
    (test : OccurrenceSelection.Slice c) (body : Realization b)
    (input : Scalar.Stack) (m : Evm.Machine) : Prop :=
  Evm.loopTurn (Evm.run test.ir) (Evm.run body.ir) m = .inr .fault ∨
  (∃ output : Scalar.Stack, StructuredExec (.loop c b) input output ∧
    Evm.loopTurn (Evm.run test.ir) (Evm.run body.ir) m =
      .inr (.ok {m with stack := irStack output} 0)) ∨
  ∃ (middle after : Scalar.Stack) (w : Scalar.Word),
    Scalar.run c input = some (w::middle) ∧ w ≠ 0 ∧
    StructuredExec b middle after ∧
    Evm.loopTurn (Evm.run test.ir) (Evm.run body.ir) m =
      .inl {m with stack := irStack after}

/-- Classify one actual turn, using the existing body classification. -/
theorem turn_classified (c : Backend.Program) (b : Backend.Block)
    (test : OccurrenceSelection.Slice c) (body : Realization b)
    (classified : Classified body) (input : Scalar.Stack) (m : Evm.Machine)
    (represented : m.stack = irStack input) : TurnCases c b test body input m := by
  have law := SolidityBridge.Yul.OccurrenceSelection.execute test.ir test.certificates input m represented
  rw [test.origin] at law
  cases tested : Solidity.Backend.Scalar.run c input with
  | none =>
    simp only [tested] at law
    left
    rw [Solidity.Evm.loopTurn,law] <;> rfl
  | some stack =>
    simp only [tested] at law
    cases stack with
    | nil =>
      left
      rw [Solidity.Evm.loopTurn,law] <;> rfl
    | cons w middle =>
      by_cases zero : w = 0
      · subst w
        right; left
        exact ⟨middle,Solidity.Backend.Selection.StructuredExec.loopDone tested,
          SolidityBridge.Yul.LoopRealization.turn_done c b test body input middle m represented tested⟩
      · rcases classified middle {m with stack := Solidity.Backend.Selection.irStack middle} rfl with fault | ⟨after,ran,_model⟩
        · left
          rw [SolidityBridge.Yul.QuotientSelection.stack_cons] at law
          have nz : w.toNat ≠ 0 := fun h => zero (BitVec.eq_of_toNat_eq h)
          simp only [Solidity.Evm.loopTurn,law,Solidity.Yul.Compilation.MachineAdapter.coreWord,nz,ite_false,fault]
        · right; right
          exact ⟨middle,after,w,tested,zero,ran,
            SolidityBridge.Yul.LoopRealization.turn_more c b test body input middle after w m represented tested zero ran⟩

/-- Finite-prefix outcomes. The continuation transports any later actual
structured execution back through every already executed turn. -/
def IterCases (c : Backend.Program) (b : Backend.Block)
    (test : OccurrenceSelection.Slice c) (body : Realization b)
    (turns : Nat) (input : Scalar.Stack) (m : Evm.Machine) : Prop :=
  Evm.loopIterN (Evm.run test.ir) (Evm.run body.ir) turns m = .inr .fault ∨
  (∃ output : Scalar.Stack, StructuredExec (.loop c b) input output ∧
    Evm.loopIterN (Evm.run test.ir) (Evm.run body.ir) turns m =
      .inr (.ok {m with stack := irStack output} 0)) ∨
  ∃ after : Scalar.Stack,
    Evm.loopIterN (Evm.run test.ir) (Evm.run body.ir) turns m =
      .inl {m with stack := irStack after} ∧
    ∀ output, StructuredExec (.loop c b) after output →
      StructuredExec (.loop c b) input output


/-- Classify each finite prefix, constructing its backwards transport rather
than accepting a prefix/execution law from the caller. -/
theorem iter_classified (c : Backend.Program) (b : Backend.Block)
    (test : OccurrenceSelection.Slice c) (body : Realization b)
    (classified : Classified body) :
    ∀ (turns : Nat) (input : Scalar.Stack) (m : Evm.Machine),
      m.stack = irStack input → IterCases c b test body turns input m := by
  intro turns
  induction turns with
  | zero =>
    intro input m represented
    right; right
    refine ⟨input,?_,?_⟩
    · rw [←represented]
      rfl
    · intro output rest
      exact rest
  | succ turns ih =>
    intro input m represented
    rcases SolidityBridge.Yul.LoopClassification.turn_classified c b test body classified input m represented with
      fault | ⟨output,executed,done⟩ | ⟨middle,after,w,condition,nonzero,executed,step⟩
    · left
      simp only [Solidity.Evm.loopIterN,fault]
    · right; left
      exact ⟨output,executed,by simp only [Solidity.Evm.loopIterN,done]⟩
    · rcases ih after {m with stack := Solidity.Backend.Selection.irStack after} rfl with
        fault | ⟨output,rest,done⟩ | ⟨last,continues,transport⟩
      · left
        simpa only [Solidity.Evm.loopIterN,step] using fault
      · right; left
        refine ⟨output,Solidity.Backend.Selection.StructuredExec.loopMore condition nonzero executed rest,?_⟩
        simpa only [Solidity.Evm.loopIterN,step] using done
      · right; right
        refine ⟨last,?_,?_⟩
        · simpa only [Solidity.Evm.loopIterN,step] using continues
        · intro output rest
          exact Solidity.Backend.Selection.StructuredExec.loopMore condition nonzero executed (transport output rest)


/-- Whole mathematical target-loop classification. Finite exits reconstruct
actual StructuredExec; the no-finite-outcome case uses the existing model denotation.
This is not executable/native termination or a source divergence theorem. -/
theorem classified (c : Backend.Program) (b : Backend.Block)
    (test : OccurrenceSelection.Slice c) (body : Realization b)
    (bodyClass : Classified body) :
    Classified (LoopRealization.realization c b test body) := by
  intro input m represented
  classical
  by_cases finite : ∃ (r : Solidity.Evm.Out) (n : Nat),
      Solidity.Evm.loopIterN (Solidity.Evm.run test.ir) (Solidity.Evm.run body.ir) n m = .inr r
  · obtain ⟨r,n,ended⟩ := finite
    rcases SolidityBridge.Yul.LoopClassification.iter_classified c b test body bodyClass n input m represented with
      fault | ⟨output,executed,done⟩ | ⟨after,continues,_transport⟩
    · left
      change (Solidity.Evm.loopRun (Solidity.Evm.run test.ir) (Solidity.Evm.run body.ir) m).bind
        (fun next pending => Solidity.Evm.exec [] pending next) = .fault
      rw [Solidity.Evm.loopRun_of_iterN fault]
      rfl
    · right
      refine ⟨output,executed,?_⟩
      change (Solidity.Evm.loopRun (Solidity.Evm.run test.ir) (Solidity.Evm.run body.ir) m).bind
        (fun next pending => Solidity.Evm.exec [] pending next) =
        .ok {m with stack := Solidity.Backend.Selection.irStack output} 0
      rw [Solidity.Evm.loopRun_of_iterN done]
      rfl
    · rw [continues] at ended
      cases ended
  · left
    have unending : ∀ n, ∃ next,
        Solidity.Evm.loopIterN (Solidity.Evm.run test.ir) (Solidity.Evm.run body.ir) n m = .inl next := by
      intro n
      rcases SolidityBridge.Yul.LoopClassification.iter_classified c b test body bodyClass n input m represented with
        fault | ⟨output,_executed,done⟩ | ⟨after,continues,_transport⟩
      · exact False.elim (finite ⟨.fault,n,fault⟩)
      · exact False.elim (finite ⟨.ok {m with stack := Solidity.Backend.Selection.irStack output} 0,n,done⟩)
      · exact ⟨_,continues⟩
    change (Solidity.Evm.loopRun (Solidity.Evm.run test.ir) (Solidity.Evm.run body.ir) m).bind
      (fun next pending => Solidity.Evm.exec [] pending next) = .fault
    rw [Solidity.Evm.loopRun_of_forall unending]
    rfl

end SolidityBridge.Yul.LoopClassification
