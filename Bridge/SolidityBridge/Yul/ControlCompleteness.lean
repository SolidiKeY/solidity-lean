import SolidityBridge.Yul.ControlRealization
/-! Reverse lowering for the existing checked block selector. This classifies
actual numeric model outcomes, not a replacement evaluator or block syntax.
Native byte/PC/charged/capacity/source-G24 closure remains separate. -/
namespace SolidityBridge.Yul.ControlCompleteness
open Solidity Backend Scalar Selection
open Solidity.Yul.Compilation MachineAdapter
open ControlRealization

/-- Every represented input either really faults or has an actual successful
structured execution and exact unchanged nonstack frame, with no pending skip. -/
def Classified {block : Backend.Block} (selected : Realization block) : Prop :=
  ∀ (input : Scalar.Stack) (m : Evm.Machine), m.stack = irStack input →
    Evm.run selected.ir m = .fault ∨ ∃ output : Scalar.Stack,
      StructuredExec block input output ∧
      Evm.run selected.ir m = .ok {m with stack := irStack output} 0

theorem append_fault (a b : List Evm.Instr) (m : Evm.Machine)
    (fault : Evm.run a m = .fault) : Evm.run (a ++ b) m = .fault := by
  simp only [Evm.run] at fault ⊢
  rw [Evm.exec_append,fault]
  rfl

theorem true_out (w : Fin Evm.W) (yes no : List Evm.Instr)
    (m : Evm.Machine) (nonzero : w.val ≠ 0) :
    Evm.run (MachineControl.branchTail yes no) {m with stack := .val w :: m.stack} = Evm.run yes m := by
  simp only [MachineControl.branchTail,Evm.run,Evm.exec_cons_zero,Evm.Instr.step,
    nonzero,ite_false,Evm.Out.ok_bind]
  rw [Evm.exec_skip_append]
  rfl

theorem false_fault (w : Fin Evm.W) (yes no : List Evm.Instr)
    (m : Evm.Machine) (zero : w.val = 0) (fault : Evm.run no m = .fault) :
    Evm.run (MachineControl.branchTail yes no) {m with stack := .val w :: m.stack} = .fault := by
  simp only [MachineControl.branchTail,Evm.run,Evm.exec_cons_zero,Evm.Instr.step,
    zero,ite_true,Evm.Out.ok_bind]
  change Evm.run (no ++ (.jump yes.length :: yes)) m = _
  exact append_fault _ _ m fault

theorem scalar_classified {p : Backend.Program} (slice : Slice p) : Classified (scalar slice) := by
  intro input m represented
  have law := SelectionSequence.execute slice.ir slice.certificates input m represented
  rw [slice.origin] at law
  cases executed : Scalar.run p input with
  | none =>
    left
    simpa only [executed] using law
  | some output =>
    right
    exact ⟨output,StructuredExec.code executed,by simpa only [executed] using law⟩

theorem sequence_classified {a b : Backend.Block} (left : Realization a) (right : Realization b)
    (first : Classified left) (second : Classified right) : Classified (sequence left right) := by
  intro input m represented
  rcases first input m represented with fault | ⟨middle,firstExec,firstRun⟩
  · left
    exact append_fault left.ir right.ir m fault
  · rcases second middle {m with stack := irStack middle} rfl with fault | ⟨output,secondExec,secondRun⟩
    · left
      change Evm.run (left.ir ++ right.ir) m = .fault
      rw [Evm.run_append_ok firstRun]
      exact fault
    · right
      refine ⟨output,StructuredExec.seq firstExec secondExec,?_⟩
      change Evm.run (left.ir ++ right.ir) m = _
      rw [Evm.run_append_ok firstRun]
      exact secondRun

/-- All outcomes are derived from the real condition program and taken arm.
An empty condition result faults; no extra logical condition value is assumed. -/
theorem conditional_classified {c : Backend.Program} {a b : Backend.Block}
    (test : Slice c) (yes : Realization a) (no : Realization b)
    (yesClass : Classified yes) (noClass : Classified no) : Classified (conditional test yes no) := by
  intro input m represented
  have law := SelectionSequence.execute test.ir test.certificates input m represented
  rw [test.origin] at law
  cases tested : Scalar.run c input with
  | none =>
    left
    change Evm.run (test.ir ++ MachineControl.branchTail yes.ir no.ir) m = .fault
    apply append_fault
    simpa only [tested] using law
  | some stack =>
    rw [tested] at law
    change Evm.run test.ir m = .ok {m with stack := irStack stack} 0 at law
    cases stack with
    | nil =>
      left
      change Evm.run (test.ir ++ MachineControl.branchTail yes.ir no.ir) m = .fault
      rw [Evm.run_append_ok law]
      rfl
    | cons w middle =>
      rw [ArithmeticSelection.irStack_words (w::middle),List.map_cons,
        ←ArithmeticSelection.irStack_words middle] at law
      by_cases zero : w = 0
      · subst w
        rcases noClass middle {m with stack := irStack middle} rfl with fault | ⟨output,body,ran⟩
        · left
          change Evm.run (test.ir ++ MachineControl.branchTail yes.ir no.ir) m = .fault
          rw [Evm.run_append_ok law]
          exact false_fault ⟨0,by decide⟩ yes.ir no.ir {m with stack := irStack middle} rfl fault
        · right
          refine ⟨output,StructuredExec.iteFalse tested body,?_⟩
          change Evm.run (test.ir ++ MachineControl.branchTail yes.ir no.ir) m = _
          rw [Evm.run_append_ok law]
          exact ControlRealization.branch_false ⟨0,by decide⟩ yes.ir no.ir
            {m with stack := irStack middle} {m with stack := irStack output} rfl ran
      · have nz : w.toNat ≠ 0 := fun h => zero (BitVec.eq_of_toNat_eq h)
        rcases yesClass middle {m with stack := irStack middle} rfl with fault | ⟨output,body,ran⟩
        · left
          change Evm.run (test.ir ++ MachineControl.branchTail yes.ir no.ir) m = .fault
          rw [Evm.run_append_ok law]
          exact (true_out ⟨w.toNat,w.isLt⟩ yes.ir no.ir {m with stack := irStack middle} nz).trans fault
        · right
          refine ⟨output,StructuredExec.iteTrue tested zero body,?_⟩
          change Evm.run (test.ir ++ MachineControl.branchTail yes.ir no.ir) m = _
          rw [Evm.run_append_ok law]
          exact (true_out ⟨w.toNat,w.isLt⟩ yes.ir no.ir {m with stack := irStack middle} nz).trans ran

/-- The actual existing selector discharges classification constructively;
there is no assumed totality/simulation or replacement compiler here. -/
theorem selected_classified_with
    (compileLeaf : (p : Backend.Program) → Option (Slice p)) (block : Backend.Block) :
    ∀ (selected : Realization block), selectBlockWith compileLeaf block = some selected → Classified selected := by
  induction block with
  | code p =>
    intro selected emitted
    change (compileLeaf p).map scalar = some selected at emitted
    cases found : compileLeaf p with
    | none => simp only [found,Option.map_none,reduceCtorEq] at emitted
    | some slice =>
      simp only [found,Option.map_some,Option.some.injEq] at emitted
      subst selected
      exact scalar_classified slice
  | seq a b ihA ihB =>
    intro selected emitted
    change (do let left ← selectBlockWith compileLeaf a; let right ← selectBlockWith compileLeaf b; pure (sequence left right)) = some selected at emitted
    cases ha : selectBlockWith compileLeaf a with
    | none =>
      rw [ha] at emitted
      change none = some selected at emitted
      cases emitted
    | some left =>
      cases hb : selectBlockWith compileLeaf b with
      | none =>
        rw [ha,hb] at emitted
        change none = some selected at emitted
        cases emitted
      | some right =>
        rw [ha,hb] at emitted
        have same : sequence left right = selected := Option.some.inj emitted
        subst selected
        exact sequence_classified left right (ihA left ha) (ihB right hb)
  | ite c a b ihA ihB =>
    intro selected emitted
    change (do let test ← compileLeaf c; let yes ← selectBlockWith compileLeaf a; let no ← selectBlockWith compileLeaf b; pure (conditional test yes no)) = some selected at emitted
    cases hc : compileLeaf c with
    | none =>
      rw [hc] at emitted
      change none = some selected at emitted
      cases emitted
    | some test =>
      cases ha : selectBlockWith compileLeaf a with
      | none =>
        rw [hc,ha] at emitted
        change none = some selected at emitted
        cases emitted
      | some yes =>
        cases hb : selectBlockWith compileLeaf b with
        | none =>
          rw [hc,ha,hb] at emitted
          change none = some selected at emitted
          cases emitted
        | some no =>
          rw [hc,ha,hb] at emitted
          have same : conditional test yes no = selected := Option.some.inj emitted
          subst selected
          exact conditional_classified test yes no (ihA yes ha) (ihB no hb)
  | loop _c _body _ih =>
    intro selected emitted
    change none = some selected at emitted
    cases emitted

/-- The legacy theorem retains its original table and public contract. -/
theorem selected_classified (block : Backend.Block) :
    ∀ (selected : Realization block), selectBlock block = some selected → Classified selected :=
  selected_classified_with selectSlice block

/-- The published full iff contract, reconstructed from actual outcomes. -/
def lowering {block : Backend.Block} (selected : Realization block)
    (classified : Classified selected) : Selection.LoweringCertificate selected.ir block := by
  constructor
  intro input output m represented
  constructor
  · intro ran
    rcases classified input m represented with fault | ⟨actual,executed,law⟩
    · have impossible : Evm.Out.fault = .ok {m with stack := irStack output} 0 := fault.symm.trans ran
      cases impossible
    · have mapped : irStack actual = irStack output :=
        congrArg Evm.Machine.stack (Evm.Out.ok.inj (law.symm.trans ran)).1
      have same : actual = output := ArithmeticSelection.irStack_injective mapped
      cases same
      exact executed
  · intro executed
    exact selected.execute input output m represented executed

/-- No classification premise remains for an actual successful selection. -/
def selected_lowering_with (compileLeaf : (p : Backend.Program) → Option (Slice p))
    {block : Backend.Block} (selected : Realization block)
    (emitted : selectBlockWith compileLeaf block = some selected) :
    Selection.LoweringCertificate selected.ir block :=
  lowering selected (selected_classified_with compileLeaf block selected emitted)

/-- Legacy selection still supplies exactly its original certificate. -/
def selected_lowering {block : Backend.Block} (selected : Realization block)
    (emitted : selectBlock block = some selected) : Selection.LoweringCertificate selected.ir block :=
  selected_lowering_with selectSlice selected emitted

/-- Exact fault/refusal transport for represented numeric inputs. This does
not reinterpret gas exhaustion, source horizons or native EVM failures. -/
theorem fault_iff_with (compileLeaf : (p : Backend.Program) → Option (Slice p))
    {block : Backend.Block} (selected : Realization block)
    (emitted : selectBlockWith compileLeaf block = some selected) (input : Scalar.Stack) (m : Evm.Machine)
    (represented : m.stack = irStack input) :
    Evm.run selected.ir m = .fault ↔ ¬ ∃ output, StructuredExec block input output := by
  constructor
  · intro fault successful
    obtain ⟨output,executed⟩ := successful
    have ran := selected.execute input output m represented executed
    have impossible : Evm.Out.fault = .ok {m with stack := irStack output} 0 := fault.symm.trans ran
    cases impossible
  · intro refused
    rcases selected_classified_with compileLeaf block selected emitted input m represented with fault | ⟨output,executed,_ran⟩
    · exact fault
    · exact False.elim (refused ⟨output,executed⟩)

/-- Legacy refusal behavior is preserved by the same concrete leaf compiler. -/
theorem fault_iff {block : Backend.Block} (selected : Realization block)
    (emitted : selectBlock block = some selected) (input : Scalar.Stack) (m : Evm.Machine)
    (represented : m.stack = irStack input) :
    Evm.run selected.ir m = .fault ↔ ¬ ∃ output, StructuredExec block input output :=
  fault_iff_with selectSlice selected emitted input m represented

/-- Concrete original source-compiler blocks, selected without residual
classification, output-stack or target-run assumptions. -/
def branch_lowering := selected_lowering branchSelected (by rfl)
def sequence_lowering := selected_lowering sequenceSelected (by rfl)
def nested_lowering := selected_lowering nestedSelected (by rfl)
def prefixed_lowering := selected_lowering prefixedSelected (by rfl)

end SolidityBridge.Yul.ControlCompleteness
