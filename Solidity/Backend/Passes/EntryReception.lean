import Solidity.Semantics.AbiEntryProofs
import Solidity.Backend.Passes.FreshBooleanCompilation

/-! Published ABI WORD admission feeds the fixed runtime receiver. This is
value handoff/provisioning, NOT decoder bytecode or a Source lowering theorem. -/
namespace Solidity.Backend.Passes.EntryReception
open Evm Evm.Memory Evm.Compiler
open Controls.Fixture FixedBooleanSequence FreshBooleanPrefix FreshBooleanFailure
open ReferenceControls (state)

def params : List AbiEntry.Param := [{shape := .word .bool,loc := .value}]
def decoded (w : AbiEntry.Word .bool) : Bool := decide (w.val = 1)

theorem decoded_repr (w : AbiEntry.Word .bool) :
    ReprV .bool (decoded w) (.val (wmod w.val)) := by
  have h := of_decide_eq_true w.valid
  change w.val < 2 at h
  have cases : w.val = 0 ∨ w.val = 1 := by omega
  change Evm.Word.val (wmod w.val) = Evm.Word.val (bword (decoded w))
  apply congrArg Evm.Word.val
  apply Fin.ext
  change w.val % Evm.W = if decide (w.val = 1) then 1 else 0
  rcases cases with hz | ho
  · rw [hz]; rfl
  · rw [ho]; rfl

/-- The only body-input provisioning change is caller local5. It contains
the ACTUAL admitted word, with the original allocator/frame and saved tail. -/
theorem provisioned_word (w : AbiEntry.Word .bool) (tail : List Evm.Word) :
    run (initializer (decoded w)).code {populatedTarget with stack := tail} =
      .ok (writeMachine {populatedTarget with stack := tail} 5 (.val (wmod w.val))) 0 := by
  have eq : Evm.Word.val (bword (decoded w)) = Evm.Word.val (wmod w.val) :=
    (decoded_repr w).symm
  rw [initialize_target,eq]

/-- Actual decoder success is retained with its original I/fuel. Every
physical body Input/map is DERIVED from the real fresh prefix. The emitted
receiver/capture/observer code takes no word/Bool parameter. -/
theorem admitted_reception (I : AbiEntry.Input) (fuel : Nat) (w : AbiEntry.Word .bool)
    (admitted : AbiEntry.verdict I fuel params = .run (.cons (.word w) .nil)) :
    (∃ es, AbiEntry.entry I fuel params = .ok es ∧
      AbiEntry.bodyValues I fuel params es 0 = .ok (.cons (.word w) .nil)) ∧
    ReprV .bool (decoded w) (.val (wmod w.val)) ∧
    ∃ (pb ib rb cb : Nat → Fin Evm.W) (mid captured : Machine), ∀ tail,
      (Compilation.memory population).Input 1 128 initialBase initial {initialMachine with stack := tail} ∧
      run population.code {initialMachine with stack := tail} = .ok {populatedTarget with stack := tail} 0 ∧
      MappedOutput (.memory population) 1 128 initialBase initial {initialMachine with stack := tail}
        σ {populatedTarget with stack := tail} pb ∧
      MappedBoundaryLink (.memory population) (.memory (provisioner (decoded w))) 1 128 initialBase initial
        {initialMachine with stack := tail} ∧
      (Compilation.memory (initializer (decoded w))).Input 1 128 pb σ {populatedTarget with stack := tail} ∧
      run (initializer (decoded w)).code {populatedTarget with stack := tail} = .ok {(runtimeInput (decoded w)) with stack := tail} 0 ∧
      MappedOutput (.memory (initializer (decoded w))) 1 128 pb σ {populatedTarget with stack := tail}
        (state (decoded w)) {(runtimeInput (decoded w)) with stack := tail} ib ∧
      MappedBoundaryLink (.memory (initializer (decoded w))) (.memory receiver) 1 128 pb σ
        {populatedTarget with stack := tail} ∧
      (Compilation.memory receiver).Input 1 128 ib (state (decoded w)) {(runtimeInput (decoded w)) with stack := tail} ∧
      run receiver.code {(runtimeInput (decoded w)) with stack := tail} = .ok {mid with stack := tail} 0 ∧
      MappedOutput (.memory receiver) 1 128 ib (state (decoded w)) {(runtimeInput (decoded w)) with stack := tail}
        (middle (decoded w)).st {mid with stack := tail} rb ∧
      MappedBoundaryLink (.memory receiver) (.memory captureStage) 1 128 ib (state (decoded w))
        {(runtimeInput (decoded w)) with stack := tail} ∧
      (Compilation.memory captureStage).Input 1 128 rb (middle (decoded w)).st {mid with stack := tail} ∧
      run captureStage.code {mid with stack := tail} = .ok {captured with stack := tail} 0 ∧
      MappedOutput (.memory captureStage) 1 128 rb (middle (decoded w)).st {mid with stack := tail}
        (afterCapture (decoded w)).st {captured with stack := tail} cb ∧
      MappedBoundaryLink (.memory captureStage) (.memory badStage) 1 128 rb (middle (decoded w)).st
        {mid with stack := tail} ∧
      (Compilation.memory badStage).Input 1 128 cb (afterCapture (decoded w)).st {captured with stack := tail} ∧
      run (prefixCode (decoded w)) {initialMachine with stack := tail} = .ok {captured with stack := tail} 0 := by
  refine ⟨AbiEntry.verdict_run_entry admitted,decoded_repr w,?_⟩
  obtain ⟨pb,hb⟩ := pipeline_shared
  obtain ⟨ib,rb,cb,mid,captured,hall⟩ := hb (decoded w)
  refine ⟨pb,ib,rb,cb,mid,captured,?_⟩
  intro tail
  obtain ⟨ip,hp,mp,l1,ii,hi,mi,l2,ir,hr,mr,l3,ic,hc,mc,l4,io,hprefix⟩ := hall tail
  exact ⟨ip,hp,mp,l1,ii,hi,mi,l2,ir,hr,mr,l3,ic,hc,mc,l4,io,hprefix⟩

def zero : AbiEntry.Word .bool := ⟨0,by decide,by decide⟩
def one : AbiEntry.Word .bool := ⟨1,by decide,by decide⟩
def input (n : Nat) : AbiEntry.Input :=
  {data := [0,0,0,0] ++ AbiEntry.wordBytes n,free := 128}

theorem zero_admitted :
    AbiEntry.verdict (input 0) 4 params = .run (.cons (.word zero) .nil) := by with_unfolding_all rfl
theorem one_admitted :
    AbiEntry.verdict (input 1) 4 params = .run (.cons (.word one) .nil) := by with_unfolding_all rfl

/-- The admitted1 executes the actual accepted WHOLE compiler body to
ordinary revert AFTER capture, rather than a literal-only receiver. -/
theorem one_actual_revert (tail : List Evm.Word) :
    AbiEntry.verdict (input 1) 4 params = .run (.cons (.word one) .nil) ∧
    run (FreshBooleanCompilation.wholeStage (decoded one)).code {initialMachine with stack := tail} = .revert := by
  exact ⟨one_admitted,FreshBooleanCompilation.actual_revert tail⟩

theorem zero_actual_success : ∃ out : Machine,
    AbiEntry.verdict (input 0) 4 params = .run (.cons (.word zero) .nil) ∧ ∀ tail,
    run (FreshBooleanCompilation.wholeStage (decoded zero)).code {initialMachine with stack := tail} =
      .ok {out with stack := tail} 0 := by
  obtain ⟨out,h⟩ := FreshBooleanCompilation.actual_opposite_target
  exact ⟨out,zero_admitted,h⟩

/-- Invalid2 fails in the published entry model BEFORE body handoff. This
does not claim an emitted decoder or any body run for an invalid word. -/
theorem dirty_two_before_body :
    AbiEntry.entry (input 2) 4 params = .error .revert ∧
    AbiEntry.verdict (input 2) 4 params = .revert := by
  have early : AbiEntry.entry (input 2) 4 params = .error .revert := by with_unfolding_all rfl
  exact ⟨early,(AbiEntry.verdict_revert_iff _ _ _).mpr early⟩

theorem dirty_two_cannot_be_handed_off : ¬ ∃ w : AbiEntry.Word .bool, w.val = 2 := by
  rintro ⟨w,h⟩
  have valid := of_decide_eq_true w.valid
  change w.val < 2 at valid
  omega

end Solidity.Backend.Passes.EntryReception
