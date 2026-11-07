import Solidity.Semantics.AbiEntryProofs
import Solidity.Backend.Failure.Correct

/-! Entry transport, adapted from the V13 ABI-world entry work. Consumers of the published indexed ABI-entry interface. The classifier
selects an existing empty REVERT emitter only for certified entry reverts.
It does not emit the decoder or assert source/native or bytecode simulation. -/
namespace Solidity.Backend.AbiEntry.EntryTransport
open Solidity.AbiEntry

/-- Allocation Panic, fuel, access-time failure and lazy-only refusals do not
become empty-revert programs. Accepted inputs have no rejection program. -/
def rejection (I : Input) (fuel : Nat) (ps : List Param) (a : Nat) : Option Program :=
  match verdict I fuel ps with
  | .revert => some (Failure.emit a .empty)
  | .run _ | .blocked _ => none

/-- Actual checked execution of the selected existing emitter, with arbitrary
suffix and initial memory/stack. This is not calldata-decoder machine execution. -/
def runRejection (I : Input) (fuel : Nat) (ps : List Param) (a : Nat)
    (suffix : Program) (m : Failure.Slice.Machine) :
    Option (Failure.Slice.Machine × Option Roadmap.Outcome) :=
  (rejection I fuel ps a).bind (fun code => Failure.Slice.checkedRun (code ++ suffix) m)

/-- Exact source of the certificate: the real entry computation failed with
revert, rather than a named blocked case or a later lazy-access failure. -/
theorem rejection_iff (I : Input) (fuel : Nat) (ps : List Param) (a : Nat) :
    (rejection I fuel ps a).isSome = true ↔ entry I fuel ps = .error .revert := by
  rw [← verdict_revert_iff I fuel ps]
  unfold rejection
  cases verdict I fuel ps with
  | revert => exact ⟨fun _ => rfl, fun _ => rfl⟩
  | run vs => constructor <;> intro h <;> cases h
  | blocked reason => constructor <;> intro h <;> cases h

/-- The actual certified failure drives actual emitted empty-byte REVERT.
Fits/stack prerequisites remain architectural obligations. Memory and the
entire stack tail are unchanged, and the suffix is unreachable. -/
theorem entry_revert_exec (I : Input) (fuel : Nat) (ps : List Param) (a : Nat)
    (suffix : Program) (m : Failure.Slice.Machine)
    (failed : entry I fuel ps = .error .revert)
    (fits : Failure.Fits a []) (stack : m.stack.length + 2 ≤ 1024) :
    runRejection I fuel ps a suffix m = some (m, some (.revert [])) := by
  have hv : verdict I fuel ps = .revert := (verdict_revert_iff I fuel ps).2 failed
  simp only [runRejection, rejection, hv, Option.bind_some]
  have h : Failure.Slice.checkedRun (Failure.emit a .empty ++ suffix) m =
      some ({m with memory := Failure.Slice.putBytes m.memory a []}, some (.revert [])) :=
    Failure.checkedRun_emit_suffix a .empty suffix m fits stack
  simpa only [Failure.Input.bytes, Failure.Input.observation, Failure.Slice.putBytes] using h

/-- A verdict is linked back to the actual entry before consuming the emitter. -/
theorem verdict_revert_exec (I : Input) (fuel : Nat) (ps : List Param) (a : Nat)
    (suffix : Program) (m : Failure.Slice.Machine)
    (failed : verdict I fuel ps = .revert)
    (fits : Failure.Fits a []) (stack : m.stack.length + 2 ≤ 1024) :
    runRejection I fuel ps a suffix m = some (m, some (.revert [])) :=
  entry_revert_exec I fuel ps a suffix m ((verdict_revert_iff I fuel ps).1 failed) fits stack

theorem run_not_rejected {I : Input} {fuel : Nat} {ps : List Param}
    (vs : Vals (ps.map Param.shape)) (h : verdict I fuel ps = .run vs) (a : Nat) :
    rejection I fuel ps a = none := by simp only [rejection, h]

theorem blocked_not_rejected {I : Input} {fuel : Nat} {ps : List Param}
    (reason : String) (h : verdict I fuel ps = .blocked reason) (a : Nat) :
    rejection I fuel ps a = none := by simp only [rejection, h]

/-- Pure observation of actual accepted typed body values. Identifying a
callback with an admitted source body needs its own witness; this adapter is
not a source evaluator and supplies no source/native correspondence. -/
def bodyObservation {α : Type} (I : Input) (fuel : Nat) (ps : List Param)
    (body : Vals (ps.map Param.shape) → α) : Option α :=
  match verdict I fuel ps with
  | .run vs => some (body vs)
  | .revert | .blocked _ => none

theorem body_from_entry {α : Type} (I : Input) (fuel : Nat) (ps : List Param)
    (es : Entries ps) (vs : Vals (ps.map Param.shape))
    (body : Vals (ps.map Param.shape) → α)
    (entered : entry I fuel ps = .ok es) (values : bodyValues I fuel ps es 0 = .ok vs) :
    bodyObservation I fuel ps body = some (body vs) := by
  simp only [bodyObservation, verdict, entered, values]

/-- An accepted verdict carries actual entry and body-value witnesses, not
merely an arbitrary well-typed fixture. -/
theorem body_witness {α : Type} {I : Input} {fuel : Nat} {ps : List Param}
    (vs : Vals (ps.map Param.shape)) (body : Vals (ps.map Param.shape) → α)
    (accepted : verdict I fuel ps = .run vs) :
    ∃ es, entry I fuel ps = .ok es ∧ bodyValues I fuel ps es 0 = .ok vs ∧
      bodyObservation I fuel ps body = some (body vs) := by
  obtain ⟨es, he, hb⟩ := verdict_run_entry accepted
  exact ⟨es, he, hb, body_from_entry I fuel ps es vs body he hb⟩

/-- An actual eager result transports to the actual lazy reference/read.
The input-size and original one-step fuel difference remain explicit. -/
theorem eager_lazy_body {α : Type} (I : Input) (fuel : Nat) (s : Shape) (pos : Nat)
    (v : Val s) (body : Val s → α) (size : I.size ≤ lim)
    (eagerValue : eager I (fuel + 1) s pos = .ok v) :
    ∃ addr len, cref I s 4 pos = .ok (addr,len) ∧
      (cval I fuel s addr len).map body = .ok (body v) := by
  obtain ⟨addr,len,hr,hv⟩ := eager_cref size eagerValue
  exact ⟨addr,len,hr,by rw [hv]; rfl⟩

/-- One calldata parameter links its real entry reference and eager body value
to the same actual lazy read, retaining the complete typed aggregate value. -/
theorem calldata_handoff {α : Type} (I : Input) (fuel : Nat) (s : Shape)
    (addr len : Nat) (v : Val s) (body : Vals [s] → α) (size : I.size ≤ lim)
    (entered : entry I (fuel + 1) [{shape := s, loc := .calldata}] =
      .ok (.cons (.ref addr len) .nil))
    (reference : cref I s 4 0 = .ok (addr,len))
    (eagerValue : eager I (fuel + 1) s 0 = .ok v) :
    bodyObservation I (fuel + 1) [{shape := s, loc := .calldata}] body =
      some (body (.cons v .nil)) ∧ cval I fuel s addr len = .ok v := by
  have hb : bodyValues I (fuel + 1) [{shape := s, loc := .calldata}]
      (.cons (.ref addr len) .nil) 0 = .ok (.cons v .nil) := by
    simp only [bodyValues, eagerValue, bind, Except.bind, pure, Except.pure]
  obtain ⟨a,n,hr,hv⟩ := eager_cref size eagerValue
  rw [reference] at hr
  cases hr
  exact ⟨body_from_entry I (fuel + 1) [{shape := s, loc := .calldata}] _ _ body entered hb, hv⟩

/-- Extracting an actual accepted value retains its real verdict witness. -/
theorem verdict_of_values {I : Input} {fuel : Nat} {ps : List Param}
    (vs : Vals (ps.map Param.shape))
    (h : bodyObservation I fuel ps id = some vs) : verdict I fuel ps = .run vs := by
  unfold bodyObservation at h
  cases hv : verdict I fuel ps with
  | revert => rw [hv] at h; cases h
  | blocked reason => rw [hv] at h; cases h
  | run actual => rw [hv] at h; cases h; rfl

/-- A checked single calldata head installs exactly the published reference. -/
theorem single_calldata_entry (I : Input) (fuel : Nat) (s : Shape) (addr len : Nat)
    (head : ¬ I.size < 4 + headsOf [{shape := s, loc := .calldata}])
    (reference : cref I s 4 0 = .ok (addr,len)) :
    entry I fuel [{shape := s, loc := .calldata}] = .ok (.cons (.ref addr len) .nil) := by
  simp only [entry, if_neg head, enter, reference, bind, Except.bind, pure, Except.pure]

/-- info: 'Solidity.Backend.AbiEntry.EntryTransport.rejection_iff' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms rejection_iff
/-- info: 'Solidity.Backend.AbiEntry.EntryTransport.entry_revert_exec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms entry_revert_exec
/-- info: 'Solidity.Backend.AbiEntry.EntryTransport.body_witness' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms body_witness
/-- info: 'Solidity.Backend.AbiEntry.EntryTransport.eager_lazy_body' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms eager_lazy_body
/-- info: 'Solidity.Backend.AbiEntry.EntryTransport.calldata_handoff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms calldata_handoff
/-- info: 'Solidity.Backend.AbiEntry.EntryTransport.verdict_revert_exec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms verdict_revert_exec
/-- info: 'Solidity.Backend.AbiEntry.EntryTransport.run_not_rejected' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms run_not_rejected
/-- info: 'Solidity.Backend.AbiEntry.EntryTransport.blocked_not_rejected' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms blocked_not_rejected
/-- info: 'Solidity.Backend.AbiEntry.EntryTransport.body_from_entry' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms body_from_entry
/-- info: 'Solidity.Backend.AbiEntry.EntryTransport.verdict_of_values' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms verdict_of_values
/-- info: 'Solidity.Backend.AbiEntry.EntryTransport.single_calldata_entry' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms single_calldata_entry
end Solidity.Backend.AbiEntry.EntryTransport
