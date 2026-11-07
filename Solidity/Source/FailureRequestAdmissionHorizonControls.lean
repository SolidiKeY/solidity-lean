import Solidity.Source.FailureRequestAdmissionHorizon
import Solidity.Source.FailureRequestAdmissionLaws

/-! Nonconstant-plan/current-ordinal and actual caller-alias controls. The
seed is an explicit quiescent cursor, not a claim of a whole session prefix.
Complete Source state, journals and bytes are compared. No native evidence. -/
namespace Solidity.Source.FailureExecution.AdmissionHorizonControls
open EM Controls

def points (balance : Nat) (cut : Option Nat) : Roadmap.Evm.FailurePoints where
  tx index := if index = 37 then .runs balance cut else .dropped
  frame index := some (index+2)
def input : St E := {journalSeed with resource := ⟨37,11,none,[],none⟩}
def finished : St E := {input with resource := ⟨38,11,none,[],none⟩}
def q7 : Roadmap.Request := AdmissionControls.q ⟨7,by decide⟩
def qMax : Roadmap.Request := AdmissionControls.q ⟨2^256-1,by decide⟩

def readBalance (balance : Nat) : EM E [.bytes .memory,.bool] (Nat × Roadmap.Bytes) := do
  let value ← lift ((← locals).getAt 0 (.bytes .memory))
  let bytes ← bytesOfRV F 1 (.val value)
  pure (balance,bytes)

def family : Nat → Nat → EM E [.bytes .memory,.bool] (Nat × Roadmap.Bytes)
  | 0, _ => halt .timeout
  | _+1, balance => readBalance balance

theorem readBalance_grow (balance : Nat) : Grow (readBalance balance) := by
  unfold readBalance
  grow_go [bytesOfRV_grow]

theorem family_step (horizon balance : Nat) :
    Approx (family horizon balance) (family (horizon+1) balance) := by
  cases horizon with
  | zero => exact Approx.timeout (readBalance_grow balance)
  | succ n => exact Approx.refl (readBalance_grow balance)

theorem current_ordinal_underfunded :
    (requestValueScope (points 6 (some 0)) q7 AdmissionControls.poison).run (caller,input) =
      (.ok none,(caller,finished)) := by rfl

theorem current_ordinal_wide_alias :
    (requestValueScope (points (2^256) none) qMax (family 1)).run (caller,input) =
      (.ok (some (2^256,[0xDE,0xAD])),(caller,finished)) := by rfl

theorem current_ordinal_zero_cut :
    (requestValueScope (points 7 (some 0)) q7 (family 1)).run (caller,input) =
      (.error (.revert []),(caller,finished)) := by rfl

theorem current_ordinal_timeout :
    (requestValueScope (points 7 none) q7 (family 0)).run (caller,input) =
      (.error .timeout,(caller,finished)) := by rfl

theorem current_ordinal_approx (horizon : Nat) :
    Approx (requestValueScope (points (2^256) none) qMax (family horizon))
      (requestValueScope (points (2^256) none) qMax (family (horizon+1))) :=
  requestValueScope_approx _ _ (family_step horizon)

/-- Changing the indexed fate to zero is detected even with equal body and
input state: the current request is now dropped rather than reading the alias. -/
theorem wrong_index_drops :
    (requestValueScope {points (2^256) none with
      tx := fun index => if index = 0 then .runs (2^256) none else .dropped}
      qMax (family 1)).run (caller,input) = (.ok none,(caller,finished)) := by rfl

def changedBytes : St E := {input with
  heap := (Heap.empty.alloc ⟨.bytes .memory, Data.bytes [0xAA,0xBB]⟩).1}

theorem same_length_wrong_bytes :
    ((requestValueScope (points (2^256) none) qMax (family 1)).run (caller,changedBytes)).1 =
      .ok (some (2^256,[0xAA,0xBB])) := by rfl

theorem full_bytes_discriminate :
    ((requestValueScope (points (2^256) none) qMax (family 1)).run (caller,changedBytes)).1 ≠
      .ok (some (2^256,[0xDE,0xAD])) := by
  rw [same_length_wrong_bytes]
  intro impossible
  cases impossible

end Solidity.Source.FailureExecution.AdmissionHorizonControls

/-- info: 'Solidity.Source.FailureExecution.request_value_underfunded_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Source.FailureExecution.request_value_underfunded_at

/-- info: 'Solidity.Source.FailureExecution.admission_at_funded' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Source.FailureExecution.admission_at_funded

/-- info: 'Solidity.Source.FailureExecution.request_value_admitted_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Source.FailureExecution.request_value_admitted_at

/-- info: 'Solidity.Source.FailureExecution.request_value_rejected_counters' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Source.FailureExecution.request_value_rejected_counters

/-- info: 'Solidity.Source.FailureExecution.requestValueScope_grow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Source.FailureExecution.requestValueScope_grow

/-- info: 'Solidity.Source.FailureExecution.requestValueScope_below' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Source.FailureExecution.requestValueScope_below

/-- info: 'Solidity.Source.FailureExecution.requestValueScope_approx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Source.FailureExecution.requestValueScope_approx

/-- info: 'Solidity.Source.FailureExecution.AdmissionHorizonControls.readBalance_grow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Source.FailureExecution.AdmissionHorizonControls.readBalance_grow

/-- info: 'Solidity.Source.FailureExecution.AdmissionHorizonControls.family_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Source.FailureExecution.AdmissionHorizonControls.family_step

/-- info: 'Solidity.Source.FailureExecution.AdmissionHorizonControls.current_ordinal_underfunded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Source.FailureExecution.AdmissionHorizonControls.current_ordinal_underfunded

/-- info: 'Solidity.Source.FailureExecution.AdmissionHorizonControls.current_ordinal_wide_alias' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Source.FailureExecution.AdmissionHorizonControls.current_ordinal_wide_alias

/-- info: 'Solidity.Source.FailureExecution.AdmissionHorizonControls.current_ordinal_zero_cut' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Source.FailureExecution.AdmissionHorizonControls.current_ordinal_zero_cut

/-- info: 'Solidity.Source.FailureExecution.AdmissionHorizonControls.current_ordinal_timeout' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Source.FailureExecution.AdmissionHorizonControls.current_ordinal_timeout

/-- info: 'Solidity.Source.FailureExecution.AdmissionHorizonControls.current_ordinal_approx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Source.FailureExecution.AdmissionHorizonControls.current_ordinal_approx

/-- info: 'Solidity.Source.FailureExecution.AdmissionHorizonControls.wrong_index_drops' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Source.FailureExecution.AdmissionHorizonControls.wrong_index_drops

/-- info: 'Solidity.Source.FailureExecution.AdmissionHorizonControls.same_length_wrong_bytes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Source.FailureExecution.AdmissionHorizonControls.same_length_wrong_bytes

/-- info: 'Solidity.Source.FailureExecution.AdmissionHorizonControls.full_bytes_discriminate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Source.FailureExecution.AdmissionHorizonControls.full_bytes_discriminate
