import Solidity.Backend.Executable.WorldPrefixes
import Solidity.Backend.Executable.PaymentCheckpointChecks

/-! Actual installation and funded calls witness finite-prefix transport,
failure ordering, exact bytes and outer checkpoint rollback. Unmetered world
API controls do not constitute a compiled payment/loop simulation. -/
namespace Solidity.Backend.Executable.WorldPrefixChecks
open ContractWorld WorldPrefixes
open PaymentCheckpointChecks (contracts sender fresh reference receive)

private def valueOr {α : Type} (r : TRes α) (fallback : α) : α :=
  match r with | .ok value => value | .error _ => fallback

private theorem recover_success {α : Type} (r : TRes α) (fallback : α)
    (present : r.toOption.isSome = true) :
    r = .ok (valueOr r fallback) := by
  cases r with
  | ok value => rfl
  | error e => cases present

private def errorCode {α : Type} : TRes α → Option THalt
  | .error e => some e
  | .ok _ => none

private theorem recover_failure {α : Type} (r : TRes α) (e : THalt)
    (failed : errorCode r = some e) : r = .error e := by
  cases r with
  | ok value => cases failed
  | error actual =>
    have same : actual = e := Option.some.inj failed
    cases same
    rfl

def one : Word := ⟨1, by decide⟩
def three : Word := ⟨3, by decide⟩
def initial : World contracts := World.empty contracts (fun a => if a = sender then three else PrimTy.dflt .uint)
def create : Operation contracts := .create () fresh .nil {sender}
def pay : Operation contracts := .call () reference (Entry.unit .nil true) {sender, mode := .ordinary one}
def failPaid : Operation contracts := .call () reference receive {sender, mode := .ordinary one}

def created : World contracts := match create.run initial with
  | .ok w => w | .error _ => initial
theorem create_run : create.run initial = .ok created := rfl

def paidOne : World contracts := valueOr (pay.run created) created
theorem first_payment : pay.run created = .ok paidOne :=
  recover_success (pay.run created) created (by decide +kernel)

def paidTwo : World contracts := valueOr (pay.run paidOne) paidOne
theorem second_payment : pay.run paidOne = .ok paidTwo :=
  recover_success (pay.run paidOne) paidOne (by decide +kernel)

def paidThree : World contracts := valueOr (pay.run paidTwo) paidTwo
theorem third_payment : pay.run paidTwo = .ok paidThree :=
  recover_success (pay.run paidTwo) paidTwo (by decide +kernel)

/-- Both caller debits and recipient credits are actual settled world effects. -/
example : ((paidTwo.funds sender).val, (paidTwo.funds fresh).val) = (1,2) := by decide +kernel
example : ((paidThree.funds sender).val, (paidThree.funds fresh).val) = (0,3) := by decide +kernel

/-- Three real repeated paid calls give an inhabited finite iteration. -/
theorem three_payments : (List.replicate 3 pay).foldlM
    (fun (w : World contracts) (op : Operation contracts) => op.run w) created = .ok paidThree := by
  simp only [List.replicate_succ, List.replicate_zero, List.foldlM_cons, List.foldlM_nil,
    first_payment, second_payment, third_payment, bind, Except.bind, pure, Except.pure]

theorem installed_paid_prefix : (create :: List.replicate 3 pay).foldlM
    (fun (w : World contracts) (op : Operation contracts) => op.run w) initial = .ok paidThree := by
  simp only [List.foldlM_cons, create_run, bind, Except.bind]
  exact three_payments

/-- Both nonempty iteration parts transport through the actual paidOne world. -/
theorem actual_iteration_cut :
    [pay].foldlM (fun (w : World contracts) (op : Operation contracts) => op.run w) created = .ok paidOne ∧
    (List.replicate 2 pay).foldlM (fun (w : World contracts) (op : Operation contracts) => op.run w) paidOne = .ok paidThree ∧
    (List.replicate 3 pay).foldlM (fun (w : World contracts) (op : Operation contracts) => op.run w) created = .ok paidThree := by
  have first : [pay].foldlM (fun (w : World contracts) (op : Operation contracts) => op.run w) created = .ok paidOne := by
    simp only [List.foldlM_cons, List.foldlM_nil, first_payment, bind, Except.bind, pure, Except.pure]
  have split := iteration_split pay 1 2 created
  rw [show List.replicate 1 pay = [pay] from rfl, first] at split
  simp only [bind, Except.bind] at split
  exact ⟨first, split.symm.trans three_payments, three_payments⟩

/-- Prefix extraction is two-sided, with the observed actual middle identified. -/
example : ∃ middle, [pay].foldlM (fun (w : World contracts) (op : Operation contracts) => op.run w) created = .ok middle ∧
    (List.replicate 2 pay).foldlM (fun (w : World contracts) (op : Operation contracts) => op.run w) middle = .ok paidThree ∧
    middle = paidOne := by
  obtain ⟨middle, first, rest⟩ := (success_iff [pay] (List.replicate 2 pay) created paidThree).mp three_payments
  have same : middle = paidOne := Except.ok.inj (first.symm.trans actual_iteration_cut.1)
  exact ⟨middle, first, rest, same⟩

/-- Funding refusal precedes even a recipient which would revert with data. -/
theorem unfunded_failure : failPaid.run paidThree = .error .revert :=
  recover_failure _ _ (by decide +kernel)

/-- With funds still available the real receive executes and exposes its bytes. -/
theorem funded_failure : failPaid.run paidTwo = .error (.revertWith [0xde,0xad]) :=
  recover_failure _ _ (by decide +kernel)

/-- A later unfunded failure rolls back creation and all three settled payments. -/
theorem rollback_prefix :
    atomic initial ((((create :: List.replicate 3 pay) ++ [failPaid]).foldlM (fun (w : World contracts) (op : Operation contracts) => op.run w) initial).map
      (fun next => (next, ()))) = (initial, .error .revert) :=
  atomic_suffix_failure _ _ initial paidThree .revert installed_paid_prefix (by simp only [List.foldlM_cons, unfunded_failure, bind, Except.bind])

/-- A failed real prefix blocks a later call which would itself succeed. -/
theorem failed_prefix_stops_successful_tail :
    [pay].foldlM (fun (w : World contracts) (op : Operation contracts) => op.run w) paidTwo = .ok paidThree ∧
    [failPaid, pay].foldlM (fun (w : World contracts) (op : Operation contracts) => op.run w) paidTwo =
      .error (.revertWith [0xde,0xad]) := by
  refine ⟨?_, prefix_failure [failPaid] [pay] paidTwo (.revertWith [0xde,0xad]) ?_⟩
  · simp only [List.foldlM_cons, List.foldlM_nil, third_payment, bind, Except.bind, pure, Except.pure]
  · simp only [List.foldlM_cons, funded_failure, bind, Except.bind]

/-- A separately successful prefix instead commits installed code and funds. -/
example : atomic initial (((create :: List.replicate 3 pay).foldlM (fun (w : World contracts) (op : Operation contracts) => op.run w) initial).map
    (fun next => (next, ()))) = (paidThree, .ok ()) :=
  atomic_prefix_success _ initial paidThree installed_paid_prefix

example : initial.accounts fresh = none ∧ (paidThree.accounts fresh).isSome = true := ⟨rfl, by decide +kernel⟩
example : THalt.data (.revertWith [0xde,0xad]) ≠ THalt.data .revert := by decide +kernel

/-- info: 'Solidity.Backend.Executable.WorldPrefixChecks.actual_iteration_cut' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms actual_iteration_cut
/-- info: 'Solidity.Backend.Executable.WorldPrefixChecks.failed_prefix_stops_successful_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms failed_prefix_stops_successful_tail
/-- info: 'Solidity.Backend.Executable.WorldPrefixChecks.three_payments' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms three_payments
/-- info: 'Solidity.Backend.Executable.WorldPrefixChecks.rollback_prefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms rollback_prefix
end Solidity.Backend.Executable.WorldPrefixChecks
