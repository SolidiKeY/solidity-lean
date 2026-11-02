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

/-- The exact successful prefix contains installation and three funded
calls. No suffix, including another successful installation, can replace the
fourth call's funding refusal with receiver bytes. -/
theorem funding_cut (rest : List (Operation contracts)) :
    ((create :: List.replicate 3 pay) ++ failPaid :: rest).foldlM
      (fun (w : World contracts) (op : Operation contracts) => op.run w) initial = .error .revert := by
  apply (failure_iff _ initial .revert).mpr
  exact ⟨create :: List.replicate 3 pay, failPaid, rest, paidThree,
    rfl, installed_paid_prefix, unfunded_failure⟩

/-- Reverse extraction applies to an inhabited paid execution, preserving the
exact original halt rather than merely asserting that some operation failed. -/
theorem extracted_cut (rest : List (Operation contracts)) :
    ∃ first op last middle,
      ((create :: List.replicate 3 pay) ++ failPaid :: rest) = first ++ op :: last ∧
      first.foldlM (fun (w : World contracts) (op : Operation contracts) => op.run w) initial = .ok middle ∧
      op.run middle = .error .revert :=
  (failure_iff _ initial .revert).mp (funding_cut rest)

/-- Negative control: a nonempty unreachable suffix cannot expose the funded
receiver's distinct error bytes after the sender has exhausted its funds. -/
theorem no_late_receiver_bytes (rest : List (Operation contracts)) :
    ((create :: List.replicate 3 pay) ++ failPaid :: pay :: rest).foldlM
      (fun (w : World contracts) (op : Operation contracts) => op.run w) initial ≠
        .error (.revertWith [0xde,0xad]) := by
  rw [funding_cut]
  intro bad
  cases bad

/-- Recovery of a failed cut does not turn its successful paid prefix into a
committed final world: the outer atomic boundary restores the original world. -/
theorem cut_rollback (rest : List (Operation contracts)) :
    atomic initial ((((create :: List.replicate 3 pay) ++ failPaid :: rest).foldlM
      (fun (w : World contracts) (op : Operation contracts) => op.run w) initial).map
        (fun next => (next, ()))) = (initial, .error .revert) := by
  rw [funding_cut]
  rfl

/-- Every real failure cut of this paid sequence identifies the same four
successful operations, exact unexecuted suffix and full paidThree world. -/
theorem funding_cut_identified (rest first : List (Operation contracts))
    (op : Operation contracts) (last : List (Operation contracts)) (middle : World contracts) (e : THalt)
    (shape : ((create :: List.replicate 3 pay) ++ failPaid :: rest) = first ++ op :: last)
    (ran : first.foldlM (fun (w : World contracts) (op : Operation contracts) => op.run w) initial = .ok middle)
    (failed : op.run middle = .error e) :
    first = create :: List.replicate 3 pay ∧ op = failPaid ∧ last = rest ∧
      middle = paidThree ∧ e = .revert :=
  failure_cut_unique first (create :: List.replicate 3 pay) op failPaid last rest
    initial middle paidThree e .revert shape.symm ran installed_paid_prefix failed unfunded_failure

/-- Existing existential extraction is strengthened by the independent
uniqueness law; the extracted middle is now identified, not postulated. -/
theorem extracted_cut_identified (rest : List (Operation contracts)) :
    ∃ first op last middle,
      ((create :: List.replicate 3 pay) ++ failPaid :: rest) = first ++ op :: last ∧
      first.foldlM (fun (w : World contracts) (op : Operation contracts) => op.run w) initial = .ok middle ∧
      op.run middle = .error .revert ∧ first.length = 4 ∧ middle = paidThree := by
  obtain ⟨first,op,last,middle,shape,ran,failed⟩ := extracted_cut rest
  obtain ⟨samePrefix,_,_,sameWorld,_⟩ := funding_cut_identified rest first op last middle .revert shape ran failed
  refine ⟨first,op,last,middle,shape,ran,failed,?_,sameWorld⟩
  rw [samePrefix]
  rfl

/-- A claimed earlier cut cannot hide a different failed call in the paid
prefix. The canonical prefix's length4 is derived from its actual contents. -/
theorem no_early_cut (rest : List (Operation contracts)) :
    ¬ ∃ first op last middle e,
      ((create :: List.replicate 3 pay) ++ failPaid :: rest) = first ++ op :: last ∧
      first.length = 3 ∧
      first.foldlM (fun (w : World contracts) (op : Operation contracts) => op.run w) initial = .ok middle ∧
      op.run middle = .error e := by
  rintro ⟨first,op,last,middle,e,shape,short,ran,failed⟩
  have same := (funding_cut_identified rest first op last middle e shape ran failed).1
  rw [same] at short
  cases short

/-- An intermediate world with one remaining sender word cannot be substituted
for the exhausted actual cut world, even if the same operation list is claimed. -/
theorem no_wrong_world_cut (rest : List (Operation contracts)) :
    ¬ ∃ first op last e,
      ((create :: List.replicate 3 pay) ++ failPaid :: rest) = first ++ op :: last ∧
      first.foldlM (fun (w : World contracts) (op : Operation contracts) => op.run w) initial = .ok paidTwo ∧
      op.run paidTwo = .error e := by
  rintro ⟨first,op,last,e,shape,ran,failed⟩
  have same := (funding_cut_identified rest first op last paidTwo e shape ran failed).2.2.2.1
  have different : (paidTwo.funds sender).val ≠ (paidThree.funds sender).val := by decide +kernel
  exact different (congrArg (fun w : World contracts => (w.funds sender).val) same)

/-- Empty successful prefix is independently inhabited by the funded receiver
failure; it preserves nonempty original error bytes rather than funding refusal. -/
theorem empty_cut_identified (first : List (Operation contracts))
    (op : Operation contracts) (last : List (Operation contracts)) (middle : World contracts) (e : THalt)
    (shape : [failPaid,pay] = first ++ op :: last)
    (ran : first.foldlM (fun (w : World contracts) (op : Operation contracts) => op.run w) paidTwo = .ok middle)
    (failed : op.run middle = .error e) :
    first = [] ∧ op = failPaid ∧ last = [pay] ∧ middle = paidTwo ∧ e = .revertWith [0xde,0xad] :=
  failure_cut_unique first [] op failPaid last [pay] paidTwo middle paidTwo e (.revertWith [0xde,0xad])
    shape.symm ran rfl failed funded_failure

/-- info: 'Solidity.Backend.Executable.WorldPrefixChecks.actual_iteration_cut' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms actual_iteration_cut
/-- info: 'Solidity.Backend.Executable.WorldPrefixChecks.failed_prefix_stops_successful_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms failed_prefix_stops_successful_tail
/-- info: 'Solidity.Backend.Executable.WorldPrefixChecks.three_payments' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms three_payments
/-- info: 'Solidity.Backend.Executable.WorldPrefixChecks.rollback_prefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms rollback_prefix
/-- info: 'Solidity.Backend.Executable.WorldPrefixChecks.funding_cut' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms funding_cut
/-- info: 'Solidity.Backend.Executable.WorldPrefixChecks.extracted_cut' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms extracted_cut
/-- info: 'Solidity.Backend.Executable.WorldPrefixChecks.no_late_receiver_bytes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms no_late_receiver_bytes
/-- info: 'Solidity.Backend.Executable.WorldPrefixChecks.cut_rollback' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms cut_rollback
/-- info: 'Solidity.Backend.Executable.WorldPrefixChecks.funding_cut_identified' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms funding_cut_identified
/-- info: 'Solidity.Backend.Executable.WorldPrefixChecks.extracted_cut_identified' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms extracted_cut_identified
/-- info: 'Solidity.Backend.Executable.WorldPrefixChecks.no_early_cut' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms no_early_cut
/-- info: 'Solidity.Backend.Executable.WorldPrefixChecks.no_wrong_world_cut' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms no_wrong_world_cut
/-- info: 'Solidity.Backend.Executable.WorldPrefixChecks.empty_cut_identified' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms empty_cut_identified
end Solidity.Backend.Executable.WorldPrefixChecks
