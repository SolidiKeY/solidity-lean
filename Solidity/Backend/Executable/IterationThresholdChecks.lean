import Solidity.Backend.Executable.IterationThreshold
import Solidity.Backend.Executable.WorldPrefixChecks

/-! Genuine repeated paid calls: three settled successes before funding fails.
A distinct funded receive has its first failure at zero with ordered error
bytes. All reached worlds are actual full World values, not balance relations. -/
namespace Solidity.Backend.Executable.IterationThresholdChecks
open ContractWorld WorldPrefixes IterationThreshold WorldPrefixChecks
open PaymentCheckpointChecks (contracts sender fresh)

theorem fourth_payment : pay.run paidThree = .error .revert := by
  have observed : (match pay.run paidThree with
    | .ok _ => none | .error e => some e) = some THalt.revert := by decide +kernel
  cases ran : pay.run paidThree with
  | ok next => rw [ran] at observed; cases observed
  | error e =>
    rw [ran] at observed
    cases Option.some.inj observed
    rfl

theorem four_fail : (List.replicate 4 pay).foldlM
    (fun (w : World contracts) (op : Operation contracts) => op.run w) created = .error .revert := by
  rw [show 4 = 3+1 from rfl, iteration_split pay 3 1 created, three_payments]
  simp only [bind,Except.bind,List.replicate_succ,List.replicate_zero,List.foldlM_cons,fourth_payment]

/-- Full exact intermediate results for each successful prefix, including the
zero horizon; balances are observations of these same independently run worlds. -/
theorem intermediate_worlds :
    (List.replicate 0 pay).foldlM (fun (w : World contracts) (op : Operation contracts) => op.run w) created = .ok created ∧
    (List.replicate 1 pay).foldlM (fun (w : World contracts) (op : Operation contracts) => op.run w) created = .ok paidOne ∧
    (List.replicate 2 pay).foldlM (fun (w : World contracts) (op : Operation contracts) => op.run w) created = .ok paidTwo ∧
    (List.replicate 3 pay).foldlM (fun (w : World contracts) (op : Operation contracts) => op.run w) created = .ok paidThree := by
  refine ⟨rfl,?_,?_,three_payments⟩
  · simp only [List.replicate_succ,List.replicate_zero,List.foldlM_cons,List.foldlM_nil,
      first_payment,bind,Except.bind,pure,Except.pure]
  · simp only [List.replicate_succ,List.replicate_zero,List.foldlM_cons,List.foldlM_nil,
      first_payment,second_payment,bind,Except.bind,pure,Except.pure]

theorem balance_observations :
    [((created.funds sender).val,(created.funds fresh).val),
     ((paidOne.funds sender).val,(paidOne.funds fresh).val),
     ((paidTwo.funds sender).val,(paidTwo.funds fresh).val),
     ((paidThree.funds sender).val,(paidThree.funds fresh).val)] = [(3,0),(2,1),(1,2),(0,3)] := by decide +kernel

/-- Extract rather than assume k and the reached world from actual failure;
real earlier success/next error then identifies them as3 and paidThree. -/
theorem discovered : ∃ k middle, k < 4 ∧
    (List.replicate k pay).foldlM (fun (w : World contracts) (op : Operation contracts) => op.run w) created = .ok middle ∧
    pay.run middle = .error .revert ∧ k = 3 ∧ middle = paidThree ∧
    (∀ i, i ≤ k → ∃ reached, (List.replicate i pay).foldlM
      (fun (w : World contracts) (op : Operation contracts) => op.run w) created = .ok reached) ∧
    (∀ m, k < m → (List.replicate m pay).foldlM
      (fun (w : World contracts) (op : Operation contracts) => op.run w) created = .error .revert) := by
  obtain ⟨k,middle,bound,ran,failed,earlier,later,_⟩ := of_failure pay created 4 .revert four_fail
  obtain ⟨index,world,_⟩ := cut_unique pay created middle paidThree k 3 .revert .revert ran failed three_payments fourth_payment
  exact ⟨k,middle,bound,ran,failed,index,world,earlier,later⟩

theorem every_later (m : Nat) (later : 3 < m) : (List.replicate m pay).foldlM
    (fun (w : World contracts) (op : Operation contracts) => op.run w) created = .error .revert :=
  later_failure pay created paidThree 3 .revert three_payments fourth_payment m later

theorem no_wrong_threshold : ¬ ∃ middle e,
    (List.replicate 2 pay).foldlM (fun (w : World contracts) (op : Operation contracts) => op.run w) created = .ok middle ∧
    pay.run middle = .error e := by
  rintro ⟨middle,e,ran,failed⟩
  have wrong := (cut_unique pay created middle paidThree 2 3 e .revert ran failed three_payments fourth_payment).1
  cases wrong

theorem no_wrong_world : ¬ ∃ k e,
    (List.replicate k pay).foldlM (fun (w : World contracts) (op : Operation contracts) => op.run w) created = .ok paidTwo ∧
    pay.run paidTwo = .error e := by
  rintro ⟨k,e,ran,failed⟩
  have wrong := (cut_unique pay created paidTwo paidThree k 3 e .revert ran failed three_payments fourth_payment).2.1
  have distinct : (paidTwo.funds sender).val ≠ (paidThree.funds sender).val := by decide +kernel
  exact distinct (congrArg (fun w : World contracts => (w.funds sender).val) wrong)

theorem no_wrong_halt (m : Nat) (later : 3 < m) :
    (List.replicate m pay).foldlM (fun (w : World contracts) (op : Operation contracts) => op.run w) created ≠
      .error (.revertWith [0xde,0xad]) := by
  rw [every_later m later]
  intro wrong
  cases wrong

/-- A genuinely empty first-success prefix, with actual funded error bytes. -/
theorem first_failure : ∃ k middle, k < 1 ∧ k = 0 ∧ middle = paidTwo ∧
    (List.replicate k failPaid).foldlM (fun (w : World contracts) (op : Operation contracts) => op.run w) paidTwo = .ok middle ∧
    failPaid.run middle = .error (.revertWith [0xde,0xad]) ∧
    (∀ m, 0 < m → (List.replicate m failPaid).foldlM
      (fun (w : World contracts) (op : Operation contracts) => op.run w) paidTwo = .error (.revertWith [0xde,0xad])) := by
  have one : (List.replicate 1 failPaid).foldlM
      (fun (w : World contracts) (op : Operation contracts) => op.run w) paidTwo = .error (.revertWith [0xde,0xad]) := by
    simp only [List.replicate_succ,List.replicate_zero,List.foldlM_cons,funded_failure,bind,Except.bind]
  obtain ⟨k,middle,bound,ran,failed,_,later,_⟩ := of_failure failPaid paidTwo 1 (.revertWith [0xde,0xad]) one
  obtain ⟨index,world,_⟩ := cut_unique failPaid paidTwo middle paidTwo k 0
    (.revertWith [0xde,0xad]) (.revertWith [0xde,0xad]) ran failed rfl funded_failure
  refine ⟨k,middle,bound,index,world,ran,failed,?_⟩
  intro m positive
  apply later
  rw [index]
  exact positive

theorem zero_horizon : (List.replicate 0 failPaid).foldlM
    (fun (w : World contracts) (op : Operation contracts) => op.run w) paidTwo = .ok paidTwo := rfl

theorem no_reversed_bytes (m : Nat) (positive : 0 < m) :
    (List.replicate m failPaid).foldlM (fun (w : World contracts) (op : Operation contracts) => op.run w) paidTwo ≠
      .error (.revertWith [0xad,0xde]) := by
  rw [later_failure failPaid paidTwo paidTwo 0 (.revertWith [0xde,0xad]) rfl funded_failure m positive]
  intro wrong
  cases wrong
/-- info: 'Solidity.Backend.Executable.IterationThresholdChecks.fourth_payment' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms fourth_payment
/-- info: 'Solidity.Backend.Executable.IterationThresholdChecks.four_fail' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms four_fail
/-- info: 'Solidity.Backend.Executable.IterationThresholdChecks.intermediate_worlds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms intermediate_worlds
/-- info: 'Solidity.Backend.Executable.IterationThresholdChecks.balance_observations' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms balance_observations
/-- info: 'Solidity.Backend.Executable.IterationThresholdChecks.discovered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms discovered
/-- info: 'Solidity.Backend.Executable.IterationThresholdChecks.every_later' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms every_later
/-- info: 'Solidity.Backend.Executable.IterationThresholdChecks.no_wrong_threshold' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms no_wrong_threshold
/-- info: 'Solidity.Backend.Executable.IterationThresholdChecks.no_wrong_world' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms no_wrong_world
/-- info: 'Solidity.Backend.Executable.IterationThresholdChecks.no_wrong_halt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms no_wrong_halt
/-- info: 'Solidity.Backend.Executable.IterationThresholdChecks.first_failure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms first_failure
/-- info: 'Solidity.Backend.Executable.IterationThresholdChecks.zero_horizon' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms zero_horizon
/-- info: 'Solidity.Backend.Executable.IterationThresholdChecks.no_reversed_bytes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms no_reversed_bytes
end Solidity.Backend.Executable.IterationThresholdChecks
