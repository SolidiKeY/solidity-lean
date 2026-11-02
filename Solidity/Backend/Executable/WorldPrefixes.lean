import Solidity.Backend.Executable.PaymentCheckpoint

/-!
# Finite-prefix algebra over actual existing world operations

This uses List.foldlM and ContractWorld.Operation.run unchanged. No operation
AST, payment semantics, loop interpreter, compiler simulation or divergence
semantics is added. Prefix worlds come from actual successful existing runs.
Atomic result algebra is not a claim that divergence/exhaustion is a completed
transaction or that the G43/G36.03 prerequisites are discharged.
-/
namespace Solidity.Backend.Executable.WorldPrefixes
open ContractWorld
variable {K : Type} [DecidableEq K] {contracts : K → Contract}

/-- Both directions of a successful finite sequence expose its actual prefix
and suffix worlds; no preservation relation is assumed by the consumer. -/
theorem success_iff (first rest : List (Operation contracts)) (before after : World contracts) :
    (first ++ rest).foldlM (fun (w : World contracts) (op : Operation contracts) => op.run w) before = .ok after ↔
      ∃ middle, first.foldlM (fun (w : World contracts) (op : Operation contracts) => op.run w) before = .ok middle ∧
        rest.foldlM (fun (w : World contracts) (op : Operation contracts) => op.run w) middle = .ok after := by
  rw [List.foldlM_append]
  cases ran : first.foldlM (fun (w : World contracts) (op : Operation contracts) => op.run w) before with
  | error e =>
    simp only [bind, Except.bind]
    constructor
    · intro bad; cases bad
    · rintro ⟨_, bad, _⟩; cases bad
  | ok middle =>
    simp only [bind, Except.bind]
    constructor
    · intro finished; exact ⟨middle, rfl, finished⟩
    · rintro ⟨other, equal, finished⟩
      cases Except.ok.inj equal
      exact finished

/-- An already failed prefix prevents every later operation from executing. -/
theorem prefix_failure (first rest : List (Operation contracts)) (before : World contracts)
    (e : THalt) (failed : first.foldlM (fun (w : World contracts) (op : Operation contracts) => op.run w) before = .error e) :
    (first ++ rest).foldlM (fun (w : World contracts) (op : Operation contracts) => op.run w) before = .error e := by
  rw [List.foldlM_append, failed]
  rfl

/-- A real successful prefix transports the suffix's exact failure unchanged. -/
theorem suffix_failure (first rest : List (Operation contracts)) (before middle : World contracts)
    (e : THalt) (prefixRan : first.foldlM (fun (w : World contracts) (op : Operation contracts) => op.run w) before = .ok middle)
    (failed : rest.foldlM (fun (w : World contracts) (op : Operation contracts) => op.run w) middle = .error e) :
    (first ++ rest).foldlM (fun (w : World contracts) (op : Operation contracts) => op.run w) before = .error e := by
  rw [List.foldlM_append, prefixRan]
  exact failed

/-- A failed finite execution has an actual first failing operation after a
successful prefix. Both directions retain the original halt, including bytes;
the remaining suffix is arbitrary and is never used to explain the failure.
This is decomposition of the existing fold, not a loop/divergence semantics. -/
theorem failure_iff (ops : List (Operation contracts)) (before : World contracts) (e : THalt) :
    ops.foldlM (fun (w : World contracts) (op : Operation contracts) => op.run w) before = .error e ↔
      ∃ first op rest middle,
        ops = first ++ op :: rest ∧
        first.foldlM (fun (w : World contracts) (op : Operation contracts) => op.run w) before = .ok middle ∧
        op.run middle = .error e := by
  constructor
  · induction ops generalizing before with
    | nil => intro bad; cases bad
    | cons op rest ih =>
      intro failed
      cases ran : op.run before with
      | error original =>
        simp only [List.foldlM_cons, ran, bind, Except.bind] at failed
        cases Except.error.inj failed
        exact ⟨[], op, rest, before, rfl, rfl, ran⟩
      | ok next =>
        simp only [List.foldlM_cons, ran, bind, Except.bind] at failed
        obtain ⟨first, bad, last, middle, shape, prefixRan, badRun⟩ := ih next failed
        refine ⟨op :: first, bad, last, middle, ?_, ?_, badRun⟩
        · rw [List.cons_append, shape]
        · simp only [List.foldlM_cons, ran, bind, Except.bind, prefixRan]
  · rintro ⟨first, op, rest, middle, rfl, prefixRan, badRun⟩
    exact suffix_failure first (op :: rest) before middle e prefixRan (by
      simp only [List.foldlM_cons, badRun, bind, Except.bind])

/-- Two actual successful-prefix/failing-operation cuts of the same list
have the same prefix, failing operation, unexecuted suffix, reached world and
original halt. First means top-level Operation, not a caught internal failure. -/
theorem failure_cut_unique (first second : List (Operation contracts))
    (op1 op2 : Operation contracts) (rest1 rest2 : List (Operation contracts))
    (before middle1 middle2 : World contracts) (e1 e2 : THalt)
    (shape : first ++ op1 :: rest1 = second ++ op2 :: rest2)
    (ran1 : first.foldlM (fun (w : World contracts) (op : Operation contracts) => op.run w) before = .ok middle1)
    (ran2 : second.foldlM (fun (w : World contracts) (op : Operation contracts) => op.run w) before = .ok middle2)
    (failed1 : op1.run middle1 = .error e1) (failed2 : op2.run middle2 = .error e2) :
    first = second ∧ op1 = op2 ∧ rest1 = rest2 ∧ middle1 = middle2 ∧ e1 = e2 := by
  induction first generalizing before second with
  | nil =>
    have same1 : before = middle1 := Except.ok.inj ran1
    cases same1
    cases second with
    | nil =>
      have same2 : middle1 = middle2 := Except.ok.inj ran2
      cases same2
      obtain ⟨sameOp,sameRest⟩ := List.cons.inj shape
      cases sameOp
      cases sameRest
      exact ⟨rfl,rfl,rfl,rfl,Except.error.inj (failed1.symm.trans failed2)⟩
    | cons x xs =>
      have sameOp : op1 = x := (List.cons.inj shape).1
      subst x
      simp only [List.foldlM_cons,failed1,bind,Except.bind] at ran2
      cases ran2
  | cons x xs ih =>
    cases second with
    | nil =>
      have same2 : before = middle2 := Except.ok.inj ran2
      cases same2
      have sameOp : x = op2 := (List.cons.inj shape).1
      subst x
      simp only [List.foldlM_cons,failed2,bind,Except.bind] at ran1
      cases ran1
    | cons y ys =>
      obtain ⟨sameHead,sameTail⟩ := List.cons.inj shape
      subst y
      cases step : x.run before with
      | error e =>
        simp only [List.foldlM_cons,step,bind,Except.bind] at ran1
        cases ran1
      | ok next =>
        simp only [List.foldlM_cons,step,bind,Except.bind] at ran1 ran2
        obtain ⟨samePrefix,sameOp,sameRest,sameWorld,sameHalt⟩ :=
          ih (before := next) (second := ys) sameTail ran1 ran2
        exact ⟨congrArg (List.cons x) samePrefix,sameOp,sameRest,sameWorld,sameHalt⟩

/-- Exact cuts at every list position, including empty/whole prefixes. -/
theorem cut_success_iff (ops : List (Operation contracts)) (n : Nat)
    (before after : World contracts) :
    ops.foldlM (fun (w : World contracts) (op : Operation contracts) => op.run w) before = .ok after ↔
      ∃ middle, (ops.take n).foldlM (fun (w : World contracts) (op : Operation contracts) => op.run w) before = .ok middle ∧
        (ops.drop n).foldlM (fun (w : World contracts) (op : Operation contracts) => op.run w) middle = .ok after := by
  simpa only [List.take_append_drop] using success_iff (ops.take n) (ops.drop n) before after

/-- Finite iteration transport reuses existing list replication/folding, with
actual world effects at each call; it does not define an effectful loop run. -/
theorem iteration_split (op : Operation contracts) (n m : Nat) (before : World contracts) :
    (List.replicate (n+m) op).foldlM (fun (w : World contracts) (op : Operation contracts) => op.run w) before =
      ((List.replicate n op).foldlM (fun (w : World contracts) (op : Operation contracts) => op.run w) before >>= fun middle =>
        (List.replicate m op).foldlM (fun (w : World contracts) (op : Operation contracts) => op.run w) middle) := by
  rw [← List.replicate_append_replicate (n := n) (m := m) (a := op), List.foldlM_append]

/-- Once a later operation fails, the existing outer checkpoint restores all
world effects of a successful finite prefix and retains the exact halt bytes. -/
theorem atomic_suffix_failure (first rest : List (Operation contracts))
    (before middle : World contracts) (e : THalt)
    (prefixRan : first.foldlM (fun (w : World contracts) (op : Operation contracts) => op.run w) before = .ok middle)
    (failed : rest.foldlM (fun (w : World contracts) (op : Operation contracts) => op.run w) middle = .error e) :
    atomic before (((first ++ rest).foldlM (fun (w : World contracts) (op : Operation contracts) => op.run w) before).map (fun next => (next, ()))) =
      (before, .error e) := by
  rw [suffix_failure first rest before middle e prefixRan failed]
  rfl

/-- A successful prefix can separately commit its actual world. That world
need not equal the one restored by a later outer rollback. -/
theorem atomic_prefix_success (first : List (Operation contracts)) (before middle : World contracts)
    (ran : first.foldlM (fun (w : World contracts) (op : Operation contracts) => op.run w) before = .ok middle) :
    atomic before ((first.foldlM (fun (w : World contracts) (op : Operation contracts) => op.run w) before).map (fun next => (next, ()))) =
      (middle, .ok ()) := by
  rw [ran]
  rfl

/-- info: 'Solidity.Backend.Executable.WorldPrefixes.success_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms success_iff
/-- info: 'Solidity.Backend.Executable.WorldPrefixes.cut_success_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms cut_success_iff
/-- info: 'Solidity.Backend.Executable.WorldPrefixes.iteration_split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms iteration_split
/-- info: 'Solidity.Backend.Executable.WorldPrefixes.atomic_suffix_failure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms atomic_suffix_failure
/-- info: 'Solidity.Backend.Executable.WorldPrefixes.failure_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms failure_iff
/-- info: 'Solidity.Backend.Executable.WorldPrefixes.failure_cut_unique' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms failure_cut_unique
end Solidity.Backend.Executable.WorldPrefixes
