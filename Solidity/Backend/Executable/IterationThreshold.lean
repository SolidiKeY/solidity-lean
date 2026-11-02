import Solidity.Backend.Executable.WorldPrefixes

/-! Exact finite failure thresholds for repeated actual operations. All runs
are the existing List.replicate/foldlM/ContractWorld.Operation.run. No loop,
trace, world or compiler semantics is introduced. A finite error (including a
resource/divergence halt) is not certified as a completed transaction. -/
namespace Solidity.Backend.Executable.IterationThreshold
open ContractWorld WorldPrefixes
variable {K : Type} [DecidableEq K] {contracts : K → Contract}

theorem cut_unique (op : Operation contracts) (before middle other : World contracts)
    (k l : Nat) (e e' : THalt)
    (ranK : (List.replicate k op).foldlM (fun (w : World contracts) (op : Operation contracts) => op.run w) before = .ok middle)
    (failure : op.run middle = .error e)
    (ranK' : (List.replicate l op).foldlM (fun (w : World contracts) (op : Operation contracts) => op.run w) before = .ok other)
    (failure' : op.run other = .error e') : k = l ∧ middle = other ∧ e = e' := by
  have shape : List.replicate k op ++ op :: List.replicate l op =
      List.replicate l op ++ op :: List.replicate k op := by
    rw [← List.replicate_succ, ← List.replicate_succ,
      List.replicate_append_replicate, List.replicate_append_replicate]
    congr 1
    omega
  obtain ⟨same,_,_,world,halt⟩ := failure_cut_unique (List.replicate k op) (List.replicate l op)
    op op (List.replicate l op) (List.replicate k op) before middle other e e'
    shape ranK ranK' failure failure'
  have lengths := congrArg List.length same
  simp only [List.length_replicate] at lengths
  exact ⟨lengths,world,halt⟩

theorem earlier_success (op : Operation contracts) (before middle : World contracts)
    (k : Nat) (ranK : (List.replicate k op).foldlM
      (fun (w : World contracts) (op : Operation contracts) => op.run w) before = .ok middle)
    (i : Nat) (earlier : i ≤ k) :
    ∃ reached, (List.replicate i op).foldlM
      (fun (w : World contracts) (op : Operation contracts) => op.run w) before = .ok reached := by
  have shape : List.replicate i op ++ List.replicate (k-i) op = List.replicate k op := by
    rw [List.replicate_append_replicate]
    congr 1
    omega
  obtain ⟨reached,ran,_⟩ := (success_iff (List.replicate i op) (List.replicate (k-i) op) before middle).mp
    (by rw [shape]; exact ranK)
  exact ⟨reached,ran⟩

theorem later_failure (op : Operation contracts) (before middle : World contracts)
    (k : Nat) (e : THalt)
    (ranK : (List.replicate k op).foldlM (fun (w : World contracts) (op : Operation contracts) => op.run w) before = .ok middle)
    (failure : op.run middle = .error e) (m : Nat) (later : k < m) :
    (List.replicate m op).foldlM (fun (w : World contracts) (op : Operation contracts) => op.run w) before = .error e := by
  have next : (List.replicate (k+1) op).foldlM
      (fun (w : World contracts) (op : Operation contracts) => op.run w) before = .error e := by
    rw [iteration_split op k 1 before, ranK]
    simp only [bind, Except.bind, List.replicate_succ, List.replicate_zero, List.foldlM_cons, failure]
  have split := iteration_split op (k+1) (m-(k+1)) before
  have total : (k+1)+(m-(k+1)) = m := by omega
  rw [total,next] at split
  exact split.trans rfl

/-- An observed finite repeated failure derives the threshold and full reached
World. k counts successful iterations; the next (k+1)st operation fails. Its
uniqueness is global, not restricted to the observed finite horizon. -/
theorem of_failure (op : Operation contracts) (before : World contracts) (n : Nat) (e : THalt)
    (failed : (List.replicate n op).foldlM
      (fun (w : World contracts) (op : Operation contracts) => op.run w) before = .error e) :
    ∃ k middle, k < n ∧
      (List.replicate k op).foldlM (fun (w : World contracts) (op : Operation contracts) => op.run w) before = .ok middle ∧
      op.run middle = .error e ∧
      (∀ i, i ≤ k → ∃ reached, (List.replicate i op).foldlM
        (fun (w : World contracts) (op : Operation contracts) => op.run w) before = .ok reached) ∧
      (∀ m, k < m → (List.replicate m op).foldlM
        (fun (w : World contracts) (op : Operation contracts) => op.run w) before = .error e) ∧
      (∀ l other e', (List.replicate l op).foldlM
          (fun (w : World contracts) (op : Operation contracts) => op.run w) before = .ok other →
        op.run other = .error e' → l = k ∧ other = middle ∧ e' = e) := by
  obtain ⟨first,bad,rest,middle,shape,ran,halt⟩ := (failure_iff _ before e).mp failed
  obtain ⟨lengths,prefixShape,_⟩ := List.replicate_eq_append_iff.mp shape
  have member : bad ∈ List.replicate n op := by
    rw [shape]
    exact List.mem_append_right first List.mem_cons_self
  have same : bad = op := List.eq_of_mem_replicate member
  subst bad
  have ranK : (List.replicate first.length op).foldlM
      (fun (w : World contracts) (op : Operation contracts) => op.run w) before = .ok middle := by
    rw [← prefixShape]
    exact ran
  refine ⟨first.length,middle,?_,ranK,halt,earlier_success op before middle _ ranK,
    later_failure op before middle _ e ranK halt,?_⟩
  · simp only [List.length_cons] at lengths
    omega
  · intro l other e' ranK' halt'
    exact cut_unique op before other middle l first.length e' e ranK' halt' ranK halt
/-- info: 'Solidity.Backend.Executable.IterationThreshold.cut_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms cut_unique
/-- info: 'Solidity.Backend.Executable.IterationThreshold.earlier_success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms earlier_success
/-- info: 'Solidity.Backend.Executable.IterationThreshold.later_failure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms later_failure
/-- info: 'Solidity.Backend.Executable.IterationThreshold.of_failure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms of_failure
end Solidity.Backend.Executable.IterationThreshold
