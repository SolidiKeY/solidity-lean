import Solidity.Semantics.Run
import Solidity.Syntax.DispatchChain

/-!
# Which arm a dispatch takes

A finite dispatch (`DispatchArm.chain`) runs exactly the first arm whose
guard holds, its locals popped, and the failure statement when no guard
holds. For guards that evaluate as `tag == tᵢ` over candidate tags, a run
with tag value `tᵢ` runs arm `i` (`chain_tag`). Two links to the elaborator
are by construction, not proved here: that `fnDispatch`'s guards evaluate so,
and that arm `i`'s body is the direct call of candidate `i`
(`docs/feature-work/finite-dispatch.md`, "Dispatch correctness").
-/

namespace Solidity

variable {C : Contract}

namespace DispatchArm

/-- A guard that holds selects its arm. -/
theorem chain_hit {Γ : Ctx} (a : DispatchArm C Γ) (as : List (DispatchArm C Γ))
    (fail : Stmt C Γ Γ) (σ : State C Γ) (h : a.cond.evalT σ = .ok true) :
    Stmt.runC (chain (a :: as) fail) σ =
      (Prog.runC a.body σ).map fun o => ⟨o.st.drop a.body.ext, o.ext⟩ := by
  simp only [chain, Stmt.runC, TRun.ite, h]
  rfl

/-- A guard that is false passes to the rest of the chain. -/
theorem chain_miss {Γ : Ctx} (a : DispatchArm C Γ) (as : List (DispatchArm C Γ))
    (fail : Stmt C Γ Γ) (σ : State C Γ) (h : a.cond.evalT σ = .ok false) :
    Stmt.runC (chain (a :: as) fail) σ = Stmt.runC (chain as fail) σ := by
  simp only [chain, Stmt.runC, TRun.ite, h]
  show (Prog.runC (Prog.cons (chain as fail) .nil) σ).map _ = _
  simp only [Prog.runC, TRun.seq, TRun.nil]
  cases Stmt.runC (chain as fail) σ with
  | error e => rfl
  | ok o =>
    obtain ⟨st, x⟩ := o
    simp only [Except.map]
    have e : (Prog.cons (chain as fail) Prog.nil).ext = Ext.refl := Ext.eq_of_depth _ _
    rw [e]
    rfl

/-- **Selection.** The first arm whose guard holds runs, every earlier
guard false. -/
theorem chain_select {Γ : Ctx} (pre : List (DispatchArm C Γ)) (a : DispatchArm C Γ)
    (post : List (DispatchArm C Γ)) (fail : Stmt C Γ Γ) (σ : State C Γ)
    (hpre : ∀ b ∈ pre, b.cond.evalT σ = .ok false) (h : a.cond.evalT σ = .ok true) :
    Stmt.runC (chain (pre ++ a :: post) fail) σ =
      (Prog.runC a.body σ).map fun o => ⟨o.st.drop a.body.ext, o.ext⟩ := by
  induction pre with
  | nil => exact chain_hit a post fail σ h
  | cons b pre ih =>
    rw [List.cons_append, chain_miss b _ fail σ (hpre b (List.mem_cons_self ..))]
    exact ih fun b' hb' => hpre b' (List.mem_cons_of_mem _ hb')

/-- **No candidate.** When every guard is false the failure statement runs:
the unassigned or foreign tag's revert. -/
theorem chain_none {Γ : Ctx} (as : List (DispatchArm C Γ)) (fail : Stmt C Γ Γ)
    (σ : State C Γ) (hall : ∀ b ∈ as, b.cond.evalT σ = .ok false) :
    Stmt.runC (chain as fail) σ = Stmt.runC fail σ := by
  induction as with
  | nil => rfl
  | cons b as ih =>
    rw [chain_miss b as fail σ (hall b (List.mem_cons_self ..))]
    exact ih fun b' hb' => hall b' (List.mem_cons_of_mem _ hb')

/-- **Per-tag selection.** Arms guarded by `tag == tᵢ`
(`guard`: in `σ` each guard of the chain is the comparison of the tag's value `v`
with the arm's candidate tag `tagOf`): when `v` is the tag of arm `a`, and no
earlier arm has that tag, the dispatch runs `a`'s body. -/
theorem chain_tag {Γ : Ctx} (σ : State C Γ) (tagOf : DispatchArm C Γ → Nat) (v : Nat)
    (pre : List (DispatchArm C Γ)) (a : DispatchArm C Γ) (post : List (DispatchArm C Γ))
    (fail : Stmt C Γ Γ)
    (guard : ∀ b ∈ pre ++ a :: post, b.cond.evalT σ = .ok (decide (v = tagOf b)))
    (hfirst : tagOf a ∉ pre.map tagOf) (hv : v = tagOf a) :
    Stmt.runC (chain (pre ++ a :: post) fail) σ =
      (Prog.runC a.body σ).map fun o => ⟨o.st.drop a.body.ext, o.ext⟩ := by
  refine chain_select pre a post fail σ (fun b hb => ?_) ?_
  · rw [guard b (List.mem_append_left _ hb)]
    have hne : v ≠ tagOf b := fun e => hfirst (by rw [← hv, e]; exact List.mem_map_of_mem hb)
    simp only [hne, decide_false]
  · rw [guard a (List.mem_append_right _ (List.mem_cons_self ..)), hv]
    simp only [decide_true]

end DispatchArm

/-- info: 'Solidity.DispatchArm.chain_tag' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms DispatchArm.chain_tag

/-- info: 'Solidity.DispatchArm.chain_select' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms DispatchArm.chain_select

/-- info: 'Solidity.DispatchArm.chain_none' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms DispatchArm.chain_none

end Solidity
