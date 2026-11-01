import Solidity.Roadmap.V16.FiniteMemoryCompilation
import Solidity.Roadmap.V16.DispatchConsumer
import Solidity.Roadmap.V16.AbiEntryConsumer
import Solidity.Roadmap.V16.FiniteHeapConsumer
import Solidity.Roadmap.V16.CompilerConsumer
import Solidity.Roadmap.V16.ConstructionCompilation
import Solidity.Roadmap.V16.ConstructionConsumer
import Solidity.Roadmap.V16.MemoryLoopConsumer
import Solidity.Semantics.RunFuel
import Solidity.Roadmap.V16.Transactions

/-!
# Scoped loop-fuel consumers over the existing TLoop definitions

No loop rule, semantics, search bound or global source resource profile changes.
These facts are about actual finite TLoop executions, not pinned runtime code.
-/
namespace Solidity.Roadmap.V16

/-- An invariant survives every pending/successful finite loop iteration;
error observations are left unchanged, not identified with successful exits. -/
theorem loop_iteration_invariant {α : Type} (body : α → TRes α) (c : α → TRes Bool)
    (P : α → Prop) (keep : ∀ s t, P s → body s = .ok t → P t) :
    ∀ n s, P s → match TLoop.iterN body c n s with
      | .inl t => P t
      | .inr (.ok t) => P t
      | .inr (.error _) => True := by
  intro n
  induction n with
  | zero => intro s hs; exact hs
  | succ n ih =>
    intro s hs
    cases hc : c s with
    | error e => simp only [TLoop.iterN, TLoop.step, hc]
    | ok b =>
      cases b with
      | false => simpa only [TLoop.iterN, TLoop.step, hc] using hs
      | true =>
        cases hb : body s with
        | error e => simp only [TLoop.iterN, TLoop.step, hc, hb]
        | ok t =>
          simpa only [TLoop.iterN, TLoop.step, hc, hb] using ih t (keep s t hs hb)

/-- Consume the existing loop-fuel result only on an actual successful exit. -/
theorem loop_success_invariant {α : Type} (body : α → TRes α) (c : α → TRes Bool)
    (P : α → Prop) (keep : ∀ s t, P s → body s = .ok t → P t)
    {n : Nat} {s t : α} (hs : P s) (run : TLoop.runF body c n s = .ok t) : P t := by
  have inv := loop_iteration_invariant body c P keep n s hs
  unfold TLoop.runF at run
  cases hi : TLoop.iterN body c n s with
  | inl u => rw [hi] at run; cases run
  | inr r =>
    rw [hi] at run
    cases run
    simpa only [hi] using inv

/-- Every finite bound of a genuine no-failure identity-body/true-guard loop
is still pending. This is an existing TLoop execution, not G01 gas failure. -/
theorem forever_iteration {α : Type} (n : Nat) (s : α) :
    TLoop.iterN (fun x : α => .ok x) (fun _ => .ok true) n s = .inl s := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih

theorem forever_loop_fuel {C : Contract} {Γ : Ctx} (n : Nat) (s : State C Γ) :
    TLoop.runF (fun x : State C Γ => .ok x) (fun _ => .ok true) n s = .error .diverge := by
  unfold TLoop.runF
  rw [forever_iteration]

/-- A single exhausted iteration horizon cannot establish global divergence:
this loop exits at the very next bound. -/
theorem pending_is_not_divergence {C : Contract} {Γ : Ctx} (s : State C Γ) :
    TLoop.runF (fun x : State C Γ => .ok x) (fun _ => .ok false) 0 s = .error .diverge ∧
    TLoop.runF (fun x : State C Γ => .ok x) (fun _ => .ok false) 1 s = .ok s := ⟨rfl,rfl⟩

/-- Loop failure data remain failure data, not pending or successful exits. -/
theorem loop_revert_payload {C : Contract} {Γ : Ctx} (n : Nat) (s : State C Γ) :
    TLoop.runF (fun _ : State C Γ => .error (.revertWith [9])) (fun _ => .ok true)
      (n+1) s = .error (.revertWith [9]) := rfl
/-- Actual typed states inhabit the no-failure loop witness. -/
theorem forever_loop_inhabited : ∃ s : State (default : Contract) [], ∀ n,
    TLoop.runF (fun x => .ok x) (fun _ => .ok true) n s = .error .diverge :=
  ⟨State.init default, fun n => forever_loop_fuel n _⟩
end Solidity.Roadmap.V16
