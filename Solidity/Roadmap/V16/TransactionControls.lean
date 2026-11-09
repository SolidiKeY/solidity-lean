import Solidity.Roadmap.V16.Transactions
import Solidity.Roadmap.V16.Relational
import Solidity.Roadmap.V16.TransportControls

/-!
# Actual intrinsic commit/rollback/wait and divergence controls

System values below execute published Prog.run/deployT/Lifetime definitions;
no execution semantics or global admissible profile is added or modified.
-/
namespace Solidity.Roadmap.V16.TransactionControls
open Solidity.Lifetime
open Solidity.Roadmap.Controls

def contract : Contract := default

def system : Lifetime.System contract Unit Bool where
  deploy _ := .nil
  call fail := if fail then .cons (.revertData [.bytes [9]]) .nil else .nil

def deployTx : TTx := { selfAddress := ⟨9, rfl⟩, msgSender := ⟨7, rfl⟩ }
def callTx : TTx := { deployTx with msgSender := ⟨8, rfl⟩ }
def start : Lifetime.World contract := Lifetime.World.ofState (State.deploy contract deployTx)

theorem deployed : system.Init start := ⟨(), deployTx, _, trivial, rfl, rfl⟩
theorem accepted : start.accepts callTx := ⟨rfl, Int.le_refl _, by decide⟩

/-- A genuine successful call and an exact payload-preserving failed call. -/
theorem commit_run : system.run start false callTx = .ok start := rfl
theorem rollback_run : system.run start true callTx = .error (.revertWith [9]) := rfl

theorem commit_step : Lifetime.Step system start (.call false callTx) start :=
  .commit accepted trivial commit_run

theorem rollback_step : Lifetime.Step system start (.call true callTx) start :=
  .rollback accepted trivial rollback_run (.inr (.inl ⟨[9], rfl⟩))

/-- Nonempty ordered events include commit, revert-with-data and waiting. -/
theorem event_trace : Lifetime.Trace system start
    [.call false callTx, .call true callTx, .wait ⟨1, rfl⟩] (start.atTime ⟨1, rfl⟩) :=
  .cons commit_step (.cons rollback_step (.cons (.wait (by decide)) (.nil _)))

/-- Exercise the NEW trace induction on an actual existing execution.
The identity step relation is proved, rather than supplied as an oracle. -/
theorem transported_event_trace : ∃ t,
    Lifetime.Trace system start
      ([.call false callTx, .call true callTx, .wait ⟨1, rfl⟩].map id) t ∧
      start.atTime ⟨1, rfl⟩ = t := by
  apply trace_transport (M₂ := system) (fun s t => s = t) id ?_ event_trace rfl
  intro s t u a hu hn
  subst u
  exact ⟨t, hn, rfl⟩

/-- Removing or reordering events is not an observation-preserving map. -/
theorem wrong_event_order :
    ([Lifetime.Event.call false callTx, .call true callTx, .wait ⟨1, rfl⟩].map id) ≠
      [.call true callTx, .call false callTx, .wait ⟨1, rfl⟩] := by
  intro h
  cases h

/-- Refute wrong revert bytes using NEW completion transport itself. -/
theorem wrong_revert_after_transport :
    (toyLang.sem (idPass.run (.fail [9]) trivial) quietEnv
      (idCert.need (.fail [9]) trivial quietEnv ⟨1, false⟩)).final ≠
      some (.revert [8]) := by
  intro wrong
  have exactPrefix := completion_at_need idCert (.fail [9]) trivial quietEnv quietEnv_allowed
    ⟨1, false⟩ trivial (toy_forward _ _ _).1 (toy_forward _ _ _).2 (o := .revert [9]) rfl
  have heq := congrArg Prefix.final exactPrefix.2
  rw [heq] at wrong
  cases wrong

/-- The NEW trace-invariant induction rejects a non-preserved timestamp
predicate on an actual reached state and actual wait event. -/
theorem invalid_timestamp_invariant :
    ¬ Lifetime.Invariant system (fun s => s.timestamp.1 = 0) := by
  intro inv
  have initial : start.timestamp.1 = 0 := rfl
  have final := trace_invariant inv event_trace initial
  change (1 : Int) = 0 at final
  cases final

/-- No-failure looping uses the existing Forward predicate as a local
observation restriction. All globally admissible failure bounds still exist. -/
theorem no_failure_divergence : (toyLang.sem .loop quietEnv).Diverges
    (fun r => toyLang.Admissible r ∧ toyLang.Forward .loop quietEnv r) := by
  intro r hr
  have hf : r.exhausted = false := hr.2.1
  change (Toy.loop.run r.exhausted).final = none
  rw [hf]
  rfl

/-- The restricted resource set is inhabited; divergence is not vacuous. -/
theorem no_failure_bound_inhabited : ∃ r,
    toyLang.Admissible r ∧ toyLang.Forward .loop quietEnv r :=
  ⟨⟨1, false⟩, trivial, (toy_forward _ _ _).1⟩

/-- Exercise NEW relational composition with that SAME local resource set,
without claiming the unrestricted G01 admissible family diverges. -/
theorem no_failure_composition :
    Refines (fun r => toyLang.Admissible r ∧ toyLang.Forward .loop quietEnv r)
      (fun r => toyLang.Admissible r ∧ toyLang.Forward .loop quietEnv r)
      (toyLang.sem .loop quietEnv) (toyLang.sem .loop quietEnv) :=
  (refinement_refl _ _).trans (refinement_refl _ _)

end Solidity.Roadmap.V16.TransactionControls
