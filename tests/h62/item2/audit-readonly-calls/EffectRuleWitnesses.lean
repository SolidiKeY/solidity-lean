import Solidity.Lowering.Readonly.EffectRules

/-! Guard separate effect-premise inhabitants being mistaken for a joint witness.
Concrete Source computations, locals and state supply all inputs of each original
EffectRules theorem; event order and caught revert retain their actual observations.
These are premise-satisfiability applications, not Source program/compiler, callback,
ABI, gas/fork or whole-contract adequacy. The same file is checked at the frozen
base and current source; no changed dependency is substituted for the frozen proof. -/
namespace Solidity.H62.ReadonlyAudit.EffectRuleWitnesses
open Solidity.Source Solidity.Lowering.Readonly Solidity.Lowering.Readonly.SourceHistory

def environment : Env := ⟨[]⟩
def context : RCtx := [.bool]
def input : Locals environment.layout context := .cons (.bool true) .nil
def changed : Locals environment.layout context := .cons (.bool false) .nil

def seed : St environment :=
  { ex := {world := ⟨fun _ => Account.empty _⟩,transient := ⟨fun _ => Storage.empty⟩,journal := []}
    heap := Heap.empty,events := [],logs := [],fnLocals := ⟨[],.nil⟩ }

def firstEvent : Solidity.Roadmap.Event := .answer (.success [17]) none
def nextEvent : Solidity.Roadmap.Event := .answer (.revert [23]) none

def first : EM environment context Unit := emitEvent firstEvent
def next (_ : Unit) : EM environment context Unit := emitEvent nextEvent

def failed : EM environment context Unit := do
  emitEvent firstEvent
  EM.halt (.revert [7])

theorem event_effect (mode : Bool) (event : Solidity.Roadmap.Event) :
    Effect mode (emitEvent event : EM environment context Unit) :=
  Effect.of_same_ex mode _ (fun _ _ => rfl)

theorem failure_effect (mode : Bool) : Effect mode failed :=
  Effect.of_same_ex mode _ (fun _ _ => rfl)

theorem of_same_ex_joint :
    (∀ (l : Locals environment.layout context) (s : St environment),
      (first.run (l,s)).2.2.ex = s.ex) ∧
    StaticJournal.History seed.ex true (first.run (input,seed)).2.2.ex :=
  ⟨(fun _ _ => rfl),Effect.of_same_ex true first (fun _ _ => rfl) input seed⟩

theorem bind_joint :
    (Effect true first ∧ ∀ u : Unit, Effect true (next u)) ∧
    StaticJournal.History seed.ex true ((first >>= next).run (input,seed)).2.2.ex :=
  ⟨⟨event_effect true firstEvent,fun _ => event_effect true nextEvent⟩,
    Effect.bind true first next (event_effect true firstEvent)
      (fun _ => event_effect true nextEvent) input seed⟩

theorem sub_joint :
    Effect true first ∧
    StaticJournal.History seed.ex true
      ((EM.sub (Γ := []) input first).run (.nil,seed)).2.2.ex :=
  ⟨event_effect true firstEvent,
    Effect.sub true input first (event_effect true firstEvent) .nil seed⟩

theorem attempt_joint :
    Effect true failed ∧
    StaticJournal.History seed.ex true ((EM.attempt failed).run (input,seed)).2.2.ex :=
  ⟨failure_effect true,Effect.attempt true failed (failure_effect true) input seed⟩

theorem parent_joint :
    Effect (true || false) first ∧
    StaticJournal.History seed.ex false (first.run (input,seed)).2.2.ex :=
  ⟨event_effect (true || false) firstEvent,
    Effect.parent false true first (event_effect (true || false) firstEvent) input seed⟩

theorem pure_joint :
    StaticJournal.History seed.ex false
      ((Pure.pure (37 : Nat) : EM environment context Nat).run (input,seed)).2.2.ex :=
  Effect.pure false (37 : Nat) input seed

theorem halt_joint :
    StaticJournal.History seed.ex true
      ((EM.halt (.revert [7]) : EM environment context Unit).run (input,seed)).2.2.ex :=
  Effect.halt true (.revert [7]) input seed

theorem st_joint :
    StaticJournal.History seed.ex true
      ((EM.st : EM environment context (St environment)).run (input,seed)).2.2.ex :=
  Effect.st true input seed

theorem locals_joint :
    StaticJournal.History seed.ex true
      ((EM.locals : EM environment context (Locals environment.layout context)).run (input,seed)).2.2.ex :=
  Effect.locals true input seed

theorem setLocals_joint :
    StaticJournal.History seed.ex true
      ((EM.setLocals changed : EM environment context Unit).run (input,seed)).2.2.ex :=
  Effect.setLocals true changed input seed

/-- Effect preserves the journaled world; observable events still change. -/
theorem event_order :
    (first >>= next).run (input,seed) =
      (.ok (), (input,{seed with events := [firstEvent,nextEvent]})) := rfl

/-- Catching a halt retains its reached events and exact failure bytes. -/
theorem attempted_failure :
    (EM.attempt failed).run (input,seed) =
      (.ok (.error (.revert [7])),(input,{seed with events := [firstEvent]})) := rfl

theorem sub_observed :
    (EM.sub (Γ := []) input first).run (.nil,seed) =
      (.ok ((),input),(.nil,{seed with events := [firstEvent]})) := rfl

theorem locals_observed :
    (EM.setLocals changed : EM environment context Unit).run (input,seed) =
      (.ok (),(changed,seed)) := rfl

end Solidity.H62.ReadonlyAudit.EffectRuleWitnesses
