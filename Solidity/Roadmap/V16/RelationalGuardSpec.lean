import Solidity.Backend.FailurePaths.RelationalGuardControls
import Solidity.Source.Hoare

/-! Scoped specifications of actual relational require statements and selected
machine code. The populated published scalar fixture supplies the representation
and both runs. Full Source admission/lowering, fetched EVM, gas and failure-state
rollback are not established. A target revert records no payload or final state;
only this actual Source bare-revert certificate supplies the empty payload. -/
namespace Solidity.Roadmap.V16.RelationalGuardSpec
open Solidity.Backend Evm Evm.Memory
open PrimitivePackets.Comparisons
namespace Fixture
abbrev E := PrimitivePackets.Comparisons.Controls.E
abbrev C := PrimitivePackets.Comparisons.Controls.C
abbrev start := (Source.L0 E,PrimitivePackets.Comparisons.Controls.sourceState)
abbrev context (signed : Bool) : Source.RCtx := [.int (ty signed),.int (ty signed)]
end Fixture
open Fixture

def operation (o : Order) (signed : Bool) (p : Roadmap.Pipeline) (x y : Int)
    (hx : (ty signed).lo≤x ∧ x≤(ty signed).hi)
    (hy : (ty signed).lo≤y ∧ y≤(ty signed).hi) :
    Source.EM E [] (Source.Out E.layout (context signed) (context signed)) :=
  Source.execS (PrimitivePackets.Comparisons.Controls.global p)
    PrimitivePackets.Comparisons.Controls.frame 7 0 none
    (FailurePaths.RelationalGuard.statement o signed .here (.there .here))
    (PrimitivePackets.Comparisons.Controls.source signed x y hx hy).1

def PostTransport (o : Order) (signed : Bool) (p : Roadmap.Pipeline) (x y : Int)
    (hx : (ty signed).lo≤x ∧ x≤(ty signed).hi)
    (hy : (ty signed).lo≤y ∧ y≤(ty signed).hi)
    (Q : Source.Out E.layout (context signed) (context signed) → Source.EMState E [] → Prop)
    (X : Source.Halt → Source.EMState E [] → Prop) : Prop :=
  let locals := (PrimitivePackets.Comparisons.Controls.source signed x y hx hy).1
  let machine := PrimitivePackets.Comparisons.Controls.machine signed x y hx hy
  let fragment := PrimitivePackets.Comparisons.Controls.fragment signed
  let selected := FailurePaths.RelationalGuard.selected (C:=C) 0 fragment o signed .here (.there .here)
  StateRepr 1 0 4 fragment (PrimitivePackets.Comparisons.Controls.target signed x y hx hy)
    PrimitivePackets.Comparisons.Controls.addresses machine ∧
  compileStmt 0 fragment (FailurePaths.RelationalGuard.target (C:=C) o signed .here (.there .here)) = some selected ∧
  (operation o signed p x y hx hy).run start =
    (if result o x y then (.ok (.normal locals),start) else (.error (.revert []),start)) ∧
  (Source.Hoare (fun input => input=start) (operation o signed p x y hx hy) Q X ↔
    match Solidity.Evm.run selected.code machine with
    | .ok after pc => after=machine ∧ pc=0 ∧ Q (.normal locals) start
    | .revert => X (.revert []) start
    | .fault => False)


/-- Actual source, compiler selection and representation construct the specification correspondence; neither run nor desired postcondition is assumed. -/
theorem transport :
    ∀ (o : Solidity.Backend.PrimitivePackets.Comparisons.Order) (signed : Bool) (p : Solidity.Roadmap.Pipeline) (x y : Int)
 (hx : (Solidity.Backend.PrimitivePackets.Comparisons.ty signed).lo≤x ∧ x≤(Solidity.Backend.PrimitivePackets.Comparisons.ty signed).hi)
 (hy : (Solidity.Backend.PrimitivePackets.Comparisons.ty signed).lo≤y ∧ y≤(Solidity.Backend.PrimitivePackets.Comparisons.ty signed).hi)
 (Q : Solidity.Source.Out Solidity.Roadmap.V16.RelationalGuardSpec.Fixture.E.layout (Solidity.Roadmap.V16.RelationalGuardSpec.Fixture.context signed) (Solidity.Roadmap.V16.RelationalGuardSpec.Fixture.context signed) → Solidity.Source.EMState Solidity.Roadmap.V16.RelationalGuardSpec.Fixture.E [] → Prop)
 (X : Solidity.Source.Halt → Solidity.Source.EMState Solidity.Roadmap.V16.RelationalGuardSpec.Fixture.E [] → Prop),
 Solidity.Roadmap.V16.RelationalGuardSpec.PostTransport o signed p x y hx hy Q X := by
  intro o signed p x y hx hy Q X
  have checked := Solidity.Backend.FailurePaths.RelationalGuard.Controls.checked o signed p x y hx hy
  dsimp only [Solidity.Roadmap.V16.RelationalGuardSpec.PostTransport]
  refine ⟨checked.1,checked.2.2.1,checked.2.1,?_⟩
  have execution : (Solidity.Roadmap.V16.RelationalGuardSpec.operation o signed p x y hx hy).run Solidity.Roadmap.V16.RelationalGuardSpec.Fixture.start =
      (if Solidity.Backend.PrimitivePackets.Comparisons.result o x y then (.ok (.normal (Solidity.Backend.PrimitivePackets.Comparisons.Controls.source signed x y hx hy).1),Solidity.Roadmap.V16.RelationalGuardSpec.Fixture.start) else (.error (.revert []),Solidity.Roadmap.V16.RelationalGuardSpec.Fixture.start)) := checked.2.1
  rw [checked.2.2.2]
  constructor
  · intro spec
    have holds := spec Solidity.Roadmap.V16.RelationalGuardSpec.Fixture.start rfl
    rw [execution] at holds
    cases decision : Solidity.Backend.PrimitivePackets.Comparisons.result o x y with
    | false => simp only [decision,Bool.false_eq_true,if_false] at holds ⊢; exact holds
    | true => simp only [decision,if_true] at holds ⊢; exact ⟨True.intro,True.intro,holds⟩
  · intro holds input same
    subst input
    rw [execution]
    cases decision : Solidity.Backend.PrimitivePackets.Comparisons.result o x y with
    | false => simp only [decision,Bool.false_eq_true,if_false] at holds ⊢; exact holds
    | true => simp only [decision,if_true] at holds ⊢; exact holds.2.2

/-- Only exact normal completion in the unchanged complete source state. -/
def NormalOnly (o : Order) (signed : Bool) (p : Roadmap.Pipeline) (x y : Int)
    (hx : (ty signed).lo≤x ∧ x≤(ty signed).hi)
    (hy : (ty signed).lo≤y ∧ y≤(ty signed).hi) : Prop :=
  Source.Hoare (fun input => input=start) (operation o signed p x y hx hy)
    (fun value after => value=.normal (PrimitivePackets.Comparisons.Controls.source signed x y hx hy).1 ∧ after=start)
    (fun _ _ => False)

/-- Only exact bare revert in the unchanged complete source state. -/
def RevertOnly (o : Order) (signed : Bool) (p : Roadmap.Pipeline) (x y : Int)
    (hx : (ty signed).lo≤x ∧ x≤(ty signed).hi)
    (hy : (ty signed).lo≤y ∧ y≤(ty signed).hi) : Prop :=
  Source.Hoare (fun input => input=start) (operation o signed p x y hx hy)
    (fun _ _ => False) (fun halt after => halt=.revert [] ∧ after=start)


/-- Signed -1 < 0: exact normal completion and unchanged full source state. -/
theorem success :
    ∀ p : Solidity.Roadmap.Pipeline, Solidity.Roadmap.V16.RelationalGuardSpec.NormalOnly .lt true p (-1) 0 (by decide) (by decide) := by
  intro p
  unfold Solidity.Roadmap.V16.RelationalGuardSpec.NormalOnly
  apply (Solidity.Roadmap.V16.RelationalGuardSpec.transport .lt true p (-1) 0 (by decide) (by decide) _ _).2.2.2.mpr
  rw [Solidity.Backend.FailurePaths.RelationalGuard.Controls.negative_lt_zero_succeeds p]
  exact ⟨rfl,rfl,rfl,rfl⟩

/-- Unsigned 7 < 7: exact bare revert and unchanged full source state. -/
theorem failure :
    ∀ p : Solidity.Roadmap.Pipeline, Solidity.Roadmap.V16.RelationalGuardSpec.RevertOnly .lt false p 7 7 (by decide) (by decide) := by
  intro p
  unfold Solidity.Roadmap.V16.RelationalGuardSpec.RevertOnly
  apply (Solidity.Roadmap.V16.RelationalGuardSpec.transport .lt false p 7 7 (by decide) (by decide) _ _).2.2.2.mpr
  rw [Solidity.Backend.FailurePaths.RelationalGuard.Controls.equal_lt_reverts p]
  exact ⟨rfl,rfl⟩

/-- An actual failing guard cannot satisfy the normal-only source specification. -/
theorem wrong_success :
    ∀ p : Solidity.Roadmap.Pipeline, ¬ Solidity.Roadmap.V16.RelationalGuardSpec.NormalOnly .lt false p 7 7 (by decide) (by decide) := by
  intro p spec
  have observed := (Solidity.Roadmap.V16.RelationalGuardSpec.transport .lt false p 7 7 (by decide) (by decide) _ _).2.2.2.mp spec
  rw [Solidity.Backend.FailurePaths.RelationalGuard.Controls.equal_lt_reverts p] at observed
  exact observed

/-- An actual successful guard cannot satisfy the revert-only source specification. -/
theorem wrong_failure :
    ∀ p : Solidity.Roadmap.Pipeline, ¬ Solidity.Roadmap.V16.RelationalGuardSpec.RevertOnly .lt true p (-1) 0 (by decide) (by decide) := by
  intro p spec
  have observed := (Solidity.Roadmap.V16.RelationalGuardSpec.transport .lt true p (-1) 0 (by decide) (by decide) _ _).2.2.2.mp spec
  rw [Solidity.Backend.FailurePaths.RelationalGuard.Controls.negative_lt_zero_succeeds p] at observed
  exact observed.2.2

/-- The new transport rejects a different source revert payload, despite target revert lacking data. -/
theorem wrong_payload :
    ∀ p : Solidity.Roadmap.Pipeline, ¬ Solidity.Source.Hoare (fun input => input=Solidity.Roadmap.V16.RelationalGuardSpec.Fixture.start)
 (Solidity.Roadmap.V16.RelationalGuardSpec.operation .lt false p 7 7 (by decide) (by decide))
 (fun _ _ => False) (fun halt after => halt=.revert [1] ∧ after=Solidity.Roadmap.V16.RelationalGuardSpec.Fixture.start) := by
  intro p spec
  have observed := (Solidity.Roadmap.V16.RelationalGuardSpec.transport .lt false p 7 7 (by decide) (by decide) _ _).2.2.2.mp spec
  rw [Solidity.Backend.FailurePaths.RelationalGuard.Controls.equal_lt_reverts p] at observed
  cases Solidity.Source.Halt.revert.inj observed.1

/-- Zero source fuel is timeout, not a completed bare revert; no divergence or failure admission is inferred. -/
theorem timeout_not_revert :
    ∀ p : Solidity.Roadmap.Pipeline,
 (Solidity.Source.execS (Solidity.Backend.PrimitivePackets.Comparisons.Controls.global p) Solidity.Backend.PrimitivePackets.Comparisons.Controls.frame 0 0 none
 (Solidity.Backend.FailurePaths.RelationalGuard.statement .lt false .here (.there .here))
 (Solidity.Backend.PrimitivePackets.Comparisons.Controls.source false 7 7 (by decide) (by decide)).1).run Solidity.Roadmap.V16.RelationalGuardSpec.Fixture.start ≠
 (.error (.revert []),Solidity.Roadmap.V16.RelationalGuardSpec.Fixture.start) := by
  intro p
  rw [Solidity.Backend.FailurePaths.RelationalGuard.Controls.zero_horizon p]
  intro impossible
  cases impossible

end Solidity.Roadmap.V16.RelationalGuardSpec

/-- info: 'Solidity.Roadmap.V16.RelationalGuardSpec.transport' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Roadmap.V16.RelationalGuardSpec.transport

/-- info: 'Solidity.Roadmap.V16.RelationalGuardSpec.success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Roadmap.V16.RelationalGuardSpec.success

/-- info: 'Solidity.Roadmap.V16.RelationalGuardSpec.failure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Roadmap.V16.RelationalGuardSpec.failure

/-- info: 'Solidity.Roadmap.V16.RelationalGuardSpec.wrong_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Roadmap.V16.RelationalGuardSpec.wrong_success

/-- info: 'Solidity.Roadmap.V16.RelationalGuardSpec.wrong_failure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Roadmap.V16.RelationalGuardSpec.wrong_failure

/-- info: 'Solidity.Roadmap.V16.RelationalGuardSpec.wrong_payload' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Roadmap.V16.RelationalGuardSpec.wrong_payload

/-- info: 'Solidity.Roadmap.V16.RelationalGuardSpec.timeout_not_revert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Roadmap.V16.RelationalGuardSpec.timeout_not_revert
