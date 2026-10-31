import Solidity.Backend.Executable.WorldPrefixChecks
import Solidity.Semantics.ContractWorldCertificates

/-! Existing tryCreate frame consumers after actual paid prefixes. Exact
constructor failure/catch bytes are distinct from arguments and continuation
failures. No source-new lowering, byte CREATE or address algorithm is supplied. -/
namespace Solidity.Backend.Executable.CreationAttempt
open ContractWorld
section Relations
variable {K : Type} {contracts : K → Contract}

/-- A caught constructor failure retains the actually completed prefix world,
not the earlier outer checkpoint, and reports precisely the constructor bytes. -/
theorem prefix_caught {α β : Type} (before paid : World contracts)
    (sequence : TRes (World contracts × α)) (a : α)
    (ran : sequence = .ok (paid,a)) (k : K) (target : Address)
    (ctor : Prog (contracts k) [] []) (ctx : Context) (bytes : List UInt8)
    (mutable : ctx.isStatic = false)
    (failed : paid.create k target ctor ctx = .error (.revertWith bytes))
    (success : World contracts → Handle k → TRes (World contracts × β))
    (observe : List UInt8 → β) :
    atomic before (sequence >>= fun pair => pair.1.tryCreate (.ok ()) k
      (fun _ => target) (fun _ => ctor) (fun _ => ctx) success
      (fun world halt => .ok (world, observe (THalt.data halt)))) =
      (paid, .ok (observe bytes)) := by
  rw [ran]
  simp only [bind, Except.bind, World.tryCreate, mutable, Bool.false_eq_true,
    ↓reduceIte, failed, catchable, THalt.data, atomic]

/-- Failed argument evaluation stays outside catch even after a genuine prefix;
the uncaught failure restores the outer checkpoint, not the paid world. This
is result algebra, not a completed divergence/exhaustion transaction. -/
theorem prefix_argument_failure {α β γ : Type} (before paid : World contracts)
    (sequence : TRes (World contracts × α)) (a : α) (ran : sequence = .ok (paid,a))
    (e : THalt) (k : K) (target : β → Address)
    (ctor : β → Prog (contracts k) [] []) (ctx : β → Context)
    (success : World contracts → Handle k → TRes (World contracts × γ))
    (caught : World contracts → THalt → TRes (World contracts × γ)) :
    atomic before (sequence >>= fun pair => pair.1.tryCreate (.error e) k target ctor ctx success caught) =
      (before, .error e) := by
  rw [ran]
  rfl

end Relations
namespace Controls
open PaymentCheckpointChecks (contracts sender fresh other)
open WorldPrefixChecks (initial created paidOne first_payment)

def failing : Prog (contracts ()) [] [] := .cons (.revertData [.bytes [0xca,0xfe]]) .nil
def context : Context := {sender}
private def errorCode {α : Type} : TRes α → Option THalt
  | .ok _ => none | .error e => some e
private theorem recover_failure {α : Type} (r : TRes α) (e : THalt)
    (observed : errorCode r = some e) : r = .error e := by
  cases r with
  | ok x => cases observed
  | error actual => cases Option.some.inj observed; rfl

theorem constructor_failure : paidOne.create () other failing context = .error (.revertWith [0xca,0xfe]) :=
  recover_failure _ _ (by decide +kernel)

def payPrefix : TRes (World contracts × Unit) := (WorldPrefixChecks.pay.run created).map (fun w => (w,()))
theorem prefix_run : payPrefix = .ok (paidOne,()) := by rw [payPrefix, first_payment]; rfl

/-- The prefix is a real one-unit call, with a previously installed account. -/
theorem caught_after_paid_prefix :
    atomic created (payPrefix >>= fun pair => pair.1.tryCreate (.ok ()) ()
      (fun _ => other) (fun _ => failing) (fun _ => context)
      (fun world _ => .ok (world, ([] : List UInt8)))
      (fun world halt => .ok (world, THalt.data halt))) =
      (paidOne, .ok [0xca,0xfe]) := by
  exact prefix_caught created paidOne payPrefix () prefix_run () other failing context
    [0xca,0xfe] rfl constructor_failure _ id

/-- The published operation certificate describes the same real caught frame. -/
theorem caught_operation :
    (.tryCreate (.ok ()) () (fun _ => other) (fun _ => failing) (fun _ => context) : Operation contracts).run paidOne = .ok paidOne :=
  Operation.tryCreate_caught paidOne () () _ _ _ (.revertWith [0xca,0xfe]) rfl constructor_failure rfl

example : (paidOne.accounts other).isNone = true ∧ (paidOne.accounts fresh).isSome = true ∧
    ((paidOne.funds sender).val, (paidOne.funds fresh).val) = (2,1) := by decide +kernel

/-- Even catchable argument bytes never reach the constructor catch handler. -/
example : paidOne.tryCreate (.error (.revertWith [0xab]) : TRes Unit) ()
    (fun _ => other) (fun _ => failing) (fun _ => context)
    (fun world _ => .ok (world, ([] : List UInt8)))
    (fun world _ => .ok (world, [0xca,0xfe])) = .error (.revertWith [0xab]) := rfl

private def valueOr {α : Type} (r : TRes α) (fallback : α) : α :=
  match r with | .ok value => value | .error _ => fallback
private theorem recover_success {α : Type} (r : TRes α) (fallback : α)
    (present : r.toOption.isSome = true) : r = .ok (valueOr r fallback) := by
  cases r with | ok value => rfl | error e => cases present

def successful : World contracts × Handle () :=
  valueOr (paidOne.create () other .nil context) (paidOne, ⟨other⟩)
theorem constructor_success : paidOne.create () other .nil context = .ok successful :=
  recover_success _ _ (by decide +kernel)

/-- A successful creation followed by a failing success continuation propagates
that new failure; constructor catch cannot replace its bytes. -/
theorem continuation_failure : paidOne.tryCreate (.ok ()) () (fun _ => other) (fun _ => .nil) (fun _ => context)
    (fun _ _ => (.error (.revertWith [0x77]) : TRes (World contracts × Unit)))
    (fun world _ => .ok (world, ())) = .error (.revertWith [0x77]) := by
  simp only [World.tryCreate, bind, Except.bind,
    show context.isStatic = false from rfl, Bool.false_eq_true, ↓reduceIte, constructor_success]

/-- Argument failure after the actual payment restores the outer checkpoint. -/
example : atomic created (payPrefix >>= fun pair => pair.1.tryCreate
    (.error (.revertWith [0xab]) : TRes Unit) () (fun _ => other)
    (fun _ => failing) (fun _ => context)
    (fun world _ => .ok (world, ())) (fun world _ => .ok (world, ()))) =
    (created, .error (.revertWith [0xab])) :=
  prefix_argument_failure created paidOne payPrefix () prefix_run (.revertWith [0xab]) () _ _ _ _ _

/-- The published world-result erasure certificate agrees with the actual caught operation. -/
theorem operation_consistency :
    forgetResult (paidOne.tryCreate (.ok ()) () (fun _ => other) (fun _ => failing) (fun _ => context)
      (fun world _ => .ok (world, ([] : List UInt8)))
      (fun world _ => .ok (world, [0xca,0xfe]))) = .ok paidOne := by
  rw [Operation.tryCreate_certificate paidOne (.ok ()) () (fun _ => other)
    (fun _ => failing) (fun _ => context) ([] : List UInt8) [0xca,0xfe]]
  exact caught_operation

/-- A successful independent constructor really installs an account. -/
example : ∃ st : Storage (contracts ()), successful.1.accounts successful.2.address = some ⟨(),st⟩ := by
  cases eq : successful with
  | mk world reference =>
    have ran := constructor_success
    rw [eq] at ran
    exact World.create_installs (w := paidOne) (next := world) (k := ()) (self := other)
      (ctor := .nil) (ctx := context) (reference := reference) ran
example : successful.2.address = other := by decide +kernel

example : THalt.data (.revertWith [0xca,0xfe]) ≠ THalt.data (.revertWith [0xab]) := by decide +kernel
end Controls
/-- info: 'Solidity.Backend.Executable.CreationAttempt.prefix_caught' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms prefix_caught
/-- info: 'Solidity.Backend.Executable.CreationAttempt.prefix_argument_failure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms prefix_argument_failure
/-- info: 'Solidity.Backend.Executable.CreationAttempt.Controls.caught_after_paid_prefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Controls.caught_after_paid_prefix
/-- info: 'Solidity.Backend.Executable.CreationAttempt.Controls.caught_operation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Controls.caught_operation
/-- info: 'Solidity.Backend.Executable.CreationAttempt.Controls.continuation_failure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Controls.continuation_failure
/-- info: 'Solidity.Backend.Executable.CreationAttempt.Controls.operation_consistency' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Controls.operation_consistency
end Solidity.Backend.Executable.CreationAttempt
