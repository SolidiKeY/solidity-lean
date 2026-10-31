import Solidity.Semantics.PaymentWorld

/-!
# Payment and creation checkpoint consumers

The first three laws are algebra over existing world-valued results; the
later laws consume actual existing world runs. They expose caught/uncaught
failure, retain successful creation before a caught send, and distinguish fresh
handles. They introduce no payment semantics and no compiled-payment relation.
The world API is unmetered and caller-selected addresses are not CREATE nonce
or pinned-EVM evidence. G43 and G44 parent obligations remain open.
-/
namespace Solidity.Backend.Executable
open ContractWorld
variable {K : Type} [DecidableEq K] {contracts : K → Contract}

omit [DecidableEq K] in
/-- False is precisely a caught completed failure, with the pre-receive world. -/
theorem send_false_iff (before next : World contracts)
    (run : TRes (World contracts × Unit)) :
    sendResult before run = .ok (next, false) ↔
      next = before ∧ ∃ e, run = .error e ∧ catchable e = true := by
  cases run with
  | ok pair =>
    rcases pair with ⟨final, ⟨⟩⟩
    constructor
    · intro bad
      have impossible : true = false := congrArg Prod.snd (Except.ok.inj bad)
      cases impossible
    · rintro ⟨_, e, bad, _⟩
      cases bad
  | error e =>
    cases completed : catchable e with
    | false =>
      simp only [sendResult, completed, Bool.false_eq_true, ↓reduceIte]
      constructor
      · intro bad; cases bad
      · rintro ⟨_, e, bad, caught⟩
        cases bad
        cases completed.symm.trans caught
    | true =>
      simp only [sendResult, completed, ↓reduceIte]
      constructor
      · intro equal
        exact ⟨(congrArg Prod.fst (Except.ok.inj equal)).symm, e, rfl, completed⟩
      · rintro ⟨rfl, _⟩
        rfl

omit [DecidableEq K] in
/-- An uncaught send halt is exactly the original noncatchable halt. -/
theorem send_error_iff (before : World contracts)
    (run : TRes (World contracts × Unit)) (e : THalt) :
    sendResult before run = .error e ↔ run = .error e ∧ catchable e = false := by
  cases run with
  | ok pair =>
    constructor
    · intro bad; cases bad
    · rintro ⟨bad, _⟩; cases bad
  | error original =>
    cases completed : catchable original with
    | false =>
      simp only [sendResult, completed, Bool.false_eq_true, ↓reduceIte]
      constructor
      · intro equal; cases equal; exact ⟨rfl, completed⟩
      · rintro ⟨equal, _⟩
        exact congrArg (fun halt : THalt => (Except.error halt : TRes (World contracts × Bool)))
          (Except.error.inj equal)
    | true =>
      simp only [sendResult, completed, ↓reduceIte]
      constructor
      · intro bad; cases bad
      · rintro ⟨equal, uncaught⟩
        cases equal
        cases completed.symm.trans uncaught

omit [DecidableEq K] in
/-- An uncaught tail failure rolls back even a successful effectful prefix. -/
theorem prefix_atomic_failure {α β : Type} (before middle : World contracts)
    (firstRun : TRes (World contracts × α)) (value : α)
    (tail : World contracts → α → TRes (World contracts × β)) (e : THalt)
    (ran : firstRun = .ok (middle, value)) (failed : tail middle value = .error e) :
    atomic before (firstRun >>= fun pair => tail pair.1 pair.2) = (before, .error e) := by
  rw [ran]
  exact payment_atomic_failure before _ e failed

/-- Creation failure precedes the send; no recipient frame can catch it. -/
theorem create_send_creation_failure (before : World contracts) (k : K)
    (fresh sender : Address) (ctor : Prog (contracts k) [] [])
    (receive : Entry (contracts k) Unit) (e : THalt)
    (failed : before.create k fresh ctor {sender := sender} = .error e) :
    before.createSend k fresh ctor receive sender = .error e := by
  simp only [World.createSend, failed, bind, Except.bind]

/-- A caught send after successful creation retains that exact created world
and actual installed storage; it does not roll back to the factory input. -/
theorem create_send_caught_prefix (before created : World contracts) (k : K)
    (fresh sender : Address) (ctor : Prog (contracts k) [] [])
    (receive : Entry (contracts k) Unit) (reference : Handle k) (e : THalt)
    (made : before.create k fresh ctor {sender := sender} = .ok (created, reference))
    (admitted : (created.isLibrary k || (created.storage? reference).isNone) = false)
    (failed : created.receiveRun reference receive sender (PrimTy.dflt .uint) = .error e)
    (completed : catchable e = true) :
    atomic before (before.createSend k fresh ctor receive sender) = (created, .ok false) ∧
      ∃ st : Storage (contracts k), created.accounts reference.address = some ⟨k, st⟩ := by
  refine ⟨?_, World.create_installs made⟩
  simp only [World.createSend, made, bind, Except.bind, World.stipend,
    admitted, Bool.false_eq_true, ↓reduceIte, failed, sendResult, completed, atomic]

/-- Successful creations at distinct checked addresses return distinct handles.
This consumes actual runs; it does not assume address-function injectivity. -/
theorem creation_handles_distinct {before middle after : World contracts} {k : K}
    {a b sender : Address} {firstCtor secondCtor : Prog (contracts k) [] []}
    {first second : Handle k}
    (firstRun : before.create k a firstCtor {sender := sender} = .ok (middle, first))
    (secondRun : middle.create k b secondCtor {sender := sender} = .ok (after, second))
    (distinct : a ≠ b) : first ≠ second := by
  obtain ⟨_, _, _, _, _, firstAddress⟩ := World.create_ok firstRun
  obtain ⟨_, _, _, _, _, secondAddress⟩ := World.create_ok secondRun
  intro equal
  exact distinct (firstAddress.symm.trans ((congrArg Handle.address equal).trans secondAddress))

/-- info: 'Solidity.Backend.Executable.send_false_iff' depends on axioms: [propext] -/
#guard_msgs in
#print axioms send_false_iff
/-- info: 'Solidity.Backend.Executable.send_error_iff' depends on axioms: [propext] -/
#guard_msgs in
#print axioms send_error_iff
/-- info: 'Solidity.Backend.Executable.prefix_atomic_failure' depends on axioms: [propext] -/
#guard_msgs in
#print axioms prefix_atomic_failure
/-- info: 'Solidity.Backend.Executable.create_send_creation_failure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms create_send_creation_failure
/-- info: 'Solidity.Backend.Executable.create_send_caught_prefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms create_send_caught_prefix
/-- info: 'Solidity.Backend.Executable.creation_handles_distinct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms creation_handles_distinct
end Solidity.Backend.Executable
