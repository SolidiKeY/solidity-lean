import Solidity.Semantics.ContractWorld
import Solidity.Syntax.Splice

/-!
# Typed world execution regressions

These examples use the explicit world API, not a source-level factory
importer. Constructor and method bodies are the actual typed Solidity
programs. The factory's world operations, library resolution and link
identity remain explicitly supplied model data.
-/

namespace Solidity.Examples.Tactics.ContractWorld

open Solidity.ContractWorld

private instance {α : Type} [DecidableEq α] : DecidableEq (TRes α)
  | .ok a, .ok b => if h : a = b then isTrue (h ▸ rfl)
      else isFalse (fun e => h (Except.ok.inj e))
  | .error a, .error b => if h : a = b then isTrue (h ▸ rfl)
      else isFalse (fun e => h (Except.error.inj e))
  | .ok _, .error _ => isFalse (by intro h; cases h)
  | .error _, .ok _ => isFalse (by intro h; cases h)


def Cell : Contract := contract!{
  bool enabled;
  constructor() payable { enabled = false; }
  function enable() public { enabled = true; }
  function fail() public payable { enabled = false; revert(); }
}

def Failing : Contract := contract!{
  bool touched;
  constructor() payable { touched = true; uint to = 42; to.transfer(1); revert(); }
}

def Factory : Contract := contract!{ constructor() payable { } }

def Empty : Contract := contract!{ }

inductive Kind where
  | cell | failing | factory | library
  deriving DecidableEq

def contracts : Kind → Contract
  | .cell => Cell
  | .failing => Failing
  | .factory => Factory
  | .library => Empty

private def zero : Word := ⟨0, by decide +kernel⟩
private def one : Word := ⟨1, by decide +kernel⟩
private def two : Word := ⟨2, by decide +kernel⟩
private def four : Word := ⟨4, by decide +kernel⟩
private def five : Word := ⟨5, by decide +kernel⟩
private def ten : Word := ⟨10, by decide +kernel⟩

private def alice : Address := ⟨⟨1, by decide +kernel⟩, by decide +kernel⟩
private def factoryAddress : Address := ⟨⟨2, by decide +kernel⟩, by decide +kernel⟩
private def first : Address := ⟨⟨3, by decide +kernel⟩, by decide +kernel⟩
private def second : Address := ⟨⟨4, by decide +kernel⟩, by decide +kernel⟩
private def third : Address := ⟨⟨5, by decide +kernel⟩, by decide +kernel⟩
private def link : Address := ⟨⟨6, by decide +kernel⟩, by decide +kernel⟩
private def recipient : Address := ⟨⟨42, by decide +kernel⟩, by decide +kernel⟩

private def funding (a : Address) : Word :=
  if a = alice then ten else if a = first then four else if a = link then five else zero

private def roles : Kind → Role
  | .library => .libraryCode
  | _ => .contractCode

def initial : World contracts := World.empty contracts funding roles

private def factoryCtor : Prog Factory [] [] := sol[Factory]{ constructor(); }
private def ctor : Prog Cell [] [] := sol[Cell]{ constructor(); }
private def badCtor : Prog Failing [] [] := sol[Failing]{ constructor(); }
private def enable : Entry Cell Unit := Entry.unit (sol[Cell]{ enable(); })
private def fail : Entry Cell Unit := Entry.unit (sol[Cell]{ fail(); }) true

private def flag (w : World contracts) (a : Address) : Option Bool := do
  let st ← w.storage? (⟨a⟩ : Handle Kind.cell)
  let .prim value ← st.find (SRef.ofRoot "enabled" rfl)
  pure value

/-- An explicitly supplied factory transaction creates two paid instances,
then calls one. The first address already holds four units before creation. -/
def factory : TRes (World contracts × Handle Kind.cell) := do
  let (w, _) ← initial.create .factory factoryAddress factoryCtor { sender := alice, mode := .ordinary five }
  let (w, a) ← w.create .cell first ctor { sender := factoryAddress, mode := .ordinary one }
  let (w, _) ← w.create .cell second ctor { sender := factoryAddress, mode := .ordinary two }
  let (w, _) ← w.call a enable { sender := factoryAddress }
  pure (w, a)

/-- The same factory written as one atomic operation descriptor. -/
def factoryOperation : Operation contracts :=
  .seq (.create .factory factoryAddress factoryCtor { sender := alice, mode := .ordinary five })
    (.seq (.create .cell first ctor { sender := factoryAddress, mode := .ordinary one })
      (.seq (.create .cell second ctor { sender := factoryAddress, mode := .ordinary two })
        (.call .cell ⟨first⟩ enable { sender := factoryAddress })))

private def admitted : World contracts → Operation contracts → Prop := fun _ _ => True

def factoryWorld : World contracts := (factoryOperation.run initial).toOption.getD initial

/-- The factory operation has an actual successful result, not an exhausted box. -/
private theorem result_ok {α : Type} (result : TRes α) (fallback : α)
    (success : result.isOk = true) : result = .ok (result.toOption.getD fallback) := by
  cases result with
  | error e => cases success
  | ok value => rfl

theorem factory_run : factoryOperation.run initial = .ok factoryWorld :=
  result_ok _ _ (by decide +kernel)

/-- Both instances are reached from empty code through their real constructors. -/
theorem factory_reachable : Reachable funding roles admitted factoryWorld :=
  .step .initial (.commit trivial factory_run)

/-- The independently reached stores disagree after only the first is called. -/
theorem reached_stores_independent :
    flag factoryWorld first = some true ∧ flag factoryWorld second = some false := by decide +kernel

private structure Snapshot where
  aliceBalance : Int
  factoryBalance : Int
  firstBalance : Int
  secondBalance : Int
  firstFlag : Option Bool
  secondFlag : Option Bool
  deriving DecidableEq

private def factorySnapshot : TRes Snapshot := do
  let (w, _) ← factory
  pure ⟨(w.balance alice).1, (w.balance factoryAddress).1,
    (w.balance first).1, (w.balance second).1, flag w first, flag w second⟩

/-- Funding moves once, prefunding survives, and only the called cell changes. -/
theorem factory_independent_instances :
    factorySnapshot = .ok ⟨5, 2, 5, 2, some true, some false⟩ := by decide +kernel

/-- Reject the false property that the two instance stores alias. -/
theorem factory_not_shared_storage :
    factorySnapshot ≠ .ok ⟨5, 2, 5, 2, some true, some true⟩ := by decide +kernel

private def failedCreation : TRes (Int × Int × Int × Bool × Bool) := do
  let (w, _) ← factory
  let (next, caught) ← w.tryCreate (.ok ()) .failing (fun _ => third)
    (fun _ => badCtor) (fun _ => { sender := factoryAddress, mode := .ordinary one })
    (fun next _ => .ok (next, false)) (fun original _ => .ok (original, true))
  pure ((next.balance factoryAddress).1, (next.balance third).1, (next.balance recipient).1,
    (next.accounts third).isNone, caught)

/-- A constructor writes and reverts after receiving value: no code, payment
or partial storage survives, and the creation handler sees the old world. -/
theorem failed_constructor_payment_rollback : failedCreation = .ok (2, 0, 0, true, true) := by decide +kernel

private def rolledBackCall : TRes (Int × Int × Option Bool × Bool) := do
  let (w, a) ← factory
  let (next, result) := atomic w (w.call a fail { sender := factoryAddress, mode := .ordinary one })
  pure ((next.balance factoryAddress).1, (next.balance first).1, flag next first,
    match result with | .error .revert => true | _ => false)

/-- A failing paid method restores the prior flag and both account balances. -/
theorem call_payment_rollback : rolledBackCall = .ok (2, 5, some true, true) := by decide +kernel

private def unfunded : TRes Bool := do
  let (w, _) ← factory
  pure (match w.create .cell third ctor { sender := factoryAddress, mode := .ordinary five } with
    | .error .revert => true | _ => false)

/-- Creation cannot spend more than the creator's actual global funds. -/
theorem unfunded_creation : unfunded = .ok true := by decide +kernel

private def collision : TRes Bool := do
  let (w, _) ← factory
  pure (match w.create .cell first ctor { sender := factoryAddress } with
    | .error .revert => true | _ => false)

/-- A successful instance's identity cannot be reused by another creation. -/
theorem creation_collision : collision = .ok true := by decide +kernel

private def decodingFailure : Entry Cell Unit := ⟨[], .nil, fun _ => .error .revert, false⟩

private def successFailure : TRes Bool := do
  let (w, _) ← factory
  pure (match w.tryCreate (.ok ()) .cell (fun _ => third) (fun _ => ctor)
      (fun _ => { sender := factoryAddress, mode := .ordinary one })
      (fun next reference => next.call reference decodingFailure { sender := factoryAddress })
      (fun original _ => .ok (original, ())) with
    | .error .revert => true | _ => false)

/-- A caller decoder failure after creation escapes the constructor catch. -/
theorem success_failure_not_caught : successFailure = .ok true := by decide +kernel

private def wrongCode : TRes Bool := do
  let (w, _) ← factory
  pure (match w.call (⟨factoryAddress⟩ : Handle Kind.cell) enable { sender := alice } with
    | .error .revert => true | _ => false)

/-- A typed cast of an address cannot substitute another contract's storage. -/
theorem call_checks_code_identity : wrongCode = .ok true := by decide +kernel

private def libraryMutation : Library contracts Kind.cell Unit :=
  ⟨.library, link, Entry.unit (sol[Cell]{ enabled = true; })⟩

private def linkedMutation : TRes (Option Bool × Option Bool × Int × Bool) := do
  let (w, _) ← factory
  let (w, _) ← w.deployLibrary .library link { sender := alice }
  let (w, _) ← w.libraryCall (⟨second⟩ : Handle Kind.cell) libraryMutation
    { sender := alice, mode := .ordinary one }
  pure (flag w second, flag w first, (w.balance second).1, (w.accounts link).isSome)

/-- A resolved linked body mutates caller storage and charges no new payment. -/
theorem linked_library_mutation : linkedMutation = .ok (some true, some true, 2, true) := by decide +kernel

private def missingLink : TRes Bool := do
  let (w, _) ← factory
  pure (match w.libraryCall (⟨second⟩ : Handle Kind.cell) libraryMutation { sender := alice } with
    | .error .revert => true | _ => false)

/-- An uninstalled library identity cannot execute a supplied body. -/
theorem library_requires_link : missingLink = .ok true := by decide +kernel

private def staticMutation : TRes Bool := do
  let (w, _) ← factory
  let (w, _) ← w.deployLibrary .library link { sender := alice }
  pure (match w.libraryCall (⟨second⟩ : Handle Kind.cell) libraryMutation
      { sender := alice, mode := .readOnly } with
    | .error .revert => true | _ => false)

/-- Static mode refuses the linked storage-writing body. -/
theorem static_library_rejects_mutation : staticMutation = .ok true := by decide +kernel

private def contextObservation : Entry Cell (Int × Int × Int) :=
  ⟨[], .nil, fun σ => .ok (σ.tx.msgSender.1, σ.tx.selfAddress.1, σ.tx.msgValue.1), false⟩

private def libraryContext (mode : Mode) : TRes (Int × Int × Int × Int) := do
  let (w, _) ← factory
  let (w, _) ← w.deployLibrary .library link { sender := alice }
  let (w, observed) ← w.libraryCall (⟨second⟩ : Handle Kind.cell)
    ⟨.library, link, contextObservation⟩ { sender := alice, mode := mode }
  pure (observed.1, observed.2.1, observed.2.2, (w.balance second).1)

/-- A linked body sees the original sender/value and the caller's address. -/
theorem library_preserves_context : libraryContext (.ordinary one) = .ok (1, 4, 1, 2) := by decide +kernel

/-- A static observation inherits zero value and preserves the caller's funds. -/
theorem static_library_observation : libraryContext .readOnly = .ok (1, 4, 0, 2) := by decide +kernel

private def directLibraryCall : TRes Bool := do
  let (w, _) ← factory
  let (w, reference) ← w.deployLibrary .library link { sender := alice }
  pure (match w.call reference (Entry.unit (.nil : Prog Empty [] [])) { sender := alice } with
    | .error .revert => true | _ => false)

/-- Library code cannot bypass its delegate-only entry policy by ordinary call. -/
theorem library_direct_call_rejected : directLibraryCall = .ok true := by decide +kernel

private def newLibrary : TRes Bool := do
  let (w, _) ← factory
  pure (match w.create .library link (.nil : Prog Empty [] []) { sender := alice } with
    | .error .revert => true | _ => false)

/-- Ordinary source creation cannot instantiate a library declaration. -/
theorem library_new_rejected : newLibrary = .ok true := by decide +kernel

#print axioms factory_independent_instances
#print axioms failed_constructor_payment_rollback
#print axioms linked_library_mutation

end Solidity.Examples.Tactics.ContractWorld
