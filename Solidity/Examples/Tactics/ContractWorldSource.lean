import Solidity.Frontend.WorldImport

/-!
# Source factories and linked storage mutation, in the typed world

The compiler fixture is real Solidity. Each command accepts a complete
recognized source body and emits the existing typed constructor/method
programs inside world frames. Unsupported composition is checked separately.
-/

namespace Solidity.Examples.Tactics.ContractWorldSource

open Solidity.ContractWorld
open Solidity.Frontend

private instance {α : Type} [DecidableEq α] : DecidableEq (TRes α)
  | .ok a, .ok b => if h : a = b then isTrue (h ▸ rfl)
      else isFalse (fun e => h (Except.ok.inj e))
  | .error a, .error b => if h : a = b then isTrue (h ▸ rfl)
      else isFalse (fun e => h (Except.error.inj e))
  | .ok _, .error _ => isFalse (by intro h; cases h)
  | .error _, .ok _ => isFalse (by intro h; cases h)

/-- Four balances and two independent Boolean observations. A flat record
keeps equality synthesis bounded independently of nested product depth. -/
private structure Snapshot where
  senderBalance : Int
  factoryBalance : Int
  childBalance : Int
  recipientBalance : Int
  checksPassed : Bool
  outcome : Bool
  deriving DecidableEq

solc_world_factory "../../../tests/solc/ContractWorld.ast.json" hash 0x7e8caacffff380a9
  contract "WorldFactory" function "make" as Direct
solc_world_factory "../../../tests/solc/ContractWorld.ast.json" hash 0x7e8caacffff380a9
  contract "WorldFactory" function "tryMake" as Tried
solc_world_factory "../../../tests/solc/ContractWorld.ast.json" hash 0x7e8caacffff380a9
  contract "WorldFactory" function "trySuccess" as Succeeded
solc_world_factory "../../../tests/solc/ContractWorld.ast.json" hash 0x7e8caacffff380a9
  contract "WorldFactory" function "failMake" as Failed
solc_world_factory "../../../tests/solc/ContractWorld.ast.json" hash 0x7e8caacffff380a9
  contract "WorldFactory" function "implicitMake" as Implicit
solc_world_library "../../../tests/solc/ContractWorld.ast.json" hash 0x7e8caacffff380a9
  contract "WorldLibraryUser" function "mutate" as Linked

private def zero : Word := ⟨0, by decide +kernel⟩
private def two : Word := ⟨2, by decide +kernel⟩
private def three : Word := ⟨3, by decide +kernel⟩
private def five : Word := ⟨5, by decide +kernel⟩
private def four : Word := ⟨4, by decide +kernel⟩
private def ten : Word := ⟨10, by decide +kernel⟩
private def alice : Address := ⟨⟨100, by decide +kernel⟩, by decide +kernel⟩
private def factory : Address := ⟨⟨200, by decide +kernel⟩, by decide +kernel⟩
private def child : Address := ⟨⟨300, by decide +kernel⟩, by decide +kernel⟩
private def libraryAddress : Address := ⟨⟨400, by decide +kernel⟩, by decide +kernel⟩
private def otherCaller : Address := ⟨⟨500, by decide +kernel⟩, by decide +kernel⟩
private def recipient : Address := ⟨⟨42, by decide +kernel⟩, by decide +kernel⟩

private def funds (a : Address) : Word :=
  if a = alice then ten else if a = child then four else if a = libraryAddress then five else zero

/-- The regression harness reports an unsupported environment as model
exhaustion. The source runner itself requires the premise as a proof. -/
private def admittedRun {α : Type} (premise : Bool)
    (run : premise = true → TRes α) : TRes α :=
  if h : premise = true then run h else .error .exhausted

private noncomputable def directSnapshot : TRes (Int × Int × Int × Int × Bool) := do
  let initial := World.empty Direct.contracts funds
  let (w, f) ← Direct.deploy initial factory { sender := alice }
  let admitted := Direct.assumptions w { sender := alice, mode := .ordinary three }
  let (w, product) ← admittedRun (Direct.assumptions w { sender := alice, mode := .ordinary three }) (Direct.run w f { sender := alice, mode := .ordinary three } child)
  let (w, _) ← w.call product (Entry.unit Direct.Source.WorldProduct.checkTen) { sender := alice }
  let (w, _) ← w.call product (Entry.unit Direct.Source.WorldProduct.bump) { sender := alice }
  let (w, _) ← w.call product (Entry.unit Direct.Source.WorldProduct.checkEleven) { sender := alice }
  let rejected := match w.call product (Entry.unit Direct.Source.WorldProduct.falseZero)
      { sender := alice } with
    | .error .panic => true | _ => false
  pure ((w.balance alice).1, (w.balance factory).1,
    (w.balance child).1, (w.balance recipient).1, admitted && rejected)

/-- Source new runs base/field initialization and the paid constructor,
settles its outgoing transfer, returns a callable instance, and rejects the
source's false zero-count assertion after a subsequent successful bump. -/
theorem source_factory : directSnapshot = .ok (7, 2, 4, 1, true) := by decide +kernel

private def successfulTry : TRes Snapshot := do
  let initial := World.empty Succeeded.contracts funds
  let (w, f) ← Succeeded.deploy initial factory { sender := alice }
  let admitted := Succeeded.assumptions w { sender := alice, mode := .ordinary three }
  let (w, result) ← admittedRun (Succeeded.assumptions w { sender := alice, mode := .ordinary three }) (Succeeded.run w f { sender := alice, mode := .ordinary three } child)
  pure ⟨(w.balance alice).1, (w.balance factory).1, (w.balance child).1,
    (w.balance recipient).1, admitted && (w.accounts child).isSome, result⟩

/-- A successful source creation try installs code, commits payments and
executes the source success branch. -/
theorem source_creation_try_success : successfulTry = .ok ⟨7, 2, 4, 1, true, true⟩ := by decide +kernel

private def triedSnapshot : TRes Snapshot := do
  let initial := World.empty Tried.contracts funds
  let (w, f) ← Tried.deploy initial factory { sender := alice }
  let admitted := Tried.assumptions w { sender := alice, mode := .ordinary two }
  let (w, result) ← admittedRun (Tried.assumptions w { sender := alice, mode := .ordinary two }) (Tried.run w f { sender := alice, mode := .ordinary two } child)
  pure ⟨(w.balance alice).1, (w.balance factory).1, (w.balance child).1,
    (w.balance recipient).1, admitted && (w.accounts child).isNone, result⟩

/-- A source bare creation catch retains the caller's incoming payment while
rolling back constructor writes, code installation and its outgoing payment. -/
theorem source_creation_try : triedSnapshot = .ok ⟨8, 2, 4, 0, true, false⟩ := by decide +kernel

private def ordinaryFailure : TRes Snapshot := do
  let initial := World.empty Failed.contracts funds
  let (w, f) ← Failed.deploy initial factory { sender := alice }
  let admitted := Failed.assumptions w { sender := alice, mode := .ordinary two }
  let (next, result) := atomic w (admittedRun (Failed.assumptions w { sender := alice, mode := .ordinary two }) (Failed.run w f { sender := alice, mode := .ordinary two } child))
  pure ⟨(next.balance alice).1, (next.balance factory).1, (next.balance child).1,
    (next.balance recipient).1, (next.accounts child).isNone,
    admitted && (match result with | .error .revert => true | _ => false)⟩

/-- Uncaught source creation failure rolls back the whole caller transaction,
including its original incoming payment and prefunded destination balance. -/
theorem source_uncaught_creation_rollback :
    ordinaryFailure = .ok ⟨10, 0, 4, 0, true, true⟩ := by decide +kernel

private def implicitSnapshot : TRes Bool := do
  let initial := World.empty Implicit.contracts funds
  let (w, f) ← Implicit.deploy initial factory { sender := alice }
  let admitted := Implicit.assumptions w { sender := alice }
  let (w, reference) ← admittedRun (Implicit.assumptions w { sender := alice }) (Implicit.run w f { sender := alice } child)
  pure (admitted && (w.accounts reference.address).isSome)

/-- A simple implicit constructor still installs a typed instance. -/
theorem source_implicit_constructor : implicitSnapshot = .ok true := by decide +kernel

private noncomputable def linkedSnapshot : TRes (Int × Int × Int × Bool) := do
  let initial := World.empty Linked.contracts funds Linked.roles
  let (w, first) ← Linked.deployCaller initial factory { sender := alice }
  let (w, second) ← Linked.deployCaller w otherCaller { sender := alice }
  let (w, _) ← Linked.deployLibrary w libraryAddress { sender := alice }
  let (w, _) ← Linked.run w first { sender := alice, mode := .ordinary two } libraryAddress
  let (w, _) ← w.call first (Entry.unit Linked.Source.WorldLibraryUser.checkNine) { sender := alice }
  let (w, _) ← w.call second (Entry.unit Linked.Source.WorldLibraryUser.checkZero) { sender := alice }
  let rejected := match w.call first (Entry.unit Linked.Source.WorldLibraryUser.checkZero)
      { sender := alice } with
    | .error .panic => true | _ => false
  pure ((w.balance alice).1, (w.balance factory).1, (w.balance libraryAddress).1, rejected)

/-- Real source linked mutation uses the selected caller's storage, leaves
the other instance unchanged, credits value once and never funds the library. -/
theorem source_linked_library : linkedSnapshot = .ok (8, 2, 5, true) := by decide +kernel

private def rejectedLink : TRes Bool := do
  let initial := World.empty Linked.contracts funds Linked.roles
  let (w, first) ← Linked.deployCaller initial factory { sender := alice }
  pure (match Linked.run w first { sender := alice } libraryAddress with
    | .error .revert => true | _ => false)

/-- Source library resolution does not substitute for installed linked code. -/
theorem source_requires_installed_link : rejectedLink = .ok true := by decide +kernel

private def rejectedStatic : TRes Bool := do
  let initial := World.empty Linked.contracts funds Linked.roles
  let (w, first) ← Linked.deployCaller initial factory { sender := alice }
  let (w, _) ← Linked.deployLibrary w libraryAddress { sender := alice }
  pure (match Linked.run w first { sender := alice, mode := .readOnly } libraryAddress with
    | .error .revert => true | _ => false)

/-- Source storage mutation through a link is refused in static context. -/
theorem source_static_library_rejected : rejectedStatic = .ok true := by decide +kernel

private def codeRecipient : TRes Bool := do
  let initial := World.empty Direct.contracts funds
  let (w, f) ← Direct.deploy initial recipient { sender := alice }
  pure (match admittedRun (Direct.assumptions w { sender := alice, mode := .ordinary three })
      (Direct.run w f { sender := alice, mode := .ordinary three } child) with
    | .error .exhausted => true | _ => false)

/-- The source API refuses a code-bearing constructor payment recipient;
unsupported receive/fallback execution does not become a successful transfer. -/
theorem source_code_recipient_not_admitted : codeRecipient = .ok true := by decide +kernel

/-- Every supplied external-response entry violates the source premise,
independently of the entry's result or the world's storage. -/
theorem source_oracle_input_not_admitted (w : World Direct.contracts)
    (key : Semantics.ExtKey) (result : Semantics.ExtResult) :
    Direct.assumptions w { sender := alice, ext := [(key, result)] } = false := by
  simp [Direct.assumptions]

/-- A successful executable result supplies its actual value; the fallback
is unreachable, and does not select a poststate on failure. -/
private theorem result_of_success {α : Type} (run : TRes α) (fallback : α)
    (success : run.toOption.isSome = true) : run = .ok (run.toOption.getD fallback) := by
  cases run with
  | error e => cases success
  | ok value => rfl

/-- A concrete source creation catch now has a funded constructor-rooted
transition witness, retaining the caller payment and the child's prefunding. -/
private def triedInitial : World Tried.contracts := World.empty Tried.contracts funds
private def triedDeployed : World Tried.contracts × Handle Tried.Code.factory :=
  (Tried.deploy triedInitial factory { sender := alice }).toOption.getD
    (triedInitial, ⟨factory⟩)
private theorem tried_deployment_ok :
    Tried.deploy triedInitial factory { sender := alice } = .ok triedDeployed :=
  result_of_success _ _ (by decide +kernel)
private def triedAdmission : Tried.assumptions triedDeployed.1
    { sender := alice, mode := .ordinary two } = true := by decide +kernel
private def triedFinal : World Tried.contracts × Bool :=
  (Tried.run triedDeployed.1 triedDeployed.2 { sender := alice, mode := .ordinary two }
    child triedAdmission).toOption.getD (triedDeployed.1, true)
private theorem tried_run_ok :
    Tried.run triedDeployed.1 triedDeployed.2 { sender := alice, mode := .ordinary two }
      child triedAdmission = .ok triedFinal :=
  result_of_success _ _ (by decide +kernel)

/-- Deployment followed by the actual source catch, rather than a chosen
poststate or an oracle response, establishes this reachable world. -/
theorem source_catch_reachable :
    Reachable funds (fun _ => .contractCode) (fun _ _ => True) triedFinal.1 := by
  have deployed : Reachable funds (fun _ => .contractCode) (fun _ _ => True)
      triedDeployed.1 :=
    Reachable.of_certificate .initial trivial
      (Operation.create_certificate triedInitial Tried.Code.factory factory .nil
        { sender := alice }) tried_deployment_ok
  have success : Tried.run triedDeployed.1 triedDeployed.2
      { sender := alice, mode := .ordinary two } child triedAdmission =
      .ok (triedFinal.1, triedFinal.2) :=
    tried_run_ok.trans (congrArg Except.ok (Prod.eta triedFinal).symm)
  exact Tried.run_reachable (w := triedDeployed.1) (next := triedFinal.1)
    (result := triedFinal.2) triedDeployed.2 { sender := alice, mode := .ordinary two }
    child triedAdmission deployed trivial success

/-- The reachable catch world retains exactly the previously observed
balances and reports the source's false catch return. -/
theorem source_catch_reachable_observations :
    ((triedFinal.1.balance alice).1, (triedFinal.1.balance factory).1,
      (triedFinal.1.balance child).1, (triedFinal.1.balance recipient).1,
      (triedFinal.1.accounts child).isNone, triedFinal.2) = (8, 2, 4, 0, true, false) := by
  decide +kernel

/-- Source factory rejection in read-only context is retained by the exact
operation certificate, even when no value was sent. -/
theorem source_static_factory_certificate (w : World Direct.contracts)
    (self : Handle Direct.Code.factory)
    (admitted : Direct.assumptions w { sender := alice, mode := .readOnly } = true) :
    (Direct.operation self { sender := alice, mode := .readOnly } child).run w =
      .error .revert := by
  rw [← Direct.run_certificate w self _ child admitted]
  simp only [Direct.run, Context.isStatic, Bool.or_true, ↓reduceIte, forgetResult]

#print axioms Direct.run_certificate
#print axioms Tried.run_certificate
#print axioms Linked.run_certificate
#print axioms Tried.run_reachable
#print axioms source_catch_reachable

private noncomputable def directOperationSnapshot : TRes (Int × Int × Int × Int) := do
  let initial := World.empty Direct.contracts funds
  let w ← (Operation.seq (.create .factory factory .nil { sender := alice })
    (Direct.operation ⟨factory⟩ { sender := alice, mode := .ordinary three } child)).run initial
  pure ((w.balance alice).1, (w.balance factory).1,
    (w.balance child).1, (w.balance recipient).1)

/-- The generated direct operation executes deployment, caller payment and
constructor settlement, agreeing with the independent source observations. -/
theorem source_direct_operation : directOperationSnapshot = .ok (7, 2, 4, 1) := by
  decide +kernel

private noncomputable def linkedOperationSnapshot : TRes (Int × Int × Int × Bool) := do
  let initial := World.empty Linked.contracts funds Linked.roles
  let w ← (Operation.seq (.create .caller factory .nil { sender := alice })
    (.seq (.create .caller otherCaller .nil { sender := alice })
      (.seq (.deployLibrary .library libraryAddress { sender := alice })
        (Linked.operation ⟨factory⟩ { sender := alice, mode := .ordinary two } libraryAddress)))).run initial
  let (w, _) ← w.call (⟨factory⟩ : Handle Linked.Code.caller)
    (Entry.unit Linked.Source.WorldLibraryUser.checkNine) { sender := alice }
  let (w, _) ← w.call (⟨otherCaller⟩ : Handle Linked.Code.caller)
    (Entry.unit Linked.Source.WorldLibraryUser.checkZero) { sender := alice }
  pure ((w.balance alice).1, (w.balance factory).1, (w.balance libraryAddress).1,
    (match w.call (⟨factory⟩ : Handle Linked.Code.caller)
        (Entry.unit Linked.Source.WorldLibraryUser.checkZero) { sender := alice } with
      | .error .panic => true | _ => false))

/-- The linked operation preserves caller alias identity and charges the
incoming payment once; the second caller and library balances stay independent. -/
theorem source_linked_operation : linkedOperationSnapshot = .ok (8, 2, 5, true) := by
  decide +kernel

/-- A failed caller argument never enters the operation's creation catch. -/
theorem source_operation_argument_exhaustion (w : World Tried.contracts) :
    (Operation.tryCreate (.error .exhausted : TRes Unit) Tried.Code.target
      (fun _ => child) (fun _ => Tried.constructor)
      (fun _ => { sender := factory })).run w = .error .exhausted := rfl

#print axioms source_direct_operation
#print axioms source_linked_operation

/-- error: solidity.worldFactory.body: expected exactly one creation return or creation try -/
#guard_msgs in
solc_world_factory "../../../tests/solc/ContractWorld.ast.json" hash 0x7e8caacffff380a9
  contract "WorldFactory" function "extra" as Extra

/-- error: solidity.worldFactory.arguments: factory parameters are not lowered yet -/
#guard_msgs in
solc_world_factory "../../../tests/solc/ContractWorld.ast.json" hash 0x7e8caacffff380a9
  contract "WorldFactory" function "dynamicArgument" as Dynamic

/-- error: solidity.worldLibrary.body: exactly one direct library call required -/
#guard_msgs in
solc_world_library "../../../tests/solc/ContractWorld.ast.json" hash 0x7e8caacffff380a9
  contract "WorldLibraryUser" function "extra" as ExtraLibrary

/-- error: solidity.worldFactory.constructor: external contract/library calls need world-aware statements -/
#guard_msgs in
solc_world_factory "../../../tests/solc/ContractWorld.ast.json" hash 0x7e8caacffff380a9
  contract "WorldFactory" function "callsExternal" as ExternalConstructor

/-- error: solidity.worldFactory.constructor: balance observations need the global world expression interface -/
#guard_msgs in
solc_world_factory "../../../tests/solc/ContractWorld.ast.json" hash 0x7e8caacffff380a9
  contract "WorldFactory" function "readsBalance" as BalanceConstructor

#print axioms source_factory
#print axioms source_creation_try
#print axioms source_creation_try_success
#print axioms source_linked_library

end Solidity.Examples.Tactics.ContractWorldSource
