import Solidity.Goals.IntrinsicSession
import Solidity.Semantics.IntrinsicStorage.Preimages.Frames
import Solidity.Semantics.IntrinsicStorage.Preimages.Ops
import Solidity.Semantics.IntrinsicStorage.Preimages.Run
import Solidity.Semantics.IntrinsicStorage.Preimages.Calls

/-! The concrete storage and preimage strengthening of the intrinsic-session goal
(`is0-intrinsic-session`), one module per goal (H666).

`intrinsicStorageAccounting` keeps `IntrinsicSession.Laws` unchanged and adds
the storage and preimage accounting it leaves open:

* the slot preimages a typed world stores are the concrete ones,
  `IntrinsicStorage.stored` of its contract world: every account, shadows and
  every mapping default, a mathematical list never enumerated. `View` is
  read only, so `View.stored` is pinned by a conjunct instead of a definition;
* a completed transaction of a determined body (the premises of `Laws.transacts`)
  accounts for the inputs its actual typed callee frame hashes:
  `IntrinsicStorage.Frame.call` at some fuel gives the actual frame result together
  with those inputs, including the inputs before a caught or uncaught revert;
* the same for the selected constructor of a deployment (`Laws.deploys`), through
  `IntrinsicStorage.Frame.create`, before rollback discards its writes.

Ideal slot terms (`Storage.Loc`, `Pre`) and concrete preimages (`encoded`, byte
lists) stay separate: the laws speak of encoded inputs only, and nothing assumes
keccak injectivity, a correspondence between terms and hashes, a toy store or a
chosen trace. Whole-session hash equality and the reachability of interacting
frames from the session strategy and history stay the session implementation's
obligation (H720). -/

namespace Solidity.Goals

open Solidity.Goal

namespace IntrinsicSession

open Solidity.Roadmap
open Solidity.Lowering.V08.EnvironmentProjection
  (liftWord liftAddress requestContext)

/-- Accounting for the canonical typed-frame observer: the slot preimages it
reached are slot preimages of the run, and every input it hashed is hashed by the
run. This pins actual reached body operands even when the enclosing frame fails;
it is not whole-session hash equality and does not instrument the opaque
caller-side `Entry.result` decoder. -/
def FrameInputs (I : IntrinsicSpec) (p : I.lang.Prog) (en : I.lang.Env) (r : I.lang.Res)
    (a : Solidity.Semantics.IntrinsicStorage.Inputs) : Prop :=
  (∀ b ∈ a.slots, b ∈ I.slotHashed p en r) ∧
  (∀ b ∈ a.hashed, b ∈ I.hashed p en r)

/-- The storage and preimage laws added to `Laws` by `intrinsicStorageAccounting`. -/
structure StorageLaws (F : Fixed) (I : IntrinsicSpec) (V : View I) : Prop where
  /-- Concrete account-function storage, including shadows and all mapping
  defaults. The finite list is a mathematical specification, never an enumerated
  test domain. Full default coverage can exceed `Forward`'s unchanged hash bound;
  no finite-support or zero-default assumption is imposed. -/
  stored : ∀ t : TypedWorld, V.stored t = Solidity.Semantics.IntrinsicStorage.stored t.world
  /-- A completed determined transaction accounts for a completed observation
  of its actual typed callee frame, including inputs before a caught or uncaught
  revert. Fuel is witnessed together with equality to the actual frame result;
  an insufficient prefix cannot stand in for a completed frame. H720 defers
  whole-session equality and interacting-frame reachability to is0. -/
  call_inputs : ∀ x en h n (code : Code) (cw : ContractWorld.World code.catalog)
      (q : Request) (k : Fin code.contracts.length) (st : Storage (code.catalog k))
      (entry : ContractWorld.Entry (code.catalog k) Bytes),
    I.lang.Allowed en → V.Boundary x en h n ⟨code, cw⟩ →
    (I.session en).requests h n = some (.request q) → Funded F (I.session en) h q →
    cw.accounts (liftAddress q.target) = some ⟨k, st⟩ → code.entry k q.input = some entry →
    Prog.callsBack true entry.body = false →
    (liftWord q.value).1 ≤ (cw.funds (liftAddress q.sender)).1 →
    let p := I.ofWorld x
    let w := (cw.atTime (liftWord q.timestamp)).resetTransient
    let ref : ContractWorld.Handle k := ⟨liftAddress q.target⟩
    let run := w.call ref entry (requestContext q [])
    (∀ ext, (cw.atTime (liftWord q.timestamp)).transact
        (fun w => w.call ref entry (requestContext q ext)) =
      (cw.atTime (liftWord q.timestamp)).transact
        (fun w => w.call ref entry (requestContext q []))) →
    Ends run → ∀ r out, Good I r →
      h ++ [Event.tx q.sender q.target q.value q.timestamp q.input out] <+:
        (I.lang.sem p en r).events →
      ∃ fuel, let a := Solidity.Semantics.IntrinsicStorage.Frame.call fuel w ref entry
          (requestContext q [])
        a.result = run ∧ FrameInputs I p en r a.inputs
  /-- The same concrete obligation for the selected constructor, before
  transaction rollback discards its attempted writes and payments. -/
  create_inputs : ∀ (code : Code) (en : I.lang.Env) (k : Fin code.contracts.length)
      (body : Prog (code.catalog k) [] []),
    I.lang.Allowed en → k.val = code.main →
    code.ctor k (I.session en).deployArgs = some body → Prog.callsBack true body = false →
    let e := I.session en
    let p := I.ofWorld (V.initial code)
    let this := F.createAddress e.deployer e.deployNonce
    e.deployValue.val ≤ (e.balance e.deployer).val → this ≠ e.deployer →
    let w := (ContractWorld.World.empty code.catalog (funds e.balance) code.roles).resetTransient
    let ctx : ContractWorld.Context :=
      { sender := liftAddress e.deployer, mode := .ordinary (liftWord e.deployValue), ext := [] }
    let run := w.create k (liftAddress this) body ctx
    (∀ ext, (ContractWorld.World.empty code.catalog (funds e.balance) code.roles).transact
        (fun w => w.create k (liftAddress this) body { ctx with ext := ext }) =
      (ContractWorld.World.empty code.catalog (funds e.balance) code.roles).transact
        (fun w => w.create k (liftAddress this) body ctx)) →
    Ends run → ∀ r out address, Good I r →
      [Event.deploy e.deployer e.deployValue e.deployArgs out address] <+:
        (I.lang.sem p en r).events →
      ∃ fuel, let a := Solidity.Semantics.IntrinsicStorage.Frame.create fuel w k
          (liftAddress this) body ctx
        a.result = run ∧ FrameInputs I p en r a.inputs

end IntrinsicSession

/-- For every fixed parameters there is a concrete intrinsic session semantics
satisfying `IntrinsicSession.Laws` whose stored slot preimages are the concrete
ones of its typed worlds and whose completed determined frames account for the
inputs their actual typed observation hashes (`IntrinsicSession.StorageLaws`).
Whole-session hash equality remains deferred to the session implementation (H720). -/
@[goal Solidity.Semantics.IntrinsicSession.storage_accounting_correct "is0-intrinsic-session"]
def intrinsicStorageAccounting : Prop :=
  ∀ F : Solidity.Roadmap.Fixed, ∃ (I : Solidity.Roadmap.IntrinsicSpec)
    (V : IntrinsicSession.View I), IntrinsicSession.Laws F I V ∧ IntrinsicSession.StorageLaws F I V

end Solidity.Goals
