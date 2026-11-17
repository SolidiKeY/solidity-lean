import Solidity.Semantics.Callback
import Solidity.Semantics.TransientWorld
import Solidity.Roadmap.Contracts
import Solidity.Lowering.V08.EnvironmentProjection

/-!
# The intrinsic session: world, bound, frames and the one-action step

Definitions for the concrete intrinsic session semantics (H556 option A, plan
step `is0d-session-step`), part 1 of 2 of the session run; nothing here is a
goal. The module sits under `Solidity/Correctness` because it reads the
projections of `Lowering.V08.EnvironmentProjection` (`liftWord`,
`liftAddress`, `requestContext`), which the core may not import; the
namespace is `Solidity.Semantics.IntrinsicSession`.

* **The session world** is an actual `ContractWorld.World` over a catalog of
  `Contract`s. Its resolution data are section parameters, in the order of
  the code of `Solidity.Goals.IntrinsicSession.Code`: the contracts, the main
  index, the roles, the constructor and the entry resolution.
* **A bound** (`Bound`) is a horizon of actions and the frames that fail for
  lack of resources: the deployment's and each action's by its index. Bounds
  are ordered by horizon at the same failures; every bound is admissible and
  a bound without failures has none (`Bound.NoFail`).
* **A frame** (`Frame`) records the exact arguments of
  `IntrinsicStorage.Frame.call` / `Frame.create`: the world it ran from (after
  `atTime` and `resetTransient`), the handle and entry or the contract index,
  address and constructor, and the `ContractWorld.Context`.
* **The step** (`step`, `deploy`) of one action at a transaction boundary
  returns the events it appends, the next world and the frames it ran,
  reverting ones included. A deployment is `World.transact` of the actual
  `World.create` at `Fixed.createAddress`; an affordable request (`Funded`)
  is `World.transact` of the actual `World.call` at the request's time with
  `requestContext`; an unaffordable one is dropped; a credit raises the
  target's global funds. A frame that exhausts or diverges shows no event and
  stops the session at a bound without resource failure; a frame the bound
  fails shows a revert with empty data and changes nothing.

Choices the laws leave open (`Solidity.Goals.IntrinsicSession`, module
comment), taken here:

* the typed run reads external answers from a table (`TTx.ext`); the frame's
  table is the callee strategy's answers on the history so far (`responses`),
  read through an ABI reading `Wire` of the keys a frame may look up. The
  typed run does not report the calls it makes, so a step appends no `call`
  or `answer` event;
* a request to an address without an instance succeeds with no data and
  changes nothing; one whose input the code does not resolve, and an
  unresolved deployment, revert with no data;
* a successful deployment shows `success []`; a credit whose sum is not a word
  changes nothing.
-/

namespace Solidity.Semantics.IntrinsicSession

open Solidity.Roadmap
open Solidity.ContractWorld (World Handle Entry Context Role)
open Solidity.Lowering.V08.EnvironmentProjection (liftWord liftAddress lowerAddress requestContext)

/-! ## Bounds -/

/-- A resource bound: the number of actions observed after the deployment,
whether the deployment's frame fails for lack of resources, and which
actions' frames do (by the action's index). -/
structure Bound where
  horizon : Nat
  deployFails : Bool := false
  fails : Nat → Bool := fun _ => false

/-- A larger bound observes more actions with the same failures. -/
instance : LE Bound where
  le r r' := r.horizon ≤ r'.horizon ∧ r.deployFails = r'.deployFails ∧ r.fails = r'.fails

theorem Bound.le_refl (r : Bound) : r ≤ r := ⟨Nat.le_refl _, rfl, rfl⟩

theorem Bound.le_trans {r r' r'' : Bound} (a : r ≤ r') (b : r' ≤ r'') : r ≤ r'' :=
  ⟨Nat.le_trans a.1 b.1, a.2.1.trans b.2.1, a.2.2.trans b.2.2⟩

/-- Every bound is admissible: a resource failure is a frame out of resources,
which reverts, never an inadmissible run. -/
def Bound.Admissible (_ : Bound) : Prop := True

/-- No frame fails for lack of resources. -/
def Bound.NoFail (r : Bound) : Prop := r.deployFails = false ∧ ∀ n, r.fails n = false

/-- Two bounds without failures have the larger horizon as a common upper bound. -/
theorem Bound.directed {r r' : Bound} (h : r.NoFail) (h' : r'.NoFail) :
    ∃ r'' : Bound, r''.NoFail ∧ r ≤ r'' ∧ r' ≤ r'' := by
  refine ⟨{ horizon := max r.horizon r'.horizon }, ⟨rfl, fun _ => rfl⟩,
    ⟨Nat.le_max_left _ _, h.1, funext h.2⟩, ⟨Nat.le_max_right _ _, h'.1, funext h'.2⟩⟩

/-! ## Frames -/

section Frames

variable {K : Type} (contracts : K → Contract)

/-- What a frame runs: a transaction's call or the deployment's creation. -/
inductive FrameKind where
  | call
  | create
  deriving DecidableEq, Repr

/-- The body of a frame with its target: the handle and resolved entry of a
call (`Frame.call`), or the contract, address and constructor of a creation
(`Frame.create`). -/
inductive FrameBody where
  | call {k : K} (r : Handle k) (entry : Entry (contracts k) Bytes)
  | create (k : K) (self : ContractWorld.Address) (ctor : Prog (contracts k) [] [])

/-- One executed frame: the world it ran from (after `atTime` and
`resetTransient`), its body and its context. -/
structure Frame where
  world : World contracts
  body : FrameBody contracts
  ctx : Context

variable {contracts}

def Frame.kind (f : Frame contracts) : FrameKind :=
  match f.body with
  | .call .. => .call
  | .create .. => .create

variable (contracts) in
/-- What one step does: the events it appends, the world it reaches, the
frames it ran, and whether the session stops (a frame that exhausted or
diverged). -/
structure StepOut where
  events : List Event
  world : World contracts
  frames : List (Frame contracts)
  stops : Bool := false

end Frames

/-! ## Outcomes and answers -/

/-- A frame result as an outcome, when it completed: a return, or a revert with
the halt's data. Exhaustion and divergence have none. -/
def outcomeOf : TRes Bytes → Option Outcome
  | .ok d => some (.success d)
  | .error h => if ContractWorld.catchable h then some (.revert h.data) else none

/-- An ABI reading of external calls: the keys a frame may look up, the call
event each one is, and the answer an outcome gives. -/
structure Wire where
  keys : List Semantics.ExtKey
  call : Semantics.ExtKey → Event
  result : Outcome → Semantics.ExtResult

/-- The response table of a frame after the history `h`: the strategy's answer
to each key's call there. A key the strategy answers with another move has no
entry. -/
def responses (wire : Wire) (e : SessionEnv) (h : List Event) :
    List (Semantics.ExtKey × Semantics.ExtResult) :=
  wire.keys.filterMap fun key =>
    match e.callee (h ++ [wire.call key]) with
    | .answer o => some (key, wire.result o)
    | _ => none

/-- Session opening balances as a world's global funds. -/
def funds (b : Address → Roadmap.Word) : ContractWorld.Address → ContractWorld.Word :=
  fun a => liftWord (b (lowerAddress a))

/-- The request is affordable after `h` on the ledger over the opening balances. -/
def Funded (F : Fixed) (e : SessionEnv) (h : List Event) (q : Request) : Prop :=
  q.value.val ≤ (F.ledger e.balance h q.sender).val

instance (F : Fixed) (e : SessionEnv) (h : List Event) (q : Request) :
    Decidable (Funded F e h q) := Nat.decLe _ _

/-! ## The step -/

section Step

/-- The catalog the session world indexes instances by. -/
abbrev catalog (contracts : List Contract) (k : Fin contracts.length) : Contract := contracts[k]

variable {contracts : List Contract} (main : Nat) (roles : Fin contracts.length → Role)
  (ctor : (k : Fin contracts.length) → Bytes → Option (Prog contracts[k] [] []))
  (entry : (k : Fin contracts.length) → Bytes → Option (Entry contracts[k] Bytes))
  (F : Fixed) (wire : Wire) (r : Bound) (e : SessionEnv)

/-- The world a session starts from: nothing deployed, funded by the opening
balances. -/
def initial : World (catalog contracts) := World.empty (catalog contracts) (funds e.balance) roles

/-- The deployment context: the deployer, the deployment value, and the
strategy's answers on the empty history. -/
def deployContext : Context :=
  { sender := liftAddress e.deployer, mode := .ordinary (liftWord e.deployValue),
    ext := responses wire e [] }

/-- The deployment: `World.transact` of the actual `World.create` of the main
contract's resolved constructor at `Fixed.createAddress`, from `initial`. -/
noncomputable def deploy : StepOut (catalog contracts) :=
  let w := initial roles e
  let this := F.createAddress e.deployer e.deployNonce
  let done out address := Event.deploy e.deployer e.deployValue e.deployArgs out address
  if hk : main < contracts.length then
    match ctor ⟨main, hk⟩ e.deployArgs with
    | none => { events := [done (.revert []) none], world := w, frames := [] }
    | some body =>
      let ctx := deployContext wire e
      let res := w.transact fun v => v.create ⟨main, hk⟩ (liftAddress this) body ctx
      let frame : Frame (catalog contracts) :=
        ⟨w.resetTransient, .create ⟨main, hk⟩ (liftAddress this) body, ctx⟩
      if r.deployFails then
        { events := [done (.revert []) none], world := w.resetTransient, frames := [frame] }
      else
        match res.2 with
        | .ok _ => { events := [done (.success []) (some this)], world := res.1, frames := [frame] }
        | .error h =>
          if ContractWorld.catchable h then
            { events := [done (.revert h.data) none], world := res.1, frames := [frame] }
          else { events := [], world := w, frames := [frame], stops := true }
  else { events := [done (.revert []) none], world := w, frames := [] }

/-- The `n`-th action's request `q` after the history `h`, at the boundary
world `w`. Dropped when not `Funded`; otherwise `World.transact` of the actual
`World.call` of the target's resolved entry at `w.atTime q.timestamp`, with
`requestContext` and the strategy's answers. -/
noncomputable def request (h : List Event) (n : Nat) (w : World (catalog contracts))
    (q : Request) : StepOut (catalog contracts) :=
  let done := Event.tx q.sender q.target q.value q.timestamp q.input
  if ¬ Funded F e h q then { events := [], world := w, frames := [] } else
  match w.accounts (liftAddress q.target) with
  | none => { events := [done (.success [])], world := w, frames := [] }
  | some ⟨k, _⟩ =>
    match entry k q.input with
    | none => { events := [done (.revert [])], world := w, frames := [] }
    | some en =>
      let w0 := w.atTime (liftWord q.timestamp)
      let target : Handle k := ⟨liftAddress q.target⟩
      let ctx := requestContext q (responses wire e h)
      let res := w0.transact fun v => v.call target en ctx
      let frame : Frame (catalog contracts) := ⟨w0.resetTransient, .call target en, ctx⟩
      if r.fails n then
        { events := [done (.revert [])], world := w0.resetTransient, frames := [frame] }
      else
        match outcomeOf res.2 with
        | some out => { events := [done out], world := res.1, frames := [frame] }
        | none => { events := [], world := w, frames := [frame], stops := true }

/-- A credit: the event, and the target's global funds raised when the sum is a
word. -/
def credit (w : World (catalog contracts)) (target : Address) (value : Roadmap.Word) :
    StepOut (catalog contracts) :=
  let a := liftAddress target
  let w' := match PrimTy.ofInt? .uint ((w.funds a).1 + (liftWord value).1) with
    | some sum => { w with funds := fun x => if x = a then sum else w.funds x }
    | none => w
  { events := [.credit target value], world := w', frames := [] }

/-- One action at a transaction boundary: the `n`-th, after the history `h`, at
the world `w`. -/
noncomputable def step (h : List Event) (n : Nat) (w : World (catalog contracts)) :
    Action → StepOut (catalog contracts)
  | .request q => request entry F wire r e h n w q
  | .credit target value => credit w target value

end Step

end Solidity.Semantics.IntrinsicSession
