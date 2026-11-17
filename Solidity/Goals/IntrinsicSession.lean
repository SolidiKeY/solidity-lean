import Solidity.Tools.Goal
import Solidity.Roadmap.Contracts
import Solidity.Semantics.Callback
import Solidity.Semantics.TransientWorld
import Solidity.Lowering.V08.EnvironmentProjection

/-! The intrinsic-session plan goal (`is0-intrinsic-session`), one module per goal. -/

namespace Solidity.Goals

open Solidity.Goal

/-! Concrete intrinsic session semantics (plan step is0-intrinsic-session). The
obligation is a concrete `Roadmap.IntrinsicSpec` whose worlds are read as actual
typed contract worlds (`ContractWorld.World` over a catalog of `Contract`s, with
the `Prog`s it runs) and whose sessions are tied, boundary by boundary, to the
existing frame semantics:

* `View.Boundary x en h n t`: the session of world `x` in `en` stands at a
  transaction boundary after exactly the history `h`, with `n` actions issued, in
  the typed world `t`. Boundaries are observed at bounds without resource failure,
  and every listed world is one;
* at a boundary, a deployment or transaction whose body never leaves its contract
  (`Prog.callsBack true = false`, and no response table changes its result) is
  exactly `World.transact` of `World.create` / `World.call`: the logical
  `Prog.run`, with no fuel in the statement. Exhaustion and divergence yield no
  event at a bound without resource failure (`ContractWorld.catchable`), and a
  completed run is observed at some such bound;
* dropped requests (`Funded`, the reading of `Lang.Affordable` at the boundary's
  history), credits, the end of the session, the callee strategy's moves,
  `Forward`, `Guard` and the environment maps are those of `Roadmap/Contracts.lean`.

Not determined by the typed definitions this reads, and therefore not chosen
here: how the strategy's answers reach a body that leaves its contract (`TTx.ext`
is a table, a strategy reads the history) and every event of such a body past the
move after a call; the revert data of a `THalt.panic` (it carries no code); the
data of a successful deployment; what follows a reverted deployment or a credit
whose sum is not a word; deployments and requests the code does not resolve;
a request or deployment whose value the sender's funds in the world do not cover
(the frame reverts there, the ledger may call it affordable); the final
observation of a session without outcomes; whether the world after a deployment
or a credit is listed; bounds with resource failures, beyond an upper bound on
the outcome a determined first step shows there (its own, or a revert with empty
data: no failing bound is required to exist); environments that are not allowed;
and the preimages a run hashes and the slot preimages of the keys a typed
storage holds (`View.stored` is only required to be accounted for, so this goal
does not pin `Forward` and `Guard` beyond their definitions). Within a determined
step the frame's own accounting is the typed world's: global funds, debited from
the sender on success. `Lang.Affordable` over a whole history is not required:
`Fixed.ledger` is an arbitrary function and the history of a transaction includes
its inner events. -/
namespace IntrinsicSession

open Solidity.Roadmap
open Solidity.Lowering.V08.EnvironmentProjection
  (liftWord lowerWord liftAddress lowerAddress requestContext)

/-- The code of a compilation: its contracts by position (as `Artifact.contracts`
and `Event.create` number them), the selected one, their roles, and the programs a
deployment or a request runs. `ctor` and `entry` resolve constructor arguments and
calldata to actual typed programs; an entry's `result` gives its return data. -/
structure Code where
  contracts : List Contract
  main : Nat
  roles : Fin contracts.length → ContractWorld.Role
  ctor : (k : Fin contracts.length) → Bytes → Option (Prog contracts[k] [] [])
  entry : (k : Fin contracts.length) → Bytes → Option (ContractWorld.Entry contracts[k] Bytes)

/-- The catalog `ContractWorld` indexes instances by. -/
abbrev Code.catalog (c : Code) (k : Fin c.contracts.length) : Contract := c.contracts[k]

/-- An actual typed contract world together with its code. -/
structure TypedWorld where
  code : Code
  world : ContractWorld.World code.catalog

/-- Session opening balances as a world's global funds. -/
def funds (b : Address → Roadmap.Word) : ContractWorld.Address → ContractWorld.Word :=
  fun a => liftWord (b (lowerAddress a))

/-- Two worlds agree at a transaction boundary: instances and storage up to the
transaction-local cells, funds and roles. The timestamp is each request's own. -/
def Same {K : Type} {contracts : K → Contract} (a b : ContractWorld.World contracts) : Prop :=
  a.resetTransient.accounts = b.resetTransient.accounts ∧ a.funds = b.funds ∧ a.roles = b.roles

/-- `t` is the world `w` of `code`, at a transaction boundary. -/
def TypedWorld.Shows (t : TypedWorld) (code : Code) (w : ContractWorld.World code.catalog) :
    Prop :=
  ∃ w' : ContractWorld.World code.catalog, t = ⟨code, w'⟩ ∧ Same w' w

/-- `b` is `a` with the funds of `target` set to `sum`, and nothing else changed. -/
def Credited {K : Type} {contracts : K → Contract} (a : ContractWorld.World contracts)
    (target : ContractWorld.Address) (sum : ContractWorld.Word)
    (b : ContractWorld.World contracts) : Prop :=
  a.resetTransient.accounts = b.resetTransient.accounts ∧ a.roles = b.roles ∧
  (∀ x, x ≠ target → b.funds x = a.funds x) ∧ b.funds target = sum

/-- The request is affordable after the history `h` (`Lang.Affordable`, on the
ledger over the opening balances); otherwise it is dropped. -/
def Funded (F : Fixed) (e : SessionEnv) (h : List Event) (q : Request) : Prop :=
  q.value.val ≤ (F.ledger e.balance h q.sender).val

/-- A frame result that completed: a return, or a failure a caller can observe.
Divergence and exhaustion are not completions. -/
def Ends {α : Type} : TRes α → Prop
  | .ok _ => True
  | .error h => ContractWorld.catchable h = true

/-- A completed failure as an outcome: a revert with the halt's data. A panic's
data is not read off `THalt.panic`, which carries no code. -/
def RevertMatches (h : THalt) (out : Outcome) : Prop :=
  ContractWorld.catchable h = true ∧ ∃ d, out = .revert d ∧ (h ≠ .panic → d = h.data)

/-- A transaction's frame result as its outcome. -/
def Matches : TRes Bytes → Outcome → Prop
  | .ok d, out => out = .success d
  | .error h, out => RevertMatches h out

/-- The outcomes of the completed deployments and transactions of a history. -/
def outcomes (h : List Event) : List Outcome :=
  h.filterMap fun
    | .deploy _ _ _ o _ => some o
    | .tx _ _ _ _ _ o => some o
    | _ => none

/-- A completed transaction. -/
def IsTx : Event → Prop
  | .tx .. => True
  | _ => False

/-- The event a move of the callee strategy shows. -/
def Moved : Move → Event → Prop
  | .answer o, x => ∃ created, x = .answer o created
  | .reenter t s v i st, x => x = .reenter t s v i st
  | .credit t v, x => x = .credit t v

/-- How a candidate's worlds are typed worlds: the typed world of each world, the
world a compilation starts from (nothing deployed), the world resumed at a typed
world, the slot preimages of the keys a typed world stores, and the transaction
boundaries of a session (history, actions issued, typed world). -/
structure View (I : IntrinsicSpec) where
  typed : I.World → TypedWorld
  initial : Code → I.World
  resume : TypedWorld → I.World
  stored : TypedWorld → List Bytes
  Boundary : I.World → I.lang.Env → List Event → Nat → TypedWorld → Prop

/-- A bound the laws speak of: admissible and without resource failure. -/
def Good (I : IntrinsicSpec) (r : I.lang.Res) : Prop := I.lang.Admissible r ∧ I.NoFail r

/-- The history is observed at some bound without resource failure. -/
def Observed (I : IntrinsicSpec) (p : I.lang.Prog) (en : I.lang.Env) (h : List Event) : Prop :=
  ∃ r, Good I r ∧ h <+: (I.lang.sem p en r).events

/-- The laws of the concrete intrinsic session semantics `I`, read through `V`,
over the fixed parameters `F`. -/
structure Laws (F : Fixed) (I : IntrinsicSpec) (V : View I) : Prop where
  /-- The fixed parameters are the given ones. -/
  fixed : I.fixed = F
  /-- The shared readings of every layer's events. -/
  precompiles : I.lang.PrecompilesFixed
  this : I.lang.ThisFromDeployment F I.session
  /-- Bounds without resource failure have common upper bounds, so the
  consistency of the prefixes relates any two of them. -/
  directed : ∀ r r', Good I r → Good I r' →
    ∃ r'', Good I r'' ∧ I.lang.resLE.le r r'' ∧ I.lang.resLE.le r' r''
  /-- Larger bounds extend the listed worlds and the preimages. -/
  worlds_consistent : ∀ p e r r', I.lang.resLE.le r r' → I.worlds p e r <+: I.worlds p e r'
  hashed_consistent : ∀ p e r r', I.lang.resLE.le r r' → I.hashed p e r <+: I.hashed p e r'
  slotHashed_sub : ∀ p e r b, b ∈ I.slotHashed p e r → b ∈ I.hashed p e r
  /-- A final observation is the last completed outcome. -/
  final_last : ∀ p e r o, (I.lang.sem p e r).final = some o →
    outcomes (I.lang.sem p e r).events = [] ∨
      (outcomes (I.lang.sem p e r).events).getLast? = some o
  /-- The event after a call to the environment is the strategy's move there. -/
  answered : ∀ p en r h callee value input static x, I.lang.Allowed en → Good I r →
    h ++ [Event.call callee value input static, x] <+: (I.lang.sem p en r).events →
    Moved ((I.session en).callee (h ++ [Event.call callee value input static])) x
  /-- Worlds keep their code. -/
  typed_resume : ∀ t, V.typed (V.resume t) = t
  initial_code : ∀ c, (V.typed (V.initial c)).code = c
  worlds_code : ∀ x e r, ∀ ω ∈ I.worlds (I.ofWorld x) e r,
    (V.typed ω).code = (V.typed x).code
  /-- A listed world runs as the world resumed at its typed world. -/
  listed_resumes : ∀ x e r, ∀ ω ∈ I.worlds (I.ofWorld x) e r,
    let p := I.ofWorld ω
    let p' := I.ofWorld (V.resume (V.typed ω))
    I.lang.sem p = I.lang.sem p' ∧ I.worlds p = I.worlds p' ∧ I.hashed p = I.hashed p' ∧
      I.slotHashed p = I.slotHashed p'
  /-- A run resumed from a world accounts for the keys the world stores. -/
  stored_hashed : ∀ t e r, ∀ b ∈ V.stored t, b ∈ I.slotHashed (I.ofWorld (V.resume t)) e r
  /-- A session resumed at a typed world starts at that world. -/
  starts : ∀ (t : TypedWorld) (en : I.lang.Env), I.lang.Allowed en →
    V.Boundary (V.resume t) en [] 0 t
  /-- A boundary's history is observed, and its world has the session's code. -/
  boundary_observed : ∀ x en h n t, V.Boundary x en h n t → Observed I (I.ofWorld x) en h
  boundary_code : ∀ x en h n t, V.Boundary x en h n t → t.code = (V.typed x).code
  /-- Every listed world is the world of a boundary the prefix has reached. -/
  listed_boundary : ∀ x en r, Good I r → ∀ ω ∈ I.worlds (I.ofWorld x) en r,
    ∃ h n, V.Boundary x en h n (V.typed ω) ∧ h <+: (I.lang.sem (I.ofWorld x) en r).events
  /-- No further action: the history is complete, and the session completes once
  it has an outcome. -/
  idle : ∀ x en h n t, I.lang.Allowed en → V.Boundary x en h n t →
    (I.session en).requests h n = none →
    (∀ r, Good I r → h <+: (I.lang.sem (I.ofWorld x) en r).events →
      (I.lang.sem (I.ofWorld x) en r).events = h) ∧
    (outcomes h ≠ [] → ∃ r, Good I r ∧ (I.lang.sem (I.ofWorld x) en r).events = h ∧
      (I.lang.sem (I.ofWorld x) en r).final ≠ none)
  /-- An unaffordable request is dropped: the next action, same history and world. -/
  dropped : ∀ x en h n t (q : Request), I.lang.Allowed en → V.Boundary x en h n t →
    (I.session en).requests h n = some (.request q) → ¬ Funded F (I.session en) h q →
    V.Boundary x en h (n + 1) t
  /-- A credit is the next event; when the sum is a word, the boundary after it
  has the target's global funds raised and nothing else changed. -/
  credited : ∀ x en h n (code : Code) (cw : ContractWorld.World code.catalog)
      (target : Address) (value : Roadmap.Word),
    I.lang.Allowed en → V.Boundary x en h n ⟨code, cw⟩ →
    (I.session en).requests h n = some (.credit target value) →
    let p := I.ofWorld x
    let done := Event.credit target value
    Observed I p en (h ++ [done]) ∧
    (∀ r, Good I r → h <+: (I.lang.sem p en r).events →
      (I.lang.sem p en r).events = h ∨ h ++ [done] <+: (I.lang.sem p en r).events) ∧
    ∀ sum, PrimTy.ofInt? .uint ((cw.funds (liftAddress target)).1 + (liftWord value).1) =
        some sum →
      ∃ cw' : ContractWorld.World code.catalog, Credited cw (liftAddress target) sum cw' ∧
        V.Boundary x en (h ++ [done]) (n + 1) ⟨code, cw'⟩
  /-- **A transaction that never leaves its contract is the actual frame**: at a
  boundary, an affordable request, covered by its sender's funds in the world, to an
  instance whose code resolves its input to a body without external interaction,
  whose result no response table changes, is
  the next event exactly when `World.transact` of the actual `World.call`
  completes, with that outcome; the world it reaches is listed and is the next
  boundary. As the first event of a session, at any admissible bound (resource
  failures included), its outcome if shown is that one or a revert with empty
  data; past the first step a failing bound may have reached another world. -/
  transacts : ∀ x en h n (code : Code) (cw : ContractWorld.World code.catalog)
      (q : Request) (k : Fin code.contracts.length) (st : Storage (code.catalog k))
      (entry : ContractWorld.Entry (code.catalog k) Bytes),
    I.lang.Allowed en → V.Boundary x en h n ⟨code, cw⟩ →
    (I.session en).requests h n = some (.request q) → Funded F (I.session en) h q →
    cw.accounts (liftAddress q.target) = some ⟨k, st⟩ → code.entry k q.input = some entry →
    Prog.callsBack true entry.body = false →
    (liftWord q.value).1 ≤ (cw.funds (liftAddress q.sender)).1 →
    let p := I.ofWorld x
    let frame := fun ext => (cw.atTime (liftWord q.timestamp)).transact fun w =>
      w.call (⟨liftAddress q.target⟩ : ContractWorld.Handle k) entry (requestContext q ext)
    let res := frame []
    (∀ ext, frame ext = res) →
    (Ends res.2 → ∃ out, Observed I p en
      (h ++ [Event.tx q.sender q.target q.value q.timestamp q.input out])) ∧
    (∀ r, Good I r → h <+: (I.lang.sem p en r).events →
      (I.lang.sem p en r).events = h ∨ ∃ out,
        let done := Event.tx q.sender q.target q.value q.timestamp q.input out
        h ++ [done] <+: (I.lang.sem p en r).events ∧ Matches res.2 out ∧
        ∃ ω ∈ I.worlds p en r, (V.typed ω).Shows code res.1 ∧
          V.Boundary x en (h ++ [done]) (n + 1) (V.typed ω)) ∧
    ∀ r, I.lang.Admissible r → h = [] → ∀ out,
      [Event.tx q.sender q.target q.value q.timestamp q.input out] <+:
        (I.lang.sem p en r).events →
      Matches res.2 out ∨ out = .revert []
  /-- Every completed transaction of an affordable request, whatever its body
  does, is that request's, and reaches a listed world that is the next boundary. -/
  resumes : ∀ x en h n t (q : Request), I.lang.Allowed en → V.Boundary x en h n t →
    (I.session en).requests h n = some (.request q) → Funded F (I.session en) h q →
    let p := I.ofWorld x
    ∀ r, Good I r → ∀ (seg : List Event) (ev : Event), IsTx ev →
      (∀ y ∈ seg, ¬ IsTx y) → h ++ seg ++ [ev] <+: (I.lang.sem p en r).events →
      (∃ out, ev = Event.tx q.sender q.target q.value q.timestamp q.input out) ∧
      ∃ ω ∈ I.worlds p en r, V.Boundary x en (h ++ seg ++ [ev]) (n + 1) (V.typed ω)
  /-- **A deployment that never leaves its contract is the actual creation**: from
  the initial world of a compilation, funded by the opening balances, the selected
  contract's constructor, under the same conditions and with the deployment value
  covered by a deployer other than the new address, runs as `World.transact` of
  the actual `World.create` at the address `Fixed.createAddress` gives; it is the
  first event exactly when that completes, and on success the world it installs is
  the first boundary. At any admissible bound (resource failures included) its
  outcome if shown is that one or a revert with empty data and no address. -/
  deploys : ∀ (code : Code) (en : I.lang.Env) (k : Fin code.contracts.length)
      (body : Prog (code.catalog k) [] []),
    I.lang.Allowed en → k.val = code.main →
    code.ctor k (I.session en).deployArgs = some body → Prog.callsBack true body = false →
    let e := I.session en
    let p := I.ofWorld (V.initial code)
    let this := F.createAddress e.deployer e.deployNonce
    e.deployValue.val ≤ (e.balance e.deployer).val → this ≠ e.deployer →
    let frame := fun ext =>
      (ContractWorld.World.empty code.catalog (funds e.balance) code.roles).transact fun w =>
        w.create k (liftAddress this) body
          { sender := liftAddress e.deployer, mode := .ordinary (liftWord e.deployValue),
            ext := ext }
    let res := frame []
    (∀ ext, frame ext = res) →
    (Ends res.2 → ∃ out address, Observed I p en
      [Event.deploy e.deployer e.deployValue e.deployArgs out address]) ∧
    (∀ r, Good I r → (I.lang.sem p en r).events ≠ [] → ∃ out address,
      let done := Event.deploy e.deployer e.deployValue e.deployArgs out address
      [done] <+: (I.lang.sem p en r).events ∧
      match res.2 with
      | .ok _ => (∃ d, out = .success d) ∧ address = some this ∧
        ∃ t', t'.Shows code res.1 ∧ V.Boundary (V.initial code) en [done] 0 t'
      | .error h => RevertMatches h out ∧ address = none) ∧
    ∀ r, I.lang.Admissible r → ∀ out address,
      [Event.deploy e.deployer e.deployValue e.deployArgs out address] <+:
        (I.lang.sem p en r).events →
      (out = .revert [] ∧ address = none) ∨
      match res.2 with
      | .ok _ => (∃ d, out = .success d) ∧ address = some this
      | .error h => RevertMatches h out ∧ address = none

end IntrinsicSession

/-- For every fixed parameters there is a concrete intrinsic session semantics: an
`IntrinsicSpec` (exact session environment, pinned `Forward` and `Guard`, consistent
prefixes, by its type) whose worlds are actual typed contract worlds and whose
sessions satisfy `IntrinsicSession.Laws`. -/
@[goal Solidity.Semantics.IntrinsicSession.session_semantics_correct "is0-intrinsic-session"]
def intrinsicSessionSemantics : Prop :=
  ∀ F : Solidity.Roadmap.Fixed, ∃ (I : Solidity.Roadmap.IntrinsicSpec)
    (V : IntrinsicSession.View I), IntrinsicSession.Laws F I V

end Solidity.Goals
