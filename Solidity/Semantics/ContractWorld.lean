import Solidity.Semantics.Deploy

/-!
# Typed instances and atomic contract-world frames

This is an explicit execution interface, above the single-contract run. A
catalog indexes each instance's storage by its contract. Bodies and their
payable metadata are supplied by the model, as in Lifetime.System; this module
does not certify source lowering or replace the run's external-response table.

Fresh addresses are selected explicitly, checked for collision, and bounded
to 160 bits. All account balances are explicit. A frame commits storage and
settles the interpreter's net ledger only after successful execution. Failed
frames return no changed world. Creation catches enclose only the creation
frame, leaving argument evaluation and the successful continuation outside.

Linked library bodies are resolved at the caller's storage types and run with
the caller's identity, sender and value. The link's installed identity is
checked. Static frames conservatively accept empty-body observations only;
general computed view bodies require a future effect-certified interface.
-/

namespace Solidity.ContractWorld

abbrev Word := Semantics.Word

/-- An account address, bounded independently of the 256-bit value sort. -/
abbrev Address := { w : Word // w.1 < (2 : Int) ^ 160 }

/-- Refuse a word which cannot identify an account. -/
def Address.ofWord? (w : Word) : Option Address :=
  if h : w.1 < (2 : Int) ^ 160 then some ⟨w, h⟩ else none

/-- A typed contract reference is an address, not a proof of installed code.
As with a Solidity contract cast, every call still checks the actual catalog
identity. References can therefore survive a change of world. -/
structure Handle {K : Type} (k : K) where
  address : Address

/-- Code identity indexes the stored data; different contracts cannot share
an untyped storage object. -/
abbrev Account {K : Type} (contracts : K → Contract) :=
  (k : K) × Storage (contracts k)

/-- The source kind of installed code. It is fixed by the world's catalog. -/
inductive Role where
  | contractCode
  | libraryCode

/-- Global balances and typed per-instance persistent storage. Funding and
installed code in an initial world are explicit chain premises. -/
structure World {K : Type} (contracts : K → Contract) where
  accounts : Address → Option (Account contracts)
  funds : Address → Word
  timestamp : Word := PrimTy.dflt .uint
  roles : K → Role := fun _ => .contractCode

variable {K : Type} [DecidableEq K] {contracts : K → Contract}

/-- No deployed instances; externally supplied funding is still explicit. -/
def World.empty (contracts : K → Contract) (funds : Address → Word)
    (roles : K → Role := fun _ => .contractCode) : World contracts :=
  { accounts := fun _ => none, funds, roles }

/-- Library code is never an ordinary mutable contract entry. -/
def World.isLibrary (w : World contracts) (k : K) : Bool :=
  match w.roles k with
  | .contractCode => false
  | .libraryCode => true

/-- Arbitrary-address balance reads use the global account ledger. -/
def World.balance (w : World contracts) (a : Address) : Word := w.funds a

/-- Advance the common chain time between completed transactions. -/
def World.atTime (w : World contracts) (timestamp : Word) : World contracts :=
  { w with timestamp := timestamp }

/-- Read storage only after checking the instance's actual code identity. -/
def World.storage? (w : World contracts) {k : K} (r : Handle k) :
    Option (Storage (contracts k)) := do
  let ⟨j, st⟩ ← w.accounts r.address
  if h : j = k then some (h ▸ st) else none

/-- Sender, incoming value and explicitly assumed external responses.
Every frame in a world uses its common chain timestamp. -/
inductive Mode where
  | ordinary (payment : Word)
  | readOnly

/-- Read-only frames carry no payment, by construction. -/
structure Context where
  sender : Address
  mode : Mode := .ordinary (PrimTy.dflt .uint)
  ext : List (Semantics.ExtKey × Semantics.ExtResult) := []

/-- The incoming value retained by an ordinary or delegated frame. -/
def Context.value (ctx : Context) : Word :=
  match ctx.mode with
  | .ordinary value => value
  | .readOnly => PrimTy.dflt .uint

/-- Whether this frame inherits the static restriction. -/
def Context.isStatic (ctx : Context) : Bool :=
  match ctx.mode with
  | .ordinary _ => false
  | .readOnly => true

/-- Construct the actual typed transaction seen by the body. -/
def Context.tx (ctx : Context) (w : World contracts) (self : Address) : TTx :=
  { msgSender := ctx.sender.1, selfAddress := self.1, msgValue := ctx.value,
    timestamp := w.timestamp, ext := ctx.ext }

/-- Static observations can decode a value without executing a statement.
Nonempty programs are refused in static mode rather than assuming that their
final state equality proves the absence of attempted writes. -/
def emptyBody {C : Contract} {Γ Δ : Ctx} : Prog C Γ Δ → Bool
  | .nil => true
  | .cons _ _ => false

/-- An explicitly resolved entry, retaining the types of all result locals.
The decoder belongs to the caller and may fail after the frame succeeds. -/
structure Entry (C : Contract) (α : Type) where
  locals : Ctx
  body : Prog C [] locals
  result : State C locals → TRes α
  payable : Bool := false

/-- A closed method whose result is discarded. -/
def Entry.unit {C : Contract} (P : Prog C [] []) (payable : Bool := false) : Entry C Unit :=
  ⟨[], P, fun _ => .ok (), payable⟩

/-- A fresh paid frame. Self-calls still require funding but move no funds.
The ledger starts empty except for this frame's incoming payment. -/
def World.enter (w : World contracts) {k : K} (self : Address) (ctx : Context)
    (st : Storage (contracts k)) (payable : Bool) : TRes (State (contracts k) []) := do
  if ctx.value.1 > (w.funds ctx.sender).1 then .error .revert else do
    if (!payable || ctx.isStatic) && ctx.value.1 != 0 then .error .revert else do
      let balance ← TRes.ofOpt (PrimTy.ofInt? .uint
        ((w.funds self).1 + if ctx.sender = self then 0 else ctx.value.1))
      pure {
        storage := st, H := [], heap := Heap.empty, env := (), selfBalance := balance,
        net := if ctx.sender = self ∨ ctx.value.1 = 0 then [] else [(ctx.sender.1, ctx.value.1)],
        tx := ctx.tx w self }

/-- Apply the frame's finite net ledger to other accounts. A positive net
entry is a payment into the frame; a negative one is a receipt by that
account. The frame's own balance has already been computed by the run.
Repeated keys use the ledger's first-entry convention. Invalid address keys, unfunded debits and overflowing credits fail closed. -/
def settle (funds : Address → Word) (self : Address) (net : Ledger) : TRes (Address → Word) :=
  go funds [] net
where
  go (funds : Address → Word) (seen : List Word) : Ledger → TRes (Address → Word)
    | [] => .ok funds
    | (a, n) :: rest =>
      if a ∈ seen ∨ a = self.1 then go funds (a :: seen) rest else do
        let address ← TRes.ofOpt (Address.ofWord? a)
        let balance ← TRes.ofOpt (PrimTy.ofInt? .uint ((funds address).1 - n))
        go (fun b => if b = address then balance else funds b) (a :: seen) rest

/-- Commit one successful frame, updating exactly its own typed storage.
Settlement cannot modify code or any other instance's storage: its result
type contains balances alone. -/
def World.finish (w : World contracts) {k : K} {Γ : Ctx} (self : Address)
    (σ : State (contracts k) Γ) : TRes (World contracts) := do
  let funds ← settle w.funds self σ.net
  pure { w with
    accounts := fun a => if a = self then some ⟨k, σ.storage⟩ else w.accounts a,
    funds := fun a => if a = self then σ.selfBalance else funds a }

/-- A commit's code/storage map changes only at the executing instance. -/
theorem World.finish_accounts {w t : World contracts} {k : K} {Γ : Ctx}
    {self : Address} {σ : State (contracts k) Γ} (run : w.finish self σ = .ok t) :
    t.accounts = fun a => if a = self then some ⟨k, σ.storage⟩ else w.accounts a := by
  unfold World.finish at run
  cases hs : settle w.funds self σ.net with
  | error e => simp only [hs, bind, Except.bind] at run; cases run
  | ok funds =>
    simp only [hs, bind, Except.bind] at run
    cases run
    rfl

/-- Independently addressed instances retain their storage after a commit. -/
theorem World.finish_other {w t : World contracts} {k : K} {Γ : Ctx}
    {self a : Address} {σ : State (contracts k) Γ} (run : w.finish self σ = .ok t)
    (different : a ≠ self) : t.accounts a = w.accounts a := by
  rw [World.finish_accounts run]
  exact if_neg different

/-- Ordinary creation: collision/funding checks, fresh initial storage,
constructor execution and payment settlement, followed by code installation.
The supplied closed body must include the source's base/field initializers. -/
private def World.deployFrame (w : World contracts) (k : K) (self : Address)
    (ctor : Prog (contracts k) [] []) (ctx : Context) :
    TRes (World contracts × Handle k) := do
  if (w.accounts self).isSome || decide (self = ctx.sender) || ctx.isStatic then .error .revert else do
    let σ ← w.enter self ctx (Storage.init (contracts k))
      (((contracts k).ctor.map (·.payable)).getD false)
    let o ← ctor.run σ
    let next ← w.finish self o.st
    pure (next, ⟨self⟩)

/-- Ordinary source creation cannot instantiate a library declaration. -/
def World.create (w : World contracts) (k : K) (self : Address)
    (ctor : Prog (contracts k) [] []) (ctx : Context) :
    TRes (World contracts × Handle k) :=
  if w.isLibrary k then .error .revert else w.deployFrame k self ctor ctx

/-- Deploy library code for a linked identity. Its implicit deployment cannot
have mutable fields, initializers or a user constructor. This is deployment
of a library declaration, not source-level new L(). -/
def World.deployLibrary (w : World contracts) (k : K) (self : Address) (ctx : Context) :
    TRes (World contracts × Handle k) :=
  if !w.isLibrary k || !(contracts k).vars.isEmpty || (contracts k).ctor.isSome ||
      !(contracts k).inits.isEmpty then .error .revert
  else w.deployFrame k self .nil ctx

/-- Execute the actual callee body against that instance's storage. -/
def World.callFrame (w : World contracts) {k : K} {α : Type} (r : Handle k)
    (entry : Entry (contracts k) α) (ctx : Context) :
    TRes (World contracts × State (contracts k) entry.locals) := do
  if w.isLibrary k || (ctx.isStatic && !(emptyBody entry.body)) then .error .revert else do
    let st ← TRes.ofOpt (w.storage? r)
    let σ ← w.enter r.address ctx st entry.payable
    let o ← entry.body.run σ
    let next ← w.finish r.address o.st
    pure (next, o.st)

/-- Every successful call frame contains an actual successful typed run,
with its paid entry and exact settlement exposed for correctness bridges. -/
theorem World.callFrame_ok {w next : World contracts} {k : K} {α : Type}
    {r : Handle k} {entry : Entry (contracts k) α} {ctx : Context}
    {result : State (contracts k) entry.locals}
    (run : w.callFrame r entry ctx = .ok (next, result)) :
    ∃ (st : Storage (contracts k)) (σ : State (contracts k) [])
      (o : Out (contracts k) σ.H entry.locals),
      w.storage? r = some st ∧ w.enter r.address ctx st entry.payable = .ok σ ∧
      entry.body.run σ = .ok o ∧ w.finish r.address o.st = .ok next ∧ o.st = result := by
  unfold World.callFrame at run
  split at run
  · cases run
  · cases hs : w.storage? r with
    | none => simp only [hs, TRes.ofOpt, bind, Except.bind] at run; cases run
    | some st =>
      simp only [hs, TRes.ofOpt, bind, Except.bind] at run
      cases he : w.enter r.address ctx st entry.payable with
      | error e => simp only [he, bind, Except.bind] at run; cases run
      | ok σ =>
        simp only [he, bind, Except.bind] at run
        cases hr : entry.body.run σ with
        | error e => simp only [hr] at run; cases run
        | ok o =>
          simp only [hr] at run
          cases hf : w.finish r.address o.st with
          | error e => simp only [hf, bind, Except.bind] at run; cases run
          | ok final =>
            simp only [hf, bind, Except.bind] at run
            have eq : (final, o.st) = (next, result) := Except.ok.inj run
            exact ⟨st, σ, o, rfl, he, hr,
              hf.trans (congrArg (fun x => Except.ok x) (congrArg Prod.fst eq)),
              congrArg Prod.snd eq⟩

/-- Creation success witnesses the constructor run from fresh typed storage,
not merely an oracle reply or a default deployed account. -/
private theorem World.deployFrame_ok {w next : World contracts} {k : K} {self : Address}
    {ctor : Prog (contracts k) [] []} {ctx : Context} {reference : Handle k}
    (run : w.deployFrame k self ctor ctx = .ok (next, reference)) :
    ∃ (σ : State (contracts k) []) (o : Out (contracts k) σ.H []),
      w.enter self ctx (Storage.init (contracts k))
        (((contracts k).ctor.map (·.payable)).getD false) = .ok σ ∧
      ctor.run σ = .ok o ∧ w.finish self o.st = .ok next ∧ reference.address = self := by
  unfold World.deployFrame at run
  split at run
  · cases run
  · cases he : w.enter self ctx (Storage.init (contracts k))
        (((contracts k).ctor.map (·.payable)).getD false) with
    | error e => simp only [he, bind, Except.bind] at run; cases run
    | ok σ =>
      simp only [he, bind, Except.bind] at run
      cases hr : ctor.run σ with
      | error e => simp only [hr] at run; cases run
      | ok o =>
        simp only [hr] at run
        cases hf : w.finish self o.st with
        | error e => simp only [hf, bind, Except.bind] at run; cases run
        | ok final =>
          simp only [hf, bind, Except.bind] at run
          have eq : (final, (⟨self⟩ : Handle k)) = (next, reference) := Except.ok.inj run
          exact ⟨σ, o, rfl, hr,
            hf.trans (congrArg (fun x => Except.ok x) (congrArg Prod.fst eq)),
            (congrArg Handle.address (congrArg Prod.snd eq)).symm⟩

/-- Successful ordinary creation retains the actual constructor witness. -/
theorem World.create_ok {w next : World contracts} {k : K} {self : Address}
    {ctor : Prog (contracts k) [] []} {ctx : Context} {reference : Handle k}
    (run : w.create k self ctor ctx = .ok (next, reference)) :
    ∃ (σ : State (contracts k) []) (o : Out (contracts k) σ.H []),
      w.enter self ctx (Storage.init (contracts k))
        (((contracts k).ctor.map (·.payable)).getD false) = .ok σ ∧
      ctor.run σ = .ok o ∧ w.finish self o.st = .ok next ∧ reference.address = self := by
  unfold World.create at run
  split at run
  · cases run
  · exact World.deployFrame_ok run

/-- A successful constructor installs its own storage at its own code type. -/
theorem World.create_installs {w next : World contracts} {k : K} {self : Address}
    {ctor : Prog (contracts k) [] []} {ctx : Context} {reference : Handle k}
    (run : w.create k self ctor ctx = .ok (next, reference)) :
    ∃ st : Storage (contracts k), next.accounts reference.address = some ⟨k, st⟩ := by
  obtain ⟨σ, o, _, _, finish, address⟩ := World.create_ok run
  refine ⟨o.st.storage, ?_⟩
  rw [address, World.finish_accounts finish]
  exact if_pos rfl

/-- Caller-side return decoding happens after the callee's frame. Its failure
propagates; this operation contains no catch around the decoder. -/
def World.call (w : World contracts) {k : K} {α : Type} (r : Handle k)
    (entry : Entry (contracts k) α) (ctx : Context) : TRes (World contracts × α) := do
  let (next, σ) ← w.callFrame r entry ctx
  let result ← entry.result σ
  pure (next, result)

/-- An installed library identity and its body resolved at the caller's types.
Declaration-aware resolution and storage-parameter mapping are model
obligations, not consequences of matching an arbitrary address. -/
structure Library (contracts : K → Contract) (caller : K) (α : Type) where
  kind : K
  address : Address
  entry : Entry (contracts caller) α

/-- A linked body uses caller storage and identity, preserving the original
sender and value without charging an additional incoming payment. The
library's own storage and funds are never substituted for the caller's. -/
def World.libraryCall (w : World contracts) {caller : K} {α : Type}
    (r : Handle caller) (library : Library contracts caller α) (ctx : Context) :
    TRes (World contracts × α) := do
  if !w.isLibrary library.kind || w.isLibrary caller ||
      (ctx.isStatic && !(emptyBody library.entry.body)) then .error .revert else do
    let _ ← TRes.ofOpt (w.storage? (⟨library.address⟩ : Handle library.kind))
    let st ← TRes.ofOpt (w.storage? r)
    let σ : State (contracts caller) [] := {
      storage := st, H := [], heap := Heap.empty, env := (), net := [],
      selfBalance := w.funds r.address, tx := ctx.tx w r.address }
    let o ← library.entry.body.run σ
    let next ← w.finish r.address o.st
    let result ← library.entry.result o.st
    pure (next, result)

/-- Exactly the halts which a completed creation-frame catch can observe.
Mathematical divergence and model exhaustion do not become caught reverts. -/
def catchable : THalt → Bool
  | .revert | .revertWith _ | .panic => true
  | .diverge | .exhausted => false

/-- Run arguments before entering the catch boundary. Only the creation
frame is caught; a failure in either continuation propagates unchanged. -/
def World.tryCreate {α β : Type} (w : World contracts) (args : TRes α) (k : K)
    (target : α → Address) (ctor : α → Prog (contracts k) [] [])
    (context : α → Context)
    (success : World contracts → Handle k → TRes (World contracts × β))
    (caught : World contracts → THalt → TRes (World contracts × β)) :
    TRes (World contracts × β) := do
  let a ← args
  let ctx := context a
  if ctx.isStatic then .error .revert else
    match w.create k (target a) (ctor a) ctx with
    | .ok (next, reference) => success next reference
    | .error e => if catchable e then caught w e else .error e

/-- No constructor handler can intercept argument evaluation failures. -/
theorem World.tryCreate_argument_failure {α β : Type} (w : World contracts) (e : THalt)
    (k : K) (target : α → Address) (ctor : α → Prog (contracts k) [] [])
    (context : α → Context)
    (success : World contracts → Handle k → TRes (World contracts × β))
    (caught : World contracts → THalt → TRes (World contracts × β)) :
    w.tryCreate (.error e) k target ctor context success caught = .error e := rfl

/-- At a transaction boundary, a failure exposes exactly the original world.
Use completed-failure evidence separately when deriving a chain transition. -/
def atomic {α : Type} (w : World contracts)
    (run : TRes (World contracts × α)) : World contracts × TRes α :=
  match run with
  | .ok (next, result) => (next, .ok result)
  | .error e => (w, .error e)

/-- All writes and payments are rolled back together on failure. -/
theorem atomic_failure {α : Type} (w : World contracts) (e : THalt) :
    atomic w (.error e : TRes (World contracts × α)) = (w, .error e) := rfl

/-- Actual world operations, including an atomic sequence. Bodies still have
the explicit interface obligations of Entry and Library. -/
inductive Operation (contracts : K → Contract) where
  /-- A source context guard; it cannot choose or modify a world. -/
  | guard (condition : Bool)
  /-- A bare creation catch. Arguments precede the catch; only a completed
  creation failure is handled, by retaining the precreation world. -/
  | tryCreate {α : Type} (args : TRes α) (k : K) (target : α → Address)
      (ctor : α → Prog (contracts k) [] []) (context : α → Context)
  | create (k : K) (self : Address) (body : Prog (contracts k) [] []) (ctx : Context)
  | deployLibrary (k : K) (self : Address) (ctx : Context)
  | call (k : K) (reference : Handle k) (entry : Entry (contracts k) Unit) (ctx : Context)
  | libraryCall (k : K) (reference : Handle k) (library : Library contracts k Unit) (ctx : Context)
  | seq (first second : Operation contracts)

/-- Each operation runs the checked world frames; sequences expose no
intermediate world if their second operation fails. -/
def Operation.run : Operation contracts → World contracts → TRes (World contracts)
  | .guard condition, w => if condition then .ok w else .error .revert
  | .tryCreate args k target ctor context, w => do
    let (next, _) ← w.tryCreate args k target ctor context
      (fun next _ => .ok (next, ())) (fun before _ => .ok (before, ()))
    pure next
  | .create k self body ctx, w => do
    let (next, _) ← w.create k self body ctx
    pure next
  | .deployLibrary k self ctx, w => do
    let (next, _) ← w.deployLibrary k self ctx
    pure next
  | .call _ reference entry ctx, w => do
    let (next, _) ← w.call reference entry ctx
    pure next
  | .libraryCall _ reference library ctx, w => do
    let (next, _) ← w.libraryCall reference library ctx
    pure next
  | .seq first second, w => do
    let next ← first.run w
    second.run next

/-- A completed world transaction, with explicit chain/environment premises.
Rollback requires a completed failure; exhaustion never supplies a step. -/
inductive Step (allowed : World contracts → Operation contracts → Prop) :
    World contracts → World contracts → Prop where
  | commit {w next : World contracts} {op : Operation contracts}
      (admitted : allowed w op) (run : op.run w = .ok next) : Step allowed w next
  | rollback {w : World contracts} {op : Operation contracts} {e : THalt}
      (admitted : allowed w op) (run : op.run w = .error e)
      (completed : catchable e = true) : Step allowed w w
  | wait {w : World contracts} {timestamp : Word}
      (later : w.timestamp.1 ≤ timestamp.1) : Step allowed w (w.atTime timestamp)

/-- Starting with funded accounts and no code, every deployed instance is
introduced by a successful constructor frame, possibly within a sequence. -/
inductive Reachable (funding : Address → Word) (roles : K → Role)
    (allowed : World contracts → Operation contracts → Prop) : World contracts → Prop where
  | initial : Reachable funding roles allowed (World.empty contracts funding roles)
  | step {w next : World contracts} (before : Reachable funding roles allowed w)
      (run : Step allowed w next) : Reachable funding roles allowed next

/-- Transaction-reachable safety is distinct from validity on arbitrary typed
states. All constructor, call, linking and environment obligations are visible
in the transition premise. -/
theorem reachable_invariant {funding : Address → Word} {roles : K → Role}
    {allowed : World contracts → Operation contracts → Prop} {I : World contracts → Prop}
    (initial : I (World.empty contracts funding roles))
    (preserved : ∀ {w next}, I w → Step allowed w next → I next)
    {w : World contracts} (reached : Reachable funding roles allowed w) : I w := by
  induction reached with
  | initial => exact initial
  | step _ run ih => exact preserved ih run

end Solidity.ContractWorld
