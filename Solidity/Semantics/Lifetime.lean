import Solidity.Semantics.Deploy

/-!
# A contract's lifetime, from successful deployment

The interface is explicit: a model supplies constructor calls and a family of
external entry calls, elaborated at the contract's types. Only those calls
generate transitions. Persistent states forget the transaction's heap and
locals; entering a call creates them afresh and books its incoming payment.

This is the deterministic run's reading, not a realization of callback havoc.
Successful execution is required for a commit. Revert and panic roll back the
payment and all writes, while time may advance. Divergence and exhaustion have
no completed-call transition. Waiting is explicit, including stuttering.

`AG`, `EF` and `AGEF` are a small temporal interface over finite execution
witnesses, not a claim of universal eventual progress or a full CTL language.
-/

namespace Solidity.Lifetime

variable {C : Contract}

/-- What survives between transactions. The address is fixed, time can advance. -/
structure World (C : Contract) where
  storage : Storage C
  net : Ledger
  balance : PrimTy.uint.Denote
  address : PrimTy.uint.Denote
  timestamp : PrimTy.uint.Denote

/-- Discard the completed call's memory and locals. -/
def World.ofState {Γ : Ctx} (σ : State C Γ) : World C :=
  ⟨σ.storage, σ.net, σ.selfBalance, σ.tx.selfAddress, σ.tx.timestamp⟩

/-- Observe a persistent state without adding a payment or a caller's frame.
Predicates reading caller, value, oracle replies or memory are not persistent
predicates; use them in entry obligations instead. -/
def World.observe (s : World C) : State C [] :=
  { storage := s.storage, H := [], heap := Heap.empty, env := (), net := s.net,
    selfBalance := s.balance, tx := { selfAddress := s.address, timestamp := s.timestamp } }

/-- Waiting and failed transactions can advance time without changing funds. -/
def World.atTime (s : World C) (t : PrimTy.uint.Denote) : World C :=
  { s with timestamp := t }

/-- A fresh transaction frame, with its incoming value credited once.
Insufficient sender funds are an environment restriction: this model has no
ledger of the environment's spendable balances. -/
def World.enter (s : World C) (tx : TTx) : TRes (State C []) := do
  let balance ← TRes.ofOpt (PrimTy.ofInt? .uint (s.balance.1 + tx.msgValue.1))
  pure {
    storage := s.storage, H := [], heap := Heap.empty, env := (),
    net := if tx.msgValue.1 = 0 then s.net else
      Semantics.setBy tx.msgSender
        ((Semantics.lookupBy tx.msgSender s.net).getD 0 + tx.msgValue.1) s.net,
    selfBalance := balance, tx }

/-- Entering a transaction changes no storage. -/
theorem World.enter_storage {s : World C} {tx : TTx} {σ : State C []}
    (h : s.enter tx = .ok σ) : σ.storage = s.storage := by
  unfold World.enter at h
  cases hb : PrimTy.ofInt? .uint (s.balance.1 + tx.msgValue.1) with
  | none => simp only [hb, TRes.ofOpt, bind, Except.bind] at h; cases h
  | some balance =>
    simp only [hb, TRes.ofOpt, bind, Except.bind] at h
    cases h
    rfl

/-- A zero-value call recreates only the transaction's ephemeral frame. -/
theorem World.enter_zero (s : World C) (tx : TTx) (zero : tx.msgValue.1 = 0) :
    s.enter tx = .ok { s.observe with tx := tx } := by
  simp only [World.enter, zero, Int.add_zero, PrimTy.ofInt?, s.balance.2,
    dite_true, TRes.ofOpt, bind, Except.bind, if_true]
  rfl

/-- An external transaction keeps the deployed address and cannot go back in
time. Self-calls belong inside the program, not to top-level transactions. -/
def World.accepts (s : World C) (tx : TTx) : Prop :=
  tx.selfAddress = s.address ∧ s.timestamp.1 ≤ tx.timestamp.1 ∧ tx.msgSender ≠ s.address

/-- The explicitly admitted interface. `deploy` is `constructor(args);`,
`call` is an externally callable `f(args);`, each with its frame closed.
Visibility is not retained by `Contract`: selecting this interface is a model
obligation. `D` and `A` can carry typed constructor and function inputs.
Environment predicates restrict funding, callers, oracle replies, and time. -/
structure System (C : Contract) (D A : Type) where
  deploy : D → Prog C [] []
  call : A → Prog C [] []
  payable : A → Bool := fun _ => false
  allowDeploy : D → TTx → Prop := fun _ _ => True
  allowCall : World C → A → TTx → Prop := fun _ _ _ => True

variable {D A : Type}

/-- Run exactly one entry call. The result is committed only when it is `ok`. -/
def System.run (M : System C D A) (s : World C) (a : A) (tx : TTx) : TRes (World C) := do
  if !M.payable a && tx.msgValue.1 != 0 then .error .revert else do
    let σ ← s.enter tx
    let o ← (M.call a).run σ
    pure (World.ofState o.st)

/-- A successful call has a fresh entry frame and an actual successful run;
exhaustion is never a witness to this theorem. -/
theorem System.run_ok {M : System C D A} {s t : World C} {a : A} {tx : TTx}
    (h : M.run s a tx = .ok t) :
    ∃ (σ : State C []) (o : Out C σ.H []),
      s.enter tx = .ok σ ∧ (M.call a).run σ = .ok o ∧ World.ofState o.st = t := by
  unfold System.run at h
  split at h
  · cases h
  · cases he : s.enter tx with
    | error e => simp only [he, bind, Except.bind] at h; cases h
    | ok σ =>
      simp only [he, bind, Except.bind] at h
      cases hr : (M.call a).run σ with
      | error e => simp only [hr] at h; cases h
      | ok o =>
        simp only [hr] at h
        exact ⟨σ, o, rfl, hr, Except.ok.inj h⟩

/-- Successful deployment alone initializes the lifetime; neither a default
storage nor an exhausted constructor is an initial deployed state. -/
def System.Init (M : System C D A) (s : World C) : Prop :=
  ∃ d tx σ, M.allowDeploy d tx ∧ C.deployT (M.deploy d) tx = .ok σ ∧ World.ofState σ = s

/-- Observable actions include inactivity, so progress cannot follow merely
from deleting executions where nobody calls the contract. -/
inductive Event (A : Type) where
  | call (action : A) (tx : TTx)
  | wait (timestamp : PrimTy.uint.Denote)

/-- A completed transaction either commits a successful run or rolls back a
revert/panic. Waiting keeps the persistent data and can leave time unchanged. -/
inductive Step (M : System C D A) : World C → Event A → World C → Prop where
  | commit {s t : World C} {a : A} {tx : TTx}
      (accepted : s.accepts tx) (allowed : M.allowCall s a tx)
      (run : M.run s a tx = .ok t) : Step M s (.call a tx) t
  | rollback {s : World C} {a : A} {tx : TTx} {e : THalt}
      (accepted : s.accepts tx) (allowed : M.allowCall s a tx)
      (run : M.run s a tx = .error e)
      (failed : e = .revert ∨ (∃ data, e = .revertWith data) ∨ e = .panic) :
      Step M s (.call a tx) (s.atTime tx.timestamp)
  | wait {s : World C} {t : PrimTy.uint.Denote} (later : s.timestamp.1 ≤ t.1) :
      Step M s (.wait t) (s.atTime t)

/-- A finite, labelled execution. Every call link carries actual run evidence. -/
inductive Trace (M : System C D A) : World C → List (Event A) → World C → Prop where
  | nil (s : World C) : Trace M s [] s
  | cons {s t u : World C} {a : Event A} {as : List (Event A)}
      (step : Step M s a t) (rest : Trace M t as u) : Trace M s (a :: as) u

/-- Concatenate two checked executions. -/
theorem Trace.append {M : System C D A} {s t u : World C} {as bs : List (Event A)}
    (h : Trace M s as t) (k : Trace M t bs u) : Trace M s (as ++ bs) u :=
  match h with
  | .nil _ => k
  | .cons step rest => .cons step (rest.append k)

/-- Reachability is rooted at a successful constructor and closed only under
the explicit interface and waiting. -/
inductive Reachable (M : System C D A) : World C → Prop where
  | init {s : World C} (deployed : M.Init s) : Reachable M s
  | step {s t : World C} {a : Event A} (before : Reachable M s)
      (next : Step M s a t) : Reachable M t

/-- A finite continuation of a reached state remains reachable. -/
theorem Trace.reachable {M : System C D A} {s t : World C} {as : List (Event A)}
    (h : Trace M s as t) (hs : Reachable M s) : Reachable M t :=
  match h with
  | .nil _ => hs
  | .cons step rest => rest.reachable (.step hs step)

/-- Every reached state has a finite execution witness from deployment. -/
theorem Reachable.trace {M : System C D A} {t : World C} (h : Reachable M t) :
    ∃ s as, M.Init s ∧ Trace M s as t :=
  match h with
  | .init hs => ⟨_, [], hs, .nil _⟩
  | .step before next =>
    let ⟨s, as, hs, path⟩ := before.trace
    ⟨s, as ++ [_], hs, path.append (.cons next (.nil _))⟩

/-- Reachability and a finite deployment-rooted trace describe the same states. -/
theorem reachable_iff_trace {M : System C D A} {t : World C} :
    Reachable M t ↔ ∃ s as, M.Init s ∧ Trace M s as t :=
  ⟨Reachable.trace, fun ⟨_, _, hs, path⟩ => path.reachable (.init hs)⟩

/-- Always: the predicate holds at every state reachable after deployment. -/
def AG (M : System C D A) (P : World C → Prop) : Prop :=
  ∀ s, Reachable M s → P s

/-- Possible eventual reachability from a specified state, including zero steps. -/
def CanReach (M : System C D A) (s : World C) (P : World C → Prop) : Prop :=
  ∃ as t, Trace M s as t ∧ P t

/-- A target that holds now needs no transaction. -/
theorem CanReach.here {M : System C D A} {s : World C} {P : World C → Prop}
    (h : P s) : CanReach M s P := ⟨[], s, .nil s, h⟩

/-- Prepend an admitted action to a finite target witness. -/
theorem CanReach.next {M : System C D A} {s t : World C} {a : Event A}
    {P : World C → Prop} (step : Step M s a t) (h : CanReach M t P) : CanReach M s P :=
  let ⟨as, u, path, hu⟩ := h
  ⟨a :: as, u, .cons step path, hu⟩

/-- Possible eventually: some successful deployment has a finite target trace. -/
def EF (M : System C D A) (P : World C → Prop) : Prop :=
  ∃ s, M.Init s ∧ CanReach M s P

/-- From every reached state a target remains reachable; this does not require
any participant actually to take that continuation. -/
def AGEF (M : System C D A) (P : World C → Prop) : Prop :=
  AG M (fun s => CanReach M s P)

/-- Constructor establishment and preservation by every admitted transition. -/
structure Invariant (M : System C D A) (I : World C → Prop) : Prop where
  initially : ∀ s, M.Init s → I s
  preserved : ∀ {s t a}, I s → Step M s a t → I t

/-- An inductive invariant holds throughout the deployed contract's lifetime. -/
theorem Invariant.always {M : System C D A} {I : World C → Prop}
    (h : Invariant M I) : AG M I :=
  fun _ reached => go reached
where
  go {s : World C} (reached : Reachable M s) : I s :=
    match reached with
    | .init deployed => h.initially _ deployed
    | .step before next => h.preserved (go before) next

/-- Exclude a bad state using an invariant stronger than its negation. -/
theorem Invariant.never {M : System C D A} {I Bad : World C → Prop}
    (h : Invariant M I) (safe : ∀ s, I s → ¬ Bad s) : AG M (fun s => ¬ Bad s) :=
  fun s reached => safe s (h.always s reached)

/-- Establish an invariant from successful constructor/call runs and stability
under advancing time. Rollback needs no separate storage or payment proof. -/
theorem Invariant.ofRuns {M : System C D A} {I : World C → Prop}
    (deploy : ∀ d tx σ, M.allowDeploy d tx →
      C.deployT (M.deploy d) tx = .ok σ → I (World.ofState σ))
    (commit : ∀ s a tx t, s.accepts tx → M.allowCall s a tx → I s →
      M.run s a tx = .ok t → I t)
    (time : ∀ s t, s.timestamp.1 ≤ t.1 → I s → I (s.atTime t)) : Invariant M I where
  initially := fun _ ⟨d, tx, σ, allowed, run, eq⟩ => eq ▸ deploy d tx σ allowed run
  preserved := fun hi step => match step with
    | .commit accepted allowed run => commit _ _ _ _ accepted allowed hi run
    | .rollback accepted _ _ _ => time _ _ accepted.2.1 hi
    | .wait later => time _ _ later hi

/-- A target witness names a genuinely reached state. -/
theorem EF.reachable {M : System C D A} {P : World C → Prop} (h : EF M P) :
    ∃ t, Reachable M t ∧ P t :=
  let ⟨_, hs, _, t, path, ht⟩ := h
  ⟨t, path.reachable (.init hs), ht⟩

/-- Possible eventually is exactly a reachable target, not an exhausted run. -/
theorem ef_iff_reachable {M : System C D A} {P : World C → Prop} :
    EF M P ↔ ∃ t, Reachable M t ∧ P t :=
  ⟨EF.reachable, fun ⟨_, ht, hp⟩ =>
    let ⟨s, as, hs, path⟩ := ht.trace
    ⟨s, hs, as, _, path, hp⟩⟩

/-- A safety theorem rules out every finite witness to a bad state. -/
theorem AG.not_EF {M : System C D A} {P : World C → Prop}
    (h : AG M (fun s => ¬ P s)) : ¬ EF M P :=
  fun witness => let ⟨t, ht, hp⟩ := witness.reachable; h t ht hp

end Solidity.Lifetime
