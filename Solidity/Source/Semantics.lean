import Solidity.Source.Eval

/-!
# Constructors, transactions and sessions (S03.02, S03.04, S04.04, S05)

The source semantics composed into G01's interface
(`Solidity/Roadmap/Contracts.lean`):

- **Constructors** (S03.02).  `construct` runs a contract's state variable
  initializers and constructors along its C3 linearization in the pinned
  order of each pipeline.  Legacy: every initializer, most base first; the
  base-constructor arguments, derived to base (each in the parameters of
  the constructor that gives them); the constructor bodies, base to
  derived.  Via IR: the arguments first, then per contract, base to
  derived, its initializers and its body (solc's `ir-breaking-changes`,
  "order of state variable initialization"; recorded in
  `docs/solc-alignment.md`).
- **Deployment and transactions** (S04.04).  `deploy` creates the instance
  at the fixed creation address with nonce 1, its balance the deployment
  value and its code the contract's position, then constructs it; a revert
  undoes the creation.  `runTx` credits the request's value, dispatches
  the call data in a frame of depth 0, rolls back on a revert, ends the
  transaction (transient storage cleared, journal closed: `ExecState.endTx`)
  and records G01's `Event.tx`.  Events of the environment's moves inside
  a transaction (calls out, answers, callbacks, credits) are recorded as
  they happen (`Solidity/Source/Eval.lean`); logs are not observations.
- **Horizons** (S03.04).  `firstDone f n` is the least horizon `k ≤ n` at
  which `f k` completes, and its result.  It is monotone by construction
  (`firstDone_mono`), and an execution diverges exactly when no horizon
  completes (`firstDone_none_iff`).  No horizon is a semantic restriction:
  a finite execution completes at some horizon, a divergent one at none.
- **Sessions** (S05).  `sessionAt` runs the deployment and then the
  session environment's actions, each transaction at its least completing
  horizon up to `n`; it is G01's `Prefix` at horizon `n`, and the family is
  consistent (`sessionAt_consistent`), so `sourceLang` has the type of G01's
  `Lang Event Outcome`.  Its resources are horizons only: the failure points
  the user decisions require (any external frame or transaction may fail),
  the stipend rule and sender-funds validity are not modelled, a `stuck`
  run shows as an unfinished prefix (like divergence), and the events of a
  transaction that never completes are not shown.  Horizon independence of
  a completed result is checked on controls, not proved.
-/

namespace Solidity.Source

open Solidity.Roadmap (Address Word Bytes Event Outcome Pipeline Strategy Fixed Request Action
  SessionEnv Prefix Prefixes Lang)
open EM

variable {E : Env}

/-! ## Constructors -/

/-- Writing a state variable's initial value: a value, or a copy of the
contents. -/
def storeRV {Γ : RCtx} (F : Fr) (n : Nat) (τ : STy) (p : SPath) {σ : STy} (v : RVal E.layout σ) :
    EM E Γ Unit :=
  match v with
  | .val x => if τ.byRef then storeVal F n τ p x else writeAt F p x
  | .strLit bs => storeData F n τ p (Data.bytes (D := E.layout) (l := .memory) bs)
  | _ => halt (.stuck "initial value")

/-- A contract's initializers, in declaration order. -/
def runInits (G : Glob E) (F : Fr) (n : Nat) : List (RInit E) → EM E [] Unit
  | [] => pure ()
  | ri :: rest => do
    let (v, _) ← sub (L0 E) (evalE G F n ri.e)
    storeRV F n ri.τ ri.var.path v
    runInits G F n rest

/-- The constructor locals collected so far, by contract. -/
abbrev CtorLocals (G : Glob E) := List (Σ X : String, Locals E.layout (G.prog.ctorLocals X))

/-- The locals of contract `X`'s constructor: collected, or empty for a
constructor without parameters. -/
def ctorLocalsOf {Γ : RCtx} (G : Glob E) (acc : CtorLocals G) (X : String) :
    EM E Γ (Locals E.layout (G.prog.ctorLocals X)) :=
  match acc.find? (·.1 == X) with
  | some ⟨Y, l⟩ => if h : Y = X then pure (h ▸ l) else halt (.stuck "constructor locals")
  | none => if h : G.prog.ctorLocals X = [] then pure (h ▸ L0 E) else halt (.revert [])

/-- The arguments `X` gives its bases, evaluated in its constructor's
locals; bases already given arguments by a more derived contract keep them. -/
def giveArgs (G : Glob E) (F : Fr) (n : Nat) (X : String) (lX : Locals E.layout (G.prog.ctorLocals X)) :
    List (RBaseArg E (G.prog.ctorLocals X)) → CtorLocals G → EM E [] (CtorLocals G)
  | [], acc => pure acc
  | ba :: rest, acc => do
    if acc.any (·.1 == ba.base) then giveArgs G F n X lX rest acc
    else
      let (vs, _) ← sub lX (evalConvArgs G F n ba.args)
      let l := vs.onto (L0 E)
      if h : ba.ps.reverseAux [] = G.prog.ctorLocals ba.base then
        giveArgs G F n X lX rest (acc ++ [⟨ba.base, h ▸ l⟩])
      else halt (.stuck "base constructor arguments")

/-- Every base-constructor argument, derived to base. -/
def collectArgs (G : Glob E) (F : Fr) (n : Nat) : List String → CtorLocals G → EM E [] (CtorLocals G)
  | [], acc => pure acc
  | X :: Xs, acc => do
    let lX ← ctorLocalsOf G acc X
    collectArgs G F n Xs (← giveArgs G F n X lX (G.prog.baseArgs X) acc)

/-- Contract `X`'s constructor body, under its modifiers. -/
def runCtorBody (G : Glob E) (F : Fr) (n : Nat) (acc : CtorLocals G) (X : String) : EM E [] Unit := do
  match G.prog.ctor X with
  | none => pure ()
  | some b =>
    let lX ← ctorLocalsOf G acc X
    if h : G.prog.ctorLocals X = b.locals then
      let _ ← runMods G { F with contract := F.contract } n b b.mods (h ▸ lX)
      pure ()
    else halt (.stuck "constructor frame")

/-- **Construction** of contract `c` (its linearization `L`, most derived
first) from its constructor's locals, in the pipeline's order. -/
def construct (G : Glob E) (F : Fr) (n : Nat) (c : String) (lc : Locals E.layout (G.prog.ctorLocals c)) :
    EM E [] Unit := do
  let L := (E.linearize c).getD [c]
  match G.pipeline with
  | .legacy =>
    for X in L.reverse do runInits G F n (G.prog.inits X)
    let acc ← collectArgs G F n L [⟨c, lc⟩]
    for X in L.reverse do runCtorBody G F n acc X
  | .viaIR =>
    let acc ← collectArgs G F n L [⟨c, lc⟩]
    for X in L.reverse do
      runInits G F n (G.prog.inits X)
      runCtorBody G F n acc X

/-- The position of a contract in the compilation input. -/
def Glob.position (G : Glob E) (c : String) : Option Nat := G.prog.contracts.idxOf? c

/-- Whether contract `c`'s constructor is `payable` (without one, the
default constructor is not: solc reverts a deployment with value). -/
def Env.ctorPayable (E : Env) (c : String) : Bool :=
  match E.ctorDecl c with
  | some d =>
    match d.kind, d.top, d.node with
    | .constructor, _, .constructor _ _ pay _ _ => pay
    | _, _, _ => false
  | none => false

/-- **Deployment** of contract `c` at `addr` by `sender` with `value` and
ABI-encoded constructor arguments; its outcome. -/
def deploy (G : Glob E) (n : Nat) (c : String) (addr sender : Address) (value : Word) (args : Bytes) :
    EM E [] Outcome := do
  let m ← mark
  let old := ((← st).ex.world.accounts addr).balance.val
  if hb : old + value.val < 2 ^ 256 then
    modSt fun s => { s with ex := s.ex.apply (.account addr fun _ =>
      { balance := ⟨old + value.val, hb⟩, nonce := 1, code := none, storage := Storage.empty }) }
  else halt (.revert [])
  let F : Fr := { this := addr, sender := sender, value := value, static := false, contract := c }
  let ps := ((G.prog.ctor c).map RBody.ps).getD []
  let r ← attempt do
    if value.val ≠ 0 && !E.ctorPayable c then halt (.revert [])
    let vs ← lift (decodeVals E.layout args ps 0)
    let l := vs.onto (L0 E)
    if h : ps.reverseAux [] = G.prog.ctorLocals c then construct G F n c (h ▸ l)
    else halt (.stuck "constructor parameters")
  modSt fun s => { s with heap := Heap.empty }
  match r with
  | .ok () => do
    modSt fun s => { s with ex := s.ex.apply (.account addr fun x => { x with code := G.position c }) }
    pure (.success [])
  | .error (.revert d) => do rollbackTo m; pure (.revert d)
  | .error h => halt h

/-- **A transaction**: the value credited, the call data dispatched at
depth 0, rolled back on a revert; then the transaction ends (transient
storage cleared) and `Event.tx` records it. -/
def runTx (G : Glob E) (n : Nat) (q : Request) : EM E [] Outcome := do
  let G := { G with timestamp := q.timestamp }
  let m ← mark
  let out ← match ← instanceAt G q.target with
    | none => pure (Outcome.revert [])
    | some c =>
      let r ← attempt do
        credit q.target q.value
        let F : Fr := { this := q.target, sender := q.sender, value := q.value, static := false, contract := c }
        dispatch G F n q.input
      modSt fun s => { s with heap := Heap.empty }
      match r with
      | .ok d => pure (.success d)
      | .error (.revert d) => do rollbackTo m; pure (.revert d)
      | .error h => halt h
  modSt fun s => { s with ex := s.ex.endTx }
  emitEvent (.tx q.sender q.target q.value q.timestamp q.input out)
  pure out

/-! ## Horizons -/

/-- Whether a result completed (did not reach its horizon). -/
def Done {α σ : Type} (r : Except Halt α × σ) : Bool :=
  match r.1 with
  | .error .timeout => false
  | _ => true

/-- **The least horizon** `k ≤ n` at which `f k` completes, with its
result. -/
def firstDone {α σ : Type} (f : Nat → Except Halt α × σ) (n : Nat) : Option (Nat × (Except Halt α × σ)) :=
  (List.range (n + 1)).findSome? fun k => if Done (f k) then some (k, f k) else none

theorem range_succ_append (n m : Nat) : List.range (n + m + 1) = List.range (n + 1) ++ (List.range m).map (n + 1 + ·) := by
  rw [show n + m + 1 = (n + 1) + m by omega, List.range_add]

/-- **Monotone by construction**: a completion within horizon `n` is the
completion within every larger horizon. -/
theorem firstDone_mono {α σ : Type} (f : Nat → Except Halt α × σ) {n m : Nat} (hnm : n ≤ m)
    {x : Nat × (Except Halt α × σ)} (h : firstDone f n = some x) : firstDone f m = some x := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hnm
  simp only [firstDone] at h ⊢
  rw [range_succ_append, List.findSome?_append, h]
  rfl

/-- What `firstDone` finds completes, at a horizon within the bound. -/
theorem firstDone_spec {α σ : Type} {f : Nat → Except Halt α × σ} {n k : Nat} {r : Except Halt α × σ}
    (h : firstDone f n = some (k, r)) : k ≤ n ∧ r = f k ∧ Done (f k) = true := by
  simp only [firstDone] at h
  obtain ⟨j, hj, hx⟩ := List.exists_of_findSome?_eq_some h
  rw [List.mem_range] at hj
  by_cases hd : Done (f j) = true
  · simp only [hd, if_true, Option.some.injEq, Prod.mk.injEq] at hx
    obtain ⟨rfl, rfl⟩ := hx
    exact ⟨by omega, rfl, hd⟩
  · simp only [hd, Bool.false_eq_true, if_false, reduceCtorEq] at hx

/-- **Divergence**: no horizon completes exactly when every bound finds
nothing. -/
theorem firstDone_none_iff {α σ : Type} (f : Nat → Except Halt α × σ) :
    (∀ n, firstDone f n = none) ↔ ∀ k, Done (f k) = false := by
  constructor
  · intro h k
    cases hd : Done (f k)
    · rfl
    · have := h k
      simp only [firstDone, List.findSome?_eq_none_iff, List.mem_range] at this
      have e := this k (by omega)
      simp only [hd, if_true, reduceCtorEq] at e
  · intro h n
    simp only [firstDone, List.findSome?_eq_none_iff]
    intro k _
    simp only [h k, Bool.false_eq_true, if_false]

/-! ## Sessions -/

/-- **A program at the source**: the elaborated program, its pipeline, the
fixed parameters and the contract the session deploys. -/
structure SrcProg (E : Env) where
  prog : Program E
  pipeline : Pipeline
  fixed : Fixed
  main : String

/-- What every execution of a program in a session environment reads. -/
def SrcProg.glob (P : SrcProg E) (env : SessionEnv) : Glob E :=
  ⟨P.prog, P.pipeline, P.fixed, env.balance, env.hasCode, env.callee, ⟨0, by decide⟩⟩

/-- The state before the session: no instances. -/
def St.init (E : Env) : St E :=
  ⟨⟨⟨fun _ => Account.empty _⟩, Transient.empty, []⟩, Heap.empty, [], [], ⟨[], .nil⟩⟩

/-- A computation of the empty context run from a state, at horizon `k`. -/
def runAt {α : Type} (m : Nat → EM E [] α) (s : St E) (k : Nat) : Except Halt α × St E :=
  match (m k).run (L0 E, s) with
  | (r, (_, s')) => (r, s')

/-- **The session after the deployment**: up to `k` more actions of the
environment, each transaction at its least completing horizon up to `n`.
It ends when the environment has no more actions (the last outcome is the
final observation), at a transaction that completes within no horizon up
to `n`, or after `k` actions. -/
def sessionGo (P : SrcProg E) (env : SessionEnv) (n : Nat) : Nat → Nat → St E → Outcome →
    Prefix Event Outcome
  | 0, _, s, _ => ⟨s.events, none⟩
  | k + 1, i, s, last =>
    match env.requests s.events i with
    | none => ⟨s.events, some last⟩
    | some (.credit t v) =>
      let s' := (runAt (fun _ => do
        if (← instanceAt (P.glob env) t).isSome then credit t v) s 0).2
      sessionGo P env n k (i + 1) { s' with events := s.events ++ [.credit t v] } last
    | some (.request q) =>
      match firstDone (runAt (fun f => runTx (P.glob env) f q) s) n with
      | some (_, (.ok o, s')) =>
        sessionGo P env n k (i + 1) { s' with events := s.events ++ s'.events.drop s.events.length } o
      | _ => ⟨s.events, none⟩

theorem prefix_of_append_prefix {α : Type} {a b c : List α} (h : a ++ b <+: c) : a <+: c :=
  (List.prefix_append a b).trans h

/-- A session's events extend the events before it. -/
theorem sessionGo_extends_app (P : SrcProg E) (env : SessionEnv) (n : Nat) :
    ∀ k i (s : St E) last (xs ys : List Event), s.events = xs ++ ys →
      xs <+: (sessionGo P env n k i s last).events
  | 0, _, s, _, xs, ys, h => by
    show xs <+: s.events
    rw [h]; exact List.prefix_append _ _
  | k + 1, i, s, last, xs, ys, h => by
    simp only [sessionGo]
    split
    · show xs <+: s.events
      rw [h]; exact List.prefix_append _ _
    · exact sessionGo_extends_app P env n k _ _ _ xs (ys ++ _) (by simp only [h, List.append_assoc]; rfl)
    · split
      · exact sessionGo_extends_app P env n k _ _ _ xs (ys ++ _) (by simp only [h, List.append_assoc]; rfl)
      · show xs <+: s.events
        rw [h]; exact List.prefix_append _ _

theorem sessionGo_extends (P : SrcProg E) (env : SessionEnv) (n k i : Nat) (s : St E) (last : Outcome) :
    s.events <+: (sessionGo P env n k i s last).events :=
  sessionGo_extends_app P env n k i s last s.events [] (List.append_nil _).symm

/-- **Sessions are consistent**: a larger horizon (more transaction
horizon, more actions) extends the prefix, and a completed session stays
as it is. -/
theorem sessionGo_mono (P : SrcProg E) (env : SessionEnv) :
    ∀ k k' n n' i (s : St E) last, k ≤ k' → n ≤ n' →
      (sessionGo P env n k i s last).Le (sessionGo P env n' k' i s last)
  | 0, _, _, _, _, s, last, _, _ =>
    ⟨sessionGo_extends P env _ _ _ s last, .inl rfl⟩
  | k + 1, 0, _, _, _, _, _, h, _ => absurd h (by omega)
  | k + 1, k' + 1, n, n', i, s, last, hk, hn => by
    simp only [sessionGo]
    split
    · exact Prefix.Le.refl _
    · exact sessionGo_mono P env k k' n n' _ _ _ (by omega) hn
    · rename_i q _
      split
      · rename_i j o s' hf
        rw [firstDone_mono _ hn hf]
        exact sessionGo_mono P env k k' n n' _ _ _ (by omega) hn
      · exact ⟨by split <;> first | exact List.prefix_refl _ | exact sessionGo_extends_app P env _ _ _ _ _ _ _ rfl, .inl rfl⟩

/-- **A session at horizon `n`**: the deployment of the main contract at
its least completing horizon, then up to `n` actions. -/
def sessionFrom (P : SrcProg E) (env : SessionEnv) (addr : Address) (n : Nat) : Prefix Event Outcome :=
  let G := P.glob env
  let dep := fun f => do
    let o ← deploy G f P.main addr env.deployer env.deployValue env.deployArgs
    emitEvent (.deploy env.deployer env.deployValue env.deployArgs o
      (match o with | .success _ => some addr | .revert _ => none))
    pure o
  match firstDone (runAt dep (St.init E)) n with
  | some (_, (.ok o, s)) => sessionGo P env n n 0 s o
  | _ => ⟨[], none⟩

/-- The session at the deployment's creation address (`this` from the
deployment, G01). -/
def sessionAt (P : SrcProg E) (env : SessionEnv) (n : Nat) : Prefix Event Outcome :=
  sessionFrom P env (P.fixed.createAddress env.deployer env.deployNonce) n

/-- Sessions from any address are consistent. -/
theorem sessionFrom_consistent (P : SrcProg E) (env : SessionEnv) (addr : Address) :
    Prefixes.Consistent (sessionFrom P env addr) := by
  intro n m hnm
  simp only [sessionFrom]
  split
  · rename_i j o s hf
    rw [firstDone_mono _ hnm hf]
    exact sessionGo_mono P env n m n m 0 s o hnm hnm
  · exact ⟨List.nil_prefix, .inl rfl⟩

/-- **The source session semantics is consistent** (G01 `Prefixes.Consistent`). -/
theorem sessionAt_consistent (P : SrcProg E) (env : SessionEnv) :
    Prefixes.Consistent (sessionAt P env) :=
  sessionFrom_consistent P env _

/-- **The source language** (G01 `Lang Event Outcome`): programs at the
source, the session environment, horizons.  `Admissible`, `Forward` and
`Guard` are trivial: resource failures, the hash premise and the stipend
rule are not instantiated (see the module docstring). -/
def sourceLang (E : Env) : Lang Event Outcome where
  Prog := SrcProg E
  Env := SessionEnv
  Res := Nat
  resLE := inferInstance
  Allowed := SessionEnv.Allowed
  Admissible := fun _ => True
  sem := sessionAt
  consistent := sessionAt_consistent

end Solidity.Source
