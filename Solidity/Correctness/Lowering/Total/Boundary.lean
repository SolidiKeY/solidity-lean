import Solidity.Correctness.Lowering.Total.Main
import Solidity.Correctness.Lowering.Total.Spells
import Solidity.Source.Agreement.Locals

/-!
# Loop lowering: the concrete boundary (e2b-loops-producer)

The concrete boundary is begun here, not finished:

* `Decode.decode` is the raw-to-Source decoder (stage 1): canonical Source
  spelling, then the existing Source inference and resolution. It is defined
  on top-level requests outside `unchecked`/`checked` scopes, over primitive
  full-width locals and state variables: expressions, simple statements,
  branches, blocks, `unchecked` and the loops. Elsewhere it is `none`, a
  coverage gap. Its spellings are choices; none is proved to agree with the
  model elaborator.
* `loopEntry` admits every request whose lowering, elaboration and placement
  all succeed. A request whose lowering succeeds but whose elaboration or
  placement fails is not admitted: at top level it still has `LowersTo`
  (`Request.lowers`), as a callee nothing is stated of it.
* `loopAssociated` is `Spells` (H1024): an inductive spelling relation and
  Source typing derivations, not the decoder. `decode_spells` proves the
  decoder sound for it and `Spells.decode` complete if Source inference is
  complete (`InferComplete`, not proved in the Source front end). `Spells`
  shares the decoder's small tables, so those rest on review.
* `loopBoundary_fullDomain` and `loopResidual_iff` state what is left once
  admission and association are fixed.
* `Observe.source`/`Observe.target` are the observation policies (H1021): no
  events, the kind of the outcome at the first completing horizon, on the
  admitted Source executions only (`Observe.Admitted`, H1033).
* `Simulation.Simulates rel` is `relates` (H1022): one general simulation,
  which the e1 endpoints imply (`of_endpoint`, `of_retEndpoint`).
  It is relative to a state relation `rel`.
* `Allocation.trace` is the allocation trace (H1023): one scope per run.
* `loopBoundaryAt rel` assembles them with `rel` unbound. For a `rel` that
  reflects Booleans and relates `false` to `false`, `loopResidualAt_iff` gives
  the four obligations left and the two family obligations follow. No such
  `rel` is required to be non-degenerate by these two hypotheses.
* `loopRel` is the stage-1 state relation (Q-9 answer): primitive values,
  primitive state variables of the running account, `msg.value` and the
  timestamp; the rest of the state is unrelated. `loopBoundaryStage1` is the
  boundary at it, a closed term, with `loopResidualStage1_iff`.

`Simulation.Bound` and `Simulation.InitialMatching` (H1035) bind the
simulation to the request's positional map and ask total matching, beside the
contract; `LowerLoopsCorrectContractV2` is version 1 with both. The allocation
trace carries the fresh-name round-trip law `Allocation.RoundTrip` (H1036).

Each of the three choices has known defects, listed at its section: the
policies observe the outcome kind only and cannot tie `PassCorrect` to the
state relation, the
simulation can hold vacuously, and the allocation trace is incomplete. The
boundary is therefore not ready to carry the goal.

Not proved, and partly not provable yet: the fields `allocation` and `pipeline`
take as hypothesis a successful run of `elabStmtsP` and, for a callee, of
`calleeBody`, which runs `renameStmts`, `lowerReturns` and `wrapMods`. All four
are `partial`, so opaque to the kernel: the hypothesis says nothing about the
elaborated program, and no request's `Request.Succeeds` can be derived (it can
be refuted where top-level lowering, which is total, fails). So the decoder's
coverage obligation cannot be proved today; once the elaborator is total it
fails on the first successful request in a listed gap. Also not proved:
`InferComplete`, and that `loopRel` has any related pair. `Solidity.Goals.lowerLoopsCorrect`
stays unstated until the boundary is complete.
-/
namespace Solidity.Correctness.Lowering.Total

open Solidity.Roadmap.G49Final

/-! ## The observation policies (H1021)

No events; the outcome at the first horizon that completes. Only the kind of an
outcome is observed (success or failure): no data, no events, no journal, no
state. Panic data cannot be compared (the intrinsic halt keeps no code); other
revert data is compared only in `Simulation.Final`. Event and journal
faithfulness is stated by no proposition in this file: it is dropped by these
policies, not yet exposed as an obligation.

The Source policy allows the admitted executions only (`Admitted`, H1033), the
same ones the simulation speaks of; every model state is allowed.

Known defects of this choice, open: a stuck Source run observes like a
diverging model run; an escaping `break` or `continue` observes as success;
and `PassCorrect` still needs a surjection from model states onto the admitted
Source executions. The frozen `PassCorrect` lets its prover choose that map,
and nothing here can tie it to the state relation, so the refinement conjunct
may be false for reasons unrelated to lowering (the admitted executions still
range over every Source global), or say little where true. This restriction is
accepted for now (H1255); tying the map to the state relation is deferred to a
later plan step, not dropped. -/
namespace Observe

open Solidity.Roadmap

/-- A Source result's outcome. A timeout has not completed; a stuck run (a
run-time type mismatch) never counts as completed. -/
def sourceOutcome {α : Type} : Source.R α → Option Outcome
  | .ok _ => some (.success [])
  | .error (.revert _) => some (.revert [])
  | .error (.stuck _) | .error .timeout => none

/-- A target result's outcome. Divergence and exhaustion do not complete. -/
def targetOutcome {α : Type} : TRes α → Option Outcome
  | .ok _ => some (.success [])
  | .error .revert | .error .panic | .error (.revertWith _) => some (.revert [])
  | .error .diverge | .error .exhausted => none

/-- The outcome at the first completing horizon up to `n`. -/
def first (f : Nat → Option Outcome) : Nat → Option Outcome
  | 0 => f 0
  | n + 1 => match first f n with
    | some o => some o
    | none => f (n + 1)

theorem first_succ_of_some {f : Nat → Option Outcome} {n : Nat} {o : Outcome}
    (e : first f n = some o) : first f (n + 1) = some o := by
  simp only [first, e]

theorem first_mono {f : Nat → Option Outcome} {n n' : Nat} {o : Outcome} (h : n ≤ n')
    (e : first f n = some o) : first f n' = some o := by
  induction h with
  | refl => exact e
  | step _ ih => exact first_succ_of_some ih

/-- A prefix with no events. -/
def silent (o : Option Outcome) : Prefix Event Outcome := ⟨[], o⟩

/-- First-completion observation is consistent with no fact about the
evaluator: once an outcome is seen it is kept. -/
theorem first_consistent (f : Nat → Option Outcome) :
    Prefixes.Consistent (fun n => silent (first f n)) := by
  intro n n' h
  refine ⟨List.prefix_refl _, ?_⟩
  cases e : first f n with
  | none => exact .inl (by simp only [silent, e])
  | some o => exact .inr (by simp only [silent, e, first_mono h e])

/-- **The admitted Source executions** (H1033): necessary conditions for a
model execution to stand for one. No failure plan and known calldata (the
model has neither), and a frame that may write and checks arithmetic (the
model always does). Static frames are thereby left out, also for programs
that write nothing: an exclusion of view executions, forced by the state
relation. An admitted execution may still have no related model state; that
is `Simulation.InitialMatching`. This is the part of "image of a model state"
that can be said of a Source execution alone: the policy of a Source program does not see the model
contract, context or state, so the abstraction itself is the state relation
of the simulation (`Simulation.Simulates`), which is stated over exactly
these executions. -/
def Admitted {s : SourceProgram} (e : SourceExecution s) : Prop :=
  e.plan = none ∧ e.calldataKnown = true ∧ e.frame.static = false ∧ e.frame.checked = true

/-- The Source policy: the first completing horizon of the actual run, on the
admitted executions. -/
def source (s : SourceProgram) :
    ObservationPolicy (fun e n => @SourceExecution.result s e n) where
  allowed := Admitted
  admissible _ := True
  forward _ _ := True
  guard _ _ := True
  observe _ n run := silent (first (fun m => sourceOutcome (run m).1) n)
  consistent _ := first_consistent _

/-- The target policy: the model run has no horizon, so every bound observes
its one result. -/
def target {C : Contract} {Γ : Ctx} (p : Blk C Γ) :
    ObservationPolicy (fun (e : State C Γ) (_ : Nat) => p.2.run e) where
  allowed _ := True
  admissible _ := True
  forward _ _ := True
  guard _ _ := True
  observe _ n run := silent (targetOutcome (run n))
  consistent _ := fun _ _ _ => Prefix.Le.refl _

end Observe

/-! ## The allocation trace (H1023)

One scope per request: the names listed by `protectedNames`, and as generated
the fresh-shaped spellings of the run whose index lies in the run's
fresh-counter interval. Callee-local rebinding and memo reuse get no scope of
their own. The trace is not complete, and both lists under-approximate:

* protected: binders the raw input declares but never reads, quantified
  invariant binders, a callee's parameters and modifiers unless in its
  locals, recursion and memo entries are missing;
* generated: only names read in the lowered output or live after elaboration
  are seen, so a temporary declared and never read, one that occurs only in
  the intrinsic program, and a memo-reused callee name below the interval
  are missing. The round-trip law on `FreshNames` (`RoundTrip`, H1036) is part
  of the trace, so a scheme whose `parse` never succeeds does not pass. -/
namespace Allocation

/-- Names in scope of the request: caller and callee locals, return slots,
state variables, enums, functions, a callee's renaming, names the scope marks
as user-supplied, and the names the raw input reads. -/
def protectedNames (r : Request) : List String :=
  r.input.before.locals.1.map Prod.fst ++
    (r.callee.map fun c => c.locals.map Prod.fst ++ c.names.map Prod.fst ++
      c.names.map Prod.snd ++ c.scope.map Prod.fst).getD [] ++
    r.input.returnSlots.getD [] ++
    r.contract.vars.map Prod.fst ++ r.contract.enums.map Prod.fst ++
    r.contract.funs.map Prod.fst ++
    r.input.scope.funs.map Prod.fst ++ r.input.scope.mutableFreshNames ++
    r.input.raw.flatMap RawStmt.names

/-- The fresh identifiers among `spellings` with index in `[lo, hi)`. -/
def generated (names : FreshNames) (lo hi : Nat) (spellings : List String) :
    List (String × Nat) :=
  spellings.filterMap fun s =>
    (names.parse s).filter fun id => decide (lo ≤ id.2) && decide (id.2 < hi)

/-- The one scope of a run, from the counter before lowering to the counter
after elaboration. -/
def scope (r : Request) (o : ProductionOutput) (after : Checker.Snapshot) : AllocationScope :=
  ⟨protectedNames r, generated r.input.names r.input.before.locals.2 after.locals.2
    (o.raw.flatMap RawStmt.names ++ after.locals.1.map Prod.fst)⟩

/-- The bases the lowering and the elaborator allocate fresh names under. -/
def bases : List String := ["se", "sp", "ie", "mv", "cnt", "brk", "first", "ret"]

/-- **The round-trip law** (H1036): a fresh identifier of an allocated base is
read back from its own spelling. `FreshNames` carries no such law; without it
the spelling based trace can be empty or wrong. It is an obligation of every
run, part of the trace below, not an assumption. It is stated for the
allocated bases only: no scheme in the repository reads back a name of an
arbitrary base. A request may carry any scheme, and admission does not look at
it, so for a successful request whose scheme breaks the law the allocation
obligation is false. This is kept as it is (H1066): the obligation stays
universal and cannot be discharged here for such schemes; a later step is to
make `FreshNames` carry the law. -/
def RoundTrip (names : FreshNames) : Prop :=
  ∀ base ∈ bases, ∀ index, names.parse (names.name base index) = some (base, index)

/-- The trace of a run is its one scope, under a fresh-name scheme that
round-trips. -/
def trace (r : Request) (o : ProductionOutput) (after : Checker.Snapshot)
    (_ : SProg r.contract) (_ : Blk r.contract r.context.ctx)
    (scopes : List AllocationScope) : Prop :=
  scopes = [scope r o after] ∧ RoundTrip r.input.names

end Allocation

/-! ## The general simulation (H1022)

One relation for every decoded program and its elaborated block, in place of
the e1 endpoints by cases. The e1 endpoints imply it (`of_endpoint`,
`of_retEndpoint`); they are stronger and are not recovered from it. It is
relative to a state relation `rel` (values and globals; `loopRel` below is the
stage-1 one). It speaks of
the admitted executions only (`Observe.Admitted`).

Known defects, open. `Simulates` alone can hold vacuously: its context maps
are chosen existentially, so a map between unrelatable types makes the premise
unsatisfiable, and a `glob` that is never true satisfies it. `Positional`,
`InitialMatching` and `Bound` (H1035) state the entry-map binding and the
initial totality that rule this out (with `Positional.unique`), as obligations
beside the contract; the final-context map stays free. Unlike the diagram of
`Goals/Shrink.lean` there is no integer reflection and no freshness clause. The return witness of the e1 return endpoint is not
kept: a Source `return` and a normal completion match the same model results. -/
namespace Simulation

/-- A Source/model state relation: values at each heap typing, and the
globals (the model state without its locals). -/
structure StateRelation (E : Source.Env) (C : Contract) where
  val : (H : HTy) → (τ : Source.STy) → (u : LTy) → Source.Val E.layout τ → u.TDenote C H → Prop
  glob : Source.Glob E → Source.Fr → Source.St E → State C [] → Prop

/-- Final matching of a Source result and a model result. Normal completion
relates the final locals through `m'`; a `return` relates the entry locals
through the block's context extension; both relate the globals. A revert keeps
its data, a panic only its kind (the intrinsic halt has no code). A Source
timeout matches model divergence. Nothing else matches: an escaping `break` or
`continue`, a stuck Source run, model exhaustion. -/
def Final {s : SourceProgram} {C : Contract} {Γ Δ : Ctx} {H : HTy}
    (rel : StateRelation s.env C) (m : Lowering.V07.ContextMap s.before Γ)
    (m' : Lowering.V07.ContextMap s.after Δ) (emb : Thin Γ Δ) (G : Source.Glob s.env)
    (F : Source.Fr) (src : SourceResult s) (tgt : TRes (Out C H Δ)) : Prop :=
  match src.1, tgt with
  | .ok (.normal ls), .ok o =>
    m'.Related (rel.val o.st.H) ls o.st.env ∧ rel.glob G F src.2.2 o.st.glob
  | .ok (.ret ls), .ok o =>
    (m.wk emb).Related (rel.val o.st.H) ls o.st.env ∧ rel.glob G F src.2.2 o.st.glob
  | .error (.revert d), .error h => h = THalt.ofData d ∨ (h = .panic ∧ ∃ c, d = Source.panicData c)
  | .error .timeout, .error .diverge => True
  | _, _ => False

/-- **The simulation.** From related states, at every horizon from some point
on, the Source result matches the model's one result. A Source run that times
out at every horizon is matched only by a diverging model run, so this is both
directions on related pairs only; it is not the backward half of `PassCorrect`.
Since model exhaustion, a stuck Source run and an escaping jump match nothing,
proving it means proving they do not occur from related states. -/
def SimulatesAt (rel : (E : Source.Env) → (C : Contract) → StateRelation E C)
    (s : SourceProgram) {C : Contract} {Γ : Ctx} (p : Blk C Γ)
    (m : Lowering.V07.ContextMap s.before Γ) (m' : Lowering.V07.ContextMap s.after p.1)
    (emb : Thin Γ p.1) : Prop :=
  ∀ (e : SourceExecution s) (tgt : State C Γ), Observe.Admitted e →
    m.Related ((rel s.env C).val tgt.H) e.initial.1 tgt.env →
    (rel s.env C).glob e.glob e.frame e.initial.2 tgt.glob →
    ∃ N, ∀ n,
      Final (rel s.env C) m m' emb e.glob e.frame (e.result (n + N)) (p.2.run tgt)

/-- The simulation at some context maps. This is `relates`: the frozen
interface gives it a Source program and a block only, with no request, names
or positions to bind the maps to (see `Bound` below). -/
def Simulates (rel : (E : Source.Env) → (C : Contract) → StateRelation E C)
    (s : SourceProgram) {C : Contract} {Γ : Ctx} (p : Blk C Γ) : Prop :=
  ∃ (m : Lowering.V07.ContextMap s.before Γ) (m' : Lowering.V07.ContextMap s.after p.1)
    (emb : Thin Γ p.1), SimulatesAt rel s p m m' emb

/-- A block of one statement runs as the statement, one horizon later. -/
theorem execItems_single {E : Source.Env} (G : Source.Glob E) (F : Source.Fr) (n nps : Nat)
    (ph : Option (Source.Ph E)) {R : List Source.STy} {M : Bool} {k : Source.SCtx}
    {Γ Γ' : Source.RCtx} (s : Source.RStmt E R M k Γ Γ') (l : Source.Locals E.layout Γ)
    (σ σ' : Source.Locals E.layout [] × Source.St E) (o : Source.Out E.layout Γ Γ')
    (h : (Source.execS G F n nps ph s l).run σ = (.ok o, σ')) :
    (Source.execItems G F (n + 1) nps ph (.stmt s .nil) l).run σ = (.ok o, σ') := by
  cases n with
  | zero => simp [Source.execS, Source.EM.halt] at h; cases h
  | succ n =>
    rw [Source.execItems]
    simp only [bind, ExceptT.bind, ExceptT.mk, ExceptT.run, StateT.bind, ExceptT.bindCont] at h ⊢
    rw [h]
    cases o <;> rfl

variable {rel : (E : Source.Env) → (C : Contract) → StateRelation E C}

/-- The e1 normal endpoint implies the simulation, for every state
relation that reflects Booleans and relates `false` to `false`. -/
theorem of_endpoint
    (reflect : ∀ E C H (v : Source.Val E.layout .bool) (b : Bool),
      (rel E C).val H .bool (.val .bool) v b → v = .bool b)
    (falseRel : ∀ E C H, (rel E C).val H .bool (.val .bool) (.bool false) false)
    {E : Source.Env} {srcΓ : Source.RCtx} {returns : List Source.STy} {M : Bool}
    {k : Source.SCtx} {C : Contract} {Γ Δ : Ctx}
    {statement : Source.RStmt E returns M k srcΓ srcΓ} {offset : Nat}
    {m : Lowering.V07.ContextMap srcΓ Γ} {program : Prog C Γ Δ} {emb : Thin Γ Δ}
    (h : Loops.Endpoint statement offset m program emb) :
    Simulates rel (SourceProgram.ofStmt statement) (⟨Δ, program⟩ : Blk C Γ) := by
  refine ⟨m, m.wk emb, emb, fun e tgt admitted related glob => ⟨offset + 1, fun n => ?_⟩⟩
  obtain ⟨plan, known, -, -⟩ := admitted
  obtain ⟨G, F, nps, ph, initial, plan', known'⟩ := e
  cases plan
  cases known
  obtain ⟨ls, out, run, target, post, same⟩ :=
    h G F n nps ph initial tgt (rel E C).val related (reflect E C) (falseRel E C)
  have step := execItems_single G F (n + offset) nps ph statement initial.1 _ _ _ run
  simp only [Final, SourceExecution.result, SourceProgram.ofStmt]
  rw [show n + (offset + 1) = n + offset + 1 from rfl, step, target]
  exact ⟨post, same ▸ glob⟩

/-- The e1 return endpoint implies the simulation as well. The returned flag
selects which matching case applies; its link to the model witness is dropped. -/
theorem of_retEndpoint
    (reflect : ∀ E C H (v : Source.Val E.layout .bool) (b : Bool),
      (rel E C).val H .bool (.val .bool) v b → v = .bool b)
    (falseRel : ∀ E C H, (rel E C).val H .bool (.val .bool) (.bool false) false)
    {E : Source.Env} {srcΓ : Source.RCtx} {M : Bool} {k : Source.SCtx} {C : Contract}
    {Γ Δ : Ctx} {statement : Source.RStmt E [] M k srcΓ srcΓ} {offset : Nat}
    {m : Lowering.V07.ContextMap srcΓ Γ} {program : Prog C Γ Δ} {emb : Thin Γ Δ}
    {witness : Idx Δ (.val .bool)}
    (h : Loops.RetEndpoint statement offset m program emb witness) :
    Simulates rel (SourceProgram.ofStmt statement) (⟨Δ, program⟩ : Blk C Γ) := by
  refine ⟨m, m.wk emb, emb, fun e tgt admitted related glob => ⟨offset + 1, fun n => ?_⟩⟩
  obtain ⟨plan, known, -, -⟩ := admitted
  obtain ⟨G, F, nps, ph, initial, plan', known'⟩ := e
  cases plan
  cases known
  obtain ⟨ls, returned, out, run, target, _, post, same⟩ :=
    h G F n nps ph initial tgt (rel E C).val related (reflect E C) (falseRel E C)
  have step := execItems_single G F (n + offset) nps ph statement initial.1 _ _ _ run
  simp only [Final, SourceExecution.result, SourceProgram.ofStmt]
  rw [show n + (offset + 1) = n + offset + 1 from rfl, step, target]
  cases returned <;> exact ⟨post, same ▸ glob⟩

/-- Negative control: a state relation whose globals are never related makes
every pair with some context maps simulate. So `Simulates` alone does not rule
out a degenerate `rel`; non-emptiness is the separate obligation
`InitialMatching` below. -/
theorem vacuous (empty : ∀ E C G F st σ, ¬ (rel E C).glob G F st σ) {s : SourceProgram}
    {C : Contract} {Γ : Ctx} (p : Blk C Γ) (m : Lowering.V07.ContextMap s.before Γ)
    (m' : Lowering.V07.ContextMap s.after p.1) (emb : Thin Γ p.1) : Simulates rel s p :=
  ⟨m, m', emb, fun _ _ _ _ glob => absurd glob (empty _ _ _ _ _ _)⟩

/-! ### The map bound to the request, and total initial matching (H1035)

The decoder reads the Source locals off the request's locals in order, so the
map a request names is the positional one: the i-th Source local is the i-th
model local. These two obligations bind the simulation to that map and ask
that every admitted Source execution has a related model state. They are
stated beside the contract, not inside `relates`: the frozen compatibility
fields quantify `relates` over every context map and every Source context of
the e1 families, including maps that are not positional and contexts with
unrelatable types. Total matching inside `relates` would make those fields
false; a positional map inside it would leave them underivable from the e1
theorems. Only the entry map is bound: the final-context map and the context
extension stay existential and are not tied to it. Positional identity also
assumes that Source lookup by spelling and model lookup by variable agree,
which is not stated here. That neither obligation follows from the contract
is not proved. -/

/-- The map sends each Source local to the model local at its position. -/
def Positional {srcΓ : Source.RCtx} {Γ : Ctx} (m : Lowering.V07.ContextMap srcΓ Γ) : Prop :=
  ∀ {τ : Source.STy} (i : Source.Idx srcΓ τ), (m.slot i).2.toNat = i.toNat

/-- A position determines the model local and its type. -/
theorem slot_eq_of_toNat : {Γ : Ctx} → {u v : LTy} → (i : Idx Γ u) → (j : Idx Γ v) →
    i.toNat = j.toNat → (⟨u, i⟩ : (u : LTy) × Idx Γ u) = ⟨v, j⟩
  | _, _, _, .here, .here, _ => rfl
  | _, _, _, .here, .there _, h => by cases h
  | _, _, _, .there _, .here, h => by cases h
  | _, _, _, .there i, .there j, h => by
      cases slot_eq_of_toNat i j (Nat.succ.inj h)
      rfl

/-- There is at most one positional map, so `InitialMatching` and `Bound`
speak of the same one. -/
theorem Positional.unique {srcΓ : Source.RCtx} {Γ : Ctx} {m n : Lowering.V07.ContextMap srcΓ Γ}
    (hm : Positional m) (hn : Positional n) : m = n :=
  Lowering.V07.ContextMap.ext m n fun i =>
    slot_eq_of_toNat (m.slot i).2 (n.slot i).2 ((hm i).trans (hn i).symm)

/-- **Total initial matching**: a successful decoded request has a positional
map under which every admitted Source execution has a related model state.
For `loopRel` the one component that can fail for a reason unrelated to
lowering is storage: the Source cell at each state variable's path must have
the declared type; that equation is proved (`Decode.unit_cellTy`), and so is
the whole obligation for `loopRel` (`initialMatching_loopRel`). -/
def InitialMatching (rel : (E : Source.Env) → (C : Contract) → StateRelation E C)
    (decode : Request → Option SourceProgram) : Prop :=
  ∀ (r : Request) (s : SourceProgram), r.Succeeds → decode r = some s →
    ∃ m : Lowering.V07.ContextMap s.before r.context.ctx, Positional m ∧
      ∀ e : SourceExecution s, Observe.Admitted e → ∃ tgt : State r.contract r.context.ctx,
        m.Related ((rel s.env r.contract).val tgt.H) e.initial.1 tgt.env ∧
        (rel s.env r.contract).glob e.glob e.frame e.initial.2 tgt.glob

/-- **The bound simulation**: every successful pipeline of a decoded request
simulates at a positional map. It implies the `relates` half of the pipeline
obligation (`Bound.simulates`); no converse is proved. -/
def Bound (rel : (E : Source.Env) → (C : Contract) → StateRelation E C)
    (decode : Request → Option SourceProgram) : Prop :=
  ∀ (r : Request) o after parts (program : Blk r.contract r.context.ctx) s, decode r = some s →
    r.pipeline o after parts program →
    ∃ m m' emb, Positional m ∧ SimulatesAt rel s program m m' emb

theorem Bound.simulates {decode : Request → Option SourceProgram} (h : Bound rel decode)
    {r : Request} {o after parts} {program : Blk r.contract r.context.ctx} {s : SourceProgram}
    (d : decode r = some s) (run : r.pipeline o after parts program) :
    Simulates rel s program :=
  (h r o after parts program s d run).elim fun m rest =>
    rest.elim fun m' rest => rest.elim fun emb at_ => ⟨m, m', emb, at_.2⟩

end Simulation

/-! ## The concrete state relation (stage 1)

The state relation of the fragment the stage-1 decoder covers. Values: a
primitive model value and the Source value of the corresponding type, by
`Source.Agreement.PrimitiveRel`; no other pair of types is related. Globals:
each primitive state variable holds related values in the model storage and
in the storage of the running Source account, at the canonical unit's path;
`msg.value` and the block timestamp agree; the Source frame is not static and
checks arithmetic. A contract with a state variable of any other type has no
related globals, as the decoder has no unit for it.

Not related, so unconstrained: memory heaps; the ledger, balances and
`selfBalance`; the caller and own address; external-call results (`tx.ext`);
transient storage; other accounts; the Source journal, events, logs, function
locals and resource metadata; the frame's contract, depth and calldata; and
all of the Source globals but the timestamp. No related pair is exhibited and
no total initial matching is proved: `Simulation.InitialMatching` states it,
and it needs the cell type at each path to equal the declared type. -/
namespace Relation

open Source.Agreement (sourceTy PrimitiveRel)

/-- Values: primitives at corresponding types. -/
def val (E : Source.Env) (C : Contract) (H : HTy) (τ : Source.STy) :
    (u : LTy) → Source.Val E.layout τ → u.TDenote C H → Prop
  | .val p, v, x => ∃ h : τ = sourceTy p, PrimitiveRel E.layout p (h ▸ v) x
  | _, _, _ => False

/-- One state variable: a primitive holds related values at its path. -/
def field {D : Source.Layout} (read : Source.SPath → Option ((τ : Source.STy) × Source.Val D τ))
    (x : Name) : {T : Ty} → SVal T → Prop
  | _, .prim (p := p) w =>
    ∃ v, read ⟨⟨some Decode.contractName, x⟩, []⟩ = some ⟨sourceTy p, v⟩ ∧ PrimitiveRel D p v w
  | _, _ => False

/-- Every state variable, in declaration order. -/
def fields {D : Source.Layout} (read : Source.SPath → Option ((τ : Source.STy) × Source.Val D τ)) :
    {fs : List (Name × Ty)} → SFields fs → Prop
  | _, .nil => True
  | _, .cons (f := x) v rest => field read x v ∧ fields read rest

/-- Globals: storage of the running account, `msg.value`, the timestamp, and a
Source frame that may write and checks arithmetic, as the model always does. -/
def glob (E : Source.Env) (C : Contract) (G : Source.Glob E) (F : Source.Fr) (st : Source.St E)
    (σ : State C []) : Prop :=
  fields (fun p => ((st.ex.world.accounts F.this).storage.read p).map fun v => ⟨_, v⟩) σ.storage ∧
  σ.tx.msgValue.1 = (F.value.val : Int) ∧ σ.tx.timestamp.1 = (G.timestamp.val : Int) ∧
  F.static = false ∧ F.checked = true

end Relation

/-- The value relation is total on primitives: every model primitive has a
related Source value. (Nothing of the kind is proved for globals.) -/
theorem Relation.val_total (E : Source.Env) (C : Contract) (H : HTy) (p : PrimTy)
    (x : p.Denote) :
    ∃ v, Relation.val E C H (Source.Agreement.sourceTy p) (.val p) v x :=
  ⟨Source.Agreement.ofModel E.layout p x, rfl, Source.Agreement.ofModel_related E.layout p x⟩

/-- The stage-1 state relation. -/
def loopRel (E : Source.Env) (C : Contract) : Simulation.StateRelation E C :=
  ⟨Relation.val E C, Relation.glob E C⟩

/-- It reflects Booleans. -/
theorem loopRel_reflect (E : Source.Env) (C : Contract) (H : HTy)
    (v : Source.Val E.layout .bool) (b : Bool)
    (h : (loopRel E C).val H .bool (.val .bool) v b) : v = .bool b := by
  obtain ⟨_, r⟩ := h
  cases r
  rfl

/-- It relates `false` to `false`. -/
theorem loopRel_false (E : Source.Env) (C : Contract) (H : HTy) :
    (loopRel E C).val H .bool (.val .bool) (.bool false) false :=
  ⟨rfl, .bool false⟩

/-! ## The storage cell types of the canonical unit

For the globals half of total initial matching: in the decoder's canonical
unit, the Source cell at the path of the state variable the model reads under
a name has the Source type of that primitive. This is the type equation the
storage clause of `loopRel` needs; it does not yet give a related pair of
states. -/
namespace Decode

/-- The declaration of a primitive state variable in the canonical unit. -/
def varDecl (x : Name) (T : Source.Syn .typeName) : Source.Decl :=
  ⟨.stateVar, x, some contractName, false, .stateVar T none none none false x .none⟩

/-- The canonical unit's declaration of the state variable the model reads
under the name `x`. -/
theorem stateVars_find (x : Name) (p : PrimTy) : (vars : List (Name × Ty)) →
    (parts : Source.Syn (.list (.part false))) → stateVars vars = some parts →
    Semantics.lookupBy x vars = some (.prim p) →
    ∃ T, stateTy (.prim p) = some T ∧
      (parts.collect (some contractName)).find?
        (fun d => d.kind == .stateVar && d.scope == some contractName && d.name == x) =
        some (varDecl x T)
  | [], _, _, hx => by cases hx
  | (y, U) :: rest, parts, h, hx => by
      simp only [stateVars, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff,
        Option.some.injEq] at h
      obtain ⟨T', hT, parts', hp, rfl⟩ := h
      simp only [Semantics.lookupBy] at hx
      by_cases e : x = y
      · subst e
        simp only [if_true, Option.some.injEq] at hx
        subst hx
        exact ⟨T', hT, by simp [Source.Syn.collect, varDecl]⟩
      · simp only [if_neg e] at hx
        obtain ⟨T, hT', found⟩ := stateVars_find x p rest parts' hp hx
        refine ⟨T, hT', ?_⟩
        have ne : (y == x) = false := by simpa using fun h => e h.symm
        simp [Source.Syn.collect, ne, found]

/-- **The cell type of a primitive state variable** in the canonical unit is
the Source type of the model primitive: the equation the state relation's
storage clause needs. -/
theorem unit_cellTy {C : Contract} {u : Source.Syn .unit} (h : unit C = some u) {x : Name}
    {p : PrimTy} (hx : Semantics.lookupBy x C.vars = some (.prim p)) :
    u.env.cellTy ⟨⟨some contractName, x⟩, []⟩ = Source.Agreement.sourceTy p := by
  unfold unit at h
  split at h
  · simp only [Option.map_eq_some_iff] at h
    obtain ⟨parts, hp, rfl⟩ := h
    obtain ⟨T, hT, found⟩ := stateVars_find x p C.vars parts hp hx
    have decl : (Source.Syn.unit (.cons (.contract false contractName .none .nil parts) .nil)).env.declOf
        .stateVar ⟨some contractName, x⟩ = some (varDecl x T) := by
      simp [Source.Env.declOf, Source.Syn.env, Source.Syn.decls, Source.Syn.collect, found]
    simp only [Source.Env.cellTy, Source.Env.pathTy, List.foldl_nil, Source.Env.rootTy, decl,
      Option.bind_some]
    cases p <;> (cases hT; rfl)
  · cases h

end Decode

/-! ## The locals half of total initial matching

A decoded request has the positional map, and under it every Source locals has
related model locals: the part of `Simulation.InitialMatching` that concerns
locals, proved for every decoded request. The globals part (storage cell
types, `msg.value`, the timestamp) stays open. -/
namespace Simulation

/-- The positional map of a list of primitive locals. -/
def primitiveMap : (ps : List PrimTy) → Lowering.V07.ContextMap (Source.Agreement.sourceContext ps) (Source.Agreement.modelContext ps)
  | [] => .empty
  | p :: ps => (primitiveMap ps).cons (Source.Agreement.sourceTy p) (.val p)

theorem primitiveMap_positional : (ps : List PrimTy) → Positional (primitiveMap ps)
  | [] => fun i => nomatch i
  | p :: ps => fun i => by
      cases i with
      | here => rfl
      | there j => exact congrArg (· + 1) (primitiveMap_positional ps j)

/-- Every Source value of a primitive's type is the image of a model value. -/
theorem val_onto (E : Source.Env) (C : Contract) (H : HTy) :
    (p : PrimTy) → (v : Source.Val E.layout (Source.Agreement.sourceTy p)) →
      ∃ x : p.Denote, Relation.val E C H (Source.Agreement.sourceTy p) (.val p) v x
  | .bool, .bool b => ⟨b, rfl, .bool b⟩
  | .uint, .int n h => ⟨⟨n, (Source.Agreement.uint_range n).mpr h⟩, rfl,
      Source.Agreement.PrimitiveRel.uint ⟨n, (Source.Agreement.uint_range n).mpr h⟩ h⟩
  | .int, .int n h => ⟨⟨n, (Source.Agreement.int_range n).mpr h⟩, rfl,
      Source.Agreement.PrimitiveRel.int ⟨n, (Source.Agreement.int_range n).mpr h⟩ h⟩

/-- Every Source locals of primitive types has related model locals. -/
theorem locals_onto (E : Source.Env) (C : Contract) (H : HTy) :
    (ps : List PrimTy) → (ls : Source.Locals E.layout (Source.Agreement.sourceContext ps)) →
      ∃ env : TEnv C H (Source.Agreement.modelContext ps),
        (primitiveMap ps).Related (Relation.val E C H) ls env
  | [], .nil => ⟨(), fun i => nomatch i⟩
  | p :: ps, .cons v rest => by
      obtain ⟨x, hx⟩ := val_onto E C H p v
      obtain ⟨env, henv⟩ := locals_onto E C H ps rest
      exact ⟨(x, env), Lowering.V07.ContextMap.related_cons _ _ _ _ henv _ _ _ _ hx⟩

/-- A decoded local is a model primitive at the corresponding Source type. -/
theorem localTy_some {t : LocalTy} {τ : Source.STy} (h : Decode.localTy t = some τ) :
    ∃ p : PrimTy, t.toLTy = .val p ∧ τ = Source.Agreement.sourceTy p := by
  cases t with
  | val p bits shape =>
    refine ⟨p, rfl, ?_⟩
    unfold Decode.localTy at h
    split at h <;> simp_all
  | _ => simp [Decode.localTy] at h

/-- The decoder's locals are primitive, position by position, on both sides. -/
theorem locals_primitive : (Γ : ECtx) → (L : List (String × Source.STy)) →
    Decode.locals Γ = some L →
    ∃ ps : List PrimTy, Source.tysOf L = Source.Agreement.sourceContext ps ∧
      ∀ names : FreshNames, (@ECtx.toNCtx names Γ).ctx = Source.Agreement.modelContext ps
  | [], L, h => by
      cases h
      exact ⟨[], rfl, fun _ => rfl⟩
  | (x, t) :: Γ, L, h => by
      simp only [Decode.locals, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff,
        Option.some.injEq] at h
      obtain ⟨τ, hτ, L', hL, rfl⟩ := h
      obtain ⟨ps, hs, hm⟩ := locals_primitive Γ L' hL
      obtain ⟨p, ht, rfl⟩ := localTy_some hτ
      exact ⟨p :: ps, congrArg (Source.Agreement.sourceTy p :: ·) hs, fun names => by
        change t.toLTy :: (@ECtx.toNCtx names Γ).ctx = _
        rw [ht, hm names]
        rfl⟩

/-- **The locals half of total initial matching.** A decoded request has a
positional map under which every Source locals has related model locals. -/
theorem decode_locals_matching {r : Request} {s : SourceProgram}
    (h : Decode.decode r = some s) :
    ∃ m : Lowering.V07.ContextMap s.before r.context.ctx, Positional m ∧
      ∀ (H : HTy) (ls : Source.Locals s.env.layout s.before),
        ∃ env : TEnv r.contract H r.context.ctx,
          m.Related (Relation.val s.env r.contract H) ls env := by
  obtain ⟨plain, C, L, b, L', d, _, hL, _, rfl⟩ := decode_spells h
  obtain ⟨contract, input, callee⟩ := r
  have none : callee = none := by
    simp only [Decode.plain, Bool.and_eq_true, Option.isNone_iff_eq_none] at plain
    exact plain.1.1.1
  subst none
  obtain ⟨ps, hs, hm⟩ := locals_primitive _ _ hL
  have key : ∀ {srcΓ : Source.RCtx} {Γ : Ctx}, srcΓ = Source.Agreement.sourceContext ps → Γ = Source.Agreement.modelContext ps →
      ∃ m : Lowering.V07.ContextMap srcΓ Γ, Positional m ∧
        ∀ (H : HTy) (ls : Source.Locals C.env.layout srcΓ),
          ∃ env : TEnv contract H Γ, m.Related (Relation.val C.env contract H) ls env := by
    intro srcΓ Γ e e'
    subst e e'
    exact ⟨primitiveMap ps, primitiveMap_positional ps, fun H ls => locals_onto _ _ H ps ls⟩
  exact key hs (hm input.names)

end Simulation

/-! ## Total initial matching, proved for the stage-1 relation

The globals half: a model storage related to the Source cells exists, because
every state variable of a decodable contract is primitive, its cell has the
primitive's Source type (`Decode.unit_cellTy`) and always reads a value. With
the locals half this proves `InitialMatching loopRel Decode.decode`. -/
namespace Simulation

/-- Every Source value of a primitive's type is the image of a model value. -/
theorem prim_onto (D : Source.Layout) : (p : PrimTy) → (v : Source.Val D (Source.Agreement.sourceTy p)) →
    ∃ w : p.Denote, Source.Agreement.PrimitiveRel D p v w
  | .bool, .bool b => ⟨b, .bool b⟩
  | .uint, .int n h => ⟨⟨n, (Source.Agreement.uint_range n).mpr h⟩,
      Source.Agreement.PrimitiveRel.uint ⟨n, (Source.Agreement.uint_range n).mpr h⟩ h⟩
  | .int, .int n h => ⟨⟨n, (Source.Agreement.int_range n).mpr h⟩,
      Source.Agreement.PrimitiveRel.int ⟨n, (Source.Agreement.int_range n).mpr h⟩ h⟩

/-- A model storage related to given Source reads exists when every state
variable is primitive and its cell reads at the primitive's Source type. -/
theorem fields_onto {D : Source.Layout}
    (read : Source.SPath → Option ((τ : Source.STy) × Source.Val D τ)) :
    (fs : List (Name × Ty)) →
    (∀ x T, (x, T) ∈ fs → ∃ p, T = .prim p ∧ ∃ v : Source.Val D (Source.Agreement.sourceTy p),
      read ⟨⟨some Decode.contractName, x⟩, []⟩ = some ⟨Source.Agreement.sourceTy p, v⟩) →
    ∃ st : SFields fs, Relation.fields read st
  | [], _ => ⟨.nil, trivial⟩
  | (x, T) :: fs, h => by
      obtain ⟨p, rfl, v, hv⟩ := h x T (List.mem_cons_self ..)
      obtain ⟨w, hw⟩ := prim_onto D p v
      obtain ⟨rest, hrest⟩ := fields_onto read fs fun y U m => h y U (List.mem_cons_of_mem _ m)
      exact ⟨.cons (.prim w) rest, ⟨v, hv, hw⟩, hrest⟩

/-- A binding of a list with distinct keys is the one its lookup finds. -/
theorem lookup_of_mem {α : Type} : (l : List (Name × α)) → Semantics.nodupKeysB l = true →
    ∀ x a, (x, a) ∈ l → Semantics.lookupBy x l = some a
  | [], _, _, _, m => nomatch m
  | (y, b) :: l, nd, x, a, m => by
      simp only [Semantics.nodupKeysB, Bool.and_eq_true, Option.isNone_iff_eq_none] at nd
      simp only [Semantics.lookupBy]
      rcases List.mem_cons.mp m with e | m'
      · cases e; simp
      · have := lookup_of_mem l nd.2 x a m'
        by_cases e : x = y
        · subst e; rw [nd.1] at this; cases this
        · simp [e, this]

/-- The decoder gives a unit only to contracts whose state variables are all
primitive. -/
theorem stateVars_prim : (vars : List (Name × Ty)) → (parts : Source.Syn (.list (.part false))) →
    Decode.stateVars vars = some parts → ∀ x T, (x, T) ∈ vars → ∃ p, T = .prim p
  | [], _, _, _, _, m => nomatch m
  | (y, U) :: rest, parts, h, x, T, m => by
      simp only [Decode.stateVars, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff,
        Option.some.injEq] at h
      obtain ⟨T', hT, parts', hp, _⟩ := h
      rcases List.mem_cons.mp m with e | m'
      · cases e
        unfold Decode.stateTy at hT
        split at hT <;> first | exact ⟨_, rfl⟩ | cases hT
      · exact stateVars_prim rest parts' hp x T m'

/-- A cell of a primitive's Source type always reads a value of that type. -/
theorem read_prim {D : Source.Layout} {L : Source.SPath → Source.STy} (s : Source.Storage D L)
    (path : Source.SPath) (p : PrimTy) (h : L path = Source.Agreement.sourceTy p) :
    ∃ v : Source.Val D (Source.Agreement.sourceTy p),
      ((s.read path).map fun v => (⟨_, v⟩ : (τ : Source.STy) × Source.Val D τ)) =
        some (⟨Source.Agreement.sourceTy p, v⟩ : (τ : Source.STy) × Source.Val D τ) := by
  have dflt : ∀ τ : Source.STy, τ = Source.Agreement.sourceTy p → (Source.Val.default D τ).isSome = true := by
    intro τ e
    subst e
    cases p <;> rfl
  have present : (s.read path).isSome = true := by
    unfold Source.Storage.read
    split
    · rfl
    · exact dflt _ h
  have key : ∀ (τ : Source.STy) (o : Option (Source.Val D τ)), τ = Source.Agreement.sourceTy p → o.isSome = true →
      ∃ v : Source.Val D (Source.Agreement.sourceTy p),
        (o.map fun v => (⟨τ, v⟩ : (τ : Source.STy) × Source.Val D τ)) = some (⟨Source.Agreement.sourceTy p, v⟩ : (τ : Source.STy) × Source.Val D τ) := by
    intro τ o e ok
    subst e
    obtain ⟨v, rfl⟩ := Option.isSome_iff_exists.mp ok
    exact ⟨v, rfl⟩
  exact key _ _ h present

/-- A `Word` as a model `uint`. -/
def wordDenote (w : Roadmap.Word) : PrimTy.uint.Denote :=
  ⟨w.val, by
    simp only [PrimTy.inRange, decide_eq_true_eq]
    exact ⟨Int.natCast_nonneg _, Int.ofNat_lt.mpr w.isLt⟩⟩

/-- **Total initial matching holds for the stage-1 state relation**: every
admitted Source execution of a successful decoded request has a related model
state under the positional map. So `loopRel` is not degenerate on decoded
requests, and the simulation premise is never vacuous there. -/
theorem initialMatching_loopRel : InitialMatching loopRel Decode.decode := by
  intro r s _ decoded
  obtain ⟨m, positional, locals⟩ := decode_locals_matching decoded
  refine ⟨m, positional, fun e admitted => ?_⟩
  obtain ⟨env, related⟩ := locals [] e.initial.1
  obtain ⟨plain, C, L, b, L', d, hC, _, _, rfl⟩ := decode_spells decoded
  simp only [Decode.context, Option.map_eq_some_iff] at hC
  obtain ⟨u, hu, rfl⟩ := hC
  have hu' := hu
  unfold Decode.unit at hu'
  split at hu'
  · simp only [Option.map_eq_some_iff] at hu'
    obtain ⟨parts, hparts, _⟩ := hu'
    obtain ⟨storage, hstorage⟩ := fields_onto
      (fun p => ((e.initial.2.ex.world.accounts e.frame.this).storage.read p).map fun v => ⟨_, v⟩)
      r.contract.vars fun x T mem => by
        obtain ⟨p, rfl⟩ := stateVars_prim _ _ hparts x T mem
        exact ⟨p, rfl, read_prim _ _ p
          (Decode.unit_cellTy hu (lookup_of_mem _ r.contract.vars_nodup x _ mem))⟩
    exact ⟨⟨storage, [], Heap.empty, env, [], PrimTy.dflt .uint,
        { msgValue := wordDenote e.frame.value, timestamp := wordDenote e.glob.timestamp }⟩,
      related, hstorage, rfl, rfl, admitted.2.2.1, admitted.2.2.2⟩
  · cases hu'

end Simulation

/-! ## The concrete boundary, as far as the decoder fixes it

Admission and association are fixed here: every request whose whole pipeline
succeeds is admitted (`loopEntry`), and a request is associated with the
programs it spells (`Spells`), so the `decoder` field is a real obligation:
soundness is `decode_spells`, completeness is left. `loopBoundary` takes the
policies, `relates` and the allocation trace as arguments, and
`loopResidual_iff` lists what is left for any choice of them. -/

/-- Admission: every request whose whole pipeline succeeds. -/
def loopEntry (r : Request) : Prop := r.Succeeds

/-- Association: the request spells the program (`Spells`, not the decoder). -/
def loopAssociated (r : Request) (s : SourceProgram) : Prop := Spells r s

/-- The reference interpretation at given observation policies. -/
def loopReference
    (source : (s : SourceProgram) → ObservationPolicy (fun e n => @SourceExecution.result s e n))
    (target : {C : Contract} → {Γ : Ctx} → (p : Blk C Γ) →
      ObservationPolicy (fun (e : State C Γ) (_ : Nat) => p.2.run e)) :
    RawSourceInterpretation :=
  ⟨loopAssociated, loopEntry, source, target⟩

/-- The boundary at given policies, state relation and allocation trace. -/
def loopBoundary
    (source : (s : SourceProgram) → ObservationPolicy (fun e n => @SourceExecution.result s e n))
    (target : {C : Contract} → {Γ : Ctx} → (p : Blk C Γ) →
      ObservationPolicy (fun (e : State C Γ) (_ : Nat) => p.2.run e))
    (relates : SourceProgram → {C : Contract} → {Γ : Ctx} → Blk C Γ → Prop)
    (allocations : (r : Request) → ProductionOutput → Checker.Snapshot → SProg r.contract →
      Blk r.contract r.context.ctx → List AllocationScope → Prop) : SemanticBoundary :=
  ⟨loopReference source target, relates, allocations⟩

/-- The boundary admits every request whose whole pipeline succeeds. -/
theorem loopBoundary_fullDomain {source target relates allocations} :
    FullDomain (loopBoundary source target relates allocations) := fun _ h => h

/-- **What is left at the concrete admission and association.** Decoder
soundness is a theorem, so the `decoder` field is its completeness on admitted
requests. Left: the decoder is defined on every successful request (not
provable for stage 1, which has gaps) and complete for `Spells` there; each
successful pipeline has a safe allocation trace, is related to its decoded
program and refines it; and `relates` holds of the e1 families. -/
theorem loopResidual_iff {source target relates allocations} :
    Residual (loopBoundary source target relates allocations) Decode.decode ↔
      (∀ r : Request, r.Succeeds → ∃ s, Decode.decode r = some s) ∧
      (∀ (r : Request) s, r.Succeeds → Spells r s → Decode.decode r = some s) ∧
      (∀ (r : Request) o after parts program, r.pipeline o after parts program →
        ∃ scopes, allocations r o after parts program scopes ∧
          ∀ scope ∈ scopes, SafeSpellings r.input.names scope.protectedNames scope.generated) ∧
      (∀ (r : Request) o after parts program s, Decode.decode r = some s →
        r.pipeline o after parts program →
        relates s program ∧
          Nonempty (PassCorrect (source s).behaviour (target program).behaviour)) ∧
      RelatesNormalFamily (loopBoundary source target relates allocations) ∧
      RelatesReturnFamily (loopBoundary source target relates allocations) := by
  constructor
  · intro h
    exact ⟨h.total, fun r s e spelled => (h.decoder r s e).mpr spelled,
      fun r o after parts program run =>
        h.allocation r o after parts program ⟨o, after, parts, program, run⟩ run,
      fun r o after parts program s d run =>
        h.pipeline r o after parts program s ⟨o, after, parts, program, run⟩ d run,
      h.normal, h.returns⟩
  · intro ⟨covered, complete, allocation, pipeline, normal, returns⟩
    exact ⟨covered, fun r s e => ⟨decode_spells, complete r s e⟩,
      fun r o after parts program _ run => allocation r o after parts program run,
      fun r o after parts program s _ d run => pipeline r o after parts program s d run,
      normal, returns⟩

/-! ## The boundary at a state relation

The policies (H1021), the simulation (H1022) and the allocation trace (H1023)
as chosen above, each with its listed defects; the state relation `rel` is
still an argument, so this is not yet a concrete boundary. -/

/-- The boundary with the state relation unbound. -/
def loopBoundaryAt (rel : (E : Source.Env) → (C : Contract) → Simulation.StateRelation E C) :
    SemanticBoundary :=
  loopBoundary Observe.source (fun p => Observe.target p)
    (fun s _ _ p => Simulation.Simulates rel s p) Allocation.trace

variable {rel : (E : Source.Env) → (C : Contract) → Simulation.StateRelation E C}

/-- The e1 normal family is related: derived from its endpoint theorem. -/
theorem loopBoundaryAt_normal
    (reflect : ∀ E C H (v : Source.Val E.layout .bool) (b : Bool),
      (rel E C).val H .bool (.val .bool) v b → v = .bool b)
    (falseRel : ∀ E C H, (rel E C).val H .bool (.val .bool) (.bool false) false) :
    RelatesNormalFamily (loopBoundaryAt rel) := by
  intro k E srcΓ returns M l u C Γ m pair extra names
  obtain ⟨embedding, endpoint⟩ := normalFamily_correct k (returns := returns) (M := M)
    (l := l) (u := u) m pair extra names (k.lowered pair extra names) rfl
  exact Simulation.of_endpoint reflect falseRel endpoint

/-- The e1 return family is related: derived from its endpoint theorem. -/
theorem loopBoundaryAt_returns
    (reflect : ∀ E C H (v : Source.Val E.layout .bool) (b : Bool),
      (rel E C).val H .bool (.val .bool) v b → v = .bool b)
    (falseRel : ∀ E C H, (rel E C).val H .bool (.val .bool) (.bool false) false) :
    RelatesReturnFamily (loopBoundaryAt rel) := by
  intro k E srcΓ M l u C Γ m pair extra names
  exact Simulation.of_retEndpoint reflect falseRel
    (returnFamily_correct k (M := M) (l := l) (u := u) m pair extra names)

/-- **What is left at the boundary**, for a state relation that reflects
Booleans and relates `false` to `false`: the decoder is defined on every
successful request and complete for `Spells` there; the fresh-name scheme
round-trips and the run's one allocation scope is safe; and each successful pipeline simulates its decoded program and
refines it under the policies. The two family obligations follow from the two
hypotheses on `rel` (`loopRel` has both). -/
theorem loopResidualAt_iff
    (reflect : ∀ E C H (v : Source.Val E.layout .bool) (b : Bool),
      (rel E C).val H .bool (.val .bool) v b → v = .bool b)
    (falseRel : ∀ E C H, (rel E C).val H .bool (.val .bool) (.bool false) false) :
    Residual (loopBoundaryAt rel) Decode.decode ↔
      (∀ r : Request, r.Succeeds → ∃ s, Decode.decode r = some s) ∧
      (∀ (r : Request) s, r.Succeeds → Spells r s → Decode.decode r = some s) ∧
      (∀ (r : Request) o after parts program, r.pipeline o after parts program →
        Allocation.RoundTrip r.input.names ∧
        SafeSpellings r.input.names (Allocation.scope r o after).protectedNames
          (Allocation.scope r o after).generated) ∧
      (∀ (r : Request) o after parts program s, Decode.decode r = some s →
        r.pipeline o after parts program →
        Simulation.Simulates rel s program ∧
          Nonempty (PassCorrect (Observe.source s).behaviour
            (Observe.target program).behaviour)) := by
  refine loopResidual_iff.trans ⟨fun ⟨covered, complete, allocation, pipeline, _, _⟩ =>
    ⟨covered, complete, fun r o after parts program run => ?_, pipeline⟩,
    fun ⟨covered, complete, allocation, pipeline⟩ =>
      ⟨covered, complete, fun r o after parts program run =>
        ⟨_, ⟨rfl, (allocation r o after parts program run).1⟩, fun scope member => ?_⟩, pipeline,
        loopBoundaryAt_normal reflect falseRel, loopBoundaryAt_returns reflect falseRel⟩⟩
  · obtain ⟨scopes, ⟨trace, law⟩, safe⟩ := allocation r o after parts program run
    cases trace
    exact ⟨law, safe _ (List.mem_singleton.mpr rfl)⟩
  · cases List.mem_singleton.mp member
    exact (allocation r o after parts program run).2

/-! ## The boundary at the stage-1 state relation

Every part is now a closed term. It is still not fit to carry the goal: the
defects listed at the policies, the simulation and the allocation trace
stand, the state relation leaves most of the state unrelated, and the decoder
has gaps. -/

/-- The stage-1 boundary. -/
def loopBoundaryStage1 : SemanticBoundary := loopBoundaryAt loopRel

/-- At the stage-1 boundary both family obligations are theorems, and four
obligations are left. -/
theorem loopResidualStage1_iff :
    Residual loopBoundaryStage1 Decode.decode ↔
      (∀ r : Request, r.Succeeds → ∃ s, Decode.decode r = some s) ∧
      (∀ (r : Request) s, r.Succeeds → Spells r s → Decode.decode r = some s) ∧
      (∀ (r : Request) o after parts program, r.pipeline o after parts program →
        Allocation.RoundTrip r.input.names ∧
        SafeSpellings r.input.names (Allocation.scope r o after).protectedNames
          (Allocation.scope r o after).generated) ∧
      (∀ (r : Request) o after parts program s, Decode.decode r = some s →
        r.pipeline o after parts program →
        Simulation.Simulates loopRel s program ∧
          Nonempty (PassCorrect (Observe.source s).behaviour
            (Observe.target program).behaviour)) :=
  loopResidualAt_iff loopRel_reflect loopRel_false

/-! ## The contract, version 2 (H1035, additive)

The frozen contract (`LowerLoopsCorrectContract`, version 1) together with the
two obligations it cannot carry: the request-bound simulation and total initial
matching. Version 1 is unchanged and is a conjunct of version 2. -/

/-- **Version 2 of the loop contract** at a state relation: version 1, and the
simulation bound to each request's positional map, and total initial matching.
Meant at `b := loopBoundaryAt rel`: for another boundary the two added
conjuncts speak of a relation that `b.relates` need not be. -/
def LowerLoopsCorrectContractV2
    (rel : (E : Source.Env) → (C : Contract) → Simulation.StateRelation E C)
    (b : SemanticBoundary) (i : RawSourceInterpretation)
    (decode : Request → Option SourceProgram) : Prop :=
  LowerLoopsCorrectContract b i decode ∧ Simulation.InitialMatching rel decode ∧
    Simulation.Bound rel decode

/-- Version 2 gives version 1: the bridge. The goal is to be stated against
version 1 as worded (H1256); version 2 counts only through this lemma. -/
theorem LowerLoopsCorrectContractV2.v1 {b : SemanticBoundary} {i : RawSourceInterpretation}
    {decode : Request → Option SourceProgram} (h : LowerLoopsCorrectContractV2 rel b i decode) :
    LowerLoopsCorrectContract b i decode := h.1

/-- **What version 2 asks at the stage-1 boundary.** The bound simulation
replaces the unbound one, so the pipeline obligation keeps only the refinement. -/
theorem loopContractV2Stage1_iff :
    LowerLoopsCorrectContractV2 loopRel loopBoundaryStage1 loopBoundaryStage1.reference
        Decode.decode ↔
      (∀ r : Request, r.Succeeds → ∃ s, Decode.decode r = some s) ∧
      (∀ (r : Request) s, r.Succeeds → Spells r s → Decode.decode r = some s) ∧
      (∀ (r : Request) o after parts program, r.pipeline o after parts program →
        Allocation.RoundTrip r.input.names ∧
        SafeSpellings r.input.names (Allocation.scope r o after).protectedNames
          (Allocation.scope r o after).generated) ∧
      (∀ (r : Request) o after parts program s, Decode.decode r = some s →
        r.pipeline o after parts program →
        Nonempty (PassCorrect (Observe.source s).behaviour (Observe.target program).behaviour)) ∧
      Simulation.InitialMatching loopRel Decode.decode ∧
      Simulation.Bound loopRel Decode.decode := by
  unfold LowerLoopsCorrectContractV2
  rw [contract_reference_iff, loopResidualStage1_iff]
  exact ⟨fun ⟨⟨covered, complete, allocation, pipeline⟩, matching, bound⟩ =>
      ⟨covered, complete, allocation,
        fun r o after parts program s d run => (pipeline r o after parts program s d run).2,
        matching, bound⟩,
    fun ⟨covered, complete, allocation, refines, matching, bound⟩ =>
      ⟨⟨covered, complete, allocation, fun r o after parts program s d run =>
        ⟨bound.simulates d run, refines r o after parts program s d run⟩⟩, matching, bound⟩⟩

/-- Version 2 at the stage-1 boundary with total initial matching discharged:
five obligations are left. -/
theorem loopContractV2Stage1_iff_open :
    LowerLoopsCorrectContractV2 loopRel loopBoundaryStage1 loopBoundaryStage1.reference
        Decode.decode ↔
      (∀ r : Request, r.Succeeds → ∃ s, Decode.decode r = some s) ∧
      (∀ (r : Request) s, r.Succeeds → Spells r s → Decode.decode r = some s) ∧
      (∀ (r : Request) o after parts program, r.pipeline o after parts program →
        Allocation.RoundTrip r.input.names ∧
        SafeSpellings r.input.names (Allocation.scope r o after).protectedNames
          (Allocation.scope r o after).generated) ∧
      (∀ (r : Request) o after parts program s, Decode.decode r = some s →
        r.pipeline o after parts program →
        Nonempty (PassCorrect (Observe.source s).behaviour (Observe.target program).behaviour)) ∧
      Simulation.Bound loopRel Decode.decode :=
  loopContractV2Stage1_iff.trans
    ⟨fun ⟨covered, complete, allocation, refines, _, bound⟩ =>
        ⟨covered, complete, allocation, refines, bound⟩,
      fun ⟨covered, complete, allocation, refines, bound⟩ =>
        ⟨covered, complete, allocation, refines, Simulation.initialMatching_loopRel, bound⟩⟩

end Solidity.Correctness.Lowering.Total
