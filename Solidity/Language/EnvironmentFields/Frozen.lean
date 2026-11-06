import Solidity.Language.EnvironmentFields.Contracts

/-!
# G01 full-scope relation contracts D1–D6, frozen version 1

The X/O/T lanes consume these names. Each relation is stated over the
definitions of `Solidity.Language.EnvironmentFields.Contracts` (namespace
`Solidity.Roadmap.FullScope`), unchanged: this module adds names, explicit
signatures and the consumer lemmas, never a premise. A later change is a new
namespace (`V2`) beside this one, with an adapter between them (H57).

| Contract | Statement | Producer obligation |
|---|---|---|
| D1 | `D1` | a run-indexed exact certificate: source meaning over the actual artifact and the run's oracle, oracle reads agreeing with the actual target execution (`D1.forward_oracle`, `D1.backward_oracle`) |
| D2 | `D2` | creation-size failures at Osaka's EIP-170/EIP-3860 limits |
| D3 | `D3` | byte memory and packed physical slots agree with the source state, total on representable states |
| D4 | `D4` | unsafe assembly writeback on every actual exit, and an optimizer that leaves unsafe blocks unchanged |
| D5 | `D5` | allowed environments correspond in both directions; every guard and Forward premise stays the language's |
| D6 | `D6` | the optimizer certificate: the same run-indexed certificate under the gas-value quotient |

`Contract` bundles all six for one compiler; `Contract.compiles` and
`forward_completes` are the H62 totality and adequacy lemmas, and
`Solidity/Language/EnvironmentFields/FrozenControls.lean` inhabits the whole
bundle with nonempty domains (joint satisfiability) beside its negative
controls.
-/

namespace Solidity.Roadmap.FullScope.V1

open Solidity.Roadmap Solidity.Roadmap.FullScope Solidity.Roadmap.FullScope.RunIndexed

/-- The producer's operational resource alignment of one source run and one
target run of the same actual artifact. -/
abbrev Alignment (source : Source) (target : Target) : Type :=
  (resolved : source.Resolved) → (art : Artifact) →
    SourceIndex source resolved art → TargetIndex target art → Prop

/-! ## D1: an independent source over the actual artifact and run oracle -/

/-- **D1.** The exact run-indexed certificate (H38): admission is exactly
compilation, legality is the independent source judgment, both coverages are
unconditional, and the forward and backward directions refine with ordered
query transcripts. -/
abbrev D1 (source : Source) (target : Target) (domain : SourceRuns source)
    (machine : TargetRuns target) (compiler : source.Resolved → Option Artifact)
    (environment : target.lang.Env → source.lang.Env) (aligned : Alignment source target) :
    Type :=
  Certificate source target domain machine compiler environment aligned .exact

/-- The target run a certificate assigns to an eligible source run. -/
def targetRunOf {source : Source} {target : Target} {domain : SourceRuns source}
    {machine : TargetRuns target} {compiler : source.Resolved → Option Artifact}
    {environment : target.lang.Env → source.lang.Env} {aligned : Alignment source target}
    {mode : Mode}
    (certificate : Certificate source target domain machine compiler environment aligned mode)
    {resolved : source.Resolved} {art : Artifact} (compiled : compiler resolved = some art)
    (run : SourceIndex source resolved art) (eligible : domain.Eligible run)
    (env : target.lang.Env) (allowed : target.lang.Allowed env)
    (sameEnv : run.environment = environment env) : TargetIndex target art :=
  ⟨env, certificate.need resolved art compiled run eligible env allowed sameEnv⟩

/-- D1, forward: every query the source run executed reads what the actual
target run assigned to it reads. -/
theorem D1.forward_oracle {source : Source} {target : Target} {domain : SourceRuns source}
    {machine : TargetRuns target} {compiler : source.Resolved → Option Artifact}
    {environment : target.lang.Env → source.lang.Env} {aligned : Alignment source target}
    {mode : Mode}
    (certificate : Certificate source target domain machine compiler environment aligned mode)
    {resolved : source.Resolved} {art : Artifact} (compiled : compiler resolved = some art)
    (run : SourceIndex source resolved art) (eligible : domain.Eligible run)
    (env : target.lang.Env) (allowed : target.lang.Allowed env)
    (sameEnv : run.environment = environment env)
    (forward : source.lang.Forward run.program run.environment run.resource)
    (guard : source.lang.Guard run.program run.environment run.resource)
    {query : Query art} {value : Word}
    (observed : (query, value) ∈ domain.queries resolved art run) :
    run.oracle query = target.read art env
      (targetRunOf certificate compiled run eligible env allowed sameEnv).resource query :=
  (certificate.forward resolved art compiled run eligible env allowed sameEnv forward guard).2.2.1
    |>.forward_oracle_agrees eligible.1 observed

/-- D1, backward: every guarded eligible target run has an eligible source run
whose oracle agrees with every query the target run executed. -/
theorem D1.backward_oracle {source : Source} {target : Target} {domain : SourceRuns source}
    {machine : TargetRuns target} {compiler : source.Resolved → Option Artifact}
    {environment : target.lang.Env → source.lang.Env} {aligned : Alignment source target}
    {mode : Mode}
    (certificate : Certificate source target domain machine compiler environment aligned mode)
    {resolved : source.Resolved} {art : Artifact} (compiled : compiler resolved = some art)
    (run : TargetIndex target art) (eligible : run.Eligible)
    (guard : target.lang.Guard (target.load art) run.environment run.resource) :
    ∃ sourceRun : SourceIndex source resolved art, domain.Eligible sourceRun ∧
      (mode.observe run.execution).Le (mode.observe sourceRun.execution) ∧
      ∀ query value, (query, value) ∈ machine.queries art run →
        sourceRun.oracle query = target.read art run.environment run.resource query := by
  obtain ⟨sourceRun, sourceEligible, coupled, _, below⟩ :=
    certificate.backward resolved art compiled run eligible guard
  exact ⟨sourceRun, sourceEligible, below,
    fun _ _ observed => coupled.backward_oracle_agrees sourceEligible.1 observed⟩

/-! ## D2: creation-size failures -/

/-- **D2.** Creation beyond Osaka's EIP-170/EIP-3860 limits fails observably
(`creationFits`), and some creation within them succeeds, so an attempt that
always fails does not satisfy it. Exact failure gas is the EVM owner's
separate obligation. -/
structure D2 (attempt : Bytes → Bytes → Evm.Halt) : Prop where
  failures : CreationSizeFailures attempt
  live : ∃ initcode runtime, creationFits initcode runtime ∧
    (attempt initcode runtime).observe.1 = true

/-- The limits are decidable, so a producer can branch on them. -/
instance creationFitsDecidable (initcode runtime : Bytes) :
    Decidable (creationFits initcode runtime) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-! ## D3: byte memory and packed physical slots -/

/-- The value a packed field holds in its slot word: `width` bytes starting
`offset` bytes from the low-order end (solc's packing order). -/
def fieldRead (field : PackedField) (slotValue : Word) : Nat :=
  slotValue.val / 256 ^ field.offset.val % 256 ^ field.width.val

/-- Two fields share no byte. -/
def fieldsDisjoint (a b : PackedField) : Prop :=
  a.slot ≠ b.slot ∨ a.offset.val + a.width.val ≤ b.offset.val ∨
    b.offset.val + b.width.val ≤ a.offset.val

/-- A physical layout: a slot space and a packed field per source variable;
distinct variables of one space never share a byte. -/
structure Layout (Var : Type) where
  space : Var → SlotSpace
  field : Var → PackedField
  disjoint : ∀ a b, a ≠ b → space a = space b → fieldsDisjoint (field a) (field b)

/-- Every source value is the content of its physical field. -/
def Layout.Agrees {Var : Type} (layout : Layout Var) (value : Var → Nat)
    (slots : SlotSpace → Word → Word) : Prop :=
  ∀ v, value v = fieldRead (layout.field v) (slots (layout.space v) (layout.field v).slot)

/-- The source's memory view is the target's byte memory, extent included. -/
def MemoryAgrees (extent : Nat) (view : Word → UInt8) (memory : ByteMemory) : Prop :=
  memory.size = extent ∧ ∀ address, view address = memory.data address

/-- One producer's physical correspondence: the source state's variable values
and memory view, the target state's slots and byte memory, and the relation
its simulation maintains. -/
structure Physical where
  Var : Type
  layout : Layout Var
  SourceState : Type
  TargetState : Type
  value : SourceState → Var → Nat
  extent : SourceState → Nat
  view : SourceState → Word → UInt8
  slots : TargetState → SlotSpace → Word → Word
  memory : TargetState → ByteMemory
  Related : SourceState → TargetState → Prop

/-- A source state the physical layout can hold: every value fits its field,
and its memory extent and view are those of a byte memory. -/
def Physical.Representable (p : Physical) (s : p.SourceState) : Prop :=
  (∀ v, p.value s v < 256 ^ (p.layout.field v).width.val) ∧
    p.extent s ≤ 2 ^ 256 ∧ p.extent s % 32 = 0 ∧
    ∀ address : Word, p.extent s ≤ address.val → p.view s address = 0

/-- **D3.** Related states agree on every slot and memory byte, and every
representable source state is related to some target state. `live` requires a
representable source state, so neither an empty source state type nor an
extent that is never word-aligned makes `total` vacuous; with it, an empty
relation does not satisfy the contract. -/
structure D3 (p : Physical) : Prop where
  agrees : ∀ s t, p.Related s t →
    p.layout.Agrees (p.value s) (p.slots t) ∧ MemoryAgrees (p.extent s) (p.view s) (p.memory t)
  total : ∀ s, p.Representable s → ∃ t, p.Related s t
  live : ∃ s, p.Representable s

/-! ## D4: unsafe assembly -/

/-- One producer's assembly boundary: its states, invariant, unsafe-block
execution, writeback and correspondence, and its optimizer on blocks. -/
structure Assembly where
  State : Type
  MemOK : State → Prop
  executes : State → State → Prop
  writeback : State → State
  Corresponds : State → State → Prop
  Block : Type
  optimize : Block → Block
  isUnsafe : Block → Prop

/-- **D4.** The writeback re-establishes the invariant and corresponds to the
actual exit state on every execution, and the optimizer keeps every unsafe
block byte for byte. -/
structure D4 (a : Assembly) : Prop where
  writeback : UnsafeWriteback a.State a.MemOK a.executes a.writeback a.Corresponds
  opaqueBlocks : Opaque a.optimize a.isUnsafe
  /-- An unsafe block executes from some state and the optimizer meets some
  unsafe block, so neither obligation holds vacuously. -/
  live : (∃ before after, a.executes before after) ∧ ∃ block, a.isUnsafe block

/-! ## D5: environments and premises -/

/-- **D5.** Allowed target environments map to allowed source environments and
reach all of them. Chain and crypto premises stay the languages' own `Allowed`,
`Admissible`, `Forward` and `Guard`; no exclusion is added here. -/
def D5 (source : Source) (target : Target)
    (environment : target.lang.Env → source.lang.Env) : Prop :=
  (∀ env, target.lang.Allowed env → source.lang.Allowed (environment env)) ∧
    ∀ env, source.lang.Allowed env → ∃ targetEnv, target.lang.Allowed targetEnv ∧
      environment targetEnv = env

/-- Every run-indexed certificate proves D5. -/
theorem d5_of_certificate {source : Source} {target : Target} {domain : SourceRuns source}
    {machine : TargetRuns target} {compiler : source.Resolved → Option Artifact}
    {environment : target.lang.Env → source.lang.Env} {aligned : Alignment source target}
    {mode : Mode}
    (certificate : Certificate source target domain machine compiler environment aligned mode) :
    D5 source target environment :=
  ⟨certificate.envSound, certificate.envOnto⟩

/-! ## D6: the optimizer quotient -/

/-- **D6.** The run-indexed certificate under the gas-value quotient
(`Mode.optimizer`, `eraseGas`): every observation occurrence, its order and
the final outcome bytes stay exact; only `gas`/`gasleft` values may differ. -/
abbrev D6 (source : Source) (target : Target) (domain : SourceRuns source)
    (machine : TargetRuns target) (compiler : source.Resolved → Option Artifact)
    (environment : target.lang.Env → source.lang.Env) (aligned : Alignment source target) :
    Type :=
  Certificate source target domain machine compiler environment aligned .optimizer

/-- The quotient is monotone: an exact prefix order survives it. -/
theorem Mode.observe_le (mode : Mode) {a b : Prefix Observation Outcome} (h : a.Le b) :
    (mode.observe a).Le (mode.observe b) := by
  cases mode
  · exact h
  · exact eraseGas_le h

/-- The quotient of a quotient is the quotient. -/
theorem Mode.observe_optimizer (mode : Mode) (p : Prefix Observation Outcome) :
    Mode.optimizer.observe (mode.observe p) = Mode.optimizer.observe p := by
  cases mode
  · rfl
  · exact eraseGas_idempotent p

/-- An exact compiler is an optimizing one: D1 gives D6 with the same `need`. -/
def D1.toD6 {source : Source} {target : Target} {domain : SourceRuns source}
    {machine : TargetRuns target} {compiler : source.Resolved → Option Artifact}
    {environment : target.lang.Env → source.lang.Env} {aligned : Alignment source target}
    (certificate : D1 source target domain machine compiler environment aligned) :
    D6 source target domain machine compiler environment aligned where
  admission := certificate.admission
  envSound := certificate.envSound
  envOnto := certificate.envOnto
  legality := certificate.legality
  sourceResourceCoverage := certificate.sourceResourceCoverage
  need := certificate.need
  sourceCoverage := certificate.sourceCoverage
  targetCoverage := certificate.targetCoverage
  forward := by
    intro resolved art compiled run eligible env allowed sameEnv forward guard
    obtain ⟨targetForward, targetGuard, coupled, below⟩ :=
      certificate.forward resolved art compiled run eligible env allowed sameEnv forward guard
    exact ⟨targetForward, targetGuard, coupled, Mode.observe_le .optimizer below⟩
  backward := by
    intro resolved art compiled run eligible guard
    obtain ⟨sourceRun, sourceEligible, coupled, sourceGuard, below⟩ :=
      certificate.backward resolved art compiled run eligible guard
    exact ⟨sourceRun, sourceEligible, coupled, sourceGuard, Mode.observe_le .optimizer below⟩

/-! ## The bundle -/

/-- **The frozen G01 full-scope contract** of one compiler in one mode: the
run-indexed certificate (D1 in `.exact`, D6 in `.optimizer`, D5 by
`d5_of_certificate`), creation-size failures (D2), the physical correspondence
(D3) and the assembly boundary (D4). Every parameter is explicit. D2–D4 are
stated over the producer's own `attempt`, `Physical` and `Assembly`; this
bundle does not tie them to `target`'s operational semantics, which is each
producer's adapter obligation. -/
structure Contract (source : Source) (target : Target) (domain : SourceRuns source)
    (machine : TargetRuns target) (compiler : source.Resolved → Option Artifact)
    (environment : target.lang.Env → source.lang.Env) (aligned : Alignment source target)
    (mode : Mode) (attempt : Bytes → Bytes → Evm.Halt) (physical : Physical)
    (assembly : Assembly) where
  run : Certificate source target domain machine compiler environment aligned mode
  /-- Some input is admitted, so `domain.Admitted := fun _ => False` with a
  compiler that compiles nothing does not satisfy the contract. Which inputs
  must be admitted (the feature catalog) is G07's obligation. -/
  admitsSome : ∃ resolved, domain.Admitted resolved
  creation : D2 attempt
  layout : D3 physical
  assemblyBoundary : D4 assembly

/-- **Totality (H62).** Every admitted input compiles, so a compiler that
rejects an admitted input satisfies no contract. -/
theorem Contract.compiles {source : Source} {target : Target} {domain : SourceRuns source}
    {machine : TargetRuns target} {compiler : source.Resolved → Option Artifact}
    {environment : target.lang.Env → source.lang.Env} {aligned : Alignment source target}
    {mode : Mode} {attempt : Bytes → Bytes → Evm.Halt} {physical : Physical}
    {assembly : Assembly}
    (contract : Contract source target domain machine compiler environment aligned mode attempt
      physical assembly)
    {resolved : source.Resolved} (admitted : domain.Admitted resolved) :
    ∃ art, compiler resolved = some art := by
  have some := (contract.run.admission resolved).1 admitted
  cases h : compiler resolved with
  | none => rw [h] at some; cases some
  | some art => exact ⟨art, rfl⟩

/-- A compiler that compiles nothing has no certificate once some input is
admitted. -/
theorem rejecting_refused {source : Source} {target : Target}
    {domain : SourceRuns source} {machine : TargetRuns target}
    {environment : target.lang.Env → source.lang.Env} {aligned : Alignment source target}
    {mode : Mode} {resolved : source.Resolved} (admitted : domain.Admitted resolved) :
    ¬ Nonempty (Certificate source target domain machine (fun _ => none) environment aligned
      mode) := by
  intro ⟨certificate⟩
  have some := (certificate.admission resolved).1 admitted
  cases some

/-- **Adequacy.** A guarded Forward source run that completes with outcome `o`
makes the assigned target run complete with the same observation, quotient
included. -/
theorem forward_completes {source : Source} {target : Target}
    {domain : SourceRuns source} {machine : TargetRuns target}
    {compiler : source.Resolved → Option Artifact}
    {environment : target.lang.Env → source.lang.Env} {aligned : Alignment source target}
    {mode : Mode}
    (certificate : Certificate source target domain machine compiler environment aligned mode)
    {resolved : source.Resolved} {art : Artifact} (compiled : compiler resolved = some art)
    (run : SourceIndex source resolved art) (eligible : domain.Eligible run)
    (env : target.lang.Env) (allowed : target.lang.Allowed env)
    (sameEnv : run.environment = environment env)
    (forward : source.lang.Forward run.program run.environment run.resource)
    (guard : source.lang.Guard run.program run.environment run.resource)
    {o : Outcome} (completes : (mode.observe run.execution).final = some o) :
    mode.observe (targetRunOf certificate compiled run eligible env allowed sameEnv).execution =
      mode.observe run.execution :=
  (certificate.forward resolved art compiled run eligible env allowed sameEnv forward guard
    ).2.2.2.final_eq completes

end Solidity.Roadmap.FullScope.V1
