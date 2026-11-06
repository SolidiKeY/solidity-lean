import Solidity.Roadmap.Contracts


/-!
## H37 D1–D6: full-observation interfaces (X01)

This is an explicit leaf import: the widely used legacy foundation deliberately
does not import this unfrozen proposal. Declaration namespaces remain unchanged.

These are contract statements, not certificates for existing producers. The
legacy six contracts imported from `Solidity.Roadmap.Contracts` retain their names until their owners supply adapters.
Every new X/O/T lane consumes `FullScope`; projecting to the legacy event type is
not sufficient evidence for any full-scope checkpoint.
-/
namespace Solidity.Roadmap.FullScope

/-- Byte-addressed EVM memory. The size is a byte count, never a word index. -/
structure ByteMemory where
  data : Word → UInt8
  size : Nat
  size_le : size ≤ 2 ^ 256
  aligned : size % 32 = 0
  unallocated_zero : ∀ address, size ≤ address.val → data address = 0

/-- Solc's reserved byte ranges; allocation starts after the zero slot. -/
def scratchEnd : Nat := 0x40
def freePointer : Nat := 0x40
def zeroSlot : Nat := 0x60
def allocationStart : Nat := 0x80

/-- A packed field fits within its physical 32-byte slot. -/
structure PackedField where
  slot : Word
  offset : Fin 32
  width : Fin 33
  nonempty : 0 < width.val
  fits : offset.val + width.val ≤ 32

/-- D3: storage and transient locations are separate physical namespaces. -/
inductive SlotSpace where
  | storage | transient
  deriving DecidableEq, Repr

/-- D1's closed whitelist of target-dependent scalar queries. No arbitrary
source expression or source result can be supplied by this interface. -/
inductive ScalarQuery where
  | gasleft | gas | msize | pc
  deriving DecidableEq, Repr

/-- The executing code's phase, including constructor code. -/
inductive Phase where
  | creation | runtime
  deriving DecidableEq, Repr

/-- A source code reference must name an actual entry of the artifact table. -/
structure CodeRef (art : Artifact) where
  unit : Fin art.contracts.length
  phase : Phase

/-- Only code bytes are read from the artifact table. -/
def CodeRef.bytes {art : Artifact} (ref : CodeRef art) : Bytes :=
  match ref.phase with
  | .creation => (art.contracts[ref.unit]).initcode
  | .runtime => (art.contracts[ref.unit]).runtime

/-- Dynamic query identity includes its occurrence and executing code. -/
structure Query (art : Artifact) where
  code : CodeRef art
  occurrence : Nat
  kind : ScalarQuery

/-- Supplied by the actual target execution, universally quantified by the
source theorem. Agreement with that execution is a producer proof obligation. -/
abbrev Oracle (art : Artifact) := Query art → Word

/-- D1: a source run reads exactly this artifact and target oracle. -/
structure Inputs where
  artifact : Artifact
  oracle : Oracle artifact

/-- Ordered logs retain emitter, at most four topics and all data bytes. -/
structure Log where
  emitter : Address
  topics : List Word
  topics_le : topics.length ≤ 4
  data : Bytes

/-- All original events remain observations. Extra observations include raw
bytes (already present in calls/answers), code, codehash, physical layout and
D1 scalar values. Their order is the order of the prefix's event list. -/
inductive Observation where
  | session (event : Event)
  | log (entry : Log)
  | code (account : Address) (bytes : Bytes)
  | codehash (account : Address) (hash : Word)
  | slot (account : Address) (space : SlotSpace) (key value : Word)
  | memory (address : Word) (value : UInt8)
  | scalar (kind : ScalarQuery) (value : Word)

/-- D6 erases only gas values. `msize` and `pc` remain exact observations. -/
def Observation.withoutGas : Observation → Observation
  | .scalar .gasleft _ => .scalar .gasleft 0
  | .scalar .gas _ => .scalar .gas 0
  | observation => observation

/-- The sole optimizer observation quotient. Outcome bytes remain exact. -/
def eraseGas (p : Prefix Observation Outcome) : Prefix Observation Outcome :=
  ⟨p.events.map Observation.withoutGas, p.final⟩

/-- D2 creation-size failures use Osaka's EIP-170/EIP-3860 limits, not the
legacy idealized pin. Exact step gas/resource semantics remain owner obligations. -/
def creationFits (initcode runtime : Bytes) : Prop :=
  initcode.length ≤ 49152 ∧ runtime.length ≤ 24576

/-- D4: entering an unsafe assembly block drops the invariant. Re-establishing
it requires a proved writeback on each actual exit. No `MemOK` assumption is
imposed on the input or on intermediate assembly states. -/
structure UnsafeWriteback (State : Type) (MemOK : State → Prop)
    (executes : State → State → Prop) (writeback : State → State)
    (Corresponds : State → State → Prop) : Prop where
  recovers : ∀ before after, executes before after → MemOK (writeback after)
  corresponds : ∀ before after, executes before after → Corresponds after (writeback after)

/-- D4's optimizer boundary: an unsafe block is unchanged, including its bytes.
A producer must prove this equation for its actual optimizing transformation. -/
def Opaque {Block : Type} (optimize : Block → Block) (isUnsafe : Block → Prop) : Prop :=
  ∀ block, isUnsafe block → optimize block = block

/-- Exact compilation/lowering contract for all new X/T lanes. Chain and
crypto premises are expressed by the languages' guards and allowed environments;
there is no new language exclusion in this interface. -/
structure Exact (source target : Lang Observation Outcome) where
  pass : Pass source target
  certificate : Cert pass
  total : ∀ program, pass.Dom program

/-- D6's relation on runs. The public producer contract must instantiate
these functions with the source meaning and actual output artifact's execution.
This relation alone is not a compiler correctness certificate. -/
def Optimizes {RS RT : Type} (AS : RS → Prop) (AT : RT → Prop)
    (FS GS : RS → Prop) (GT : RT → Prop)
    (source : Prefixes RS Observation Outcome)
    (target : Prefixes RT Observation Outcome) : Prop :=
  RefinesUnder AS AT FS GS GT (fun r => eraseGas (source r))
    (fun r => eraseGas (target r))

/-- D1/G07: a source evaluator has no compiler argument. Its code table and
closed query oracle are explicit independent inputs. G07 must additionally audit
its definition/import closure; this type alone does not prove non-circularity. -/
structure Source where
  Resolved : Type
  lang : Lang Observation Outcome
  meaning : Resolved → Inputs → lang.Prog

/-- Target oracle linkage is stated against the actual compiled artifact,
not an arbitrary oracle existentially selected to make refinement hold. -/
def OracleAgreement (art : Artifact) (oracle targetRead : Oracle art) : Prop :=
  ∀ query, oracle query = targetRead query

/-- A target producer fixes its reader with its execution, before correctness
is stated. `Inputs` is constructed from that reader, never chosen existentially
by a correctness proof. The target owner must justify both definitions from its
operational semantics. -/
structure Target where
  lang : Lang Observation Outcome
  load : Artifact → lang.Prog
  read : (art : Artifact) → lang.Env → lang.Res → Oracle art

/-- One directional, actual-run obligation. The oracle is indexed by the
actual target resource bound, so different initial gas supplies may return
different values. This is only soundness, not the public two-sided contract:
resource adequacy and source/target resource alignment remain mandatory. -/
def ArtifactSound (source : Source) (target : Target)
    (compile : source.Resolved → Artifact)
    (environment : target.lang.Env → source.lang.Env) : Prop :=
  ∀ resolved env rt, target.lang.Allowed env → target.lang.Admissible rt →
    let art := compile resolved
    target.lang.Guard (target.load art) env rt →
    let program := source.meaning resolved ⟨art, target.read art env rt⟩
    ∃ rs, source.lang.Admissible rs ∧
      (eraseGas (target.lang.sem (target.load art) env rt)).Le
        (eraseGas (source.lang.sem program (environment env) rs))

/-- Normalizing gas values a second time cannot hide another observation. -/
theorem Observation.withoutGas_idempotent (observation : Observation) :
    observation.withoutGas.withoutGas = observation.withoutGas := by
  cases observation with
  | scalar kind value => cases kind <;> rfl
  | _ => rfl

/-- Normalizing one prefix retains its exact observation count. -/
theorem eraseGas_length (p : Prefix Observation Outcome) :
    (eraseGas p).events.length = p.events.length :=
  List.length_map Observation.withoutGas

/-- Return/revert bytes remain exact even under the optimizer quotient. -/
theorem eraseGas_final (p : Prefix Observation Outcome) :
    (eraseGas p).final = p.final := rfl

/-- The quotient is a projection, not repeated information loss. -/
theorem eraseGas_idempotent (p : Prefix Observation Outcome) :
    eraseGas (eraseGas p) = eraseGas p := by
  cases p with
  | mk events final =>
    change Prefix.mk ((events.map Observation.withoutGas).map Observation.withoutGas) final = _
    rw [List.map_map]
    have hmap : events.map (Observation.withoutGas ∘ Observation.withoutGas) =
        events.map Observation.withoutGas :=
      List.map_congr_left fun observation _ => observation.withoutGas_idempotent
    rw [hmap]
    rfl

/-- Normalization preserves finite-prefix order, including completed prefixes. -/
theorem eraseGas_le {a b : Prefix Observation Outcome} (h : a.Le b) :
    (eraseGas a).Le (eraseGas b) := by
  refine ⟨h.1.map Observation.withoutGas, ?_⟩
  rcases h.2 with unfinished | completed
  · exact .inl unfinished
  · exact .inr (congrArg eraseGas completed)

/-- Any exact two-sided refinement also satisfies the optimizer relation.
The converse is deliberately not asserted: gas values alone may differ. -/
theorem optimizes_of_refines {RS RT : Type} {AS : RS → Prop} {AT : RT → Prop}
    {FS GS : RS → Prop} {GT : RT → Prop}
    {source : Prefixes RS Observation Outcome} {target : Prefixes RT Observation Outcome}
    (h : RefinesUnder AS AT FS GS GT source target) :
    Optimizes AS AT FS GS GT source target := by
  constructor
  · intro rs admissible forward guard
    obtain ⟨rt, hadmissible, hprefix⟩ := h.1 rs admissible forward guard
    exact ⟨rt, hadmissible, eraseGas_le hprefix⟩
  · intro rt admissible guard
    obtain ⟨rs, hadmissible, hprefix⟩ := h.2 rt admissible guard
    exact ⟨rs, hadmissible, eraseGas_le hprefix⟩

/-- Empty physical memory is inhabited and all byte reads are zero. This
witness precedes the solc prologue; it does not assert an initialized FMP. -/
def ByteMemory.empty : ByteMemory where
  data := fun _ => 0
  size := 0
  size_le := Nat.zero_le _
  aligned := rfl
  unallocated_zero := fun _ _ => rfl

/-- D2's necessary observable creation-size failure obligation, parameterized
by actual producer execution. It does not assert success or exact failure gas;
those remain separate obligations. No producer proof is supplied. -/
def CreationSizeFailures (attempt : Bytes → Bytes → Evm.Halt) : Prop :=
  ∀ initcode runtime, ¬ creationFits initcode runtime →
    (attempt initcode runtime).observe = (false, [])


/-! ## H38 run-indexed proposal (producer review required)

Source oracle/resource indices are fixed before constructing a target witness.
Legality belongs to the independent source semantics; it must not be defined as
"the runs a target can match". The certificate proves coverage and both prefix
directions. These declarations do not supply any producer proof or replace the
six G01 public contracts. Source/EVM owners must review legality, operational
query provenance and resource alignment before this proposal can be frozen.
-/
namespace RunIndexed

/-- One source run: actual artifact is a type index, with oracle and source
resources fixed together. A target witness cannot retrospectively change them. -/
structure SourceIndex (source : Source) (resolved : source.Resolved) (art : Artifact) where
  environment : source.lang.Env
  resource : source.lang.Res
  oracle : Oracle art

/-- One target execution bound of the same actual artifact. -/
structure TargetIndex (target : Target) (art : Artifact) where
  environment : target.lang.Env
  resource : target.lang.Res

def SourceIndex.program {source : Source} {resolved : source.Resolved} {art : Artifact}
    (run : SourceIndex source resolved art) : source.lang.Prog :=
  source.meaning resolved ⟨art, run.oracle⟩

def SourceIndex.execution {source : Source} {resolved : source.Resolved} {art : Artifact}
    (run : SourceIndex source resolved art) : Prefix Observation Outcome :=
  source.lang.sem run.program run.environment run.resource

def TargetIndex.execution {target : Target} {art : Artifact}
    (run : TargetIndex target art) : Prefix Observation Outcome :=
  target.lang.sem (target.load art) run.environment run.resource

/-- Only executed scalar reads are in the operational query transcript. A
missing query is not interpreted as an executed read of zero. -/
def scalarRead : Observation → Option (ScalarQuery × Word)
  | .scalar kind value => some (kind, value)
  | _ => none

/-- Producer-facing source judgments. `Legal` must be characterized by the
independent source resource/oracle semantics and audited by G07, not by target
coverage or refinement. No certificate may assume its coverage as a premise. -/
structure SourceRuns (source : Source) where
  Admitted : source.Resolved → Prop
  /-- The authoritative run judgment of the independent source semantics,
  fixed before the compiler/coupling. Its characterization is a source-owner
  review obligation; it must not be defined by matching target executions. -/
  Specified : (resolved : source.Resolved) → (art : Artifact) →
    SourceIndex source resolved art → Prop
  Legal : (resolved : source.Resolved) → (art : Artifact) →
    SourceIndex source resolved art → Prop
  queries : (resolved : source.Resolved) → (art : Artifact) →
    SourceIndex source resolved art → List (Query art × Word)
  observations : ∀ resolved art run, Legal resolved art run →
    (queries resolved art run).map (fun entry => (entry.1.kind, entry.2)) =
      run.execution.events.filterMap scalarRead
  reads : ∀ resolved art run, Legal resolved art run → ∀ query value,
    (query, value) ∈ queries resolved art run → run.oracle query = value

/-- The target owner supplies a transcript from the actual pinned execution,
with observed-value and reader proofs. Its definition and query provenance need
producer review; setting a free reader equal to the source oracle is not a proof. -/
structure TargetRuns (target : Target) where
  queries : (art : Artifact) → TargetIndex target art → List (Query art × Word)
  observations : ∀ art run,
    (queries art run).map (fun entry => (entry.1.kind, entry.2)) =
      run.execution.events.filterMap scalarRead
  reads : ∀ art run query value, (query, value) ∈ queries art run →
    target.read art run.environment run.resource query = value

/-- Source legality adds no replacement for the existing allowed-environment,
admissibility, Forward or hash judgments. Every one is read from `source.lang`. -/
def SourceRuns.Eligible {source : Source} (domain : SourceRuns source)
    {resolved : source.Resolved} {art : Artifact}
    (run : SourceIndex source resolved art) : Prop :=
  domain.Legal resolved art run ∧ source.lang.Allowed run.environment ∧
    source.lang.Admissible run.resource

def TargetIndex.Eligible {target : Target} {art : Artifact}
    (run : TargetIndex target art) : Prop :=
  target.lang.Allowed run.environment ∧ target.lang.Admissible run.resource

/-- Finite-prefix query order follows the direction of refinement. A target
cut between two atomic source observations is allowed in the backward direction. -/
inductive Direction where
  | forward | backward
  deriving DecidableEq, Repr

def Direction.Ordered {α : Type} : Direction → List α → List α → Prop
  | .forward, sourceQueries, targetQueries => sourceQueries <+: targetQueries
  | .backward, sourceQueries, targetQueries => targetQueries <+: sourceQueries

/-- Unguarded binding of artifact, shared environment and physical run/resource
plan. The producer's Aligned relation must characterize those operational facts,
not prefix refinement. It may not filter source behavior using a hash guard. -/
structure Bound {source : Source} {target : Target}
    (environment : target.lang.Env → source.lang.Env)
    (Aligned : (resolved : source.Resolved) → (art : Artifact) →
      SourceIndex source resolved art → TargetIndex target art → Prop)
    {resolved : source.Resolved} {art : Artifact}
    (sourceRun : SourceIndex source resolved art) (targetRun : TargetIndex target art) : Prop where
  environment_agrees : sourceRun.environment = environment targetRun.environment
  resources : Aligned resolved art sourceRun targetRun

/-- Artifact identity is enforced by the shared index. Resource alignment is a
producer-defined operational relation (failure points/horizons), which must not
contain desired prefix refinement or a new language restriction. Query occurrence
and code labels remain in the ordered transcripts; their operational provenance
must be proved by the source/EVM owners before freeze. -/
structure Coupled {source : Source} {target : Target}
    (domain : SourceRuns source) (machine : TargetRuns target)
    (environment : target.lang.Env → source.lang.Env)
    (Aligned : (resolved : source.Resolved) → (art : Artifact) →
      SourceIndex source resolved art → TargetIndex target art → Prop)
    (direction : Direction)
    {resolved : source.Resolved} {art : Artifact}
    (sourceRun : SourceIndex source resolved art) (targetRun : TargetIndex target art) : Prop extends Bound environment Aligned sourceRun targetRun where
  queries_ordered : direction.Ordered (domain.queries resolved art sourceRun)
    (machine.queries art targetRun)

/-- Forward source readings agree with the fixed target execution. Unexecuted
queries outside the source prefix acquire no arbitrary default value. -/
theorem Coupled.forward_oracle_agrees {source : Source} {target : Target}
    {domain : SourceRuns source} {machine : TargetRuns target}
    {environment : target.lang.Env → source.lang.Env}
    {Aligned : (resolved : source.Resolved) → (art : Artifact) →
      SourceIndex source resolved art → TargetIndex target art → Prop}
    {resolved : source.Resolved} {art : Artifact}
    {sourceRun : SourceIndex source resolved art} {targetRun : TargetIndex target art}
    (coupled : Coupled domain machine environment Aligned .forward sourceRun targetRun)
    (legal : domain.Legal resolved art sourceRun) {query : Query art} {value : Word}
    (observed : (query, value) ∈ domain.queries resolved art sourceRun) :
    sourceRun.oracle query = target.read art targetRun.environment targetRun.resource query :=
  (domain.reads resolved art sourceRun legal query value observed).trans
    (machine.reads art targetRun query value
      (List.IsPrefix.subset coupled.queries_ordered observed)).symm

/-- Backward target readings agree with the matching source extension. Source
queries beyond this target horizon need not already occur in the target prefix. -/
theorem Coupled.backward_oracle_agrees {source : Source} {target : Target}
    {domain : SourceRuns source} {machine : TargetRuns target}
    {environment : target.lang.Env → source.lang.Env}
    {Aligned : (resolved : source.Resolved) → (art : Artifact) →
      SourceIndex source resolved art → TargetIndex target art → Prop}
    {resolved : source.Resolved} {art : Artifact}
    {sourceRun : SourceIndex source resolved art} {targetRun : TargetIndex target art}
    (coupled : Coupled domain machine environment Aligned .backward sourceRun targetRun)
    (legal : domain.Legal resolved art sourceRun) {query : Query art} {value : Word}
    (observed : (query, value) ∈ machine.queries art targetRun) :
    sourceRun.oracle query = target.read art targetRun.environment targetRun.resource query :=
  (domain.reads resolved art sourceRun legal query value
    (List.IsPrefix.subset coupled.queries_ordered observed)).trans
    (machine.reads art targetRun query value observed).symm

/-- Public compilation is exact. Only optimizer certificates select the D6
normalization, which retains event occurrences and all final outcome bytes. -/
inductive Mode where
  | exact | optimizer
  deriving DecidableEq, Repr

def Mode.observe : Mode → Prefix Observation Outcome → Prefix Observation Outcome
  | .exact, execution => execution
  | .optimizer, execution => eraseGas execution

/-- H38's two-sided run-indexed proposal. `need` sees a fixed eligible source
index before any Forward/Guard check. Unconditional source and target coverage
are theorem fields, not new public assumptions. All resources and observations
remain explicit. Existing admission, environment and guard obligations remain.

The full X01 freeze additionally needs producer approval of the independent
Legal/Aligned definitions, preservation of G01 source/Forward coverage and
non-vacuity, and all remaining D2–D5/public-contract obligations. -/
structure Certificate (source : Source) (target : Target)
    (domain : SourceRuns source) (machine : TargetRuns target)
    (compiler : source.Resolved → Option Artifact)
    (environment : target.lang.Env → source.lang.Env)
    (Aligned : (resolved : source.Resolved) → (art : Artifact) →
      SourceIndex source resolved art → TargetIndex target art → Prop)
    (mode : Mode) where
  admission : ∀ resolved, domain.Admitted resolved ↔ (compiler resolved).isSome
  envSound : ∀ env, target.lang.Allowed env → source.lang.Allowed (environment env)
  envOnto : ∀ env, source.lang.Allowed env →
    ∃ targetEnv, target.lang.Allowed targetEnv ∧ environment targetEnv = env
  /-- The candidate legality predicate cannot filter any independently
  specified source run, including its positive Forward obligations. This is a
  required proof, not an assumed public premise. G07 must audit Specified's
  independent source definition; resource-totality alone is insufficient. -/
  legality : ∀ resolved art, compiler resolved = some art →
    ∀ run : SourceIndex source resolved art,
      domain.Legal resolved art run ↔ domain.Specified resolved art run
  /-- Every original admissible source resource has a legal oracle instance,
  independently of Forward/Guard and before a target witness is selected. -/
  sourceResourceCoverage : ∀ resolved art, compiler resolved = some art →
    ∀ env resource, source.lang.Allowed env → source.lang.Admissible resource →
      ∃ oracle, domain.Legal resolved art ⟨env, resource, oracle⟩
  need : ∀ resolved art, compiler resolved = some art →
    (run : SourceIndex source resolved art) → domain.Eligible run →
    (env : target.lang.Env) → target.lang.Allowed env →
      run.environment = environment env → target.lang.Res
  /-- No Forward or hash antecedent can hide an eligible source run. Binding
  is unconditional; semantic query correspondence, like prefix refinement,
  belongs to the guarded forward/backward fields below. -/
  sourceCoverage : ∀ resolved art (compiled : compiler resolved = some art)
    (run : SourceIndex source resolved art) (eligible : domain.Eligible run)
    env (allowed : target.lang.Allowed env) (sameEnv : run.environment = environment env),
    let targetRun : TargetIndex target art :=
      ⟨env, need resolved art compiled run eligible env allowed sameEnv⟩
    targetRun.Eligible ∧ Bound environment Aligned run targetRun
  targetCoverage : ∀ resolved art, compiler resolved = some art →
    ∀ run : TargetIndex target art, run.Eligible →
      ∃ sourceRun : SourceIndex source resolved art, domain.Eligible sourceRun ∧
        Bound environment Aligned sourceRun run
  forward : ∀ resolved art (compiled : compiler resolved = some art)
    (run : SourceIndex source resolved art) (eligible : domain.Eligible run)
    env (allowed : target.lang.Allowed env) (sameEnv : run.environment = environment env),
    source.lang.Forward run.program run.environment run.resource →
    source.lang.Guard run.program run.environment run.resource →
    let targetRun : TargetIndex target art :=
      ⟨env, need resolved art compiled run eligible env allowed sameEnv⟩
    target.lang.Forward (target.load art) env targetRun.resource ∧
      target.lang.Guard (target.load art) env targetRun.resource ∧
      Coupled domain machine environment Aligned .forward run targetRun ∧
      (mode.observe run.execution).Le (mode.observe targetRun.execution)
  backward : ∀ resolved art, compiler resolved = some art →
    ∀ run : TargetIndex target art, run.Eligible →
      target.lang.Guard (target.load art) run.environment run.resource →
      ∃ sourceRun : SourceIndex source resolved art, domain.Eligible sourceRun ∧
        Coupled domain machine environment Aligned .backward sourceRun run ∧
        source.lang.Guard sourceRun.program sourceRun.environment sourceRun.resource ∧
        (mode.observe run.execution).Le (mode.observe sourceRun.execution)

end RunIndexed

end Solidity.Roadmap.FullScope
