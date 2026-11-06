import Solidity.Language.EnvironmentFields.Contracts

/-!
# VX1 interface controls

Inhabited witnesses, negative controls and mixed observations for the X01
contract definitions. These are kernel controls of the interface only. The toy
creation guard is not an EVM execution or a compiler correctness certificate.
-/
namespace Solidity.FullScope.VX1Controls

open Solidity.Roadmap Solidity.Roadmap.FullScope

/-- Neither arbitrary nonzero out-of-extent memory nor misaligned extent can
inhabit the byte-memory boundary. -/
theorem empty_memory_zero (memory : ByteMemory) (empty : memory.size = 0)
    (address : Word) : memory.data address = 0 := by
  apply memory.unallocated_zero address
  rw [empty]
  exact Nat.zero_le _

theorem memory_extent_aligned (memory : ByteMemory) : memory.size % 32 = 0 :=
  memory.aligned

theorem memory_witness : ∃ memory : ByteMemory, memory.size = 0 ∧
    ∀ address, memory.data address = 0 :=
  ⟨ByteMemory.empty, rfl, fun _ => rfl⟩

def artifact : Artifact :=
  ⟨[⟨[0x60, 0x01], [0x60, 0x02, 0x00], []⟩], 0⟩

def creationRef : CodeRef artifact := ⟨⟨0, by decide⟩, .creation⟩
def runtimeRef : CodeRef artifact := ⟨⟨0, by decide⟩, .runtime⟩

theorem artifact_creation_bytes : creationRef.bytes = [0x60, 0x01] := rfl
theorem artifact_runtime_bytes : runtimeRef.bytes = [0x60, 0x02, 0x00] := rfl

/-- Independent oracle instances demonstrate why initial gas must index the
reader. This is not evidence of target-execution oracle agreement. -/
def gasOracle (supply : Word) : Oracle artifact := fun query =>
  match query.kind with
  | .gasleft | .gas => supply
  | .msize | .pc => 0

def gasQuery : Query artifact := ⟨runtimeRef, 0, .gasleft⟩

theorem resource_index_required : gasOracle 5 gasQuery ≠ gasOracle 6 gasQuery := by
  decide

def scalarValue : Observation → Option Word
  | .scalar _ value => some value
  | _ => none

def logData : Observation → Bytes
  | .log entry => entry.data
  | _ => []

def codeData : Observation → Bytes
  | .code _ bytes => bytes
  | _ => []

/-- Gas values may differ, while gas-read occurrence/kind is retained. -/
theorem gas_values_only :
    Observation.withoutGas (.scalar .gasleft 5) =
      Observation.withoutGas (.scalar .gasleft 6) ∧
    (.scalar .gasleft 5 : Observation) ≠ .scalar .gasleft 6 := by
  refine ⟨rfl, ?_⟩
  intro equality
  have values : some (5 : Word) = some 6 := congrArg scalarValue equality
  exact (by decide : (5 : Word) ≠ 6) (Option.some.inj values)

/-- `pc` is artifact-dependent, but D6 does not permit changing its value. -/
theorem pc_stays_exact :
    Observation.withoutGas (.scalar .pc 5) ≠
      Observation.withoutGas (.scalar .pc 6) := by
  intro equality
  have values : some (5 : Word) = some 6 := congrArg scalarValue equality
  exact (by decide : (5 : Word) ≠ 6) (Option.some.inj values)

def firstLog : Log := ⟨Address.zero, [1, 2], by decide, [0, 0xff]⟩
def changedLog : Log := ⟨Address.zero, [1, 2], by decide, [1, 0xff]⟩

theorem log_bytes_not_erased :
    Observation.withoutGas (.log firstLog) ≠
      Observation.withoutGas (.log changedLog) := by
  intro equality
  have bytes : ([0, 0xff] : Bytes) = [1, 0xff] := congrArg logData equality
  exact (by decide : ([0, 0xff] : Bytes) ≠ [1, 0xff]) bytes

theorem code_bytes_not_erased :
    Observation.withoutGas (.code Address.zero [0x60, 1]) ≠
      Observation.withoutGas (.code Address.zero [0x60, 2]) := by
  intro equality
  have bytes : ([0x60, 1] : Bytes) = [0x60, 2] := congrArg codeData equality
  exact (by decide : ([0x60, 1] : Bytes) ≠ [0x60, 2]) bytes

/-- Gas, logs, exact raw call bytes, code/codehash and physical reads coexist
in one ordered prefix. Only the supplied gas value changes under normalization. -/
def combined (gas : Word) : Prefix Observation Outcome :=
  ⟨[.log firstLog,
    .session (.call Address.zero 0 [0, 0xff, 0] false),
    .scalar .gasleft gas,
    .code Address.zero [0x60, 0x02, 0x00],
    .codehash Address.zero 7,
    .memory 0x5f 0x80,
    .slot Address.zero .storage 0 0xab,
    .slot Address.zero .transient 0 0xcd],
    some (.success [0, 0xff])⟩

theorem combined_gas_change : eraseGas (combined 5) = eraseGas (combined 6) := rfl

theorem combined_count_and_outcome :
    (eraseGas (combined 5)).events.length = 8 ∧
    (eraseGas (combined 5)).final = some (.success [0, 0xff]) := ⟨rfl, rfl⟩

/-- The actual target producer must prove this obligation for its creation
execution. This toy implementation exercises both branches of the interface. -/
def toyCreation (initcode runtime : Bytes) : Evm.Halt :=
  if initcode.length ≤ 49152 ∧ runtime.length ≤ 24576 then .success runtime else .exceptional

theorem toy_creation_size_failures : CreationSizeFailures toyCreation := by
  intro initcode runtime oversized
  change ¬ (initcode.length ≤ 49152 ∧ runtime.length ≤ 24576) at oversized
  simp only [toyCreation, if_neg oversized, Evm.Halt.observe]

theorem creation_boundary_fits :
    creationFits (List.replicate 49152 0) (List.replicate 24576 0) := by
  simp only [creationFits, List.length_replicate]
  exact ⟨Nat.le_refl _, Nat.le_refl _⟩

/-- Exact boundary success with nonempty runtime rules out an always-reverting
implementation as a substitute for this inhabited toy control. -/
theorem toy_creation_boundary_success :
    toyCreation (List.replicate 49152 0) (List.replicate 24576 0) =
      .success (List.replicate 24576 0) := by
  have fits : (List.replicate 49152 (0 : UInt8)).length ≤ 49152 ∧
      (List.replicate 24576 (0 : UInt8)).length ≤ 24576 := creation_boundary_fits
  exact if_pos fits

theorem oversized_initcode_refused : ¬ creationFits (List.replicate 49153 0) [] := by
  simp only [creationFits, List.length_replicate, List.length_nil]
  omega

theorem oversized_runtime_refused : ¬ creationFits [] (List.replicate 24577 0) := by
  simp only [creationFits, List.length_replicate, List.length_nil]
  omega

/-- A producer that ignores code-size limits cannot satisfy the failure
obligation, even though it returns well-formed bytes. -/
theorem always_success_refuted :
    ¬ CreationSizeFailures (fun _ runtime => Evm.Halt.success runtime) := by
  intro certificate
  have failure := certificate (List.replicate 49153 0) [] oversized_initcode_refused
  have impossible : true = false := congrArg Prod.fst failure
  cases impossible

/-- Reordering two distinct logs remains observable after gas normalization. -/
theorem log_order_not_erased :
    eraseGas ⟨[.log firstLog, .log changedLog], none⟩ ≠
      eraseGas ⟨[.log changedLog, .log firstLog], none⟩ := by
  intro equality
  have bytes : ([[0, 0xff], [1, 0xff]] : List Bytes) = [[1, 0xff], [0, 0xff]] :=
    congrArg (fun p : Prefix Observation Outcome => p.events.map logData) equality
  exact (by decide : ([[0, 0xff], [1, 0xff]] : List Bytes) ≠
    [[1, 0xff], [0, 0xff]]) bytes

/-- The quotient cannot turn a revert into success or alter its raw bytes. -/
theorem outcome_not_erased (a b : Prefix Observation Outcome)
    (different : a.final ≠ b.final) : eraseGas a ≠ eraseGas b := by
  intro equality
  have finals : (eraseGas a).final = (eraseGas b).final :=
    congrArg (fun p : Prefix Observation Outcome => p.final) equality
  exact different finals

end Solidity.FullScope.VX1Controls

/- The following commands inventory actual kernel dependencies. They are not
pins and do not change the repository trust inventory. -/
#print axioms Solidity.Roadmap.FullScope.eraseGas_idempotent
#print axioms Solidity.Roadmap.FullScope.eraseGas_le
#print axioms Solidity.Roadmap.FullScope.optimizes_of_refines
#print axioms Solidity.FullScope.VX1Controls.memory_witness
#print axioms Solidity.FullScope.VX1Controls.resource_index_required
#print axioms Solidity.FullScope.VX1Controls.gas_values_only
#print axioms Solidity.FullScope.VX1Controls.pc_stays_exact
#print axioms Solidity.FullScope.VX1Controls.log_bytes_not_erased
#print axioms Solidity.FullScope.VX1Controls.code_bytes_not_erased
#print axioms Solidity.FullScope.VX1Controls.combined_gas_change
#print axioms Solidity.FullScope.VX1Controls.toy_creation_size_failures
#print axioms Solidity.FullScope.VX1Controls.creation_boundary_fits
#print axioms Solidity.FullScope.VX1Controls.oversized_initcode_refused
#print axioms Solidity.FullScope.VX1Controls.oversized_runtime_refused
#print axioms Solidity.FullScope.VX1Controls.always_success_refuted
#print axioms Solidity.FullScope.VX1Controls.log_order_not_erased
#print axioms Solidity.FullScope.VX1Controls.outcome_not_erased

#print axioms Solidity.FullScope.VX1Controls.toy_creation_boundary_success


/-! H38 run-indexed toy. This is an inhabited model of the proposed interface,
not a source/EVM producer implementation or a gas-cost correctness proof. -/
namespace Solidity.FullScope.VX1Controls.RunIndexedToy

open Solidity.Roadmap Solidity.Roadmap.FullScope Solidity.Roadmap.FullScope.RunIndexed

def query? (art : Artifact) : Option (Query art) :=
  if present : 0 < art.contracts.length then
    some ⟨⟨⟨0, present⟩, .runtime⟩, 0, .gasleft⟩
  else none

def transcript (art : Artifact) (oracle : Oracle art) : List (Query art × Word) :=
  match query? art with
  | none => []
  | some query => [(query, oracle query)]

def execution (art : Artifact) (oracle : Oracle art) : Prefix Observation Outcome :=
  match query? art with
  | none => ⟨[], some (.revert [])⟩
  | some query =>
    ⟨[.scalar query.kind (oracle query)], some (.success [UInt8.ofNat (oracle query).val])⟩

/-- The source reads the artifact/oracle parameter; its denotation does not
call a compiler or target execution. Word resources denote fixed gas supplies. -/
def source : Source where
  Resolved := Unit
  lang := {
    Prog := Inputs
    Env := Unit
    Res := Word
    resLE := ⟨fun a b => a = b⟩
    Allowed := fun _ => True
    Admissible := fun _ => True
    sem := fun input _ _ => execution input.artifact input.oracle
    consistent := fun _ _ _ _ _ => Prefix.Le.refl _
    Forward := fun input _ _ => ∀ query, query? input.artifact = some query → input.oracle query ≠ 0
    Guard := fun _ _ _ => True }
  meaning := fun _ input => input

/-- An independent toy target with a gas-supply-indexed reader. -/
def target : Target where
  lang := {
    Prog := Artifact
    Env := Unit
    Res := Word
    resLE := ⟨fun a b => a = b⟩
    Allowed := fun _ => True
    Admissible := fun _ => True
    sem := fun art _ supply => execution art (fun _ => supply)
    consistent := by
      intro art env supply supply' same
      cases same
      exact Prefix.Le.refl _
    Forward := fun _ _ _ => True
    Guard := fun _ _ _ => True }
  load := fun art => art
  read := fun _ _ supply _ => supply

/-- Independent source oracle/resource law on its one executed query. -/
def legal {resolved : source.Resolved} {art : Artifact}
    (run : SourceIndex source resolved art) : Prop :=
  ∀ query, query? art = some query → run.oracle query = run.resource

theorem transcript_observations (art : Artifact) (oracle : Oracle art) :
    (transcript art oracle).map (fun entry => (entry.1.kind, entry.2)) =
      (execution art oracle).events.filterMap scalarRead := by
  cases choice : query? art <;> simp only [transcript, execution, choice] <;> rfl

theorem transcript_reads (art : Artifact) (oracle : Oracle art)
    (query : Query art) (value : Word) (observed : (query, value) ∈ transcript art oracle) :
    oracle query = value := by
  cases choice : query? art with
  | none => simp only [transcript, choice, List.not_mem_nil] at observed
  | some actual =>
    simp only [transcript, choice, List.mem_singleton] at observed
    have sameQuery : query = actual := congrArg (fun entry : Query art × Word => entry.1) observed
    have sameValue : value = oracle actual := congrArg (fun entry : Query art × Word => entry.2) observed
    subst query
    exact sameValue.symm

def domain : SourceRuns source where
  Admitted := fun _ => True
  Specified := fun _ _ run => legal run
  Legal := fun _ _ run => legal run
  queries := fun _ art run => transcript art run.oracle
  observations := fun _ art run _ => transcript_observations art run.oracle
  reads := fun _ art run _ query value observed => transcript_reads art run.oracle query value observed

def machine : TargetRuns target where
  queries := fun art run => transcript art (fun _ => run.resource)
  observations := fun art run => transcript_observations art (fun _ => run.resource)
  reads := fun art run query value observed =>
    transcript_reads art (fun _ => run.resource) query value observed

/-- Resource alignment is operational equality of supplies, not a refinement
predicate. Both independent resource sets contain every Word supply. -/
def aligned (_resolved : source.Resolved) (_art : Artifact)
    (sourceRun : SourceIndex source _resolved _art)
    (targetRun : TargetIndex target _art) : Prop := sourceRun.resource = targetRun.resource

def compiler (_ : source.Resolved) : Option Artifact := some artifact

def sourceRun (supply : Word) : SourceIndex source () artifact :=
  ⟨(), supply, fun _ => supply⟩

def targetRun (supply : Word) : TargetIndex target artifact := ⟨(), supply⟩

theorem source_run_eligible (supply : Word) : domain.Eligible (sourceRun supply) :=
  ⟨fun _ _ => rfl, trivial, trivial⟩

theorem gas_supplies_distinct :
    (sourceRun 5).execution.final = some (.success [5]) ∧
    (sourceRun 6).execution.final = some (.success [6]) ∧
    (targetRun 5).execution.final ≠ (targetRun 6).execution.final := by
  exact ⟨rfl, rfl, by decide⟩


theorem transcript_eq_supply {resolved : source.Resolved} {art : Artifact}
    (run : SourceIndex source resolved art) (valid : legal run) :
    transcript art run.oracle = transcript art (fun _ => run.resource) := by
  cases choice : query? art with
  | none => simp only [transcript, choice]
  | some query => simp only [transcript, choice, valid query choice]

theorem execution_eq_supply {resolved : source.Resolved} {art : Artifact}
    (run : SourceIndex source resolved art) (valid : legal run) (env : target.lang.Env) :
    run.execution = (⟨env, run.resource⟩ : TargetIndex target art).execution := by
  change execution art run.oracle = execution art (fun _ => run.resource)
  cases choice : query? art with
  | none => simp only [execution, choice]
  | some query => simp only [execution, choice, valid query choice]

theorem coupled_supply {resolved : source.Resolved} {art : Artifact}
    (run : SourceIndex source resolved art) (valid : legal run) (env : target.lang.Env)
    (sameEnv : run.environment = env) (direction : Direction) :
    Coupled domain machine id aligned direction run (⟨env, run.resource⟩ : TargetIndex target art) := by
  refine ⟨⟨sameEnv, rfl⟩, ?_⟩
  have same : domain.queries resolved art run =
      machine.queries art (⟨env, run.resource⟩ : TargetIndex target art) :=
    transcript_eq_supply run valid
  cases direction <;> change _ <+: _ <;> rw [same] <;> exact List.prefix_refl _

def canonical {resolved : source.Resolved} {art : Artifact}
    (run : TargetIndex target art) : SourceIndex source resolved art :=
  ⟨run.environment, run.resource, fun _ => run.resource⟩

theorem canonical_eligible {resolved : source.Resolved} {art : Artifact}
    (run : TargetIndex target art) : domain.Eligible (canonical (resolved := resolved) run) :=
  ⟨fun _ _ => rfl, trivial, trivial⟩

/-- Inhabited exact two-sided certificate. Coverage quantifies every source and
target Word resource, and need preserves the source's already fixed supply. -/
def certificate : Certificate source target domain machine compiler id aligned .exact where
  admission := fun _ => ⟨fun _ => rfl, fun _ => trivial⟩
  envSound := fun _ _ => trivial
  envOnto := fun env _ => ⟨env, trivial, rfl⟩
  legality := fun _ _ _ _ => Iff.rfl
  sourceResourceCoverage := fun _ _ _ _ resource _ _ =>
    ⟨fun _ => resource, fun _ _ => rfl⟩
  need := fun _ _ _ run _ _ _ _ => run.resource
  sourceCoverage := by
    intro resolved art compiled run eligible env allowed sameEnv
    exact ⟨⟨trivial, trivial⟩, ⟨sameEnv, rfl⟩⟩
  targetCoverage := by
    intro resolved art compiled run eligible
    exact ⟨canonical run, canonical_eligible run, ⟨rfl, rfl⟩⟩
  forward := by
    intro resolved art compiled run eligible env allowed sameEnv forward guard
    refine ⟨trivial, trivial, coupled_supply run eligible.1 env sameEnv .forward, ?_⟩
    change run.execution.Le (⟨env, run.resource⟩ : TargetIndex target art).execution
    rw [execution_eq_supply run eligible.1 env]
    exact Prefix.Le.refl _
  backward := by
    intro resolved art compiled run eligible guard
    refine ⟨canonical run, canonical_eligible run,
      coupled_supply (canonical run) (canonical_eligible run).1 run.environment rfl .backward,
      trivial, ?_⟩
    change run.execution.Le (canonical run).execution
    have same : (canonical (resolved := resolved) run).execution = run.execution := rfl
    rw [same]
    exact Prefix.Le.refl _

/-- Swapping resource supplies cannot preserve operational run binding. -/
theorem swapped_supply_refused : ¬ Bound id aligned (sourceRun 5) (targetRun 6) := by
  intro bound
  exact (by decide : (5 : Word) ≠ 6) bound.resources

/-- The reader agreement lemma also rejects swapped supplies independently of
the resource-alignment test whenever the source gas query is observed. -/
theorem swapped_reader_refused :
    ¬ Coupled domain machine id (fun _ _ _ _ => True) .forward (sourceRun 5) (targetRun 6) := by
  intro coupled
  have observed : (gasQuery, (5 : Word)) ∈ domain.queries () artifact (sourceRun 5) := by
    exact List.mem_singleton_self _
  have agreement := coupled.forward_oracle_agrees (source_run_eligible 5).1 observed
  exact (by decide : (5 : Word) ≠ 6) agreement

/-- A target prefix cut after q0 may have a source extension with q1. Direction
is important: backward admits that cut; forward cannot skip the second query. -/
theorem backward_cut_allowed :
    Direction.Ordered .backward [(gasQuery, (5 : Word)), ({ gasQuery with occurrence := 1 }, 4)]
      [(gasQuery, 5)] := ⟨[({ gasQuery with occurrence := 1 }, 4)], rfl⟩

theorem forward_cut_refused :
    ¬ Direction.Ordered .forward [(gasQuery, (5 : Word)), ({ gasQuery with occurrence := 1 }, 4)]
      [(gasQuery, 5)] := by
  intro ordered
  have impossible : 2 ≤ 1 := List.IsPrefix.length_le ordered
  omega

/-- Candidate legality selecting only zero-valued gas oracles still covers
all resource words, but erases the independently specified positive runs. -/
def filteredDomain : SourceRuns source :=
  { domain with
    Legal := fun _ art run => ∀ query, query? art = some query → run.oracle query = 0
    observations := fun _ art run _ => transcript_observations art run.oracle
    reads := fun _ art run _ query value observed => transcript_reads art run.oracle query value observed }

theorem filtered_resource_coverage (resource : Word) :
    ∃ oracle, filteredDomain.Legal () artifact ⟨(), resource, oracle⟩ :=
  ⟨fun _ => 0, fun _ _ => rfl⟩

theorem filtered_forward_false (resource : Word) :
    ¬ source.lang.Forward (⟨artifact, fun _ => 0⟩ : Inputs) () resource := by
  intro forward
  exact (forward gasQuery rfl) rfl

theorem source_run_forward (supply : Word) (positive : supply ≠ 0) :
    source.lang.Forward (sourceRun supply).program () supply := fun _ _ => positive

/-- Unconditional equality with the independent source judgment rejects the
zero-oracle filter, even though its resource coverage above is total. -/
theorem specified_run_cannot_be_filtered :
    ¬ Nonempty (Certificate source target filteredDomain machine compiler id aligned .exact) := by
  intro existsCertificate
  obtain ⟨alleged⟩ := existsCertificate
  have specified : filteredDomain.Specified () artifact (sourceRun 5) :=
    (source_run_eligible 5).1
  have legalRun := (alleged.legality () artifact rfl (sourceRun 5)).2 specified
  have impossible : (5 : Word) = 0 := legalRun gasQuery rfl
  exact (by decide : (5 : Word) ≠ 0) impossible

def reverting : Target where
  lang := { target.lang with
    sem := fun art env resource =>
      { target.lang.sem art env resource with final := some (.revert []) }
    consistent := by
      intro art env resource resource' same
      cases same
      exact Prefix.Le.refl _ }
  load := fun art => art
  read := fun _ _ supply _ => supply

def revertingMachine : TargetRuns reverting where
  queries := fun art run => transcript art (fun _ => run.resource)
  observations := fun art run => transcript_observations art (fun _ => run.resource)
  reads := fun art run query value observed =>
    transcript_reads art (fun _ => run.resource) query value observed

def revertingAligned (resolved : source.Resolved) (art : Artifact)
    (sourceRun : SourceIndex source resolved art)
    (targetRun : TargetIndex reverting art) : Prop := sourceRun.resource = targetRun.resource

/-- Same actual gas reads and resource supplies do not excuse an always-revert
target: exact source adequacy must transfer the nonempty successful outcome. -/
theorem always_reverting_refused :
    ¬ Nonempty (Certificate source reverting domain revertingMachine compiler id revertingAligned .exact) := by
  intro existsCertificate
  obtain ⟨alleged⟩ := existsCertificate
  have forward := alleged.forward () artifact rfl (sourceRun 5) (source_run_eligible 5)
    () trivial rfl (source_run_forward 5 (by decide)) trivial
  have same := forward.2.2.2.final_eq
    (show (Mode.exact.observe (sourceRun 5).execution).final = some (.success [5]) from rfl)
  have impossible : (some (.revert []) : Option Outcome) = some (.success [5]) :=
    congrArg (fun p : Prefix Observation Outcome => p.final) same
  cases impossible


def otherArtifact : Artifact := ⟨[⟨[0x60, 2], [0], []⟩], 0⟩

/-- An artifact with the same table length but different bytes cannot be
substituted for the compiler output used to index a certificate run. -/
theorem wrong_artifact_refused : compiler () ≠ some otherArtifact := by
  intro equality
  have bytes : ([0x60, 1] : Bytes) = [0x60, 2] :=
    congrArg (fun art : Artifact => art.initcode 0) (Option.some.inj equality)
  exact (by decide : ([0x60, 1] : Bytes) ≠ [0x60, 2]) bytes

end Solidity.FullScope.VX1Controls.RunIndexedToy


#print axioms Solidity.Roadmap.FullScope.RunIndexed.Coupled.forward_oracle_agrees
#print axioms Solidity.Roadmap.FullScope.RunIndexed.Coupled.backward_oracle_agrees
#print axioms Solidity.FullScope.VX1Controls.RunIndexedToy.transcript_observations
#print axioms Solidity.FullScope.VX1Controls.RunIndexedToy.transcript_reads
#print axioms Solidity.FullScope.VX1Controls.RunIndexedToy.source_run_eligible
#print axioms Solidity.FullScope.VX1Controls.RunIndexedToy.gas_supplies_distinct
#print axioms Solidity.FullScope.VX1Controls.RunIndexedToy.transcript_eq_supply
#print axioms Solidity.FullScope.VX1Controls.RunIndexedToy.execution_eq_supply
#print axioms Solidity.FullScope.VX1Controls.RunIndexedToy.coupled_supply
#print axioms Solidity.FullScope.VX1Controls.RunIndexedToy.canonical_eligible
#print axioms Solidity.FullScope.VX1Controls.RunIndexedToy.certificate
#print axioms Solidity.FullScope.VX1Controls.RunIndexedToy.swapped_supply_refused
#print axioms Solidity.FullScope.VX1Controls.RunIndexedToy.swapped_reader_refused
#print axioms Solidity.FullScope.VX1Controls.RunIndexedToy.backward_cut_allowed
#print axioms Solidity.FullScope.VX1Controls.RunIndexedToy.forward_cut_refused
#print axioms Solidity.FullScope.VX1Controls.RunIndexedToy.filtered_resource_coverage
#print axioms Solidity.FullScope.VX1Controls.RunIndexedToy.filtered_forward_false
#print axioms Solidity.FullScope.VX1Controls.RunIndexedToy.source_run_forward
#print axioms Solidity.FullScope.VX1Controls.RunIndexedToy.specified_run_cannot_be_filtered
#print axioms Solidity.FullScope.VX1Controls.RunIndexedToy.always_reverting_refused
#print axioms Solidity.FullScope.VX1Controls.RunIndexedToy.wrong_artifact_refused
