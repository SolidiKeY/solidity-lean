import Solidity.Language.EnvironmentFields.Frozen
import Solidity.Language.EnvironmentFields.ContractControls

/-!
# Joint satisfiability and negative controls of the frozen D1–D6 contracts

`witness` inhabits the whole `V1.Contract` bundle with one toy model: an
admitted input, a source run with an executed gas query whose oracle is the
target's gas supply, a successful completion, a creation attempt that both
succeeds at the limits and fails above them, a one-field storage layout with
byte memory, and an unsafe assembly block. The hypotheses of D1–D6 are
therefore jointly satisfiable with live domains (H62/H69). The negative
controls show that the bundle rejects a compiler that compiles nothing, an
always-reverting target, an empty or shifted physical relation, overlapping
fields, and an optimizer that rewrites unsafe blocks.

These are interface models, not Source/EVM producer certificates.
-/

namespace Solidity.Roadmap.FullScope.V1.Controls

open Solidity.Roadmap Solidity.Roadmap.FullScope Solidity.Roadmap.FullScope.RunIndexed

/-! ## The run model (D1, D5, D6) -/

def artifact : Artifact :=
  ⟨[⟨[0x60, 0x01], [0x60, 0x02, 0x00], []⟩], 0⟩

def gasQuery : Query artifact := ⟨⟨⟨0, by decide⟩, .runtime⟩, 0, .gasleft⟩

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

/-- The source reads its artifact/oracle input; it calls no compiler and no
target execution. A `Word` resource is a gas supply. -/
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

/-- An independent target whose reader is indexed by its gas supply. -/
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

/-- The source's own oracle law: the executed gas query reads the supply. -/
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
    have sameValue : value = oracle actual :=
      congrArg (fun entry : Query art × Word => entry.2) observed
    subst query
    exact sameValue.symm

def domain : SourceRuns source where
  Admitted := fun _ => True
  Specified := fun _ _ run => legal run
  Legal := fun _ _ run => legal run
  queries := fun _ art run => transcript art run.oracle
  observations := fun _ art run _ => transcript_observations art run.oracle
  reads := fun _ art run _ query value observed =>
    transcript_reads art run.oracle query value observed

def machine : TargetRuns target where
  queries := fun art run => transcript art (fun _ => run.resource)
  observations := fun art run => transcript_observations art (fun _ => run.resource)
  reads := fun art run query value observed =>
    transcript_reads art (fun _ => run.resource) query value observed

/-- Operational alignment: equal gas supplies, not a refinement predicate. -/
def aligned : Alignment source target :=
  fun _ _ sourceRun targetRun => sourceRun.resource = targetRun.resource

def compiler (_ : source.Resolved) : Option Artifact := some artifact

def sourceRun (supply : Word) : SourceIndex source () artifact :=
  ⟨(), supply, fun _ => supply⟩

theorem source_run_eligible (supply : Word) : domain.Eligible (sourceRun supply) :=
  ⟨fun _ _ => rfl, trivial, trivial⟩

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
    Coupled domain machine id aligned direction run
      (⟨env, run.resource⟩ : TargetIndex target art) := by
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

/-- D1: the exact run-indexed certificate, over every gas supply. -/
def d1 : D1 source target domain machine compiler id aligned where
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

/-- D6 from D1. -/
def d6 : D6 source target domain machine compiler id aligned := d1.toD6

theorem d5 : D5 source target id := d5_of_certificate d1

/-! ## Creation (D2) -/

def creation (initcode runtime : Bytes) : Evm.Halt :=
  if creationFits initcode runtime then .success runtime else .exceptional

theorem d2_failures : CreationSizeFailures creation := by
  intro initcode runtime oversized
  simp only [creation, if_neg oversized, Evm.Halt.observe]

theorem creation_at_limits :
    creation (List.replicate 49152 0) (List.replicate 24576 0) =
      .success (List.replicate 24576 0) :=
  if_pos (by simp only [creationFits, List.length_replicate]; exact ⟨Nat.le_refl _, Nat.le_refl _⟩)

theorem d2 : D2 creation :=
  ⟨d2_failures, ⟨List.replicate 49152 0, List.replicate 24576 0,
    by simp only [creationFits, List.length_replicate]; exact ⟨Nat.le_refl _, Nat.le_refl _⟩,
    by rw [creation_at_limits]; rfl⟩⟩

/-- An attempt that always fails meets the failure obligation but not D2. -/
theorem always_failing_refused : ¬ D2 (fun _ _ => Evm.Halt.exceptional) := by
  intro alleged
  obtain ⟨_, _, _, succeeds⟩ := alleged.live
  cases succeeds

/-! ## Physical layout (D3) -/

/-- One storage variable in the low byte of slot 0. -/
def lowByte : PackedField := ⟨0, 0, 1, by decide, by decide⟩

def layout : Layout Unit where
  space := fun _ => .storage
  field := fun _ => lowByte
  disjoint := fun a b different _ => absurd (Subsingleton.elim a b) different

/-- The source state is a value and a byte memory; the target state a slot
word and a byte memory. -/
def physical : Physical where
  Var := Unit
  layout := layout
  SourceState := Nat × ByteMemory
  TargetState := Word × ByteMemory
  value := fun s _ => s.1
  extent := fun s => s.2.size
  view := fun s => s.2.data
  slots := fun t _ _ => t.1
  memory := fun t => t.2
  Related := fun s t => s.1 < 256 ∧ t.1.val = s.1 ∧ t.2 = s.2

theorem lowByte_read (w : Word) (small : w.val < 256) : fieldRead lowByte w = w.val := by
  show w.val / 256 ^ 0 % 256 ^ 1 = w.val
  rw [Nat.pow_zero, Nat.div_one, Nat.pow_one]
  exact Nat.mod_eq_of_lt small

theorem d3 : D3 physical where
  agrees := by
    intro s t related
    obtain ⟨small, word, mem⟩ := related
    refine ⟨fun _ => ?_, ?_, fun _ => ?_⟩
    · change s.1 = fieldRead lowByte t.1
      rw [lowByte_read t.1 (word ▸ small), word]
    · change t.2.size = s.2.size
      rw [mem]
    · change s.2.data _ = t.2.data _
      rw [mem]
  total := by
    intro s representable
    have small : s.1 < 256 := representable.1 ()
    exact ⟨(⟨s.1, Nat.lt_trans small (by decide)⟩, s.2), small, rfl, rfl⟩
  live := ⟨((7, ByteMemory.empty) : Nat × ByteMemory),
    fun _ => show 7 < 256 ^ 1 by decide, Nat.zero_le _, rfl, fun _ _ => rfl⟩

/-- A representable source state with a nonzero stored value. -/
theorem d3_live : physical.Representable ((7, ByteMemory.empty) : Nat × ByteMemory) ∧
    physical.Related ((7, ByteMemory.empty) : Nat × ByteMemory) (7, ByteMemory.empty) :=
  ⟨⟨fun _ => show 7 < 256 ^ 1 by decide, Nat.zero_le _, rfl, fun _ _ => rfl⟩, by decide, rfl, rfl⟩

/-! ## Assembly (D4) -/

def boundary : Assembly where
  State := Controls.AssemblyState
  MemOK := Controls.memOK
  executes := FullScope.Controls.assembly
  writeback := Controls.writeback
  Corresponds := Controls.corresponds
  Block := Bool × Bytes
  optimize := Controls.optimize
  isUnsafe := Controls.isUnsafe

theorem d4 : D4 boundary :=
  ⟨Controls.unsafe_writeback, Controls.opaque_preservation,
    ⟨⟨FullScope.Controls.dirtyBefore, FullScope.Controls.dirtyAfter, rfl⟩, ⟨(true, [0x60, 1]), rfl⟩⟩⟩

/-! ## The bundle, inhabited -/

/-- **Joint satisfiability**: every frozen hypothesis at once, exact mode. -/
def witness : Contract source target domain machine compiler id aligned .exact creation
    physical boundary :=
  ⟨d1, ⟨(), trivial⟩, d2, d3, d4⟩

/-- The same model in optimizer mode. -/
def optimizerWitness : Contract source target domain machine compiler id aligned .optimizer
    creation physical boundary :=
  ⟨d6, ⟨(), trivial⟩, d2, d3, d4⟩

/-- The witness is live: an admitted input compiles, its source run executes a
gas query, completes successfully, and the assigned target run completes with
the same observation. -/
theorem witness_live :
    domain.Admitted () ∧ (∃ art, compiler () = some art) ∧
    (sourceRun 5).execution = ⟨[.scalar .gasleft 5], some (.success [5])⟩ ∧
    (targetRunOf witness.run rfl (sourceRun 5) (source_run_eligible 5) () trivial rfl).execution =
      (sourceRun 5).execution := by
  refine ⟨trivial, witness.compiles trivial, rfl, ?_⟩
  exact forward_completes witness.run rfl (sourceRun 5) (source_run_eligible 5) () trivial rfl
    (fun _ _ => show (5 : Word) ≠ 0 by decide) trivial (o := .success [5]) rfl

/-- D1's oracle lemma reads the actual target supply. -/
theorem oracle_live :
    (sourceRun 5).oracle gasQuery = target.read artifact ()
      (targetRunOf d1 rfl (sourceRun 5) (source_run_eligible 5) () trivial rfl).resource
      gasQuery :=
  D1.forward_oracle d1 rfl (sourceRun 5) (source_run_eligible 5) () trivial rfl
    (fun _ _ => show (5 : Word) ≠ 0 by decide) trivial (List.mem_singleton_self _)

/-! ## Negative controls -/

/-- A compiler that compiles nothing, over a domain admitting nothing, has a
certificate but no contract: `admitsSome` fails. -/
theorem nothing_admitted_refused (attempt : Bytes → Bytes → Evm.Halt) (p : Physical)
    (a : Assembly) (mode : Mode) :
    ¬ Nonempty (Contract source target { domain with Admitted := fun _ => False }
      machine (fun _ => none) id aligned mode attempt p a) := by
  intro ⟨alleged⟩
  obtain ⟨_, impossible⟩ := alleged.admitsSome
  exact impossible

/-- A compiler that compiles nothing has no certificate in either mode. -/
theorem rejecting_refused (mode : Mode) :
    ¬ Nonempty (Certificate source target domain machine (fun _ => none) id aligned mode) :=
  V1.rejecting_refused (resolved := ()) trivial

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

def revertingAligned : Alignment source reverting :=
  fun _ _ sourceRun targetRun => sourceRun.resource = targetRun.resource

/-- An always-reverting target has no certificate in either mode: the
quotient keeps outcome bytes. -/
theorem reverting_refused (mode : Mode) :
    ¬ Nonempty (Certificate source reverting domain revertingMachine compiler id
      revertingAligned mode) := by
  intro ⟨alleged⟩
  have same := forward_completes alleged rfl (sourceRun 5) (source_run_eligible 5) () trivial rfl
    (fun _ _ => show (5 : Word) ≠ 0 by decide) trivial (o := .success [5]) (by cases mode <;> rfl)
  have finals := congrArg (fun p : Prefix Observation Outcome => p.final) same
  cases mode <;> cases finals

/-- A target that adds a non-gas observation (a memory byte) before the gas
read, with the same gas reads and outcome. -/
def extraEvent : Target where
  lang := { target.lang with
    sem := fun art env resource =>
      { target.lang.sem art env resource with
        events := .memory 0 0 :: (target.lang.sem art env resource).events }
    consistent := by
      intro art env resource resource' same
      cases same
      exact Prefix.Le.refl _ }
  load := fun art => art
  read := fun _ _ supply _ => supply

def extraEventMachine : TargetRuns extraEvent where
  queries := fun art run => transcript art (fun _ => run.resource)
  observations := fun art run => transcript_observations art (fun _ => run.resource)
  reads := fun art run query value observed =>
    transcript_reads art (fun _ => run.resource) query value observed

def extraEventAligned : Alignment source extraEvent :=
  fun _ _ sourceRun targetRun => sourceRun.resource = targetRun.resource

/-- The gas quotient does not hide an extra non-gas observation: D6 (and D1)
reject a target whose outcome and gas reads agree but which emits one more
memory observation. -/
theorem extra_event_refused (mode : Mode) :
    ¬ Nonempty (Certificate source extraEvent domain extraEventMachine compiler id
      extraEventAligned mode) := by
  intro ⟨alleged⟩
  have same := forward_completes alleged rfl (sourceRun 5) (source_run_eligible 5) () trivial rfl
    (fun _ _ => show (5 : Word) ≠ 0 by decide) trivial (o := .success [5]) (by cases mode <;> rfl)
  have lengths := congrArg (fun p : Prefix Observation Outcome => p.events.length) same
  cases mode <;> cases lengths

/-- An empty physical relation fails D3's totality. -/
theorem empty_relation_refused : ¬ D3 { physical with Related := fun _ _ => False } := by
  intro alleged
  obtain ⟨_, impossible⟩ := alleged.total ((7, ByteMemory.empty) : Nat × ByteMemory) d3_live.1
  exact impossible

/-- A relation that stores the value one higher fails D3's agreement. -/
theorem shifted_relation_refused :
    ¬ D3 { physical with Related := fun s t => s.1 < 255 ∧ t.1.val = s.1 + 1 ∧ t.2 = s.2 } := by
  intro alleged
  have agrees := (alleged.agrees ((7, ByteMemory.empty) : Nat × ByteMemory)
    ((8 : Word), ByteMemory.empty) ⟨by decide, rfl, rfl⟩).1 ()
  change 7 = fieldRead lowByte 8 at agrees
  rw [lowByte_read 8 (by decide)] at agrees
  cases agrees

/-- Two fields overlapping in byte 0 of slot 0 are not disjoint, so no layout
places two variables there. -/
theorem overlap_refused : ¬ fieldsDisjoint lowByte ⟨0, 0, 2, by decide, by decide⟩ := by
  intro disjoint
  rcases disjoint with different | below | below
  · exact different rfl
  · exact absurd below (by decide)
  · exact absurd below (by decide)

/-- An optimizer that rewrites unsafe blocks fails D4. -/
theorem rewriting_optimizer_refused :
    ¬ D4 { boundary with optimize := fun block => (block.1, block.2 ++ [0]) } := by
  intro alleged
  have same := alleged.opaqueBlocks (true, []) rfl
  cases same

end Solidity.Roadmap.FullScope.V1.Controls
