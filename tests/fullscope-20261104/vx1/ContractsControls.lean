import Solidity.Roadmap.Contracts

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
