import Solidity.Lowering.V08.TransactionPrefixes
import Solidity.Lowering.V08.CreationSuccessControls
import Solidity.Lowering.V08.Audit

/-! Successive actual transactions, including two distinct failures after a
real installed-constructor/library commit. Tagged existing return types retain
all data; no Source execution or replacement world interpreter is supplied. -/
namespace Solidity.Lowering.V08.PrefixControls
open Solidity.ContractWorld Controls LibraryHandlerControls CreationSuccessControls

abbrev Output := LibraryHandlerControls.Result ⊕ (Unit ⊕ (Handle false ⊕ List Int))
private instance : DecidableEq (Handle false) := fun a b =>
  decidable_of_iff (a.address = b.address) ⟨(by
    cases a; cases b; intro h; cases h; rfl), congrArg Handle.address⟩

private instance outputDecidable : DecidableEq Output := inferInstance
private instance statusDecidable : DecidableEq (TRes Output) := fun a b => by
  cases a with
  | error e =>
    cases b with
    | error f => exact decidable_of_iff (e = f) ⟨congrArg Except.error, Except.error.inj⟩
    | ok v => exact isFalse (fun h => Except.noConfusion h)
  | ok v =>
    cases b with
    | error e => exact isFalse (fun h => Except.noConfusion h)
    | ok u => exact decidable_of_iff (v = u) ⟨congrArg Except.ok, Except.ok.inj⟩

private theorem map_success {α β : Type} (w : World Catalog) (value : α) (tag : α → β) :
    ((.ok (w, value) : TRes (World Catalog × α)).map (fun pair => (pair.1, tag pair.2))) =
      .ok (w, tag value) := rfl

def commit : TransactionFrame Catalog Output := fun w =>
  (commitFrame w).map (fun pair => (pair.1, .inl pair.2))
def failing : TransactionFrame Catalog Output := fun w =>
  (w.call (⟨self⟩ : Handle false) failureEntry HandlerControls.failureCtx).map
    (fun pair => (pair.1, .inr (.inl pair.2)))
def occupied : TransactionFrame Catalog Output := fun w =>
  (w.create false candidate goodCtor ctorCtx).map
    (fun pair => (pair.1, .inr (.inr (.inl pair.2))))
def reading : TransactionFrame Catalog Output := fun w =>
  (readCandidate w).map (fun pair => (pair.1, .inr (.inr (.inr pair.2))))

def commitValue : Output := .inl expected
def readValue : Output := .inr (.inr (.inr [11, 0, 19, 0, 8, 0]))
def h1 : List (TRes Output) := [.ok commitValue]
def h2 : List (TRes Output) := h1 ++ [.error laterHalt]
def h3 : List (TRes Output) := h2 ++ [.error .revert]
def h4 : List (TRes Output) := h3 ++ [.ok readValue]
def frames : List (TransactionFrame Catalog Output) := [commit, failing, occupied, reading]

private theorem extract_failure {α : Type} (run : TRes α) (halt : THalt)
    (checked : run.halt? = some halt) : run = .error halt := by
  cases run with
  | ok value => cases checked
  | error actual =>
    have same : actual = halt := Option.some.inj checked
    cases same
    rfl

theorem commit_reached : commit base.resetTransient = .ok (linked, commitValue) := by
  rw [commit, commit_frame_reached]
  exact map_success linked expected (fun value => (Sum.inl value : Output))

/-- Independently checked at the post-COMMIT reset input, never transplanted
from the base-world failure equation. Real paid call/body/binary revert. -/
theorem paid_failure_reached :
    linked.resetTransient.call (⟨self⟩ : Handle false) failureEntry HandlerControls.failureCtx =
      .error laterHalt := extract_failure _ _ (by decide +kernel)
theorem failing_reached : failing linked.resetTransient = .error laterHalt := by
  rw [failing, paid_failure_reached]; rfl

theorem collision_reached : linked.resetTransient.create false candidate goodCtor ctorCtx =
    .error .revert := extract_failure _ _ (by decide +kernel)
theorem occupied_reached : occupied linked.resetTransient = .error .revert := by
  rw [occupied, collision_reached]; rfl

theorem read_reached : reading linked.resetTransient = .ok (readWorld, readValue) := by
  rw [reading, read_candidate_reached]
  exact map_success readWorld [11, 0, 19, 0, 8, 0] (fun value => (Sum.inr (Sum.inr (Sum.inr value)) : Output))

theorem boundary0 : transactPrefix (α := Output) base [] = (base, []) := transact_prefix_nil base
theorem boundary1 : transactPrefix base [commit] = (linked.resetTransient, h1) := by
  rw [transact_prefix_singleton, World.transact_commit base linked commit commitValue commit_reached]
  exact congrArg (fun history => (linked.resetTransient, history)) (show [.ok commitValue] = h1 from rfl)

theorem second_input : failing (transactPrefix base [commit]).1.resetTransient = .error laterHalt := by
  rw [boundary1, resetTransient_idem]
  exact failing_reached

theorem boundary2 : transactPrefix base [commit, failing] = (linked.resetTransient, h2) := by
  have result := transact_prefix_failure_snoc base [commit] failing laterHalt second_input
  simpa only [boundary1, resetTransient_idem] using result

theorem third_input : occupied (transactPrefix base [commit, failing]).1.resetTransient = .error .revert := by
  rw [boundary2, resetTransient_idem]
  exact occupied_reached

theorem boundary3 : transactPrefix base [commit, failing, occupied] = (linked.resetTransient, h3) := by
  have result := transact_prefix_failure_snoc base [commit, failing] occupied .revert third_input
  simpa only [boundary2, resetTransient_idem] using result

theorem fourth_input : reading (transactPrefix base [commit, failing, occupied]).1.resetTransient =
    .ok (readWorld, readValue) := by
  rw [boundary3, resetTransient_idem]
  exact read_reached

theorem boundary4 : transactPrefix base frames = (readWorld.resetTransient, h4) := by
  have result := transact_prefix_commit_snoc base readWorld [commit, failing, occupied]
    reading readValue fourth_input
  simpa only [boundary3] using result

abbrev FullVector := LibraryHandlerControls.Vector × Option (List Int) × Bool
private instance fullVectorDecidable : DecidableEq FullVector := inferInstance
private instance observedResultDecidable : DecidableEq (FullVector × Output) := inferInstance

def committedVector : FullVector :=
  (([88, 7, 0, 5, 0], [some [11, 0], some [19, 0], some []], installedFlags), some [8, 0], true)
def observeBoundary (fs : List (TransactionFrame Catalog Output)) :=
  (extended (transactPrefix base fs).1, (transactPrefix base fs).2)

private theorem committed_vector_value : extended linked.resetTransient = committedVector := by decide +kernel
private theorem read_vector_value : extended readWorld.resetTransient = committedVector := by decide +kernel

theorem complete_boundaries :
    observeBoundary [] =
      ((([95, 0, 0, 5, 0], [some [0, 0], some [19, 29], some []], flags), none, false), []) ∧
    observeBoundary [commit] = (committedVector, h1) ∧
    observeBoundary [commit, failing] = (committedVector, h2) ∧
    observeBoundary [commit, failing, occupied] = (committedVector, h3) ∧
    observeBoundary frames = (committedVector, h4) := by
  simp only [observeBoundary, boundary0, boundary1, boundary2, boundary3, boundary4,
    committed_vector_value, read_vector_value]
  decide +kernel

theorem exact_history : (transactPrefix base frames).2 =
    [.ok (.inl ([0xb1, 0xb2], [1, 7, 2, 7, 12345])),
      .error (.revertWith (Semantics.encodeError [0x6c, 0, 0xff, 0x48])),
      .error .revert, .ok (.inr (.inr (.inr [11, 0, 19, 0, 8, 0])))] := by
  rw [boundary4]; rfl

theorem history_length : (transactPrefix base frames).2.length = 4 :=
  transact_prefix_length base frames

theorem append_one : transactPrefix base ([commit] ++ [failing, occupied, reading]) =
    ((transactPrefix (transactPrefix base [commit]).1 [failing, occupied, reading]).1,
      (transactPrefix base [commit]).2 ++
        (transactPrefix (transactPrefix base [commit]).1 [failing, occupied, reading]).2) :=
  transact_prefix_append base [commit] [failing, occupied, reading]

theorem append_multiple : transactPrefix base ([commit, failing] ++ [occupied, reading]) =
    ((transactPrefix (transactPrefix base [commit, failing]).1 [occupied, reading]).1,
      (transactPrefix base [commit, failing]).2 ++
        (transactPrefix (transactPrefix base [commit, failing]).1 [occupied, reading]).2) :=
  transact_prefix_append base [commit, failing] [occupied, reading]

theorem failure_keeps_suffix : transactPrefix base (([commit] ++ [failing]) ++ [occupied, reading]) =
    ((transactPrefix (transactPrefix base [commit]).1.resetTransient [occupied, reading]).1,
      (transactPrefix base [commit]).2 ++
        .error laterHalt :: (transactPrefix (transactPrefix base [commit]).1.resetTransient [occupied, reading]).2) :=
  transact_prefix_failure_suffix base [commit] [occupied, reading] failing laterHalt second_input

theorem every_nonempty_boundary_normalized (first : TransactionFrame Catalog Output)
    (rest : List (TransactionFrame Catalog Output)) :
    (transactPrefix base (first :: rest)).1.resetTransient = (transactPrefix base (first :: rest)).1 :=
  transact_prefix_normalized base first rest

theorem empty_is_not_a_boundary : extended (transactPrefix (α := Output) base []).1.resetTransient ≠
    extended (transactPrefix (α := Output) base []).1 := by
  rw [boundary0]; decide +kernel

/-- Actual direct dirty-input reads expose23/12, unlike the transaction reads.
Full balances/store/installation/type vector remains observable in this control. -/
theorem dirty_read_run : (reading linked).toOption.map (fun pair => (extended pair.1, pair.2)) =
    some ((([88, 7, 0, 5, 0], [some [11, 23], some [19, 0], some []], installedFlags), some [8, 12], true),
      .inr (.inr (.inr [11, 23, 19, 0, 8, 12]))) := by decide +kernel

theorem wrong_dirty_input : (reading linked).toOption.map Prod.snd ≠ some readValue := by decide +kernel

theorem wrong_rollback_snapshot : extended (transactPrefix base [commit, failing]).1 ≠
    extended base.resetTransient := by
  rw [boundary2]; decide +kernel

theorem wrong_halt : (transactPrefix base frames).2 ≠
    [.ok commitValue, .error .panic, .error .revert, .ok readValue] := by
  rw [boundary4]; decide +kernel

theorem wrong_status_order : (transactPrefix base frames).2 ≠
    [.ok commitValue, .error .revert, .error laterHalt, .ok readValue] := by
  rw [boundary4]; decide +kernel

/-- Original typed result retained whole, with a derived size observation. -/
def extendOutput (output : Output) : Output × Nat :=
  (output, match output with
    | .inl libraryResult => libraryResult.1.length
    | .inr (.inl _) => 0
    | .inr (.inr (.inl _)) => 1
    | .inr (.inr (.inr values)) => values.length)
def observedFrames := frames.map (fun frame => observeTransactionFrame frame extendOutput)

theorem observed_complete :
    (extended (transactPrefix base observedFrames).1, (transactPrefix base observedFrames).2) =
      (committedVector, [.ok (commitValue, 2), .error laterHalt, .error .revert, .ok (readValue, 6)]) := by
  simp only [observedFrames, transact_prefix_observe, boundary4, read_vector_value]
  rfl

/-- Dropping only the ADDED observation recovers every original ordered value
and exact error, including both real failures between the two successes. -/
theorem observed_recovery :
    (transactPrefix base observedFrames).2.map (fun result => result.map Prod.fst) =
      (transactPrefix base frames).2 := by
  simp only [observedFrames, transact_prefix_observe, boundary4]
  rfl

#print axioms commit_reached
#print axioms paid_failure_reached
#print axioms failing_reached
#print axioms collision_reached
#print axioms occupied_reached
#print axioms read_reached
#print axioms boundary0
#print axioms boundary1
#print axioms second_input
#print axioms boundary2
#print axioms third_input
#print axioms boundary3
#print axioms fourth_input
#print axioms boundary4
#print axioms complete_boundaries
#print axioms exact_history
#print axioms history_length
#print axioms append_one
#print axioms append_multiple
#print axioms failure_keeps_suffix
#print axioms every_nonempty_boundary_normalized
#print axioms empty_is_not_a_boundary
#print axioms dirty_read_run
#print axioms wrong_dirty_input
#print axioms wrong_rollback_snapshot
#print axioms wrong_halt
#print axioms wrong_status_order


/-! Standalone focused audit of the preserved imported inventory. -/
#print axioms Solidity.Lowering.V08.AbiControls.malformed_reason
#print axioms Solidity.Lowering.V08.AbiControls.panic_catch
#print axioms Solidity.Lowering.V08.AbiControls.reason_roundtrip
#print axioms Solidity.Lowering.V08.AbiControls.wrong_panic
#print axioms Solidity.Lowering.V08.CallableMetadata.argsFit_length
#print axioms Solidity.Lowering.V08.CallableMetadata.convert_originTypes
#print axioms Solidity.Lowering.V08.CallableMetadata.function_signature_unique
#print axioms Solidity.Lowering.V08.CallableMetadata.matched_names_length
#print axioms Solidity.Lowering.V08.CallableMetadata.namesMatch_iff
#print axioms Solidity.Lowering.V08.CallableMetadata.paramsOf_unique
#print axioms Solidity.Lowering.V08.CallableMetadata.target_names_length
#print axioms Solidity.Lowering.V08.CallbackControls.callback_after_failure
#print axioms Solidity.Lowering.V08.CallbackControls.callback_committed
#print axioms Solidity.Lowering.V08.CallbackControls.callback_program
#print axioms Solidity.Lowering.V08.CallbackControls.callback_transfer
#print axioms Solidity.Lowering.V08.CallbackControls.callback_wrong_frame
#print axioms Solidity.Lowering.V08.Controls.constructor_caught
#print axioms Solidity.Lowering.V08.Controls.constructor_wrong_snapshot
#print axioms Solidity.Lowering.V08.Controls.decoder_failure
#print axioms Solidity.Lowering.V08.Controls.extension_funded
#print axioms Solidity.Lowering.V08.Controls.funded_call
#print axioms Solidity.Lowering.V08.Controls.funded_rollback
#print axioms Solidity.Lowering.V08.Controls.repeated_reset
#print axioms Solidity.Lowering.V08.Controls.wrong_failure_payload
#print axioms Solidity.Lowering.V08.Controls.wrong_frame
#print axioms Solidity.Lowering.V08.Controls.wrong_payload
#print axioms Solidity.Lowering.V08.CreationSuccessControls.atomic_application
#print axioms Solidity.Lowering.V08.CreationSuccessControls.combined_application
#print axioms Solidity.Lowering.V08.CreationSuccessControls.commit_application
#print axioms Solidity.Lowering.V08.CreationSuccessControls.commit_frame_reached
#print axioms Solidity.Lowering.V08.CreationSuccessControls.commit_repeat
#print axioms Solidity.Lowering.V08.CreationSuccessControls.committed_vector
#print axioms Solidity.Lowering.V08.CreationSuccessControls.creation_and_library_vectors
#print axioms Solidity.Lowering.V08.CreationSuccessControls.creation_reached
#print axioms Solidity.Lowering.V08.CreationSuccessControls.double_payment_run
#print axioms Solidity.Lowering.V08.CreationSuccessControls.exact_payload
#print axioms Solidity.Lowering.V08.CreationSuccessControls.failure_repeat
#print axioms Solidity.Lowering.V08.CreationSuccessControls.failure_then_recreate
#print axioms Solidity.Lowering.V08.CreationSuccessControls.frame_failed
#print axioms Solidity.Lowering.V08.CreationSuccessControls.keep_reached
#print axioms Solidity.Lowering.V08.CreationSuccessControls.later_reached
#print axioms Solidity.Lowering.V08.CreationSuccessControls.library_reached
#print axioms Solidity.Lowering.V08.CreationSuccessControls.library_result_context
#print axioms Solidity.Lowering.V08.CreationSuccessControls.not_recaught
#print axioms Solidity.Lowering.V08.CreationSuccessControls.observed_failure_application
#print axioms Solidity.Lowering.V08.CreationSuccessControls.observed_keep_reached
#print axioms Solidity.Lowering.V08.CreationSuccessControls.read_candidate_reached
#print axioms Solidity.Lowering.V08.CreationSuccessControls.recreate_vector_statuses
#print axioms Solidity.Lowering.V08.CreationSuccessControls.repeat_vector_statuses
#print axioms Solidity.Lowering.V08.CreationSuccessControls.rollback_candidate_read_fails
#print axioms Solidity.Lowering.V08.CreationSuccessControls.rollback_vectors_status
#print axioms Solidity.Lowering.V08.CreationSuccessControls.success_work_failed
#print axioms Solidity.Lowering.V08.CreationSuccessControls.transaction_application
#print axioms Solidity.Lowering.V08.CreationSuccessControls.untouched_accounts
#print axioms Solidity.Lowering.V08.CreationSuccessControls.wrong_continuation_run
#print axioms Solidity.Lowering.V08.CreationSuccessControls.wrong_payload
#print axioms Solidity.Lowering.V08.CreationSuccessControls.wrong_role
#print axioms Solidity.Lowering.V08.CreationSuccessControls.wrong_rollback_snapshot
#print axioms Solidity.Lowering.V08.CreationSuccessControls.wrong_runtime_identity
#print axioms Solidity.Lowering.V08.CreationSuccessControls.wrong_world
#print axioms Solidity.Lowering.V08.CryptoControls.empty_hash
#print axioms Solidity.Lowering.V08.CryptoControls.fixed_transport
#print axioms Solidity.Lowering.V08.CryptoControls.wrong_hash
#print axioms Solidity.Lowering.V08.CryptoControls.wrong_input
#print axioms Solidity.Lowering.V08.CryptoObservations.byte_input_normalize
#print axioms Solidity.Lowering.V08.CryptoObservations.fixed_keccak_bytes
#print axioms Solidity.Lowering.V08.CryptoObservations.fixed_keccak_observation
#print axioms Solidity.Lowering.V08.CryptoObservations.fold_byte_bound
#print axioms Solidity.Lowering.V08.CryptoObservations.keccak_bytes_bound
#print axioms Solidity.Lowering.V08.CryptoObservations.keccak_length_bound
#print axioms Solidity.Lowering.V08.CryptoObservations.keccak_word_bound
#print axioms Solidity.Lowering.V08.CryptoObservations.ofBytes_bound
#print axioms Solidity.Lowering.V08.DeclarationRoles.attach_of_role
#print axioms Solidity.Lowering.V08.DeclarationRoles.library_call_refused
#print axioms Solidity.Lowering.V08.DeclarationRoles.library_create_refused
#print axioms Solidity.Lowering.V08.DeclarationRoles.library_role
#print axioms Solidity.Lowering.V08.DeclarationRoles.other_role
#print axioms Solidity.Lowering.V08.DeclarationRoles.source_library_create_refused
#print axioms Solidity.Lowering.V08.DeclarationRoles.storage_unchanged
#print axioms Solidity.Lowering.V08.EmitControls.dependent_arguments_retained
#print axioms Solidity.Lowering.V08.EmitControls.dependent_read
#print axioms Solidity.Lowering.V08.EmitControls.dropped_effects
#print axioms Solidity.Lowering.V08.EmitControls.effect_order
#print axioms Solidity.Lowering.V08.EmitControls.event3_member
#print axioms Solidity.Lowering.V08.EmitControls.event_member
#print axioms Solidity.Lowering.V08.EmitControls.reordered_failure
#print axioms Solidity.Lowering.V08.EmitControls.reversed_effects
#print axioms Solidity.Lowering.V08.EmitControls.source_arguments_retained
#print axioms Solidity.Lowering.V08.EmitControls.wrong_failure_payload
#print axioms Solidity.Lowering.V08.EnvironmentProjection.balance_projection
#print axioms Solidity.Lowering.V08.EnvironmentProjection.expression_observations
#print axioms Solidity.Lowering.V08.EnvironmentProjection.funds_at_source_address
#print axioms Solidity.Lowering.V08.EnvironmentProjection.lift_lower_address
#print axioms Solidity.Lowering.V08.EnvironmentProjection.lift_lower_word
#print axioms Solidity.Lowering.V08.EnvironmentProjection.lower_lift_address
#print axioms Solidity.Lowering.V08.EnvironmentProjection.lower_lift_word
#print axioms Solidity.Lowering.V08.EnvironmentProjection.request_tx
#print axioms Solidity.Lowering.V08.EnvironmentProjection.reset_funds_projection
#print axioms Solidity.Lowering.V08.EnvironmentProjection.session_funds_endTx
#print axioms Solidity.Lowering.V08.EnvironmentProjection.session_funds_external
#print axioms Solidity.Lowering.V08.EnvironmentProjection.session_funds_installed
#print axioms Solidity.Lowering.V08.EnvironmentProjection.source_outer_rollback_funds
#print axioms Solidity.Lowering.V08.EnvironmentProjection.source_rollback_funds
#print axioms Solidity.Lowering.V08.EnvironmentProjection.state_environment_reset
#print axioms Solidity.Lowering.V08.HandlerControls.argument_bypasses_handler
#print axioms Solidity.Lowering.V08.HandlerControls.atomic_application
#print axioms Solidity.Lowering.V08.HandlerControls.atomic_vector_status
#print axioms Solidity.Lowering.V08.HandlerControls.collision_atomic_vector_status
#print axioms Solidity.Lowering.V08.HandlerControls.collision_failed
#print axioms Solidity.Lowering.V08.HandlerControls.collision_handler_application
#print axioms Solidity.Lowering.V08.HandlerControls.constructor_catchable
#print axioms Solidity.Lowering.V08.HandlerControls.constructor_failed
#print axioms Solidity.Lowering.V08.HandlerControls.constructor_payload_observation
#print axioms Solidity.Lowering.V08.HandlerControls.constructor_prefix_view
#print axioms Solidity.Lowering.V08.HandlerControls.constructor_reason_not_returned
#print axioms Solidity.Lowering.V08.HandlerControls.correct_work_vector
#print axioms Solidity.Lowering.V08.HandlerControls.ctor_input_reached
#print axioms Solidity.Lowering.V08.HandlerControls.dirty_transaction_snapshot
#print axioms Solidity.Lowering.V08.HandlerControls.distinct_halts
#print axioms Solidity.Lowering.V08.HandlerControls.fourth_read_reached
#print axioms Solidity.Lowering.V08.HandlerControls.frame_failed
#print axioms Solidity.Lowering.V08.HandlerControls.guard_work_reached
#print axioms Solidity.Lowering.V08.HandlerControls.handler_failed
#print axioms Solidity.Lowering.V08.HandlerControls.handler_failure_application
#print axioms Solidity.Lowering.V08.HandlerControls.handler_payload_observation
#print axioms Solidity.Lowering.V08.HandlerControls.later_failed
#print axioms Solidity.Lowering.V08.HandlerControls.later_panic_failed
#print axioms Solidity.Lowering.V08.HandlerControls.observed_atomic_status
#print axioms Solidity.Lowering.V08.HandlerControls.observed_handler_failure
#print axioms Solidity.Lowering.V08.HandlerControls.outer_reached
#print axioms Solidity.Lowering.V08.HandlerControls.panic_constructor_application
#print axioms Solidity.Lowering.V08.HandlerControls.panic_constructor_failed
#print axioms Solidity.Lowering.V08.HandlerControls.panic_handler_application
#print axioms Solidity.Lowering.V08.HandlerControls.panic_handler_atomic_vector_status
#print axioms Solidity.Lowering.V08.HandlerControls.panic_not_exhausted_or_diverged
#print axioms Solidity.Lowering.V08.HandlerControls.panic_work_reached
#print axioms Solidity.Lowering.V08.HandlerControls.populated_vectors
#print axioms Solidity.Lowering.V08.HandlerControls.recatch_negative
#print axioms Solidity.Lowering.V08.HandlerControls.recatch_run
#print axioms Solidity.Lowering.V08.HandlerControls.repeated_after_failure_application
#print axioms Solidity.Lowering.V08.HandlerControls.repeated_after_failure_vector
#print axioms Solidity.Lowering.V08.HandlerControls.setup_reached
#print axioms Solidity.Lowering.V08.HandlerControls.skipped_payment
#print axioms Solidity.Lowering.V08.HandlerControls.skipped_payment_run
#print axioms Solidity.Lowering.V08.HandlerControls.static_bypasses_handler
#print axioms Solidity.Lowering.V08.HandlerControls.transaction_application
#print axioms Solidity.Lowering.V08.HandlerControls.transaction_vector_status
#print axioms Solidity.Lowering.V08.HandlerControls.untouched_atomic
#print axioms Solidity.Lowering.V08.HandlerControls.untouched_transaction
#print axioms Solidity.Lowering.V08.HandlerControls.work_reached
#print axioms Solidity.Lowering.V08.HandlerControls.wrong_ancestor_boundary
#print axioms Solidity.Lowering.V08.HandlerControls.wrong_handler_payload
#print axioms Solidity.Lowering.V08.HandlerControls.wrong_snapshot
#print axioms Solidity.Lowering.V08.HandlerControls.wrong_snapshot_run
#print axioms Solidity.Lowering.V08.InheritedControls.base_functions
#print axioms Solidity.Lowering.V08.InheritedControls.base_member
#print axioms Solidity.Lowering.V08.InheritedControls.checked_override
#print axioms Solidity.Lowering.V08.InheritedControls.derived_member
#print axioms Solidity.Lowering.V08.InheritedControls.funded_header
#print axioms Solidity.Lowering.V08.InheritedControls.inherited_payment
#print axioms Solidity.Lowering.V08.InheritedControls.stricter_nonpayable
#print axioms Solidity.Lowering.V08.InheritedControls.wrong_header
#print axioms Solidity.Lowering.V08.InheritedControls.wrong_payability
#print axioms Solidity.Lowering.V08.InheritedMetadata.mutOK_payable
#print axioms Solidity.Lowering.V08.InheritedMetadata.override_enter
#print axioms Solidity.Lowering.V08.InheritedMetadata.override_nonzero_rejected
#print axioms Solidity.Lowering.V08.InheritedMetadata.override_payable
#print axioms Solidity.Lowering.V08.LibraryControls.constructor_installed
#print axioms Solidity.Lowering.V08.LibraryControls.constructor_wrong_store
#print axioms Solidity.Lowering.V08.LibraryControls.delegated_owner
#print axioms Solidity.Lowering.V08.LibraryControls.delegated_wrong_context
#print axioms Solidity.Lowering.V08.LibraryHandlerControls.ancestor_reached
#print axioms Solidity.Lowering.V08.LibraryHandlerControls.atomic_application
#print axioms Solidity.Lowering.V08.LibraryHandlerControls.atomic_vector_status
#print axioms Solidity.Lowering.V08.LibraryHandlerControls.combined_application
#print axioms Solidity.Lowering.V08.LibraryHandlerControls.constructor_failed
#print axioms Solidity.Lowering.V08.LibraryHandlerControls.ctor_input_context
#print axioms Solidity.Lowering.V08.LibraryHandlerControls.ctor_input_reached
#print axioms Solidity.Lowering.V08.LibraryHandlerControls.delegated_reached
#print axioms Solidity.Lowering.V08.LibraryHandlerControls.delegated_vector_context
#print axioms Solidity.Lowering.V08.LibraryHandlerControls.dirty_transient_reuse
#print axioms Solidity.Lowering.V08.LibraryHandlerControls.distinct_payloads
#print axioms Solidity.Lowering.V08.LibraryHandlerControls.double_payment_run
#print axioms Solidity.Lowering.V08.LibraryHandlerControls.exact_payload
#print axioms Solidity.Lowering.V08.LibraryHandlerControls.frame_failed
#print axioms Solidity.Lowering.V08.LibraryHandlerControls.handler_failed
#print axioms Solidity.Lowering.V08.LibraryHandlerControls.later_failed
#print axioms Solidity.Lowering.V08.LibraryHandlerControls.library_account_preserved
#print axioms Solidity.Lowering.V08.LibraryHandlerControls.library_fields_empty
#print axioms Solidity.Lowering.V08.LibraryHandlerControls.mapped_handler_failure
#print axioms Solidity.Lowering.V08.LibraryHandlerControls.no_second_payment
#print axioms Solidity.Lowering.V08.LibraryHandlerControls.observation_retains_result
#print axioms Solidity.Lowering.V08.LibraryHandlerControls.observed_atomic_status
#print axioms Solidity.Lowering.V08.LibraryHandlerControls.observed_combined_application
#print axioms Solidity.Lowering.V08.LibraryHandlerControls.observed_later_failed
#print axioms Solidity.Lowering.V08.LibraryHandlerControls.observed_prefix_reached
#print axioms Solidity.Lowering.V08.LibraryHandlerControls.other_account_preserved
#print axioms Solidity.Lowering.V08.LibraryHandlerControls.populated_vectors
#print axioms Solidity.Lowering.V08.LibraryHandlerControls.read_reached
#print axioms Solidity.Lowering.V08.LibraryHandlerControls.repeat_application
#print axioms Solidity.Lowering.V08.LibraryHandlerControls.repeat_vector_statuses
#print axioms Solidity.Lowering.V08.LibraryHandlerControls.setup_reached
#print axioms Solidity.Lowering.V08.LibraryHandlerControls.static_library_guard
#print axioms Solidity.Lowering.V08.LibraryHandlerControls.transaction_application
#print axioms Solidity.Lowering.V08.LibraryHandlerControls.transaction_vector_status
#print axioms Solidity.Lowering.V08.LibraryHandlerControls.wrong_caller
#print axioms Solidity.Lowering.V08.LibraryHandlerControls.wrong_caller_run
#print axioms Solidity.Lowering.V08.LibraryHandlerControls.wrong_context
#print axioms Solidity.Lowering.V08.LibraryHandlerControls.wrong_context_run
#print axioms Solidity.Lowering.V08.LibraryHandlerControls.wrong_failure_payload
#print axioms Solidity.Lowering.V08.LibraryHandlerControls.wrong_role_guard
#print axioms Solidity.Lowering.V08.LibraryHandlerControls.wrong_rollback_snapshot
#print axioms Solidity.Lowering.V08.LibraryHandlerControls.wrong_runtime_identity
#print axioms Solidity.Lowering.V08.MetadataControls.binding_order
#print axioms Solidity.Lowering.V08.MetadataControls.converted_order
#print axioms Solidity.Lowering.V08.MetadataControls.error_argument_origins
#print axioms Solidity.Lowering.V08.MetadataControls.error_member
#print axioms Solidity.Lowering.V08.MetadataControls.error_parameters
#print axioms Solidity.Lowering.V08.MetadataControls.function_member
#print axioms Solidity.Lowering.V08.MetadataControls.names
#print axioms Solidity.Lowering.V08.MetadataControls.signature
#print axioms Solidity.Lowering.V08.MetadataControls.wrong_argument_order
#print axioms Solidity.Lowering.V08.MetadataControls.wrong_error_order
#print axioms Solidity.Lowering.V08.MetadataControls.wrong_names
#print axioms Solidity.Lowering.V08.MetadataControls.wrong_signature
#print axioms Solidity.Lowering.V08.NestedControls.argument_failure
#print axioms Solidity.Lowering.V08.NestedControls.catch_classification
#print axioms Solidity.Lowering.V08.NestedControls.caught_creation_vector
#print axioms Solidity.Lowering.V08.NestedControls.complete_observation
#print axioms Solidity.Lowering.V08.NestedControls.complete_status
#print axioms Solidity.Lowering.V08.NestedControls.creation_atomic
#print axioms Solidity.Lowering.V08.NestedControls.creation_reached
#print axioms Solidity.Lowering.V08.NestedControls.dirty_read
#print axioms Solidity.Lowering.V08.NestedControls.dirty_transient_reuse
#print axioms Solidity.Lowering.V08.NestedControls.distinct_halts
#print axioms Solidity.Lowering.V08.NestedControls.frame_reached
#print axioms Solidity.Lowering.V08.NestedControls.inner_not_reCaught
#print axioms Solidity.Lowering.V08.NestedControls.middle_failed
#print axioms Solidity.Lowering.V08.NestedControls.middle_reached
#print axioms Solidity.Lowering.V08.NestedControls.middle_tail_dirty
#print axioms Solidity.Lowering.V08.NestedControls.nested_application
#print axioms Solidity.Lowering.V08.NestedControls.outer_reached
#print axioms Solidity.Lowering.V08.NestedControls.populated_snapshots
#print axioms Solidity.Lowering.V08.NestedControls.read_reached
#print axioms Solidity.Lowering.V08.NestedControls.recatch_negative
#print axioms Solidity.Lowering.V08.NestedControls.repeated_application
#print axioms Solidity.Lowering.V08.NestedControls.repeated_dirty_negative
#print axioms Solidity.Lowering.V08.NestedControls.repeated_failure_application
#print axioms Solidity.Lowering.V08.NestedControls.repeated_failure_vector
#print axioms Solidity.Lowering.V08.NestedControls.repeated_reset
#print axioms Solidity.Lowering.V08.NestedControls.second_failed
#print axioms Solidity.Lowering.V08.NestedControls.second_wrong_payload
#print axioms Solidity.Lowering.V08.NestedControls.setup_reached
#print axioms Solidity.Lowering.V08.NestedControls.static_failure
#print axioms Solidity.Lowering.V08.NestedControls.tail_reached
#print axioms Solidity.Lowering.V08.NestedControls.wrong_ancestor
#print axioms Solidity.Lowering.V08.NestedControls.wrong_ancestor_run
#print axioms Solidity.Lowering.V08.NestedControls.wrong_payload
#print axioms Solidity.Lowering.V08.PayableControls.constructor_refused
#print axioms Solidity.Lowering.V08.PayableControls.fallback_flags
#print axioms Solidity.Lowering.V08.PayableControls.fallback_paid
#print axioms Solidity.Lowering.V08.PayableControls.internal_read_not_payable
#print axioms Solidity.Lowering.V08.PayableControls.malformed_receive_refused
#print axioms Solidity.Lowering.V08.PayableControls.noncallable_refused
#print axioms Solidity.Lowering.V08.PayableControls.nonpayable_fallback
#print axioms Solidity.Lowering.V08.PayableControls.nonpayable_function
#print axioms Solidity.Lowering.V08.PayableControls.payable_function
#print axioms Solidity.Lowering.V08.PayableControls.receive_flag
#print axioms Solidity.Lowering.V08.PayableControls.receive_member
#print axioms Solidity.Lowering.V08.PayableControls.receive_paid
#print axioms Solidity.Lowering.V08.PayableControls.wrong_payment
#print axioms Solidity.Lowering.V08.PayableControls.zero_nonpayable
#print axioms Solidity.Lowering.V08.PayableMetadata.attach_none
#print axioms Solidity.Lowering.V08.PayableMetadata.attach_of_flag
#print axioms Solidity.Lowering.V08.PayableMetadata.nonpayable_enter
#print axioms Solidity.Lowering.V08.PayableMetadata.payable_enter_success
#print axioms Solidity.Lowering.V08.PayableMetadata.source_nonpayable_rejected
#print axioms Solidity.Lowering.V08.PayableMetadata.source_payable_entered
#print axioms Solidity.Lowering.V08.ProjectionControls.boundary_roundtrips
#print axioms Solidity.Lowering.V08.ProjectionControls.environment_values
#print axioms Solidity.Lowering.V08.ProjectionControls.exact_inner_reason
#print axioms Solidity.Lowering.V08.ProjectionControls.external_balance_choice
#print axioms Solidity.Lowering.V08.ProjectionControls.inner_observations
#print axioms Solidity.Lowering.V08.ProjectionControls.installed_balance_choice
#print axioms Solidity.Lowering.V08.ProjectionControls.reset_observations
#print axioms Solidity.Lowering.V08.ProjectionControls.source_caught
#print axioms Solidity.Lowering.V08.ProjectionControls.source_dirty
#print axioms Solidity.Lowering.V08.ProjectionControls.source_payments
#print axioms Solidity.Lowering.V08.ProjectionControls.source_reset
#print axioms Solidity.Lowering.V08.ProjectionControls.source_rolled
#print axioms Solidity.Lowering.V08.ProjectionControls.stale_transient
#print axioms Solidity.Lowering.V08.ProjectionControls.target_caught
#print axioms Solidity.Lowering.V08.ProjectionControls.target_dirty
#print axioms Solidity.Lowering.V08.ProjectionControls.target_rolled
#print axioms Solidity.Lowering.V08.ProjectionControls.target_stale_transient
#print axioms Solidity.Lowering.V08.ProjectionControls.wrong_environment
#print axioms Solidity.Lowering.V08.ProjectionControls.wrong_external_balance
#print axioms Solidity.Lowering.V08.ProjectionControls.wrong_inner_frame
#print axioms Solidity.Lowering.V08.ProjectionControls.wrong_reason
#print axioms Solidity.Lowering.V08.RoleControls.library_deployed
#print axioms Solidity.Lowering.V08.RoleControls.library_member
#print axioms Solidity.Lowering.V08.RoleControls.ordinary_creation_refused
#print axioms Solidity.Lowering.V08.RoleControls.other_catalogue_preserved
#print axioms Solidity.Lowering.V08.RoleControls.source_roles
#print axioms Solidity.Lowering.V08.SelectorControls.argument_order
#print axioms Solidity.Lowering.V08.SelectorControls.canonical_error
#print axioms Solidity.Lowering.V08.SelectorControls.distinct_signatures
#print axioms Solidity.Lowering.V08.SelectorControls.error_input
#print axioms Solidity.Lowering.V08.SelectorControls.panic_input
#print axioms Solidity.Lowering.V08.SelectorObservations.beBytes_split
#print axioms Solidity.Lowering.V08.SelectorObservations.beBytes_take
#print axioms Solidity.Lowering.V08.SelectorObservations.selectorBytes_layout
#print axioms Solidity.Lowering.V08.SelectorObservations.selectorBytes_ofNat
#print axioms Solidity.Lowering.V08.SelectorObservations.signature_arguments
#print axioms Solidity.Lowering.V08.SelectorObservations.signature_selector
#print axioms Solidity.Lowering.V08.atomic_tryCreate_handler_steps_failure
#print axioms Solidity.Lowering.V08.atomic_tryCreate_library_handler_failure
#print axioms Solidity.Lowering.V08.atomic_tryCreate_success_continuation_failure
#print axioms Solidity.Lowering.V08.beBytes_layout
#print axioms Solidity.Lowering.V08.beBytes_mod
#print axioms Solidity.Lowering.V08.callFrame_observeEntry
#print axioms Solidity.Lowering.V08.call_observeEntry
#print axioms Solidity.Lowering.V08.call_observeEntry_comp
#print axioms Solidity.Lowering.V08.call_observeEntry_error_iff
#print axioms Solidity.Lowering.V08.catch_error_transport
#print axioms Solidity.Lowering.V08.catch_error_transport_total
#print axioms Solidity.Lowering.V08.errorData_transport
#print axioms Solidity.Lowering.V08.errorData_transport_total
#print axioms Solidity.Lowering.V08.libraryCall_observe
#print axioms Solidity.Lowering.V08.libraryCall_other_accounts
#print axioms Solidity.Lowering.V08.natWordBytes_transport
#print axioms Solidity.Lowering.V08.pad32_transport
#print axioms Solidity.Lowering.V08.panicData_transport
#print axioms Solidity.Lowering.V08.panic_payload_injective
#print axioms Solidity.Lowering.V08.resetTransient_idem
#print axioms Solidity.Lowering.V08.rollback_observation
#print axioms Solidity.Lowering.V08.transact_atomic_descendant
#print axioms Solidity.Lowering.V08.transact_complete_observation
#print axioms Solidity.Lowering.V08.transact_congr
#print axioms Solidity.Lowering.V08.transact_descendant_failure
#print axioms Solidity.Lowering.V08.transact_failure_then_commit
#print axioms Solidity.Lowering.V08.transact_observe
#print axioms Solidity.Lowering.V08.transact_repeat
#print axioms Solidity.Lowering.V08.transact_repeat_failure
#print axioms Solidity.Lowering.V08.transact_tryCreate_handler_steps_failure
#print axioms Solidity.Lowering.V08.transact_tryCreate_library_handler_failure
#print axioms Solidity.Lowering.V08.transact_two_boundaries
#print axioms Solidity.Lowering.V08.transact_wrong_halt
#print axioms Solidity.Lowering.V08.tryCreate_completed_failure
#print axioms Solidity.Lowering.V08.tryCreate_handler_steps_failure
#print axioms Solidity.Lowering.V08.tryCreate_library_handler_failure
#print axioms Solidity.Lowering.V08.tryCreate_library_success_failure
#print axioms Solidity.Lowering.V08.tryCreate_observe
#print axioms Solidity.Lowering.V08.tryCreate_static
#print axioms Solidity.Lowering.V08.tryCreate_success_continuation_failure
#print axioms Solidity.Lowering.V08.wordBytes_transport
#print axioms Solidity.Lowering.V08.wordSequence_transport

/-- Instantiate exact indexed commit at the dirty initial world; World.transact
performs its entry reset, not the empty fold. -/
theorem indexed_commit :
    (transactPrefix base frames).2[0]'(by rw [transact_prefix_length]; decide) = .ok commitValue ∧
    (transactPrefix base (frames.take 1)).1 = linked.resetTransient := by
  have ran : frames[0] (transactPrefix base (frames.take 0)).1.resetTransient = .ok (linked, commitValue) := by
    simpa only [frames, List.take_zero, transact_prefix_nil, List.getElem_cons_zero] using commit_reached
  exact transact_prefix_index_success base linked frames 0 (by decide) commitValue ran

theorem indexed_paid_failure :
    (transactPrefix base frames).2[1]'(by rw [transact_prefix_length]; decide) = .error laterHalt ∧
    (transactPrefix base (frames.take 2)).1 = (transactPrefix base (frames.take 1)).1.resetTransient := by
  apply transact_prefix_index_failure base frames 1 (by decide) laterHalt
  simpa only [frames, List.take_succ_cons, List.take_zero, List.getElem_cons_succ,
    List.getElem_cons_zero] using second_input

theorem indexed_collision :
    (transactPrefix base frames).2[2]'(by rw [transact_prefix_length]; decide) = .error .revert ∧
    (transactPrefix base (frames.take 3)).1 = (transactPrefix base (frames.take 2)).1.resetTransient := by
  apply transact_prefix_index_failure base frames 2 (by decide) .revert
  simpa only [frames, List.take_succ_cons, List.take_zero, List.getElem_cons_succ,
    List.getElem_cons_zero] using third_input

theorem indexed_read :
    (transactPrefix base frames).2[3]'(by rw [transact_prefix_length]; decide) = .ok readValue ∧
    (transactPrefix base (frames.take 4)).1 = readWorld.resetTransient := by
  have ran : frames[3] (transactPrefix base (frames.take 3)).1.resetTransient = .ok (readWorld, readValue) := by
    simpa only [frames, List.take_succ_cons, List.take_zero, List.getElem_cons_succ,
      List.getElem_cons_zero] using fourth_input
  exact transact_prefix_index_success base readWorld frames 3 (by decide) readValue ran

/-- Locality at a middle split preserves the full typed ordered history. -/
theorem middle_locality :
    (transactPrefix base frames).2.take 2 = h2 ∧
    (transactPrefix base frames).2.drop 2 =
      (transactPrefix (transactPrefix base (frames.take 2)).1 (frames.drop 2)).2 := by
  constructor
  · rw [transact_prefix_take_history]; exact congrArg Prod.snd boundary2
  · exact transact_prefix_drop_history base frames 2

/-- Complete prior vector is retained at ALL boundaries, together with the
indexed full values/statuses; no vector is claimed to observe every World field. -/
theorem indexed_complete_vectors :
    (observeBoundary [] =
      ((([95, 0, 0, 5, 0], [some [0, 0], some [19, 29], some []], flags), none, false), []) ∧
    observeBoundary [commit] = (committedVector, h1) ∧
    observeBoundary [commit, failing] = (committedVector, h2) ∧
    observeBoundary [commit, failing, occupied] = (committedVector, h3) ∧
    observeBoundary frames = (committedVector, h4)) ∧
    ((transactPrefix base frames).2[0]'(by rw [transact_prefix_length]; decide) = .ok commitValue ∧
     (transactPrefix base frames).2[1]'(by rw [transact_prefix_length]; decide) = .error laterHalt ∧
     (transactPrefix base frames).2[2]'(by rw [transact_prefix_length]; decide) = .error .revert ∧
     (transactPrefix base frames).2[3]'(by rw [transact_prefix_length]; decide) = .ok readValue) :=
  ⟨complete_boundaries, indexed_commit.1, indexed_paid_failure.1, indexed_collision.1, indexed_read.1⟩

theorem indexed_observed_read :
    (transactPrefix base observedFrames).2[3]'(by
      rw [transact_prefix_length]; decide) = .ok (readValue, 6) := by
  unfold observedFrames
  rw [transact_prefix_index_observe base frames extendOutput 3 (by decide), indexed_read.1]
  rfl

theorem indexed_observed_error :
    (transactPrefix base observedFrames).2[1]'(by
      rw [transact_prefix_length]; decide) = .error laterHalt := by
  unfold observedFrames
  rw [transact_prefix_index_observe base frames extendOutput 1 (by decide), indexed_paid_failure.1]
  rfl

theorem out_of_range_locality :
    (transactPrefix base frames).2.take 7 = h4 ∧
    (transactPrefix base frames).2.drop 7 = [] := by
  rw [boundary4]; decide +kernel

theorem wrong_index :
    (transactPrefix base frames).2[2]'(by rw [transact_prefix_length]; decide) ≠ .error laterHalt := by
  rw [indexed_collision.1]; decide +kernel

theorem shifted_success :
    (transactPrefix base frames).2[0]'(by rw [transact_prefix_length]; decide) ≠ .ok readValue := by
  rw [indexed_commit.1]; decide +kernel

theorem wrong_suffix_order : (transactPrefix base frames).2.drop 1 ≠
    [.error .revert, .error laterHalt, .ok readValue] := by
  rw [boundary4]; decide +kernel

/-- Recover the actual paid binary failure and immediate snapshot from its
recorded middle-history observation. No new execution equality is assumed. -/
theorem paid_history_reconstruction :
    frames[1] (transactPrefix base (frames.take 1)).1.resetTransient = .error laterHalt ∧
      (transactPrefix base (frames.take 2)).1 = (transactPrefix base (frames.take 1)).1.resetTransient :=
  transact_prefix_failure_of_index base frames 1 (by decide) laterHalt indexed_paid_failure.1

theorem collision_history_reconstruction :
    frames[2] (transactPrefix base (frames.take 2)).1.resetTransient = .error .revert ∧
      (transactPrefix base (frames.take 3)).1 = (transactPrefix base (frames.take 2)).1.resetTransient :=
  transact_prefix_failure_of_index base frames 2 (by decide) .revert indexed_collision.1

/-- Actual constructor/library success reconstructed from the exact full
history value. Existence preserves raw transient data until the boundary reset. -/
theorem commit_history_reconstruction :
    ∃ next : World Catalog,
      frames[0] (transactPrefix base (frames.take 0)).1.resetTransient = .ok (next, commitValue) ∧
      (transactPrefix base (frames.take 1)).1 = next.resetTransient :=
  transact_prefix_success_of_index base frames 0 (by decide) commitValue indexed_commit.1

theorem read_history_reconstruction :
    ∃ next : World Catalog,
      frames[3] (transactPrefix base (frames.take 3)).1.resetTransient = .ok (next, readValue) ∧
      (transactPrefix base (frames.take 4)).1 = next.resetTransient :=
  transact_prefix_success_of_index base frames 3 (by decide) readValue indexed_read.1

/-- Reconstruction retains all previous listed fields at EVERY boundary and
both intervening exact errors, not merely a projection of successful values. -/
theorem reconstructed_complete_boundaries :
    (∃ next : World Catalog,
      frames[0] (transactPrefix base (frames.take 0)).1.resetTransient = .ok (next, commitValue) ∧
      (transactPrefix base (frames.take 1)).1 = next.resetTransient) ∧
    (∃ next : World Catalog,
      frames[3] (transactPrefix base (frames.take 3)).1.resetTransient = .ok (next, readValue) ∧
      (transactPrefix base (frames.take 4)).1 = next.resetTransient) ∧
    (observeBoundary [] =
      ((([95, 0, 0, 5, 0], [some [0, 0], some [19, 29], some []], flags), none, false), []) ∧
    observeBoundary [commit] = (committedVector, h1) ∧
    observeBoundary [commit, failing] = (committedVector, h2) ∧
    observeBoundary [commit, failing, occupied] = (committedVector, h3) ∧
    observeBoundary frames = (committedVector, h4)) :=
  ⟨commit_history_reconstruction, read_history_reconstruction, complete_boundaries⟩

theorem wrong_library_success_value :
    (transactPrefix base frames).2[0]'(by rw [transact_prefix_length]; decide) ≠
      .ok (.inl ([0xb1, 0], [1, 7, 2, 7, 12345])) := by
  rw [indexed_commit.1]; decide +kernel

/-- Successful raw constructor/library world actually has dirty transient cells;
it cannot be substituted for the committed boundary world. -/
theorem wrong_raw_reset_world : extended linked ≠ extended (transactPrefix base [commit]).1 := by
  rw [boundary1]; decide +kernel

/-- Actual middle segment after constructor/library commit: both exact errors
and the subsequent full read survive in order, from the reached snapshot. -/
theorem middle_segment_reached :
    transactPrefix linked.resetTransient ((frames.drop 1).take 3) =
      (readWorld.resetTransient, [.error laterHalt, .error .revert, .ok readValue]) := by
  have segment := transact_prefix_segment_complete base frames 1 3
  have preceding : transactPrefix base (frames.take 1) = (linked.resetTransient, h1) := boundary1
  have endpoint : frames.take (1 + 3) = frames := rfl
  rw [preceding, endpoint, boundary4] at segment
  exact segment

/-- Middle segment error reconstruction at its first actual local frame. -/
theorem middle_paid_reconstruction :
    ((frames.drop 1).take 3)[0]
      (transactPrefix (transactPrefix base (frames.take 1)).1
        (((frames.drop 1).take 3).take 0)).1.resetTransient = .error laterHalt ∧
    (transactPrefix (transactPrefix base (frames.take 1)).1
      (((frames.drop 1).take 3).take 1)).1 =
      (transactPrefix (transactPrefix base (frames.take 1)).1
        (((frames.drop 1).take 3).take 0)).1.resetTransient := by
  apply (transact_prefix_segment_error_iff base frames 1 3 0 (by decide) laterHalt).mp
  have history : (transactPrefix base frames).2 = h4 := congrArg Prod.snd boundary4
  simpa only [history] using (show ((h4.drop 1).take 3)[0] = .error laterHalt from rfl)

/-- Middle segment success reconstructs an actual raw read world after BOTH
failures, rather than applying a base-world read equation. -/
theorem middle_read_reconstruction :
    ∃ next : World Catalog,
      ((frames.drop 1).take 3)[2]
        (transactPrefix (transactPrefix base (frames.take 1)).1
          (((frames.drop 1).take 3).take 2)).1.resetTransient = .ok (next, readValue) ∧
      (transactPrefix (transactPrefix base (frames.take 1)).1
        (((frames.drop 1).take 3).take 3)).1 = next.resetTransient := by
  apply (transact_prefix_segment_ok_iff base frames 1 3 2 (by decide) readValue).mp
  have history : (transactPrefix base frames).2 = h4 := congrArg Prod.snd boundary4
  simpa only [history] using (show ((h4.drop 1).take 3)[2] = .ok readValue from rfl)

/-- Entire old boundary vector and ordered histories remain alongside the
complete reached middle-segment observation. -/
theorem middle_complete_vectors :
    (observeBoundary [] =
      ((([95, 0, 0, 5, 0], [some [0, 0], some [19, 29], some []], flags), none, false), []) ∧
    observeBoundary [commit] = (committedVector, h1) ∧
    observeBoundary [commit, failing] = (committedVector, h2) ∧
    observeBoundary [commit, failing, occupied] = (committedVector, h3) ∧
    observeBoundary frames = (committedVector, h4)) ∧
    (extended (transactPrefix linked.resetTransient ((frames.drop 1).take 3)).1,
      (transactPrefix linked.resetTransient ((frames.drop 1).take 3)).2) =
      (committedVector, [.error laterHalt, .error .revert, .ok readValue]) := by
  constructor
  · exact complete_boundaries
  · rw [middle_segment_reached, read_vector_value]

/-- Count-zero preserves its genuinely reached starting world, including dirty
initial state at start0. An empty segment is never an extra reset operation. -/
theorem empty_segment_dirty :
    transactPrefix (transactPrefix base (frames.take 0)).1 ((frames.drop 0).take 0) = (base, []) ∧
    extended (transactPrefix (transactPrefix base (frames.take 0)).1
      ((frames.drop 0).take 0)).1 ≠ extended base.resetTransient := by
  simp only [List.take_zero, transact_prefix_nil]
  decide +kernel

theorem empty_segment_reached :
    transactPrefix (transactPrefix base (frames.take 1)).1 ((frames.drop 1).take 0) =
      (linked.resetTransient, []) := by
  have preceding : transactPrefix base (frames.take 1) = (linked.resetTransient, h1) := boundary1
  rw [preceding]; rfl

theorem truncated_segment :
    transactPrefix (transactPrefix base (frames.take 7)).1 ((frames.drop 7).take 12) =
      (readWorld.resetTransient, []) := by
  have preceding : transactPrefix base (frames.take 7) = (readWorld.resetTransient, h4) := boundary4
  rw [preceding]; rfl

theorem wrong_middle_order : (transactPrefix linked.resetTransient ((frames.drop 1).take 3)).2 ≠
    [.error .revert, .error laterHalt, .ok readValue] := by
  rw [middle_segment_reached]; decide +kernel

/-- Guessed original-base snapshot differs on the full listed vector, even
though both transactions may eventually read successfully. -/
theorem wrong_middle_snapshot : extended (transactPrefix base (frames.take 1)).1 ≠
    extended base.resetTransient := by
  have preceding : transactPrefix base (frames.take 1) = (linked.resetTransient, h1) := boundary1
  rw [preceding]; decide +kernel

theorem extendOutput_injective (first second : Output)
    (same : extendOutput first = extendOutput second) : first = second := congrArg Prod.fst same

/-- Actual observed full history reflects every candidate only because this
observer retains the ENTIRE original typed result (including same-tag bytes). -/
theorem complete_history_reflection (candidate : List (TRes Output)) :
    (transactPrefix base observedFrames).2 = candidate.map (fun result => result.map extendOutput) ↔
      h4 = candidate := by
  simp only [observedFrames, transact_prefix_observe, boundary4]
  exact history_observe_eq_iff extendOutput extendOutput_injective h4 candidate

theorem middle_history_reflection (candidate : List (TRes Output)) :
    (((transactPrefix base observedFrames).2.drop 1).take 3) =
      candidate.map (fun result => result.map extendOutput) ↔
      [.error laterHalt, .error .revert, .ok readValue] = candidate := by
  have reflected := transact_prefix_segment_observe_reflect_iff base frames 1 3
    extendOutput extendOutput_injective candidate
  have history : (transactPrefix base frames).2 = h4 := congrArg Prod.snd boundary4
  simpa only [observedFrames, history] using reflected

/-- All previous listed observations and all four full ordered results remain
at every original boundary alongside injective reflection. -/
theorem reflection_complete_boundaries :
    (observeBoundary [] =
      ((([95, 0, 0, 5, 0], [some [0, 0], some [19, 29], some []], flags), none, false), []) ∧
    observeBoundary [commit] = (committedVector, h1) ∧
    observeBoundary [commit, failing] = (committedVector, h2) ∧
    observeBoundary [commit, failing, occupied] = (committedVector, h3) ∧
    observeBoundary frames = (committedVector, h4)) ∧
    ((extended (transactPrefix base observedFrames).1, (transactPrefix base observedFrames).2) =
      (committedVector, [.ok (commitValue, 2), .error laterHalt, .error .revert, .ok (readValue, 6)])) ∧
    (∀ candidate : List (TRes Output),
      (transactPrefix base observedFrames).2 = candidate.map (fun result => result.map extendOutput) ↔
        h4 = candidate) :=
  ⟨complete_boundaries, observed_complete, complete_history_reflection⟩

def wrongByteValue : Output := .inl ([0xb1, 0], [1, 7, 2, 7, 12345])
def wrongByteHistory : List (TRes Output) :=
  [.ok wrongByteValue, .error laterHalt, .error .revert, .ok readValue]

/-- Lossy constant-success observation merges two different complete histories,
while both exact errors remain in order. Injectivity cannot be dropped. -/
theorem lossy_observer_counterexample :
    (transactPrefix base frames).2.map (fun result => result.map (fun _ : Output => ())) =
      wrongByteHistory.map (fun result => result.map (fun _ : Output => ())) ∧
    (transactPrefix base frames).2 ≠ wrongByteHistory := by
  have history : (transactPrefix base frames).2 = h4 := congrArg Prod.snd boundary4
  rw [history]
  constructor
  · rfl
  · decide +kernel

theorem injective_wrong_success_rejected :
    (transactPrefix base observedFrames).2 ≠ wrongByteHistory.map (fun result => result.map extendOutput) := by
  intro same
  have wrong : h4 = wrongByteHistory := (complete_history_reflection wrongByteHistory).mp same
  have differs : h4 ≠ wrongByteHistory := by decide +kernel
  exact differs wrong

theorem injective_wrong_order_rejected :
    (transactPrefix base observedFrames).2 ≠
      ([.ok commitValue, .error .revert, .error laterHalt, .ok readValue] : List (TRes Output)).map (fun result => result.map extendOutput) := by
  intro same
  have wrong := (complete_history_reflection _).mp same
  have differs : h4 ≠ [.ok commitValue, .error .revert, .error laterHalt, .ok readValue] := by decide +kernel
  exact differs wrong

/-- Pure result adapter on actual frames: funded operations/worlds are retained,
only the library success bytes change. No alternate call interpreter. -/
def wrongByteObserver (output : Output) : Output := match output with
  | .inl libraryResult => .inl ([0xb1, 0], libraryResult.2)
  | other => other
def wrongByteFrames := frames.map (fun frame => observeTransactionFrame frame wrongByteObserver)

/-- The same loss of information also occurs between two ACTUAL transaction
folds with real funded work, not only between an execution and a candidate list. -/
theorem lossy_actual_runs :
    (transactPrefix base (frames.map (fun frame => observeTransactionFrame frame (fun _ : Output => ())))).2 =
      (transactPrefix base (wrongByteFrames.map (fun frame => observeTransactionFrame frame (fun _ : Output => ())))).2 ∧
    (transactPrefix base frames).2 ≠ (transactPrefix base wrongByteFrames).2 := by
  simp only [wrongByteFrames, transact_prefix_observe, boundary4]
  constructor
  · rfl
  · decide +kernel

theorem adjacent_first_reached :
    transactPrefix linked.resetTransient ((frames.drop 1).take 1) =
      (linked.resetTransient, [.error laterHalt]) := by
  have segment := transact_prefix_segment_complete base frames 1 1
  have preceding : transactPrefix base (frames.take 1) = (linked.resetTransient, h1) := boundary1
  have endpoint : transactPrefix base (frames.take (1 + 1)) = (linked.resetTransient, h2) := boundary2
  rw [preceding, endpoint, boundary4] at segment
  exact segment

theorem adjacent_second_reached :
    transactPrefix (transactPrefix base (frames.take 2)).1 ((frames.drop 2).take 2) =
      (readWorld.resetTransient, [.error .revert, .ok readValue]) := by
  have segment := transact_prefix_segment_complete base frames 2 2
  have endpoint : frames.take (2 + 2) = frames := rfl
  rw [endpoint, boundary4] at segment
  exact segment

/-- Both reached adjacent snapshots/histories plus EVERY original boundary
observation; subdivision never projects away either exact error or full return. -/
theorem adjacent_complete_vectors :
    (observeBoundary [] =
      ((([95, 0, 0, 5, 0], [some [0, 0], some [19, 29], some []], flags), none, false), []) ∧
    observeBoundary [commit] = (committedVector, h1) ∧
    observeBoundary [commit, failing] = (committedVector, h2) ∧
    observeBoundary [commit, failing, occupied] = (committedVector, h3) ∧
    observeBoundary frames = (committedVector, h4)) ∧
    ((extended (transactPrefix linked.resetTransient ((frames.drop 1).take 1)).1,
       (transactPrefix linked.resetTransient ((frames.drop 1).take 1)).2),
     (extended (transactPrefix (transactPrefix base (frames.take 2)).1 ((frames.drop 2).take 2)).1,
       (transactPrefix (transactPrefix base (frames.take 2)).1 ((frames.drop 2).take 2)).2)) =
      ((committedVector, [.error laterHalt]), (committedVector, [.error .revert, .ok readValue])) := by
  constructor
  · exact complete_boundaries
  · rw [adjacent_first_reached, adjacent_second_reached, committed_vector_value, read_vector_value]

theorem labelled_partition_reflection (first second : List (TRes Output)) :
    ((((transactPrefix base observedFrames).2.drop 1).take 1) = first.map (fun result => result.map extendOutput) ∧
      (((transactPrefix base observedFrames).2.drop 2).take 2) = second.map (fun result => result.map extendOutput)) ↔
      ([.error laterHalt] = first ∧ [.error .revert, .ok readValue] = second) := by
  have reflected := transact_prefix_partition_reflect_iff base frames 1 1 2 extendOutput
    extendOutput_injective first second
  have history : (transactPrefix base frames).2 = h4 := congrArg Prod.snd boundary4
  simpa only [observedFrames, history] using reflected

/-- The actual first component contains the binary halt, differs from an empty
component, and differs from the shifted plain-error component. -/
theorem wrong_partition :
    (((transactPrefix base frames).2.drop 1).take 1) ≠ [] ∧
    (((transactPrefix base frames).2.drop 1).take 1) ≠
      (((transactPrefix base frames).2.drop 2).take 1) := by
  have history : (transactPrefix base frames).2 = h4 := congrArg Prod.snd boundary4
  rw [history]; decide +kernel

/-- An empty first partition followed by the complete real trace does not reset
the dirty starting world until the first actual World.transact is reached. -/
theorem empty_first_partition :
    transactPrefix (transactPrefix base (frames.take 0)).1 ((frames.drop 0).take (0 + 4)) =
      (readWorld.resetTransient, [] ++ h4) ∧
    extended (transactPrefix base (frames.take 0)).1 ≠ extended base.resetTransient := by
  have input : (transactPrefix base (frames.take 0)).1 = base := by
    rw [List.take_zero, transact_prefix_nil]
  have whole : (frames.drop 0).take (0 + 4) = frames := rfl
  constructor
  · rw [input, whole, List.nil_append, boundary4]
  · rw [input]
    decide +kernel

/-- Requested first length7 naturally consumes only the three remaining frames;
the adjacent segment at index8 is empty at the actually reached final snapshot. -/
theorem truncated_partition :
    transactPrefix linked.resetTransient ((frames.drop 1).take (7 + 3)) =
      (readWorld.resetTransient, [.error laterHalt, .error .revert, .ok readValue]) ∧
    transactPrefix (transactPrefix base (frames.take (1 + 7))).1 ((frames.drop (1 + 7)).take 3) =
      (readWorld.resetTransient, []) := by
  constructor
  · have same : (frames.drop 1).take (7 + 3) = (frames.drop 1).take 3 := rfl
    rw [same]; exact middle_segment_reached
  · have endpoint : frames.take (1 + 7) = frames := rfl
    rw [endpoint, boundary4]; rfl

/-- Apply the actual subdivision theorem at the populated postcommit split. -/
theorem adjacent_subdivision_application :
    transactPrefix linked.resetTransient ((frames.drop 1).take 3) =
      ((transactPrefix (transactPrefix base (frames.take 2)).1 ((frames.drop 2).take 2)).1,
       (transactPrefix linked.resetTransient ((frames.drop 1).take 1)).2 ++
       (transactPrefix (transactPrefix base (frames.take 2)).1 ((frames.drop 2).take 2)).2) := by
  have subdivision := transact_prefix_segment_subdivide base frames 1 1 2
  have preceding : transactPrefix base (frames.take 1) = (linked.resetTransient, h1) := boundary1
  rw [preceding] at subdivision
  exact subdivision

theorem adjacent_observation_application :
    (((transactPrefix base observedFrames).2.drop 1).take 3) =
      (((transactPrefix base frames).2.drop 1).take 1).map (fun result => result.map extendOutput) ++
      (((transactPrefix base frames).2.drop 2).take 2).map (fun result => result.map extendOutput) := by
  unfold observedFrames
  exact transact_prefix_segment_subdivide_observe base frames 1 1 2 extendOutput

/-- Same ENTIRE concatenated history but different labelled first components
and actual prefix snapshots: history equality cannot locate a partition. -/
theorem ambiguous_partition_concat :
    h1 ++ [.error laterHalt, .error .revert, .ok readValue] = [] ++ h4 ∧
    h1 ≠ [] ∧ extended (transactPrefix base (frames.take 1)).1 ≠ extended base := by
  constructor
  · rfl
  · constructor
    · decide +kernel
    · have preceding : transactPrefix base (frames.take 1) = (linked.resetTransient, h1) := boundary1
      rw [preceding]; decide +kernel

/-- Real paidcall when the constructor candidate is installed; otherwise an
actual creation. Only the actual reached branch is required for replacement. -/
def paidReplacement (w : World Catalog) : TRes (World Catalog × Output) :=
  if (w.accounts candidate).isSome then failing w else occupied w

def baseOnlyReplacement (w : World Catalog) : TRes (World Catalog × Output) :=
  if (w.accounts candidate).isSome then occupied w else failing w

def dirtyOnlyReplacement (w : World Catalog) : TRes (World Catalog × Output) :=
  if cells w candidate = some [8, 12] then failing w else occupied w

theorem paid_replacement_reached : paidReplacement linked.resetTransient = failing linked.resetTransient := by
  have present : (linked.resetTransient.accounts candidate).isSome = true := by decide +kernel
  unfold paidReplacement
  rw [present]; rfl

theorem paid_replacement_actual_input :
    failing (transactPrefix base [commit]).1.resetTransient =
      paidReplacement (transactPrefix base [commit]).1.resetTransient := by
  rw [boundary1, resetTransient_idem]
  exact paid_replacement_reached.symm

theorem replacement_continuation :
    transactPrefix base [commit, paidReplacement, occupied, reading] = transactPrefix base frames :=
  (transact_prefix_replace_frame base [commit] [occupied, reading] failing paidReplacement paid_replacement_actual_input).symm

/-- All listed balances/cells/identity/context/status observations at all original
boundaries retained; replaced trace has both exact errors and both full returns. -/
theorem replacement_complete_vectors :
    (observeBoundary [] =
      ((([95, 0, 0, 5, 0], [some [0, 0], some [19, 29], some []], flags), none, false), []) ∧
    observeBoundary [commit] = (committedVector, h1) ∧
    observeBoundary [commit, failing] = (committedVector, h2) ∧
    observeBoundary [commit, failing, occupied] = (committedVector, h3) ∧
    observeBoundary frames = (committedVector, h4)) ∧
    (extended (transactPrefix base [commit, paidReplacement, occupied, reading]).1,
      (transactPrefix base [commit, paidReplacement, occupied, reading]).2) = (committedVector, h4) := by
  constructor
  · exact complete_boundaries
  · rw [replacement_continuation, boundary4, read_vector_value]

theorem base_only_agrees_at_wrong_input : baseOnlyReplacement base.resetTransient = failing base.resetTransient := by
  have absent : (base.resetTransient.accounts candidate).isSome = false := by decide +kernel
  unfold baseOnlyReplacement
  rw [absent]; rfl

theorem base_only_reached_failure : baseOnlyReplacement linked.resetTransient = .error .revert := by
  have present : (linked.resetTransient.accounts candidate).isSome = true := by decide +kernel
  unfold baseOnlyReplacement
  rw [present]
  exact occupied_reached

theorem wrong_base_input_discriminates :
    (baseOnlyReplacement linked.resetTransient).halt? ≠ (failing linked.resetTransient).halt? := by
  rw [base_only_reached_failure, failing_reached]; decide +kernel

theorem dirty_only_agrees_at_wrong_input : dirtyOnlyReplacement linked = failing linked := by
  have dirty : cells linked candidate = some [8, 12] := by decide +kernel
  rw [dirtyOnlyReplacement, if_pos dirty]

theorem dirty_only_reached_failure : dirtyOnlyReplacement linked.resetTransient = .error .revert := by
  have clean : cells linked.resetTransient candidate ≠ some [8, 12] := by decide +kernel
  rw [dirtyOnlyReplacement, if_neg clean, occupied_reached]

theorem wrong_dirty_input_discriminates :
    (dirtyOnlyReplacement linked.resetTransient).halt? ≠ (failing linked.resetTransient).halt? := by
  rw [dirty_only_reached_failure, failing_reached]; decide +kernel

def replacementFrames : List (TransactionFrame Catalog Output) := [commit, paidReplacement, occupied, reading]

/-- The LEFT original trace supplies every premise's reached reset world. No
agreement on unrelated worlds or equality of traces is assumed. -/
theorem replacement_pointwise : ∀ i (valid : i < frames.length),
    frames[i] (transactPrefix base (frames.take i)).1.resetTransient =
      (replacementFrames[i]'(by exact valid)) (transactPrefix base (frames.take i)).1.resetTransient := by
  intro i valid
  match i with
  | 0 => rfl
  | 1 =>
    simpa only [frames, replacementFrames, List.getElem_cons_succ, List.getElem_cons_zero,
      List.take_succ_cons, List.take_zero] using paid_replacement_actual_input
  | 2 => rfl
  | 3 => rfl
  | i + 4 =>
    simp only [frames, List.length_cons, List.length_nil] at valid
    omega

theorem replacement_every_prefix (count : Nat) :
    transactPrefix base (frames.take count) = transactPrefix base (replacementFrames.take count) :=
  transact_prefix_reachable_congr base frames replacementFrames rfl replacement_pointwise count

theorem replacement_every_listed_vector (count : Nat) :
    (extended (transactPrefix base (replacementFrames.take count)).1,
      (transactPrefix base (replacementFrames.take count)).2) =
    (extended (transactPrefix base (frames.take count)).1,
      (transactPrefix base (frames.take count)).2) :=
  congrArg (fun pair => (extended pair.1, pair.2)) (replacement_every_prefix count).symm

/-- Explicit actual middle-SEGMENT application, preserving the arbitrary prefix
and the real final read using only two individual reached-input obligations. -/
theorem replacement_segment_application :
    transactPrefix base (([commit] ++ [failing, occupied]) ++ [reading]) =
      transactPrefix base (([commit] ++ [paidReplacement, occupied]) ++ [reading]) := by
  apply transact_prefix_replace_segment base [commit] [reading] [failing, occupied] [paidReplacement, occupied] rfl
  intro i valid
  match i with
  | 0 =>
    simpa only [List.getElem_cons_zero, List.take_zero, transact_prefix_nil] using paid_replacement_actual_input
  | 1 => rfl
  | i + 2 =>
    simp only [List.length_cons, List.length_nil] at valid
    omega

private theorem normalize_success (w : World Catalog) (value : Output) :
    ((.ok (w, value) : TRes (World Catalog × Output)).map
      (fun pair => (pair.1.resetTransient, pair.2))) = .ok (w.resetTransient, value) := rfl

theorem normalize_commit_reached : normalizeTransactionFrame commit base.resetTransient =
    .ok (linked.resetTransient, commitValue) := by
  have mapped := congrArg (fun run : TRes (World Catalog × Output) =>
    run.map (fun pair => (pair.1.resetTransient, pair.2))) commit_reached
  exact mapped.trans (normalize_success linked commitValue)

/-- Raw completed worlds REALLY differ on transient cells, though legal boundary
normalization retains their exact complete committed world and typed value. -/
theorem normalize_commit_raw_vectors :
    ((commit base.resetTransient).toOption.map (fun pair => (extended pair.1, pair.2)),
      (normalizeTransactionFrame commit base.resetTransient).toOption.map (fun pair => (extended pair.1, pair.2))) =
    (some ((([88, 7, 0, 5, 0], [some [11, 23], some [19, 0], some []], installedFlags), some [8, 12], true), commitValue),
      some (committedVector, commitValue)) := by
  rw [commit_reached, normalize_commit_reached]
  decide +kernel

theorem normalize_commit_raw_different :
    (commit base.resetTransient).toOption.map (fun pair => extended pair.1) ≠
      (normalizeTransactionFrame commit base.resetTransient).toOption.map (fun pair => extended pair.1) := by
  rw [commit_reached, normalize_commit_reached]
  decide +kernel

theorem normalize_commit_trace :
    transactPrefix base [normalizeTransactionFrame commit, failing, occupied, reading] = transactPrefix base frames := by
  symm
  apply transact_prefix_replace_frame_normalized base [] [failing, occupied, reading] commit (normalizeTransactionFrame commit)
  simp only [transact_prefix_nil, normalizeTransactionFrame, commit_reached, Except.map, resetTransient_idem]

theorem normalization_every_prefix (count : Nat) :
    transactPrefix base ((frames.take count).map normalizeTransactionFrame) = transactPrefix base (frames.take count) :=
  transact_prefix_normalize_frames base (frames.take count)

theorem normalization_every_listed_vector (count : Nat) :
    (extended (transactPrefix base ((frames.take count).map normalizeTransactionFrame)).1,
      (transactPrefix base ((frames.take count).map normalizeTransactionFrame)).2) =
    (extended (transactPrefix base (frames.take count)).1,
      (transactPrefix base (frames.take count)).2) :=
  congrArg (fun pair => (extended pair.1, pair.2)) (normalization_every_prefix count)

def badFrames : List (TransactionFrame Catalog Output) := [commit, baseOnlyReplacement, occupied, reading]
def badHistory : List (TRes Output) := [.ok commitValue, .error .revert, .error .revert, .ok readValue]

/-- Actual invalid replacement still reaches the SAME final world and read,
but loses the paid call's exact binary halt. No desired trace equation assumed. -/
theorem bad_trace_reached : transactPrefix base badFrames = (readWorld.resetTransient, badHistory) := by
  have first : base.transact commit = (linked.resetTransient, .ok commitValue) :=
    World.transact_commit base linked commit commitValue commit_reached
  have bad : linked.resetTransient.transact baseOnlyReplacement = (linked.resetTransient, .error .revert) := by
    have failed : baseOnlyReplacement linked.resetTransient.resetTransient = .error .revert := by
      simpa only [resetTransient_idem] using base_only_reached_failure
    rw [World.transact_failure _ _ _ failed, resetTransient_idem]
  have collision : linked.resetTransient.transact occupied = (linked.resetTransient, .error .revert) := by
    have failed : occupied linked.resetTransient.resetTransient = .error .revert := by
      simpa only [resetTransient_idem] using occupied_reached
    rw [World.transact_failure _ _ _ failed, resetTransient_idem]
  have read : linked.resetTransient.transact reading = (readWorld.resetTransient, .ok readValue) := by
    apply World.transact_commit
    simpa only [resetTransient_idem] using read_reached
  simp only [badFrames, transact_prefix_cons, first, bad, collision, read, transact_prefix_nil]
  rfl

theorem same_terminal_not_history :
    ((transactPrefix base badFrames).1, (transactPrefix base badFrames).2.getLast?) =
      ((transactPrefix base frames).1, (transactPrefix base frames).2.getLast?) ∧
    (transactPrefix base badFrames).2 ≠ (transactPrefix base frames).2 := by
  simp only [bad_trace_reached, boundary4]
  constructor
  · rfl
  · decide +kernel

theorem bad_exact_payload_discriminates :
    (transactPrefix base badFrames).2[1]'(by rw [transact_prefix_length]; decide) ≠
      (transactPrefix base frames).2[1]'(by rw [transact_prefix_length]; decide) := by
  simp only [bad_trace_reached, boundary4]
  decide +kernel

#print axioms normalize_commit_reached
#print axioms normalize_commit_raw_vectors
#print axioms normalize_commit_raw_different
#print axioms normalize_commit_trace
#print axioms normalization_every_prefix
#print axioms normalization_every_listed_vector
#print axioms bad_trace_reached
#print axioms same_terminal_not_history
#print axioms bad_exact_payload_discriminates

#print axioms replacement_pointwise
#print axioms replacement_every_prefix
#print axioms replacement_every_listed_vector
#print axioms replacement_segment_application

#print axioms paid_replacement_reached
#print axioms paid_replacement_actual_input
#print axioms replacement_continuation
#print axioms replacement_complete_vectors
#print axioms base_only_agrees_at_wrong_input
#print axioms base_only_reached_failure
#print axioms wrong_base_input_discriminates
#print axioms dirty_only_agrees_at_wrong_input
#print axioms dirty_only_reached_failure
#print axioms wrong_dirty_input_discriminates

#print axioms adjacent_subdivision_application
#print axioms adjacent_observation_application
#print axioms ambiguous_partition_concat

#print axioms adjacent_first_reached
#print axioms adjacent_second_reached
#print axioms adjacent_complete_vectors
#print axioms labelled_partition_reflection
#print axioms wrong_partition
#print axioms empty_first_partition
#print axioms truncated_partition

#print axioms lossy_actual_runs

#print axioms extendOutput_injective
#print axioms complete_history_reflection
#print axioms middle_history_reflection
#print axioms reflection_complete_boundaries
#print axioms lossy_observer_counterexample
#print axioms injective_wrong_success_rejected
#print axioms injective_wrong_order_rejected

#print axioms middle_segment_reached
#print axioms middle_paid_reconstruction
#print axioms middle_read_reconstruction
#print axioms middle_complete_vectors
#print axioms empty_segment_dirty
#print axioms empty_segment_reached
#print axioms truncated_segment
#print axioms wrong_middle_order
#print axioms wrong_middle_snapshot

#print axioms commit_history_reconstruction
#print axioms read_history_reconstruction
#print axioms reconstructed_complete_boundaries
#print axioms wrong_library_success_value
#print axioms wrong_raw_reset_world

#print axioms paid_history_reconstruction
#print axioms collision_history_reconstruction

#print axioms indexed_commit
#print axioms indexed_paid_failure
#print axioms indexed_collision
#print axioms indexed_read
#print axioms middle_locality
#print axioms indexed_complete_vectors
#print axioms indexed_observed_read
#print axioms indexed_observed_error
#print axioms out_of_range_locality
#print axioms wrong_index
#print axioms shifted_success
#print axioms wrong_suffix_order

#print axioms observed_complete
#print axioms observed_recovery
end Solidity.Lowering.V08.PrefixControls
