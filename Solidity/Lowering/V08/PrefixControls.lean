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

end Solidity.Lowering.V08.PrefixControls
