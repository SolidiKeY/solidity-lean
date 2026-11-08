"""Designated audit certificates shared by snapshot and portable verifiers.
Trusted verifier data, never read from an untrusted archive. Import performs no
file I/O. Mapping edits require the same statement-fidelity review as before.
"""
WITNESSES={
 "Solidity.Theory.Progress.tuple_stmt_progress":("ProgressWitnesses","tuple_stmt_progress_joint_witness"),
 "Solidity.Theory.Progress.stmt_progress":("ProgressWitnesses","stmt_progress_joint_witness"),
 "Solidity.Theory.Progress.expr_progress":("ScopeControls","expr_progress_joint_witness"),
 "Solidity.Theory.Progress.items_progress":("ScopeControls","items_progress_joint_witness"),
 "Solidity.Theory.Progress.body_progress":("ScopeControls","body_progress_joint_witness"),
 "Solidity.Theory.Progress.callsOKX_none":("ScopeControls","callsOKX_none_joint_witness"),
 'Solidity.Path.append_assoc':("PathWitnesses",'path_append_assoc_joint_witness'),
 'Solidity.Path.append_nil_right':("PathWitnesses",'path_append_nil_right_joint_witness'),
 'Solidity.Path.strip?_append':("PathWitnesses",'path_strip_append_joint_witness'),
 'Solidity.Path.eq_of_strip?':("PathWitnesses",'path_eq_of_strip_joint_witness'),
 'Solidity.Path.split_of_labels':("PathWitnesses",'path_split_of_labels_joint_witness'),
 'Solidity.Path.strip?_none':("PathWitnesses",'path_strip_none_joint_witness'),
 'Solidity.Path.strip?_append_append':("PathWitnesses",'path_strip_append_append_joint_witness'),
 'Solidity.ObsLoc.app_path':("PathWitnesses",'obsloc_app_path_joint_witness'),
 'Solidity.ObsLoc.strip?_path':("PathWitnesses",'obsloc_strip_path_joint_witness'),
 'Solidity.Obs.ext':("ObservationDomains",'obs_ext_populated_joint_witness'),
 'Solidity.Obs.find_word':("PathWitnesses",'obs_find_word_joint_witness'),
 'Solidity.Obs.find_len':("PathWitnesses",'obs_find_len_joint_witness'),
 'Solidity.Obs.find_save_same':("PathWitnesses",'obs_find_save_same_joint_witness'),
 'Solidity.Obs.find_save_frame':("PathWitnesses",'obs_find_save_frame_joint_witness'),
 'Solidity.Obs.save_word_frame':("PathWitnesses",'obs_save_word_frame_joint_witness'),
 'Solidity.Obs.save_len_frame':("PathWitnesses",'obs_save_len_frame_joint_witness')}
WITNESSES.update({
 'Solidity.Path.ty_eq_of_lookup': ('PathRemaining', 'path_lookup_joint_witness'),
 'Solidity.Obs.find_find': ('PathRemaining', 'obs_find_find_joint_witness'),
 'Solidity.Obs.find_nil': ('PathRemaining', 'obs_find_nil_joint_witness'),
 'Solidity.Obs.save_find': ('PathRemaining', 'obs_save_find_joint_witness'),
 'Solidity.Obs.save_word_below': ('PathRemaining', 'obs_save_word_below_joint_witness'),
 'Solidity.Obs.save_word_same': ('PathRemaining', 'obs_save_word_same_joint_witness'),
 'Solidity.Obs.find_save_below': ('PathRemaining', 'obs_find_save_below_joint_witness'),
 'Solidity.SRef.ty_eq': ('PathRemaining', 'sref_ty_eq_joint_witness'),
 'Solidity.SRef.strip?_append': ('PathRemaining', 'sref_strip_append_joint_witness'),
 'Solidity.SRef.eq_of_strip?': ('PathRemaining', 'sref_eq_of_strip_joint_witness'),
 'Solidity.SRef.append_append': ('PathRemaining', 'sref_append_append_joint_witness'),
 'Solidity.SRef.append_nil': ('PathRemaining', 'sref_append_nil_joint_witness'),
 'Solidity.SRef.strip?_append_append': ('PathRemaining', 'sref_strip_append_append_joint_witness'),
 'Solidity.SRef.strip?_root_ne': ('PathRemaining', 'sref_root_ne_joint_witness'),
 'Solidity.SLoc.strip?_app': ('PathRemaining', 'sloc_strip_app_joint_witness'),
 'Solidity.SLoc.eq_of_strip?': ('PathRemaining', 'sloc_eq_of_strip_joint_witness'),
 'Solidity.SLoc.app_app': ('PathRemaining', 'sloc_app_app_joint_witness'),
 'Solidity.SLoc.app_nil': ('PathRemaining', 'sloc_app_nil_joint_witness'),
 'Solidity.SLoc.strip?_app_app': ('PathRemaining', 'sloc_strip_app_app_joint_witness'),
 'Solidity.SLoc.app_ref': ('PathRemaining', 'sloc_app_ref_joint_witness'),
 'Solidity.SVal.findM_append': ('PathRemaining', 'sval_findM_append_joint_witness'),
 'Solidity.SVal.saveM_append_eq': ('PathRemaining', 'sval_saveM_append_eq_joint_witness'),
 'Solidity.SVal.saveM_of_findM': ('PathRemaining', 'sval_saveM_of_findM_joint_witness'),
 'Solidity.SVal.saveM_append': ('PathRemaining', 'sval_saveM_append_joint_witness'),
 'Solidity.SVal.saveM_at_n': ('PathRemaining', 'sval_saveM_at_n_joint_witness'),
})
WITNESSES.update({
 'Solidity.SVal.Mirrors.mono': ('MirrorWitnesses', 'mirror_val_mono_joint_witness'),
 'Solidity.SFields.Mirrors.mono': ('MirrorWitnesses', 'mirror_fields_mono_joint_witness'),
 'Solidity.SVec.Mirrors.mono': ('MirrorWitnesses', 'mirror_vec_mono_joint_witness'),
 'Solidity.SVal.Mirrors.wk': ('MirrorWitnesses', 'mirror_val_wk_joint_witness'),
 'Solidity.SFields.Mirrors.wk': ('MirrorWitnesses', 'mirror_fields_wk_joint_witness'),
 'Solidity.SVec.Mirrors.wk': ('MirrorWitnesses', 'mirror_vec_wk_joint_witness'),
 'Solidity.SVal.mirrors_copyStToM': ('MirrorWitnesses', 'mirror_val_copy_joint_witness'),
 'Solidity.SFields.mirrors_copyStToM': ('MirrorWitnesses', 'mirror_fields_copy_joint_witness'),
 'Solidity.SVec.mirrors_copyStToM': ('MirrorWitnesses', 'mirror_vec_copy_joint_witness'),
 'Solidity.SVal.Mirrors.prim': ('MirrorWitnesses', 'mirror_prim_joint_witness'),
 'Solidity.SVal.Mirrors.id_ge': ('MirrorWitnesses', 'mirror_id_ge_joint_witness'),
 'Solidity.SFields.Mirrors.get': ('MirrorWitnesses', 'mirror_fields_get_joint_witness'),
 'Solidity.SVec.Mirrors.getElem': ('MirrorWitnesses', 'mirror_vec_getElem_joint_witness'),
})
WITNESSES.update({
 'Solidity.Storage.obs_len_ref_some': ('BridgeWitnesses', 'bridge_obs_len_joint_witness'),
 'Solidity.Storage.obs_word_ref_some': ('BridgeWitnesses', 'bridge_obs_word_joint_witness'),
 'Solidity.Storage.full_of_push': ('BridgeWitnesses', 'bridge_full_push_joint_witness'),
 'Solidity.Storage.full_of_pushPlace': ('BridgeWitnesses', 'bridge_full_pushPlace_joint_witness'),
 'Solidity.Op0.denote_eval': ('BridgeWitnesses', 'bridge_op0_joint_witness'),
 'Solidity.Op1.denote_eval': ('BridgeWitnesses', 'bridge_op1_joint_witness'),
 'Solidity.Op2.denote_eval': ('BridgeWitnesses', 'bridge_op2_joint_witness'),
 'Solidity.Op3.denote_eval': ('BridgeWitnesses', 'bridge_op3_joint_witness'),
})
WITNESSES.update({
 'Solidity.Theory.Progress.ends_of_notStuck': ('OutcomeWitnesses', 'outcome_notStuck_joint_witness'),
 'Solidity.Theory.Progress.Ends.notStuck': ('OutcomeWitnesses', 'outcome_ends_notStuck_joint_witness'),
 'Solidity.Theory.Progress.ns_iff_ends': ('OutcomeWitnesses', 'outcome_ns_iff_joint_witness'),
 'Solidity.Theory.Progress.NS.ends': ('OutcomeWitnesses', 'outcome_ns_ends_joint_witness'),
 'Solidity.Theory.Progress.not_ends_stuck': ('OutcomeWitnesses', 'outcome_stuck_negative_joint_witness'),
 'Solidity.Theory.Progress.coreEnds': ('OutcomeWitnesses', 'outcome_core_joint_witness'),
 'Solidity.Theory.Progress.Prog.run_ends': ('OutcomeWitnesses', 'outcome_run_joint_witness'),
 'Solidity.Theory.Progress.Prog.runF_ends': ('OutcomeWitnesses', 'outcome_runF_joint_witness'),
 'Solidity.Theory.Progress.Stmt.runF_ends': ('OutcomeWitnesses', 'outcome_stmt_runF_joint_witness'),
})
WITNESSES.update({
 'Solidity.Theory.Mutability.holds_modal_readOnly': ('CloserWitnesses', 'closer_modal_joint_witness'),
 'Solidity.Theory.Mutability.Spec.box_readOnly': ('CloserWitnesses', 'closer_spec_joint_witness'),
 'Solidity.Theory.Mutability.Transient.holds_readOnly': ('CloserWitnesses', 'closer_transient_modal_joint_witness'),
 'Solidity.Theory.Mutability.Transient.holds_frame': ('CloserWitnesses', 'closer_transient_frame_joint_witness'),
})
WITNESSES.update({
 'Solidity.Theory.Mutability.refuses': ('PayableWitnesses', 'payable_refuses_joint_witness'),
 'Solidity.Theory.Mutability.System.run_nonpayable': ('PayableWitnesses', 'payable_system_joint_witness'),
 'Solidity.Theory.Mutability.deployT_nonpayable': ('PayableWitnesses', 'payable_deploy_joint_witness'),
 'Solidity.Theory.Mutability.transact_nonpayable': ('PayableWitnesses', 'payable_transact_joint_witness'),
 'Solidity.Theory.Mutability.ContractWorld.World.enter_nonpayable': ('PayableWitnesses', 'payable_enter_joint_witness'),
 'Solidity.Theory.Mutability.ContractWorld.World.callFrame_nonpayable': ('PayableWitnesses', 'payable_call_joint_witness'),
})
WITNESSES.update({
 "Solidity.Theory.Mutability.Frames.nothing": ("AssignableWitnesses", "assignable_nothing_joint_witness"),
 "Solidity.Theory.Mutability.Frames.mono": ("AssignableWitnesses", "assignable_mono_joint_witness"),
 "Solidity.Theory.Mutability.Frames.of_globals": ("AssignableWitnesses", "assignable_globals_joint_witness"),
 "Solidity.Theory.Mutability.Prog.frames_readOnly": ("AssignableWitnesses", "assignable_readonly_joint_witness"),
 "Solidity.Theory.Mutability.Prog.storage_readOnly": ("AssignableWitnesses", "assignable_storage_joint_witness"),
 "Solidity.Theory.Mutability.Prog.frames_of_storeAt": ("AssignableWitnesses", "assignable_store_joint_witness"),
 "Solidity.Theory.Mutability.assignableCheck_sound": ("AssignableWitnesses", "assignable_check_joint_witness"),
 "Solidity.Theory.Mutability.committed_frames": ("AssignableWitnesses", "assignable_committed_joint_witness"),
})
WITNESSES.update({
 "Solidity.Theory.Mutability.withOutside_outside": ("PureBoundaryWitnesses", "pure_restore_joint_witness"),
 "Solidity.Theory.Mutability.outside_withOutside": ("PureBoundaryWitnesses", "pure_replace_joint_witness"),
 "Solidity.Theory.Mutability.withOutside_withOutside": ("PureBoundaryWitnesses", "pure_replace_twice_joint_witness"),
 "Solidity.Theory.Mutability.TRes.map_map": ("PureBoundaryWitnesses", "pure_result_map_joint_witness"),
 "Solidity.Theory.Mutability.TLoop.step_map": ("PureBoundaryWitnesses", "pure_loop_step_joint_witness"),
 "Solidity.Theory.Mutability.TLoop.iterN_map": ("PureBoundaryWitnesses", "pure_loop_iter_joint_witness"),
 "Solidity.Theory.Mutability.TLoop.run_map": ("PureBoundaryWitnesses", "pure_loop_run_joint_witness"),
 "Solidity.Theory.Mutability.Simple.evalT_withOutside": ("PureBoundaryWitnesses", "pure_simple_joint_witness"),
})
WITNESSES.update({
 "Solidity.SFields.all_anon":("CleanTailWitnesses","tail_anon_inputs_joint"),
 "Solidity.Storage.resetTransient_cleanTail":("CleanTailWitnesses","tail_reset_inputs_joint"),
 "Solidity.Reachable.ofState_clean":("CleanTailWitnesses","tail_ofState_inputs_joint"),
 "Solidity.Reachable.cleanTail_invariant":("CleanTailWitnesses","tail_invariant_inputs_joint"),
 "Solidity.Reachable.EntryState.cleanTail":("CleanTailWitnesses","tail_entry_inputs_joint"),
 "Solidity.ValidTail.validStart_reachable":("CleanTailWitnesses","tail_validStart_inputs_joint"),
})
IMPOSSIBLE={
 "Solidity.Theory.Progress.Val.not_tuple":("ProgressWitnesses","no_plain_tuple_input"),
 "Solidity.Theory.Progress.Controls.no_tuple_local":("ProgressWitnesses","no_tuple_locals_input"),
 "Solidity.Ty.Finite.not_array":("FiniteBoundary","no_finite_array_path_input")}

IMPOSSIBLE["Solidity.Theory.Mutability.ContractWorld.World.enter_static"]=("PayableWitnesses","payable_static_inputs_impossible")
assert not set(WITNESSES)&set(IMPOSSIBLE)
