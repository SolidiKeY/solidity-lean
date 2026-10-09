#!/usr/bin/env bash
# W5 (docs/intrinsic.md, "W5 — final rename"): the scoped calculus takes the
# plain names.  One scripted commit, no hand edits:
#
#   namespaces  Solidity.Core.X -> Solidity.X, Solidity.Evm.Core.X -> Solidity.Evm.X
#               (`namespace Core`/`end Core` lines inside them are dropped)
#   identifiers TState -> State, trun* -> run* (trunSt, trunR, trunF, ...)
#   modules     Calculus/Core/X -> Calculus/X, Evm/CoreX -> Evm/X,
#               Semantics/Core/TypedX -> Semantics/X, Semantics/Core/X -> Semantics/X,
#               Semantics/Core.lean -> Semantics/Erased.lean
#
# `Syntax/Core*.lean`, `Examples/Tactics/Core*.lean` and
# `TestSuite/CoreProblems.lean` keep their paths (two of them would clash with
# `Examples/Tactics/Callback.lean` and `TestSuite/Problems.lean`).
#
# The W5 preparation (`docs/intrinsic.md`, "W5 preparation") renamed the old
# side of every clash, and checked that every identifier of the tree resolves
# after these rules to the renamed constant it resolved to before.  A bare
# `Core.X` is rewritten only for `X` a first component of `Solidity.Core.*` or
# `Solidity.Evm.Core.*` (the list below, from the environment at the
# preparation), so Lean's own `Core.CoreM` and the paths `Syntax/Core.lean`
# are left alone.
#
# Usage: scripts/w5-rename.sh   (from a clean tree; then build, and commit)
set -euo pipefail
cd "$(dirname "$0")/.."
export LC_ALL=C.UTF-8

if [ -n "$(git status --porcelain --untracked-files=no)" ]; then
  echo "w5-rename: the tree has uncommitted changes" >&2; exit 1
fi

# 1. modules
for f in Solidity/Calculus/Core/*.lean; do
  git mv "$f" "Solidity/Calculus/$(basename "$f")"
done
for f in Solidity/Evm/Core*.lean; do
  b=$(basename "$f"); git mv "$f" "Solidity/Evm/${b#Core}"
done
for f in Solidity/Semantics/Core/*.lean; do
  b=$(basename "$f"); git mv "$f" "Solidity/Semantics/${b#Typed}"
done
git mv Solidity/Semantics/Core.lean Solidity/Semantics/Erased.lean

# 2. names, in every tracked source and prose file
CORE_FIRST=(
  'evalSolDecideUnconstrainedCore' 'instTransFmlOneStepStepBySteps' 'instTransFmlStepByOneStepSteps' 'sound_memIndexWriteRecvUnfold' 'tacticCore_contract_walk_____' 'sound_localValueDeclInitDrop'
  'instTransFmlLeadsOfSoundRel' 'sound_deleteMemIndexCapture' 'sound_memIndexRefRecvUnfold' 'evalSolDecideHeuristicCore' 'holds_of_erase_valid_agree' 'instTransFmlOneStepSteps_1'
  'sound_storageLocalDeclSkip' 'instTransFmlStepBySteps_1' 'sound_fieldWriteRefUnfold' 'sound_memIndexWriteUnfold' 'instDecidableEqBlockKind' 'instTransFmlOneStepSteps'
  'instTransFmlStepsOneStep' 'lookupBy_none_of_not_mem' 'sound_deleteIndexCapture' 'sound_deleteMemFieldRecv' 'sound_deleteMemIndexRecv' 'sound_fromMemFieldUnfold'
  'sound_fromMemIndexUnfold' 'sound_indexRefCaptureAll' 'sound_memIndexRefCapture' 'tacticCore_contract_____' 'assignFromMemStep_sound' 'instTransFmlStepBySteps'
  'instTransFmlStepsStepBy' 'lookupBy_append_of_none' 'setBy_eq_append_of_none' 'sound_deleteRecvCapture' 'sound_memFieldWriteRecv' 'sound_rebindPushCapture'
  'storesFrom_retEnterCode' 'storesFrom_retLeaveCode' 'evalSolCloseUnwrapCore' 'sound_fieldWriteUnfold' 'storesFrom_compileProg' 'storesFrom_compileStmt'
  'tacticCore_settle_side' 'evalSolDecideConsCore' 'holds_of_envAgree_nil' 'holds_of_holdsC_modal' 'lookupBy_of_mem_nodup' 'noStore_compileSimple'
  'nonpayable_of_within'\''' 'sound_binopUnfoldLeft' 'sound_declStorageInit' 'sound_indexCaptureAll' 'sound_pushRecvCapture' 'tacticCore_cases_hole'
  'tacticCore_cases_part' 'tacticTo_step_replay_' 'useContractC_of_valid' 'afterRunTR_box_error' 'evalSolCloseEvalCore' 'evalSolFoldTermsCore'
  'holds_of_erase_valid' 'instDecidableEqTHalt' 'keepsC_assignFromMem' 'noStore_compileSPath' 'noStore_pushSlotCode' 'sound_memCopyCapture'
  'sound_rebindMemAlias' 'sound_requireCapture' 'storesFrom_callFrame' 'storesFrom_opLocCode' 'tacticCore_apply_upd' 'tacticNo_store_piece'
  'tyRank_le_fieldsRank' 'useContract_of_valid' 'agreeExcept_overlay' 'asInt_erase_numeric' 'assignBumpLocal_sim' 'assignBumpStore_sim'
  'assignIncDec_family' 'assignMemStep_sound' 'deleteMemStep_sound' 'evalSolApplyUpdCore' 'evalSolSpecPrepCore' 'frames_pop_nil_trun'
  'holdsC_closedAt_iff' 'holds_isBoolD_lower' 'holds_of_holdsC_imp' 'holds_upd_of_substU' 'instDecidableAvoids' 'instDecidableEqFrag'
  'instSoundRelMergeBy' 'instSoundRelOneStep' 'keepsC_assignIncDec' 'overlayElems_eq_zip' 'rebindMemStep_sound' 'sound_assertCapture'
  'sound_transferRight' 'sound_valueDeclSkip' 'storesFrom_argsCode' 'tacticApply_toStep_' 'tacticCore_simplify' 'tight_assignFromMem'
  'trunSt_block_frames' 'tyRank_le_rankBound' 'validT_withCallback' 'writeStorage_toSVal' 'after_ofRes_frames' 'agreeExcept_setEnv'
  'asValue_erase_prim' 'assignLocal_family' 'declStorage_family' 'evalBinop_and_true' 'evalBinop_cmp_true' 'evalBinop_or_false'
  'evalSolDeriveQCore' 'holdsC_binders_all' 'holds_callContract' 'holds_of_erase_pos' 'indexRefCaptureAll' 'instDecidableEqLTy'
  'instInhabitedTHalt' 'instReprCodeBinder' 'instSoundRelStepBy' 'keepsC_assignLocal' 'keepsC_declStorage' 'noStore_compileLoc'
  'noStore_compileVal' 'rebindMemAlias_run' 'sound_assignIncDec' 'sound_declMemFresh' 'sound_deleteMemVar' 'sound_transferLeft'
  'structRank_le_four' 'tight_assignIncDec' 'transferStep_sound' 'trunSt_cons_frames' 'writeStorage_stChg' 'agreeExcept_trans'
  'assignFromMemStep' 'cdl_local_Memory_' 'defaultOfElems_eq' 'elabValidDispatch' 'evalSolDecideCore' 'evalSolDeriveCore'
  'evalSolProveQCore' 'evalSolReduceCore' 'holdsC_exit_after' 'holdsC_transferCb' 'holds_binders_all' 'holds_exit_closed'
  'instDecidableEqFl' 'instReprBlockKind' 'instSoundRelLeads' 'instSoundRelSteps' 'instTransFmlSteps' 'loopFalse_derived'
  'mapFree_structDef' 'memWriteField_nat' 'memWriteIndex_nat' 'noStore_fixedSlot' 'pushPlaceAt_stChg' 'requireStep_sound'
  'saveStorage_stChg' 'sound_copyCapture' 'sound_declMemInit' 'sound_mlenCapture' 'sound_pushCapture' 'sound_transferBox'
  'sound_unopCapture' 'storesFrom_append' 'tacticRule_admits' 'tacticStores_from' 'tacticTo_step_tac' 'ternaryStep_sound'
  'tight_assignLocal' 'tight_declStorage' 'validT_noCallback' 'writeAddr_ok_with' 'afterRunTR_error' 'after_frames_iff'
  'agreeExcept_full' 'agreeExcept_mono' 'agreeExcept_refl' 'agreeExcept_symm' 'allocDefault_nat' 'assertStep_sound'
  'assignIncDec_run' 'assignStep_sound' 'avoids_of_meetsB' 'binopRight_sound' 'bumpStoreT_erase' 'bumpStoreT_frame'
  'copyMElems_erase' 'copyStFields_nat' 'declLocal_family' 'declMemFresh_run' 'deleteMemVar_run' 'deleteStep_sound'
  'disjointB_avoids' 'evalSolMergeCore' 'evalSolProveCore' 'evalSolReadsCore' 'evalSolSymexCore' 'find_of_findLive'
  'holdsC_and_intro' 'holdsC_and_right' 'holdsC_iff_holds' 'holds_congr_full' 'holds_modalK_pop' 'holds_upd_seqPar'
  'instInhabitedLTy' 'keepsC_assignMem' 'keepsC_assignNew' 'keepsC_declLocal' 'keepsC_deleteMem' 'keepsC_rebindMem'
  'lookupBy_map_snd' 'lookupBy_mergeOn' 'lookupBy_overlay' 'memRefStep_sound' 'noStore_bumpCode' 'noStore_elemSlot'
  'noStore_pushCode' 'rebindStep_sound' 'saveStorage_glob' 'sound_binopRight' 'sound_done_false' 'sound_iteCapture'
  'sound_lenCapture' 'sound_popCapture' 'sound_rebindPath' 'sound_rebindPush' 'sref_erase_field' 'sref_erase_index'
  'storesFrom_store' 'tacticCore_brute' 'tacticCore_merge' 'transfer_booking' 'writeStorage_nat' 'writeStorage_wl'\'''
  'aliasPath_erase' 'assignLocal_sim' 'bumpStoreT_ends' 'bumpStoreT_lift' 'bumpStoreT_push' 'callNone_run_eq'
  'compile_correct' 'compile_storage' 'compound_erase'\''' 'copyStElems_nat' 'coreReplayGoals' 'coreSurfaceFlag'
  'erase_upd_holds' 'evalBinop_short' 'evalSolProveSeq' 'evalSolStepCore' 'holdsC_and_left' 'holds_anonHavoc'
  'holds_declsThen' 'holds_liftBinds' 'holds_modal_iff' 'holds_upd_graft' 'indexCaptureAll' 'instReprBinders'
  'keepsC_opAssign' 'keepsC_transfer' 'liftedT_up_drop' 'liftedTopT_bind' 'liftedTopT_pure' 'localStep_sound'
  'noStore_binTail' 'noStore_expCode' 'noStore_expLoop' 'noStore_flatMap' 'opAssign_family' 'pushPlaceAt_nat'
  'pushPlaceAt_wl'\''' 'resolveArgsFrom' 'saveStorage_nat' 'saveStorage_wl'\''' 'shortStep_sound' 'solDeriveScoped'
  'sound_allocCopy' 'sound_assignNew' 'sound_opCapture' 'sound_sendRight' 'structDef_nodup' 'tacticNat_step_'
  'tight_assignMem' 'tight_assignNew' 'tight_declLocal' 'tight_deleteMem' 'tight_rebindMem' 'transferBox_run'
  'transfer_family' 'trunSt_declThen' 'valid_of_validC' 'writeAddr_erase' 'CallbackTaclet' 'bumpMemT_erase'
  'callVal_run_eq' 'compound_erase' 'copyStep_sound' 'coreBruteHeads' 'coreCasesFirst' 'coreCasesLocal'
  'evalBinop_long' 'evalCoreParams' 'evalCoreSilent' 'evalSolUpdCore' 'findStorage_wl' 'holds_FO_erase'
  'holds_callNone' 'holds_callPost' 'holds_callRets' 'holds_erase_fo' 'holds_upd_simp' 'holeCandidates'
  'indexOrderCore' 'instCoePostFml' 'keepsC_declMem' 'memArrayLen_wl' 'noStore_addRep' 'noStore_append'
  'noStore_leaves' 'opStoreT_erase' 'opStoreT_frame' 'pushSlot_erase' 'pushStep_sound' 'rebindPath_run'
  'rebindPush_run' 'require_family' 'resolveExtCall' 'resolveLoopAnn' 'saveStorage_wl' 'sendStep_sound'
  'sound_clearMem' 'sound_opAssign' 'sound_pushSlot' 'sound_pushSome' 'sound_sendLeft' 'sound_setLocal'
  'sound_shortAnd' 'sound_writeMem' 'specObligation' 'tacticLift_fin' 'tacticNo_store' 'tight_opAssign'
  'tight_transfer' 'tyAtSegs_erase' 'writeAddr_glob' 'afterRunTR_ok' 'allocCopy_run' 'assertLowCore'
  'assert_family' 'assignIncStep' 'assignMemStep' 'assignNewStep' 'assign_family' 'bind_withGlob'
  'bumpLocal_sim' 'bumpMemT_ends' 'bumpMemT_lift' 'bumpMemT_push' 'bumpStore_sim' 'checkIndex_wl'
  'compileSimple' 'compile_exact' 'copyStToMFold' 'copyStToM_nat' 'coreSidePreds' 'declAlias_sim'
  'declLocal_sim' 'declStorageIn' 'defaultOfFold' 'deleteMemStep' 'delete_family' 'elabModalProg'
  'envAgree_symm' 'erase_numeric' 'headModality\?' 'holdsC_modalK' 'holdsC_sendCb' 'holdsC_unfold'
  'holdsC_update' 'holds_allArgs' 'holds_callMem' 'holds_callPre' 'holds_callVal' 'holds_closedB'
  'holds_isBoolD' 'holds_openInv' 'holds_reclose' 'holds_snapOld' 'holds_upd_rwC' 'incDec_family'
  'incStep_sound' 'instReprTHalt' 'instToExprLTy' 'iteStep_sound' 'keepsC_assign' 'keepsC_delete'
  'keepsC_incDec' 'keepsC_rebind' 'liftedT_error' 'liftedT₂_bind' 'liftedT₂_pure' 'loopTurn_lift'
  'meetsB_eq_any' 'mergeOn_agree' 'missingToStep' 'newArrT_erase' 'numeric_of_ne' 'opStoreT_ends'
  'opStoreT_lift' 'opStoreT_push' 'popStep_sound' 'pushedT2_drop' 'pushedT3_drop' 'readLoc_erase'
  'rebindMemStep' 'rebind_family' 'resolveNewLhs' 'resolveSimple' 'setBy_map_snd' 'sound_saveMem'
  'sound_shortOr' 'stripElems_eq' 'tacticWl_norm' 'tight_declMem' 'trunSt_pushed' 'unexpandValid'
  'validDispatch' 'writeAddr_nat' 'writeAddr_wl'\''' 'aliasPath_wt' 'bind_bind_eq' 'callNone_sim'
  'checkSequent' 'clearMem_run' 'compileSPath' 'conclusionOf' 'corePlanSpan' 'elabAgainstQ'
  'evalCoreSkip' 'guardLowCore' 'holdsC_split' 'holdsC_tryCb' 'holds_isBool' 'holds_modalK'
  'incDec_write' 'incOrderCore' 'instReprFrag' 'instReprThin' 'lenU_inRange' 'liftedT_bind'
  'liftedT_pure' 'opAssign_run' 'opLocT_store' 'opMemT_erase' 'opStep_sound' 'pushAt_stChg'
  'pushSlot_run' 'pushSome_run' 'replayToStep' 'resolveMPath' 'resolveOpLoc' 'resolveSPath'
  'retEnterCode' 'retLeaveCode' 'setLocal_run' 'sound_extend' 'sound_incDec' 'sound_revert'
  'storage_glob' 'tbind_ok_inv' 'tight_assign' 'tight_delete' 'tight_incDec' 'tight_rebind'
  'toSVal_erase' 'toStepPrefix' 'toStepReplay' 'toStepSearch' 'transferStep' 'transfer_sim'
  'writeMem_run' 'FunContract' 'TransferSem' 'arrayLen_wl' 'bump_bumped' 'callVal_sim'
  'call_family' 'call_run_eq' 'cdl_local__' 'clearT_ends' 'clearT_lift' 'clearT_push'
  'compileProg' 'compileStmt' 'compile_box' 'compile_net' 'ctxOfLocals' 'evalCoreTag'
  'holdsC_bind' 'holdsC_cons' 'instReprExt' 'instReprIdx' 'instReprLTy' 'keepsC_push'
  'keepsC_send' 'liftedT_ite' 'memory_glob' 'offWk_trans' 'opLocT_bump' 'opLocal_sim'
  'opMemT_ends' 'opMemT_lift' 'opMemT_push' 'opStore_sim' 'overlayFold' 'popAt_stChg'
  'push_family' 'readAddr_wl' 'readSequent' 'requireStep' 'require_sim' 'resolveARhs'
  'resolveArgs' 'resolveList' 'resolveMLoc' 'resolveMRhs' 'resolveMSrc' 'resolveProg'
  'resolveStmt' 'saveMem_run' 'sem_storage' 'sequentFmlC' 'showSequent' 'sound_block'
  'sound_delAt' 'symex_sound' 'symex_valid' 'ternaryStep' 'tmap_ok_inv' 'useContract'
  'whereLocals' 'writeLoc_eq' 'CodeBinder' 'FrameFresh' 'LeanTaclet' 'RuleExists'
  'StepAgrees' 'StoresFrom' 'assertStep' 'assert_sim' 'assignCode' 'assignStep'
  'assign_sim' 'block_frag' 'bumpStoreT' 'bump_erase' 'callsBlock' 'cdl_local_'
  'compileLoc' 'compileVal' 'copyMem_wl' 'coreParams' 'coreReplay' 'coreSilent'
  'deleteStep' 'delete_sim' 'elabFmlAtC' 'erasedGoal' 'extend_run' 'fillSlotsC'
  'freshT_sem' 'holds_conj' 'holds_exit' 'holds_wkFO' 'incDec_run' 'indexOrder'
  'instReprFl' 'keepsC_pop' 'legacyShow' 'liftedTopT' 'lvl_eq_iff' 'map_ok_inv'
  'memRefStep' 'newBinders' 'offWk_self' 'opLocToLoc' 'pop_family' 'pushAt_nat'
  'pushAt_wl'\''' 'rebindStep' 'rebind_sim' 'redeclared' 'resolveLoc' 'resolveOpt'
  'resolveSrc' 'resolveVal' 'sendT_lift' 'sendT_push' 'simple_sim' 'slot_erase'
  'sound_save' 'sound_send' 'specParams' 'tight_push' 'tight_send' 'tkeepsT_of'
  'toListFold' 'toRes_none' 'toStepType' 'upd1_apply' 'upd2_apply' 'withLocals'
  'writesRets' 'BlockKind' 'CallRetIn' 'FindHeads' 'Invariant' 'ProofTree'
  'TLocAgree' 'addToStep' 'aliasPath' 'assertLow' 'block_sim' 'bumpLocal'
  'call_frag' 'callsCore' 'cdl_local' 'cmpParts\?' 'compoundT' 'coreBrute'
  'corePlans' 'coreRule2' 'core_item' 'delAt_run' 'disjointB' 'elabCdlAt'
  'eraseFold' 'eraseLeaf' 'getObj_wl' 'glob₂_fst' 'glob₂_snd' 'holds_wkD'
  'kindError' 'localStep' 'loopFalse' 'lvl_there' 'matchFind' 'memAt_upd'
  'newArr_lt' 'ok_of_map' 'opLocCode' 'peelHypsC' 'popAt_nat' 'popAt_wl'\'''
  'prim_find' 'rankBound' 'shortStep' 'showStmts' 'slotIdxC\?' 'sound_pop'
  'spath_sim' 'stripFold' 'surfaceOn' 'tight_pop' 'withBinds' 'withGlob₂'
  'Contract' 'Examples' 'NaturalA' 'Resolved' 'RunCanon' 'RunTight'
  'StateInv' 'StepRule' 'argsCode' 'args_sim' 'assertOk' 'assignIn'
  'bumpMemT' 'bump_key' 'callStep' 'canonInv' 'cell_inj' 'copyStep'
  'copy_sim' 'coreRule' 'coreSkip' 'elabDlCN' 'elabFmlC' 'example₁'
  'example₂' 'exec_mem' 'frameMsg' 'frameMut' 'guardLow' 'incOrder'
  'ite_frag' 'liftedT₂' 'loopFuel' 'loopStep' 'loopThen' 'lvl_here'
  'nat_bind' 'opStoreT' 'primName' 'prog_sim' 'pushCode' 'pushSlot'
  'pushStep' 'push_sim' 'pushedT₂' 'save_run' 'sendStep' 'send_run'
  'showSame' 'simpleIn' 'step_mem' 'stmt_sim' 'thinOlds' 'tightInv'
  'tourCore' 'ArrView' 'Binders' 'CallRet' 'ExtCall' 'LocOutT'
  'LoopAnn' 'MFields' 'Natural' 'NoStore' 'Premise' 'Problem'
  'ProvesC' 'SFields' 'Sequent' 'StmtOut' 'Storage' 'TGFrame'
  'UpdElem' 'ValOutT' 'beqFold' 'callStr' 'coreInv' 'coreTag'
  'ctxFrom' 'ctxOnto' 'elabDlC' 'fillFns' 'guardOk' 'inFragP'
  'incStep' 'into_ok' 'iteStep' 'ite_sim' 'liftedT' 'loc_sim'
  'lvl_ext' 'mayFind' 'mergeOn' 'newArrT' 'ok_bind' 'opLocIn'
  'opLocal' 'overlay' 'paramsN' 'popStep' 'pop_run' 'pop_sim'
  'push_ok' 'pushedT' 'rejects' 'ruleOf\?' 'sem_pay' 'seq_sim'
  'snapOld' 'spathIn' 'tryStep' 'unfold₁' 'val_sim' 'Branch'
  'Derive' 'EState' 'ExtArg' 'FShape' 'Frames' 'NewLhs'
  'Peeled' 'PrimTy' 'Proves' 'RunInv' 'Schema' 'Scoped'
  'Simple' 'TState' 'TWkRel' 'Taclet' 'VShape' 'ValOut'
  'ValidC' 'ValidT' 'argsIn' 'bindFl' 'cdlSeq' 'cellOf'
  'checkT' 'elemTy' 'fmtCat' 'freshT' 'hintOf' 'holdsC'
  'holdsT' 'inFrag' 'le_lvl' 'lvl_lt' 'meetsB' 'memRef'
  'opMemT' 'opStep' 'pushIn' 'see_wk' 'sendAt' 'split₁'
  'Agree' 'BinOp' 'Binds' 'Build' 'Chain' 'Delab'
  'ExecF' 'ExecP' 'ExecS' 'Focus' 'Grown' 'IdxLe'
  'Keeps' 'LineQ' 'MAddr' 'MHole' 'MPath' 'OpLoc'
  'Quote' 'RemOk' 'RunWT' 'SHole' 'SList' 'SPath'
  'Shape' 'StChg' 'Subst' 'Symex' 'THalt' 'TLoop'
  'TStep' 'Tight' 'VHole' 'Valid' 'Value' 'alice'
  'bind₁' 'boolT' 'bumpT' 'conn₁' 'consE' 'glob₂'
  'holds' 'locIn' 'offWk' 'paren' 'prog₁' 'sendT'
  'symex' 'tailE' 'toRes' 'uintT' 'valIn' 'wtInv'
  'ARhs' 'Args' 'CLTy' 'COut' 'Fold' 'Frag'
  'Grew' 'HRef' 'Heap' 'Held' 'Hyps' 'Link'
  'Look' 'MLoc' 'MObj' 'MRhs' 'MSrc' 'MVal'
  'NCtx' 'Objs' 'Olds' 'Path' 'Post' 'Prog'
  'Rule' 'SMap' 'SRef' 'SVal' 'SVec' 'Seen'
  'Stmt' 'TDom' 'TEnv' 'TRes' 'TRun' 'Thin'
  'TyLe' 'TyLt' 'UpdE' 'Walk' 'cell' 'ctxE'
  'els₁' 'lenU' 'litV' 'locV' 'ltyE' 'optQ'
  'pos₁' 'thn₁' 'upd₁' 'Ctx' 'Env' 'Ext'
  'Fml' 'HTy' 'Idx' 'LTy' 'Loc' 'Op0'
  'Op1' 'Op2' 'Op3' 'Out' 'Res' 'Rhs'
  'Seq' 'Sim' 'Src' 'Srt' 'TTx' 'Tms'
  'Tri' 'Upd' 'Val' 'cSE' 'fie' 'fmv'
  'fse' 'fsp' 'lit' 'loc' 'lvl' 'see'
  'tru' 'Fl' 'QM' 'SE' 'Tm' 'pv'
  'up' 'P' 'p' 'x' 'y'
)
# names ending in a word character end at a word boundary; `ruleOf?`,
# `compound_erase'` end with themselves
words=(); others=()
for n in "${CORE_FIRST[@]}"; do
  case "$n" in *[A-Za-z0-9_]) words+=("$n") ;; *) others+=("$n") ;; esac
done
alt=$(IFS='|'; echo "${words[*]}")
alt2=$(IFS='|'; echo "${others[*]}")
script=$(mktemp)
trap 'rm -f "$script"' EXIT
cat > "$script" <<SED
s#\`Core/([A-Z][A-Za-z]*)#\`\1#g
s/\bSolidity\.Calculus\.Core\./Solidity.Calculus./g
s/\bSolidity\.Evm\.Core([A-Z])/Solidity.Evm.\1/g
s/\bSolidity\.Semantics\.Core\.Typed/Solidity.Semantics./g
s/\bSolidity\.Semantics\.Core\./Solidity.Semantics./g
s/\bSolidity\.Semantics\.Core\b/Solidity.Semantics.Erased/g
s#\bCalculus/Core/#Calculus/#g
s#\bEvm/Core([A-Z])#Evm/\1#g
s#\bSemantics/Core/Typed#Semantics/#g
s#\bSemantics/Core/#Semantics/#g
s#\bSemantics/Core\.lean#Semantics/Erased.lean#g
/^(namespace|end) Core$/d
s/\bSolidity\.Evm\.Core\b/Solidity.Evm/g
s/\bEvm\.Core\b/Evm/g
s/\bSolidity\.Core\b/Solidity/g
s/(^|[^.[:alnum:]_'])Core\.($alt)\b/\1\2/g
s/(^|[^.[:alnum:]_'])Core\.($alt2)/\1\2/g
s/\bTState\b/State/g
s/\btrun([A-Z_])/run\1/g
s/\btrun\b/run/g
SED
# a citation of `Core/X` relative to `Calculus/` (in `Calculus/Core/*`,
# `Calculus/TacticSyntax`, `docs/module-map`) loses its `Core/`; the one
# outside `Calculus/` gains `Calculus/`
sed -i 's#`Core/Notation\.lean`#`Calculus/Notation.lean`#' Solidity/Examples/Chains/EvaluationOrder.lean
git ls-files -z '*.lean' '*.md' '*.sh' '*.mjs' '*.toml' ':!:tests/**' ':!:scripts/w5-rename.sh' ':!:docs/intrinsic.md' \
  | xargs -0 sed -E -i -f "$script"
# the corpus notes `scripts/solkey-port.mjs` writes cite module paths
sed -E -i -f "$script" tests/solkey/expected.tsv
# the record cites files by the paths they had at each step: history, like
# `git log`, which `check-doc-paths` does not read (decision 68)
sed -i 's#^  git ls-files -z \\$#  git ls-files -z -- '"':!:docs/intrinsic.md'"' \\#' scripts/check-doc-paths.sh
grep -q "git ls-files -z -- ':!:docs/intrinsic.md'" scripts/check-doc-paths.sh

echo "w5-rename: done; build with SolidityCorpus and SolkeyTestSuite, then commit"
