#!/usr/bin/env python3
"""Exact delegated logical-contract graph, ending at intrinsic data/arithmetic.
No producer implementation is repaired or certified by this catalogue.
"""
import fcntl,hashlib,json,pathlib,re
HERE=pathlib.Path(__file__).resolve().parent;ROOT=HERE.parents[2]
SPECS=[]
def add(namespace,file,route,*names):
 for name in names:
  full=name.removeprefix('_root_.') if name.startswith('_root_.') else namespace+'.'+name
  SPECS.append((full,'Solidity/'+file+'.lean',name,route))
add('Solidity.Main','Theorems','main','ValidUnder','Derives','DerivesK','Rewrites','RewritesK','DoesAs','Runs','MRuns','MReverts','Compiles','Represents')
add('Solidity.Evm','Evm/Compile','core','Frag','inFrag','inFragP')
add('Solidity.Evm','Evm/Sim','core','SimL','Sim')
add('Solidity.Evm','Evm/Repr','store','ReprV','ReprAt','ReprStore','PathAt','PathSlot')
add('Solidity.Evm','Evm/SimLemmas','env','EnvSim')
add('Solidity.Evm.Compiler.Compilation','Evm/Compiler','checked','Input','Rep','Agrees')
add('Solidity','Calculus/PremiseSound','rules','Premise.Sound','Stmt.Sound')
add('Solidity','Calculus/Fml','rules','Premise.fml','_root_.Solidity.Modality.forallB')
add('Solidity','Calculus/Proves','logic','Hyps.wrap','_root_.Solidity.RuleSet.admits')
add('Solidity','Calculus/Logic','logic','holds','_root_.Solidity.Modality.afterRunTR','Fml.Valid')
add('Solidity.Spec','Calculus/Correct','logic','sat','Valid','toFml')
add('Solidity.Spec','Calculus/CorrectCallback','callback','satC','ValidC')
add('Solidity','Calculus/CallbackHolds','callback','Fml.stateInv','COut.thenF','holdsC','Invariant','ValidC')
add('Solidity','Semantics/Callback','callback','StateInv','Stmt.callsBack','Prog.callsBack','Frames.callsBack','Fml.callsBack')
add('Solidity.COut','Semantics/Callback','callback','after')
add('Solidity','Calculus/FirstOrder','callback','Fml.FO')
add('Solidity','Calculus/SolkeyFragment','solkey','Stmt.inSolkey','Fml.inSolkey')
add('Solidity','Calculus/TailMode','tail','ValidTail')
add('Solidity','Typing/CleanTail','tail','ordinaryDefaultFold','SVal.OrdinaryDefault','SFields.OrdinaryDefault','SList.OrdinaryDefault','SVec.OrdinaryDefault','cleanTailH','SVal.CleanTail','SFields.CleanTail','Storage.CleanTail')
add('Solidity','Semantics/RunFrame','halts','_root_.Solidity.Modality.onTHalt')
add('Solidity','Update','halts','Modality.onHalt')
add('Solidity.Evm.Memory','Evm/MemorySource','heap','PointerRepr','StateRepr')
add('Solidity.Evm.Memory','Evm/Memory','heap','ArrayRepr')
add('Solidity.Evm.Memory','Evm/MemoryHeap','heap','HeapRepr')
add('Solidity.Evm.Memory','Evm/MemoryStruct','struct','StructRepr')
add('Solidity.Evm.Memory','Evm/MemoryStructHeap','struct','StructHeapRepr','StructArraySeparated')
add('Solidity.Evm.Memory','Evm/MemoryRefs','struct','RefFieldsRepr')
add('Solidity.Evm.Memory','Evm/MemoryAlloc','allocator','FreeMemory','AllocatorRepr')
add('Solidity.Evm.Memory','Evm/MemoryStructAlloc','allocator','StructAllocatorRepr')
add('Solidity.Evm.Memory.Objects','Evm/MemoryObjects','objects','ValueRepr','header','cells','Ownership','ArrayRepr','HeapRepr','StateRepr')
add('Solidity.Evm.Memory.Objects','Evm/MemoryObjectAllocator','allocator','AllocatorRepr','AllocationInput','GrowsAllocator','KeepsAllocator')
add('Solidity.Evm.Memory','Evm/MemoryGrowResult','allocator','BaseExtends','GrowsAllocator','AllocationInput')
add('Solidity.Evm.Memory','Evm/MemoryRefArray','refarray','RefArrayRepr','RefArrayHeapRepr')
add('Solidity.Evm.Memory','Evm/MemoryRefArrayState','refarray','RefArrayStateRepr')
add('Solidity.Evm.Memory','Evm/MemoryFixedStorageCopy','fixed','FixedArrayRepr','FixedHeapRepr','FixedStateRepr')
add('Solidity.Evm.Memory.Loops','Evm/MemoryLoopCompile','loop','StmtCert.Cost','Cost','StmtCert.Demand','Demand','Room')
add('Solidity.Evm.Memory.LoopScopes','Evm/MemoryLoopScope','loop','StmtCost','Cost','StmtDemand','Demand','Room')
add('Solidity.Evm.Memory','Evm/MemoryCompile','budget','frameNeedProg','allocationCostProg')
add('Solidity.Evm.Memory.Construction','Evm/MemoryObjectAllocationCost','budget','allocationCostProg')
add('Solidity.Evm.Memory.StorageCopy','Evm/MemoryStorageCopyCompile','budget','allocationCostProg')
add('Solidity.Evm.Memory','Evm/MemoryCopyBound','budget','copyBoundProg')
add('Solidity','Calculus/Lands','rules','Held.OK','Upd.Lands','Upd.afterT')
add('Solidity','Semantics/Callback','callback','StateInv.at','ExecF','Fml.hasTransfer','Frames.hasTransfer','Stmt.forksIn')
add('Solidity','Semantics/NoPanic','callback','Stmt.hasTransfer','Prog.hasTransfer')
add('Solidity','Calculus/Proves','logic','Hyps.boxOnly','Fml.modalFree','Stmt.keyStep')
add('Solidity.Evm.Memory','Evm/MemoryLoop','loop','LoopPrefix','LoopRoom')

add('Solidity.Evm.Compiler','Evm/Compiler','checked','Compilation')
add('Solidity.Evm.Memory','Evm/MemoryCompile','checked','CompiledProg')
add('Solidity.Evm.Memory.ReferenceArrays','Evm/MemoryRefArrayCompile','checked','CompiledProg')
add('Solidity.Evm.Memory.Objects','Evm/MemoryObjectCompile','checked','CompiledProg')
add('Solidity.Evm.Memory.Construction','Evm/MemoryObjectConstructionCompile','checked','CompiledProg')
add('Solidity.Evm.Memory.Loops','Evm/MemoryLoopCompile','checked','CompiledProg')
add('Solidity.Evm.Memory.LoopScopes','Evm/MemoryLoopScopeCompile','checked','CompiledProg')
add('Solidity.Evm.Memory.Calls','Evm/MemoryCalls','checked','Program')
add('Solidity.Evm.Memory.StorageCopy','Evm/MemoryStorageCopyCompile','checked','CompiledProg')
add('Solidity.Evm.Memory.Fixed','Evm/MemoryFixedCompile','checked','CompiledProg')
add('Solidity.Evm.Memory.CopyConstruction','Evm/MemoryStorageConstructionCompile','checked','CompiledProg')

ROUTES={
'main':(['Families.closed_joint_witness','Calculus.assertion_rule_semantics','CheckedFamilies.checked_families_joint'],[],'Main aliases retain their original scoped, conditional meanings.'),
'core':(['Families.closed_simulation','Families.inhabited_fragment','Preconditions.dead_alias_fragment_rejected','MemoryInputs.primitive_input'],['H28-STMT-assign'],'Core contracts are inhabited; unsupported fragment clauses and unqueried statement/path instances remain explicit.'),
'store':(['Storage.write_compiler_application','PrimitiveFamilies.all_primitive_value_fields','Fragile.fragile_joint'],['H28-STMT-assign','H28-STMT-push'],'Primitive fields/root writes/fixed-index aliases are queried. Populated dynamic-storage elements, arbitrary mapping keys and all field/path cases are not thereby claimed.'),
'env':(['Environments.environment_simulation','Environments.mismatched_timestamp','Outcomes.refused_simulation'],[],'All four transaction-field equalities and matched refusal oracle inputs are constructed.'),
'checked':(['CheckedFamilies.checked_families_joint','MemoryInputs.primitive_joint','CheckedObjects.construction_joint','HeapQueries.concrete_object_allocator_kept'],['H28-RESOURCE-ROOM-LOOP','H28-RESOURCE-ROOM-SCOPE','H28-RESOURCE-CALLCOPY-COST','H28-RESOURCE-OBJECT-COST','H28-RESOURCE-COPY-EXTENT','H28-RESOURCE-FIXED-LIVE','H28-RESOURCE-REFARRAY-LIVE'],'All11 public constructor contracts have joint inputs/runs/output relations; scalar clients do not audit backend operations.'),
'rules':(['ScalarPremises.flag_rule_application','ScalarPremises.flag_split_application','Calculus.assertion_rule_semantics','Originals.original_arms_input'],['H28-PREMISE-inv','H28-PREMISE-branches','H28-PREMISE-allocBranches'],'True update/split/check/done antecedents are queried; remaining premise families have their exact constructor findings.'),
'logic':(['Originals.original_calculus_induction','Calculus.assertion_derivation','Calculus.assertion_runs'],['H28-PROVES-notLeft','H28-PROVES-closeFalse'],'The empty-context assertion derivation is inhabited; contradictory closure branches are not successful execution witnesses.'),
'callback':(['Originals.original_callback_formula','Originals.original_noCallback_formula','Originals.original_invariant_inputs','Callbacks.callback_program_resume','Callbacks.callback_program_revert','Callbacks.callback_program_violation'],['H28-PROVESC-recCall','H28-EXECS-tryOk'],'Actual first-order invariant, pay/noCallback, resumed/reverting/violated behaviors; unconstructed call/decode/recursive cases remain open.'),
'solkey':(['Calculus.solkey_equivalence','Calculus.solkey_strict','Calculus.solkey_rule_application','Calculus.zero_unwind_strict'],[],'Actual admitted derivation and strictness/exclusion witnesses retain the original RuleSet restriction.'),
'halts':(['VacuityControls.assumption_exhausts','VacuityControls.assumption_not_successful','Outcomes.compiler_panic_application','Outcomes.compiler_divergence_application','Callbacks.callback_revert'],[],'Typed onTHalt and update onHalt stay distinct; exhausted is not normal source success, panic is rejected, scoped target divergence may fault.'),
 'tail':(['TailSensitive.tail_clean_main','TailSensitive.tail_clean_source','TailSensitive.tail_dirty_source','TailSensitive.dirty_tail_reachable','TailSensitive.tail_premise_cannot_be_erased'],[],'A reachable dirty tail refutes erasing the clean premise. Arbitrary physical storage/compiler adequacy is not asserted.'),
'heap':(['MemoryInputs.fresh_object_state','MemoryInputs.primitive_joint','HeapQueries.primitive_source_observations','HeapQueries.live_array_layout_queried','MemoryControls.allocated_erasure_countercontrol'],['H28-RESOURCE-STRUCT-LIVE','H28-RESOURCE-REF-FIELDS','H28-RESOURCE-DISTINCT-OWNERS'],'A real nonempty dynamic primitive array/pointer is queried. Other object families and distinct-object ownership are not inferred from the whole relation.'),
'objects':(['CheckedObjects.construction_live_pointer','HeapQueries.live_array_layout_queried','HeapQueries.allocated_single_object','HeapQueries.distinct_object_domain_empty'],['H28-RESOURCE-STRUCT-LIVE','H28-RESOURCE-REF-FIELDS','H28-RESOURCE-DISTINCT-OWNERS','H28-RESOURCE-FIXED-LIVE','H28-RESOURCE-REFARRAY-LIVE'],'Actual header/primitive element and ownership above-frame are queried. The one-object fixture makes distinct-ID separation vacuous by a kernel proof; no second object/struct/reference-array witness is claimed.'),
'allocator':(['MemoryInputs.fresh_free_memory','MemoryInputs.fresh_object_allocator','AllocatorGrowth.primitive_allocator_growth','MemoryControls.near_end_allocator','MemoryControls.near_end_allocation_rejected','AllocatorGrowth.construction_allocator_growth','HeapQueries.concrete_object_allocator_kept','HeapQueries.live_base_extension_queried'],['H28-RESOURCE-CALLCOPY-COST','H28-RESOURCE-OBJECT-COST'],'Positive allocation cost/cursor256→258, near-end rejection, kept actual cursor and live old-reference extension are queried. Call/copy positive costs remain separate findings.'),
'struct':([],['H28-RESOURCE-STRUCT-LIVE','H28-RESOURCE-REF-FIELDS','H28-RESOURCE-DISTINCT-OWNERS'],'No live struct or struct reference field is allocated in these fixtures; cross-struct/array separation domains are not claimed exercised.'),
'refarray':(['CheckedFamilies.checked_families_joint'],['H28-RESOURCE-REFARRAY-LIVE'],'Whole reference-array contract is inhabited on a primitive-array rebind, but no reference-element array or child pointer field is queried.'),
'fixed':(['CheckedFamilies.checked_families_joint'],['H28-RESOURCE-FIXED-LIVE'],'Whole fixed contract is inhabited, but actual fixed-array object/payload fields are unexercised.'),
'loop':(['CheckedFamilies.checked_families_joint'],['H28-RESOURCE-ROOM-LOOP','H28-RESOURCE-ROOM-SCOPE'],'Scalar nonallocating programs inhabit whole contracts. Reached positive loop demand, loop-body cost and positive capacity are unexercised.'),
'budget':(['MemoryInputs.primitive_input','CheckedObjects.construction_input','CheckedFamilies.checked_families_joint','MemoryControls.near_end_allocation_rejected'],['H28-RESOURCE-ROOM-LOOP','H28-RESOURCE-COPY-EXTENT'],'Exact computed gates are evaluated at the actual fixture programs; positive copy extents and loop demand remain unexercised.')}
# Navigation routes never decide leaf-predicate inhabitation. Overrides bind
# aliases and unexercised object domains at declaration granularity.
OVERRIDES={
 'Solidity.Main.ValidUnder':(['Calculus.calculus_application'],[]),
 'Solidity.Main.Derives':(['Calculus.assertion_derivation'],[]),
 'Solidity.Main.DerivesK':(['Calculus.assertion_derivation','Calculus.solkey_application'],[]),
 'Solidity.Main.Rewrites':(['Families.every_rule_inhabited'],[]),
 'Solidity.Main.RewritesK':(['Calculus.solkey_rule_application'],[]),
 'Solidity.Main.DoesAs':(['Calculus.assertion_rule_semantics'],[]),
 'Solidity.Main.Runs':(['Families.source_true','Families.closed_joint_witness'],[]),
 'Solidity.Main.MRuns':(['Families.target_true','Families.closed_joint_witness'],[]),
 'Solidity.Main.MReverts':(['Families.target_false','Families.correct_revert','Outcomes.refused_target'],[]),
 'Solidity.Main.Compiles':(['Families.fragment_family','Families.inhabited_fragment'],[]),
 'Solidity.Main.Represents':(['Families.closed_simulation','Environments.environment_simulation'],[]),
 'Solidity.Evm.ReprV':(['PrimitiveFamilies.all_primitive_value_fields'],[]),
 'Solidity.Evm.Memory.FixedArrayRepr':([],['H28-RESOURCE-FIXED-LIVE']),
 'Solidity.Evm.Memory.FixedHeapRepr':([],['H28-RESOURCE-FIXED-LIVE']),
 'Solidity.Evm.Memory.RefArrayRepr':([],['H28-RESOURCE-REFARRAY-LIVE']),
 'Solidity.Evm.Memory.RefArrayHeapRepr':([],['H28-RESOURCE-REFARRAY-LIVE']),
 'Solidity.Evm.Memory.StructRepr':([],['H28-RESOURCE-STRUCT-LIVE']),
 'Solidity.Evm.Memory.StructHeapRepr':([],['H28-RESOURCE-STRUCT-LIVE']),
 'Solidity.Evm.Memory.StructArraySeparated':([],['H28-RESOURCE-STRUCT-LIVE','H28-RESOURCE-DISTINCT-OWNERS']),
 'Solidity.Evm.Memory.RefFieldsRepr':([],['H28-RESOURCE-REF-FIELDS']),
 'Solidity.Modality.forallB':(['ScalarPremises.flag_binding_antecedent','ScalarPremises.flag_binding_source'],['H28-PROVES-bindIntro']),
 'Solidity.ExecF':(['CallbackFrames.callback_nil_frame','CallbackFrames.callback_seq_frame','CallbackFrames.callback_halt_frame','CallbackFrames.callback_violated_frame','CallbackFrames.callback_pop_frame','CallbackFrames.callback_drop_frame'],[]),
 'Solidity.Evm.Memory.Loops.Demand':(['LoopContracts.scalar_loop_demand'],['H28-RESOURCE-ROOM-LOOP']),
 'Solidity.Evm.Memory.Loops.Cost':(['LoopContracts.scalar_loop_cost'],['H28-RESOURCE-ROOM-LOOP']),
 'Solidity.Evm.Memory.LoopScopes.Demand':(['LoopContracts.scalar_scope_demand'],['H28-RESOURCE-ROOM-SCOPE']),
 'Solidity.Evm.Memory.LoopScopes.Cost':(['LoopContracts.scalar_scope_cost'],['H28-RESOURCE-ROOM-SCOPE']),
 'Solidity.Evm.Memory.GrowsAllocator':(['AllocatorGrowth.primitive_allocator_growth'],['H28-RESOURCE-CALLCOPY-COST']),
 'Solidity.Evm.Memory.StructAllocatorRepr':(['AllocatorGrowth.primitive_allocator_growth'],['H28-RESOURCE-STRUCT-LIVE','H28-RESOURCE-REF-FIELDS']),
 'Solidity.Evm.Memory.Objects.GrowsAllocator':(['AllocatorGrowth.construction_allocator_growth'],['H28-RESOURCE-OBJECT-COST']),
 'Solidity.Evm.Memory.Objects.KeepsAllocator':(['HeapQueries.concrete_object_allocator_kept','HeapQueries.concrete_object_cursor_kept'],[]),
 'Solidity.Evm.Memory.BaseExtends':(['HeapQueries.live_base_extension_queried'],[]),
 'Solidity.Stmt.hasTransfer':(['LogicalGates.payment_syntax_gates'],[]),
 'Solidity.Prog.hasTransfer':(['LogicalGates.payment_syntax_gates'],[]),
 'Solidity.Frames.hasTransfer':(['LogicalGates.payment_syntax_gates'],[]),
 'Solidity.Fml.hasTransfer':(['LogicalGates.payment_syntax_gates','Originals.original_invariant_inputs'],[]),
 'Solidity.Frames.callsBack':(['LogicalGates.frame_callback_gates'],[]),
 'Solidity.Stmt.callsBack':(['LogicalGates.payment_syntax_gates'],[]),
 'Solidity.Prog.callsBack':(['LogicalGates.payment_syntax_gates'],[]),
 'Solidity.Fml.callsBack':(['LogicalGates.payment_syntax_gates'],[]),
 'Solidity.Stmt.forksIn':(['LogicalGates.payment_syntax_gates'],[]),
 'Solidity.Modality.onHalt':(['LogicalGates.halt_gate_domains'],[]),
 'Solidity.Modality.onTHalt':(['LogicalGates.halt_gate_domains'],[]),
 'Solidity.Hyps.boxOnly':(['LogicalGates.calculus_context_gates'],[]),
 'Solidity.Fml.modalFree':(['LogicalGates.calculus_context_gates'],[]),
 'Solidity.Stmt.keyStep':(['LogicalGates.calculus_context_gates'],[]),
 'Solidity.RuleSet.admits':(['LogicalGates.calculus_context_gates','Calculus.solkey_admission_application'],[]),
 'Solidity.Evm.Memory.LoopPrefix':([],['H28-RESOURCE-ROOM-LOOP']),
 'Solidity.Evm.Memory.LoopRoom':([],['H28-RESOURCE-ROOM-LOOP'])}

def sha(raw):return hashlib.sha256(raw).hexdigest()
def extract(text,name):
 pattern=r'^(?:(?:private|protected|noncomputable|partial) )*(?:def|abbrev|structure|inductive) '+re.escape(name)+r'(?=[\s{(:])'
 matches=list(re.finditer(pattern,text,re.M));assert len(matches)==1,(name,len(matches))
 m=matches[0];end=re.search(r'\n(?:(?:private|protected|noncomputable|partial) )*(?:def|abbrev|structure|inductive|theorem|namespace|end|section|mutual)\b',text[m.end():])
 stop=m.end()+end.start() if end else len(text)
 return text[m.start():stop].rstrip(),text[:m.start()].count('\n')+1

def catalogue():
 rows=[]
 for full,source,name,route in SPECS:
  raw=(ROOT/source).read_bytes();text,line=extract(raw.decode(),name);related,related_findings,boundary=ROUTES[route]
  witnesses,findings=OVERRIDES.get(full,(related,related_findings))
  ws=[{'file':'tests/h28-sol/non-vacuity/lean/Solidity/Assurance/NonVacuityH28/'+x.split('.')[0]+'.lean','name':'Solidity.Assurance.NonVacuityH28.'+x.split('.')[1]} for x in witnesses]
  fields=re.findall(r'^  ([\w]+)\s*:',text,re.M);constructors=re.findall(r'^  \| ([\w]+)',text,re.M)
  rows.append(dict(id=full,source=source,declaration=name,line=line,text=text,text_sha256=sha(text.encode()),source_sha256=sha(raw),route=route,related_route_witnesses=related,fields=fields,constructors=constructors,witnesses=ws,findings=findings,boundary=boundary,status='witnessed-with-findings' if ws and findings else 'witnessed' if ws else 'durable-open',preceding_declarations='\n'.join(l for l in raw.decode().splitlines()[:line-1] if re.match(r'^(import|namespace|variable|open)\b',l))))
 assert len({x['id'] for x in rows})==len(rows)
 return rows
if __name__=='__main__':
 lock=open('/tmp/solidity-lean-feature-groups-20261025/writer.lock','a');fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
 rows=catalogue();(HERE/'public-contracts.json').write_text(json.dumps({'status':'exact delegated logical-contract graph; field gaps retained','endpoint':'Intrinsic typed state/value/certificate data, typed evaluator/observer functions, primitive equality/arithmetic, and explicitly identified executable budget functions. Unexpanded immutable computational certificates are not producer-correctness claims.','contracts':rows},indent=2,ensure_ascii=False)+'\n')
 print(len(rows),'delegated contracts recorded')
