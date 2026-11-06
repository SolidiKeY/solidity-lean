#!/usr/bin/env python3
"""Reviewed source grouping of frozen memory-copy declarations, not proof replay.

The explicit family registry covers every module, including empty aggregators.
Each declaration retains its exact identity and statement/header hashes. Several
axes may apply simultaneously. Literal-evidence labels describe statement syntax
(including hypotheses), never an assertion that an implication's premise holds.
Curated cases record semantic distinctions that names/syntax alone cannot carry.
No label equates two statements, authorizes a migration, or excludes a case.
"""
import argparse
from collections import Counter
import json
from pathlib import Path
import re
from census import census, sha, mask, DECL, BOUNDARY
from audit import NEGATIVE, audit

# Explicit membership reviewed against original module docstrings and contracts.
# domains describe the family boundary, not a claim each declaration executes.
REGISTRY = [
 ('alias_binding', ['typed_heap','word_target','intrinsic_statement_run'],
  'Bind an existing reference; separate aliasing from allocating rebinding.',
  'AliasBinding'),
 ('allocating_rebinding', ['typed_heap','word_target','intrinsic_statement_run'],
  'Canonical path copying and runtime new-array rebinding allocate fresh roots while retaining old aliases.',
  'CanonicalRebind RuntimeRebind'),
 ('primitive_allocation', ['typed_heap','word_target'],
  'Fresh primitive copies, retained source/shadows, headerless fixed reservations.',
  'SingletonCopy PrimitiveArray PrimitiveArrayLive FixedMemoryCopy FixedStorageCopy RuntimeMemoryArray RuntimeStorageArray'),
 ('empty_reference_allocation', ['typed_heap','word_target'],
  'Empty live arrays at arbitrary map-free element types, including unused reference and struct children.',
  'EmptyReferenceMemory EmptyReferenceStorage'),
 ('checked_primitive_allocation', ['typed_heap','word_target'],
  'Actual capacity guards precede the same primitive copy; capacity reverts are target-only.',
  'CheckedMemoryArray CheckedStorageArray CheckedFixedMemory CheckedFixedStorage'),
 ('storage_path_binding', ['typed_heap','word_target','intrinsic_statement_run'],
  'Existing expression/path selection feeds fresh copying, declarations and rebinding.',
  'CanonicalArray CanonicalSingleton LoadedArray LoadedSingleton RuntimePathArray RuntimeLiveArray FixedStoragePath CheckedStoragePath CheckedFixedStoragePath'),
 ('memory_path_binding', ['typed_heap','word_target','intrinsic_statement_run'],
  'Resolve a typed memory path, allocate/adopt, then bind; retain old aliases and distinct path/capacity refusals.',
  'MemoryPathCopy FixedPathCopy CheckedPathCopy CheckedFixedPathCopy NestedMemoryPath NestedMemoryPathFrame'),
 ('fixed_reference_binding', ['typed_heap','word_target','intrinsic_statement_run'],
  'Original fixed reference values and storage paths feed live copying and binding without rewriting shadows.',
  'FixedReferenceLive FixedReferencePath FixedReferencePathCopy FixedReferenceDeclare FixedReferenceDeclareFrame FixedReferenceRebind'),
 ('nested_storage_copy', ['typed_heap','word_target','intrinsic_statement_run'],
  'Reserve parent, copy child turns/traversal, adopt and bind actual dynamic storage values.',
  'NestedStorageTurn NestedStorageLoop NestedStorageParent NestedStorageHeader NestedStorageLive NestedStoragePath'),
 ('fixed_reference_storage_copy', ['typed_heap','word_target'],
  'Headerless fixed-parent reservation/traversal/adoption with varying dynamic children.',
  'FixedReferenceStorageTurn FixedReferenceStorageLoop FixedReferenceStorageParent'),
 ('nested_memory_copy', ['typed_heap','word_target'],
  'Actual source headers/heap rows drive checked child traversal, parent adoption and demand.',
  'NestedMemoryTurn NestedMemoryLoop NestedMemoryMixed NestedMemoryRows NestedMemoryParent NestedMemoryParentMixed NestedMemoryParentDemand MemoryParentSnapshot'),
 ('copy_pipeline', ['typed_heap','word_target'],
  'Compose two actual copies; preserve first-copy results across second-phase refusal.',
  'StorageMemoryPipeline NestedLocationPipeline NestedLocationPipelineObservations NestedLivePipeline'),
 ('default_allocation', ['typed_heap','word_target','intrinsic_statement_run'],
  'Selected primitive/finite default plans, complete allocator transport and budget guards.',
  'DefaultSelection GuardedDefaultDeclaration CheckedDefault CheckedFiniteDefault BudgetedDefault BudgetedFinite'),
 ('reference_default_allocation', ['typed_heap','word_target','intrinsic_statement_run'],
  'Production-selected reference/nested defaults; unused children, complete runtime demand and guards.',
  'NestedDefault NestedDefaults SelectedArrayDefault SelectedArrayDefaults RuntimeArray RuntimeArrays CheckedReference BudgetedReference'),
 ('allocation_demand', ['typed_heap','word_target'],
  'Intrinsic reservation/word demand, planner agreement, cursor growth and alias zero growth.',
  'DefaultDemand SelectedDefaultDemand ReferenceDefaultDemand MemoryCopyDemand RuntimeGrowth'),
 ('overlap_and_capture', ['typed_heap','word_target'],
  'Forward/backward snapshot range copying and shallow capture overwrite with bounds.',
  'ForwardOverlap RangeOverlap TypedCapture CheckedCapture'),
 ('intrinsic_copy_contents', ['typed_heap'],
  'Published deep-copy contents, mirrors, rank-bounded snapshots and typed-path observation.',
  'HeapContents DeepCopyContents CopyPath CopyPaths SnapshotPath SnapshotPaths SnapshotTransport'),
 ('intrinsic_copy_footprint', ['typed_heap'],
  'Exact fresh identities, distinct descendants and symbolic cell demand of intrinsic copies.',
  'Traversal TraversalFresh TraversalFootprint TraversalWords'),
 ('source_byte_string_copy', ['source_execution'],
  'Source storage traversal, fresh payload/parent allocation and retained frame; no byte-target claim.',
  'SourceBytes SourceStrings SourceNestedBytes'),
 ('source_construction', ['source_execution'],
  'Existing Source defaults and recursive/fixed/reference/field/element closure.',
  'SourceConstruction SourceFields SourceLeaf SourceLeafArrays SourceStoredElements SourceStoredFields SourceStoredReferences'),
 ('source_copy_freshness', ['source_execution'],
  'Actual Source root and repeated copies, parent-last allocation and retained first-copy state.',
  'SourceRootCopies SourceStoredFresh'),
 ('source_frame_preservation', ['source_execution'],
  'Frame/old-object preservation on every outcome, including partial allocation and timeout.',
  'SourceFrames SourceFramesCore SourceDefaultFrames SourceStorageFrames'),
 ('source_horizons', ['source_execution'],
  'Fuel extension preserves non-timeout outcomes; timeouts may recover and retain partial allocations.',
  'SourceCopyHorizon SourceDefaultHorizon'),
 ('allocation_panic_boundary', ['source_execution','byte_target'],
  'Existing Source size-panic premise and exact byte emitter; never equate timeout with panic.',
  'AllocationPanic SourceSize SourceSizeInputs'),
 ('published_interfaces', ['typed_heap','word_target','intrinsic_statement_run','source_execution'],
  'Original and V2 certificate boundaries, concrete witnesses, roots/gaps and Source compatibility imports.',
  'Interface InterfaceV2 InterfaceV2Laws InterfaceV2Roots ControlsV2 Source'),
 ('published_producer_boundary', ['typed_heap','word_target','intrinsic_statement_run','source_execution'],
  'Actual published producer fields discharge local premises; unresolved external obligations stay explicit.',
  'PublishedStorage Premises'),
]

# Label -> exact statement syntax pattern; evidence retains offsets and excerpts.
# These labels intentionally do not infer execution from a theorem's name.
PATTERNS = {
 'bare_ok_literal': r'=\s*\.ok\b',
 'revert_literal': r'=\s*\.revert\b',
 'timeout_literal': r'=\s*\(?\s*\.error\s+\.timeout\b',
 'stuck_literal': r'=\s*\(?\s*\.error\s*\(?\s*\.stuck\b',
 'tuple_ok_literal': r'=\s*\(\s*\.ok\b',
 'option_absence_literal': r'=\s*none\b',
 'option_presence_literal': r'=\s*some\b',
 'negative_proposition': r'¬|≠|\bFalse\b',
 'inhabitation': r'\bNonempty\b',
 'execution_relation': r'\brun\b|\.run\b|\bcheckedRun\b|\bTRun\b',
 'heap_ownership': r'\bHeapRepr\b|\bAllocatorRepr\b|\bStateRepr\b|\bReprAt\b',
 'payload_observation': r'\bpayloads?\b|\bcontents\b|\bcopyMToSt\b|\bfindLiveM\b|\bbyteContent\b|\.mem\b|\.heap\.get\b',
 'identity_observation': r'\bHRef\b|\.id\b|\bBaseExtends\b|\bmemRef\b',
 'allocator_observation': r'\bAllocatorRepr\b|\bheapWords\b|\bliveWordCount\b|\.heap\.next\b|\bcursor\b',
 'local_or_stack_observation': r'\.stack\b|\bsetLocal\b|\.env\b|\bTRun\b',
 'frame_or_gap_observation': r'\bKeeps\b|\bGap\b|\bAllocationExtension\b|\bAllocatesOnly\b|\bnonheap\b',
 'compiler_selection': r'\bcompileStmt\b|\bcompileDefault\b|\bcompileFiniteDefault\b|\bofTarget\b',
 'certificate_statement': r'\w*(?:Certificate|Premise|Outcome|Witness|Result)\b',
}
# Search names only for navigation topics, never for terminal result classification.
TOPICS = {
 'alias_identity': r'alias|shared|sharing|fresh|identit|separat|distinct',
 'shadow_noninterference': r'shadow|same_copy|unread|unused',
 'capacity_boundary': r'capac|budget|saturat|fitt|room|boundary|endpoint|huge|oversiz|maximal',
 'path_selection': r'path|index|indexed|selection|lookup|bounds|overrun',
 'refusal_or_negative': r'refus|reject|wrong|bad|overrun|not_|panic|fail|exhaust|timeout|invalid|absen|refut',
 'allocation_demand': r'demand|growth|cost|cursor|reservation|words|span',
 'preservation': r'preserv|retain|kept|keeps|frame|gap|old_|nonheap',
 'contents_layout': r'content|payload|header|word|root|layout|field|element|pointer|length',
 'horizon': r'horizon|timeout|fuel|recovered',
 'empty_or_long_variant': r'empty|zero|long|two_|pair|mixed|heterogeneous|repeated',
}

# Each curated fact is reviewed against the original statement. This list pins
# name traps and mixed claims, not an alternate proof or a comprehensive proof
# of the classifier. expected excerpts below are checked against frozen source.
CURATED = {
 ('ControlsV2','default_cost_W_rejected'): ('certificate_impossibility', ['¬','Nonempty'], 'No runtime panic/revert follows from lack of a certificate.'),
 ('TypedCaptureControls','invalid_bounds'): ('intrinsic_option_refusal', ['checkedCaptureOverwrite','= none'], 'Intrinsic checked capture returns none; not a target revert.'),
 ('TypedCaptureControls','reference_identities'): ('shallow_identity_overwrite', ['MObj.elems'], 'Shallow overwrite preserves the identity-bearing child objects; not fresh deep descendants.'),
 ('ForwardOverlapControls','right_overlap_run'): ('successful_corruption', ['= .ok corrupted'], 'Actual successful forward execution corrupts right-overlapping contents.'),
 ('SourceCopyHorizonControls','mapping_refusal'): ('source_stuck_unchanged', ['.stuck','before true'], 'Mapping copy refusal is Source stuck and retains the input.'),
 ('SourceCopyHorizonControls','mapping_horizon'): ('source_stuck_unchanged', ['.stuck','1 + slack'], 'Added fuel preserves the non-timeout Source stuck result.'),
 ('SourceCopyHorizonControls','partial_timeout'): ('source_timeout_partial_allocation', ['.error .timeout','heap.next = 2'], 'Timeout retains an allocated child.'),
 ('SourceCopyHorizonControls','old_and_nonheap'): ('frame_on_partial_timeout_path', ['frame 6 T path','heap.get 0'], 'Frame/old-object statement concerns the partial-timeout input, not only successful loads.'),
 ('SourceCopyHorizonControls','recovered'): ('source_success_after_timeout', ['frame 7 T path','= some (3,4)'], 'The larger horizon succeeds after the smaller-horizon timeout.'),
 ('SourceStoredReferencesControls','horizon_refusal'): ('source_timeout_unchanged', ['.error .timeout','result.2 = before'], 'Timeout here preserves the input; other Source timeouts may allocate.'),
 ('CheckedMemoryArrayControls','guard_reads_cursor'): ('mixed_success_and_target_revert', ['∃ fits','= .revert'], 'One statement combines represented success and moved-cursor target revert.'),
 ('CheckedStorageArrayControls','header_selects_capacity'): ('mixed_success_and_target_revert', ['∃ fits','= .revert'], 'Empty header fits while the pair header refuses at the same cursor.'),
 ('NestedMemoryLoopControls','saturated_completed_suffix'): ('success_at_saturation', ['.ok','target = moved [] wMax'], 'A completed suffix succeeds without further allocation even at saturation.'),
 ('FixedReferenceStorageLoopControls','saturated_empty_success'): ('success_at_saturation', ['FixedReferenceStorageLoopResult'], 'Zero remaining traversal succeeds at saturation.'),
 ('EmptyReferenceStorageControls','unread_storage_run'): ('success_despite_unread_storage', ['.ok'], 'Successful allocation ignores unread storage, not negative execution.'),
 ('EmptyReferenceStorageControls','wrong_header_not_represented'): ('invalid_representation_premise', ['¬','ReprAt'], 'A wrong header refutes input representation, not runtime execution.'),
 ('CheckedDefaultControls','unfittable_selected'): ('inhabited_selector', ['Nonempty'], 'Selection remains inhabited although subsequent execution cannot fit.'),
 ('CheckedDefaultControls','unused_huge_child'): ('successful_unused_child', ['some'], 'Empty-parent success does not evaluate/allocate an unreachable huge child.'),
 ('BudgetedReferenceControls','unused_huge_child'): ('successful_unused_child', ['some'], 'Size-zero success despite an unused W-sized child; size one is separate refusal.'),
 ('CheckedFixedMemoryControls','huge_code_only_refusal'): ('code_only_target_revert', ['checkedFixedMemoryCode','= .revert'], 'Actual code refusal; no represented W-sized source is claimed.'),
 ('CheckedFixedMemoryControls','room_boundary_refused'): ('arithmetic_capacity_impossibility', ['¬'], 'Only a strict arithmetic room inequality is refuted.'),
 ('DefaultDemandControls','no_word_capacity'): ('witness_impossibility', ['¬','Nonempty'], 'No AllocatorWitness W exists; not runtime failure.'),
 ('DefaultDemandControls','finite_selector_boundary'): ('selector_option_refusal', ['none','liveWordCount'], 'Selector limitation coexists with defined intrinsic semantic demand.'),
 ('GuardedDefaultDeclarationControls','unsupported_reference_field'): ('compiler_selection_refusal', ['compileStmt','false'], 'Production compiler selection fails; no runtime trace is asserted.'),
 ('AliasBindingControls','fresh_pointer_rejected'): ('wrong_success_observation', ['≠'], 'Successful alias binding is distinguished from a fresh-copy pointer.'),
 ('NestedMemoryPathControls','wrong_alias_for_deep_copy'): ('wrong_success_observation', ['≠'], 'Reject a wrong observation of successful deep copy, not the operation.'),
 ('PrimitiveArrayLiveControls','same_copy'): ('shadow_noninterference', ['copyStToM'], 'Different storage shadows yield the same live memory copy.'),
 ('CopyPathControls','shadow_is_not_live'): ('stored_shadow_and_absent_live_path', ['some 99','none'], 'Storage shadow remains observable in storage while absent on the live memory path.'),
 ('CopyPathControls','fixed_overrun'): ('absent_path_observation', ['= none'], 'Out-of-range typed-path observation is absent; no target run is asserted.'),
 ('CopyPathControls','dynamic_overrun'): ('absent_path_observation', ['= none'], 'Dynamic typed-path observation is absent; no runtime revert claim.'),
 ('SnapshotPathInterface','SnapshotPathFailure'): ('successful_prefix_and_intrinsic_refusal', ['some mid','= none','SnapshotPathObservation'], 'Keep the successful prefix, failing checked step and observation of the reached heap.'),
 ('SnapshotPathControls','failure_prefix'): ('prefix_preserved_before_option_refusal', ['rightAfter'], 'Retain changed words of the successful prefix before checked schedule failure.'),
 ('SnapshotPathControls','long_schedule'): ('long_operation_schedule', ['List.replicate 64'], '64 repeated operations are a schedule length, not 64 copied payload words.'),
 ('SourceFramesControls','partial_timeout_keeps_allocation'): ('retained_partial_allocation', ['heap.next','heap.get'], 'Allocated child and old objects remain after timeout.'),
 ('SourceFramesControls','partial_state_ne_input'): ('partial_state_not_rollback', ['oneChild ≠ before'], 'The reached partially allocated state differs from the input.'),
 ('SourceStoredFreshControls','second_timeout_keeps_first'): ('second_timeout_retains_first_copy', ['.timeout'], 'Second-copy timeout retains the already-created first copy.'),
 ('NestedMemoryParentControls','child_refusal_after_successful_prefix'): ('intermediate_success_then_target_revert', ['.ok','.revert'], 'Intermediate successful child is witnessed; .revert does not return that state.'),
 ('AllocationPanic','timeout_not_panic'): ('source_panic_premise_exclusion', ['¬ Panic41Premise'], 'Source horizon exhaustion cannot supply allocation-panic premise.'),
 ('AllocationPanic','zero_length_not_panic'): ('source_panic_premise_exclusion', ['¬ Panic41Premise'], 'Zero-length success cannot supply allocation-panic premise.'),
 ('MemoryPathCopyControls','actual_binding'): ('binding_full_observations', ['AllocatorRepr','target.mem 0','target.mem 256','target.mem 1','target.mem 2','target.mem 7','target.stack','257 + index','17 + index'], 'Retain execution, allocator/cursor, header, local store, old alias, frame, stack and both payload ranges.'),
}

def family_of(stem):
    if stem == 'Interface':
        return stem
    for suffix in ('Controls','Interface'):
        if stem.endswith(suffix):
            return stem[:-len(suffix)]
    return stem

def registry():
    result = {}
    for group, domains, description, members in REGISTRY:
        for family in members.split():
            if family in result:
                raise ValueError('duplicate family: ' + family)
            result[family] = dict(group=group, domains=domains, description=description)
    return result

def role(stem, decl):
    private = decl['header'].startswith(('private ', 'private noncomputable '))
    control = 'Controls' in stem or (stem == 'AllocationPanic' and decl['name'] in {'input','expression','oversized_panic','oversized_emission','marked_emission','wrong_outcomes_rejected','timeout_not_panic','zero_length_not_panic'})
    if decl['kind'] in ('structure','inductive'):
        return 'control_fixture_type' if control else 'contract_or_typed_data'
    if control:
        if decl['kind'] in ('theorem','lemma'):
            return 'control_support_lemma' if private else 'control_statement'
        return 'control_fixture' if private else 'control_witness_or_definition'
    if decl['kind'] in ('theorem','lemma'):
        return 'semantic_support_lemma'
    if re.search(r':\s*Prop\s*$', decl['header']):
        return 'contract_predicate'
    return 'semantic_definition'

def build(root, inventory):
    byfamily = registry()
    old_audit={(row['path'],row['line'],row['name']):row['audit_candidates'] for row in audit(inventory)['rows']}
    modules = []
    rows = []
    seen_curated = set()
    for file in inventory['files']:
        path = root / file['path']
        text = path.read_text()
        clean = mask(text)
        stem = path.stem
        family = family_of(stem)
        if family not in byfamily:
            raise ValueError('unregistered family: ' + stem + ' -> ' + family)
        entry = byfamily[family]
        doc = re.search(r'/-!([\s\S]*?)-/',text)
        modules.append(dict(path=file['path'], file_sha256=file['sha256'], family=family,
                            **entry, module_doc=' '.join(doc[1].split()) if doc else '',
                            declaration_count=len(file['declarations']), aggregator=not file['declarations']))
        matches=list(DECL.finditer(clean))
        for index, decl in enumerate(file['declarations']):
            start=matches[index].start()
            end=matches[index+1].start() if index+1<len(matches) else len(text)
            boundary=BOUNDARY.search(clean,matches[index].end(),end)
            if boundary: end=boundary.start()
            # Structures and Prop-valued predicates carry statement clauses in
            # their bodies. Theorem proof bodies never contribute literal claims.
            whole_claim=decl['kind'] in ('structure','inductive') or bool(re.search(r':\s*Prop\s*$',decl['header']))
            claim=text[start:end] if whole_claim else decl['header']
            claim_clean=mask(claim)
            evidence=[]
            for label, pattern in PATTERNS.items():
                for found in re.finditer(pattern,claim_clean):
                    evidence.append(dict(axis=label, excerpt=claim[found.start():found.end()],
                                         context=claim[max(0,found.start()-40):min(len(claim),found.end()+60)],
                                         byte_start=len(text[:start+found.start()].encode()),
                                         byte_end=len(text[:start+found.end()].encode())))
            topics=sorted(label for label,pattern in TOPICS.items() if re.search(pattern,decl['name'],re.I))
            legacy_negative=bool(decl['kind'] in ('theorem','lemma') and NEGATIVE.search(decl['name']))
            key=(stem,decl['name'])
            fact=None
            if key in CURATED:
                category,excerpts,note=CURATED[key]
                # Excerpt may be in the full predicate body, never an unrelated file.
                for excerpt in excerpts:
                    if excerpt not in claim:
                        raise ValueError('curated source excerpt missing: '+str(key)+' '+excerpt)
                fact=dict(category=category, statement_excerpts=excerpts, note=note)
                seen_curated.add(key)
            local_names=sorted(set(re.findall(r"[A-Za-z_][A-Za-z_0-9']*",claim)) & {d['name'] for d in file['declarations']} - {decl['name']})
            semantic_audit=[]
            if entry['group'] in {'storage_path_binding','memory_path_binding','fixed_reference_binding'}:
                semantic_audit.append(9)
            if role(stem,decl) in {'control_fixture','control_fixture_type','control_support_lemma'}:
                semantic_audit.append(11)
            if role(stem,decl) in {'control_statement','control_witness_or_definition'}:
                semantic_audit.append(16)
            rows.append(dict(audit_candidates=old_audit[file['path'],decl['line'],decl['name']],
                             semantic_audit_routes=semantic_audit,id=file['path']+':'+str(decl['line'])+':'+decl['name'],path=file['path'],line=decl['line'],name=decl['name'],
                             kind=decl['kind'],header_sha256=decl['header_sha256'],source_region_sha256=decl['source_region_sha256'],
                             role=role(stem,decl),family=family,semantic_group=entry['group'],family_domains=entry['domains'],
                             statement_axes=sorted({e['axis'] for e in evidence}),literal_evidence=evidence,
                             navigation_topics=topics,legacy_negative_name_signal=legacy_negative,
                             local_statement_references=local_names,curated_semantics=fact))
    if seen_curated != set(CURATED):
        raise ValueError('missing curated declarations: '+str(set(CURATED)-seen_curated))
    roles=Counter(row['role'] for row in rows)
    groups=Counter(row['semantic_group'] for row in rows)
    refusal_ids=sorted(row['id'] for row in rows if row['legacy_negative_name_signal'] or
        set(row['statement_axes']) & {'negative_proposition','revert_literal','timeout_literal','stuck_literal','option_absence_literal'} or
        (row['curated_semantics'] and re.search(r'refus|timeout|exclusion|impossib',row['curated_semantics']['category'])))
    alias_ids=sorted(row['id'] for row in rows if 'alias_identity' in row['navigation_topics'] or
        'identity_observation' in row['statement_axes'] or
        (row['curated_semantics'] and row['curated_semantics']['category'] in {'binding_full_observations','shallow_identity_overwrite'}))
    return dict(schema=1,base='c6f550e281a7e5affa9a99bc2cdaed556dec00e4',
                inventory_sha256=sha((json.dumps(inventory,ensure_ascii=False,indent=2,sort_keys=True)+'\n').encode()),
                boundary='Reviewed semantic-family source grouping, not theorem equivalence, proof replay, case exclusion, owner permission, or passing semantic gate. Literal axes include hypotheses; navigation topics do not classify terminal outcomes.',
                counts=dict(modules=len(modules),declarations=len(rows),curated_cases=len(seen_curated),roles=dict(sorted(roles.items())),groups=dict(sorted(groups.items()))),
                retained_refusal_related_ids=refusal_ids,retained_alias_identity_ids=alias_ids,
                modules=modules,declarations=rows)

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--root',type=Path,default=Path.cwd())
    p.add_argument('--output',type=Path,required=True)
    a=p.parse_args()
    report=build(a.root,census(a.root))
    data=(json.dumps(report,ensure_ascii=False,indent=2,sort_keys=True)+'\n').encode()
    a.output.write_bytes(data)
    print(json.dumps(dict(sha256=sha(data),**report['counts']),sort_keys=True))

if __name__=='__main__': main()
