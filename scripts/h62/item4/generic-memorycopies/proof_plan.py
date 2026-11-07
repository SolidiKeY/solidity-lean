#!/usr/bin/env python3
"""Concrete owner-review proof obligations, not checked Lean implementation.

Keep all declarations from the three pending exact-file requests. Each public
control has an explicit disposition and original statement hash. No inference
from the plan is accepted as a proof, an agreement or a passing semantic gate.
"""
import argparse
import json
from pathlib import Path
from census import census, sha

PREFIX='Solidity/Backend/MemoryCopies/'
FILES=('CopyPathControls','MemoryPathCopyControls','FixedPathCopyControls')
PATH_ROUTES={
 'certificate_inhabited':('certificate','copiedPaths','Retain the exact original inhabited certificate.'),
 'reference_ids':('exact_layout','copy_path_bounds','Bounds are insufficient for exact IDs 1/2/4. Retain the existing exact layout proof until a separately checked layout lemma exists.'),
 'word_observations':('projected_contents','copy_path_contents','Instantiate typed paths and prove primitive projection commutes with snapshots; retain all three observations, including absence.'),
 'full_child_contents':('contents','copy_path_contents','Exact original instance with seed.heap, tree, map-free proof and refPath i0 i0.'),
 'reference_bounds':('bounds','copy_path_bounds','Retain arbitrary reference type/path and both inequalities; instantiate original frontier/count constants.'),
 'fixed_overrun':('absence','copy_path_absent_iff','Typed fixed-path absence; not emitted-code revert.'),
 'dynamic_overrun':('absence','copy_path_absent_iff','Typed dynamic-path absence; not emitted-code revert.'),
 'shadow_is_not_live':('shadow_and_absence','copy_path_absent_iff','Retain both storage observation some99 and live-memory absence. The absence lemma does not prove the storage half.'),
 'empty_copy':('absence','copy_path_absent_iff','Retain original empty source with storage shadow and reference-id projection of none.'),
 'long_copy':('contents_and_exact_layout','copy_path_contents','Primitive word comes from semantic contents; exact child ID64 remains separate layout evidence.'),
 'struct_path':('projected_contents','copy_path_contents','Retain actual Basket/items field proof and final uint projection.'),
 'path_preserved_after_second':('kept_path','copyPathObserver_keeps','Retain arbitrary typed path and actual Heap.Keeps witness of the second allocation.'),
 'contents_preserved_after_second':('kept_contents','copy_path_contents_keeps','Retain arbitrary result type U and original source snapshot under actual extension.'),
 'all_reference_paths_separated':('separation','copy_paths_separated','Retain both independently typed reference paths, successful observations and strict identity inequality.'),
 'descendant_ids_after_second':('exact_layout','copy_paths_separated','Strict separation does not give exact IDs1/8. Retain the exact layout computation separately.'),
 'wrong_word_rejected':('wrong_success_observation','copy_path_contents','Use the exact positive word instance plus unequal literals; no runtime refusal is inferred.'),
 'absence_matches_live_path':('absence_iff','copy_path_absent_iff','Preserve both directions, not just one implication.'),
}
BIND_ROUTES={
 'certificate_inhabited':('certificate','Retain the exact original inhabited certificate.'),
 'actual_binding':('represented_binding','Derive from existing semantic bind execution, not a run equality stored in a table. Preserve every conjunction and original premises.'),
 'pair_binding':('pair_instance','Project the original actual_binding instance for arbitrary left/right Fin W payloads; do not freeze them to11/23.'),
 'empty_binding':('empty_instance','Preserve allocator advance, destination and old alias; dynamic header zero is an additional conjunct only in the dynamic case.'),
 'long_binding':('long_instance','Retain 64 payloads, final source/destination words and shape-specific final cursor.'),
 'alias_source':('intrinsic_alias','Retain actual TRun alias result; no allocation/growth is introduced.'),
 'alias_target':('compiled_alias','Retain unchanged whole machine, not only the local pointer or cursor.'),
 'intrinsic_other_alias':('old_alias','Retain the original old reference weakened into the grown heap.'),
 'old_pointer_rejected':('wrong_success_observation','Use successful empty-copy determinism; keep arbitrary target and its run hypothesis.'),
 'indexed_binding':('indexed_success','Retain actual indexed input, resolution, snapshot, old aliases, payload and stack clauses.'),
 'indexed_refusal':('indexed_path_refusal','Preserve both path .error .revert and target .revert. The vacuous room proof on an invalid path is not a capacity-refusal witness.'),
}
EXTRA={
 'MemoryPathCopyControls':('wrong_payload_rejected','wrong_success_observation','Keep the second dynamic payload cell unequal to zero under the original successful-run hypothesis.'),
 'FixedPathCopyControls':('header_rejected','wrong_success_observation','Retain first headerless payload unequal to dynamic length2; do not add a header to fixed arrays.'),
}

def encoded(value):
    return (json.dumps(value,ensure_ascii=False,indent=2,sort_keys=True)+'\n').encode()

def produce(root, inventory):
    allfiles={Path(f['path']).stem:f for f in inventory['files']}
    cases=[];declarations=[];anchors={}
    for stem in FILES:
        file=allfiles[stem]
        public=[d for d in file['declarations'] if d['kind']=='theorem' and not d['header'].startswith('private ')]
        if stem=='CopyPathControls':
            routes=PATH_ROUTES
        else:
            producer='SelectedAlias.deepBindExecute' if stem=='MemoryPathCopyControls' else 'SelectedAlias.fixedDeepBindExecute'
            routes={name:(kind,producer,note) for name,(kind,note) in BIND_ROUTES.items()}
            extra,kind,note=EXTRA[stem];routes[extra]=(kind,producer,note)
        actual={d['name'] for d in public}
        if actual != set(routes):
            raise ValueError('unplanned or obsolete public controls: '+stem+' '+str(actual ^ set(routes)))
        for decl in file['declarations']:
            declarations.append(dict(path=file['path'],name=decl['name'],line=decl['line'],kind=decl['kind'],
                                     header_sha256=decl['header_sha256'],source_region_sha256=decl['source_region_sha256'],
                                     disposition='explicit_case_route' if decl['name'] in routes else 'retain_support_or_fixture_until_exact_correspondence',
                                     validation='pending'))
        for decl in public:
            kind,anchor,note=routes[decl['name']]
            anchor_file='CopyPaths' if stem=='CopyPathControls' else ('MemoryPathCopy' if stem=='MemoryPathCopyControls' else 'FixedPathCopy')
            anchor_kind='existing_semantic_producer'
            if stem=='CopyPathControls' and decl['name'] in {'reference_ids','descendant_ids_after_second'}:
                anchor_file=stem
                anchor='first' if decl['name']=='reference_ids' else 'second'
                anchor_kind='original_allocation_fixture; exact layout proof retained'
            elif stem!='CopyPathControls':
                local={'pair_binding':'actual_binding','empty_binding':'actual_binding','long_binding':'actual_binding',
                       'alias_source':'resolved','alias_target':'chosen','intrinsic_other_alias':'after',
                       'old_pointer_rejected':'empty_binding','wrong_payload_rejected':'pair_binding','header_rejected':'pair_binding'}
                if decl['name'] in local:
                    anchor_file=stem;anchor=local[decl['name']]
                    anchor_kind='original_local_proof_or_fixture'
                elif decl['name']=='certificate_inhabited':
                    anchor='memoryPathCopy' if stem=='MemoryPathCopyControls' else 'fixedPathCopy'
            selected=[d for d in allfiles[anchor_file]['declarations'] if d['name']==anchor]
            if len(selected)!=1:raise ValueError('missing or ambiguous original producer: '+anchor)
            found=selected[0]
            anchor_id=PREFIX+anchor_file+'.lean:'+anchor
            anchors[anchor_id]=dict(path=PREFIX+anchor_file+'.lean',name=anchor,line=found['line'],header_sha256=found['header_sha256'])
            cases.append(dict(path=file['path'],name=decl['name'],line=decl['line'],original_header=decl['header'],header_sha256=decl['header_sha256'],
                              route=kind,existing_boundary=anchor_id,anchor_kind=anchor_kind,obligation=note,
                              proof_status='pending; this plan is not a Lean proof',original_statement_must_remain_exact=True))
    if len(cases)!=41 or len(declarations)!=137:raise ValueError('frozen three-file inventory drift')
    return dict(schema=1,base='c6f550e281a7e5affa9a99bc2cdaed556dec00e4',
      inventory_sha256=sha(encoded(inventory)),scope=[PREFIX+stem+'.lean' for stem in FILES],
      boundary='Owner-review plan only. No checked generic lemma, typed fixture implementation, correspondence proof, original-file agreement, budget change or passing semantic gate.',
      counts=dict(files=3,declarations=137,public_controls=41,existing_source_anchors=len(anchors)),
      proposed_obligations={
        'P-CONTENTS':'Typed fixture H,T,U,heap:Heap H,value:SVal T,mapFree:T.mapFree=true,path:Path T U; prove projected read-back equality using copy_path_contents and congrArg (Option.map projection). Expected run/contents equality must not be a fixture field.',
        'P-PRIM-PROJECTION':'Prove at U=.prim .uint that the original value.val observation agrees with typed snapshot then SVal primitive projection. Preserve both some and none cases.',
        'P-EXACT-LAYOUT':'Exact IDs remain separate from contents/bounds. Retain original reference_ids, long child ID64 and descendant IDs1/8 proofs until exact typed allocation-layout instances are checked.',
        'P-UNIVERSAL-INPUTS':'Keep actual_binding universally quantified over every original fitting payload list; finite rows 0/2/64 do not replace its quantifiers. Pair inputs remain arbitrary Fin W words.',
        'P-DYNAMIC-FIXED':'Use distinct typed dynamic/fixed fixture records rather than erasing RefTy, count, State or context. Share payload data and singleton-HRef fixture proof only where the original types align.',
        'P-SINGLETON-REF':'Proposed intrinsic helper: for arbitrary R,Q and reference:HRef [R] Q, prove Q=R and HEq reference (the typed id0 HRef [R] R). Instantiate both original refs lemmas exactly; no duplicate heap representation.',
        'P-ALIAS':'Keep intrinsic alias, compiled unchanged-machine alias, weakened old alias and fresh deep binding as four distinct claims.',
        'P-REFUSAL':'Invalid indexed path supplies original path and target refusals; separately retained room implication on that invalid path is vacuous and is not capacity non-vacuity.',
        'P-EXACT-INSTANCE':'After Raw and owner approval, retain all137 original declaration headers, scope/binders/import dependencies and proof budgets; prove moved fixture equalities at original intrinsic types before original owners apply body patches.',
        'P-BUDGET-TIMING':'No heartbeat increases or native trust. Save baseline before any owner-applied patch; same tree/cache/resources, serial bounded checks, stop >10% slowdown. No measurement is implied by this plan.'},
      proposed_typed_fixture_and_lemma='''-- Proposal text only: pending Lean elaboration after Raw prerequisite.
structure IntrinsicPathFixture where
  H : HTy
  sourceType : Ty
  observedType : Ty
  heap : Heap H
  value : SVal sourceType
  memory : sourceType.mapFree = true
  path : Path sourceType observedType

theorem fixture_observations (fixture : IntrinsicPathFixture)
    (A : Type) (projection : SVal fixture.observedType → A) :
    let grown := fixture.value.copyStToM fixture.heap fixture.memory
    ((copyPathObserver grown.heap fixture.path grown.val).map
      (MVal.copyMToSt grown.heap)).map projection =
      ((fixture.value.findLiveM fixture.path).map SVal.strip).map projection := by
  exact congrArg (Option.map projection)
    (copy_path_contents fixture.heap fixture.value fixture.memory fixture.path)
''',
      layout_observations={
        'dynamic':dict(reference_type='.array (.prim primitive)',reservation='payloads.length + 1',payload_offset=1,empty_cursor=257,pair_cursor=259,long_cursor=321,empty_header='target.mem 256 = w[0]'),
        'fixed':dict(reference_type='.fixed (.prim primitive) count',reservation='max 1 count',payload_offset=0,empty_cursor=257,pair_cursor=258,long_cursor=320,empty_header='no dynamic header claim; first cell is payload when populated')},
      indexed_layout_observations={
        'dynamic':dict(initial_cursor=40,final_cursor=42,destination_cell=1,destination_pointer=40,old_alias_cell=2,old_alias_pointer=24,old_payload_cell=17,new_payload_cell=41,payload=7,stack=[77]),
        'fixed':dict(initial_cursor=40,final_cursor=41,destination_cell=1,destination_pointer=40,old_alias_cell=2,old_alias_pointer=24,old_payload_cell=16,new_payload_cell=40,payload=7,stack=[77])},
      planned_fixture_table='Typed input data only. Original seed/heap/shadows, arbitrary pair payloads, 0/2/64 lengths, typed paths and represented inputs; no stored execution theorem replacing the semantic proof.',
      existing_anchors=list(anchors.values()),declarations=declarations,cases=cases)

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--root',type=Path,default=Path.cwd())
    p.add_argument('--output',type=Path,required=True)
    p.add_argument('--check',type=Path)
    a=p.parse_args();report=produce(a.root,census(a.root));data=encoded(report)
    if a.check and a.check.read_bytes()!=data:raise SystemExit('PLAN_FAIL: correspondence plan or original inventory changed')
    a.output.write_bytes(data)
    print(json.dumps(dict(status='SOURCE_PLAN_PASS',sha256=sha(data),**report['counts']),sort_keys=True))

if __name__=='__main__':main()
