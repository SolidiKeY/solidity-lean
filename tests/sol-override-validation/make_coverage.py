"""Emit the reviewed arm/clause/control map and complete proof/fixture inventory.
The mapping is a review artifact, not instrumentation or a coverage theorem.
"""
import json
from pathlib import Path
import re
ROOT=Path(__file__).resolve().parents[2]
TESTS=ROOT/'tests/sol-override-validation'
rows=json.loads((TESTS/'matrix.json').read_text())
registered=set(re.findall(r'^import (\S+)',(ROOT/'Solidity.lean').read_text(),re.M))
ids={r['id'] for r in rows}
# Every Boolean checker has a named independent clause. Constructor/signature
# projections are primitive Source observations, explicitly outside that claim.
relations={
 'contractB':'Source top-level contract/interface constructor',
 'refersB':'Refers','baseEdgeB':'BaseEdge','ownB':'Own','ordinaryB':'SameSlot ordinary arm',
 'paramsB':'Params','sameSlotB':'SameSlot','ownMatchingB':'OwnMatching','shadowStepB':'ShadowStep','frontierB':'Frontier',
 'routeB':'Route / RelRoute',
 'visibilityAllowedB':'VisibilityAllowed','mutabilityAllowedB':'MutabilityAllowed',
 'signatureConditionB':'SignatureCondition','pairTypesB':'PairTypes','functionLikeB':'Virtual Source FunctionDefinition classification',
 'virtualB':'Virtual','compatibleB':'Compatible',
 'overrideOwnB':'OverrideOwn','overrideStepB':'OverrideStep','overrideFrontierB':'OverrideFrontier',
 'overrideEdgeB':'OverrideEdge','activeB':'Active','adjacentB':'Adjacent','avoidingB':'Avoiding',
 'cutVertexB':'CutVertex','retainedB':'Retained',
 'hasBaseB':'HasBase','hasOverrideBaseB':'HasOverrideBase','multipleB':'Multiple','singleInterfaceB':'SingleInterface',
 'listedB':'Listed','pathsDistinctB':'PathsDisjoint (pairwise)','namedListB':'NamedList','overrideListsB':'OverrideLists',
 'crossFamilyB':'CrossFamily','noCrossFamilyB':'NoCrossFamily','inheritedFamiliesB':'InheritedFamilies',
 'namespaceConflictB':'NamespaceConflict / ScopeEarlier','memberNamesB':'MemberNames',
 'declarationOverridesB':'DeclarationOverrides',
 'descriptorB':'Descriptor','topOwnerB':'Source owner constructor/top/scope projection',
 'getterReturnsB':'getterReturns','bytesSignatureB':'BytesSignature','fallbackShapeB':'FallbackShape',
 'attributesOKB':'AttributesOK','scopeKnownB':'ScopeKnown','graphValidB':'GraphValid',
 'exposesB':'Exposes','hasOwnB':'HasOwn','implementationB':'Implemented','ambiguityB':'AmbiguityResolved',
 'extractionB':'ExtractionOK','validateB':'OverrideGraphOK','tableAdjacentB':'Adjacent (materialized edge tables)',
 'fastAmbiguityB':'AmbiguityResolved via unconditional fastAmbiguityB_eq',
 'fastValidateB':'OverrideGraphOK via unconditional fastValidateB_eq',
}
controls={
 'Graph':['diamond-shared','diamond-required','diamond-listed','qualified-wrong-kind','private-base-no-local'],
 'Routes':['diamond-shared','pruning','upstream-triangle_no_impl'],
 'Compatibility':['function-external-public-view-pure','function-external-external-payable-view','function-nonvirtual','fallback-nonvirtual','receive-nonvirtual','getter-to-function','modifier-param-mismatch','function-location-public','function-location-external','function-return-mismatch','function-keeps-body'],
 'OverrideFrontier':['private-base-no-local','private-base-redeclaration','private-base-override','diamond-listed'],
 'Pruning':['pruning','pruning-no-local','upstream-triangle_no_impl','upstream-nonintermediate_common_base_and_unique_implementation','upstream-nonintermediate_common_base_and_unique_implementation_unimplemented'],
 'OverrideLists':['diamond-listed','diamond-missing-list','diamond-extra-list','diamond-duplicate-list','interface-multiple-missing','interface-multiple-listed','interface-fallback-implicit','interface-receive-implicit','fallback-extraneous','receive-extraneous','modifier-extraneous','getter-no-base','sibling-function-modifier','sibling-getter-modifier','sibling-private-modifier','sibling-different-name','getter-function-local-overload','function-getter-local-overload','getter-function-sibling-overload','function-getter-sibling-overload','getter-private-local-overload','getter-private-sibling-overload','getter-getter-local-overload','getter-getter-sibling-overload'],
 'Validity':['control-good-concrete','base-cycle','c3-inconsistent','interface-inherits-contract','getter-empty-struct','fallback-bad-parameter','fallback-bad-return','abstract-fallback','abstract-receive','library-virtual-modifier','library-modifier','state-private-override','state-internal-override'],
 'Selection':['same-name-different-body','modifier-body-identity','private-base-no-local','abstract-fallback','abstract-receive','upstream-correct_choice_for_base_function','upstream-nonintermediate_common_base_and_unique_implementation_unimplemented'],
 'Extraction':['same-name-different-body','modifier-body-identity'],
 'Validator':['control-good-concrete','diamond-listed','diamond-required','getter-interface'],
 'Memoized':['diamond-required','upstream-nonintermediate_common_base_and_unique_implementation','upstream-triangle_no_impl'],
}
# Each entry names all semantic alternatives of a multi-arm checker. Conditions
# in structure checkers name independent relation fields, not copied Booleans.
branches={
 'routeB':['same endpoint','different endpoint absent from available','consume source occurrence and recurse over each permitted edge'],
 'contractB':['contract','interface','nonowner / not top / scoped'],
 'ordinaryB':['function','getter','other'],
 'paramsB':['two extracted signatures','either missing'],
 'sameSlotB':['function/getter same name and parameters up to location','fallback regardless tuple','receive','modifier same name','different slots'],
 'signatureConditionB':['both signatures present','one missing'],
 'pairTypesB':['modifier exact parameters','fallback tuple may change','other returns up to location','non-external ordinary function exact parameter/return locations'],
 'compatibleB':['notGetter','virtual','visibility','mutability (modifier exemption)','keepsBody','types'],
 'virtualB':['written virtual','interface function/fallback/receive implicit virtual','other'],
 'adjacentB':['two active real declarations, either edge direction','artificial root to frontier','artificial top to active leaf','symmetric real-to-artificial','two artificial vertices false'],
 'tableAdjacentB':['same Adjacent arms with typed table retrieval'],
 'retainedB':['initial frontier','strict descendants of cuts removed','unimplemented cut itself removed','other frontier declarations retained'],
 'pathsDistinctB':['empty list','head disjoint from every suffix path; recursive suffix'],
 'overrideListsB':['absent: no raw base or single interface','present: NamedList'],
 'namedListB':['hasBase','complete when multiple','valid every entry','pairwise distinct resolved owners'],
 'crossFamilyB':['same-name modifier versus function/fallback/receive/getter','symmetric family direction','other names/families'],
 'namespaceConflictB':['distinct same-name getters','function before getter in checked C3','getter before different-signature function allowed','inherited private omitted, own private retained'],
 'bytesSignatureB':['exact bytes calldata parameter and bytes memory result','all other tuples false'],
 'fallbackShapeB':['no-parameter fallback','parameter fallback exact BytesSignature','other constructors false'],
 'getterReturnsB':['extracted nonempty returns','empty returns','unknown signature'],
 'descriptorB':['top agrees with scope','node constructor agrees with kind','nonempty collect head agrees on kind/top/scope/name','empty collect false'],
 'scopeKnownB':['top level','scoped with existing original owner'],
 'attributesOKB':['placement','signature','bodyVirtual','virtualPrivate','virtualLibrary','free','payable','specialVis','specialMut','receiveMut','interfaceBody','getter','fallbackShape','libraryOverrides','stateVariableOverride'],
 'graphValidB':['descriptors','attributes','roots','owners','uniqueOwners','noClashes','uniqueSlots','basePaths','earlier','linearizes'],
 'implementationB':['noncontract exemption','abstract exemption','no own/visible inherited slot','no chosen declaration false','chosen original declaration must be implemented'],
 'fastAmbiguityB':['local declaration','multiple raw candidates materialized pruning','at most one raw candidate'],
 'validateB':['extraction','validity','per-contract member names','inherited cross-family collision','own override legality','ambiguity','implementation'],
 'fastValidateB':['same complete judgment via unconditional equality'],
}
entries=[];proofs=[];modules=[]
for p in sorted((ROOT/'Solidity/Frontend/OverrideValidation').glob('*.lean')):
 text=p.read_text();module=p.stem;names=re.findall(r'^def ([\w.]+)',text,re.M)
 checks=[n for n in names if n.endswith('B')]
 for n in checks:
  assert n in relations,n
  selected=controls[module]
  assert set(selected)<=ids,(module,set(selected)-ids)
  entries.append(dict(checker=n,file=str(p.relative_to(ROOT)),relation=relations[n],
      arms=branches.get(n,[relations[n]+' independent clause alternatives']),controls=selected,
      kernelControls=['AdvancedControls.good_accepted','AdvancedControls.missing_rejected','AdvancedControls.substituted_rejected'] if module in ['Extraction','Validity','Validator'] else []))
 theorem_names=re.findall(r'^theorem (\S+)',text,re.M)
 proofs += [dict(file=str(p.relative_to(ROOT)),name='Solidity.Frontend.OverrideValidation.'+n,pin='tests/sol-override-validation/Trust.lean') for n in theorem_names]
 modules.append(dict(file=str(p.relative_to(ROOT)),definitions=names,theorems=theorem_names,
     centralRegistration='registered in current generated root' if 'Solidity.Frontend.OverrideValidation.'+module in registered else 'pending central registration REG-OV-1104'))
assert set(relations)=={x['checker'] for x in entries},set(relations)-{x['checker'] for x in entries}
projectionArms={
 'family':['function','fallback','receive','modifier','public state variable getter','other'],
 'overridePaths':['function','fallback','receive','modifier','state variable','other'],
 'writtenVirtual':['function','fallback','receive','modifier','other false'],
 'visibility':['ordinary function','fallback external flag','receive external flag','public getter external','modifier internal','other none'],
 'mutability':['function','fallback','receive payable flag','constant getter pure','other getter view','other none'],
 'implemented':['getter','original hasBody'],
 'getterField':['arrays omitted','mappings omitted','other fields retained'],
 'getterSignature':['mapping key argument and recurse','array uint256 index and recurse','struct storage fields filtered','elementary return'],
 'signature':['function tuple','no-parameter fallback','parameterized fallback','receive empty tuple','modifier absent/present params','public getter','other none'],
}
# Explicit per-arm controls replace the coarse module-level review sketch.
# $ = kernel theorem control; @ = guarded executable output (not kernel).
arm_rows = r"""
contractB|contract, interface, nonowner|control-good-concrete,interface-multiple-listed,$DefensiveControls.classifier_controls
refersB|resolved original owner|function-single-explicit
refersB|missing path, wrong kind|$DefensiveControls.absent_reference,qualified-wrong-kind
baseEdgeB|direct edge; absent or non-direct edge; noncontract|function-single-explicit,diamond-shared,control-good-concrete,$Controls.nested_frontiers
ownB|owner and scope agree; nonowner or different scope|$DefensiveControls.ownership_controls
ordinaryB|ordinary function; getter; other|function-single-explicit,getter-interface,$DefensiveControls.classifier_controls
paramsB|two signatures same parameters up to location; different parameters|getter-interface,getter-params-mismatch
paramsB|left or right signature missing|$DefensiveControls.missing_signature
sameSlotB|ordinary function/function same parameters|diamond-listed
sameSlotB|function/getter same name and parameters|getter-interface,getter-array
sameSlotB|ordinary parameters differ|getter-params-mismatch
sameSlotB|fallback ignores parameter/return tuple|fallback-params-to-empty,fallback-empty-to-params
sameSlotB|receive separate slot|receive-diamond-listed
sameSlotB|modifiers use name regardless parameter type|modifier-param-same,modifier-param-type
sameSlotB|different families or names|cross-function-modifier,cross-different-name
ownMatchingB|visible own matching slot|diamond-listed,$Controls.nested_frontiers
ownMatchingB|private excluded; nonmatching slot|$DefensiveControls.private_frontier_distinction,cross-different-name
shadowStepB|direct base with no own match; stop at own match|$Controls.nested_frontiers,upstream-interface_and_base_override_fine
frontierB|nested first-matching-owner routes|$Controls.nested_frontiers
frontierB|shared original declaration; self not inherited|diamond-shared,@Controls.edgeControls
routeB|same endpoint; absent available source; edge step; no outgoing edge|@Controls.routeControls
visibilityAllowedB|equal; external becomes public; other transition refused|function-external-external-nonpayable-nonpayable,function-external-public-nonpayable-nonpayable,function-public-external-nonpayable-nonpayable
mutabilityAllowedB|equal|function-external-external-nonpayable-nonpayable
mutabilityAllowedB|nonpayable becomes view or pure; view becomes pure|function-external-external-nonpayable-view,function-external-external-nonpayable-pure,function-external-external-view-pure
mutabilityAllowedB|payability change or weaker mutability refused|function-external-external-payable-view,function-external-external-pure-view
signatureConditionB|both extracted tuples; condition passes or refuses|modifier-param-same,modifier-param-type,function-return-mismatch
signatureConditionB|either signature missing|$DefensiveControls.missing_signature
pairTypesB|modifier parameters exactly preserved|modifier-param-same,modifier-param-type
pairTypesB|fallback tuple may change both directions|fallback-params-to-empty,fallback-empty-to-params
pairTypesB|other returns same up to location; return mismatch|getter-interface,function-return-mismatch
pairTypesB|external function location change allowed|function-location-external,function-return-location-external
pairTypesB|nonexternal function exact locations required|function-location-public,function-return-location-public,same-name-different-body
functionLikeB|ordinary function; fallback; receive; getter/modifier excluded|function-single-explicit,interface-fallback-implicit,interface-receive-implicit,getter-interface,modifier-1-1
virtualB|written virtual in each nongetter family|function-single-explicit,fallback-diamond-listed,receive-diamond-listed,modifier-1-1
virtualB|implicit interface ordinary/fallback/receive virtual|getter-interface,interface-fallback-implicit,interface-receive-implicit
virtualB|nonvirtual declarations refused when overridden|function-nonvirtual,fallback-nonvirtual,receive-nonvirtual
compatibleB|notGetter|getter-to-function
compatibleB|virtual|function-nonvirtual
compatibleB|visibility|function-public-external-nonpayable-nonpayable
compatibleB|mutability; modifier exemption|function-external-external-pure-view,modifier-1-1
compatibleB|keepsBody|function-keeps-body
compatibleB|types|modifier-param-type,function-return-mismatch
compatibleB|all fields pass|function-single-explicit,getter-interface
 overrideOwnB|own matching slot includes private|$DefensiveControls.private_frontier_distinction,private-base-redeclaration
 overrideStepB|base traversal stops at any own match including private|private-base-redeclaration,private-base-override
 overrideFrontierB|first raw matching owner on each base route|private-base-redeclaration,diamond-listed,diamond-shared
 overrideEdgeB|own declaration to raw inherited frontier; reverse not an edge|@Controls.edgeControls
activeB|initial declaration; descendant; inactive declaration|@Controls.edgeControls
adjacentB|real-active edges in either direction|@Controls.adjacencyControls
adjacentB|artificial root incident to raw frontier; symmetric direction|@Controls.adjacencyControls
adjacentB|artificial top incident to active leaves; symmetric direction|@Controls.adjacencyControls
adjacentB|artificial/artificial; inactive/nonleaf rejected|@Controls.adjacencyControls
avoidingB|incident endpoint deleted in both directions; unaffected edge retained|@Controls.avoidingControls
cutVertexB|active articulation; active non-articulation; inactive|@Controls.pruningControls
retainedB|not initially inherited|@Controls.pruningControls
retainedB|unimplemented cut itself removed|@Controls.pruningControls
retainedB|implemented initial declaration retained|@Controls.pruningControls
retainedB|strict descendant of cut removed on defensive invalid cyclic Source input|@Controls.strictDescendantControls,$Controls.cut_cycle_invalid
hasBaseB|visible inherited declaration; no base; private-only base excluded|diamond-shared,control-good-concrete,private-base-no-local
hasOverrideBaseB|raw private inherited declaration; no raw base|private-base-redeclaration,function-extraneous-override
multipleB|distinct originals; one shared original; no originals|diamond-listed,diamond-shared,function-extraneous-override
singleInterfaceB|single interface ordinary/fallback/receive|getter-interface,interface-fallback-implicit,interface-receive-implicit
singleInterfaceB|multiple interface bases or ordinary contract base not exempt|interface-multiple-missing,fallback-missing
listedB|correct owner; extraneous or wrong-kind owner|function-single-explicit,diamond-extra-list,qualified-wrong-kind
pathsDistinctB|empty; distinct owners; duplicate resolved owner|function-external-external-nonpayable-nonpayable,diamond-listed,diamond-duplicate-list
namedListB|hasBase|function-extraneous-override
namedListB|complete when multiple|diamond-listed,diamond-missing-list
namedListB|valid entries|diamond-extra-list
namedListB|distinct entries|diamond-duplicate-list
 overrideListsB|absent and no inherited declaration|control-good-concrete
 overrideListsB|absent and exactly one interface function|getter-interface,interface-fallback-implicit,interface-receive-implicit
 overrideListsB|absent with noninterface inherited declaration refused|fallback-missing,receive-missing
 overrideListsB|present plain or explicit named list|function-external-external-nonpayable-nonpayable,function-single-explicit,diamond-listed
crossFamilyB|modifier versus function/getter; reverse family direction|cross-function-modifier,cross-getter-modifier,cross-modifier-function,cross-modifier-getter
crossFamilyB|different name or unrelated families allowed|cross-different-name,same-name-different-body
noCrossFamilyB|local inherited cross-family collision; no collision|cross-function-modifier,cross-modifier-getter,cross-different-name
inheritedFamiliesB|sibling function/modifier or getter/modifier collision|sibling-function-modifier,sibling-getter-modifier
inheritedFamiliesB|private inherited function excluded; different names allowed|sibling-private-modifier,sibling-different-name
namespaceConflictB|distinct same-name getters|getter-getter-local-overload,getter-getter-sibling-overload,getter-getter-sibling-overload-reverse
namespaceConflictB|higher-priority function cannot hide getter|getter-function-local-overload,getter-function-sibling-overload
namespaceConflictB|higher-priority getter may hide different-parameter function|function-getter-local-overload,function-getter-sibling-overload
namespaceConflictB|own private included, inherited private omitted|getter-private-local-overload,getter-private-sibling-overload,private-getter-sibling-overload
memberNamesB|every exposed pair respects NamespaceConflict rule|getter-function-local-overload,function-getter-local-overload,getter-getter-sibling-overload,getter-private-local-overload,getter-private-sibling-overload
 declarationOverridesB|override list refusal|fallback-missing,diamond-missing-list
 declarationOverridesB|edge compatibility refusal|function-nonvirtual,function-return-mismatch
 declarationOverridesB|cross-family refusal|cross-function-modifier
 declarationOverridesB|all fields pass in all five families|function-single-explicit,fallback-diamond-listed,receive-diamond-listed,modifier-diamond-listed,getter-multiple-listed
 descriptorB|descriptor matches original collect head|$AdvancedControls.good_accepted
 descriptorB|top/scope mismatch; constructor mismatch; wrong head metadata; empty collection|$DefensiveControls.root_flag_refusal,$DefensiveControls.descriptor_defenses,$DefensiveControls.descriptor_refusal
 topOwnerB|contract; interface; library; nonowner; wrong flags|control-good-concrete,interface-multiple-listed,library-modifier,$DefensiveControls.classifier_controls,$DefensiveControls.root_flag_refusal
 getterReturnsB|nonempty elementary/indexed/struct return tuple|getter-array,getter-mapping,getter-struct
 getterReturnsB|empty returns refused; unknown signature refused|getter-empty-struct,$DefensiveControls.missing_signature
 bytesSignatureB|exact bytes calldata to bytes memory tuple|fallback-params-valid
 bytesSignatureB|bad parameter; bad return; absent/empty tuple|fallback-bad-parameter,fallback-bad-return,$DefensiveControls.bytes_refusals
 fallbackShapeB|no-parameter fallback|fallback-external-external-nonpayable-nonpayable
 fallbackShapeB|parameterized fallback exact tuple; bad tuple|fallback-params-valid,fallback-bad-parameter,fallback-bad-return
 fallbackShapeB|other constructor rejected|$DefensiveControls.fallback_other_constructor
 attributesOKB|placement|$DefensiveControls.attribute_defenses
 attributesOKB|signature|$DefensiveControls.attribute_defenses
 attributesOKB|bodyVirtual|$DefensiveControls.attribute_defenses,abstract-fallback,abstract-receive
 attributesOKB|virtualPrivate|function-private-private-nonpayable-nonpayable
 attributesOKB|virtualLibrary|library-virtual-modifier
 attributesOKB|free|$DefensiveControls.free_accepted,$DefensiveControls.free_virtual_rejected
 attributesOKB|payable|function-internal-internal-payable-payable
 attributesOKB|specialVis|$DefensiveControls.attribute_defenses
 attributesOKB|specialMut|fallback-external-external-view-view
 attributesOKB|receiveMut|receive-external-external-nonpayable-nonpayable
 attributesOKB|interfaceBody|$DefensiveControls.attribute_defenses,interface-fallback-implicit
 attributesOKB|getter|getter-empty-struct,getter-struct
 attributesOKB|fallbackShape|fallback-bad-parameter,fallback-bad-return,fallback-params-valid
 attributesOKB|libraryOverrides|$DefensiveControls.attribute_defenses,library-modifier
 attributesOKB|stateVariableOverride|state-private-override,state-internal-override,state-default-override,getter-interface
scopeKnownB|top-level; existing owner; missing owner|$AdvancedControls.good_accepted,$DefensiveControls.unknown_owner_refusal
 graphValidB|descriptors|$DefensiveControls.descriptor_refusal,$DefensiveControls.descriptor_defenses
 graphValidB|attributes|state-private-override,$DefensiveControls.attribute_defenses
 graphValidB|roots; owners|$DefensiveControls.root_flag_refusal,$DefensiveControls.unknown_owner_refusal
 graphValidB|uniqueOwners|$DefensiveControls.duplicate_owners_rejected
 graphValidB|noClashes|$DefensiveControls.duplicate_clash
 graphValidB|uniqueSlots|$DefensiveControls.duplicate_slots_rejected
 graphValidB|basePaths|$DefensiveControls.missing_base_rejected,interface-inherits-contract
 graphValidB|earlier|base-cycle,$Controls.cut_cycle_invalid
 graphValidB|linearizes|c3-inconsistent
exposesB|matching original scope and slot; wrong scope/name|same-name-different-body,cross-different-name
exposesB|own private allowed; inherited private excluded|$DefensiveControls.selection_private_controls
hasOwnB|own slot; inherited only; unrelated key|control-good-concrete,diamond-shared,cross-different-name
 implementationB|noncontract exemption; abstract exemption|interface-multiple-listed,abstract-fallback,abstract-receive
 implementationB|no own/visible inherited slot|private-base-no-local
 implementationB|chosen original declaration implemented; chosen declaration unimplemented|$AdvancedControls.good_accepted,$AdvancedControls.getter_accepted,$DefensiveControls.unimplemented_concrete
 implementationB|no chosen declaration on invalid cyclic input|$DefensiveControls.cyclic_choice_none,@DefensiveControls.cyclic
 ambiguityB|own declaration resolves ambiguity|diamond-listed
 ambiguityB|at most one pruned declaration|upstream-triangle_no_impl,upstream-common_base_and_unique_mention
 ambiguityB|multiple pruned originals with no local declaration refused, including private functions|diamond-required,fallback-diamond-no-local,receive-diamond-no-local,modifier-diamond-no-local,parallel-private-private-A-B,parallel-public-private-A-B,parallel-private-public-B-A,parallel-internal-private-B-A
 extractionB|exact typed original list; omitted member; substituted body|$AdvancedControls.good_accepted,$AdvancedControls.missing_rejected,$AdvancedControls.substituted_rejected
 validateB|extraction|$AdvancedControls.missing_rejected,$AdvancedControls.substituted_rejected
 validateB|validity|state-private-override,$DefensiveControls.duplicate_owners_rejected
 validateB|memberNames|getter-function-local-overload,function-getter-local-overload
 validateB|inheritedFamilies|sibling-function-modifier,sibling-private-modifier
 validateB|own override legality|fallback-missing,receive-missing
 validateB|ambiguity|diamond-required
 validateB|implementation|$DefensiveControls.unimplemented_concrete
 validateB|nonempty accepted all five families|$AdvancedControls.good_accepted,$AdvancedControls.getter_accepted,$AdvancedControls.fallback_accepted,$AdvancedControls.receive_accepted,$AdvancedControls.modifier_accepted
 tableAdjacentB|same real and artificial adjacency alternatives through typed tables|@Controls.tableAdjacencyControls,@Controls.tableControls
 fastAmbiguityB|local short circuit; multiple materialized graph; at most one raw declaration|diamond-listed,diamond-required,upstream-triangle_no_impl,diamond-shared
 fastValidateB|all validateB alternatives, unconditional equality rather than different specification|$AdvancedControls.good_accepted,$AdvancedControls.missing_rejected,$AdvancedControls.substituted_rejected,diamond-required,sibling-function-modifier,getter-function-local-overload
"""
arm_map={}
for line in arm_rows.strip().splitlines():
    checker,arm,links=[x.strip() for x in line.split('|')]
    links=[x.strip() for x in links.split(',')]
    assert checker in relations,checker
    fixtures=[x for x in links if x[0] not in '$@']
    assert set(fixtures)<=ids,(checker,set(fixtures)-ids)
    arm_map.setdefault(checker,[]).append(dict(arm=arm,clause=relations[checker]+': '+arm,
        fixtures=fixtures,kernelControls=[x[1:] for x in links if x.startswith('$')],
        executableControls=[x[1:] for x in links if x.startswith('@')]))
assert set(arm_map)==set(relations),(set(relations)-set(arm_map))
control_sources={}
for file,namespace in [('AdvancedControls','AdvancedControls'),('DefensiveControls','DefensiveControls'),('GraphControls','Controls')]:
    text=(TESTS/(file+'.lean')).read_text()
    for name in re.findall(r'^(?:def|theorem) (\S+)',text,re.M):
        control_sources[namespace+'.'+name]='tests/sol-override-validation/'+file+'.lean'
for entry in entries:
    entry['armControls']=arm_map[entry['checker']]
    entry['arms']=[a['arm'] for a in entry['armControls']]
    entry['controls']=sorted({f for a in entry['armControls'] for f in a['fixtures']})
    entry['kernelControls']=sorted({f for a in entry['armControls'] for f in a['kernelControls']})
    for a in entry['armControls']:
        for name in a['kernelControls']+a['executableControls']:
            assert name in control_sources,name
projection_rows = r"""
family|function|function-single-explicit
family|fallback|fallback-params-valid
family|receive|receive-diamond-listed
family|modifier|modifier-1-1
family|public state variable getter|get ter-interface
family|other constructor|$DefensiveControls.projection_defaults
 overridePaths|function|function-single-explicit
 overridePaths|fallback|fallback-diamond-listed
 overridePaths|receive|receive-diamond-listed
 overridePaths|modifier|modifier-diamond-listed
 overridePaths|state variable|getter-interface,state-private-override
 overridePaths|other none|$DefensiveControls.projection_defaults
writtenVirtual|function|function-single-explicit,function-nonvirtual
writtenVirtual|fallback|fallback-diamond-listed,fallback-nonvirtual
writtenVirtual|receive|receive-diamond-listed,receive-nonvirtual
writtenVirtual|modifier|modifier-1-1,modifier-0-1
writtenVirtual|other false|$DefensiveControls.projection_defaults
visibility|ordinary function|function-external-public-nonpayable-nonpayable
visibility|fallback external flag|fallback-params-valid,$DefensiveControls.attribute_defenses
visibility|receive external flag|receive-diamond-listed,$DefensiveControls.receive_flag_defenses
visibility|public getter external|getter-interface
visibility|modifier internal|modifier-1-1
visibility|other none|$DefensiveControls.projection_defaults
mutability|ordinary function|function-external-external-nonpayable-view
mutability|fallback|fallback-external-external-nonpayable-payable
mutability|receive payable flag|receive-diamond-listed,$DefensiveControls.receive_flag_defenses
mutability|constant getter pure|getter-constant-pure
mutability|other getter view|getter-interface,getter-ordinary-pure
mutability|other none|$DefensiveControls.projection_defaults
implemented|getter|getter-interface
implemented|original body present or absent|$AdvancedControls.good_original_body,$DefensiveControls.unimplemented_concrete
implemented|other false|$DefensiveControls.projection_defaults
getterField|arrays omitted, mappings omitted, scalar fields retained|getter-struct,getter-empty-struct
getterSignature|mapping key argument and recurse|getter-mapping,getter-nested
getterSignature|array uint256 index and recurse|getter-array,getter-nested
getterSignature|struct storage fields filtered|getter-struct,getter-empty-struct
getterSignature|elementary return|getter-interface
signature|function tuple|function-single-explicit
signature|no-parameter fallback|fallback-external-external-nonpayable-nonpayable
signature|parameter fallback|fallback-params-valid,fallback-bad-parameter,fallback-bad-return
signature|receive empty tuple|receive-diamond-listed
signature|modifier parameters absent or present|modifier-1-1,modifier-param-same
signature|getter|getter-interface,getter-array,getter-mapping,getter-struct
signature|other or unresolvable type|$DefensiveControls.projection_defaults,$DefensiveControls.attribute_defenses
""".replace('get ter-interface','getter-interface')
projection_map={}
for line in projection_rows.strip().splitlines():
    name,arm,links=[x.strip() for x in line.split('|')]
    links=[x.strip() for x in links.split(',')]
    fixtures=[x for x in links if not x.startswith('$')]
    assert set(fixtures)<=ids,(name,set(fixtures)-ids)
    kernels=[x[1:] for x in links if x.startswith('$')]
    for kernel in kernels: assert kernel in control_sources,kernel
    projection_map.setdefault(name,[]).append(dict(arm=arm,fixtures=fixtures,kernelControls=kernels))
assert set(projection_map)==set(projectionArms)
control_theorems=[]
for file,namespace in [('AdvancedControls','AdvancedControls'),('DefensiveControls','DefensiveControls'),('GraphControls','Controls')]:
    for name in re.findall(r'^theorem (\S+)',(TESTS/(file+'.lean')).read_text(),re.M):
        control_theorems.append(dict(file='tests/sol-override-validation/'+file+'.lean',
            name='Solidity.Frontend.OverrideValidation.'+namespace+'.'+name,pin='same file'))
result=dict(boundary='Reviewed clause/control mapping; execution coverage is external, not an instrumentation theorem. Source type/placement/C3 primitives remain lower-stage boundaries.',
 checkerArms=entries,sourceProjections=[dict(projection=n,armControls=arms) for n,arms in projection_map.items()],
 modules=modules,proofs=proofs,controlTheorems=control_theorems,controlSources=control_sources,
 fixtures=[dict(id=r['id'],file=r['file'],family=r['family'],phase=r['phase'],expected=r['expected']) for r in rows],
 kernelControls=dict(file='tests/sol-override-validation/AdvancedControls.lean',specialFamilies=['getter_accepted','fallback_accepted','receive_accepted','modifier_accepted'],identity=['good_dispatch','good_original_body','missing_rejected','substituted_rejected','private_override_rejected']),
 supplementalCompilerControls=dict(file='tests/sol-override-validation/getter-pipelines/cases.json',rows=12,pipelines=['legacy','viaIR'],output=['abi','evm.bytecode.object'],boundary='Code generation and ABI observations only; not EVM execution or kernel equivalence.'),
 pending=[f'central queue REG-OV-1104: {sum(m["centralRegistration"] != "registered in current generated root" for m in modules)} modules and135standard-axiom pins','repository final gates and cache delivery'],
 sourceBoundaries=['Source type extraction/equality and placement','Source checked C3 and name lookup','checked parser','G13 body/expression typing is not proved here','no G15 admission replacement or whole compiler adequacy'])
(TESTS/'coverage.json').write_text(json.dumps(result,indent=2)+'\n')
print('PASS coverage inventory:',len(entries),'Boolean checkers;',len(proofs),'library theorems;',len(rows),'fixture rows;',len(modules),'modules')
