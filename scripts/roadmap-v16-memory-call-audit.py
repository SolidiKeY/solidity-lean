#!/usr/bin/env python3
"""Read-only, revision-bound accounting for the actual V16 memory-call consumer.
No constructor/profile/stage obligation is discharged by this structural audit.
"""
import argparse, importlib.util, json, pathlib, subprocess, sys
sys.dont_write_bytecode = True
ROOT = pathlib.Path(__file__).resolve().parents[1]
PRODUCER = '91e94ab57305ca055127934fd9e68fe9ea5e6be3'
FILES = ['Solidity/Evm/Compiler.lean', 'Solidity/Evm/MemoryCalls.lean',
         'Solidity/Evm/MemoryCallExamples.lean']
CONSTRUCTOR = 'Solidity.Evm.Compiler.Compilation.memoryCalls'
spec = importlib.util.spec_from_file_location('v16_core_accounting', ROOT/'scripts/roadmap-v16-accounting.py')
core = importlib.util.module_from_spec(spec); spec.loader.exec_module(core)
P = 'Solidity.Roadmap.V16.'
T = P+'MemoryCallControls.'
REQUIRED = {
 P+'memory_call_not_exhausted': {P+'memory_call_failure'},
 P+'memory_call_capacity': {'Solidity.Evm.Compiler.Compilation.memoryCalls_input'},
 P+'memory_call_diamond': {P+'spec_diamond_success',P+'memory_call_not_exhausted',P+'memory_call_success'},
 P+'memory_call_diamond_iff': {P+'memory_call_diamond'},
 P+'memory_call_diamond_cursor': {P+'memory_call_diamond',P+'memory_call_capacity'},
 T+'populated_diamond': {P+'memory_call_diamond_cursor',T+'populated_input'},
 T+'diamond_complete_observations': {P+'memory_call_diamond',T+'ordered_words',T+'source_arrays'},
 T+'failure_diamond_rejected': {P+'memory_call_diamond',T+'failure_source'},
 T+'general_diamond_not_success': {P+'SpecificationControls.exhausted_diamond',P+'SpecificationControls.exhausted_has_no_success'},
 P+'memory_call_box': {P+'memory_call_result',P+'spec_box_post'},
 P+'memory_call_box_iff': {P+'memory_call_box'},
 P+'memory_call_box_diamond_dual': {P+'memory_call_result'},
 T+'populated_box': {P+'memory_call_box',T+'populated_input'},
 T+'box_false_post_exact_revert': {P+'memory_call_box',T+'failure_box_false_post'},
 T+'general_modal_duality_rejected': {'Solidity.Spec.sat'},
 P+'memory_call_result': {'Solidity.Evm.Memory.Calls.Program.sound'},
 T+'populated_input': {P+'memory_call_cursor', 'Solidity.Evm.Compiler.Compilation.memoryCalls_input'},
 T+'populated_spec': {P+'memory_call_spec'},
 T+'populated_alias_escape': {P+'memory_call_success', P+'memory_call_alias'},
 T+'remaining_actual': {'Solidity.Evm.Compiler.compile'},
 T+'wrong_alias': {T+'ownership_alias'},
 T+'wrong_cursor': {T+'ownership_cursor'},
 T+'expanded_frame_refused': {P+'memory_call_small_frame'},
 T+'failure_exact': {P+'memory_call_failure'},
 T+'wrong_revert_data': {T+'failure_observation'},
}
BOUNDARY = ('Scoped actual ordinary memory-call certificate/specification consumer and inhabited controls. '
            'No full-profile, recursive/external, pinned Osaka/resource, deployment/adversarial or final SolKey closure. '
            'No G01 events or byte-EVM observations are fabricated.')

# Exact DECLARED binders, not hypotheses obtained by unfolding a negative result.
PREMISE_POLICY = ROOT/'tests/roadmap-v16/diamond-premises.json'
COMMON = ['C','b','L','frame','Γ','Δ','F','P','compiled','path','σ','base','m']
DIAMOND_PARAMETERS = {
 'memory_call_box':COMMON+['φ','input','box'],
 'memory_call_box_iff':COMMON+['φ','input'],
 'memory_call_box_diamond_dual':COMMON+['φ','input'],
 'memory_call_not_exhausted':COMMON+['input'],
 'memory_call_capacity':COMMON+['input','cursor','allocator'],
 'memory_call_diamond':COMMON+['φ','input','diamond'],
 'memory_call_diamond_iff':COMMON+['φ','input'],
 'memory_call_diamond_cursor':COMMON+['φ','input','diamond','cursor','positive','allocator'],
}
DIAMOND_PROPOSITIONS = {
 'memory_call_box':['path','input','box'],
 'memory_call_box_iff':['path','input'],
 'memory_call_box_diamond_dual':['path','input'],
 'memory_call_not_exhausted':['path','input'],
 'memory_call_capacity':['path','input','allocator'],
 'memory_call_diamond':['path','input','diamond'],
 'memory_call_diamond_iff':['path','input'],
 'memory_call_diamond_cursor':['path','input','diamond','positive','allocator'],
}

def validate_diamond_premises(theorems):
    policy=json.loads(PREMISE_POLICY.read_text())
    core.require(policy['producerRevision']==PRODUCER and
      set(policy['theorems'])=={P+n for n in DIAMOND_PARAMETERS},'wrong reviewed premise policy')
    for short, names in DIAMOND_PARAMETERS.items():
        row=theorems[P+short];premises=row['premises']
        core.require([p['name'] for p in premises]==names,
          'extra/missing declared premise or oracle parameter: '+short)
        core.require([p['name'] for p in premises if p['isProp']]==DIAMOND_PROPOSITIONS[short],
          'assumed source success/exhaustion/target run/capacity: '+short)
        core.require(all(p.get('closedExpr') for p in premises), 'missing complete closed binder expression')
        core.require(premises==policy['theorems'][P+short],
          'strengthened/replaced complete reviewed binder type: '+short)
        by_name={p['name']:p for p in premises}
        for name,constant in [('path','Solidity.Evm.Compiler.Compilation.isMemoryCalls'),
                              ('input','Solidity.Evm.Compiler.Compilation.Input'),
                              ('diamond','Solidity.Spec.diamond'),
                              ('box','Solidity.Spec.box'),
                              ('allocator','Solidity.Evm.Memory.StructAllocatorRepr')]:
            if name in by_name:
                core.require(constant in by_name[name]['constants'],
                  'replaced actual certificate/diamond/allocator premise: '+short+':'+name)

def validate_scoped_dependencies(controls):
    # Keep ALL imported metadata, including unrelated existing conditional laws.
    # Reject a PublicCorrectness premise anywhere in the actual consumer/control
    # dependency closure, including a helper theorem or owned definition.
    nodes={r['name']:r for r in controls['theorems']+controls['definitions']}
    todo=[n for n,row in nodes.items() if row.get('ownerName',n).startswith(P+'memory_call_') or row.get('ownerName',n).startswith(T)]
    seen=set()
    while todo:
        name=todo.pop()
        if name in seen:continue
        seen.add(name);row=nodes[name]
        deps=set(row.get('dependencies',[])) | set(row.get('typeConstants',[]))
        core.require(not any('PublicCorrectness' in c for c in deps),
          'desired full correctness assumed in scoped dependency: '+name)
        for dep in deps:
            owned=dep.startswith(P) or (dep.startswith('_private.') and '.'+P in dep)
            core.require(not owned or dep in nodes,'missing reached owned declaration metadata: '+dep)
            if dep in nodes and dep not in seen:todo.append(dep)
    return sorted(seen)

def producer_pin():
    subprocess.run(['git','merge-base','--is-ancestor',PRODUCER,'HEAD'],cwd=ROOT,check=True)
    subprocess.run(['git','merge-base','--is-ancestor',PRODUCER,'origin/master'],cwd=ROOT,check=True)
    hashes = {}
    for name in FILES:
        published = subprocess.check_output(['git','show',PRODUCER+':'+name],cwd=ROOT)
        actual = (ROOT/name).read_bytes()
        core.require(actual == published, 'reserved producer differs from published revision: '+name)
        hashes[name] = core.digest(actual)
    return hashes

def observations(core_data, controls_log):
    inv = core_data['inventory']
    ledger = core.validate_inventory(inv)
    core.validate_report(core_data['report'], inv, ledger)
    controls = core.snapshot(controls_log)
    theorems = {t['name']: t for t in controls['theorems']}
    core.require(len(theorems)==len(controls['theorems']), 'duplicate actual theorem')
    for name, deps in REQUIRED.items():
        core.require(name in theorems, 'missing actual consumer/control: '+name)
        row = theorems[name]
        core.require(deps <= set(row['dependencies']) | set(row['typeConstants']),
                     'missing actual certificate/composition dependency: '+name)
    for row in controls['theorems']:
        core.require(set(row['axioms']) <= core.AXIOMS, 'unexpected actual axiom: '+row['name'])
    validate_diamond_premises(theorems)
    validate_scoped_dependencies(controls)
    families = {r['name']:r['constructors'] for r in inv['inductives']}
    core.require(CONSTRUCTOR in families.get('Solidity.Evm.Compiler.Compilation',[]),
                 'actual published constructor absent')
    obligation = next((r for r in core_data['report']['obligations']
                       if r['id']=='constructor:'+CONSTRUCTOR), None)
    core.require(obligation is not None and obligation['status']=='open',
                 'constructor coverage incorrectly closed')
    defs = {r['name']:r['dependencies'] for r in controls['definitions']}
    for name, dependency in [(T+'remainingCompiled','Solidity.Evm.Compiler.compile'),
                             (T+'prefixCertificate','Solidity.Evm.Memory.Calls.compile'),
                             (T+'prefixCompiled',CONSTRUCTOR)]:
        core.require(dependency in defs.get(name,[]), 'actual emitter origin missing: '+name)
    return inv, controls

def make_report(core_data, controls_log):
    inv, controls = observations(core_data, controls_log)
    return {'base':inv['base'], 'head':inv['head'], 'producerRevision':PRODUCER,
      'producerHashes':producer_pin(), 'constructor':CONSTRUCTOR, 'constructorStatus':'open',
      'laneComplete':False, 'stageStatus':{s:'open' for s in core.STAGES},
      'boundary':BOUNDARY, 'coreBinding':{k:inv[k] for k in core.current_binding()},
      'coreAccountingSha256':core.digest(json.dumps(core_data,sort_keys=True).encode()),
      'premisePolicySha256':core.digest(PREMISE_POLICY.read_bytes()),
      'auditScriptSha256':core.digest(pathlib.Path(__file__).read_bytes()),
      'controls':controls,
      'scopedProofClosure':validate_scoped_dependencies(controls),
      'importedConditionalOutsideScope':[t['name'] for t in controls['theorems']
        if any('PublicCorrectness' in c for c in t['typeConstants'])],
      'openPremises':['Actual compiler Input state/frame/reached AllocationInput',
        'Actual source-success and box premises remain on the older box-only consumer',
        'New diamond consumer requires actual diamond and Input; success/exhaustion/capacity are derived, not new premises',
        'New box consumer requires actual box and Input; success/post OR exact revert is retained, not total success',
        'SourceSpec/admission/lowering/full-profile coverage and progress',
        'Recursive/external execution and pinned Osaka/resources',
        'Deployment/rollback/adversarial transactions and final SolKey applications'],
      'eventBoundary':'Ordered word/source-array/stack observations only; word revert is separate from source bytes.'}

def validate_report(report, core_data, controls_log):
    expected = make_report(core_data, controls_log)
    core.require(report == expected, 'altered revision, constructor, theorem, dependency, premise, trust or closure claim')

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--core-accounting',type=pathlib.Path,required=True)
    ap.add_argument('--controls-log',type=pathlib.Path,required=True)
    ap.add_argument('--output',type=pathlib.Path,required=True)
    a=ap.parse_args();data=json.loads(a.core_accounting.read_text())
    report=make_report(data,a.controls_log);validate_report(report,data,a.controls_log)
    a.output.write_text(json.dumps(report,indent=2,sort_keys=True)+'\n')
    print(f"PASS: published {PRODUCER}; actual memoryCalls constructor OPEN; populated compiler/input/control dependencies bound; laneComplete=false")
if __name__=='__main__':
    try:main()
    except (core.Invalid,subprocess.CalledProcessError) as e:print('FAIL:',e,file=sys.stderr);sys.exit(1)
