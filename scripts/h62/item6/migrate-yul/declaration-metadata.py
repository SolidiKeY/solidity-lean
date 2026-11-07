#!/usr/bin/env python3
"""Focused old persisted metadata observations; no public/semantic acceptance."""
import argparse,json,pathlib,sys
sys.dont_write_bytecode=True
import interfaces
name=interfaces.expr_dag.name

def nat(x):return type(x) is int and x>=0
def optional_name(x):
    if x is not None:name(x)
def inspect(raw,module):
    rows=[json.loads(line) for line in pathlib.Path(raw).read_text().splitlines()]
    if len(rows)<2 or rows[0].get('record')!='header' or rows[-1].get('record')!='complete':raise ValueError('incomplete metadata snapshot')
    h,f=rows[0],rows[-1];wanted=interfaces.module_name(module)
    if type(h.get('schema')) is not int or h['schema']!=1 or h.get('loaded_extensions') is not True or h.get('import_all') is not True or h.get('import_level')!='private':raise ValueError('unsupported schema/import/extension initialization')
    if any(row.get('module')!=wanted for row in rows):raise ValueError('module mismatch')
    groups={'declaration':[],'class':[],'instance':[],'default_instance':[]};seen=set()
    for row in rows[1:-1]:
        kind=row.get('record')
        if kind not in groups:raise ValueError('unknown metadata record')
        if kind=='declaration':
            name(row['name']);encoded=interfaces.canonical(row['name'])
            if encoded in seen:raise ValueError('duplicate declaration')
            seen.add(encoded)
            for field in ['private_name_marker','protected','class']:
                if type(row[field]) is not bool:raise ValueError('invalid declaration flag')
            if row['active_instance_priority'] is not None and not nat(row['active_instance_priority']):raise ValueError('invalid active priority')
        else:
            if type(row['index']) is not int or row['index']!=len(groups[kind]):raise ValueError('entry order/index mismatch')
            if kind=='class':
                name(row['name'])
                if not isinstance(row['out_parameters'],list) or any(not nat(x) for x in row['out_parameters']):raise ValueError('invalid class out parameters')
            if kind=='instance':
                e=row['entry'];optional_name(e['global_name']);optional_name(e['scope_namespace'])
                if e['attribute_kind'] not in ['global','local','scoped'] or not nat(e['priority']) or type(e['private_name_marker']) is not bool:raise ValueError('invalid instance metadata')
                if not isinstance(e['synthesis_order'],list) or any(not nat(x) for x in e['synthesis_order']):raise ValueError('invalid synthesis order')
                if not isinstance(e['value_repr'],str):raise ValueError('invalid instance expression repr')
            if kind=='default_instance':
                name(row['class_name']);name(row['instance_name'])
                if not nat(row['priority']):raise ValueError('invalid default priority')
        groups[kind].append(row)
    for key,label in [('declaration','declarations'),('class','classes'),('instance','instances'),('default_instance','defaults')]:
        if not nat(h['expected_'+label]) or not nat(f[label]) or h['expected_'+label]!=len(groups[key]) or f[label]!=len(groups[key]):raise ValueError('metadata coverage/count mismatch')
    if f.get('migration_acceptance') is not False:raise ValueError('unsupported acceptance claim')
    return dict(schema_version=1,module=module,header=h,footer=f,records=groups,migration_acceptance=False)

def seal(raw,probe_path,module):
    raw=pathlib.Path(raw).resolve();probe=interfaces.validate_probe(probe_path)
    if 'version 4.24.0,' not in probe['lean']:raise ValueError('old metadata observer only')
    if len(probe['modules'])!=1:raise ValueError('expected one supervised process')
    cmd=probe['modules'][0]['command'];pos=cmd.index('--run');root=pathlib.Path(probe['repository'])
    if len(cmd)!=pos+4 or cmd[pos+2]!=module or (root/cmd[pos+3]).resolve()!=raw:raise ValueError('metadata argument/output mismatch')
    helper=(root/cmd[pos+1]).resolve()
    if helper!=(root/'tests/h62/item6/migrate-yul/ExportDeclarationMetadata.lean').resolve() or str(helper) not in probe['probe_sources_before']:raise ValueError('unbound metadata observer')
    bound=probe['probe_outputs_after'].get(str(raw))
    if probe.get('probe_output_freshness_required') is not True or not bound or bound['sha256']!=interfaces.digest(raw) or bound['bytes']!=raw.stat().st_size:raise ValueError('unbound metadata bytes')
    result=inspect(raw,module)
    result.update(raw=str(raw),raw_sha256=interfaces.digest(raw),probe=str(pathlib.Path(probe_path).resolve()),probe_sha256=interfaces.digest(probe_path),lean=probe['lean'],lake=probe['lake'],validator_sha256=interfaces.digest(__file__),limitation='Focused old persisted metadata and initialized-state observations only. Not all attributes, public classification, semantic proof, new compatibility or performance acceptance. Unsafe IO initialization is external to the model and proofs.')
    return result

def check_fixture(report,compile_path):
    compiled=interfaces.validate_probe(compile_path);observed=json.loads(pathlib.Path(report['probe']).read_text())
    if (compiled['lean'],compiled['lake'])!=(report['lean'],report['lake']):raise ValueError('fixture toolchain mismatch')
    outputs=compiled['probe_outputs_after']
    if len(outputs)!=1:raise ValueError('fixture compile coverage')
    for path,bound in outputs.items():
        if interfaces.digest(path)!=bound['sha256'] or observed['probe_sources_before'].get(path)!=bound['sha256']:raise ValueError('fixture compile/inspection binding')
    ds={d['display_name']:d for d in report['records']['declaration']};es={e['entry']['display_name']:e['entry'] for e in report['records']['instance']};prefix='H62.MigrateYul.MetadataFixture.'
    expected={'global17':(17,'global',False),'global63':(63,'global',False),'private11':(11,'global',True),'Scoped.scoped41':(41,'scoped',False)}
    if set(es)!={prefix+k for k in expected}:raise ValueError('fixture serialized instance coverage')
    for suffix,(priority,kind,private) in expected.items():
        e=es[prefix+suffix]
        if (e['priority'],e['attribute_kind'],e['private_name_marker'])!=(priority,kind,private):raise ValueError('fixture priority/kind/private mismatch')
        expected_scope=interfaces.module_name(prefix+'Scoped') if kind=='scoped' else None
        if e['scope_namespace']!=expected_scope:raise ValueError('fixture scoped namespace mismatch')
        expected_active=priority if kind=='global' else None
        if ds[prefix+suffix]['active_instance_priority']!=expected_active:raise ValueError('fixture effective priority mismatch')
    if ds[prefix+'local97']['active_instance_priority'] is not None or prefix+'local97' in es:raise ValueError('local attribute persisted unexpectedly')
    if not ds[prefix+'Marker']['class'] or not ds[prefix+'protectedValue']['protected'] or not ds[prefix+'privateValue']['private_name_marker']:raise ValueError('fixture declaration flags mismatch')
    classes=report['records']['class'];defaults=report['records']['default_instance']
    if len(classes)!=1 or classes[0]['name']!=ds[prefix+'Marker']['name'] or classes[0]['out_parameters']!=[]:raise ValueError('fixture class entry mismatch')
    if len(defaults)!=1 or defaults[0]['priority']!=7 or defaults[0]['instance_name']!=ds[prefix+'global17']['name'] or defaults[0]['class_name']!=classes[0]['name']:raise ValueError('fixture default entry mismatch')
    return dict(status='pass',compile_probe_sha256=interfaces.digest(compile_path),cases=['global priorities17/63','private priority11 retained','scoped priority41 retained but inactive','local97 declaration retained without persistent attribute','default priority7','class/protected/private flags'],scope='finite fixture observations only; no theorem/API acceptance')

def check_original_coverage(report,summary_path):
    original=json.loads(pathlib.Path(summary_path).read_text())
    if original['module']!=report['module']:raise ValueError('kernel summary module mismatch')
    before={interfaces.canonical(d['name']):d for d in original['declarations']}
    after={interfaces.canonical(d['name']):d for d in report['records']['declaration']}
    if set(before)!=set(after) or len(before)!=len(original['declarations']):raise ValueError('original kernel declaration coverage mismatch')
    if any(before[n]['private']!=after[n]['private_name_marker'] for n in before):raise ValueError('original private marker mismatch')
    return dict(status='pass',declarations=len(before),kernel_summary=str(pathlib.Path(summary_path).resolve()),kernel_summary_sha256=interfaces.digest(summary_path),scope='original kernel name/private-marker coverage only; no public/new API acceptance')

if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    for key in ['raw','probe','output']:p.add_argument('--'+key,type=pathlib.Path,required=True)
    p.add_argument('--module',required=True);p.add_argument('--fixture-compile-probe',type=pathlib.Path);p.add_argument('--kernel-summary',type=pathlib.Path)
    a=p.parse_args()
    if a.output.exists():raise SystemExit('output must be fresh')
    result=seal(a.raw,a.probe,a.module)
    if a.fixture_compile_probe:result['fixture_controls']=check_fixture(result,a.fixture_compile_probe)
    if a.kernel_summary:result['original_coverage']=check_original_coverage(result,a.kernel_summary)
    a.output.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result['footer']))
