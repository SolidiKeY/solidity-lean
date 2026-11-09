#!/usr/bin/env python3
"""Portable native diagnostic findings from replay-verified external profiles.
python3 .../native_findings.py --local PROFILE --reference PROFILE \
 --sample LOCAL-SAMPLE --reference-results REFERENCE-RESULTS --out NEWDIR
Function-family counts are conservative named-symbol lower bounds from top40;
not allocation counts, call-chain attribution, exact times or global direction.
"""
import argparse,collections,json,pathlib
HERE=pathlib.Path(__file__).resolve().parent

def read(path):return json.loads(path.read_text())
def family(name):
    if name.startswith(('mi_','lean_dec_ref','lean_inc_ref','lean_free','lean_alloc')):return 'allocation_reference_counting'
    if '__hash_table' in name or 'PersistentHashMap' in name:return 'container_operations'
    if 'replace_rec_fn' in name or 'replace_fn' in name:return 'expression_replacement'
    if 'sharecommon' in name:return 'expression_sharing_family'
    if 'expr_eq_fn' in name or 'expr_hash' in name:return 'expression_equality_hash'
    return None

def report(data,lines):
    assert data['check']['exit_code']==0 and data['profile']['samples']>0 and data['profile']['lost_samples']==0
    total=data['profile']['samples'];groups=collections.Counter()
    for row in data['profile']['top_symbols']:
        kind=family(row['symbol'])
        if kind is not None:groups[kind]+=row['samples']
    return {'head':data['head'],'module':data['check']['command'][-1],'lines':lines,'versions':data['versions'],'instrumented_wall_seconds':data['check']['wall_seconds'],'child_rusage_delta':data['child_rusage_delta'],'rusage_boundary':data['rusage_boundary'],'samples':total,'unknown_samples':data['profile']['unknown_symbol_samples'],'lost_samples':data['profile']['lost_samples'],'identified_family_samples_lower_bound':dict(sorted(groups.items())),'identified_family_fraction_lower_bound':{kind:n/total for kind,n in sorted(groups.items())},'combined_identified_fraction_lower_bound':sum(groups.values())/total,'top_symbols':[{'binary':pathlib.Path(r['binary']).name,'symbol':r['symbol'],'samples':r['samples'],'fraction_of_samples':r['fraction_of_samples']} for r in data['profile']['top_symbols'][:10]]}

def main():
    ap=argparse.ArgumentParser()
    for name in ('local','reference','sample','reference-results','out'):ap.add_argument('--'+name,type=pathlib.Path,required=True)
    args=ap.parse_args();local=read(args.local);ref=read(args.reference);sample=read(args.sample);baseline=read(args.reference_results)
    assert local['head']==sample['base'] and local['versions']==sample['versions']
    localrow=next(r for r in sample['samples'] if r['path']==local['check']['command'][-1]);assert localrow['plain']['command']==local['check']['command'] and localrow['plain']['cwd']==local['check']['cwd']
    assert ref['head']==baseline['pin'] and ref['versions']=={'lean':baseline['lean_version'],'lake':baseline['lake_version']}
    refrow=next(r for r in baseline['modules'] if r['path']==ref['check']['command'][-1]);assert refrow['check']['command']==ref['check']['command'] and refrow['check']['cwd']==ref['check']['cwd']
    findings={'base':sample['base'],'local':report(local,localrow['lines']),'reference':report(ref,refrow['lines']),'boundaries':['Diagnostic instrumented runs are not substituted for matched plain area timings.','Named top40 symbol families are exclusive lower bounds; unclassified/unknown/tail samples are not inferred.','Native symbols do not establish allocation counts, a unique caller, proof redundancy or an area-wide verdict.','Child CPU counters include the awaited Lake invocation and descendants; user-IP sampling includes Lean kernel but excludes OS kernel.','Prebuilt dependency oleans do not imply warm OS page cache; retain each run major-fault and input-block counters.','Reference compiler is Lean4.22 versus local4.24; no compiler-version causal claim.']}
    out=args.out.resolve()
    for checkout in (HERE.parents[3],pathlib.Path(local['check']['cwd']).resolve(),pathlib.Path(ref['check']['cwd']).resolve()):
        if out==checkout or checkout in out.parents:ap.error('--out must be outside checkouts')
    try:out.mkdir(parents=True,exist_ok=False)
    except FileExistsError:ap.error('--out must be a new directory')
    (out/'native-findings.json').write_text(json.dumps(findings,indent=2)+'\n');print('native diagnostic findings derived')
if __name__=='__main__':main()
