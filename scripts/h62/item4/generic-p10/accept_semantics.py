#!/usr/bin/env python3
"""Reproduce source acceptance plus actual Lean proofs/axiom guards, serially.

Transport exit0 is insufficient: every MCP response must report complete
semantic success. Timing and owner authorization are separate gates.
"""
import argparse
import json
from pathlib import Path
import re
import subprocess
import time
import census
from make_axiom_audit import messages
from make_candidate import SOURCE
from export_migration import OWNER_NAMESPACE


def require_success(report, diagnostic=False, build=False):
    if not isinstance(report,dict): raise ValueError('MCP result is not an object')
    if report.get('success') is not True or report.get('timed_out') or report.get('partial') or report.get('failed_dependencies'):
        raise ValueError('MCP did not report complete semantic success')
    if diagnostic and (report.get('partial') is not False or report.get('timed_out') is not False or not isinstance(report.get('items'),list) or not isinstance(report.get('failed_dependencies'),list)):
        raise ValueError('diagnostic completeness fields missing')
    if not diagnostic and not build and (report.get('timed_out') is not False or not isinstance(report.get('diagnostics'),list)):
        raise ValueError('run completeness field missing')
    if build and (not isinstance(report.get('errors'),list) or not isinstance(report.get('output'),str)):
        raise ValueError('unknown MCP success result shape')
    if report.get('errors'): raise ValueError('Lean build reported errors')
    items=report.get('items',[]) if diagnostic else report.get('diagnostics',[])
    if any(not isinstance(item,dict) or item.get('severity') not in {'info','warning','error'} or not isinstance(item.get('message'),str) for item in items):
        raise ValueError('malformed diagnostic payload')
    if any(item.get('severity')=='error' for item in items): raise ValueError('Lean error diagnostics present')


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repo',type=Path,default=Path(__file__).resolve().parents[4])
    parser.add_argument('--evidence',type=Path,required=True)
    args=parser.parse_args()
    repo,evidence=args.repo.resolve(),args.evidence.resolve()
    if not evidence.is_relative_to(repo.parent/'generic-p10-artifacts'): parser.error('evidence must stay off git in this lane artifacts')
    evidence.mkdir(parents=True,exist_ok=True)
    scripts=repo/'scripts/h62/item4/generic-p10'
    package=repo/'tests/h62/item4/generic-p10'
    rows=[]
    def run(name,command,json_result=False,diagnostic=False,build=False):
        start=time.monotonic()
        result=subprocess.run(command,cwd=repo,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
        path=evidence/f'accept-{name}.log'
        path.write_bytes(result.stdout)
        row=dict(name=name,command=command,exit_code=result.returncode,seconds=time.monotonic()-start,evidence=str(path),status='fail')
        rows.append(row)
        try:
            if result.returncode: raise SystemExit(f'FAIL {name}: see {path}')
            data=json.loads(result.stdout) if json_result else None
            if json_result: require_success(data,diagnostic,build)
            row['status']='pass'
        finally:
            (evidence/'semantic-acceptance-gates.json').write_text(json.dumps(rows,indent=2)+'\n')
        print(f'PASS {name}',flush=True)
        return data
    run('source',['python3','-B',str(scripts/'accept.py'),'--inventory',str(evidence/'census.json')])
    run('source-refusals',['python3','-B',str(package/'negative_acceptance.py'),'--inventory',str(evidence/'census.json')])
    for name in ['prepare_package','make_candidate','make_correspondence','export_migration']:
        run(name,['python3','-B',str(scripts/f'{name}.py'),'--check'])
    run('axiom-source',['python3','-B',str(scripts/'make_axiom_audit.py'),'--diagnostics',str(evidence/'resume-headline-axioms.json'),'--check'])
    forbidden=re.compile(r'\bsorry\b|\bnative_decide\b|\bunsafe\b|debug\.skipKernelTC|(?m:^\s*(?:private\s+)?axiom\b)|\bset_option\s+maxHeartbeats\b')
    for source in sorted(package.rglob('*.lean')):
        if '.lake' in source.relative_to(package).parts: continue
        if forbidden.search(census.mask(source.read_text())): raise SystemExit(f'FAIL trust/budget source scan: {source}')
    cli=str(repo/'scripts/coord-tools/lean-mcp')
    run('full-affected-build',[cli,'call','lean_build',json.dumps(dict(lean_project_path=str(package),clean=False,fetch_cache=False,output_lines=12))],True,build=True)
    for module in ['ByteFixture','ByteControls','Correspondence','AxiomAudit']:
        run('diag-'+module,[cli,'call','lean_diagnostic_messages',json.dumps(dict(file_path=str(package/'GenericP10'/f'{module}.lean'),interactive=False))],True,True)
    run('diag-root',[cli,'call','lean_diagnostic_messages',json.dumps(dict(file_path=str(package/'GenericP10.lean'),interactive=False))],True,True)
    code=(evidence/'owner-validation.lean').read_text()
    owner=run('owner-validation',[cli,'call','lean_run_code',json.dumps(dict(code=code))],True)
    expected=['OwnerValidation.'+OWNER_NAMESPACE+'.'+r['name'] for r in census.declarations((repo/SOURCE).read_text(),str(SOURCE)) if r['kind']=='theorem' and not r['private']]
    messages(dict(success=True,partial=False,timed_out=False,failed_dependencies=[],items=owner['diagnostics']),expected)
    run('layers',['node','scripts/check-layers.mjs'])
    run('patch-apply-check',['git','apply','--check',str(package/'owner-migration.patch')])
    run('scope-frozen',['git','diff','--exit-code',census.BASE,'--',str(SOURCE),'Bridge/lake-manifest.json','lean-toolchain','Bridge/lean-toolchain'])
    run('whitespace',['git','diff','--check'])
    run('staged-whitespace',['git','diff','--cached','--check'])
    print('LEAN_SEMANTIC_ACCEPTANCE_PASS: typed fixtures, all21public correspondences, retained refusals,48headline guards; timing/owner relay separate')


if __name__=='__main__':main()
