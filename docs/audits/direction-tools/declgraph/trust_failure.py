#!/usr/bin/env python3
"""Reproduce the pinned trust-audit diagnostic finding from a normal Lean log.
Capture command (from frozen source root, using the verified warm view):
 LEAN_PATH=VIEW lean --tstack=131072 -j1 -M10000 TrustAudit.lean > LOG 2>&1
Then run this script with --log LOG --exit-code EXIT [--check]. Source-only
citation checks below are not declaration dependency edges or root inference.
"""
import argparse,hashlib,json,pathlib,re,runpy,subprocess
HERE=pathlib.Path(__file__).resolve().parent
API=runpy.run_path(str(HERE/'audit.py'))
def measure(log,code):
 assert code!=0,'This finding requires the actual failing compiler exit status'
 source=API['sources']()['TrustAudit.lean'];diagnostics=[]
 for line in log.read_text().splitlines():
  m=re.match(r'^(.*?TrustAudit\.lean):(\d+):(\d+): error(?:\([^)]*\))?: (.*)$',line)
  if m:
   number=int(m[2]);diagnostics.append(dict(line=number,column=int(m[3]),message=m[4],source=source.splitlines()[number-1]))
 assert diagnostics,'No native trust-audit errors found'
 child='Solidity/Examples/Tactics/OpenLoops/RowsNine.lean';text=API['sources']()[child];needle='theorem binomialRowsNine :'
 definition_line=next(i+1 for i,line in enumerate(text.splitlines()) if line.startswith(needle))
 workflow='.github/workflows/lean.yml';ci=API['git']('show',API['BASE']+':'+workflow)
 workflow_line=next(i+1 for i,line in enumerate(ci.splitlines()) if 'run: lake env lean --tstack=131072 TrustAudit.lean' in line)
 return dict(base=API['BASE'],status='fail',source='TrustAudit.lean',source_sha256=hashlib.sha256(source.encode()).hexdigest(),exit_code=code,diagnostics=diagnostics,ci_citation=dict(path=workflow,line=workflow_line),source_observations=dict(parent_import_line=next(i+1 for i,line in enumerate(source.splitlines()) if line=='import Solidity.Examples.Tactics.OpenLoops'),definition_path=child,definition_line=definition_line,child_import_present='import Solidity.Examples.Tactics.OpenLoops.RowsNine' in source.splitlines()),verdict='The unmodified pinned CI trust audit fails. This run cannot certify baseline root coverage.',settling_measurement='In a separately authorized source revision, add the missing child import, check that module within its existing proof budget, and rerun the same trust-audit command. The pinned-base failure remains a finding.',boundaries=['Diagnostics are from the normal Lean file runner, not an inferred lexical use graph.', 'Source citation observations locate the parent import and child theorem definition; they do not add graph edges.', 'A failing baseline does not establish which declarations are unused or safe to delete.'])
def main():
 p=argparse.ArgumentParser();p.add_argument('--log',type=pathlib.Path,required=True);p.add_argument('--exit-code',type=int,required=True);p.add_argument('--check',action='store_true');a=p.parse_args();data=measure(a.log,a.exit_code);body=json.dumps(data,indent=2,sort_keys=True)+'\n';target=HERE/'trust-audit-summary.json'
 if a.check:assert target.read_text()==body,'STALE trust-audit finding'
 else:target.write_text(body)
 print('TRUST_AUDIT_FINDING_REPRODUCED',data['exit_code'],len(data['diagnostics']))
if __name__=='__main__':main()
