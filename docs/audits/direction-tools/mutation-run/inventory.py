#!/usr/bin/env python3
"""Reinventory existing audit inputs at the pinned base; do not rerun old audits."""
import hashlib,json,pathlib,subprocess,sys
BASE='d6fd95f0886775d7c286813fa9b993a40ba7a777'
HERE=pathlib.Path(__file__).resolve().parent

def git(*a):return subprocess.check_output(['git',*a])
def make():
    paths=git('ls-tree','-r','--name-only',BASE).decode().splitlines()
    scopes=['docs/audits/architecture-tools/','docs/audits/proof-coverage-tools/','docs/audits/build-speed','scripts/build-measure','scripts/differential/','scripts/bench/','scripts/h62/item3/g52-differential/']
    prior={}
    for scope in scopes:
        matches=[p for p in paths if p.startswith(scope)]
        prior[scope]={'tracked_files':len(matches),'files':matches,'boundary':'Presence only; historical outputs are not new execution results.'}
    old=json.loads(git('show',BASE+':docs/audits/direction-tools/mutation/mutants.json'))
    drift=[]
    for m in old:
        data=git('show',BASE+':'+m['path']).decode().splitlines()
        drift.append({'id':m['id'],'path':m['path'],'line':m['line'],'anchor_matches':m['old'] in data[m['line']-1]})
    cited=['docs/audits/direction.md','docs/audits/direction-tools/mutation/summary.json','docs/audits/architecture-tools/timing-sample.tsv','docs/feature-work/h62-3-g52-differential.md']
    return {'base':BASE,'prior_work':prior,'candidate_drift':drift,'sources':[{'path':p,'sha256':hashlib.sha256(git('show',BASE+':'+p)).hexdigest()} for p in cited],'decision':'Reuse the existing static candidates only after exact anchor checks. Historical conformance/timings do not execute these Lean mutations and are excluded from mutation score.'}
x=make();out=HERE/'inventory.json'
if '--check' in sys.argv:
    assert json.loads(out.read_text())==x;print('PASS pinned inventory and historical source hashes')
else:out.write_text(json.dumps(x,indent=2)+'\n')
