#!/usr/bin/env python3
"""Diagnose existing value-entry prerequisites without importing Lean or building.

This is cache/interface evidence, never a typed execution or semantic verdict.
"""
import argparse, copy, hashlib, importlib.util, json, subprocess, time, resource, sys
sys.dont_write_bytecode=True
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
SPEC=importlib.util.spec_from_file_location('cache_audit',ROOT/'scripts/solidity-baseline-cache-audit.py')
CACHE=importlib.util.module_from_spec(SPEC);SPEC.loader.exec_module(CACHE)
START='38871aee752a24e37c2ac6196e9539ea3fd2c03a'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def assess(row):
    missing=[k for k in ['source','trace','olean','setup'] if not row[k]['exists']]
    refs=row.get('importArtifactChecks',[])
    different=[r for r in refs if not r['byteIdenticalToLocal']]
    absent=sorted(set(row['directImports'])-{r['module'] for r in refs})
    return dict(requiredFilesMissing=missing,currentDirectImportsAbsent=absent,
                differingSavedImportReferences=different,
                descriptorIdentitySatisfied=not(missing or different or absent))
def collect():
    CACHE.TARGETS=['Solidity.Tools.Upstream','Solidity.Semantics.Lifetime','Solidity.Semantics.ContractWorld']
    a=CACHE.audit(ROOT)
    before=json.loads((ROOT/'tests/upstream/baseline-20261028/native-cache/cache-after.json').read_text())
    stable=[]
    for x in before['checks']:
        r=a['modules'][x['module']][x['kind']]
        stable.append(dict(module=x['module'],kind=x['kind'],previousSha256=x['sha256'],
                           currentSha256=r.get('sha256'),unchanged=r.get('sha256')==x['sha256']))
    targets={n:dict(sourceClosure=a['targetClosures'][n],module=a['modules'][n],assessment=assess(a['modules'][n])) for n in CACHE.TARGETS[1:]}
    for n,t in targets.items():
        saved={r['module'] for r in t['module'].get('importArtifactChecks',[])}
        current=set(t['sourceClosure'])-{n}
        t['assessment']['currentTransitiveImportsAbsent']=sorted(current-saved)
        t['assessment']['savedImportsOutsideCurrentSourceClosure']=sorted(saved-current)
        if current!=saved:t['assessment']['descriptorIdentitySatisfied']=False
    # Do not assert any new positive cache validity from descriptor agreement:
    # mismatch alone suffices to refuse a new no-build import.
    synthetic={k:{'exists':True} for k in ['source','trace','olean','setup']}
    synthetic.update(directImports=['Example.Direct'],importArtifactChecks=[dict(module='Example.Direct',byteIdenticalToLocal=True)])
    controls=[dict(control='consistent-synthetic-descriptor',accepted=assess(synthetic)['descriptorIdentitySatisfied'],notRuntimeEvidence=True)]
    for label,mutate in [('missing-setup',lambda r:r['setup'].update(exists=False)),
                          ('missing-current-direct-import',lambda r:r['importArtifactChecks'].clear()),
                          ('changed-import',lambda r:r['importArtifactChecks'][0].update(byteIdenticalToLocal=False))]:
        r=copy.deepcopy(synthetic);mutate(r);controls.append(dict(control=label,rejected=not assess(r)['descriptorIdentitySatisfied']))
    sourcepaths=['Solidity/Tools/Upstream.lean','Solidity/Tools/Run.lean','Solidity/Semantics/Lifetime.lean','Solidity/Semantics/ContractWorld.lean','Solidity/Semantics/Deploy.lean','Solidity/Semantics/State.lean','Solidity/Frontend/Import.lean','Solidity/Frontend/SolcJson/Contract.lean']
    sources={p:dict(sha256=sha(ROOT/p),text=(ROOT/p).read_text()) for p in sourcepaths}
    fixture=json.loads((ROOT/'docs/solidity-features.json').read_text())
    historical={}
    for base in ['gaps','attribution','probes','native-cache']:
        for p in (ROOT/'tests/upstream/baseline-20261028'/base).rglob('*'):
            if p.is_file():
                rel=str(p.relative_to(ROOT))
                if subprocess.run(['git','cat-file','-e',START+':'+rel],cwd=ROOT,stdout=subprocess.DEVNULL,stderr=subprocess.DEVNULL).returncode:continue
                old=subprocess.check_output(['git','show',START+':'+rel],cwd=ROOT)
                historical[rel]=dict(sha256=sha(p),unchanged=hashlib.sha256(old).hexdigest()==sha(p))
    return dict(startingCommit=START,branch=subprocess.check_output(['git','branch','--show-current'],cwd=ROOT,text=True).strip(),
        sameSavedVm='ccarenv_b64_Y2NhcmVudl9mNjQxMmFkYWVhYTQ4MTkxYTFiMjVjYWQzNDkzNzJjOQ',
        targets=targets,nativeCacheSnapshots=stable,all304NativeArtifactsUnchanged=len(stable)==304 and all(x['unchanged'] for x in stable),
        rootLakefile=a['rootLakefile'],sources=sources,features=[f for f in fixture['features'] if f['id'] in ['stateMutability','msgValue']],
        integrityControls=controls,historicalTrackedFiles=historical,
        nativeValidationComplete=False,nonzeroPaymentRuntimeChecks='unrun: no identity-satisfied existing value-aware API in current cache',
        prerequisite='Current-identity Solidity.Semantics.Lifetime root artifact against its 27 current dependencies already present in the verified Upstream closure, then an ABI-resolved diagnostic binding imported payable metadata to Lifetime.System.run and explicit TTx; no proof-search/Testing closure required.',
        noBuildNoLeanInvocation=True,notClaimed=['semantic mismatch','typed nonzero-payment rejection','payable success at nonzero payment','rollback under nonzero payment','compiled EVM dispatcher equivalence'])
def main():
    p=argparse.ArgumentParser();p.add_argument('--out',type=Path,required=True);args=p.parse_args()
    if args.out.exists():p.error('fresh output required; refusing to overwrite evidence')
    begin=time.monotonic();x=collect();r=resource.getrusage(resource.RUSAGE_SELF)
    x['measurement']=dict(elapsedSeconds=time.monotonic()-begin,maxSelfRssKiB=r.ru_maxrss,memoryMetric='process self high-water RSS; not aggregate cgroup peak')
    ok=x['all304NativeArtifactsUnchanged'] and all(v['unchanged'] for v in x['historicalTrackedFiles'].values()) and all(c.get('rejected',c.get('accepted',False)) for c in x['integrityControls'])
    assert ok,'integrity controls or preserved evidence drifted'
    args.out.parent.mkdir(parents=True,exist_ok=True)
    with args.out.open('x') as report:report.write(json.dumps(x,indent=2)+'\n')
    print(json.dumps(dict(integrityPass=ok,nativeValidationComplete=False,targets={n:dict(closure=len(t['sourceClosure']),missing=t['assessment']['requiredFilesMissing'],differingRefs=len(t['assessment']['differingSavedImportReferences'])) for n,t in x['targets'].items()},measurement=x['measurement'])))
if __name__=='__main__':main()
