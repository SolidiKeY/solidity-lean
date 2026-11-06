"""Regression: a moving publication cannot conceal a committed ownership violation.
All synthetic repository writes stay below this lane's ignored artifacts.
"""
import json, pathlib, shutil, subprocess, tempfile
root=pathlib.Path(__file__).resolve().parents[3]
owned=pathlib.Path('tests/directruntime-20261104/shared-translator')
baseline=json.loads((root/owned/'ownership-baseline.json').read_text())['commit']
out=root/owned/'artifacts/h68'; out.mkdir(parents=True,exist_ok=True)
def run(args,cwd=root,check=True):
    return subprocess.run(args,cwd=cwd,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,check=check)
with tempfile.TemporaryDirectory(prefix='baseline-',dir=out) as tmp:
    repo=pathlib.Path(tmp)/'repo'
    run(['git','clone','--shared','--no-checkout',str(root),str(repo)])
    run(['git','sparse-checkout','set','--no-cone','/Solidity/Tools/DirectRuntime.lean','/Solidity/Frontend/ExecutableAst/Shared/',f'/{owned}/','/docs/README.md'],repo)
    run(['git','checkout','--detach',baseline],repo)
    for name in ['audit.py','ownership-baseline.json']:
        shutil.copyfile(root/owned/name,repo/owned/name)
    def audit():return run(['python3',str(owned/'audit.py')],repo,False)
    healthy=audit(); assert healthy.returncode==0,healthy.stdout
    target=repo/'docs/README.md'; target.write_text(target.read_text()+'\nSynthetic ownership regression probe.\n')
    run(['git','add','docs/README.md'],repo)
    run(['git','-c','user.name=Regression','-c','user.email=fixture@example.invalid','commit','-m','synthetic out-of-scope probe'],repo)
    head=run(['git','rev-parse','HEAD'],repo).stdout.strip()
    run(['git','update-ref','refs/remotes/origin/master',head],repo)
    refused=audit(); assert refused.returncode!=0 and 'unowned path modified' in refused.stdout,refused.stdout
    # The original moving audit incorrectly admits the same committed change.
    old=run(['git','show','4095d848297d87e374b4f069692511cfe4a36cf7:'+str(owned/'audit.py')],root).stdout
    (repo/owned/'audit-moving-control.py').write_text(old)
    moving=run(['python3',str(owned/'audit-moving-control.py')],repo,False)
    assert moving.returncode==0,moving.stdout
    receipt={'healthyExit':healthy.returncode,'pinnedViolationExit':refused.returncode,'movingAuditViolationExit':moving.returncode,'pin':baseline,'syntheticHead':head,'healthy':healthy.stdout,'pinnedRefusal':refused.stdout,'movingControl':moving.stdout,'boundary':'Private disposable Git fixture only; no unowned main-checkout mutation.'}
    (out/'audit-baseline-controls.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps({k:v for k,v in receipt.items() if k.endswith('Exit') or k=='pin'}))
