#!/usr/bin/env bash
set -euo pipefail
# Usage: fetch.sh EXTERNAL-CACHE; clones stay outside the code branch.
python3 - "$1" "$(dirname "$0")/sources.json" <<'PYTHON'
import json,pathlib,subprocess,sys
root=pathlib.Path(sys.argv[1]).resolve(); root.mkdir(parents=True,exist_ok=True)
pins=json.load(open(pathlib.Path(sys.argv[2]).with_name('pins.json')))
rows=[]
for name,repo in json.load(open(sys.argv[2])).items():
    dest=root/name
    url='https://github.com/'+repo+'.git'
    r=subprocess.run(['git','clone','--depth','1',url,str(dest)],capture_output=True,text=True) if not dest.exists() else None
    if r is not None and r.returncode:
        rows.append(dict(project=name,url=url,status='unavailable',error=r.stderr[-1000:])); continue
    if (dest/'.git').exists():
        if subprocess.check_output(['git','-C',str(dest),'status','--porcelain'],text=True).strip(): raise SystemExit('refuse dirty source: '+name)
        actual=subprocess.check_output(['git','-C',str(dest),'remote','get-url','origin'],text=True).strip()
        if actual!=url: raise SystemExit('refuse unexpected origin: '+name)
        subprocess.run(['git','-C',str(dest),'fetch','--depth','1','origin',pins[name]],check=True)
        subprocess.run(['git','-C',str(dest),'checkout','--detach',pins[name]],check=True)
    commit=subprocess.check_output(['git','-C',str(dest),'rev-parse','HEAD'],text=True).strip()
    rows.append(dict(project=name,url=url,commit=commit,status='measured-source'))
(root/'revisions.json').write_text(json.dumps(rows,indent=2)+'\n')
print(json.dumps(rows,indent=2))
PYTHON
