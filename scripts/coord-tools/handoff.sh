#!/usr/bin/env bash
set -euo pipefail
exec python3 - "$@" <<'PY'
import json,os,pathlib,subprocess,sys

def git(*a): return subprocess.check_output(["git",*a],text=True).strip()
def main():
    if len(sys.argv)>2: raise ValueError("usage: handoff.sh [NOTES-FILE]")
    env=os.environ; status=env.get("HANDOFF_STATUS","partial")
    if status not in ("done","partial","blocked"): raise ValueError("invalid status")
    root=git("rev-parse","--show-toplevel"); base=git("rev-parse","--verify",env.get("HANDOFF_BASE","origin/master")+"^{commit}"); head=git("rev-parse","HEAD"); merge=git("merge-base",base,head)
    gates=[]; stale=[]
    for d in filter(None,env.get("HANDOFF_GATES","").split(":")):
        h=pathlib.Path(d)/"HEAD"
        if h.is_file() and h.read_text().strip()!=head: stale.append(d)
        for row in (pathlib.Path(d)/"gates.tsv").read_text().splitlines():
            st,name,seconds,evidence,command=row.split("\t",4)
            if st not in ("PASS","FAIL"): raise ValueError("invalid gate status")
            gates.append(dict(gate=name,command=command,status=st.lower(),seconds=float(seconds),evidence=evidence))
    if status=="done" and stale: raise ValueError("done refused: gates ran on another commit: "+" ".join(stale))
    if status=="done" and (not gates or any(g["status"]!="pass" for g in gates) or git("status","--porcelain","--untracked-files=no")): raise ValueError("done requires passing gates and a clean tracked tree")
    changed=[]; deleted=[]
    for row in git("diff","--name-status","--no-renames",merge,head).splitlines():
        state,path=row.split("\t",1)
        if path.endswith(".lean"):
            (deleted if state=="D" else changed).append(path[:-5].replace("/","."))
    commits=[]
    for line in git("log","--reverse","--format=%H %s",base+"..HEAD").splitlines():
        sha,subject=line.split(" ",1); commits.append(dict(sha=sha,subject=subject))
    checkpoints=[]
    for item in filter(None,env.get("HANDOFF_CHECKPOINTS","").split(",")):
        name,st=item.split("=",1); checkpoints.append(dict(name=name,status=st))
    out=pathlib.Path(env.get("HANDOFF_OUT") or pathlib.Path(env.get("TMPDIR","/tmp"))/("coord-handoff-"+head[:12])).resolve(); out.mkdir(parents=True,exist_ok=True); md=out/"HANDOFF.md"
    notes=pathlib.Path(sys.argv[1]).read_bytes().decode() if len(sys.argv)==2 else ""
    result=dict(batch=env.get("HANDOFF_BATCH",""),slug=env.get("HANDOFF_SLUG",""),status=status,branch=git("branch","--show-current"),base=base,head=head,repository=root,commits=commits,modules_changed=sorted(changed),modules_deleted=sorted(deleted),checkpoints=checkpoints,gates=gates,notes=notes,questions=[],artifacts=dict(handoff=str(md)))
    body=json.dumps(result,indent=2,ensure_ascii=False)+"\n"
    md.write_text("# Handoff\n\n"+"\n".join(c["sha"]+" "+c["subject"] for c in commits)+"\n\n```json\n"+body+"```\n\n"+notes)
    (out/"CLOUDVM-RESULT.json").write_text(body)
    print("CLOUDVM-RESULT\n"+body+"END-CLOUDVM-RESULT")
try: main()
except Exception as e: print("handoff: "+str(e),file=sys.stderr); sys.exit(1)
PY
