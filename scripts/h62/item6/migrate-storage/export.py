#!/usr/bin/env python3
"""Export committed migration checkpoint and deterministic off-git evidence."""
import fcntl,gzip,hashlib,io,json,pathlib,subprocess,sys,tarfile
from census import ROOT,BASE
E=pathlib.Path(sys.argv[1]);assert E.is_absolute() and E.is_dir()
lock=open("/tmp/solidity-lean-feature-groups-20261025/writer.lock","r+");fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
def git(*args):return subprocess.check_output(["git","-C",str(ROOT),*args])
def sha(p):
 h=hashlib.sha256()
 with p.open("rb") as f:
  for b in iter(lambda:f.read(1024*1024),b""):h.update(b)
 return h.hexdigest()
assert not git("status","--porcelain"),"export committed clean checkpoint only"
head=git("rev-parse","HEAD").decode().strip();branch=git("branch","--show-current").decode().strip()
assert branch=="codex/solidity-h62-6-20261106/migrate-storage"
subprocess.run(["git","-C",str(ROOT),"merge-base","--is-ancestor",BASE,head],check=True)
changes=git("diff","--name-only",BASE,head).decode().splitlines()
assert all(p.startswith(("scripts/h62/item6/migrate-storage/","tests/h62/item6/migrate-storage/")) or p=="docs/feature-work/h62-6-migrate-storage.md" for p in changes),"unexpected scope edit"
(E/"original.patch").write_bytes(git("diff","--binary",BASE,head))
subprocess.run(["git","-C",str(ROOT),"bundle","create",str(E/"migration.bundle"),BASE+".."+branch],check=True)
subprocess.run(["git","-C",str(ROOT),"bundle","verify",str(E/"migration.bundle")],check=True)
state={"base":BASE,"head":head,"branch":branch,"repository":str(ROOT),"changed_files":changes,"goal_status":"blocked","production_lean_files_edited":0}
retirement=ROOT/"tests/h62/item6/migrate-storage/h82-handoff/retirement-status.json"
if retirement.exists():
 r=json.loads(retirement.read_text())
 state.update(goal_status="pause_pending_coordinator",goal_pause_confirmed=False,execution_status=r["execution_status"],handoff_to=r["handoff_to"])
 snapshot=E/"h82-handoff-scope";snapshot.mkdir(exist_ok=True)
 for p in sorted(retirement.parent.iterdir()):
  if p.is_file():(snapshot/p.name).write_bytes(p.read_bytes())
(E/"committed-state.json").write_text(json.dumps(state,indent=2,sort_keys=True)+"\n")
(E/"handoff.md").write_text("Committed HEAD: `"+head+"`\n\n"+(ROOT/"docs/feature-work/h62-6-migrate-storage.md").read_text())
# Historical receipts retain their original absolute manifest; add a relocated
# checksum list so the preserved prior checkpoint remains directly verifiable.
if (E/"history").exists():
 for directory in sorted((E/"history").iterdir()):
  if directory.is_dir():
   prior=sorted(p for p in directory.iterdir() if p.is_file() and p.name!="local-checksums.sha256")
   (directory/"local-checksums.sha256").write_text("".join(sha(p)+"  "+str(p)+"\n" for p in prior))
# Raw Lean artifacts and full compiler trees remain on the VM; the release
# archive has its own manifest entry below. Archive only review evidence.
excluded={"checksums.sha256","evidence-files.sha256","evidence.tar.gz","CLOUDVM-RESULT.json"}
files=sorted(p for p in E.rglob("*") if p.is_file() and not p.is_symlink() and not {"artifacts","toolchains"}.intersection(p.relative_to(E).parts) and p.name not in excluded and p!=E/"SHA256SUMS")
(E/"evidence-files.sha256").write_text("".join(sha(p)+"  "+str(p.relative_to(E))+"\n" for p in files))
files.append(E/"evidence-files.sha256");files.sort()
with (E/"evidence.tar.gz").open("wb") as out:
 with gzip.GzipFile(fileobj=out,mode="wb",filename="",mtime=0) as gz:
  with tarfile.open(fileobj=gz,mode="w") as tf:
   for p in files:
    b=p.read_bytes();entry=tarfile.TarInfo(str(p.relative_to(E)));entry.size=len(b);entry.mode=0o644;entry.mtime=0;tf.addfile(entry,io.BytesIO(b))
selected=[E/n for n in ["original.patch","migration.bundle","handoff.md","evidence.tar.gz","evidence-files.sha256","frozen-interface-old.json","dependency-report.json","committed-state.json"]]
selected.append(E/"toolchains/lean-4.35.0-linux.tar.zst")
if retirement.exists():
 selected.extend(E/"h82-handoff-scope"/n for n in ["original-assignment.txt","original-goal-objective.txt","original-work-backfill-queue.txt","original-scope-manifest.json","open-queue.json","waits-v1.json","retirement-status.json","SHA256SUMS"])
(E/"checksums.sha256").write_text("".join(sha(p)+"  "+str(p)+"\n" for p in selected))
(E/"SHA256SUMS").write_bytes((E/"checksums.sha256").read_bytes())
print(json.dumps(state));print("ARTIFACT_CHECKSUMS",E/"checksums.sha256")
