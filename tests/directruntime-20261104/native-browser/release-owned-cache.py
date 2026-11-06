"""Release clean cache pages only for this task's generated disk artifacts."""
import json, os, pathlib
root=pathlib.Path.cwd()
scope=pathlib.Path("/sys/fs/cgroup")
before=int((scope/"memory.current").read_text())
count=0;total=0;errors=[]
for base in [root/".lake/build",root/".lake/native-browser-lean4",root/".lake/direct-native",root/".lake/native-browser-wasm"]:
 for directory, dirs, files in os.walk(base, followlinks=False):
  for name in files:
   path=pathlib.Path(directory)/name
   if path.is_symlink():continue
   try:
    fd=os.open(path,os.O_RDONLY|os.O_NOFOLLOW)
    try:
     size=os.fstat(fd).st_size
     os.posix_fadvise(fd,0,0,os.POSIX_FADV_DONTNEED)
     count+=1;total+=size
    finally:os.close(fd)
   except OSError as error:errors.append({"path":str(path),"error":str(error)})
after=int((scope/"memory.current").read_text())
result={"beforeOuterCurrentBytes":before,"afterOuterCurrentBytes":after,"filesAdvised":count,"fileBytesAdvised":total,"errors":errors,"boundary":"POSIX_FADV_DONTNEED on owned generated artifacts only; no deletion, content change, global cache drop, guard change or budget change."}
out=root/"docs/benchmarks/directruntime-2026-11-04/setup/cache-release.json"
if out.exists():raise SystemExit("refusing receipt overwrite")
out.parent.mkdir(parents=True,exist_ok=True);out.write_text(json.dumps(result,indent=2)+"\n")
print(json.dumps(result))
