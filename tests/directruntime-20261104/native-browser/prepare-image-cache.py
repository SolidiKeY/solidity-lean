"""Drop clean cache pages for this private SDK container and its public Lean libraries."""
import json,os,pathlib,time
scope=pathlib.Path("/sys/fs/cgroup");outer=pathlib.Path("/task-outer-cgroup")
assert int((scope/"memory.max").read_text())==12*1024**3
assert int((scope/"memory.swap.max").read_text())==0
assert os.getuid()==1000
out=pathlib.Path(__import__("sys").argv[1])
if out.exists():raise SystemExit("refusing cleanup receipt overwrite")
start=time.monotonic();before=int((outer/"memory.current").read_text());count=0;total=0;errors=0
for base in [pathlib.Path("/workspace/solidity-lean/.lake/native-browser-h35-cache-ship"),pathlib.Path("/workspace/solidity-lean/.lake/native-browser-cold-native"),pathlib.Path("/opt/codex/runtimes/codex-primary-runtime/dependencies/node"),pathlib.Path("/workspace/solidity-lean/.lake/native-browser-hardening"),pathlib.Path("/workspace/solidity-lean/.lake/direct-native"),pathlib.Path("/workspace/solidity-lean/.lake/native-browser-wasm/direct"),pathlib.Path("/workspace/solidity-lean/.lake/native-browser-sdk-usr"),pathlib.Path("/workspace/solidity-lean/.lake/native-browser-lean4"),pathlib.Path("/workspace/solidity-lean/.lake/native-browser-wasm/lean4"),pathlib.Path("/emsdk"),pathlib.Path("/usr"),pathlib.Path("/lib"),pathlib.Path("/workspace/.setup/tools/lean-4.24.0-linux/lib"),pathlib.Path("/work/toolchain-cache"),pathlib.Path("/work/gmp-build64"),pathlib.Path("/work/build64"),pathlib.Path("/work/direct-native-cache"),pathlib.Path("/workspace/solidity-lean/.lake/build"),pathlib.Path("/workspace/.setup/cache/lake/artifacts")]:
 for directory,dirs,files in os.walk(base,followlinks=False):
  for name in files:
   p=pathlib.Path(directory)/name
   if p.is_symlink():continue
   try:
    fd=os.open(p,os.O_RDONLY|os.O_NOFOLLOW)
    try:
     size=os.fstat(fd).st_size
     try:os.fsync(fd)
     except OSError:pass
     os.posix_fadvise(fd,0,0,os.POSIX_FADV_DONTNEED);count+=1;total+=size
    finally:os.close(fd)
   except OSError:errors+=1
after=int((outer/"memory.current").read_text())
result={"uid":os.getuid(),"beforeOuterCurrentBytes":before,"afterOuterCurrentBytes":after,"afterRawHeadroomBytes":int((outer/"memory.max").read_text())-after,"filesAdvised":count,"fileBytesAdvised":total,"errors":errors,"wallSeconds":time.monotonic()-start,"boundary":"Preparation only; no compiler/Lean child started. Read-only fds, fsync and POSIX_FADV_DONTNEED on private public SDK files and public Lean libraries. No file deletion/content changes or threshold changes."}
out.parent.mkdir(parents=True,exist_ok=True)
with out.open("x") as f:f.write(json.dumps(result,indent=2)+"\n")
print(json.dumps(result),flush=True)
