#!/usr/bin/env python3
"""Advise away clean pages of owned completed build/cache files; never edit data.
Run before a heavyweight check, with both writer and Lake-client locks free.
This changes neither memory limits nor the H1 guard. It does not drop global
caches, delete artifacts, alter mappings, or touch toolchains/source files.
"""
from pathlib import Path
import argparse,fcntl,json,os,stat,subprocess,time
ROOT=Path(__file__).resolve().parents[2]
def memory():
    cg=Path("/sys/fs/cgroup")
    stats={k:int(v) for k,v in (line.split() for line in (cg/"memory.stat").read_text().splitlines())}
    return {"memory_max":(cg/"memory.max").read_text().strip(),"memory_current":int((cg/"memory.current").read_text()),"anon":stats.get("anon"),"file":stats.get("file")}
def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument("--out",required=True);a=ap.parse_args()
    out=(ROOT/a.out).resolve();assert out.is_relative_to(ROOT/"tests/sol-c3-exactness/evidence")
    with open("/tmp/solidity-lean-feature-groups-20261025/writer.lock","a") as writer:
        fcntl.flock(writer,fcntl.LOCK_EX|fcntl.LOCK_NB)
        with (ROOT/"tests/sol-c3-exactness/.artifacts/lake-serial.lock").open("a") as clients:
            fcntl.flock(clients,fcntl.LOCK_EX|fcntl.LOCK_NB)
            before=memory();start=time.monotonic();seen=set();count=total=0
            roots=[ROOT/".lake/build",ROOT.parent/".setup/cache/lake/artifacts"]
            for root in roots:
                assert root.resolve()==root, "owned cache root must be canonical"
                if not root.is_dir():continue
                assert root.stat().st_uid==os.getuid()
                for p in root.rglob("*"):
                    if p.is_symlink() or not p.resolve().is_relative_to(root.resolve()):continue
                    st=p.stat()
                    if not stat.S_ISREG(st.st_mode) or st.st_uid!=os.getuid():continue
                    key=(st.st_dev,st.st_ino)
                    if key in seen:continue
                    fd=os.open(p,os.O_RDONLY|os.O_NOFOLLOW)
                    try:
                        st=os.fstat(fd)
                        if not stat.S_ISREG(st.st_mode) or st.st_uid!=os.getuid():continue
                        os.posix_fadvise(fd,0,0,os.POSIX_FADV_DONTNEED)
                        after=os.fstat(fd)
                        assert (after.st_size,after.st_mtime_ns)==(st.st_size,st.st_mtime_ns)
                        seen.add(key);count+=1;total+=st.st_size
                    finally:os.close(fd)
            after=memory();assert after["memory_max"]==before["memory_max"]
            record={"command":[".venv/bin/python","tests/sol-c3-exactness/release-owned-file-cache.py","--out",a.out],"head":subprocess.check_output(["git","rev-parse","HEAD"],cwd=ROOT,text=True).strip(),"roots":[str(r) for r in roots],"regular_files_advised":count,"file_bytes_advised_not_ram_bytes":total,"size_mtime_preserved":True,"before":before,"after":after,"elapsed_seconds":time.monotonic()-start,"method":"O_RDONLY + POSIX_FADV_DONTNEED only; all files/artifacts retained; no global cache drop or budget change"}
            out.write_text(json.dumps(record,indent=2)+"\n");print(json.dumps(record))
if __name__=="__main__":main()
