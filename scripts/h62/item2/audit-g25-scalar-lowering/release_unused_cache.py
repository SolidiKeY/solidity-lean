#!/usr/bin/env python3
"""Release OS pages for this task's unused historical files; never delete data.
Only POSIX_FADV_DONTNEED on read-only descriptors, confined to owned obsolete
artifact directories. No current4.24 toolchain/cache, VM limit, swap, systemd,
sysctl or source change. This does not execute/install/overlay Lean4.35.
"""
import json,os,time
from pathlib import Path

def main():
 root=Path('/workspace/h62-audit-g25-artifacts')
 targets=[root/x for x in ['toolchain','environment-v435','slice-v435','keysort-v435','draft-controls-v435','draft-slice-v435']]
 def stats():
  cg=Path('/sys/fs/cgroup');return {x:(cg/x).read_text().strip() for x in ['memory.current','memory.max','memory.swap.current']}
 before=stats();count=0;size=0
 for target in targets:
  for path in target.rglob('*'):
   if not path.is_file() or path.is_symlink():continue
   with path.open('rb') as stream:os.posix_fadvise(stream.fileno(),0,0,os.POSIX_FADV_DONTNEED)
   count+=1;size+=path.stat().st_size
 report={'action':'POSIX_FADV_DONTNEED on read-only owned unused historical files','files':count,'bytes_advised':size,
  'before':before,'after':stats(),'data_deleted':False,'limits_changed':False,'targets':list(map(str,targets))}
 (root/'evidence/unused-cache-release.json').write_text(json.dumps(report,indent=2)+'\n')
 print(json.dumps(report))

if __name__=='__main__': main()
