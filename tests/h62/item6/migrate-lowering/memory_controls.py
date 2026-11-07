#!/usr/bin/env python3
"""Cache-heavy and real low-headroom cases under unchanged cap/reserve."""
import sys
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parents[4]/"scripts/h62/item6/migrate-lowering"))
from memory_headroom import cgroup_available, stop_reason
G=1024**3
# A 12GiB charge including 6GiB clean unmapped cache leaves 10GiB available.
a,r=cgroup_available(16*G,12*G,{"file":6*G,"active_file":3*G,"inactive_file":3*G})
assert a==10*G and r==6*G
a,r=cgroup_available(16*G,17*G,{"file":4*G,"active_file":4*G}); assert a==3*G
a,r=cgroup_available(16*G,2*G,{"file":6*G,"active_file":6*G}); assert r==2*G and a==16*G
for protected in ("file_mapped","file_dirty","file_writeback","shmem","unevictable"):
    a,r=cgroup_available(16*G,13*G,{"file":6*G,"active_file":6*G,protected:6*G})
    assert a==3*G and r==0
    assert stop_reason({"host_available_bytes":16*G,"cgroup_available_bytes":a,"swap_bytes":0},4*G)
a,r=cgroup_available(16*G,13*G,{"anon":13*G}); assert a==3*G and r==0
assert stop_reason({"host_available_bytes":3*G,"cgroup_available_bytes":10*G,"swap_bytes":0},4*G)
assert stop_reason({"host_available_bytes":10*G,"cgroup_available_bytes":10*G,"swap_bytes":1},4*G)
assert stop_reason({"host_available_bytes":4*G,"cgroup_available_bytes":4*G,"swap_bytes":0},4*G) is None
print("PASS: clean unmapped cache credited; mapped/dirty/shared/unevictable/anonymous memory protected; host/cgroup 4GiB reserve and no swap retained")
