"""Exercise the review finding: host availability can exceed VM headroom."""
import pathlib,tempfile,subprocess,sys
from resource_guard import available_bytes,heavy_lock
with tempfile.TemporaryDirectory(prefix='h28-type-guard-') as tmp:
    p=pathlib.Path(tmp)
    (p/'meminfo').write_text('MemAvailable: 8388608 kB\n')
    (p/'memory.max').write_text(str(6*1024**3))
    (p/'memory.current').write_text(str(4*1024**3))
    assert available_bytes(p/'meminfo',p)==2*1024**3
    (p/'memory.max').write_text('max')
    assert available_bytes(p/'meminfo',p)==8*1024**3
lock=heavy_lock()
proc=subprocess.run([sys.executable,'-c','from resource_guard import heavy_lock; heavy_lock()'],cwd=pathlib.Path(__file__).parent,capture_output=True,text=True)
assert proc.returncode!=0 and 'Another task heavy runtime is active' in proc.stderr
print('PASS: finite cgroup restricts host headroom; unlimited cgroup uses host; heavy-runtime overlap refused')
