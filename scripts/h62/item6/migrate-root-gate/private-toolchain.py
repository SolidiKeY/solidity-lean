#!/usr/bin/env python3
"""Private toolchain facade: unchanged release binaries, serial -j1 elaboration.

Not a new release pin. The official archive SHA remains the fleet identity.
Use LEAN_SYSROOT=facade LAKE_OVERRIDE_LEAN=true and its bin directory on PATH.
Keep facade, process lock, artifact cache and logs outside git.
"""
import argparse
from pathlib import Path
import shlex

p = argparse.ArgumentParser()
p.add_argument('release', type=Path)
p.add_argument('facade', type=Path)
a = p.parse_args()
release = a.release.resolve(strict=True)
facade = a.facade.absolute()
if facade.exists():
    p.error('facade must not exist')
(facade/'bin').mkdir(parents=True)
for entry in release.iterdir():
    if entry.name != 'bin':
        (facade/entry.name).symlink_to(entry, target_is_directory=entry.is_dir())
for entry in (release/'bin').iterdir():
    if entry.name != 'lean':
        (facade/'bin'/entry.name).symlink_to(entry)
wrapper = facade/'bin/lean'
wrapper.write_text('#!/usr/bin/env bash\nset -euo pipefail\n'
                   'exec 8>'+shlex.quote(str(facade/'lean-process.lock'))+'\n'
                   'flock 8\nexport LEAN_NUM_THREADS=1\nexec '+
                   shlex.quote(str(release/'bin/lean'))+' -j1 "$@"\n')
wrapper.chmod(0o755)
print(facade)
