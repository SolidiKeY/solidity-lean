#!/usr/bin/env python3
"""Private symlink sysroot, unchanged official binaries, serial Lean wrapper.
Use LEAN_SYSROOT=<output> LAKE_OVERRIDE_LEAN=true when invoking official Lake.
"""
import argparse,pathlib,shlex
p=argparse.ArgumentParser(); p.add_argument("official",type=pathlib.Path); p.add_argument("output",type=pathlib.Path); a=p.parse_args()
a.official=a.official.resolve(); a.output=a.output.resolve(); a.output.mkdir(parents=True,exist_ok=False)
for x in a.official.iterdir():
    if x.name!="bin": (a.output/x.name).symlink_to(x,target_is_directory=x.is_dir())
(a.output/"bin").mkdir()
for x in (a.official/"bin").iterdir():
    if x.name!="lean": (a.output/"bin"/x.name).symlink_to(x)
wrapper=a.output/"bin/lean"
wrapper.write_text("#!/bin/sh\nfor arg in \"$@\"; do\n  case \"$arg\" in --server|--githash|--version|--print-prefix|--print-libdir|--help) exec "+shlex.quote(str(a.official/"bin/lean"))+" -j1 \"$@\";; esac\ndone\nexec flock --close /tmp/h62-migrate-corpus-heavy.lock "+shlex.quote(str(a.official/"bin/lean"))+" -j1 \"$@\"\n")
wrapper.chmod(0o755)
print(a.output)

wrapper.write_text(wrapper.read_text().replace("#!/bin/sh\n", "#!/bin/sh\nif [ -n \"${H62_LAKE_WRAPPER:-}\" ]; then export LAKE=\"$H62_LAKE_WRAPPER\"; fi\n", 1))
