"""Prepare this VM's owned single-thread Lake configuration; no shared edits."""
import os,pathlib
p=pathlib.Path(__file__).resolve().parent;repo=p.parents[2];runtime=p/'runtime';runtime.mkdir(exist_ok=True)
config=(repo/'lakefile.toml').read_text().replace('weakLeanArgs = ["--tstack=131072"]','weakLeanArgs = ["--tstack=131072", "-j1"]')
config=config.replace('root = "SolkeyCheck"','root = "SolkeyCheck"\nweakLeanArgs = ["-j1"]')
config+='\n[[lean_lib]]\nname = "MemoryReferenceTests"\nsrcDir = "tests/directruntime-20261104/memory-references"\nroots = ["Admission", "KernelControls", "KernelMatrix", "V1StorageCases"]\nweakLeanArgs = ["--tstack=131072", "-j1"]\n'
(runtime/'lakefile.toml').write_text(config)
real=os.environ.get('MEMORY_LEAN_BIN','/workspace/.setup/tools/lean-4.24.0-linux/bin')+'/lake'
rel='tests/directruntime-20261104/memory-references/runtime/lakefile.toml'
(runtime/'lake').write_text(f'''#!/bin/bash
set -e
if [ "$1" = env ] && [ "${{2:-}}" = lean ]; then
  shift 2
  # Lake cache imports may supersede old materialized build files.
  # Reuse the setup emitted by the successful owned-module build.
  for arg in "$@"; do
    case "$arg" in
      tests/directruntime-20261104/memory-references/*.lean)
        base="${{arg##*/}}"
        setup=".lake/build/ir/${{base%.lean}}.setup.json"
        if [ -f "$setup" ]; then
          exec {real} -f {rel} env lean -j1 --setup "$setup" "$@"
        fi
        ;;
    esac
  done
  exec {real} -f {rel} env lean -j1 "$@"
fi
if [ "$1" = serve ]; then
  exec {real} -f {rel} "$@" -j1
fi
exec {real} -f {rel} "$@"
''')
(runtime/'lake').chmod(0o755)
print('Prepared owned configuration with explicit -j1; no shared root/configuration written')
