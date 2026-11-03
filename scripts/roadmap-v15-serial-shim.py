#!/usr/bin/env python3
"""VM-local launch shim; pinned compiler/libraries and guards stay unchanged.
Lake5 has no native -j option. The lake frontend consumes -j1, sets its runtime
thread env, and directs every Lean child (including metadata queries) through
the Lean shim. No cache is copied and no existing conflicting path is replaced.
"""
from pathlib import Path
import json,os,shlex,sys

def install(real,shim,configs,overrides):
 real=Path(real).resolve();shim=Path(shim).absolute();assert not shim.is_symlink();shim.mkdir(exist_ok=True,parents=True)
 assert not (shim/'bin').is_symlink()
 (shim/'bin').mkdir(exist_ok=True)
 for source in real.iterdir():
  if source.name=='bin':continue
  target=shim/source.name
  if target.is_symlink():assert target.resolve()==source.resolve()
  else:assert not target.exists();target.symlink_to(source,target_is_directory=source.is_dir())
 for source in (real/'bin').iterdir():
  if source.name in ['lean','lake']:continue
  target=shim/'bin'/source.name
  if target.is_symlink():assert target.resolve()==source.resolve()
  else:assert not target.exists();target.symlink_to(source)
 parser='#!/bin/bash\nset -euo pipefail\nexport LEAN_NUM_THREADS=1\nargs=()\nwhile (($#)); do\n case "$1" in\n  -j1) shift ;;\n  -j) [[ ${2-} == 1 ]] || { echo \'serial shim: only -j1 allowed\' >&2; exit 2; }; shift 2 ;;\n  -j*) echo \'serial shim: only -j1 allowed\' >&2; exit 2 ;;\n  *) args+=("$1"); shift ;;\n esac\ndone\n'
 contents={'lean':parser+'exec '+shlex.quote(str(real/'bin/lean'))+' -j1 "${args[@]}"\n'}
 lake_parser='#!/bin/bash\nset -euo pipefail\nexport LEAN_NUM_THREADS=1\nwhile (($#)); do\n case "$1" in\n  -j1) shift ;;\n  -j) [[ ${2-} == 1 ]] || exit 2; shift 2 ;;\n  -j*) echo "serial shim: only -j1 allowed" >&2; exit 2 ;;\n  *) break ;;\n esac\ndone\nargs=("$@")\n'
 contents['lake']=lake_parser+'export LAKE_OVERRIDE_LEAN=true\n'+'export LEAN_SYSROOT='+shlex.quote(str(shim))+'\nexport LEAN='+shlex.quote(str(shim/'bin/lean'))+'\n'+'case "$PWD" in\n /workspace/solidity-lean-v15-p10-help) cfg='+shlex.quote(str(Path(configs)/'core.toml'))+'; extra=() ;;\n /workspace/solidity-lean-v15-p10-help/Bridge) cfg='+shlex.quote(str(Path(configs)/'bridge.toml'))+'; extra=('+shlex.quote('--packages='+str(overrides))+') ;;\n *) echo "serial shim: unsupported cwd" >&2; exit 2 ;;\nesac\nexec '+shlex.quote(str(real/'bin/lake'))+' --no-cache -f "$cfg" "${extra[@]}" "${args[@]}"\n'
 for name,text in contents.items():
  target=shim/'bin'/name
  if target.is_symlink():raise AssertionError('refusing frontend symlink: '+str(target))
  if target.exists():assert target.read_text()==text
  else:target.write_text(text);target.chmod(0o755)
 return contents

if __name__=='__main__':
 real='/workspace/.setup/tools/lean-4.24.0-linux'
 shim='/workspace/v15-serial-toolchain-20261102-v4'
 configs='/workspace/v15-evm-agreement-evidence/p10-help-20261102/configs'
 overrides='/workspace/v15-evm-agreement-evidence/p10-help-20261102/package-overrides-02.json'
 install(real,shim,configs,overrides)
 print(json.dumps({'shim':shim,'pinnedRoot':real,'copiedLibraries':False,'budgetChanges':False}))
