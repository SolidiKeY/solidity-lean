#!/usr/bin/env bash
# Invoke only inside bounded.py; it owns the writer lock and resource guard.
set -euo pipefail
mode=${1:?mode}; out=${2:?fresh owned delivery directory}; shift 2
[[ "$out" != /* ]] || { echo "require relative owned output path" >&2; exit 2; }
export VO1_GATE_OUTPUT="$out"
export VO1_GATE_CONFIG="$PWD/$out/runtime.toml"
python3 - <<'CONFIG'
from pathlib import Path
import copy,json,os,re,tomllib
root=Path.cwd()
delivery=root/"tests/fullscope-20261104/vo1/delivery"
out=root/os.environ["VO1_GATE_OUTPUT"]
if out.is_symlink() or out.parent.resolve()!=delivery.resolve() or out.exists():
    raise SystemExit("require fresh direct owned delivery child")
source=Path("lakefile.toml").read_text()
original=tomllib.loads(source); expected=copy.deepcopy(original)
parts=re.split(r"(?=\[\[lean_(?:lib|exe)\]\])",source)
indices={"lean_lib":0,"lean_exe":0}
for i in range(1,len(parts)):
    kind="lean_lib" if parts[i].startswith("[[lean_lib]]") else "lean_exe"
    target=expected[kind][indices[kind]]; indices[kind]+=1
    args=list(target.get("weakLeanArgs",[]))
    for flag in ["--tstack=131072","-j1"]:
        if flag not in args: args.append(flag)
    target["weakLeanArgs"]=args
    parts[i]=re.sub(r"^weakLeanArgs\s*=.*\n","",parts[i],flags=re.M)
    parts[i]=parts[i].rstrip()+"\nweakLeanArgs = "+json.dumps(args)+"\n\n"
rendered="".join(parts)
if tomllib.loads(rendered)!=expected: raise SystemExit("unexpected config transformation")
out.mkdir()
Path(os.environ["VO1_GATE_CONFIG"]).write_text(rendered)
CONFIG
before=$(sha256sum "$VO1_GATE_CONFIG")
printf '%s\n' "$before"
verify_config() {
  status=$?
  after=$(sha256sum "$VO1_GATE_CONFIG") || exit 2
  printf '%s\n' "$after"
  [[ "$before" = "$after" ]] || { echo "config changed" >&2; exit 2; }
  exit "$status"
}
trap verify_config EXIT
lake() {
  if [[ "$1" = lean ]]; then
    /workspace/.setup/tools/lean-4.24.0-linux/bin/lake -f "$VO1_GATE_CONFIG" "$@" -j1
  else
    /workspace/.setup/tools/lean-4.24.0-linux/bin/lake -f "$VO1_GATE_CONFIG" "$@"
  fi
}
export -f lake
/workspace/.setup/tools/lean-4.24.0-linux/bin/lean --version
/workspace/.setup/tools/lean-4.24.0-linux/bin/lake --version
export GATE_LOGS="$PWD/$out/gates"
bash scripts/coord-tools/gate.sh "$mode" "$@"
