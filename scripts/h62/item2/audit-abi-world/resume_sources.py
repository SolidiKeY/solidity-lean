"""Fail-closed canonical upstream input snapshot; no Lean execution/writes."""
import hashlib,json,subprocess
from pathlib import Path
import census
from prepare_resume_config import INTEGRATION
ROOT=Path(__file__).resolve().parents[4]
def snapshot():
 def git(*args):return subprocess.check_output(["git",*args],cwd=ROOT,text=True)
 expected=sorted(p for p in git("ls-tree","-r","--name-only",INTEGRATION).splitlines() if p.endswith(".lean"))
 actual=sorted(set(git("ls-files","--cached","--others","--","*.lean",":(exclude).lake/**",":(exclude).venv/**").splitlines()))
 assert expected==actual,"Unexpected/missing upstream Lean input"
 assert not git("diff","--name-only",INTEGRATION,"--","*.lean","lakefile.toml","lean-toolchain").strip(),"Integration inputs changed"
 for path in [census.MAP]+census.module_paths(census.frozen(census.MAP)):
  assert (ROOT/path).read_bytes()==subprocess.check_output(["git","show",census.BASE+":"+path],cwd=ROOT),path
 entries={p:hashlib.sha256((ROOT/p).read_bytes()).hexdigest() for p in expected}
 return dict(integration=INTEGRATION,count=len(entries),sha256=hashlib.sha256(json.dumps(entries,sort_keys=True,separators=(",",":")).encode()).hexdigest())
