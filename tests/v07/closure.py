"""Print local module import closure in dependency-first order; no builds."""
from pathlib import Path
import re,sys
seen=set();active=set()
def visit(m):
 p=Path(m.replace('.', '/')+'.lean')
 if not p.exists() or m in seen:return
 if m in active:raise SystemExit('cyclic import '+m)
 active.add(m)
 for dep in re.findall(r'^import (\S+)',p.read_text(),re.M):visit(dep)
 active.remove(m);seen.add(m);print(m)
for m in sys.argv[1:]:visit(m)
