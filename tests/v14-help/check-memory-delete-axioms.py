import re,sys,json
from pathlib import Path
text=Path(sys.argv[1]).read_text()
expected=re.findall(r"^#print axioms (\S+)$",Path(__file__).with_name('MemoryDeleteAxioms.lean').read_text(),re.M)
if len(expected)!=22 or len(set(expected))!=22:
    raise SystemExit('FAIL: expected exactly 22 distinct headline/control queries')
records=[(n,set(filter(None,re.split(r"[,\s]+",a)))) for n,a in
    re.findall(r"'([^']+)' depends on axioms: \[(.*?)\]",text,re.S)]
records += [(n,set()) for n in re.findall(r"'([^']+)' does not depend on any axioms",text)]
found={}
allowed={'propext','Quot.sound','Classical.choice'}
for name,axioms in records:
    if name in found: raise SystemExit('FAIL: duplicate theorem report '+name)
    if not axioms<=allowed: raise SystemExit('FAIL: nonstandard axioms '+str(axioms-allowed))
    found[name]=axioms
if set(found)!=set(expected): raise SystemExit('FAIL: missing or unexpected theorem reports')
if 'sorryAx' in text: raise SystemExit('FAIL: sorryAx in output')
print(json.dumps({'status':'pass','theorems':len(found),'axioms':{n:sorted(found[n]) for n in expected}},indent=2))
