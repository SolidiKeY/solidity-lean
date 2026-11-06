#!/usr/bin/env python3
"""Audit all six importer and 22 kernel-control theorem axiom sets."""
from pathlib import Path
import json,re
base=Path(__file__).parent;ev=base/'evidence';records={}
for label in ['import','controls','fixtures']:
 logs=[]
 for f in ev.glob(label+'-*.json'):
  x=json.loads(f.read_text())
  if x.get('exit')==0:logs.append((int(f.stem.rsplit('-',1)[1]),ev/(f.stem+'.log')))
 assert logs,label
 for m in re.finditer(r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",max(logs)[1].read_text()):
  ax=[x.strip() for x in (m[2] or '').split(',') if x.strip()]
  assert set(ax)<={'propext','Classical.choice','Quot.sound'},(m[1],ax)
  records[m[1]]=ax
assert len(records)==28,len(records)
for name in ['IrImport','IrImportControls']:
 s=Path('Solidity/Frontend/SolcJson/'+name+'.lean').read_text()
 assert not re.search(r'\b(?:sorry|sorryAx|axiom|native_decide)\b',s),name
(ev/'axioms.json').write_text(json.dumps(records,indent=2)+'\n')
print('AXIOM_INVENTORY_PASS',len(records))
