import json,re,pathlib
root=pathlib.Path('tests/calldata-packets-1105/RawBool');results={}
for part,label in [('Execution','execution'),('Controls','controls')]:
 source=pathlib.Path(f'Solidity/Backend/CalldataPackets/RawBool/{part}.lean').read_text()
 assert source.count('#guard_msgs in') == len(re.findall(r'^#print axioms ',source,re.M))
 text=source;found={}
 for match in re.finditer(r"'([^']*CalldataPackets.RawBool[^']*)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",text,re.S):
  if ('.Controls.' in match.group(1)) != (part=='Controls'):continue
  axioms=sorted(x.strip() for x in (match.group(2) or '').split(',') if x.strip())
  assert set(axioms)<=set(['propext','Classical.choice','Quot.sound']),match.group(0)
  found[match.group(1)]=axioms
 source=pathlib.Path(f'Solidity/Backend/CalldataPackets/RawBool/{part}.lean').read_text()
 assert len(found)==len(re.findall(r'^(?:private )?theorem ',source,re.M))
 assert not re.search(r'\b(?:sorry|sorryAx|axiom|native_decide)\b',re.sub(r'/\*[\s\S]*?\*/','',source))
 results.update(found)
(root/'evidence/axioms.json').write_text(json.dumps(results,indent=2)+'\n');print('AXIOM_INVENTORY_PASS',len(results))
