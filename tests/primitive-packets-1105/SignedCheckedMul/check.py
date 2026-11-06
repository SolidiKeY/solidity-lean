"""Check all thirty-two complete native/Source observation rows independently."""
import json
import re
import sys
text = open(sys.argv[1]).read()
rows = re.findall(r'pipeline=.*?(?=\npipeline=|\Z)', text, re.S)
H, W = 2**255, 2**256
pairs = [(-7,9),(9,-7),(-7,-9),(-H,-1),(-1,-H),(H-1,2),(-H,-H),(-H,2),(2,-H),(H-1,-9),
         (-H,1),(1,-H),(H-1,-1),(-1,H-1),(-H,0),(0,-H)]
assert len(rows) == 32, len(rows)
for row, (a,b,p) in zip(rows, [(a,b,p) for a,b in pairs for p in ['legacy','viaIR']]):
    prefix=f'pipeline={p};a={a};b={b};source='
    assert row.startswith(prefix), row
    source,target = row[len(prefix):].strip().split(';target=')
    value=a*b
    if not -H <= value < H:
        assert source.startswith('panic:')
        assert json.loads(source[6:]) == [78,72,123,113]+[0]*31+[17]
        assert target == 'coarse-revert'
    else:
        assert source == ('ok:some '+(f'({value})' if value<0 else str(value)))
        stack,skip,cells = target.split(';')
        assert json.loads(stack[3:]) == [str(value%W),'77','88']
        assert skip == 'skip:0'
        assert json.loads(cells[6:]) == list(map(str,[20,16,16,0,b%W,a%W,2,7,9,1,4]))
print('PASS: all 32 complete rows, both pipelines, exact panic/stack/cells')
