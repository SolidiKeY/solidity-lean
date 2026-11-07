"""Exact local theorem-statement and observed-axiom coverage, not final trust acceptance."""
import hashlib,json,pathlib,re
root=pathlib.Path(__file__).resolve().parents[3]
evidence=root/'tests/h28-sol/type-grammar/evidence'
records=json.loads((evidence/'local-axiom-signatures.json').read_text())
seen=set()
for source in (root/'Solidity/Frontend/TypeGrammarH28').glob('*.lean'):
    text=source.read_text()
    namespace=re.search(r'^namespace ([\w.]+)',text,re.M).group(1)
    for hit in re.finditer(r'^theorem (\w+)[\s\S]*? := (?:by|rfl)',text,re.M):
        short=hit.group(1);name=namespace+'.'+short
        record=records[name]
        assert record['source']==str(source.relative_to(root)),name
        assert record['statement']==hit.group(0).rsplit(' := ',1)[0],name
        assert '#print axioms '+short in text,name
        log=evidence/record['evidence']
        gate=json.loads(log.with_suffix('.json').read_text())
        assert gate['exit']==0 and gate.get('guard') is None,name
        assert gate.get('source_unchanged') is True,name
        assert gate['source_hashes'][record['source']]==hashlib.sha256(source.read_bytes()).hexdigest(),name
        lines=log.read_text().splitlines()
        assert any('Build completed successfully' in line for line in lines),name
        if not record['axioms']:
            expected="'"+name+"' does not depend on any axioms"
        else:
            expected="'"+name+"' depends on axioms: ["+', '.join(record['axioms'])+']'
        assert any(line.endswith(expected) for line in lines),name
        assert record['axioms'] in ([],['propext']),name
        seen.add(name)
assert seen==set(records)
print('PASS: every one of '+str(len(seen))+' local theorem statements has a matching observed axiom signature and print site')
print('No type-name syntax uniqueness, parser completeness, solc fixture or full-assignment acceptance is implied')
