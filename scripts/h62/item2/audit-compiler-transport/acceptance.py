#!/usr/bin/env python3
"""Adversarial scanner acceptance and complete frozen per-module regression."""
import json
from pathlib import Path
import re
import subprocess
import tempfile
from unittest.mock import patch
from census import BASE, MAP, declarations, generate

ROOT = Path(__file__).resolve().parents[4]
EXPECTED = ROOT/'tests/h62/item2/audit-compiler-transport/frozen-modules.json'


def main():
    fixture = '''/- theorem fake : False := by /- nested -/ contradiction -/
namespace Outer
section S
variable {n : Nat}
@[simp] theorem actual (h : n = 1) (f : Nat := 2) : n = 1 := h
-- theorem gone : False := nope
end S
namespace Inner
private theorem impossible (h : False) : False := h
def quoted := "theorem string : False := nope"
end Inner
end Outer
'''
    rows = declarations(fixture, 'Fixture.lean')
    assert [r['source_name'] for r in rows] == ['Outer.actual', 'Outer.Inner.impossible']
    assert rows[0]['signature'].endswith(': n = 1')
    assert rows[1]['visibility'] == 'private' and rows[1]['false_conclusion']
    result = generate(ROOT)
    expected = json.loads(EXPECTED.read_text())
    assert result['modules'] == expected['modules']
    assert result['summary'] == expected['summary']
    assert len({r['id'] for r in result['statements']}) == 560
    # Regression for a current-tree map-row omission: must fail before scanning.
    real_read = Path.read_bytes
    first_line = next(l for l in (ROOT/MAP).read_bytes().splitlines(keepends=True)
                      if l.startswith(b'| `') and b'.lean` |' in l)
    altered = (ROOT/MAP).read_bytes().replace(first_line, b'', 1)
    def changed_read(path):
        return altered if path == ROOT/MAP else real_read(path)
    with patch.object(Path, 'read_bytes', changed_read):
        try: generate(ROOT)
        except ValueError as e: assert str(e) == 'frozen module-map modified'
        else: raise AssertionError('removed map row accepted')
    # Independent per-file raw token census after a separately implemented comment
    # remover. This comparison uses no declaration extraction or namespace parser.
    def uncomment(text):
        pattern = re.compile(r'/\-|\-/|--[^\n]*|"(?:\\.|[^"\\])*"', re.S)
        depth, prev, chunks = 0, 0, []
        for m in pattern.finditer(text):
            if depth == 0: chunks.append(text[prev:m.start()])
            token = m.group()
            if token == '/-': depth += 1
            elif token == '-/' and depth: depth -= 1
            prev = m.end()
        if depth == 0: chunks.append(text[prev:])
        return ''.join(chunks)
    for entry in result['modules']:
        source = subprocess.check_output(['git','show',f"{BASE}:{entry['module']}"], cwd=ROOT).decode()
        assert len(re.findall(r'\btheorem\s+[^\s:({]+', uncomment(source))) == entry['theorems'], entry['module']
    # Exercise the required slowdown boundary and mismatched-context rejection.
    timing = ROOT/'scripts/h62/item2/audit-compiler-transport/compare_timings.py'
    with tempfile.TemporaryDirectory(prefix='h62-timing-') as directory:
        temp = Path(directory)
        before, after = [], []
        for label, target in [('before', before), ('after', after)]:
            for i in range(3):
                path = temp/f'{label}-{i}.json'
                target.append(path)
        def trial(seconds, expected_exit, changed_context=False):
            for paths, elapsed in [(before, 10), (after, seconds)]:
                for path in paths:
                    context = 'different' if changed_context and paths is after else 'same'
                    path.write_text(json.dumps({'exit':0, 'stop_reason':None,
                                                'wall_seconds':elapsed, 'command':['fixture'], 'context':context}))
            command = ['python3', str(timing), '--before', *map(str,before),
                       '--after', *map(str,after), '--output', str(temp/'result.json')]
            checked = subprocess.run(command, capture_output=True, text=True)
            assert checked.returncode == expected_exit, checked.stderr+checked.stdout
        trial(11, 0)
        trial(11.01, 2)
        trial(10, 1, True)
    print('PASS: 122 frozen module rows; 560 unique declarations; per-module hashes/counts; nested-comment/string/inline-attribute/default-binder fixtures; removed-row rejection; independent token counts; >10% stop and context mismatch controls')
    print('BOUNDARY: source acceptance only; elaborated census, joint witnesses and totality remain separate gates')

if __name__ == '__main__': main()
