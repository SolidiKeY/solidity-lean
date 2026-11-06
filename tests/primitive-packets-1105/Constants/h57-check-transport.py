#!/usr/bin/env python3
"""Guard regression: mapFree transport must retain the frozen refusal domain and strict failure."""
import argparse, hashlib, json, pathlib, subprocess
ROOT = pathlib.Path(__file__).resolve().parents[3]
HERE = pathlib.Path(__file__).resolve().parent
sha = lambda b: hashlib.sha256(b).hexdigest()
def original(base, path):
    return subprocess.check_output(['git', 'show', base + ':' + path], cwd=ROOT)
def function(text, name):
    start = text.index('def ' + name + ' ')
    return text[start:text.index('/-- **Explicit conversion**', start)]
def statement(text):
    start = text.index('theorem conversion_refused ')
    return text[start:text.index(':=', start)].rstrip()
def module_checks(text, frozen_types, old_source, current_source):
    expected = function(frozen_types, 'STy.implicit').replace('def STy.implicit ', 'def implicitV0 ', 1)
    start = text.index('def implicitV0 ')
    actual = text[start:text.index('/-- The rational/integer branch', start)]
    assert actual == expected, 'legacy definition differs from frozen full function'
    old_lhs = '(Source.STy.rational (Source.Q.ofInt z)).implicit E.isBase (.int t)'
    version_lhs = 'implicitV0 E.isBase (Source.STy.rational (Source.Q.ofInt z)) (.int t)'
    old_header = statement(old_source)
    assert old_header.count(old_lhs) == 1
    v0 = text.split('namespace V0\n', 1)[1].split('end V0', 1)[0]
    v1 = text.split('namespace V1\n', 1)[1].split('end V1', 1)[0]
    assert statement(v0) == old_header.replace(old_lhs, version_lhs), 'V0 statement domain changed'
    assert statement(v1) == statement(current_source), 'V1 statement differs from production'
def verify(meta, text):
    base = meta['frozen_base']
    frozen = {p: original(base, p) for p in meta['frozen_hashes']}
    current = {p: (ROOT / p).read_bytes() for p in meta['current_hashes']}
    assert {p: sha(b) for p,b in frozen.items()} == meta['frozen_hashes'], 'frozen source pin differs'
    assert {p: sha(b) for p,b in current.items()} == meta['current_hashes'], 'paired current source differs'
    for p in ['Solidity/Source/Const.lean','Solidity/Source/Syntax.lean','Solidity/Source/Resolve.lean','Solidity/Source/Decls.lean','lean-toolchain']:
        assert frozen[p] == current[p], 'legacy dependency changed: ' + p
    cp = 'Solidity/Source/Ctor.lean'
    assert frozen[cp].decode().split('/-- The nodes of a tree',1)[0] == current[cp].decode().split('/-- The nodes of a tree',1)[0], 'constructor data prefix changed'
    tp = 'Solidity/Source/Types.lean'
    old = frozen[tp].decode(); now = current[tp].decode()
    for start,end in [('/-- A one-word value type', '/-! ## Integer and fixed-point ranges -/'),
                      ('/-- A reference type moved to a location', '/-- solc\'s location rule'),
                      ('/-- Whether a type holds no mapping', '/-- **Implicit conversion**')]:
        i = now.index(start); j = now.index(end,i); now = now[:i] + now[j:]
    assert now.split('/-- **Implicit conversion**',1)[0] == old.split('/-- **Implicit conversion**',1)[0], 'legacy type/dependency prefix changed'
    assert sha(function(old,'STy.implicit').encode()) == meta['legacy_function_sha256']
    sp = 'Solidity/Backend/PrimitivePackets/Constants/Source.lean'
    before = frozen[sp].decode(); after = current[sp].decode()
    old_lhs = '.implicit E.isBase (.int t)'
    assert before.count(old_lhs) == 1
    assert before.replace(old_lhs,'.implicit E.isBase E.mapFree (.int t)') == after, 'production drift exceeds recorded argument'
    assert frozen[sp] != current[sp], 'original strict failure was unexpectedly cleared'
    kernel = meta['frozen_kernel_inventory']
    raw = original(base, kernel['path'])
    assert sha(raw) == kernel['sha256'], 'frozen typed inventory differs'
    rows = [r for r in json.loads(raw) if r['name'] == kernel['name']]
    assert len(rows) == 1 and rows[0]['kind'] == 'theorem'
    assert not rows[0]['isUnsafe'] and not rows[0]['isPartial']
    module_checks(text, old, before, after)
    return old,before,after

def main():
    p = argparse.ArgumentParser(); p.add_argument('--output', type=pathlib.Path); a = p.parse_args()
    meta = json.loads((HERE/'h57-conversion-transport.json').read_text())
    text = (HERE/'H57ConversionTransport.lean').read_text()
    old,before,after = verify(meta,text)
    mutations = [text.replace('| .rational q, .int t => decide (q.FitsInt t)', '| .rational q, .int t => true',1),
                 text.replace('    (outside : ¬ (t.lo ≤ z ∧ z ≤ t.hi)) :','    (outside : False) :',1),
                 text.replace('namespace V1\n','namespace V1\n',1).replace('.implicit E.isBase E.mapFree (.int t)', '.implicit E.isBase (fun _ => true) (.int t)',1)]
    for changed in mutations:
        assert changed != text
        try: module_checks(changed,old,before,after)
        except AssertionError: pass
        else: raise AssertionError('mutation accepted')
    result = dict(status='versioned-source-fidelity-pass', strict_original_inventory_pass=False,
                  strict_failure_preserved=True, negative_controls=3,
                  frozen_base=meta['frozen_base'], module_sha256=sha(text.encode()),
                  boundary='Source/dependency/header checks only. Kernel transport and full acceptance remain separate gates.')
    if a.output:
        assert not a.output.resolve().is_relative_to(ROOT), 'external output required'
        a.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result))
if __name__ == '__main__': main()
