#!/usr/bin/env python3
"""Check/generate the pinned Solidity feature catalog. No third-party packages."""
import argparse
import hashlib
import html
import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
MANIFEST = ROOT / 'docs/solidity-features.json'
LEDGER = ROOT / 'docs/solidity-upstream-inventory.json'
LEAN = ROOT / 'Solidity/Language/Features.lean'
REPORT = ROOT / 'docs/solidity-feature-inventory.md'


def strip_comments(text):
    # Only used to recognize source declarations, not to parse Solidity programs.
    return re.sub(r'/\*.*?\*/|//[^\n]*',
                  lambda m: '\n' * m[0].count('\n'), text, flags=re.S)


def extract_symbols(upstream):
    """Bounded, explicit source surfaces. A source hash change also fails the audit."""
    read = lambda p: (upstream / p).read_text()
    parser = strip_comments(read('docs/grammar/SolidityParser.g4'))
    lexer = strip_comments(read('docs/grammar/SolidityLexer.g4'))
    ast = strip_comments(read('libsolidity/ast/AST.h'))
    types_h = strip_comments(read('libsolidity/ast/Types.h'))
    types_cpp = strip_comments(read('libsolidity/ast/Types.cpp'))
    glob = strip_comments(read('libsolidity/analysis/GlobalContext.cpp'))
    kinds = types_h.split('class FunctionType:')[1].split('enum class Kind')[1].split('};')[0]
    magic = types_cpp.split('MagicType::nativeMembers')[1].split('std::string MagicType::toString')[0]
    result = {
        'parserRules': re.findall(r'^([a-z]\w*)(?:\[[^\]\n]*\])?\s*(?::|\nlocals)', parser, re.M),
        'expressionAlternatives': re.findall(r'#\s*(\w+)', parser),
        'lexerRules': re.findall(r'^(?:fragment )?([A-Z]\w*)\s*:', lexer, re.M),
        'astClasses': re.findall(r'^class (\w+)[^;\n]*\n\{', ast, re.M),
        'functionKinds': re.findall(r'^\s*(\w+)\s*,', kinds, re.M),
        'globalNames': re.findall(r'\{"(\w+)",\s*-\d+\}', glob),
        'yulBuiltins': re.findall(r"'([^']+)'", lexer.split('YulEVMBuiltin:')[1].split(';')[0]),
        'compilerTokens': re.findall(r'^\s*[TK]\((\w+),', read('liblangutil/Token.h'), re.M),
        'typeCategories': re.findall(r'^\s*(\w+)\s*,?\s*$', types_h.split('enum class Category')[1].split('};')[0], re.M),
        'nativeMemberOwners': re.findall(r'MemberList::MemberMap (\w+)::nativeMembers\(', types_cpp),
    }
    members = []
    for case in re.finditer(r'case Kind::(\w+):', magic):
        start = case.end()
        stop = magic.find('case Kind::', start)
        section = magic[start:] if stop < 0 else magic[start:stop]
        members.extend(case[1] + '.' + s for s in re.findall(r'\{"(\w+)"\s*,', section))
    result['magicMembers'] = members
    for owner in ['AddressType', 'FixedBytesType', 'ArrayType', 'FunctionType', 'TypeType']:
        body = types_cpp.split(owner + '::nativeMembers')[1]
        body = body.split('\n}\n', 1)[0]
        result[owner + 'Members'] = re.findall(r'\{\s*"(\w+)"\s*,\s*TypeProvider::', body)
        result[owner + 'Members'] += re.findall(
            r'emplace_back\(\s*(?:MemberList::Member\{)?"(\w+)"', body)
    return {k: sorted(set(v)) for k, v in result.items()}


def q(value):
    return json.dumps(value, ensure_ascii=False)


def raw_text(value):
    # The repository's trust scanner deliberately examines ordinary string text.
    # Raw strings identify explanatory prose without hiding executable terms.
    hashes = '#'
    while '"' + hashes in value:
        hashes += '#'
    return 'r' + hashes + '"' + value + '"' + hashes


def render_lean(data):
    rows = data['features']
    excluded = [r for r in rows if r['scope'] == 'exclude']
    block = [r for r in excluded if r['id'].startswith('block') and r['syntax'].startswith('block.')]
    ordinary = [r for r in excluded if r not in block]
    lines = ['import Lean.Data.Name', '', '/-!', '# Solidity feature scope', '',
             'Generated from docs/solidity-features.json by scripts/solidity-feature-audit.py.',
             'The catalog classifies language features; it does not implement a Solidity parser,',
             'a feature extractor, or a proof of frontend/solc equivalence. The subset wrapper',
             'is meaningful only with a complete, declaration-aware feature extractor.',
             '-/', '', 'namespace Solidity.Language', '',
             'inductive Scope where', '  | model | abstract | exclude | upstream',
             '  deriving Repr, DecidableEq, Inhabited', '',
             '/-- Source inspection status, not an end-to-end correctness certificate. -/',
             'inductive Current where', '  | present | limited | missing | notApplicable',
             '  deriving Repr, DecidableEq, Inhabited', '',
             'structure SourceRef where', '  path : String', '  line : Nat',
             '  deriving Repr, DecidableEq, Inhabited', '',
             'structure FeatureInfo where', '  category : String', '  spelling : String',
             '  scope : Scope', '  current : Current', '  requirement : String',
             '  upstream : List SourceRef', '  localEvidence : List String',
             '  deriving Repr, DecidableEq, Inhabited', '', 'inductive Feature where']
    lines.extend('  | '+r['id'] for r in rows)
    lines += ['  deriving Repr, DecidableEq, Inhabited', '', 'def Feature.id : Feature → String']
    lines.extend('  | .'+r['id']+' => '+q(r['id']) for r in rows)
    lines += ['', 'def Feature.info : Feature → FeatureInfo']
    for r in rows:
        refs = ', '.join('{ path := '+q(s['path'])+', line := '+str(s['line'])+' }' for s in r['upstream'])
        ev = ', '.join(q(s) for s in r['localEvidence'])
        current = 'limited' if r['current'] == 'partial' else r['current']
        lines += ['  | .'+r['id']+' =>', '    { category := '+q(r['category'])+', spelling := '+q(r['syntax'])+',',
                  '      scope := .'+r['scope']+', current := .'+current+',',
                  '      requirement := '+raw_text(r['requirement'])+',',
                  '      upstream := ['+refs+'], localEvidence := ['+ev+'] }']
    lines += ['', 'def Feature.all : List Feature :=', '  [ '+',\n    '.join('.'+r['id'] for r in rows)+' ]', '',
              '/-- The catalog list enumerates the entire feature type. -/',
              'theorem Feature.all_complete (f : Feature) : f ∈ Feature.all := by',
              '  cases f <;> decide', '',
              '/-- Fields excluded by this profile; timestamp is intentionally absent. -/',
              'inductive BlockField where']
    lines += ['  | '+r['syntax'].split('.')[1] for r in block]
    lines += ['  deriving Repr, DecidableEq, Inhabited', '', 'def BlockField.id : BlockField → String']
    lines += ['  | .'+r['syntax'].split('.')[1]+' => '+q(r['syntax'].split('.')[1]) for r in block]
    lines += ['', 'inductive Unmodelled where', '  | blockField (field : BlockField)']
    lines += ['  | '+r['id'] for r in ordinary]
    lines += ['  deriving Repr, DecidableEq, Inhabited', '', 'def Unmodelled.feature : Unmodelled → Feature']
    lines += ['  | .blockField .'+r['syntax'].split('.')[1]+' => .'+r['id'] for r in block]
    lines += ['  | .'+r['id']+' => .'+r['id'] for r in ordinary]
    lines += ['', 'def Unmodelled.reason (u : Unmodelled) : String := u.feature.info.requirement', '',
              'def Unmodelled.errorName (u : Unmodelled) : Lean.Name :=', '  match u with',
              '  | .blockField f => .str (.str (.str .anonymous "solidity") "blockField") f.id',
              '  | _ => .str (.str .anonymous "solidity") u.feature.id', '',
              'def Feature.unmodelled? : Feature → Option Unmodelled']
    lines += ['  | .'+r['id']+' => some (.blockField .'+r['syntax'].split('.')[1]+')' for r in block]
    lines += ['  | .'+r['id']+' => some .'+r['id'] for r in ordinary]
    lines += ['  | _ => none', '', 'def Unmodelled.all : List Unmodelled :=',
              '  Feature.all.filterMap Feature.unmodelled?', '',
              'def modelFeatures : List Feature :=',
              '  Feature.all.filter fun f => f.info.scope == .model', '',
              'def abstractFeatures : List Feature :=',
              '  Feature.all.filter fun f => f.info.scope == .abstract', '',
              'def targetFeatures : List Feature :=',
              '  Feature.all.filter fun f => f.info.scope == .model || f.info.scope == .abstract', '',
              'def outsideScope : List Unmodelled := Unmodelled.all', '',
              'def presentFeatures : List Feature :=',
              '  targetFeatures.filter fun f => f.info.current == .present', '',
              'def missingFeatures : List Feature :=',
              '  targetFeatures.filter fun f => f.info.current == .missing', '',
              'def partialFeatures : List Feature :=',
              '  targetFeatures.filter fun f => f.info.current == .limited', '',
              'def rejectedByUpstream : List Feature :=',
              '  Feature.all.filter fun f => f.info.scope == .upstream', '',
              'def requirements : List (Feature × String) :=',
              '  targetFeatures.map fun f => (f, f.info.requirement)', '',
              '/-- A policy decision; no assertion of current implementation support. -/',
              'def Feature.inProfile (f : Feature) : Prop :=',
              '  f.info.scope = .model ∨ f.info.scope = .abstract', '',
              'def WithinProfile (features : List Feature) : Prop :=',
              '  ∀ f ∈ features, f.inProfile', '',
              '/-- Restrict an actual syntax representation using a supplied feature extractor.',
              'Completeness of `uses` must be established separately; this is not a fake full AST. -/',
              'def ProfileSyntax (Syntax : Type u) (uses : Syntax → List Feature) : Type u :=',
              '  { ast : Syntax // WithinProfile (uses ast) }', '',
              '/-- The diagnostic metadata and exclusion decision cannot disagree. -/',
              'theorem Unmodelled.excluded (u : Unmodelled) : u.feature.info.scope = .exclude := by',
              '  cases u with', '  | blockField f => cases f <;> rfl']
    lines += ['  | '+r['id']+' => rfl' for r in ordinary]
    lines += ['', '/-- Every deliberately excluded feature has a structured diagnostic. -/',
              'theorem Feature.exclusion_complete (f : Feature) (h : f.info.scope = .exclude) :',
              '    ∃ u : Unmodelled, f.unmodelled? = some u ∧ u.feature = f := by',
              '  cases f <;> first | exact ⟨_, rfl, rfl⟩ | cases h', '',
              'def upstreamCommit : String := '+q(data['upstream']['commit']),
              'def upstreamVersion : String := '+q(data['upstream']['tag']), '',
              'end Solidity.Language', '']
    return '\n'.join(lines)


def render_report(data):
    up = data['upstream']
    base = f"https://github.com/{up['repository']}/blob/{up['commit']}/"
    out = ['# Solidity feature inventory', '',
           'Generated by `python3 scripts/solidity-feature-audit.py` from [the manifest](solidity-features.json).',
           'Read [the scope and interpretation](solidity-scope.md) before treating an entry as supported.', '',
           f"Pinned upstream: [{up['tag']}]({base}Changelog.md), commit `{up['commit']}`.", '',
           '`model`: target functional semantics; `abstract`: explicit environment/oracle/profile;',
           '`exclude`: deliberately outside this profile; `upstream`: removed, reserved or incomplete upstream.', '',
           '`present` means source-level implementation evidence exists for the named narrow feature;',
           '`partial` is a conditional/limited implementation; `missing` is work to add.',
           'These are inspection assessments, not equivalence certificates. Local evidence is a starting point for review.', '',
           'Current inventory: ' + str(len(data['features'])) + ' feature families; ' +
           ', '.join(str(sum(r['current'] == status for r in data['features'])) + ' ' + status
                     for status in ['present', 'partial', 'missing', 'notApplicable']) + '.', '']
    for category in dict.fromkeys(r['category'] for r in data['features']):
        out += ['## '+category.title(), '', '| Feature / syntax | Scope | Current | Required meaning / reason | Evidence |', '|---|---|---|---|---|']
        for r in data['features']:
            if r['category'] != category:
                continue
            refs = ', '.join(f"[upstream]({base}{s['path']}#L{s['line']})" for s in r['upstream'])
            refs += ''.join(f'; [local](../{p})' for p in r['localEvidence'])
            if 'decision' in r:
                d = r['decision']
                refs += f"; [decision {d['question']}, {d['date']}](../{d['record']}): {d['outcome']}"
                refs += f" — {d['note']}" if 'note' in d else ''
            safe = lambda s: s.replace('|', '&#124;').replace('\n', ' ')
            out += [f"| `{r['id']}`<br><code>{safe(html.escape(r['syntax']))}</code> | {r['scope']} | {r['current']} | {safe(r['requirement'])} | {refs} |"]
        out += ['']
    return '\n'.join(out)


# A scope decision cites an attributable user decision: the record's anchor
# must hold the repository's "**User decision (date):**" marker. Decisions are
# provenance only; the Lean catalog does not carry them.
DECISION_OUTCOMES = {
    'G00 Q1': ({'exclude'}, {'approvedExclusion'}),
    'G00 Q2': ({'abstract'}, {'approved', 'replace', 'provedSpecialCase', 'followsG01'}),
    'G00 Q6': ({'model'}, {'fullSupport'}),
}
DECIDED_SCOPES = {'exclude': 'G00 Q1', 'abstract': 'G00 Q2'}


def decision_marker(record, date):
    path, _, anchor = record.partition('#')
    assert anchor and (ROOT / path).is_file(), ('decision record not found', record)
    text = (ROOT / path).read_text()
    slug = lambda h: re.sub(r'[^a-z0-9 -]', '', h.lower()).replace(' ', '-')
    lines = text.splitlines()
    heads = [i for i, line in enumerate(lines) if line.startswith('#') and slug(line.lstrip('#').strip()) == anchor]
    assert len(heads) == 1, record
    section = []
    for line in lines[heads[0] + 1:]:
        if line.startswith('#'):
            break
        section.append(line)
    return '\n'.join(section), f'**User decision ({date}):**'


def validate_decision(r):
    d = r.get('decision')
    if r['scope'] in DECIDED_SCOPES:
        assert d and d['question'] == DECIDED_SCOPES[r['scope']], ('scope without its decision', r['id'])
    if d is None:
        return
    assert set(d) <= {'date', 'question', 'outcome', 'record', 'note'}, d
    assert re.fullmatch(r'\d{4}-\d{2}-\d{2}', d['date']), d
    scopes, outcomes = DECISION_OUTCOMES[d['question']]
    assert r['scope'] in scopes and d['outcome'] in outcomes, (r['id'], d)
    section, marker = decision_marker(d['record'], d['date'])
    assert marker in section and f"| {d['question']} " in section, ('decision not in record', r['id'], d)


def validate(data, ledger, upstream=None):
    rows = data['features']
    ids = [r['id'] for r in rows]
    assert len(ids) == len(set(ids)), 'duplicate feature IDs'
    assert data['schemaVersion'] == 1
    assert re.fullmatch(r'[0-9a-f]{40}', data['upstream']['commit'])
    for r in rows:
        assert re.fullmatch(r'[a-z][A-Za-z0-9]*', r['id']), r['id']
        assert r['scope'] in ('model', 'abstract', 'exclude', 'upstream'), r
        assert r['current'] in ('present', 'partial', 'missing', 'notApplicable'), r
        assert r['requirement'] and r['syntax'] and r['upstream'], r
        assert (r['scope'] in ('exclude', 'upstream')) == (r['current'] == 'notApplicable'), r
        if r['current'] in ('present', 'partial'):
            assert r['localEvidence'], r
        for path in r['localEvidence']:
            assert (ROOT / path).is_file(), path
        validate_decision(r)
    source_paths = {s['path'] for s in data['upstream']['sources']}
    assert len(source_paths) == len(data['upstream']['sources']), 'duplicate source paths'
    for source in data['upstream']['sources']:
        assert re.fullmatch(r'[0-9a-f]{64}', source['sha256']), source
        assert re.fullmatch(r'[0-9a-f]{40}', source['gitBlobSha']), source
    assert ledger['commit'] == data['upstream']['commit']
    assert ledger['schemaVersion'] == 1
    referenced = set()
    for family, symbols in ledger['symbols'].items():
        assert symbols, family
        for symbol, features in symbols.items():
            assert features and set(features) <= set(ids), (family, symbol, features)
            referenced.update(features)
    for r in rows:
        assert all(s['path'] in source_paths and s['line'] > 0 for s in r['upstream']), r
    if upstream:
        for s in data['upstream']['sources']:
            content = (upstream / s['path']).read_bytes()
            assert hashlib.sha256(content).hexdigest() == s['sha256'], 'source drift: '+s['path']
            blob = b'blob ' + str(len(content)).encode() + b'\0' + content
            assert hashlib.sha1(blob).hexdigest() == s['gitBlobSha'], 'GitHub blob mismatch: '+s['path']
        observed = extract_symbols(upstream)
        assert set(observed) == set(ledger['symbols']), 'inventory families changed'
        for family, symbols in observed.items():
            assert set(symbols) == set(ledger['symbols'][family]), f'unclassified/drifted {family}: '+str(set(symbols) ^ set(ledger['symbols'][family]))
        for r in rows:
            for s in r['upstream']:
                assert s['line'] <= len((upstream / s['path']).read_text().splitlines()), r


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--check', action='store_true', help='fail instead of rewriting generated files')
    p.add_argument('--upstream', type=Path, help='also check exact source hashes and symbol coverage against a checkout')
    args = p.parse_args()
    data, ledger = json.loads(MANIFEST.read_text()), json.loads(LEDGER.read_text())
    validate(data, ledger, args.upstream)
    for path, content in [(LEAN, render_lean(data)), (REPORT, render_report(data))]:
        if args.check:
            assert path.read_text() == content, f'stale generated file: {path}'
        else:
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(content)
    from collections import Counter
    print(f"{len(data['features'])} features: {dict(Counter(r['scope'] for r in data['features']))}")
    print(f"{sum(len(s) for s in ledger['symbols'].values())} upstream symbols classified; generated files current")


if __name__ == '__main__':
    main()
