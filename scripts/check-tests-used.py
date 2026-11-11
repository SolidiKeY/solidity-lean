#!/usr/bin/env python3
"""Inventory committed tests and H55/H62 harnesses; never prune or run them.

Usage (from any directory in the repository):
  python3 scripts/check-tests-used.py --ref origin/master --write
  python3 scripts/check-tests-used.py --ref origin/master --check
  python3 scripts/check-tests-used.py --self-test

Inputs are Git objects, not working-tree fixture bytes. --write writes only
scripts/tests-inventory.json. --check rebuilds the deterministic model, verifies
recovery objects, and rejects unresolved classifications as well as tampering.
A partial --write is useful for review but returns 1 and is NOT acceptance.
Run recorded generators/reproducers only in disposable committed-byte copies;
their commands can write fixed paths. Normal write/check never executes them.

The use graph is deliberately an under-approximation: explicit reviewed routes,
Lean imports/solc_imports and validated Python reads of measured bytes.
Unchanged demonstrated committed runners may be source-only roots with
unavailable current validation, without fixture/child or passing-reproducer credit.
Text matches are search candidates, never invocation edges. Shell expansion,
Python eval/importlib, computed Node reads and producer environments need review;
no static absence is sufficient to prune a candidate. Unresolved paths have a
null class and make the completion check fail. Repository-wide policy scans
are secondary coverage; keep requires independent test/runner/Lean/fixture use.
The inventory cannot justify itself: classifier and inventory paths are excluded from candidate discovery.

Recovery selects the first change in Git's topological history that introduced
the measured blob at that path (no rename following). A unique merge resolution uses Git path-specific history. Every selected commit:path is checked against the measured object.
No receipt, timestamp, workstation path or execution result belongs in this data.
"""
from __future__ import annotations

import argparse
import ast
import bisect
import collections
import hashlib
import gzip
import io
import zlib
import json
import math
import posixpath
import re
import subprocess
import sys
import tempfile
import shlex
import importlib.util
from pathlib import Path, PurePosixPath

SCOPE = ('tests/', 'scripts/h55/', 'scripts/h62/')
OUTPUT = 'scripts/tests-inventory.json'
SCHEMA = 1
sys.dont_write_bytecode = True
CLASSES = ('keep', 'regenerable', 'evidence', 'orphan')
EXCLUDED = ('scripts/check-tests-used', OUTPUT)


def git(root, *args, data=None):
    p = subprocess.run(['git', '--no-replace-objects', '-C', str(root), *args],
                       input=data, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    if p.returncode:
        raise ValueError(f'git {args[0]}: {p.stderr.decode(errors="replace").strip()}')
    return p.stdout


def decode(b):
    return b.decode('utf-8', 'surrogateescape')


def canonical(value):
    return (json.dumps(value, ensure_ascii=True, indent=2, sort_keys=True) + '\n').encode()


def excluded(p):
    return any(p.startswith(x) for x in EXCLUDED)


def clean(path):
    path = posixpath.normpath(path)
    return path if path != '..' and not path.startswith(('../', '/')) else None


class Repository:
    def __init__(self, root, ref):
        self.root = Path(root)
        self.ref = decode(git(root, 'rev-parse', '--verify', ref + '^{commit}')).strip()
        self.tree = {}
        for item in git(root, 'ls-tree', '-r', '-z', self.ref).split(b'\0'):
            if not item:
                continue
            meta, path = item.split(b'\t', 1)
            mode, kind, oid = meta.split()
            self.tree[decode(path)] = (decode(mode), decode(kind), decode(oid))
        self.paths = sorted(p for p in self.tree if p.startswith(SCOPE))
        self.shallow = decode(git(root, 'rev-parse', '--is-shallow-repository')).strip() == 'true'
        self.boundaries = set()
        if self.shallow:
            shallow_file = Path(decode(git(root, 'rev-parse', '--git-path', 'shallow')).strip())
            if not shallow_file.is_absolute(): shallow_file = self.root / shallow_file
            self.boundaries = set(shallow_file.read_text().splitlines())
        # One batch subprocess, including duplicate objects only once.
        oids = sorted({oid for _, kind, oid in self.tree.values() if kind == 'blob'})
        raw = git(root, 'cat-file', '--batch', data=('\n'.join(oids) + '\n').encode())
        self.blobs = {}
        at = 0
        for expected in oids:
            end = raw.index(b'\n', at)
            oid, kind, size = raw[at:end].split()
            if decode(oid) != expected or kind != b'blob':
                raise ValueError('unexpected batch object header')
            at = end + 1
            size = int(size)
            self.blobs[expected] = raw[at:at + size]
            at += size + 1
        self.texts = {p: decode(self.blobs[oid]) for p, (_, kind, oid) in self.tree.items()
                      if kind == 'blob' and b'\0' not in self.blobs[oid] and not excluded(p)}

    def bytes(self, p):
        return self.blobs[self.tree[p][2]]

    def pins(self):
        wanted = set(self.paths)
        pins = {}
        tokens = git(self.root, 'log', '--topo-order', '--full-history', '--diff-merges=combined',
                     '--format=commit:%H', '--raw', '-z', '--no-abbrev',
                     '--no-renames', '--diff-filter=AMT', self.ref, '--', *SCOPE).split(b'\0')
        commit = None
        i = 0
        while i < len(tokens):
            token = tokens[i].strip(b'\n')
            i += 1
            if token.startswith(b'commit:'):
                commit = decode(token[7:])
            elif token.startswith(b':'):
                if i >= len(tokens):
                    raise ValueError('truncated raw history')
                p = decode(tokens[i]); i += 1
                if commit not in self.boundaries and p in wanted and p not in pins and decode(token.split()[-2]) == self.tree[p][2]:
                    pins[p] = commit
        # Unique merge resolutions may have no nonmerge authoring object.
        # Resolve only those exceptional paths with Git's path-specific history.
        for p in self.paths:
            if p not in pins:
                last = decode(git(self.root, 'log', '-1', '--format=%H', self.ref, '--', p)).strip()
                if last and last not in self.boundaries: pins[p] = last
        specs = [(p, pins[p] + ':' + p) for p in self.paths if p in pins]
        # Batch verify the pinned tree lookup itself, not merely a matching raw diff.
        raw = git(self.root, 'cat-file', '--batch-check', '-Z', data=b''.join(
            s.encode('utf-8', 'surrogateescape') + b'\0' for _, s in specs))
        lines = raw.rstrip(b'\0').split(b'\0') if raw else []
        if len(lines) != len(specs):
            raise ValueError('recovery batch length differs')
        result = {}
        self.pin_limitations = {}
        for (p, spec), line in zip(specs, lines):
            pieces = line.split()
            if len(pieces) != 3 or decode(pieces[0]) != self.tree[p][2] or pieces[1] != b'blob':
                self.pin_limitations[p] = 'UNVERIFIABLE: last-touch tree lookup ' + spec + ' does not recover the measured blob'
                continue
            result[p] = {'last_touch_commit': pins[p], 'command': 'git show ' + shlex.quote(spec),
                         'blob': self.tree[p][2]}
        return result


class Graph:
    def __init__(self, repo):
        self.repo = repo
        self.roots = {}
        self.properties = {}
        self.notes = []
        self.observed = []
        self.policy_scans = {}
        self.policy_targets = set()
        self.uncertain_reads = collections.defaultdict(set)
        self.edges = collections.defaultdict(list)

    def root(self, p, kind, command, source, line, root_id=None):
        if p in self.repo.tree and not excluded(p):
            self.roots.setdefault(root_id or p, {'kind': kind, 'path': p, 'command': command,
                                     'location': f'{source}:{line}', 'cwd': '.'})

    def edge(self, source, target, line, operation, validated_for=None, kind="consumes", repository_lean=False):
        if target in self.repo.tree and not excluded(source) and not excluded(target):
            e = {'source': source, 'target': target, 'line': line, 'operation': operation, 'kind': kind}
            if validated_for is not None: e['validated_for'] = validated_for
            if repository_lean: e['repository_lean'] = True
            if e not in self.edges[source]:
                self.edges[source].append(e)

    def chains(self):
        chains = {}
        for root_id, entry in sorted(self.roots.items()):
            first = entry['path']
            found = {(first, True): {'root': root_id, 'entry': entry, 'edges': []}}
            queue = collections.deque([(first, True)])
            while queue:
                source, executing = queue.popleft()
                if not executing or entry.get('source_only'): continue
                for edge in sorted(self.edges[source], key=lambda e: (e['target'], e['line'], e['operation'])):
                    if edge.get('validated_for', root_id) != root_id: continue
                    if entry.get('lake_package') and edge.get('repository_lean'): continue
                    target = edge['target']
                    state = (target, edge['kind'] == 'executes')
                    if state not in found:
                        found[state] = {**found[(source, executing)], 'edges': found[(source, executing)]['edges'] + [edge]}
                        queue.append(state)
            for (target, _), chain in found.items():
                if target not in chains or len(chain['edges']) < len(chains[target]['edges']): chains[target] = chain
        # Observed stacks are ordered paths, not a graph quotient by filename.
        # Recursion and callbacks may revisit a source with a different frame.
        for target, chain in self.observed:
            if target not in chains or len(chain['edges']) < len(chains[target]['edges']):
                chains[target] = chain
        return chains


def lean_lex(text):
    """Mask nested Lean comments and strings, retaining literal spans and line offsets."""
    outside = re.compile(r'/\-|--[^\n]*|r#+"|"(?:\\.|[^"\\])*"')
    inside = re.compile(r'/\-|-/', re.MULTILINE)
    def blank(chunk):
        return re.sub(r'[^\n]+', lambda m: ' ' * len(m[0]), chunk)
    out = []; literals = []; depth = 0; at = 0
    while at < len(text):
        match = (inside if depth else outside).search(text, at)
        if match is None:
            out.append(blank(text[at:]) if depth else text[at:]); break
        gap = text[at:match.start()]
        out.append(blank(gap) if depth else gap)
        token = match[0]
        if depth:
            depth += 1 if token == '/-' else -1
            out.append(blank(token))
        elif token == '/-': depth = 1; out.append('  ')
        elif token.startswith('--'): out.append(blank(token))
        elif token.startswith('r#'):
            close = text.find('"' + token[1:-1], match.end())
            stop = len(text) if close < 0 else close + len(token) - 1
            out.append(blank(text[match.start():stop])); at = stop; continue
        else:
            literals.append((match.start(), token)); out.append(blank(token))
        at = match.end()
    return ''.join(out), literals


def lean_code(text):
    return lean_lex(text)[0]


def add_lean(graph):
    repo = graph.repo
    repo.lean_lex_cache = {}
    for p, text in repo.texts.items():
        if not p.endswith('.lean') or p.startswith('tests/h28-sol/non-vacuity/lean/'): continue
        code, literals = lean_lex(text)
        repo.lean_lex_cache[p] = code
        starts = [0] + [m.end() for m in re.finditer('\n', code)]
        by_line = collections.defaultdict(list)
        for start, literal in literals:
            by_line[bisect.bisect_right(starts, start)].append((start, literal))
        depth = 0
        for n, line in enumerate(code.splitlines(), 1):
            if depth == 0:
                match = re.match(r'\s*(?:(?:public|private|meta)\s+)*import(?:\s+all)?\s+(.+)', line)
                if match:
                    for module in match[1].split():
                        graph.edge(p, module.replace('.', '/') + '.lean', n, 'Lean import', kind='executes', repository_lean=True)
                for start, literal in by_line[n]:
                    if not re.fullmatch(r'\s*solc_import\s+', code[starts[n - 1]:start]): continue
                    try: argument = json.loads(literal)
                    except ValueError: continue
                    if not isinstance(argument, str): continue
                    target = clean(posixpath.join(posixpath.dirname(p), argument))
                    graph.edge(p, target, n, 'solc_import reads hash-pinned AST', repository_lean=True)
            depth += sum(line.count(c) for c in '([{') - sum(line.count(c) for c in ')]}')


def shell_operands(command):
    """Recognize interpreter operands, never words quoted/passed to echo.

    Complex shell syntax is not interpreted. Unsupported commands produce no
    certified edge; their references remain search candidates.
    """
    if any(operator in command for operator in (';', '&&', '||', '|', '<', '>', '$(', '`', '\\')):
        return []
    try: words = shlex.split(command, comments=True)
    except ValueError: return []
    while words and re.fullmatch(r'[A-Za-z_][A-Za-z_0-9]*=.*', words[0]): words.pop(0)
    if words[:2] == ['lake', 'env']: words = words[2:]
    if words and words[0] == 'timeout':
        words.pop(0)
        while words and words[0].startswith('-'): words.pop(0)
        if not words or not re.fullmatch(r'[0-9.]+[smhd]?', words.pop(0)): return []
    if not words or words[0] not in ('python', 'python3', 'node', 'bash', 'lean'): return []
    tool = words.pop(0)
    flags = {'-B', '-b', '-u', '-j1', '--test'}
    test = '--test' in words and tool == 'node'
    while words and (words[0] in flags or words[0].startswith('--tstack=')): words.pop(0)
    if not words or words[0].startswith('-'): return []
    if test and any(w.startswith('-') for w in words): return []
    return words if test else words[:1]


def add_roots(graph):
    repo = graph.repo
    for p, text in repo.texts.items():
        if not p.startswith('.github/workflows/') or not p.endswith(('.yml', '.yaml')): continue
        # Until step-level YAML cwd is modelled, refuse ambiguous workflows.
        if 'working-directory:' in text: continue
        blocks = []; block = None; indent = None
        for n, line in enumerate(text.splitlines(), 1):
            m = re.match(r'^(\s*)(?:-\s+)?run:\s*(.*)$', line)
            if m:
                if block: blocks.append(block)
                indent = len(m[1]) + (2 if line.lstrip().startswith('- ') else 0); block = []
                if m[2].startswith('>'):
                    block = None
                    continue
                if m[2] not in ('|', '>'): block.append((n, m[2]))
            elif block is not None and (not line.strip() or len(line) - len(line.lstrip()) > indent):
                block.append((n, line.strip()))
            else:
                if block is not None: blocks.append(block)
                block = None
        if block is not None: blocks.append(block)
        for block in blocks:
            if any('<<' in command or '\\' in command or
                   re.match(r'\s*(?:cd|pushd|popd|source|eval|if|for|while|case|function|\.)\b', command) or
                   any(c in command for c in ('{', '}', '(', ')'))
                   for _, command in block): continue
            for n, command in block:
                for target in shell_operands(command):
                    graph.root(target, 'CI', command, p, n)
    gate = 'scripts/coord-tools/gate.sh'
    if gate in repo.tree:
        graph.root(gate, 'gate', 'bash scripts/coord-tools/gate.sh full', gate, 1)
    if 'lakefile.toml' in repo.texts:
        import tomllib
        config = tomllib.loads(repo.texts['lakefile.toml'])
        for kind in ('lean_lib', 'lean_exe'):
            for entry in config.get(kind, []):
                names = entry.get('roots', [entry.get('root', entry['name'])])
                for name in names:
                    target = clean(posixpath.join(entry.get('srcDir', '.'), name.replace('.', '/') + '.lean'))
                    lineno = next((n for n, l in enumerate(repo.texts['lakefile.toml'].splitlines(), 1)
                                   if l.strip() == 'name = ' + json.dumps(entry['name'])), 1)
                    graph.root(target, 'Lean root', 'lake build ' + entry['name'], 'lakefile.toml', lineno)


def reviewed_routes(graph):
    """Narrow audited dispatch/reads; changed definitions fail closed.

    Each matcher names an operation, not an arbitrary lexical reference. These
    routes deliberately do not infer entire H55/H62 trees from the gate.
    """
    repo = graph.repo
    audited_blobs = {'scripts/coord-tools/gate.sh': 'd60977c0abccb00ccaf1d5a4b777bee9fde34b98', 'scripts/ci/checks-fast.sh': '71ae3185f23f860a4ff907bc53815991e6bc8719', 'scripts/check-trust.sh': '7c93af4335a60c0def576b35d78f1d07a84cfca4', 'scripts/check-trust.mjs': '9a4e8eb53b3a1fb68d7ef8ac8c439600475b7e2d', 'scripts/check-testsuite.sh': '312daf403db3c45a7c26a0d3704febd0099ea2a9', 'scripts/h62/item1/p16-generator/check.py': '1222082617c3db1ba6df27c083ae8ebd71f3d86c', 'scripts/h62/item1/p16-generator/generate.py': 'c79d2fc8a61162f192e5e549f272ee1745c4c3d3', 'tests/h28-sol/non-vacuity/kernel.py': '7190d611d05931e9aebe509685fbc16fbc6a686d'}
    def audited(path):
        return path in repo.tree and repo.tree[path][2] == audited_blobs.get(path)
    routes = [
        ('scripts/coord-tools/gate.sh', 'scripts/ci/checks-fast.sh', r'^\s*run_gate checks-fast bash scripts/ci/checks-fast[.]sh$', 'gate all modes invokes fast checks'),
        ('scripts/coord-tools/gate.sh', 'scripts/check-testsuite.sh', r'^\s*run_gate testsuite bash scripts/check-testsuite[.]sh$', 'gate full invokes TestSuite'),
        ('scripts/coord-tools/gate.sh', 'scripts/check-corpus.sh', r'^\s*run_gate corpus bash scripts/check-corpus[.]sh$', 'gate full invokes corpus'),
        ('scripts/coord-tools/gate.sh', 'scripts/h62/item1/p16-generator/check.py', r'^\s*run_gate p16-generated python3 -B scripts/h62/item1/p16-generator/check[.]py$', 'gate checkpoint/full invokes P16 integrity check'),
        ('scripts/ci/checks-fast.sh', 'tests/h62/item5/statement-graph/h112-tooling.test.mjs', r'^axiom-pin-tests\t node --test scripts/check-axiom-pins[.]test[.]mjs tests/h62/item5/statement-graph/h112-tooling[.]test[.]mjs$', 'checks-fast command table, Node test runner'),
        ('scripts/ci/checks-fast.sh', 'tests/h62/item5/statement-graph/test_w0_tooling.py', r'^w0-tooling\t python3 -B tests/h62/item5/statement-graph/test_w0_tooling[.]py -v$', 'checks-fast command table, Python test runner'),
        ('scripts/ci/checks-fast.sh', 'tests/h55/module-times/test_slow_examples.py', r'^slow-partition\t python3 -B tests/h55/module-times/test_slow_examples[.]py$', 'checks-fast command table, Python test runner'),
        ('scripts/ci/checks-fast.sh', 'scripts/check-trust.sh', r'^trust\t bash scripts/check-trust[.]sh$', 'checks-fast command table, trust check'),
        ('scripts/check-trust.sh', 'scripts/check-trust.mjs', r'.*node scripts/check-trust[.]mjs.*', 'trust shell invokes Node audit'),
        ('scripts/check-trust.mjs', 'tests/trust-inventory.json', r'.*const inventory = JSON[.]parse\(readFileSync\(resolve\(root, \'tests/trust-inventory[.]json\'\), \'utf8\'\)\);', 'Node readFileSync consumes trust inventory'),
        ('scripts/check-testsuite.sh', 'tests/solc/TestSuite.ast.json', r'.*const fixture = JSON[.]parse\(readFileSync\("tests/solc/TestSuite[.]ast[.]json", "utf8"\)\);', 'TestSuite reads AST'),
        ('scripts/check-testsuite.sh', 'tests/solkey/expected.tsv', r'.*const rows = tsvRows\("tests/solkey/expected[.]tsv"\);', 'TestSuite reads expected rows'),
    ]
    for source, target, pattern, operation in routes:
        if not audited(source) or source not in repo.texts or target not in repo.tree: continue
        for n, line in enumerate(repo.texts[source].splitlines(), 1):
            # Whitespace after the literal tab in the table is optional.
            if re.fullmatch(pattern.replace('\\t ', '\\t'), line):
                graph.edge(source, target, n, operation, kind='executes' if ('invokes' in operation or 'command table' in operation) else 'consumes',
                           validated_for='scripts/coord-tools/gate.sh')
    p16 = 'scripts/h62/item1/p16-generator/'
    source = p16 + 'check.py'
    text = repo.texts.get(source, '')
    if (audited(source) and 'for label, script, arguments in checks:' in text and
        'str(HERE / script), *arguments]' in text and 'cwd=ROOT' in text):
        for n, line in enumerate(text.splitlines(), 1):
            for name in ('generate.py', 'census.py'):
                if re.search(r'\("[^"\n]+", "' + re.escape(name) + r'", \[', line):
                    graph.edge(source, p16 + name, n, 'P16 subprocess dispatch; cwd=repository root', kind='executes', validated_for='scripts/coord-tools/gate.sh')
    generator = p16 + 'generate.py'
    text = repo.texts.get(generator, '')
    anchor = 'inventory = json.loads((HERE / "baseline-inventory.json").read_bytes().decode("utf-8"))'
    if audited(generator) and anchor in text:
        line = text[:text.index(anchor)].count('\n') + 1
        graph.edge(generator, p16 + 'baseline-inventory.json', line, 'generator reads fragment manifest', validated_for='scripts/coord-tools/gate.sh')
        if 'path = HERE / kind / name' in text and 'path.read_bytes()' in text:
            manifest = json.loads(repo.texts[p16 + 'baseline-inventory.json'])
            for kind in ('imports', 'body'):
                for name in manifest[kind]:
                    graph.edge(generator, p16 + kind + '/' + name,
                               text[:text.index('path.read_bytes()')].count('\n') + 1,
                               'generator reads each manifest-named fragment; kind=' + kind,
                               validated_for='scripts/coord-tools/gate.sh')
    kernel = 'tests/h28-sol/non-vacuity/kernel.py'
    text = repo.texts.get(kernel, '')
    expression = "(SOURCE/'Solidity/Assurance/NonVacuityH28').glob('*.lean')"
    if audited(kernel) and "SOURCE=HERE/'lean'" in text and expression in text and 'str(file)]' in text:
        line = text[:text.index(expression)].count('\n') + 1
        prefix = posixpath.dirname(kernel) + '/lean/Solidity/Assurance/NonVacuityH28/'
        for p in repo.paths:
            if p.startswith(prefix) and '/' not in p[len(prefix):] and p.endswith('.lean'):
                graph.edge(kernel, p, line, 'kernel --all enumerates source glob, visits and invokes lean -j1',
                           kind='executes', validated_for=kernel)
                for lineno, source in enumerate(lean_code(repo.texts[p]).splitlines(), 1):
                    match = re.match(r'^\s*import\s+(.+)$', source)
                    if not match: continue
                    for module in match[1].split():
                        private = 'Solidity.Assurance.NonVacuityH28.'
                        target = prefix + module[len(private):] + '.lean' if module.startswith(private) else module.replace('.', '/') + '.lean'
                        graph.edge(p, target, lineno, 'private-kernel Lean import resolution',
                                   kind='executes', validated_for=kernel)


def entrypoint_lines(source):
    """Actual top-level control/call statements; definitions alone are not roots."""
    tree = ast.parse(source)
    return {node.lineno for node in tree.body if isinstance(node, (ast.If, ast.For, ast.While, ast.With, ast.Try, ast.Assert))
            or isinstance(node, ast.Expr) and isinstance(node.value, ast.Call)}


def validated_routes(graph, catalog):
    """Reviewed validation definitions; raw run receipts live outside the branch.

    A passing-validation definition is bound to an exact input revision, command and source blob.
    Identical demonstrated committed runner sources may remain source-only roots
    at another revision, with explicit unavailable validation and no edge credit.
    Check/write do not execute it. Changes to the measured revision invalidate
    it until deliberate validation updates the definition. Definitions are part
    of the classifier, not evidence supplied by the inventory under test.
    """
    repo = graph.repo
    if not isinstance(catalog, dict) or set(catalog) != {'schema_version', 'standalone', 'generators', 'reads', 'orphans'} or catalog['schema_version'] != 1:
        raise ValueError('invalid validation definition schema')
    current_runner_paths = {e.get('path') for e in catalog['standalone'] if e.get('input_revision') == repo.ref}
    # Historical source-only eligibility needs a real commit and the exact
    # recorded source object, not merely a matching current filename/blob.
    historical_specs = {}
    historical_revisions = set()
    for entry in catalog['standalone']:
        p = entry.get('path')
        if (entry.get('input_revision') == repo.ref or entry.get('kind') not in ('unittest', 'node-test', 'runnable-entrypoint')
                or p in current_runner_paths or p not in repo.tree or repo.tree[p][2] != entry.get('source_blob')): continue
        revision = entry.get('input_revision')
        if not hex_pin(revision, 40): raise ValueError('historical runner demonstration requires full commit revision')
        historical_revisions.add(revision)
        historical_specs[revision + ':' + p] = entry['source_blob']
    requests = sorted(historical_revisions) + sorted(historical_specs)
    if requests:
        raw = git(repo.root, 'cat-file', '--batch-check', '-Z', data=b''.join(v.encode('utf-8', 'surrogateescape') + b'\0' for v in requests))
        lines = raw.rstrip(b'\0').split(b'\0')
        if len(lines) != len(requests): raise ValueError('historical runner object batch mismatch')
        for request, line in zip(requests, lines):
            fields = line.split()
            expected_oid = request if request in historical_revisions else historical_specs[request]
            expected_type = b'commit' if request in historical_revisions else b'blob'
            if len(fields) != 3 or fields[0].decode() != expected_oid or fields[1] != expected_type:
                raise ValueError('unverifiable historical runner demonstration: ' + request)
    for entry in catalog['standalone']:
        required = {'path', 'input_revision', 'source_blob', 'command', 'kind'}
        if entry.get('kind') == 'manual-reproducer': required.add('documentation')
        if entry.get('kind') == 'runnable-entrypoint': required.update(('entry_line', 'purpose', 'input_scope', 'other_reads'))
        if set(entry) != required:
            raise ValueError('invalid standalone definition')
        p = entry['path']
        historical_runner = entry['input_revision'] != repo.ref
        if historical_runner and (entry['kind'] not in ('unittest', 'node-test', 'runnable-entrypoint')
                or p in current_runner_paths or p not in repo.tree or repo.tree[p][2] != entry['source_blob']):
            continue
        if p not in repo.tree or repo.tree[p][2] != entry['source_blob']:
            raise ValueError('standalone definition source mismatch: ' + p)
        command = entry['command']
        if entry['kind'] != 'manual-reproducer' and command not in (['python3', '-B', p], ['node', '--test', p]):
            raise ValueError('unsupported standalone invocation: ' + p)
        if entry['kind'] not in ('unittest', 'node-test', 'manual-reproducer', 'runnable-entrypoint'):
            raise ValueError('unsupported standalone kind')
        if entry['kind'] == 'unittest':
            tree = ast.parse(repo.texts[p])
            if command[0] != 'python3' or not any(isinstance(n, ast.Call) and ast.unparse(n.func) == 'unittest.main' for n in ast.walk(tree)):
                raise ValueError('not a unittest entry point: ' + p)
        elif entry['kind'] == 'node-test':
            if command[0] != 'node' or not p.endswith(('.test.mjs', '.test.js', '.test.cjs')):
                raise ValueError('not a Node test entry point: ' + p)
        elif entry['kind'] == 'runnable-entrypoint':
            if command != ['python3', '-B', p] or type(entry['entry_line']) is not int or entry['entry_line'] not in entrypoint_lines(repo.bytes(p)):
                raise ValueError('unsupported default runnable entry point')
            if not isinstance(entry['purpose'], str) or not entry['purpose'].strip(): raise ValueError('runnable entry point lacks purpose')
            if entry['other_reads'] not in ('unresolved', 'secondary'): raise ValueError('invalid other-read eligibility')
            scopes = entry['input_scope']
            if not isinstance(scopes, list) or not all(isinstance(scope, str) and scope not in SCOPE and
                    (historical_runner or scope in repo.tree or scope.endswith('/') and any(path.startswith(scope) for path in repo.tree)) for scope in scopes):
                raise ValueError('invalid fixture-specific data scope')
        else:
            if not isinstance(command, list) or not command or not all(isinstance(a, str) for a in command):
                raise ValueError('invalid manual reproducer command')
            prefixes = (['node', p], ['python3', '-B', p], ['bash', p])
            if not any(command[:len(prefix)] == prefix for prefix in prefixes):
                raise ValueError('unsupported manual reproducer invocation')
            doc = entry['documentation']
            if not isinstance(doc, dict) or set(doc) != {'path', 'blob', 'line', 'invocation', 'normalization'}:
                raise ValueError('invalid manual reproducer documentation')
            source = doc['path']; line = doc['line']
            if source not in repo.texts or repo.tree[source][2] != doc['blob'] or not isinstance(line, int) or not 1 <= line <= len(repo.texts[source].splitlines()):
                raise ValueError('manual reproducer documentation mismatch')
            fragments = re.findall(r'`([^`]+)`', repo.texts[source].splitlines()[line - 1])
            if not isinstance(doc['invocation'], str) or doc['invocation'] not in fragments:
                raise ValueError('manual reproducer lacks its exact documented invocation')
            if doc['normalization'] == 'verbatim':
                matched = shlex.split(doc['invocation']) == command
            elif doc['normalization'] == 'node-basename-no-arguments':
                # A README naming only `check.mjs` documents its default check,
                # never an invented --help/--dry-run or other argument mode.
                matched = (doc['invocation'] == posixpath.basename(p) and command == ['node', p]
                           and p.endswith(('.mjs', '.js', '.cjs')))
            else: matched = False
            if not matched: raise ValueError('manual reproducer arguments differ from documentation')
        if historical_runner:
            # H490 / X1-RUNNER-ROOT: the demonstrated committed runner source
            # is a root independently of current passing-validation credit.
            # It cannot propagate any fixture/child edge, even a shared edge.
            identity = 'committed:' + p
            graph.root(p, 'committed standalone runner', shlex.join(command), p,
                       entry.get('entry_line', 1), root_id=identity)
            graph.roots[identity].update({'runner_kind': entry['kind'], 'source_blob': entry['source_blob'],
                'source_only': True, 'source_demonstration_revision': entry['input_revision'],
                'validation_at_measured_revision': {'status': 'unavailable', 'command': command,
                    'reason': 'Not executed at measured revision; source role and command established independently.'}})
            continue
        graph.root(p, 'validated standalone runner', shlex.join(command), p, entry.get('entry_line', 1), root_id='validated:' + p)
        graph.roots['validated:' + p].update({'runner_kind': entry['kind'], 'source_blob': entry['source_blob']})
        if entry['kind'] == 'runnable-entrypoint':
            graph.roots['validated:' + p].update({'purpose': entry['purpose'], 'data_use_scope': entry['input_scope'], 'other_reads': entry['other_reads']})
        if entry['kind'] == 'manual-reproducer': graph.roots['validated:' + p]['documentation'] = entry['documentation']
    for route in catalog['reads']:
        if set(route) != {'runner', 'input_revision', 'frames', 'target', 'target_blob', 'operation'}:
            raise ValueError('invalid validated read route')
        if route['input_revision'] != repo.ref: continue
        original = route['runner']
        if original not in graph.roots or graph.roots[original]['kind'] != 'validated standalone runner':
            raise ValueError('validated read has no validated runner')
        target = route['target']
        if target not in repo.tree or repo.tree[target][2] != route['target_blob']:
            raise ValueError('validated read target mismatch')
        if route['operation'] != 'validated Python read of measured bytes':
            raise ValueError('unsupported validated read operation')
        frames = route['frames']
        if not isinstance(frames, list) or not frames or frames[0].get('path') != graph.roots[original]['path']:
            raise ValueError('validated read route does not start at its runner')
        for frame in frames:
            if set(frame) != {'path', 'blob', 'line'}: raise ValueError('invalid read stack frame')
            source = frame['path']
            if source not in repo.tree or repo.tree[source][2] != frame['blob']:
                raise ValueError('validated read source mismatch')
            if not isinstance(frame['line'], int) or not 1 <= frame['line'] <= len(repo.texts.get(source, '').splitlines()):
                raise ValueError('validated read location mismatch')
        if any(excluded(f['path']) for f in frames) or excluded(target): continue
        scopes = graph.roots[original].get('data_use_scope')
        eligible = scopes is None or any(target == scope or scope.endswith('/') and target.startswith(scope) for scope in scopes)
        if not eligible and graph.roots[original].get('other_reads') == 'unresolved':
            graph.uncertain_reads[target].add(original)
        if not eligible and all(frame['path'] == graph.roots[original]['path'] for frame in frames): continue
        identity = original + ':read:' + hashlib.sha256(canonical(route)).hexdigest()
        graph.roots[identity] = {**graph.roots[original], 'derived_from': original, 'observed_target': target}
        # Preserve the complete ordered stack, including repeated source paths.
        # Turning it into filename nodes could shortcut a callback or recursion.
        chain = {'root': identity, 'entry': graph.roots[identity], 'edges': []}
        for caller, callee in zip(frames, frames[1:]):
            chain = {**chain, 'edges': chain['edges'] + [{
                'source': caller['path'], 'target': callee['path'],
                'line': caller['line'], 'operation': 'validated Python call stack',
                'kind': 'executes', 'validated_for': identity}]}
            graph.observed.append((callee['path'], chain))
        reader = frames[-1]
        chain = {**chain, 'edges': chain['edges'] + [{
            'source': reader['path'], 'target': target, 'line': reader['line'],
            'operation': route['operation'], 'kind': 'consumes', 'validated_for': identity}]}
        if eligible: graph.observed.append((target, chain))
    generated = {}
    for entry in catalog['generators']:
        required = {'path', 'input_revision', 'output_blob', 'generator', 'generator_blob',
                    'command', 'inputs', 'tools', 'comparison'}
        if set(entry) not in (required, required | {'consumption_review'}): raise ValueError('invalid generator definition')
        if entry['input_revision'] != repo.ref: continue
        p, generator = entry['path'], entry['generator']
        if entry['comparison'] != 'exact bytes': raise ValueError('unsupported generator comparison')
        if p not in repo.tree or repo.tree[p][2] != entry['output_blob']:
            raise ValueError('generated output mismatch: ' + p)
        if generator not in repo.tree or repo.tree[generator][2] != entry['generator_blob']:
            raise ValueError('generator source mismatch: ' + generator)
        if not isinstance(entry['inputs'], dict) or not entry['inputs'] or not entry['tools']:
            raise ValueError('generator lacks inputs/tools')
        for source, oid in entry['inputs'].items():
            if source not in repo.tree or repo.tree[source][2] != oid:
                raise ValueError('generator input mismatch: ' + source)
        command = entry['command']
        if not isinstance(command, list) or not command or not all(isinstance(a, str) for a in command):
            raise ValueError('unsupported generator invocation')
        prefix = ['python3', '-B', generator] if command[0] == 'python3' else [command[0], generator]
        if command[0] not in ('python3', 'node', 'bash') or command[:len(prefix)] != prefix:
            raise ValueError('unsupported generator invocation')
        if p in generated: raise ValueError('duplicate generator output')
        generated[p] = entry
    return generated


def command_receipt_rows(value):
    rows = value if isinstance(value, list) else value.get('commands', []) if isinstance(value, dict) else []
    if not isinstance(rows, list) or not rows: return []
    def valid(row):
        return (isinstance(row, dict) and {'command', 'exitCode', 'elapsedSeconds'} <= set(row)
                and isinstance(row['command'], list) and bool(row['command'])
                and all(isinstance(argument, str) for argument in row['command'])
                and type(row['exitCode']) is int and nonnegative_number(row['elapsedSeconds']))
    return rows if all(valid(row) for row in rows) else []


def nonnegative_number(value):
    return (type(value) is int and value >= 0
            or type(value) is float and math.isfinite(value) and value >= 0)


def hex_pin(value, length=64):
    return isinstance(value, str) and re.fullmatch('[0-9a-f]{' + str(length) + '}', value) is not None


def historical_json_role(value):
    """Reviewed observation schemas; expected vectors and policy maps do not match.

    These establish an archived role, never the truth of an outcome or access
    to a named external log/review. Keep and unresolved-read precedence remain
    in inventory(). Producer schemas: solkey-migration.mjs summarize(),
    evm-reference/generated.mjs report construction; explicit review/gate and
    compiler/EVM receipts include measured observations and digest bindings.
    """
    if not isinstance(value, dict): return None
    def counters(x):
        return isinstance(x, dict) and bool(x) and all(isinstance(k, str) and k and type(v) is int and v >= 0 for k, v in x.items())
    keys = set(value)
    if keys == {'commit', 'mode', 'completedSources', 'totalSources', 'results', 'errors', 'suites'}:
        if (hex_pin(value['commit'], 40) and value['mode'] in ('proof', 'parse', 'audit-with-focused-retries')
                and all(type(value[k]) is int and value[k] >= 0 for k in ('completedSources', 'totalSources', 'errors'))
                and value['completedSources'] <= value['totalSources'] and counters(value['results'])
                and isinstance(value['suites'], dict) and value['suites'] and all(counters(v) for v in value['suites'].values())
                and {k: sum(row.get(k, 0) for row in value['suites'].values()) for k in set().union(*value['suites'].values())} == value['results']):
            return 'Historical migration summary: pinned source commit, completed/total counts and measured result counters by suite (solkey-migration.mjs summarize).'
    reviews = value.get('reviews')
    if isinstance(reviews, list) and reviews and all(isinstance(r, dict)
            and {'area', 'role', 'agent', 'verdict', 'read_only', 'used_lean_server', 'artifact', 'sha256', 'reviewed_inputs_sha256', 'scope'} <= set(r)
            and r['role'] in ('finder', 'skeptic') and all(isinstance(r[k], str) and r[k] for k in ('area', 'agent', 'verdict', 'artifact', 'scope'))
            and type(r['read_only']) is bool and type(r['used_lean_server']) is bool
            and hex_pin(r['sha256']) and hex_pin(r['reviewed_inputs_sha256']) for r in reviews):
        return 'Historical independent review receipts: reviewer roles/verdicts, flags, artifact digests and reviewed-input digests; external artifacts not verified.'
    observations = value.get('observations')
    if (value.get('version') == 1 and type(value.get('version')) is int and hex_pin(value.get('compilerSha256'))
            and hex_pin(value.get('archiveSha256')) and isinstance(value.get('compiler'), str)
            and isinstance(value.get('scope'), str) and 'evidence' in value['scope'].lower()
            and isinstance(observations, list) and observations and all(isinstance(r, dict)
                and {'path', 'sourceSha256', 'pipeline', 'settings', 'signature', 'args', 'calldata', 'failure', 'expected', 'actual'} <= set(r)
                and hex_pin(r['sourceSha256']) and type(r['failure']) is bool and isinstance(r['settings'], dict)
                and isinstance(r['args'], list) and all(isinstance(r[k], str) for k in ('path', 'pipeline', 'signature', 'calldata', 'expected', 'actual'))
                and re.fullmatch('0x[0-9a-fA-F]*', r['calldata']) for r in observations)):
        return 'Historical compiler/EVM observations: compiler/archive/source digests and concrete calldata, failure, expected and actual results.'
    gates = value.get('gates')
    if hex_pin(value.get('upstream'), 40) and hex_pin(value.get('merge'), 40) and isinstance(gates, dict) and gates:
        def measured(r):
            return (isinstance(r, dict) and isinstance(r.get('command'), list) and bool(r['command'])
                    and all(isinstance(a, str) for a in r['command']) and type(r.get('exit')) is int
                    and nonnegative_number(r.get('elapsed_seconds')))
        if all(measured(r) and hex_pin(r.get('git_head'), 40) and hex_pin(r.get('log_sha256'))
                and measured(r.get('rusage')) and all(nonnegative_number(r['rusage'].get(k)) for k in
                    ('children_user_seconds', 'children_system_seconds', 'children_max_rss_kib')) for r in gates.values()):
            return 'Historical integration gate receipts: upstream/merge pins and commit-bound argv, exits, durations, resources and log digests; named logs not verified.'
    return None


def reviewed_receipt_rows(value):
    """Measured rows from three reviewed historical envelope schemas.

    Not arbitrary recursive keys: native/probe resource envelopes contain
    commands[]; pinned continuation reports contain checks[]. A commands dict
    is a recipe table, never measured output. Missing commands get no credit.
    No success, active-consumer or external-artifact claim follows from a row.
    """
    if not isinstance(value, dict): return []
    recorded = value.get('recordedAt')
    if not isinstance(recorded, str) or not re.fullmatch(r'\d{4}-\d{2}-\d{2}T[0-9:.+\-]+Z?', recorded): return []
    def argv(v): return isinstance(v, list) and bool(v) and all(isinstance(x, str) for x in v)
    def measured(row, resource, command_type):
        return (isinstance(row, dict) and command_type(row.get('command'))
                and type(row.get('exitCode')) is int and nonnegative_number(row.get('elapsedSeconds'))
                and type(row.get(resource)) is int and row[resource] >= 0
                and isinstance(row.get('log'), str) and bool(row['log']))
    rows = value.get('commands')
    native = (isinstance(value.get('historicalFiles'), list) and bool(value['historicalFiles'])
              and all(isinstance(r, dict) and isinstance(r.get('path'), str) and r['path']
                      and hex_pin(r.get('sha256')) and type(r.get('byteIdenticalToStartingCommit')) is bool
                      for r in value['historicalFiles']) and type(value.get('nativeValidationComplete')) is bool
              and all(isinstance(value.get(k), str) for k in ('remainingNativeCapability', 'historicalGeneratorNote')))
    probes = all(isinstance(value.get(k), str) for k in ('nativeValidation', 'originalCoreAndCorpus', 'newTheoremAxiomAudit'))
    if (isinstance(rows, list) and rows and (native or probes)
            and nonnegative_number(value.get('elapsedSeconds')) and type(value.get('maxWait4JobRssKiB')) is int
            and value['maxWait4JobRssKiB'] >= 0 and isinstance(value.get('resourceInterpretation'), str)
            and all(measured(r, 'wait4MaxRssKiB', argv) and hex_pin(r.get('uncompressedLogSha256')) for r in rows)):
        return [(f'/commands/{i}', r) for i, r in enumerate(rows)]
    if (type(value.get('version')) is not int or value['version'] != 1
            or not isinstance(value.get('runtime'), dict) or not isinstance(value.get('branch'), str)
            or not hex_pin(value.get('implementationCommit'), 40)):
        return []
    rows = value.get('checks')
    if not isinstance(rows, list) or not rows: return []
    continuation = hex_pin(value.get('evidenceBaseCommit'), 40) and isinstance(value.get('historicalIntegrity'), dict)
    validation = hex_pin(value.get('startingCommit'), 40) and isinstance(value.get('scope'), str)
    if continuation:
        if not all(measured(r, 'peakCgroupBytes', lambda v: isinstance(v, str) and bool(v))
                and isinstance(r.get('runner'), str) and isinstance(r.get('status'), str)
                and hex_pin(r.get('sha256')) for r in rows): return []
        return [(f'/checks/{i}', r) for i, r in enumerate(rows)]
    if validation:
        return [(f'/checks/{i}', r) for i, r in enumerate(rows)
                if measured(r, 'prototypePeakGroupRssBytes', argv)
                and isinstance(r.get('status'), str) and hex_pin(r.get('sha256'))]
    return []


def evidence_role(data):
    """Content signatures, never extension or directory alone. Keep wins first."""
    if data.startswith(b'\x1f\x8b'):
        try:
            with gzip.GzipFile(fileobj=io.BytesIO(data)) as stream: data = stream.read(8_000_001)
        except (OSError, EOFError, zlib.error): return None
    if len(data) > 8_000_000: return None
    try: text = data.decode('utf-8')
    except UnicodeDecodeError: return None
    try: value = json.loads(text)
    except (ValueError, RecursionError): value = None
    if isinstance(value, list) and command_receipt_rows(value):
        return 'Historical sequential command receipts: argv, exit codes and elapsed measurements.'
    if isinstance(value, dict):
        keys = set(value)
        if reviewed_receipt_rows(value):
            return 'Historical resource/validation command receipts: reviewed dated envelope, explicit commands, exit/timing/resource observations and output digests; no current validation credit.'
        reviewed = historical_json_role(value)
        if reviewed: return reviewed
        gate = value.get('combinedGate')
        if ({'recordedOn', 'startingCommit', 'implementationCommit', 'branch', 'runtime', 'resourceBounds'} <= keys
                and isinstance(value['recordedOn'], str) and re.fullmatch(r'\d{4}-\d{2}-\d{2}', value['recordedOn'])
                and hex_pin(value['startingCommit'], 40) and hex_pin(value['implementationCommit'], 40)
                and isinstance(value['branch'], str) and value['branch'] and isinstance(value['runtime'], dict)
                and isinstance(value['resourceBounds'], dict) and isinstance(gate, dict)
                and isinstance(gate.get('command'), str) and gate['command'] and type(gate.get('exitCode')) is int
                and nonnegative_number(gate.get('elapsedSeconds')) and isinstance(gate.get('log'), str)
                and hex_pin(gate.get('uncompressedLogSha256'))):
            return 'Historical validation record: recordedOn, startingCommit and implementationCommit provenance fields.'
        if ({'command', 'exit', 'elapsed_seconds', 'resource_stop', 'peak_group_rss_bytes'} <= keys
                and isinstance(value['command'], list) and value['command'] and all(isinstance(a, str) for a in value['command'])
                and type(value['exit']) is int and nonnegative_number(value['elapsed_seconds'])
                and type(value['resource_stop']) is bool and type(value['peak_group_rss_bytes']) is int and value['peak_group_rss_bytes'] >= 0):
            return 'Command receipt with command, exit and elapsed_seconds fields; no demonstrated active consumer.'
        if (isinstance(value.get('recordedAt', value.get('recordedOn')), str)
                and hex_pin(value.get('startingCommit'), 40) and isinstance(value.get('commands'), list) and value['commands']):
            if all(isinstance(r, dict) and {'command', 'exitCode', 'elapsedSeconds'} <= set(r)
                   and isinstance(r['command'], (list, str)) and bool(r['command']) and type(r['exitCode']) is int
                   and nonnegative_number(r['elapsedSeconds']) for r in value['commands']):
                return 'Historical validation receipt: recorded time, starting commit and command/exit/elapsed measurements.'
        metadata = value.get('metadata')
        if (isinstance(metadata, dict) and hex_pin(metadata.get('commit'), 40)
                and all(hex_pin(metadata.get(k)) for k in ('compilerSha256', 'runnerSha256', 'modelSha256'))):
            results = value.get('results')
            if isinstance(results, list) and results and all(isinstance(r, dict) and isinstance(r.get('path'), str) and r['path']
                    and isinstance(r.get('status'), str) and r['status'] for r in results):
                return 'Historical upstream execution results with pinned commit/compiler/runner/model metadata and per-path statuses.'
        if {'commit', 'completed', 'errors', 'mode', 'results', 'sources', 'version'} <= keys:
            if (hex_pin(value['commit'], 40) and type(value['version']) is int and value['version'] == 1
                    and value['mode'] in ('proof', 'listing', 'audit-with-focused-retries')
                    and all(isinstance(value[k], list) for k in ('completed', 'errors', 'results', 'sources'))
                    and value['sources'] and value['results']
                    and all(isinstance(p, str) and p for p in value['sources'] + value['completed'])
                    and set(value['completed']) <= set(value['sources'])
                    and all(isinstance(r, dict) and isinstance(r.get('status'), str) and r['status']
                            and isinstance(r.get('source'), str) and r['source'] for r in value['results'])):
                return 'Historical migration execution report: commit, mode, completed sources, errors and per-result statuses.'
        if ({'archiveSha256', 'runnerSha256', 'modelSha256', 'completedFixtureFiles', 'totalFixtureFiles', 'counts', 'complete'} <= keys
                and all(hex_pin(value[k]) for k in ('archiveSha256', 'runnerSha256', 'modelSha256'))
                and type(value['complete']) is bool and type(value['completedFixtureFiles']) is int
                and type(value['totalFixtureFiles']) is int and 0 <= value['completedFixtureFiles'] <= value['totalFixtureFiles']
                and value['totalFixtureFiles'] > 0 and isinstance(value['counts'], dict) and value['counts']
                and all(isinstance(k, str) and k and type(v) is int and v >= 0 for k, v in value['counts'].items())):
            return 'Historical upstream run summary: pinned archive/runner/model, completion counters and observed status counts.'
    # Require multiple nontrivial log markers; a source containing a string is not a log.
    lines = text.splitlines()
    matches = sum(bool(re.match(r'^(?:[✔✖⚠] \[\d+/\d+\]|(?:info|warning|error): [^ ]+\.lean:\d+:|PASS [a-z][\w-]* \d+s|H28_MODULE_PASS \{)', l)) for l in lines)
    first = next((line for line in lines if line.strip()), '')
    first_marker = bool(re.match(r'^(?:[✔✖⚠] \[\d+/\d+\]|(?:info|warning|error): [^ ]+\.lean:\d+:|PASS [a-z][\w-]* \d+s|H28_MODULE_PASS \{)', first))
    if matches >= 3 and ((first_marker and matches * 2 >= len(lines)) or re.fullmatch(r'\d+ core modules, \d+ reach the elaborator', first)):
        return 'Historical process output: repeated structured build/diagnostic/test result lines.'
    if first == 'TAP version 13' and re.search(r'^# tests \d+$', text, re.M) and re.search(r'^# pass \d+$', text, re.M) and re.search(r'^# fail \d+$', text, re.M):
        return 'Historical Node TAP process transcript with explicit test/pass/fail summary.'
    if re.fullmatch(r'[.sFxEux]+', first) and re.search(r'^Ran \d+ tests? in [0-9.]+s$', text, re.M) and re.search(r'^(?:OK(?: \(skipped=\d+\))?|FAILED \(.*\))$', text, re.M):
        return 'Historical unittest process transcript with timed test count and outcome.'
    diagnostics = sum(bool(re.match(r'^(?:missing|ambiguous): +[^ ]+ cites `', line)) for line in lines)
    if diagnostics >= 3 and diagnostics * 2 >= len(lines) and re.match(r'^(?:missing|ambiguous): ', first):
        return 'Historical documentation-path diagnostic transcript with repeated source/citation findings.'
    return None


def historical_outputs(repo):
    """Receipt-named logs, independently bound to their recorded content hash.

    A filename or a mention in prose is insufficient. Only a structured command
    receipt with exit/timing fields and a matching output digest establishes a
    historical-output role. This does not make its command a live entry point.
    """
    roles = {}
    for source in sorted(repo.texts):
        try: value = json.loads(repo.texts[source])
        except (ValueError, RecursionError): continue
        if not evidence_role(repo.bytes(source)): continue
        standard = command_receipt_rows(value)
        rows = [(f'/{i}' if isinstance(value, list) else f'/commands/{i}', row) for i, row in enumerate(standard)]
        rows += reviewed_receipt_rows(value)
        for pointer, row in rows:
            if not {'log'} <= set(row) or not isinstance(row['log'], str): continue
            digest = row.get('uncompressedLogSha256', row.get('sha256'))
            if not isinstance(digest, str) or not re.fullmatch('[0-9a-f]{64}', digest): continue
            # A basename is never a substitute for an external absolute path.
            if row['log'].startswith('/') or '\0' in row['log'] or '..' in row['log'].split('/'): continue
            # Historical receipts use both repository-relative and sibling names.
            direct = clean(row['log'])
            sibling = clean(posixpath.join(posixpath.dirname(source), row['log']))
            possibilities = {path for path in (direct, sibling) if path in repo.tree and repo.tree[path][1] == 'blob' and repo.tree[path][0] in ('100644', '100755')}
            if len(possibilities) != 1: continue  # ambiguous cwd is not provenance
            target = possibilities.pop()
            data = repo.bytes(target)
            if 'uncompressedLogSha256' in row and data.startswith(b'\x1f\x8b'):
                try:
                    with gzip.GzipFile(fileobj=io.BytesIO(data)) as stream: data = stream.read(8_000_001)
                except (OSError, EOFError, zlib.error): continue
            if len(data) > 8_000_000 or hashlib.sha256(data).hexdigest() != digest: continue
            encoding = 'uncompressed' if 'uncompressedLogSha256' in row else 'stored-byte'
            roles[target] = f'Historical command output: {source} {pointer} names this log; recorded {encoding} SHA256 matches measured bytes.'
    return roles


def add_declared_test_runners(graph):
    """H490 source-only roots from explicit unittest declarations.

    Require an unshadowed unittest import, a real module-level TestCase with
    test methods, and a direct unittest.main call under the literal __main__
    guard. Text examples, dead guards, plain failing scripts and helpers are
    not roots. This demonstrates the committed runner ROLE, never a current
    pass or any fixture/child use. No code is executed.
    """
    repo = graph.repo
    existing = {v['path'] for v in graph.roots.values()}
    for path, text in sorted(repo.texts.items()):
        if not path.endswith('.py') or path in existing or repo.tree[path][0] not in ('100644', '100755'): continue
        try: tree = ast.parse(text)
        except (SyntaxError, ValueError, RecursionError): continue
        modules = set(); cases = set(); mains = set()
        for node in tree.body:
            if isinstance(node, ast.Import):
                modules.update(a.asname or 'unittest' for a in node.names
                               if a.name == 'unittest' or a.name.startswith('unittest.') and a.asname is None)
            elif isinstance(node, ast.ImportFrom) and node.module == 'unittest' and not node.level:
                cases.update(a.asname or a.name for a in node.names if a.name == 'TestCase')
                mains.update(a.asname or a.name for a in node.names if a.name == 'main')
        if not modules and not (cases and mains): continue
        bindings = modules | cases | mains | {'__name__'}
        shadowed = any(isinstance(n, ast.Name) and isinstance(n.ctx, (ast.Store, ast.Del)) and n.id in bindings
                       or isinstance(n, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)) and n.name in bindings
                       or isinstance(n, ast.Attribute) and isinstance(n.ctx, (ast.Store, ast.Del))
                          and isinstance(n.value, ast.Name) and n.value.id in modules and n.attr in ('main', 'TestCase')
                       for n in ast.walk(tree))
        for node in ast.walk(tree):
            if isinstance(node, ast.Import):
                for alias in node.names:
                    bound = alias.asname or alias.name.split('.')[0]
                    if bound == '__name__': shadowed = True
                    if bound in bindings and not (bound in modules and
                            (alias.name == 'unittest' or alias.name.startswith('unittest.') and alias.asname is None)):
                        shadowed = True
            elif isinstance(node, ast.ImportFrom):
                for alias in node.names:
                    bound = alias.asname or alias.name
                    if bound == '__name__': shadowed = True
                    if alias.name == '*': shadowed = True
                    if bound in bindings and not (node.module == 'unittest' and not node.level
                            and (alias.name == 'TestCase' and bound in cases or alias.name == 'main' and bound in mains)):
                        shadowed = True
        if modules & cases or modules & mains or cases & mains: shadowed = True
        if shadowed: continue
        def terminal(statement):
            if isinstance(statement, ast.Raise): return True
            if isinstance(statement, ast.Expr) and isinstance(statement.value, ast.Call):
                func = statement.value.func
                return (isinstance(func, ast.Name) and func.id in ('exit', 'quit')
                        or isinstance(func, ast.Attribute) and func.attr in ('exit', '_exit'))
            return False
        def testcase(base):
            return (isinstance(base, ast.Name) and base.id in cases
                    or isinstance(base, ast.Attribute) and base.attr == 'TestCase'
                    and isinstance(base.value, ast.Name) and base.value.id in modules)
        classes = [n for n in tree.body if isinstance(n, ast.ClassDef) and any(testcase(b) for b in n.bases)
                   and any(isinstance(m, (ast.FunctionDef, ast.AsyncFunctionDef)) and m.name.startswith('test_') for m in n.body)]
        if not classes: continue
        calls = []
        for index, node in enumerate(tree.body):
            if not isinstance(node, ast.If) or not isinstance(node.test, ast.Compare): continue
            test = node.test
            if len(test.ops) != 1 or not isinstance(test.ops[0], ast.Eq) or len(test.comparators) != 1: continue
            pair = (test.left, test.comparators[0])
            if not (any(isinstance(n, ast.Name) and n.id == '__name__' for n in pair)
                    and any(isinstance(n, ast.Constant) and n.value == '__main__' for n in pair)): continue
            if any(terminal(n) for n in tree.body[:index]): continue
            for position, statement in enumerate(node.body):
                if not isinstance(statement, ast.Expr) or not isinstance(statement.value, ast.Call): continue
                call = statement.value; func = call.func
                if not (isinstance(func, ast.Name) and func.id in mains or isinstance(func, ast.Attribute)
                        and func.attr == 'main' and isinstance(func.value, ast.Name) and func.value.id in modules): continue
                if any(terminal(n) for n in node.body[:position]): continue
                calls.append(call)
        if not calls: continue
        try: compile(text, path, 'exec', dont_inherit=True)
        except (SyntaxError, ValueError, RecursionError, OverflowError): continue
        identity = 'committed:' + path
        graph.root(path, 'committed standalone test runner', shlex.join(['python3', '-B', path]), path,
                   calls[0].lineno, root_id=identity)
        graph.roots[identity].update({'source_only': True, 'source_blob': repo.tree[path][2],
            'role_provenance': {'kind': 'unittest declaration and explicit main entry', 'revision': repo.ref,
                'class_lines': [c.lineno for c in classes], 'main_line': calls[0].lineno},
            'validation_at_measured_revision': {'status': 'unavailable', 'command': ['python3', '-B', path],
                'reason': 'Committed runner role audited from syntax; command not executed by inventory.'}})


def reviewed_generated_consumption(entry, graph, candidate_sources):
    """A reproduction receipt cannot establish absence of active consumers.

    This optional, independently reviewed negative analysis is classifier input,
    bound to the exact revision, reviewed source objects and the entire current
    entry-point set. Missing/stale/incomplete reviews leave consumption open.
    It is never synthesized from a missing graph edge or a successful generator.
    """
    review = entry.get('consumption_review')
    if review is None: return False
    required = {'verdict', 'input_revision', 'search_coverage', 'dynamic_analysis',
                'reviewed_sources', 'entry_points_reviewed'}
    if not isinstance(review, dict) or set(review) != required:
        raise ValueError('invalid generated consumption review')
    if review['verdict'] != 'no-active-consumer-found' or review['input_revision'] != graph.repo.ref:
        raise ValueError('stale or unsupported generated consumption review')
    if not all(isinstance(review[k], str) and review[k].strip() for k in ('search_coverage', 'dynamic_analysis')):
        raise ValueError('generated consumption review lacks independent search/dynamic analysis')
    sources = review['reviewed_sources']
    if not isinstance(sources, dict) or not sources or entry['generator'] not in sources:
        raise ValueError('generated consumption review lacks source bindings')
    if any(p not in graph.repo.tree or graph.repo.tree[p][2] != oid for p, oid in sources.items()):
        raise ValueError('generated consumption review source mismatch')
    roots = {k: v for k, v in sorted(graph.roots.items()) if 'derived_from' not in v}
    if review['entry_points_reviewed'] != roots:
        raise ValueError('generated consumption review entry-point coverage mismatch')
    required_sources = set(candidate_sources)
    for root in roots.values():
        required_sources.update((root['path'], root['location'].rsplit(':', 1)[0]))
    return required_sources <= set(sources)


def inventory(repo, catalog=None):
    graph = Graph(repo)
    if catalog is None:
        definitions = Path(__file__).with_name('check-tests-used-routes.json')
        catalog = json.loads(definitions.read_bytes()) if definitions.exists() else {'schema_version': 1, 'standalone': [], 'generators': [], 'reads': [], 'orphans': []}
    add_roots(graph); reviewed_routes(graph); add_lean(graph)
    generated = validated_routes(graph, catalog)
    add_declared_test_runners(graph)
    ci_spec = importlib.util.spec_from_file_location('tests_used_ci', Path(__file__).with_name('check-tests-used-ci.py'))
    ci_rules = importlib.util.module_from_spec(ci_spec); ci_spec.loader.exec_module(ci_rules)
    ci_rules.add(graph)
    lake_spec = importlib.util.spec_from_file_location('tests_used_lake', Path(__file__).with_name('check-tests-used-lake.py'))
    lake_rules = importlib.util.module_from_spec(lake_spec); lake_spec.loader.exec_module(lake_rules)
    lake_rules.add(graph, lean_lex)
    chains = graph.chains()
    orphan_reviews = {}
    for entry in catalog['orphans']:
        if set(entry) != {'path', 'input_revision', 'blob', 'reason', 'dynamic_review'}:
            raise ValueError('invalid reviewed orphan definition')
        if entry['input_revision'] != repo.ref: continue
        p = entry['path']
        if p not in repo.tree or entry['blob'] != repo.tree[p][2] or p in orphan_reviews:
            raise ValueError('reviewed orphan object mismatch or duplicate')
        if not all(isinstance(entry[k], str) and entry[k].strip() for k in ('reason', 'dynamic_review')):
            raise ValueError('reviewed orphan lacks concrete negative/dynamic analysis')
        orphan_reviews[p] = entry
    pins = repo.pins()
    historical = historical_outputs(repo)
    # Search coverage is explicitly broader than the certified use graph. A
    # textual hit is negative-evidence context, not a consumer certification.
    names = collections.defaultdict(list)
    for p in repo.paths: names[posixpath.basename(p)].append(p)
    candidates = collections.defaultdict(list)
    candidate_sources = collections.defaultdict(set)  # eligibility is never display-capped
    # Single indexed scan rather than one repository scan per inventoried file.
    token_re = re.compile(r'[A-Za-z0-9_.+@/-]+')
    for source, text in sorted(repo.texts.items()):
        for n, line in enumerate(text.splitlines(), 1):
            for token in dict.fromkeys(token_re.findall(line)):
                key = token.rsplit('/', 1)[-1]
                for p in names.get(key, ()):
                    if source != p: candidate_sources[p].add(source)
                    if source != p and len(candidates[p]) < 8:
                        candidate = {'location': f'{source}:{n}', 'token': token if token in repo.tree else key}
                        if candidate not in candidates[p]: candidates[p].append(candidate)
    # Exact unusual-name/literal search supplements the ASCII discovery index.
    # It includes quoted escape spellings so newlines/Unicode do not look absent.
    unusual = collections.defaultdict(set)
    for path in repo.paths:
        base = posixpath.basename(path)
        if token_re.fullmatch(base): continue
        for name in (path, base):
            for spelling in (name, json.dumps(name, ensure_ascii=True)[1:-1], repr(name)[1:-1]):
                unusual[spelling].add(path)
    for source, text in sorted(repo.texts.items()):
        for spelling, paths in sorted(unusual.items()):
            at = text.find(spelling)
            if at < 0: continue
            line = text.count('\n', 0, at) + 1
            for path in sorted(paths):
                if source == path: continue
                candidate_sources[path].add(source)
                if len(candidates[path]) >= 8: continue
                candidate = {'location': f'{source}:{line}', 'token': path}
                if candidate not in candidates[path]: candidates[path].append(candidate)
    records = []
    for p in repo.paths:
        mode, kind, oid = repo.tree[p]
        recovery = pins.get(p)
        reason = None; classification = None; unresolved = []
        chain = chains.get(p)
        historical_role = historical.get(p) or (evidence_role(repo.bytes(p)) if kind == 'blob' and mode != '120000' else None)
        if chain:
            classification = 'keep'
            reason = (chain['entry']['kind'] + ' entry point: ' + chain['entry']['command'] if not chain['edges'] else
                      chain['edges'][-1]['operation'] + ' at ' + chain['edges'][-1]['source'] + ':' + str(chain['edges'][-1]['line']))
        elif p in generated:
            if reviewed_generated_consumption(generated[p], graph, candidate_sources[p]):
                classification = 'regenerable'
                reason = 'Exact reproduction is verified and an independent source-bound consumer/search review found no active consumer.'
            else:
                reason = 'Exact reproduction is verified, but consumption remains unresolved; a missing edge in this incomplete graph is not non-use.'
                unresolved.append('UNRESOLVED_GENERATED_CONSUMPTION: independent consumer/search review required')
        elif kind == 'blob' and mode != '120000':
            reason = historical_role
            if reason: classification = 'evidence'
        if not classification and p not in generated and p in orphan_reviews and not candidates[p]:
            classification = 'orphan'
            reason = orphan_reviews[p]['reason']
        if not classification:
            if reason is None: reason = 'No certified consumer or content-based historical role in the current model; further runner/dynamic-path analysis required.'
            unresolved.append('UNRESOLVED_USE: candidate search is not a certified use graph or proof of non-use')
            if p in orphan_reviews and candidates[p]: unresolved.append('UNSUPPORTED_ORPHAN_REVIEW: candidate matches remain unresolved')
        if p in graph.uncertain_reads and classification != 'keep':
            classification = None
            reason = 'A passing entry point read this object; fixture-specific versus secondary-scan eligibility needs review. Independent historical/generated properties are retained.'
            unresolved.append('UNRESOLVED_READ_ROLE: observed read eligibility is unreviewed; this is not established non-use')
        if recovery is None:
            unresolved.append(repo.pin_limitations.get(p, 'UNVERIFIABLE: ' + ('shallow history boundary prevents establishing last-touch provenance' if repo.shallow else 'no historical change introducing the measured object was recovered')))
        records.append({'path': p, 'class': classification, 'reason': reason,
                        'mode': mode, 'object_type': kind, 'blob': oid,
                        'recovery': recovery, 'runner_chain': chain, 'secondary': {**graph.properties.get(p, {}), **({'historical_role': historical_role} if historical_role else {}), **({'policy_scans': ['private-paths']} if p in graph.policy_targets else {}), **({'unreviewed_readers': sorted(graph.uncertain_reads[p])} if p in graph.uncertain_reads else {})},
                        'search_candidates': candidates[p], 'generator': generated.get(p),
                        'orphan_analysis': ({'review': orphan_reviews[p], 'search_matches': 0,
                                             'entry_points_reviewed': sorted(k for k, v in graph.roots.items() if 'derived_from' not in v)} if classification == 'orphan' else None),
                        'unresolved': unresolved})
    counts = {c: sum(r['class'] == c for r in records) for c in CLASSES}
    return {'schema_version': SCHEMA, 'goal_decl': None, 'measured_revision': repo.ref,
            'entry_points': {k: v for k, v in sorted(graph.roots.items()) if 'derived_from' not in v},
            'universe': list(SCOPE), 'policy_scans': graph.policy_scans, 'analysis_gaps': sorted(set(graph.notes)), 'totals': {**counts, 'paths': len(records),
                                              'unresolved': sum(bool(r['unresolved']) for r in records)},
            'search_coverage': {'inputs': 'All committed non-NUL blobs, excluding classifier and inventory outputs.',
                                'candidates': 'Basename token search plus exact unusual-name and escaped-literal search, with source line locations; capped at eight samples per path.',
                                'limitations': ['Under-approximate use graph; no automatic script execution.',
                                                'Unresolved dynamic shell/Python/Node dispatch prevents a complete classification.',
                                                'No orphan or regenerable classification inferred from an absent static edge.',
                                                'Recovery: topological first matching authored change or combined-diff merge resolution; no rename following.']},
            'records': records}


def verify(actual, expected, require_complete=True):
    if not isinstance(actual, dict): raise ValueError('inventory must be an object')
    if actual.get('schema_version') != SCHEMA: raise ValueError('schema version mismatch')
    if actual.get('measured_revision') != expected['measured_revision']:
        raise ValueError('stale or mismatched measured revision')
    rows = actual.get('records')
    if not isinstance(rows, list): raise ValueError('records must be a list')
    paths = [r.get('path') for r in rows if isinstance(r, dict)]
    if len(paths) != len(rows) or len(set(paths)) != len(paths): raise ValueError('duplicate or malformed rows')
    wanted = [r['path'] for r in expected['records']]
    if sorted(paths) != wanted: raise ValueError('missing or extra paths')
    for r in rows:
        if r.get('class') not in (*CLASSES, None): raise ValueError('invalid class')
    # Rebuilding all rows checks every pin/chain/content claim, not a digest
    # supplied by the same untrusted input. This also rejects extra fields.
    if actual != expected: raise ValueError('classification provenance, recovery pin, ordering or schema differs from rebuilt model')
    if require_complete and expected['analysis_gaps']:
        raise ValueError('unresolved analysis: ' + '; '.join(expected['analysis_gaps']))
    if require_complete and expected['totals']['unresolved']:
        raise ValueError(f"incomplete classification: {expected['totals']['unresolved']} unresolved paths")
    if sum(expected['totals'][c] for c in CLASSES) != len(wanted):
        if require_complete: raise ValueError('four-class totals do not equal universe')


def self_test():
    if not __debug__: raise ValueError("self-test requires Python assertions; omit -O")
    import copy
    assert evidence_role(b'\x1f\x8b' + b'\0' * 40) is None
    transcript = b'....\n----------------------------------------------------------------------\nRan 4 tests in 0.001s\n\nOK\n'
    assert evidence_role(gzip.compress(transcript, mtime=0))
    assert evidence_role(gzip.compress(b'import unittest\n', mtime=0)) is None
    quoted_log = b'\"\"\"\n' + b'PASS build 1s\n' * 5 + b'\"\"\"\n'
    assert evidence_role(quoted_log) is None
    for placeholder in (
            {'recordedOn': None, 'startingCommit': 'expected', 'implementationCommit': 'expected'},
            {'command': None, 'exit': 'expected', 'elapsed_seconds': 'unrun'},
            {'metadata': dict.fromkeys(('commit', 'compilerSha256', 'runnerSha256', 'modelSha256')), 'results': []},
            {'reviews': []}, {'groups': [{'expected': '0x00'}]},
            dict.fromkeys(('archiveSha256', 'runnerSha256', 'modelSha256', 'completedFixtureFiles', 'totalFixtureFiles', 'counts', 'complete')),
            {'commit': None, 'completed': [], 'errors': [], 'mode': None, 'results': [], 'sources': [], 'version': None}):
        assert evidence_role(json.dumps(placeholder).encode()) is None
    assert nonnegative_number(10 ** 1000)
    resource_receipt = {'command': ['archived-runner'], 'exit': 7, 'elapsed_seconds': 0.25,
                        'resource_stop': False, 'peak_group_rss_bytes': 1024}
    assert evidence_role(json.dumps(resource_receipt).encode())
    for bad in (None, True, 'unrun', -1, float('nan'), float('inf')):
        assert evidence_role(json.dumps(dict(resource_receipt, elapsed_seconds=bad)).encode()) is None
    summary = {'commit': 'a' * 40, 'mode': 'proof', 'completedSources': 1, 'totalSources': 1,
               'results': {'proved': 2, 'error': 1}, 'errors': 1, 'suites': {'suite': {'proved': 2, 'error': 1}}}
    assert evidence_role(json.dumps(summary).encode())
    assert evidence_role(json.dumps(dict(summary, commit='unrun')).encode()) is None
    assert evidence_role(json.dumps(dict(summary, suites={'suite': {'proved': 1}})).encode()) is None
    assert evidence_role(json.dumps(dict(summary, suites={'suite': {'proved': 2, 'error': 1, 'extra': 1}})).encode()) is None
    measured_row = {'command': ['old-runner'], 'exitCode': 7, 'elapsedSeconds': 0.25,
                    'wait4MaxRssKiB': 1024, 'log': 'bound.log.gz', 'uncompressedLogSha256': 'a' * 64}
    resource_envelope = {'recordedAt': '2026-01-01T00:00:00+00:00', 'elapsedSeconds': 0.5,
        'maxWait4JobRssKiB': 1024, 'resourceInterpretation': 'Recorded child resources',
        'nativeValidation': 'partial', 'originalCoreAndCorpus': 'recorded', 'newTheoremAxiomAudit': 'recorded',
        'commands': [measured_row]}
    assert reviewed_receipt_rows(resource_envelope) == [('/commands/0', measured_row)]
    assert evidence_role(json.dumps(resource_envelope).encode())
    for field, bad in (('elapsedSeconds', float('nan')), ('maxWait4JobRssKiB', True), ('commands', {})):
        assert not reviewed_receipt_rows(dict(resource_envelope, **{field: bad}))
    check_row = {'command': 'archived command', 'runner': 'old-wrapper', 'exitCode': 9, 'elapsedSeconds': 1,
                 'peakCgroupBytes': 100, 'status': 'failed', 'log': 'tests/old.log', 'sha256': 'b' * 64}
    continuation = {'version': 1, 'recordedAt': '2026-01-01T00:00:00Z', 'evidenceBaseCommit': 'a' * 40,
                    'implementationCommit': 'b' * 40, 'branch': 'old', 'runtime': {},
                    'historicalIntegrity': {}, 'checks': [check_row]}
    assert reviewed_receipt_rows(continuation) == [('/checks/0', check_row)]
    assert not reviewed_receipt_rows(dict(continuation, checks=[dict(check_row, command=None)]))
    with tempfile.TemporaryDirectory(prefix='tests-used-controls-') as directory:
        root = Path(directory)
        git(root, 'init', '-q')
        sources = {
            '.github/workflows/test.yml': 'jobs:\n  test:\n    steps:\n      - run: python3 tests/live.py\n      - run: echo python3 tests/mention.py\n        env:\n          TEXT: python3 tests/env-only.py\n',
            'tests/live.py': 'import helper\nfrom pathlib import Path\nPath("tests/generated.txt").read_bytes()\nPath("tests/dead.lean").read_text()\n',
            'tests/helper.py': 'VALUE = 1\nif __name__ == "__main__":\n from pathlib import Path\n Path("tests/main-only.txt").read_text()\n',
            'tests/main-only.txt': 'main only\n',
            'tests/pass.py': 'import unittest\nclass T(unittest.TestCase):\n def test_value(self): import live; self.assertEqual(2 + 2, 4)\nif __name__ == "__main__": unittest.main()\n',
            'tests/fail.py': 'raise SystemExit(1)\n',
            'tests/failing-unit.py': 'import unittest\nclass Failed(unittest.TestCase):\n def test_failure(self): self.fail("intentional control")\nif __name__ == "__main__": unittest.main()\n',
            'tests/dead-unit.py': 'import unittest\nclass Dead(unittest.TestCase):\n def test_value(self): pass\nif False: unittest.main()\n',
            'tests/quoted-unit.py': '"""import unittest\nclass Fake(unittest.TestCase):\n def test_value(self): pass\nif __name__ == "__main__": unittest.main()\n"""\n',
            'tests/shadowed-unit.py': 'import unittest\nunittest = object()\nclass Fake(unittest.TestCase):\n def test_value(self): pass\nif __name__ == "__main__": unittest.main()\n',
            'tests/plain.py': 'from pathlib import Path\ndef main(): assert Path("tests/generated.txt").read_bytes() == b"generated\\n"; Path("tests/" + "mention" + ".txt").read_text()\nif __name__ == "__main__": main()\n',
            'tests/callback.py': 'import callback_helper as helper\ndef callback(): return helper.read()\nassert helper.invoke(callback) == "callback\\n"\n',
            'tests/callback_helper.py': 'from pathlib import Path\ndef invoke(f): return f()\ndef read(): return Path("tests/callback.txt").read_text()\n',
            'tests/callback.txt': 'callback\n',
            'tests/callback.md': 'Run `python3 -B tests/callback.py` to check helper callback/read behavior.\n',
            'scripts/h62/generator.py': 'from pathlib import Path\nPath("tests/generated.txt").write_bytes(b"generated\\n")\nPath("tests/spare.txt").write_bytes(b"spare\\n")\n',
            'tests/generated.txt': 'generated\n',
            'tests/spare.txt': 'spare\n',
            'tests/dead.lean': 'solc_import "secondary.json" hash 0x1 as Dead\n',
            'tests/secondary.json': '{}\n',
            'tests/mention.py': 'raise SystemExit(0)\n',
            'tests/env-only.py': 'raise SystemExit(0)\n',
            'tests/mention.txt': 'A mention is not use.\n',
            'tests/dead.py': 'import cycle\n',
            'tests/cycle.py': 'import dead\n',
            'tests/evidence.json': json.dumps({'command': ['old-runner'], 'exit': 7, 'elapsed_seconds': 1.0, 'resource_stop': False, 'peak_group_rss_bytes': 12}) + '\n',
            'tests/unknown.bin': b'\x00\x01',
            'tests/.hidden': 'hidden\n',
            'tests/history-empty.log': b'',
            'tests/history-receipts.json': json.dumps([{'command': ['python3', '-c', 'pass'], 'exitCode': 0, 'elapsedSeconds': 0.0, 'log': 'tests/history-empty.log', 'sha256': hashlib.sha256(b'').hexdigest()}]),
            'tests/space name.txt': 'spaces\n',
            'tests/α.txt': 'unicode\n',
            'tests/unusual-reader.py': 'from pathlib import Path\nPath("tests/space name.txt").read_bytes()\nPath("tests/α.txt").read_bytes()\nPath("tests/line\\nname.txt").read_bytes()\n',
            'tests/line\nname.txt': 'newlines\n',
            'tests/package/lakefile.toml': 'name = "control-package"\n[[lean_lib]]\nname = "Package"\nsrcDir = "src"\n',
            'tests/package/lean-toolchain': 'leanprover/lean4:v4.24.0\n',
            'tests/package/src/Package.lean': 'import Package.Leaf\n',
            'tests/package/src/Package/Leaf.lean': 'import tests.foreign\n',
            'tests/package/src/Package/Unused.lean': 'def unused := 1\n',
            'tests/foreign.lean': 'def foreign := 1\n',
            'tests/missing-package/lakefile.toml': 'name = "missing"\n[[lean_lib]]\nname = "Missing"\n',
            'tests/missing-package/lean-toolchain': 'leanprover/lean4:v4.24.0\n',
            'tests/missing-package/Unselected.lean': 'def unselected := 1\n',
            'scripts/h55/other': 'h55\n',
            'scripts/h62/other': 'h62\n',
        }
        bound_envelope = dict(resource_envelope, commands=[dict(measured_row, log='tests/bound-history.log', uncompressedLogSha256=hashlib.sha256(b'archived failure\n').hexdigest())])
        sources['tests/bound-history.json'] = json.dumps(bound_envelope)
        sources['tests/bound-history.log'] = 'archived failure\n'
        sources['tests/unsafe-history.json'] = json.dumps(dict(resource_envelope, commands=[dict(measured_row, log='/tests/not-an-input.log', uncompressedLogSha256=hashlib.sha256(b'unused\n').hexdigest())]))
        sources['tests/not-an-input.log'] = 'unused\n'
        sources['tests/magic-name-unit.py'] = 'import unittest as u\nimport unittest as __name__\nclass T(u.TestCase):\n def test_value(self): pass\nif __name__ == "__main__": u.main()\n'
        sources['tests/import-shadow-unit.py'] = 'import unittest\nimport json as unittest\nclass T(unittest.TestCase):\n def test_value(self): pass\nif __name__ == "__main__": unittest.main()\n'
        sources['tests/from-shadow-unit.py'] = 'from unittest import TestCase, main\nfrom json import loads as main\nclass T(TestCase):\n def test_value(self): pass\nif __name__ == "__main__": main()\n'
        sources['tests/exit-before-unit.py'] = 'import unittest,sys\nclass T(unittest.TestCase):\n def test_value(self): pass\nsys.exit(0)\nif __name__ == "__main__": unittest.main()\n'
        for i in range(9): sources[f'tests/reference-{i}.txt'] = 'Historical mention of tests/spare.txt only.\n'
        for p, content in sources.items():
            target = root / p; target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(content if isinstance(content, bytes) else content.encode())
        git(root, 'add', '.')
        git(root, '-c', 'user.name=Control', '-c', 'user.email=control@example.invalid', 'commit', '-qm', 'control')
        repo = Repository(root, 'HEAD')
        assert repo.paths == sorted(p for p in sources if p.startswith(SCOPE))
        passed = subprocess.run([sys.executable, '-B', 'tests/pass.py'], cwd=root, capture_output=True)
        failed = subprocess.run([sys.executable, '-B', 'tests/fail.py'], cwd=root, capture_output=True)
        assert passed.returncode == 0 and failed.returncode == 1
        before = (root / 'tests/generated.txt').read_bytes()
        (root / 'tests/generated.txt').unlink(); (root / 'tests/spare.txt').unlink()
        reproduced = subprocess.run([sys.executable, '-B', 'scripts/h62/generator.py'], cwd=root, capture_output=True)
        assert reproduced.returncode == 0 and (root / 'tests/generated.txt').read_bytes() == before
        catalog = {'schema_version': 1, 'standalone': [{
            'path': 'tests/pass.py', 'input_revision': repo.ref,
            'source_blob': repo.tree['tests/pass.py'][2],
            'command': ['python3', '-B', 'tests/pass.py'], 'kind': 'unittest'}],
            'orphans': [{'path': 'tests/unknown.bin', 'input_revision': repo.ref,
                'blob': repo.tree['tests/unknown.bin'][2],
                'reason': 'No references or runner use after complete source/root search of the closed control repository.',
                'dynamic_review': 'Inspected control workflow and all runner sources: named literal reads/imports only; no dynamic selection can reach unknown.bin.'}],
            'reads': [], 'generators': [{'path': 'tests/generated.txt', 'input_revision': repo.ref,
                'output_blob': repo.tree['tests/generated.txt'][2],
                'generator': 'scripts/h62/generator.py',
                'generator_blob': repo.tree['scripts/h62/generator.py'][2],
                'command': ['python3', '-B', 'scripts/h62/generator.py'],
                'inputs': {'scripts/h62/generator.py': repo.tree['scripts/h62/generator.py'][2]},
                'tools': ['Python standard library'], 'comparison': 'exact bytes'}]}
        for target, line in (('tests/helper.py', 1), ('tests/generated.txt', 3), ('tests/dead.lean', 4)):
            catalog['reads'].append({'runner': 'validated:tests/pass.py', 'input_revision': repo.ref,
                'frames': [{'path': 'tests/pass.py', 'blob': repo.tree['tests/pass.py'][2], 'line': 3},
                           {'path': 'tests/live.py', 'blob': repo.tree['tests/live.py'][2], 'line': line}],
                'target': target, 'target_blob': repo.tree[target][2],
                'operation': 'validated Python read of measured bytes'})
        assert subprocess.run(['python3', '-B', 'tests/plain.py'], cwd=root, capture_output=True).returncode == 0
        catalog['standalone'].append({'path': 'tests/plain.py', 'input_revision': repo.ref, 'source_blob': repo.tree['tests/plain.py'][2], 'command': ['python3', '-B', 'tests/plain.py'], 'kind': 'runnable-entrypoint', 'entry_line': 3, 'purpose': 'Check the generated fixture in the default command', 'input_scope': ['tests/generated.txt'], 'other_reads': 'unresolved'})
        catalog['reads'].append({'runner': 'validated:tests/plain.py', 'input_revision': repo.ref,
            'frames': [{'path': 'tests/plain.py', 'blob': repo.tree['tests/plain.py'][2], 'line': 2}],
            'target': 'tests/mention.txt', 'target_blob': repo.tree['tests/mention.txt'][2], 'operation': 'validated Python read of measured bytes'})
        catalog['orphans'].append({'path': 'tests/mention.txt', 'input_revision': repo.ref, 'blob': repo.tree['tests/mention.txt'][2],
            'reason': 'Unsupported negative claim despite an observed dynamic read', 'dynamic_review': 'Unsupported review'})
        callback_command = ['python3', '-B', 'tests/callback.py']
        assert subprocess.run(callback_command, cwd=root, capture_output=True).returncode == 0
        catalog['standalone'].append({'path': 'tests/callback.py', 'input_revision': repo.ref,
            'source_blob': repo.tree['tests/callback.py'][2], 'command': callback_command,
            'kind': 'manual-reproducer', 'documentation': {'path': 'tests/callback.md',
                'blob': repo.tree['tests/callback.md'][2], 'line': 1,
                'invocation': 'python3 -B tests/callback.py', 'normalization': 'verbatim'}})
        callback_frames = [('tests/callback.py', 3), ('tests/callback_helper.py', 2),
                           ('tests/callback.py', 2), ('tests/callback_helper.py', 3)]
        catalog['reads'].append({'runner': 'validated:tests/callback.py', 'input_revision': repo.ref,
            'frames': [{'path': path, 'blob': repo.tree[path][2], 'line': line} for path, line in callback_frames],
            'target': 'tests/callback.txt', 'target_blob': repo.tree['tests/callback.txt'][2],
            'operation': 'validated Python read of measured bytes'})
        spare = copy.deepcopy(catalog['generators'][0]); spare.update(path='tests/spare.txt', output_blob=repo.tree['tests/spare.txt'][2])
        catalog['generators'].append(spare)
        assert (root / 'tests/spare.txt').read_bytes() == b'spare\n'
        expected = inventory(repo, catalog)
        rows = {r['path']: r for r in expected['records']}
        for p in ('tests/live.py', 'tests/helper.py', 'tests/pass.py', 'tests/generated.txt'):
            assert rows[p]['class'] == 'keep', p
        assert rows['tests/generated.txt']['generator']
        assert subprocess.run(['python3', '-B', 'tests/failing-unit.py'], cwd=root, capture_output=True).returncode == 1
        assert rows['tests/failing-unit.py']['class'] == 'keep'
        assert rows['tests/failing-unit.py']['runner_chain']['entry']['source_only']
        assert rows['tests/failing-unit.py']['runner_chain']['entry']['validation_at_measured_revision']['status'] == 'unavailable'
        for name in ('dead-unit.py', 'quoted-unit.py', 'shadowed-unit.py', 'import-shadow-unit.py', 'from-shadow-unit.py', 'exit-before-unit.py', 'magic-name-unit.py'): assert rows['tests/' + name]['class'] is None
        assert rows['tests/plain.py']['class'] == 'keep'
        assert rows['tests/mention.txt']['class'] is None and rows['tests/mention.txt']['secondary']['unreviewed_readers']
        for path in ('tests/package/lakefile.toml', 'tests/package/src/Package.lean', 'tests/package/src/Package/Leaf.lean'): assert rows[path]['class'] == 'keep', path
        for path in ('tests/foreign.lean', 'tests/package/src/Package/Unused.lean', 'tests/missing-package/Unselected.lean'): assert rows[path]['class'] is None, path
        callback_chain = rows['tests/callback.txt']['runner_chain']
        assert [edge['source'] for edge in callback_chain['edges']] == [path for path, _ in callback_frames]
        assert [edge['line'] for edge in callback_chain['edges']] == [line for _, line in callback_frames]
        assert rows['tests/callback.py']['class'] == 'keep'
        assert rows['tests/callback.md']['class'] is None  # classifier definitions cannot keep documentation
        unsupported = copy.deepcopy(catalog)
        unsupported['standalone'][-1]['command'] = ['python3', '-c', 'pass', 'tests/callback.py']
        try: inventory(repo, unsupported)
        except ValueError: pass
        else: raise AssertionError('unsupported manual invocation accepted')
        mismatched = copy.deepcopy(catalog)
        mismatched['standalone'][-1]['command'].append('--help')
        try: inventory(repo, mismatched)
        except ValueError: pass
        else: raise AssertionError('same-runner different-arguments reproducer accepted')
        assert rows['tests/spare.txt']['class'] is None
        assert rows['tests/spare.txt']['generator']
        assert 'UNRESOLVED_GENERATED_CONSUMPTION' in ' '.join(rows['tests/spare.txt']['unresolved'])
        overclaimed = copy.deepcopy(expected)
        next(r for r in overclaimed['records'] if r['path'] == 'tests/spare.txt')['class'] = 'regenerable'
        try: verify(overclaimed, expected, require_complete=False)
        except ValueError: pass
        else: raise AssertionError('absent graph edge granted regenerable non-use')
        catalog['generators'][-1]['consumption_review'] = {
            'verdict': 'no-active-consumer-found', 'input_revision': repo.ref,
            'search_coverage': 'Reviewed every committed control source and all references: spare.txt is only written by generator.py.',
            'dynamic_analysis': 'Reviewed all fixture controls, imports and literal/default reads; none select spare.txt. No unresolved dynamic reference reaches this output.',
            'reviewed_sources': {p: repo.tree[p][2] for p in repo.texts},
            'entry_points_reviewed': copy.deepcopy(expected['entry_points'])}
        expected = inventory(repo, catalog)
        rows = {r['path']: r for r in expected['records']}
        assert rows['tests/spare.txt']['class'] == 'regenerable'
        uncovered = copy.deepcopy(catalog)
        del uncovered['generators'][-1]['consumption_review']['reviewed_sources']['tests/reference-8.txt']
        assert next(r for r in inventory(repo, uncovered)['records'] if r['path'] == 'tests/spare.txt')['class'] is None
        graph_control = Graph(repo)
        graph_control.root('tests/live.py', 'control', 'runner --mode-a', 'tests/live.py', 1, root_id='same-id')
        bound = copy.deepcopy(catalog['generators'][-1])
        bound['consumption_review']['entry_points_reviewed'] = copy.deepcopy(graph_control.roots)
        assert reviewed_generated_consumption(bound, graph_control, set())
        for field, replacement in (('command', 'runner --mode-b'), ('cwd', 'other'), ('source_argument', 'other.txt')):
            changed_graph = Graph(repo); changed_graph.roots = copy.deepcopy(graph_control.roots)
            changed_graph.roots['same-id'][field] = replacement
            try: reviewed_generated_consumption(bound, changed_graph, set())
            except ValueError: pass
            else: raise AssertionError('changed root definition preserved a negative consumption review')
        unsupported_review = copy.deepcopy(catalog)
        unsupported_review['generators'][-1]['consumption_review']['dynamic_analysis'] = ''
        try: inventory(repo, unsupported_review)
        except ValueError: pass
        else: raise AssertionError('empty generated-consumption analysis accepted')
        assert rows['tests/unknown.bin']['class'] == 'orphan'
        assert rows['tests/dead.lean']['class'] == 'keep'
        assert rows['tests/secondary.json']['class'] is None  # a data read cannot elaborate Lean
        for p in ('tests/fail.py', 'tests/main-only.txt', 'tests/mention.py', 'tests/env-only.py', 'tests/dead.py', 'tests/cycle.py'):
            assert rows[p]['class'] is None, p
        assert rows['tests/evidence.json']['class'] == 'evidence'
        assert rows['tests/history-empty.log']['class'] == 'evidence'
        assert rows['tests/bound-history.log']['class'] == 'evidence'
        assert '/commands/0' in rows['tests/bound-history.log']['reason']
        assert rows['tests/not-an-input.log']['class'] is None
        assert rows['tests/history-receipts.json']['class'] == 'evidence'
        assert all(r['recovery'] for r in rows.values())
        for path in ('tests/space name.txt', 'tests/α.txt', 'tests/line\nname.txt'):
            assert rows[path]['search_candidates'], path
        for path, row in rows.items():
            recovered = subprocess.check_output(shlex.split(row['recovery']['command']), cwd=root)
            assert recovered == repo.bytes(path)
        contradicted = copy.deepcopy(catalog)
        contradicted['orphans'].append({'path': 'tests/α.txt', 'input_revision': repo.ref,
            'blob': repo.tree['tests/α.txt'][2], 'reason': 'Unsupported negative claim', 'dynamic_review': 'none'})
        assert next(r for r in inventory(repo, contradicted)['records'] if r['path'] == 'tests/α.txt')['class'] is None
        (root / 'tests/live.py').write_text('raise RuntimeError()\n')
        (root / 'tests/untracked').write_text('ignored\n')
        assert canonical(inventory(Repository(root, 'HEAD'), catalog)) == canonical(expected)
        mutations = [lambda d: d['records'].pop(),
                     lambda d: d['records'].append(copy.deepcopy(d['records'][0])),
                     lambda d: d['records'][0].update({'class': 'unused'}),
                     lambda d: d.update({'measured_revision': '0' * 40}),
                     lambda d: d['records'][0]['recovery'].update({'last_touch_commit': '0' * 40}),
                     lambda d: d['records'][0].update({'runner_chain': {'root': 'fabricated'}})]
        for mutate in mutations:
            data = copy.deepcopy(expected); mutate(data)
            try: verify(data, expected, require_complete=False)
            except ValueError: pass
            else: raise AssertionError('tampered inventory accepted')
        invalid = copy.deepcopy(catalog)
        invalid['generators'][0]['command'] = ['python3', '-c', 'pass', 'scripts/h62/generator.py']
        try: validated_routes(Graph(repo), invalid)
        except ValueError: pass
        else: raise AssertionError('non-invocation generator claim accepted')
        verify(expected, expected, require_complete=False)
        try: verify(expected, expected)
        except ValueError as e: assert 'incomplete' in str(e)
        else: raise AssertionError('partial inventory accepted')
        merge_root = root / 'merge-control'; merge_root.mkdir()
        git(merge_root, 'init', '-q')
        git(merge_root, 'config', 'user.name', 'Control')
        git(merge_root, 'config', 'user.email', 'control@example.invalid')
        git(merge_root, 'config', 'core.hooksPath', '/dev/null')
        f = merge_root / 'tests/restored.txt'; f.parent.mkdir(); f.write_text('original')
        git(merge_root, 'add', '.'); git(merge_root, 'commit', '-qm', 'original')
        original = decode(git(merge_root, 'rev-parse', 'HEAD')).strip()
        git(merge_root, 'checkout', '-qb', 'left')
        f.write_text('left'); git(merge_root, 'commit', '-qam', 'left')
        git(merge_root, 'checkout', '-qb', 'right', original)
        f.write_text('right'); git(merge_root, 'commit', '-qam', 'right')
        merged = subprocess.run(['git', '-C', str(merge_root), 'merge', 'left', '--no-edit'], capture_output=True)
        assert merged.returncode == 1
        f.write_text('original'); git(merge_root, 'add', '.'); git(merge_root, 'commit', '-qm', 'restore through merge resolution')
        merged_ref = decode(git(merge_root, 'rev-parse', 'HEAD')).strip()
        assert Repository(merge_root, 'HEAD').pins()['tests/restored.txt']['last_touch_commit'] == merged_ref
        git(root, '-c', 'user.name=Control', '-c', 'user.email=control@example.invalid', 'commit', '--allow-empty', '-qm', 'advance without touching inputs')
        newer = inventory(Repository(root, 'HEAD'), catalog)
        later_rows = {r['path']: r for r in newer['records']}
        entry = later_rows['tests/pass.py']['runner_chain']['entry']
        assert later_rows['tests/pass.py']['class'] == 'keep' and entry['source_only']
        assert entry['validation_at_measured_revision']['status'] == 'unavailable'
        assert entry['command'] == 'python3 -B tests/pass.py'
        assert later_rows['tests/callback.txt']['class'] is None  # old passing reproducer/read receives no current credit
        source_graph = Graph(Repository(root, 'HEAD'))
        source_graph.root('tests/pass.py', 'committed standalone runner', 'python3 -B tests/pass.py', 'tests/pass.py', 1)
        source_graph.roots['tests/pass.py']['source_only'] = True
        source_graph.edge('tests/pass.py', 'tests/cycle.py', 1, 'unrelated shared invocation', kind='executes')
        source_graph.edge('tests/cycle.py', 'tests/callback.txt', 1, 'unrelated shared read')
        assert 'tests/cycle.py' not in source_graph.chains() and 'tests/callback.txt' not in source_graph.chains()
        try: verify(expected, newer)
        except ValueError as error: assert 'revision' in str(error)
        else: raise AssertionError('genuine stale revision accepted')
        git(root, 'rm', '-q', '--', 'tests/generated.txt')
        git(root, '-c', 'user.name=Control', '-c', 'user.email=control@example.invalid', 'commit', '-qm', 'remove old fixture only')
        removed_repo = Repository(root, 'HEAD')
        removed = {r['path']: r for r in inventory(removed_repo, catalog)['records']}
        assert removed['tests/plain.py']['class'] == 'keep'
        assert removed['tests/plain.py']['runner_chain']['entry']['source_only']
        assert 'tests/generated.txt' not in removed
        fabricated_demonstration = copy.deepcopy(catalog)
        fabricated_demonstration['standalone'][0]['input_revision'] = '0' * 40
        try: inventory(removed_repo, fabricated_demonstration)
        except ValueError as error: assert 'historical runner' in str(error)
        else: raise AssertionError('fabricated historical demonstration revision accepted')
        shallow = root / 'shallow-clone'
        git(root, 'clone', '-q', '--depth=1', root.as_uri(), str(shallow))
        shallow_repo = Repository(shallow, 'HEAD')
        assert shallow_repo.shallow and not shallow_repo.pins()
        assert not shell_operands('echo python3 tests/mention.py')
        assert not shell_operands('echo "node --test tests/mention.py"')
        assert shell_operands('lake env python3 -B tests/live.py') == ['tests/live.py']
    print('self-test: enumeration, recovery, shallow history, shell, standalone pass/fail, exact generation, consumed-generated data and tamper and reviewed-orphan controls PASS')


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument('--ref', default='origin/master', help='committed revision to measure (default: origin/master)')
    modes = parser.add_mutually_exclusive_group(required=True)
    modes.add_argument('--write', action='store_true')
    modes.add_argument('--check', action='store_true')
    modes.add_argument('--self-test', action='store_true')
    args = parser.parse_args()
    try:
        if args.self_test: self_test(); return 0
        root = decode(git(Path.cwd(), 'rev-parse', '--show-toplevel')).strip()
        expected = inventory(Repository(root, args.ref))
        target = Path(root) / OUTPUT
        if args.write: target.write_bytes(canonical(expected))
        else:
            actual = json.loads(target.read_bytes())
            verify(actual, expected)
            if target.read_bytes() != canonical(expected): raise ValueError('noncanonical inventory bytes')
        print(json.dumps(expected['totals'], sort_keys=True))
        if expected['totals']['unresolved'] or expected['analysis_gaps']:
            print('INCOMPLETE: unresolved paths are not justified classes; no pruning authorization.', file=sys.stderr)
            return 1
        return 0
    except (ValueError, OSError, KeyError, TypeError, AssertionError) as e:
        print('tests-used: ' + str(e), file=sys.stderr); return 1


if __name__ == '__main__':
    sys.exit(main())
