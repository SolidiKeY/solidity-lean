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
Lean imports/solc_imports and observed Python reads of measured bytes.
Separately audited nonpassing unittest routes retain failure status and grant
no passing-reproducer credit; actual test/setup method identity is required.
Unreviewed unittest data reads remain unresolved even when the test passes.
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
import tarfile
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



def unique_json_object(pairs):
    result = {}
    for key, value in pairs:
        if key in result: raise ValueError('duplicate JSON object key: ' + key)
        result[key] = value
    return result


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


def compact_read_routes(routes):
    """Lossless family representation: identical full stacks share target pins.

    Only contiguous, path-ordered contexts are compactable. Exact ordered
    expansion must equal the input, preserving all equal-length chain ties.
    Every path/blob pair remains explicit; no glob or inferred target is added.
    """
    groups = {}
    for route in routes:
        if not isinstance(route, dict) or set(route) != {'runner', 'input_revision', 'frames', 'target', 'target_blob', 'operation'}:
            raise ValueError('invalid validated read route')
        base = {key: route[key] for key in ('runner', 'input_revision', 'frames', 'operation')}
        key = json.dumps(base, sort_keys=True, separators=(',', ':'))
        if key not in groups: groups[key] = (base, {})
        targets = groups[key][1]; target = route['target']; blob = route['target_blob']
        if not isinstance(target, str) or not isinstance(blob, str): raise ValueError('invalid target pin')
        if target in targets and targets[target] != blob: raise ValueError('conflicting grouped target pins')
        targets[target] = blob
    result = [{**base, 'targets': [{'path': path, 'blob': targets[path]} for path in sorted(targets)]}
              for base, targets in groups.values()]
    if list(read_routes({'schema_version': 2, 'reads': result})) != routes:
        raise ValueError('route order is not losslessly compactable')
    return result


def read_routes(catalog):
    """Expand compact definitions only; ordinary runs never execute commands."""
    rows = catalog['reads']
    if not isinstance(rows, list): raise ValueError('read definitions must be a list')
    if catalog['schema_version'] == 1:
        yield from rows
        return
    contexts = set()
    for group in rows:
        if not isinstance(group, dict) or set(group) != {'runner', 'input_revision', 'frames', 'operation', 'targets'}:
            raise ValueError('invalid grouped read definition')
        base = {key: group[key] for key in ('runner', 'input_revision', 'frames', 'operation')}
        key = json.dumps(base, sort_keys=True, separators=(',', ':'))
        if key in contexts: raise ValueError('duplicate grouped read context')
        contexts.add(key)
        targets = group['targets']
        if not isinstance(targets, list) or not targets: raise ValueError('empty or invalid grouped targets')
        if any(not isinstance(row, dict) or set(row) != {'path', 'blob'}
               or not isinstance(row['path'], str) or not isinstance(row['blob'], str) for row in targets):
            raise ValueError('invalid grouped target pin')
        paths = [row['path'] for row in targets]
        if paths != sorted(set(paths)): raise ValueError('duplicate or unordered grouped targets')
        for row in targets:
            yield {**base, 'target': row['path'], 'target_blob': row['blob']}


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
    if not isinstance(catalog, dict) or set(catalog) != {'schema_version', 'standalone', 'generators', 'reads', 'orphans'} or type(catalog['schema_version']) is not int or catalog['schema_version'] not in (1, 2):
        raise ValueError('invalid validation definition schema')
    current_runner_paths = {e.get('path') for e in catalog['standalone'] if e.get('input_revision') == repo.ref}
    # Historical source-only eligibility needs a real commit and the exact
    # recorded source object, not merely a matching current filename/blob.
    historical_specs = {}
    historical_revisions = set()
    for entry in catalog['standalone']:
        p = entry.get('path')
        if (entry.get('input_revision') == repo.ref or entry.get('kind') not in ('unittest', 'node-test', 'runnable-entrypoint', 'committed-cli')
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
        if entry.get('kind') == 'nonpassing-unittest': required.update(('purpose', 'input_scope'))
        if entry.get('kind') == 'skipped-unittest': required.add('purpose')
        if entry.get('kind') == 'committed-cli': required.update(('purpose', 'entry_line', 'required_options'))
        allowed = (required, required | {'purpose', 'input_scope', 'other_reads'}) if entry.get('kind') in ('unittest', 'node-test') else (required,)
        if set(entry) not in allowed:
            raise ValueError('invalid standalone definition')
        p = entry['path']
        historical_runner = entry['input_revision'] != repo.ref
        if historical_runner and (entry['kind'] not in ('unittest', 'node-test', 'runnable-entrypoint', 'committed-cli')
                or p in current_runner_paths or p not in repo.tree or repo.tree[p][2] != entry['source_blob']):
            continue
        if p not in repo.tree or repo.tree[p][2] != entry['source_blob']:
            raise ValueError('standalone definition source mismatch: ' + p)
        command = entry['command']
        if entry['kind'] != 'manual-reproducer' and command not in (['python3', '-B', p], ['node', '--test', p]):
            raise ValueError('unsupported standalone invocation: ' + p)
        if entry['kind'] not in ('unittest', 'node-test', 'manual-reproducer', 'runnable-entrypoint', 'nonpassing-unittest', 'skipped-unittest', 'committed-cli'):
            raise ValueError('unsupported standalone kind')
        if entry['kind'] == 'committed-cli':
            declaration = declared_configured_cli(repo, p)
            if (declaration is None or command != ['python3', '-B', p]
                    or type(entry['entry_line']) is not int or entry['entry_line'] != declaration['main_line']
                    or entry['required_options'] != declaration['required_options']
                    or not isinstance(entry['purpose'], str) or not entry['purpose'].strip()):
                raise ValueError('unsupported committed CLI source role')
            identity = 'committed-cli:' + p
            graph.root(p, 'committed CLI runner source', shlex.join(command), p,
                       declaration['main_line'], root_id=identity)
            graph.roots[identity].update({'source_only': True, 'source_blob': entry['source_blob'],
                'role_provenance': declaration, 'purpose': entry['purpose'],
                'source_demonstration_revision': entry['input_revision'],
                'command_form': 'entry prefix; required configuration is not supplied',
                'required_options': entry['required_options'],
                'validation_at_measured_revision': {'status': 'unavailable', 'command_prefix': command,
                    'reason': 'Configured checker invocation not validated; required options are absent. Source role only, no helper/fixture or passing-reproducer credit.'}})
            continue
        if entry['kind'] == 'skipped-unittest':
            declaration = declared_unittest(repo, p)
            if (declaration is None or command != ['python3', '-B', p]
                    or not isinstance(entry['purpose'], str) or not entry['purpose'].strip()):
                raise ValueError('skipped source lacks a declared unittest role/purpose')
            identity = 'skipped:' + p
            graph.root(p, 'unavailable committed unittest runner', shlex.join(command), p,
                       declaration['main_line'], root_id=identity)
            graph.roots[identity].update({'source_only': True, 'source_blob': entry['source_blob'],
                'role_provenance': declaration, 'purpose': entry['purpose'],
                'validation_at_measured_revision': {'status': 'unavailable', 'command': command,
                    'reason': 'All reported cases were skipped; zero exit does not establish test execution. No fixture or child credit.'}})
            continue
        if entry['kind'] == 'nonpassing-unittest':
            declaration = declared_unittest(repo, p)
            if declaration is None or command != ['python3', '-B', p]:
                raise ValueError('nonpassing source is not a declared unittest runner')
            scopes = entry['input_scope']
            if (not isinstance(entry['purpose'], str) or not entry['purpose'].strip()
                    or not isinstance(scopes, list) or not all(isinstance(v, str) and v not in SCOPE
                        and (v in repo.tree or v.endswith('/') and any(q.startswith(v) for q in repo.tree)) for v in scopes)):
                raise ValueError('nonpassing test lacks reviewed fixture scope')
            identity = 'nonpassing:' + p
            graph.root(p, 'nonpassing committed unittest runner', shlex.join(command), p,
                       declaration['main_line'], root_id=identity)
            graph.roots[identity].update({'source_only': True, 'source_blob': entry['source_blob'],
                'role_provenance': declaration, 'purpose': entry['purpose'], 'data_use_scope': scopes,
                'other_reads': 'unresolved', 'validation_at_measured_revision': {'status': 'failed',
                    'command': command, 'reason': 'Normal run failed; only separately observed test-context reads qualify. No passing-reproducer credit.'}})
            continue
        if entry['kind'] == 'unittest':
            if command != ['python3', '-B', p] or declared_unittest(repo, p) is None:
                raise ValueError('not a declared unittest entry point: ' + p)
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
                    'reason': 'No successful current validation is certified by this historical source-only definition; source role and command are established independently.'}})
            continue
        graph.root(p, 'validated standalone runner', shlex.join(command), p, entry.get('entry_line', 1), root_id='validated:' + p)
        graph.roots['validated:' + p].update({'runner_kind': entry['kind'], 'source_blob': entry['source_blob']})
        if entry['kind'] == 'runnable-entrypoint':
            graph.roots['validated:' + p].update({'purpose': entry['purpose'], 'data_use_scope': entry['input_scope'], 'other_reads': entry['other_reads']})
        if entry['kind'] in ('unittest', 'node-test'):
            if 'input_scope' in entry:
                scopes = entry['input_scope']
                if (not isinstance(entry['purpose'], str) or not entry['purpose'].strip()
                        or entry['other_reads'] not in ('unresolved', 'secondary')
                        or not isinstance(scopes, list) or not all(isinstance(v, str) and v not in SCOPE
                            and (v in repo.tree or v.endswith('/') and any(q.startswith(v) for q in repo.tree)) for v in scopes)):
                    raise ValueError('invalid reviewed unittest fixture scope')
                purpose = entry['purpose']; other = entry['other_reads']
            else:
                scopes = []; other = 'unresolved'
                purpose = 'Fixture roles not reviewed; passing test status and IO alone do not establish data eligibility.'
            graph.roots['validated:' + p].update({'purpose': purpose, 'data_use_scope': scopes, 'other_reads': other})
        if entry['kind'] == 'manual-reproducer': graph.roots['validated:' + p]['documentation'] = entry['documentation']
    for route in read_routes(catalog):
        if set(route) != {'runner', 'input_revision', 'frames', 'target', 'target_blob', 'operation'}:
            raise ValueError('invalid validated read route')
        if route['input_revision'] != repo.ref: continue
        original = route['runner']
        if original not in graph.roots or graph.roots[original]['kind'] not in ('validated standalone runner', 'nonpassing committed unittest runner'):
            raise ValueError('validated read has no validated runner')
        target = route['target']
        if target not in repo.tree or repo.tree[target][2] != route['target_blob']:
            raise ValueError('validated read target mismatch')
        nonpassing = graph.roots[original]['kind'] == 'nonpassing committed unittest runner'
        operation = 'Observed fixture read during nonpassing unittest' if nonpassing else 'validated Python read of measured bytes'
        if route['operation'] != operation:
            raise ValueError('unsupported validated read operation')
        frames = route['frames']
        if not isinstance(frames, list) or not frames or frames[0].get('path') != graph.roots[original]['path']:
            raise ValueError('validated read route does not start at its runner')
        for frame in frames:
            required_frame = {'path', 'blob', 'line'} | ({'code_qualname', 'code_firstlineno'} if nonpassing else set())
            if set(frame) != required_frame: raise ValueError('invalid read stack frame')
            if nonpassing and (not isinstance(frame['code_qualname'], str) or type(frame['code_firstlineno']) is not int or frame['code_firstlineno'] < 1):
                raise ValueError('invalid nonpassing frame code identity')
            source = frame['path']
            if source not in repo.tree or repo.tree[source][2] != frame['blob']:
                raise ValueError('validated read source mismatch')
            if not isinstance(frame['line'], int) or not 1 <= frame['line'] <= len(repo.texts.get(source, '').splitlines()):
                raise ValueError('validated read location mismatch')
        if nonpassing and not any(frame['path'] == graph.roots[original]['path'] and
                any(c['first'] <= frame['line'] <= c['last'] and c['qualname'] == frame['code_qualname'] and c['code_firstlineno'] == frame['code_firstlineno'] for c in graph.roots[original]['role_provenance']['test_contexts']) for frame in frames):
            raise ValueError('nonpassing read lacks an entered test or setup context')
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
                'line': caller['line'], 'operation': ('Observed nonpassing unittest call stack' if nonpassing else 'validated Python call stack'),
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


def reviewed_archive_report(value):
    """Two historical report shapes, independently traced to committed producers.

    shared-translator/verify-sourcebuild-intake.py:60-75 emits archive intake
    observations, not execution/source qualification. occurrence-integrity-
    controls.py:14-42 emits six control outcomes; its surrounding manifest is
    documented in docs/feature-work/directruntime-shared-translator.md:827.
    External paths/digests are recorded provenance only, never verified here.
    """
    if not isinstance(value, dict): return None
    def text(v): return isinstance(v, str) and bool(v.strip())
    def sized_digest(v):
        return (isinstance(v, dict) and set(v) == {'sha256', 'bytes'}
                and hex_pin(v['sha256']) and type(v['bytes']) is int and v['bytes'] > 0)
    intake = {'guardedRegression', 'inputDirectory', 'inputs', 'evidenceFiles',
              'recordedSourceModules', 'recordedSourceArraysEqual', 'binaries',
              'gitSourceIdentityVerified', 'execution', 'extraction', 'boundary'}
    if set(value) == intake:
        inputs, binaries = value['inputs'], value['binaries']
        if (all(text(value[k]) for k in ('guardedRegression', 'inputDirectory', 'boundary'))
                and value['guardedRegression'] == 'Historical sourceBuild1e8 intake is not current H90 qualification'
                and isinstance(inputs, dict) and set(inputs) == {'evidence.tar.gz', 'runtime-artifacts.tar.gz', 'files.json'}
                and all(hex_pin(v) for v in inputs.values())
                and all(type(value[k]) is int and value[k] > 0 for k in ('evidenceFiles', 'recordedSourceModules'))
                and value['recordedSourceArraysEqual'] is True
                and all(value[k] is False for k in ('gitSourceIdentityVerified', 'execution', 'extraction'))
                and isinstance(binaries, dict) and set(binaries) == {'native/direct-check', 'direct/direct.wasm', 'direct/direct.js'}
                and all(sized_digest(v) for v in binaries.values())):
            return 'Historical archive intake report (shared-translator/verify-sourcebuild-intake.py:60-75): archive/binary pins and recorded source-array observations; no current execution, Git identity or external-artifact verification.'
    occurrence = {'checkpoint', 'command', 'exit', 'wallSeconds', 'results', 'boundary', 'bulk'}
    if set(value) == occurrence:
        results, bulk = value['results'], value['bulk']
        names = ['healthy', 'missing-occurrence', 'case-identity', 'pointer', 'node-hash', 'route']
        if (all(text(value[k]) for k in ('checkpoint', 'boundary'))
                and value['command'] == 'PYTHONDONTWRITEBYTECODE=1 python3 tests/directruntime-20261104/shared-translator/occurrence-integrity-controls.py'
                and type(value['exit']) is int and nonnegative_number(value['wallSeconds'])
                and isinstance(results, dict) and set(results) == {'controls', 'boundary'} and text(results['boundary'])
                and isinstance(results['controls'], list) and len(results['controls']) == len(names)
                and all(isinstance(row, dict) and row.get('case') == name
                        and (set(row) == {'case', 'result'} and row['result'] == 'accepted' if index == 0 else
                             set(row) == {'case', 'result', 'line'} and row['result'] == 'rejected'
                             and type(row['line']) is int and row['line'] > 0)
                        for index, (name, row) in enumerate(zip(names, results['controls'])))
                and isinstance(bulk, list) and bulk and all(isinstance(row, dict)
                    and set(row) == {'path', 'bytes', 'sha256'} and text(row['path'])
                    and type(row['bytes']) is int and row['bytes'] >= 0 and hex_pin(row['sha256']) for row in bulk)):
            return 'Historical occurrence-integrity control report (shared-translator/occurrence-integrity-controls.py:14-42): recorded six-case outcomes, exit/timing and external bulk pins; no current pass, Lean proof or external-artifact verification.'
    return None


def reviewed_receipt_rows(value):
    """Measured rows from three reviewed historical envelope schemas.

    Not arbitrary recursive keys: native/probe resource envelopes contain
    commands[]; pinned continuation reports contain checks[]. A commands dict
    is a recipe table, never measured output. Missing commands get no credit.
    No success, active-consumer or external-artifact claim follows from a row.
    """
    if not isinstance(value, dict): return []
    # Frozen baseline producer schemas: value-entry/gates-runner.py:6,
    # value-entry/capped-gates.py:6 and value-runtime/final-gates.py:6.
    # These date-free reports record cumulative child RSS, not aggregate peak.
    fields = set(value)
    baseline_envelopes = (
        {'commands', 'memoryMetric', 'noLeanNoBuild'},
        {'commands', 'environment', 'cgroupMemoryPeakBytes', 'cgroupMemoryMaxBytes', 'cgroupSwapMaxBytes', 'memoryEvents', 'noLeanNoBuild'},
        {'commands', 'archiveRegularFilesVerified', 'docPathOutputUnchanged', 'noLeanOrBuildInFinalGates', 'cgroupPeakBytes', 'memoryMaxBytes', 'swapMaxBytes', 'memoryEvents'},
    )
    baseline = False
    if fields == baseline_envelopes[0]:
        baseline = value['noLeanNoBuild'] is True and isinstance(value['memoryMetric'], str) and bool(value['memoryMetric'])
    elif fields == baseline_envelopes[1]:
        baseline = (value['noLeanNoBuild'] is True and value['environment'] == {'LEAN_NUM_THREADS': '1'}
                    and isinstance(value['memoryEvents'], str) and all(type(value[k]) is int and value[k] >= 0
                        for k in ('cgroupMemoryPeakBytes', 'cgroupMemoryMaxBytes', 'cgroupSwapMaxBytes')))
    elif fields == baseline_envelopes[2]:
        baseline = (value['docPathOutputUnchanged'] is True and value['noLeanOrBuildInFinalGates'] is True
                    and isinstance(value['memoryEvents'], str) and all(type(value[k]) is int and value[k] >= 0
                        for k in ('archiveRegularFilesVerified', 'cgroupPeakBytes', 'memoryMaxBytes', 'swapMaxBytes')))
    if baseline:
        rows = command_receipt_rows(value)
        required = {'command', 'exitCode', 'elapsedSeconds', 'cumulativeChildrenMaxRssKiB', 'log', 'uncompressedSha256'}
        if rows and all(set(row) in (required, required | {'expectedExitCode'})
                and type(row['cumulativeChildrenMaxRssKiB']) is int and row['cumulativeChildrenMaxRssKiB'] >= 0
                and isinstance(row['log'], str) and row['log'] and hex_pin(row['uncompressedSha256'])
                and ('expectedExitCode' not in row or type(row['expectedExitCode']) is int) for row in rows):
            return [(f'/commands/{i}', row) for i, row in enumerate(rows)]
        return []
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


def failed_validation_logs(value):
    """Two reviewed initial-failure indexes; hashes bind stored log bytes.

    The reports retain failed whitespace checks and name their archived output
    objects. No committed producer for the initial envelopes was found. The
    related attribution/validate.py:29-41 and probes/validate.py:28-37 create
    sequential gzip logs, but that does not identify every indexed command.
    Never invent per-log commands, exits, timing or current validation credit.
    """
    if not isinstance(value, dict): return []
    core = {'exitCode', 'failedGate', 'failedGateExitCode', 'reason', 'logs'}
    if set(value) not in (core, core | {'status', 'command'}): return []
    if set(value) != core and (value['status'] != 'failed-whitespace-check' or value['command'] !=
            ['python3', 'tests/upstream/baseline-20261028/attribution/validate.py']): return []
    if (value['failedGate'] != ['git', 'diff', '--cached', '--check']
            or any(type(value[k]) is not int or value[k] == 0 for k in ('exitCode', 'failedGateExitCode'))
            or not isinstance(value['reason'], str) or not value['reason'].strip()): return []
    logs = value['logs']
    if not isinstance(logs, list) or not logs: return []
    paths = []
    for row in logs:
        if not isinstance(row, dict) or set(row) != {'path', 'sha256'}: return []
        path = row['path']
        if (not isinstance(path, str) or not path or '\0' in path or path.startswith(('/', '\\'))
                or re.match(r'^[A-Za-z]:', path) or any(p in ('', '.', '..') for p in path.split('/'))
                or not hex_pin(row['sha256'])): return []
        paths.append(path)
    if len(set(paths)) != len(paths): return []
    return [(f'/logs/{index}', {'log': row['path'], 'sha256': row['sha256']}) for index, row in enumerate(logs)]



def flat_node_transcript(text):
    """Narrow Node spec output: only flat timed cases and a full EOF summary.

    Reviewed baseline gate and group04 transcripts use this exact form. Nested
    suites, failure diagnostics, resource wrappers and partial summaries are
    deliberately outside it. Counters describe historical output, never a
    current run, identified producer, or successful-reproducer claim.
    """
    if '\0' in text: return False
    lines = text.splitlines()
    if len(lines) < 10: return False
    labels = ('tests', 'suites', 'pass', 'fail', 'cancelled', 'skipped', 'todo')
    counters = []
    for line, name in zip(lines[-8:-1], labels):
        match = re.fullmatch('ℹ ' + name + r' (0|[1-9][0-9]*)', line)
        if not match or len(match[1]) > 20: return False
        counters.append(int(match[1]))
    duration = re.fullmatch(r'ℹ duration_ms ([0-9]+(?:\.[0-9]+)?)', lines[-1])
    if not duration or not math.isfinite(float(duration[1])): return False
    cases = lines[:-8]
    for line in cases:
        match = re.fullmatch(r'[✔✖] [^\x00-\x1f]+ \(([0-9]+(?:\.[0-9]+)?)ms\)', line)
        if not match or not math.isfinite(float(match[1])): return False
    tests, suites, passed, failed, cancelled, skipped, todo = counters
    # This first reviewed subset has no suites, cancellations, skips or todos;
    # unsupported outcome forms remain unresolved rather than guessed.
    return (tests == len(cases) and tests >= 2 and suites == cancelled == skipped == todo == 0
            and passed == sum(line.startswith('✔ ') for line in cases)
            and failed == sum(line.startswith('✖ ') for line in cases))



def lake_build_transcript(text):
    """Reviewed Lake job/diagnostic output with an exact final build footer.

    Progress totals can change and cached jobs need not be displayed. This
    recognizes historical output content, not successful fresh validation or
    an identified command. Resource wrappers and partial output are excluded.
    """
    if '\0' in text: return False
    lines = text.splitlines()
    if len(lines) < 3: return False
    job = re.compile(r'[✔✖⚠] \[([1-9][0-9]{0,8})/([1-9][0-9]{0,8})\] (?:Built|Replayed) [A-Za-z_][A-Za-z_0-9]*(?:\.[A-Za-z_][A-Za-z_0-9]*)*(?: \(([0-9]+(?:\.[0-9]+)?)s\))?')
    if not job.fullmatch(lines[0]): return False
    footer = re.fullmatch(r'Build completed successfully \(([1-9][0-9]{0,8}) jobs\)\.', lines[-1])
    if not footer: return False
    jobs = set(); diagnostics = 0
    for line in lines[:-1]:
        if 'Build completed successfully' in line or 'All targets up-to-date' in line: return False
        match = job.fullmatch(line)
        if match:
            if not int(match[1]) <= int(match[2]) <= int(footer[1]) or match[3] is not None and not math.isfinite(float(match[3])): return False
            jobs.add(line)
        elif re.match(r'^[✔✖⚠] \[', line): return False
        if re.match(r'^(?:warning|info|error): [^\s:]+\.lean:[0-9]+:[0-9]+: ', line): diagnostics += 1
    return len(jobs) >= 2 and (diagnostics >= 1 or len(jobs) >= 3)



def unapplied_pin_comparison(value):
    """Historical prepare-pin-proposal.mjs:47 output, not pin adoption.

    Retained reports precede the current addition count/optional fields. Their
    source, generator and candidate identities are recorded claims only; this
    predicate neither reproduces nor authenticates external historical objects.
    """
    if not isinstance(value, dict): return False
    core = {'command', 'generator_sha256', 'source_head', 'base', 'shared_inventory',
            'shared_inventory_sha256', 'source_pins', 'source_pins_sha256', 'old_count',
            'added_count', 'candidate_count', 'old_entries_unchanged', 'before', 'after',
            'candidate_sha256', 'boundary'}
    if not core <= set(value) <= core | {'registry_base', 'external_unregistered_count'}: return False
    command = value['command']; producer = 'tests/h28-sol/non-vacuity/prepare-pin-proposal.mjs'
    if (not isinstance(command, list) or len(command) != 3
            or not all(isinstance(a, str) and a and '\0' not in a for a in command)
            or command[0] != 'node' or not (command[1] == producer or command[1].endswith('/' + producer))): return False
    if (value['shared_inventory'] != 'scripts/g07-axiom-pins.json'
            or value['source_pins'] != 'tests/h28-sol/non-vacuity/lean/Solidity/Assurance/NonVacuityH28/Pins.lean'
            or value['old_entries_unchanged'] is not True
            or not isinstance(value['boundary'], str) or not value['boundary'].startswith('UNAPPLIED proposal only.')): return False
    if not all(hex_pin(value[k]) for k in ('generator_sha256', 'shared_inventory_sha256', 'source_pins_sha256', 'candidate_sha256')): return False
    if not all(hex_pin(value[k], 40) for k in ('source_head', 'base')): return False
    if 'registry_base' in value and not hex_pin(value['registry_base'], 40): return False
    for key in ('old_count', 'added_count', 'candidate_count', 'external_unregistered_count'):
        if key in value and (type(value[key]) is not int or value[key] < 0): return False
    if value['old_count'] + value['added_count'] != value['candidate_count']: return False
    for key in ('before', 'after'):
        row = value[key]
        if (not isinstance(row, dict) or set(row) != {'errors', 'notes'}
                or not all(isinstance(row[k], list) and all(isinstance(a, str) for a in row[k]) for k in row)): return False
    return (not value['before']['errors'] and not value['after']['errors']
            and len(value['before']['notes']) - len(value['after']['notes']) == value['added_count'])


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
        if unapplied_pin_comparison(value):
            return 'Historical unapplied axiom-pin proposal comparison (prepare-pin-proposal.mjs:47): recorded identities, preserved-entry counts and comparison diagnostics; no adoption, current validation, external-object verification or reproduction claim.'
        if failed_validation_logs(value):
            return 'Historical failed-validation index: recorded nonzero run/gate exits, failed whitespace command and archived output digests; no per-log command/timing or current success claim.'
        if reviewed_receipt_rows(value):
            return 'Historical resource/validation command receipts: reviewed envelope, explicit commands, exit/timing/resource observations and output digests; no current validation credit.'
        reviewed = historical_json_role(value) or reviewed_archive_report(value)
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
    if lake_build_transcript(text):
        return 'Historical Lake build transcript: structured job progress, diagnostic context and terminal completion text; no verified fresh build success or command identity claim.'
    if flat_node_transcript(text):
        return 'Historical flat Node spec transcript: timed case results and complete, counter-consistent EOF summary; no current validation or producer identity claim.'
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

    A filename or prose mention is insufficient. Structured command receipts
    or reviewed failed-validation indexes must name the output and match its
    measured bytes. An index does not identify each log's command or timing;
    neither kind creates a live entry point.
    """
    roles = {}
    for source in sorted(repo.texts):
        try: value = json.loads(repo.texts[source])
        except (ValueError, RecursionError): continue
        if not evidence_role(repo.bytes(source)): continue
        standard = command_receipt_rows(value)
        rows = [(f'/{i}' if isinstance(value, list) else f'/commands/{i}', row) for i, row in enumerate(standard)]
        rows += reviewed_receipt_rows(value)
        failed_index = failed_validation_logs(value)
        rows += failed_index
        failed_pointers = {pointer for pointer, _ in failed_index}
        for pointer, row in rows:
            if not {'log'} <= set(row) or not isinstance(row['log'], str): continue
            digest = row.get('uncompressedLogSha256', row.get('uncompressedSha256', row.get('sha256')))
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
            if ('uncompressedLogSha256' in row or 'uncompressedSha256' in row) and data.startswith(b'\x1f\x8b'):
                try:
                    with gzip.GzipFile(fileobj=io.BytesIO(data)) as stream: data = stream.read(8_000_001)
                except (OSError, EOFError, zlib.error): continue
            if len(data) > 8_000_000 or hashlib.sha256(data).hexdigest() != digest: continue
            encoding = 'uncompressed' if 'uncompressedLogSha256' in row or 'uncompressedSha256' in row else 'stored-byte'
            role = 'Historical failed-validation indexed output' if pointer in failed_pointers else 'Historical command output'
            roles[target] = f'{role}: {source} {pointer} names this log; recorded {encoding} SHA256 matches measured bytes.'
    return roles



def archive_member_matches(data, name, digest):
    """Read bounded regular historical tar members in memory; never extract."""
    if len(data) > 8_000_000: return False
    try:
        with gzip.GzipFile(fileobj=io.BytesIO(data)) as stream: raw = stream.read(8_000_001)
        if len(raw) > 8_000_000: return False
        with tarfile.open(fileobj=io.BytesIO(raw), mode='r:') as archive:
            seen = set(); selected = None; count = 0; total = 0
            for member in archive:
                count += 1; total += member.size
                parts = member.name.rstrip('/').split('/')
                canonical_name = '/'.join(parts)
                if (count > 100 or total > 8_000_000 or canonical_name in seen
                        or not (member.isfile() or member.isdir()) or member.name.startswith('/')
                        or '\\' in member.name or any(p in ('', '.', '..') for p in parts)): return False
                seen.add(canonical_name)
                if member.name == name:
                    if not member.isfile(): return False
                    selected = archive.extractfile(member).read()
            return selected is not None and hashlib.sha256(selected).hexdigest() == digest
    except (OSError, EOFError, ValueError, tarfile.TarError, zlib.error): return False


def reviewed_historical_archive(repo, path):
    """Exact-blob exceptions independently inspected by finder and skeptic.

    The first archive is described in baseline README:98-104/build-archive.json;
    the second in its adjacent manifest.json:302-306 and verification JSON.
    Exact selected member digests make these role assertions re-checkable.
    Source/configuration snapshots coexist with receipts; no non-use, fresh
    integration, proof or regeneration claim follows. The mixed Terra frozen
    fixture archive is deliberately NOT included pending consumer resolution.
    """
    reviewed = {
        'tests/upstream/baseline-20261028/build-evidence.tar.gz': (
            'c01c878e924562b8e0f0b27b76f95f7dcd3cb64e',
            'tests/upstream/baseline-20261028/cold/logs/cold.json',
            '3ceaa3ca1cacbe33784d8e42bef6b7fc6743088f449218bdbd6b0da01a4d7b90',
            'Historical cold-build archive: selected cold.json records timeout exit 124; captured logs, resources and harness/configuration, not a passing build.'),
        'tests/upstream/diamond-payments-integration-20261030/coordinator-evidence.tar.gz': (
            '644af637d1feeffa91affc3e9b10c76d6c6f6d55',
            'context/3-investigation-b8355e59-controller-handoff.json',
            'd987a14ad2b21a57325c5221260e9a0b55a2e8a6620841e228262dcaf6351678',
            'Historical coordination/repair archive: selected controller handoff records integration_passed false; documentation comparisons, failed checks and read-only reviews, not a passing integration.')}
    if path not in reviewed: return None
    blob, member, digest, role = reviewed[path]
    if repo.tree.get(path) not in (('100644', 'blob', blob), ('100755', 'blob', blob)): return None
    if not archive_member_matches(repo.bytes(path), member, digest): return None
    return role + ' Exact reviewed Git blob and member ' + member + ' SHA256 ' + digest + ' verified.'



def reviewed_historical_notes(repo, definitions=None):
    """Per-file reviewed captured records, never a Markdown/directory rule.

    Exact blobs and literal anchors revoke role claims when content changes.
    Captured prompts/steering are data, not instructions or current permission.
    This creates no use-graph root or edge; live/uncertain consumers retain
    precedence. Definitions are classifier input, not current lane receipts.
    """
    if definitions is None:
        path = Path(__file__).with_name('check-tests-used-roles.json')
        if not path.exists(): return {}
        definitions = json.loads(path.read_bytes())
    if (not isinstance(definitions, dict) or set(definitions) != {'schema_version', 'records'}
            or type(definitions['schema_version']) is not int or definitions['schema_version'] != 1
            or not isinstance(definitions['records'], list)): raise ValueError('invalid historical note definitions')
    result = {}; seen = set()
    for row in definitions['records']:
        if not isinstance(row, dict) or set(row) != {'path', 'blob', 'anchor', 'role'}: raise ValueError('invalid historical note definition')
        path = row['path']
        if (not isinstance(path, str) or not path.startswith(SCOPE) or path in seen
                or not hex_pin(row['blob'], 40) or not isinstance(row['anchor'], str) or not row['anchor'].strip()
                or not isinstance(row['role'], str) or not row['role'].startswith('Historical record: ')):
            raise ValueError('unsupported historical note claim')
        seen.add(path)
        if repo.tree.get(path) not in (('100644', 'blob', row['blob']), ('100755', 'blob', row['blob'])): continue
        if row['anchor'] not in repo.texts.get(path, '').splitlines(): raise ValueError('historical note content anchor mismatch')
        result[path] = row['role'] + ' Exact reviewed Git blob and literal content anchor verified.'
    return result


def declared_configured_cli(repo, path):
    """Structural guard for curated CLI roles, never an automatic root finder.

    The catalog must separately pin/review a meaningful checker purpose. This
    narrow form has a local zero-argument main, direct argparse setup with
    required long options, and an explicit live main call. Its bare command is
    an entry prefix, not a working configured invocation. No reads propagate.
    """
    if path not in repo.texts or not path.endswith('.py') or repo.tree[path][0] not in ('100644', '100755'): return None
    try:
        tree = ast.parse(repo.texts[path]); compile(repo.texts[path], path, 'exec', dont_inherit=True)
    except (SyntaxError, ValueError, RecursionError): return None
    modules = {alias.asname or 'argparse' for node in tree.body if isinstance(node, ast.Import)
               for alias in node.names if alias.name == 'argparse'}
    functions = [node for node in tree.body if isinstance(node, ast.FunctionDef) and node.name == 'main']
    if not modules or len(functions) != 1: return None
    function = functions[0]; args = function.args
    if function.decorator_list: return None
    if args.posonlyargs or args.args or args.vararg or args.kwonlyargs or args.kwarg: return None
    protected = modules | {'__name__', 'main'}
    for node in ast.walk(tree):
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)) and node.name in protected and node is not function: return None
        if isinstance(node, ast.Name) and isinstance(node.ctx, (ast.Store, ast.Del)) and node.id in protected: return None
        if isinstance(node, ast.ImportFrom) and any(a.name == '*' or (a.asname or a.name) in protected for a in node.names): return None
        if isinstance(node, ast.Import):
            for alias in node.names:
                name = alias.asname or alias.name.split('.')[0]
                if name in protected and not (alias.name == 'argparse' and name in modules): return None
        if isinstance(node, ast.Attribute) and isinstance(node.ctx, (ast.Store, ast.Del)) and isinstance(node.value, ast.Name) and node.value.id in modules: return None
    def terminal(node):
        return (isinstance(node, ast.Raise) or isinstance(node, ast.Expr) and isinstance(node.value, ast.Call)
                and (isinstance(node.value.func, ast.Name) and node.value.func.id in ('exit', 'quit')
                     or isinstance(node.value.func, ast.Attribute) and node.value.func.attr in ('exit', '_exit')))
    def main_call(node):
        return node.value if isinstance(node, ast.Expr) and isinstance(node.value, ast.Call) and isinstance(node.value.func, ast.Name) and node.value.func.id == 'main' else None
    calls = []
    for index, node in enumerate(tree.body):
        if any(terminal(n) for n in tree.body[:index]): break
        call = main_call(node)
        if call is not None: calls.append(call); continue
        if not isinstance(node, ast.If) or not isinstance(node.test, ast.Compare): continue
        test = node.test
        if len(test.ops) != 1 or not isinstance(test.ops[0], ast.Eq) or len(test.comparators) != 1: continue
        pair = (test.left, test.comparators[0])
        if not (any(isinstance(n, ast.Name) and n.id == '__name__' for n in pair)
                and any(isinstance(n, ast.Constant) and n.value == '__main__' for n in pair)): continue
        for statement in node.body:
            if terminal(statement): break
            call = main_call(statement)
            if call is not None: calls.append(call)
    if not calls or calls[0].args or calls[0].keywords or function.lineno >= calls[0].lineno: return None
    parsers = {}
    for statement in function.body:
        if isinstance(statement, ast.Expr) and isinstance(statement.value, ast.Constant) and isinstance(statement.value.value, str): continue
        if isinstance(statement, ast.Assign) and len(statement.targets) == 1 and isinstance(statement.targets[0], ast.Name):
            value = statement.value; name = statement.targets[0].id
            if isinstance(value, ast.Call) and isinstance(value.func, ast.Attribute):
                owner = value.func.value
                if isinstance(owner, ast.Name) and owner.id in modules and value.func.attr == 'ArgumentParser':
                    parsers[name] = set(); continue
                if isinstance(owner, ast.Name) and owner.id in parsers and value.func.attr == 'parse_args' and not value.args and not value.keywords:
                    if not parsers[owner.id]: return None
                    return {'kind': 'curated local argparse entry', 'revision': repo.ref,
                            'function_line': function.lineno, 'main_line': calls[0].lineno,
                            'parse_args_line': statement.lineno, 'required_options': sorted(parsers[owner.id])}
            return None
        if isinstance(statement, ast.Expr) and isinstance(statement.value, ast.Call):
            call = statement.value; target = call.func
            if (isinstance(target, ast.Attribute) and isinstance(target.value, ast.Name)
                    and target.value.id in parsers and target.attr == 'add_argument'):
                required = [k.value for k in call.keywords if k.arg == 'required']
                if required and not (len(required) == 1 and isinstance(required[0], ast.Constant) and type(required[0].value) is bool): return None
                if required and required[0].value is True:
                    if len(call.args) != 1 or not isinstance(call.args[0], ast.Constant) or not isinstance(call.args[0].value, str) or not re.fullmatch(r'--[A-Za-z][A-Za-z0-9-]*', call.args[0].value): return None
                    parsers[target.value.id].add(call.args[0].value)
                continue
        # No unreviewed setup call, control branch or parser mutation before
        # parse_args may silently alter the declared configuration contract.
        return None
    return None


def reviewed_unittest_wildcard(repo, path, node):
    """One reviewed import, bound to BOTH exact committed source objects.

    The test's line5 inserts this precise helper directory; line6 imports the
    helper, then line9 explicitly imports unittest. The pinned helper has no
    __all__, magic-name assignments or top-level calls: only ordinary imports,
    a FIELDS constant and function declarations. This establishes runner-source
    structure, never passing validation, helper execution or fixture use.
    All other wildcard imports remain unresolved; changing either blob revokes
    this exception. Git object/content identity is established by Repository.
    """
    test = 'tests/h62/item2/audit-bytecode-selection/test_kernel_metadata.py'
    helper = 'scripts/h62/item2/audit-bytecode-selection/kernel_metadata.py'
    return (path == test and repo.tree.get(path) == ('100644', 'blob', 'a259a155420d7f88a902cee9745c7ee2942ae87d')
            and repo.tree.get(helper) == ('100644', 'blob', '2d86485ff102d8bf983e89a315a565d5cf05275d')
            and isinstance(node, ast.ImportFrom) and node.module == 'kernel_metadata'
            and node.level == 0 and node.lineno == 6 and len(node.names) == 1
            and node.names[0].name == '*' and node.names[0].asname is None)


def declared_unittest(repo, path):
    """Recognize a committed runner role without executing it or granting reads."""
    if path not in repo.texts or not path.endswith('.py') or repo.tree[path][0] not in ('100644', '100755'): return None
    text = repo.texts[path]
    try: tree = ast.parse(text)
    except (SyntaxError, ValueError, RecursionError): return None
    modules = set(); cases = set(); mains = set()
    for node in tree.body:
        if isinstance(node, ast.Import):
            modules.update(a.asname or 'unittest' for a in node.names
                           if a.name == 'unittest' or a.name.startswith('unittest.') and a.asname is None)
        elif isinstance(node, ast.ImportFrom) and node.module == 'unittest' and not node.level:
            cases.update(a.asname or a.name for a in node.names if a.name == 'TestCase')
            mains.update(a.asname or a.name for a in node.names if a.name == 'main')
    if not modules and not (cases and mains): return None
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
                if alias.name == '*' and not reviewed_unittest_wildcard(repo, path, node): shadowed = True
                if bound in bindings and not (node.module == 'unittest' and not node.level
                        and (alias.name == 'TestCase' and bound in cases or alias.name == 'main' and bound in mains)):
                    shadowed = True
    if modules & cases or modules & mains or cases & mains: shadowed = True
    if shadowed: return None
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
    if not classes: return None
    def main_call(statement):
        if not isinstance(statement, ast.Expr) or not isinstance(statement.value, ast.Call): return None
        func = statement.value.func
        return statement.value if (isinstance(func, ast.Name) and func.id in mains or isinstance(func, ast.Attribute)
                and func.attr == 'main' and isinstance(func.value, ast.Name) and func.value.id in modules) else None
    calls = []
    for index, node in enumerate(tree.body):
        direct = main_call(node)
        if direct is not None:
            if not any(terminal(n) for n in tree.body[:index]): calls.append(direct)
            continue
        if not isinstance(node, ast.If) or not isinstance(node.test, ast.Compare): continue
        test = node.test
        if len(test.ops) != 1 or not isinstance(test.ops[0], ast.Eq) or len(test.comparators) != 1: continue
        pair = (test.left, test.comparators[0])
        if not (any(isinstance(n, ast.Name) and n.id == '__name__' for n in pair)
                and any(isinstance(n, ast.Constant) and n.value == '__main__' for n in pair)): continue
        if any(terminal(n) for n in tree.body[:index]): continue
        for position, statement in enumerate(node.body):
            call = main_call(statement)
            if call is None or any(terminal(n) for n in node.body[:position]): continue
            calls.append(call)
    # The first recognized main is a boundary: its default exit prevents a
    # later call from rescuing classes that have not yet been declared.
    if not calls or not any(c.lineno < calls[0].lineno for c in classes): return None
    classes = [c for c in classes if c.lineno < calls[0].lineno]
    try: compile(text, path, 'exec', dont_inherit=True)
    except (SyntaxError, ValueError, RecursionError, OverflowError): return None
    methods = [m for c in classes for m in c.body if isinstance(m, (ast.FunctionDef, ast.AsyncFunctionDef))
               and (m.name.startswith('test_') or m.name in ('setUp', 'tearDown', 'setUpClass', 'tearDownClass'))]
    return {'kind': 'unittest declaration and explicit main entry', 'revision': repo.ref,
            'class_lines': [c.lineno for c in classes], 'main_line': calls[0].lineno,
            'test_contexts': [{'name': m.name, 'qualname': c.name + '.' + m.name,
                'code_firstlineno': min([m.lineno] + [d.lineno for d in m.decorator_list]),
                'first': m.body[0].lineno, 'last': m.end_lineno} for c in classes for m in c.body if m in methods]}


def add_declared_test_runners(graph):
    """H490 source-only roots; no fixture, child or passing-reproducer credit."""
    repo = graph.repo
    existing = {v['path'] for v in graph.roots.values()}
    for path in sorted(repo.texts):
        if path in existing: continue
        declaration = declared_unittest(repo, path)
        if declaration is None: continue
        identity = 'committed:' + path
        graph.root(path, 'committed standalone test runner', shlex.join(['python3', '-B', path]), path,
                   declaration['main_line'], root_id=identity)
        graph.roots[identity].update({'source_only': True, 'source_blob': repo.tree[path][2],
            'role_provenance': declaration,
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
    historical.update(reviewed_historical_notes(repo))
    # Search coverage is explicitly broader than the certified use graph. A
    # textual hit is negative-evidence context, not a consumer certification.
    names = collections.defaultdict(list)
    for p in repo.paths:
        base = posixpath.basename(p)
        names[base].append(p)
        stem, suffix = posixpath.splitext(base)
        if suffix in ('.py', '.lean', '.mjs', '.js', '.cjs'):
            # Module imports omit source extensions. This broadens SEARCH only;
            # it never certifies invocation, consumption or orphan eligibility.
            for spelling in {stem, p[:-len(suffix)].replace('/', '.')}:
                if spelling != base: names[spelling].append(p)
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
        historical_role = historical.get(p) or reviewed_historical_archive(repo, p) or (evidence_role(repo.bytes(p)) if kind == 'blob' and mode != '120000' else None)
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
            reason = 'An observed entry point read this object; fixture-specific versus secondary-scan eligibility needs review. Independent historical/generated properties are retained.'
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
                                'candidates': 'Basename/module-stem/module-name token search plus exact unusual-name and escaped-literal search, with source line locations; capped at eight samples per path.',
                                'limitations': ['Under-approximate use graph; no automatic script execution.',
                                                'Unresolved dynamic shell/Python/Node dispatch prevents a complete classification.',
                                                'No orphan or regenerable classification inferred from an absent static edge.',
                                                'Recovery: topological first matching authored change or combined-diff merge resolution; no rename following.']},
            'records': records}


def verify(actual, expected, require_complete=True):
    if not isinstance(actual, dict): raise ValueError('inventory must be an object')
    if type(actual.get('schema_version')) is not int or actual['schema_version'] != SCHEMA: raise ValueError('schema version mismatch')
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
    # JSON distinguishes booleans, integers and floats; Python equality does not.
    if canonical(actual) != canonical(expected): raise ValueError('classification provenance, recovery pin, ordering or schema differs from rebuilt model')
    if require_complete and expected['analysis_gaps']:
        raise ValueError('unresolved analysis: ' + '; '.join(expected['analysis_gaps']))
    if require_complete and expected['totals']['unresolved']:
        raise ValueError(f"incomplete classification: {expected['totals']['unresolved']} unresolved paths")
    if sum(expected['totals'][c] for c in CLASSES) != len(wanted):
        if require_complete: raise ValueError('four-class totals do not equal universe')



def nonpassing_boundary_controls():
    import copy
    with tempfile.TemporaryDirectory(prefix='tests-used-failed-controls-') as directory:
        root = Path(directory)
        sources = {'tests/data.txt': 'actual', 'tests/other.txt': 'unreviewed',
            'tests/helper.py': 'from pathlib import Path\ndef read(): return Path("tests/data.txt").read_text()\n',
            'tests/failure.py': 'import unittest\nfrom helper import read\nclass T(unittest.TestCase):\n def test_input(self):\n  self.assertEqual(read(), "expected")\nif __name__ == "__main__": unittest.main()\n',
            'tests/bootstrap.py': 'import unittest\nfrom pathlib import Path\nPath("tests/data.txt").read_text()\nassert False, "bootstrap"\nclass T(unittest.TestCase):\n def test_input(self): pass\nif __name__ == "__main__": unittest.main()\n',
            'tests/plain.py': 'from pathlib import Path\nPath("tests/data.txt").read_text()\nassert False\n'}
        for path, text in sources.items():
            target = root / path; target.parent.mkdir(exist_ok=True, parents=True); target.write_text(text)
        git(root, 'init', '-q'); git(root, 'add', '.')
        git(root, '-c', 'user.name=Control', '-c', 'user.email=control@example.invalid', 'commit', '-qm', 'failed controls')
        repo = Repository(root, 'HEAD'); runner = 'tests/failure.py'
        assert subprocess.run(['python3', '-B', runner], cwd=root, capture_output=True).returncode == 1
        entry = {'path': runner, 'source_blob': repo.tree[runner][2], 'input_revision': repo.ref,
                 'command': ['python3', '-B', runner], 'kind': 'nonpassing-unittest',
                 'purpose': 'A real test reads this specific fixture and then fails its assertion.', 'input_scope': ['tests/data.txt']}
        route = {'runner': 'nonpassing:' + runner, 'input_revision': repo.ref,
                 'frames': [{'path': path, 'blob': repo.tree[path][2], 'line': line, 'code_qualname': name, 'code_firstlineno': first}
                            for path, line, name, first in [(runner, 6, '<module>', 1), (runner, 5, 'T.test_input', 4), ('tests/helper.py', 2, 'read', 2)]],
                 'target': 'tests/data.txt', 'target_blob': repo.tree['tests/data.txt'][2],
                 'operation': 'Observed fixture read during nonpassing unittest'}
        catalog = {'schema_version': 1, 'standalone': [entry], 'reads': [route], 'generators': [], 'orphans': []}
        result = inventory(repo, catalog); rows = {r['path']: r for r in result['records']}
        assert rows['tests/data.txt']['class'] == rows['tests/helper.py']['class'] == 'keep'
        chain = rows['tests/data.txt']['runner_chain']; assert chain['entry']['source_only']
        assert chain['entry']['validation_at_measured_revision']['status'] == 'failed'
        assert chain['entry']['kind'] == 'nonpassing committed unittest runner'
        graph = Graph(repo); validated_routes(graph, catalog)
        graph.edge(runner, 'tests/other.txt', 1, 'Unsupported inferred fixture edge', validated_for='nonpassing:' + runner)
        assert 'tests/other.txt' not in graph.chains()
        execution_only = copy.deepcopy(catalog); execution_only['standalone'][0]['input_scope'] = []
        execution_rows = {r['path']: r for r in inventory(repo, execution_only)['records']}
        assert execution_rows['tests/helper.py']['class'] == 'keep' and execution_rows['tests/data.txt']['class'] is None
        outside = copy.deepcopy(catalog); outside['reads'][0].update(target='tests/other.txt', target_blob=repo.tree['tests/other.txt'][2])
        outside_rows = {r['path']: r for r in inventory(repo, outside)['records']}
        assert outside_rows['tests/other.txt']['class'] is None and outside_rows['tests/other.txt']['secondary']['unreviewed_readers']
        assert outside_rows['tests/helper.py']['class'] == 'keep'
        root_only = copy.deepcopy(outside); root_only['reads'][0]['frames'] = root_only['reads'][0]['frames'][:2]
        root_rows = {r['path']: r for r in inventory(repo, root_only)['records']}
        assert root_rows['tests/other.txt']['class'] is None and root_rows['tests/helper.py']['class'] is None
        data_only = copy.deepcopy(root_only); data_only['reads'][0].update(target='tests/helper.py', target_blob=repo.tree['tests/helper.py'][2])
        assert next(r for r in inventory(repo, data_only)['records'] if r['path'] == 'tests/helper.py')['class'] is None
        for scenario in ('bootstrap', 'plain', 'operation', 'command', 'no-test-context', 'nested-code'):
            bad = copy.deepcopy(catalog)
            if scenario in ('bootstrap', 'plain'):
                source = 'tests/' + scenario + '.py'; bad['standalone'][0].update(path=source, source_blob=repo.tree[source][2], command=['python3', '-B', source])
                bad['reads'][0]['runner'] = 'nonpassing:' + source
                bad['reads'][0]['frames'] = [{'path': source, 'blob': repo.tree[source][2], 'line': 3 if scenario == 'bootstrap' else 2, 'code_qualname': '<module>', 'code_firstlineno': 1}]
            elif scenario == 'operation': bad['reads'][0]['operation'] = 'validated Python read of measured bytes'
            elif scenario == 'command': bad['standalone'][0]['command'].append('--help')
            elif scenario == 'nested-code': bad['reads'][0]['frames'][1]['code_qualname'] = 'T.test_input.<locals>.escaped'
            else: bad['reads'][0]['frames'] = [bad['reads'][0]['frames'][0]]
            try: inventory(repo, bad)
            except ValueError: pass
            else: raise AssertionError('unsupported nonpassing route accepted: ' + scenario)



def passing_scan_boundary_controls():
    import copy
    with tempfile.TemporaryDirectory(prefix='tests-used-scan-controls-') as directory:
        root = Path(directory)
        text = 'import unittest\nfrom pathlib import Path\nclass T(unittest.TestCase):\n def test_scan(self):\n  values=[p.read_text() for p in Path("tests/scanned").rglob("*") if p.is_file()]\n  self.assertTrue(values)\nif __name__ == "__main__": unittest.main()\n'
        sources = {'tests/scan.py': text, 'tests/scanned/receipt.json': json.dumps({
            'command': ['old-run'], 'exit': 7, 'elapsed_seconds': 1, 'resource_stop': False, 'peak_group_rss_bytes': 1})}
        for path, value in sources.items():
            target = root/path; target.parent.mkdir(parents=True, exist_ok=True); target.write_text(value)
        git(root, 'init', '-q'); git(root, 'add', '.')
        git(root, '-c', 'user.name=Control', '-c', 'user.email=control@example.invalid', 'commit', '-qm', 'scan control')
        repo = Repository(root, 'HEAD'); runner = 'tests/scan.py'; target = 'tests/scanned/receipt.json'
        assert subprocess.run(['python3', '-B', runner], cwd=root, capture_output=True).returncode == 0
        catalog = {'schema_version': 1, 'generators': [], 'orphans': [], 'standalone': [{
            'path': runner, 'input_revision': repo.ref, 'source_blob': repo.tree[runner][2],
            'command': ['python3', '-B', runner], 'kind': 'unittest'}], 'reads': [{
            'runner': 'validated:' + runner, 'input_revision': repo.ref,
            'frames': [{'path': runner, 'blob': repo.tree[runner][2], 'line': 5}],
            'target': target, 'target_blob': repo.tree[target][2], 'operation': 'validated Python read of measured bytes'}]}
        rows = {r['path']: r for r in inventory(repo, catalog)['records']}
        assert rows[runner]['class'] == 'keep' and rows[target]['class'] is None
        assert rows[target]['secondary']['unreviewed_readers'] and rows[target]['secondary']['historical_role']
        secondary = copy.deepcopy(catalog); secondary['standalone'][0].update(input_scope=[],
            purpose='Reviewed blanket count-policy scan; no fixture-specific consumer is claimed.', other_reads='secondary')
        rows = {r['path']: r for r in inventory(repo, secondary)['records']}
        assert rows[target]['class'] == 'evidence' and not rows[target]['runner_chain']


def configured_cli_boundary_controls():
    import copy
    with tempfile.TemporaryDirectory(prefix='tests-used-cli-controls-') as directory:
        root = Path(directory)
        text = 'import argparse\nfrom pathlib import Path\ndef main():\n p=argparse.ArgumentParser()\n p.add_argument("--input", required=True)\n a=p.parse_args()\n assert Path(a.input).read_text()=="fixture\\n"\nif __name__ == "__main__": main()\n'
        variants = {
            'valid': text,
            'dead': text.replace('if __name__ == "__main__":', 'if False:'),
            'nested': text.replace('if __name__ == "__main__": main()', 'def never(): main()'),
            'early-exit': text.replace('if __name__', 'import sys\nsys.exit(0)\nif __name__'),
            'shadow-module': text.replace('from pathlib', 'import json as argparse\nfrom pathlib'),
            'shadow-main': text.replace('if __name__', 'main=lambda:None\nif __name__'),
            'parser-mutation': text.replace(' a=p.parse_args()', ' p.parse_args=lambda:None\n a=p.parse_args()'),
            'different-parser': text.replace(' a=p.parse_args()', ' q=argparse.ArgumentParser()\n a=q.parse_args()'),
            'no-parser': 'def main(): pass\nif __name__ == "__main__": main()\n',
            'class-main': text.replace('if __name__', 'class main: pass\nif __name__'),
            'function-argparse': text.replace('def main():', 'def argparse(): pass\ndef main():'),
            'class-argparse': text.replace('def main():', 'class argparse: pass\ndef main():'),
            'class-magic-name': text.replace('if __name__', 'class __name__: pass\nif __name__'),
            'function-magic-name': text.replace('if __name__', 'def __name__(): pass\nif __name__'),
            'decorated-main': text.replace('def main():', '@replace_checker\ndef main():'),
        }
        for name, source in variants.items():
            target = root/('scripts/h55/' + name + '.py'); target.parent.mkdir(parents=True, exist_ok=True); target.write_text(source)
        (root/'tests').mkdir(); (root/'tests/input.txt').write_text('fixture\n')
        git(root, 'init', '-q'); git(root, 'add', '.')
        git(root, '-c', 'user.name=Control', '-c', 'user.email=control@example.invalid', 'commit', '-qm', 'CLI controls')
        repo = Repository(root, 'HEAD'); path = 'scripts/h55/valid.py'; declaration = declared_configured_cli(repo, path)
        assert declaration and declaration['required_options'] == ['--input']
        refusal = subprocess.run(['python3', '-B', path], cwd=root, capture_output=True)
        assert refusal.returncode == 2 and b'--input' in refusal.stderr
        entry = {'path': path, 'input_revision': repo.ref, 'source_blob': repo.tree[path][2],
                 'command': ['python3', '-B', path], 'kind': 'committed-cli',
                 'entry_line': declaration['main_line'], 'required_options': ['--input'],
                 'purpose': 'Curated input-checker source; configured invocation not validated.'}
        catalog = {'schema_version': 1, 'standalone': [entry], 'generators': [], 'reads': [], 'orphans': []}
        model = inventory(repo, catalog); rows = {r['path']: r for r in model['records']}; source = rows[path]['runner_chain']['entry']
        assert rows[path]['class'] == 'keep' and source['source_only']
        assert source['command_form'].startswith('entry prefix') and source['required_options'] == ['--input']
        assert source['validation_at_measured_revision']['status'] == 'unavailable'
        assert rows['tests/input.txt']['class'] is None
        graph = Graph(repo); validated_routes(graph, catalog)
        graph.edge(path, 'tests/input.txt', 7, 'unreviewed configured read')
        assert 'tests/input.txt' not in graph.chains()
        for name in variants:
            if name == 'valid': continue
            candidate = 'scripts/h55/' + name + '.py'; assert declared_configured_cli(repo, candidate) is None, name
            bad = copy.deepcopy(catalog); bad['standalone'][0].update(path=candidate, source_blob=repo.tree[candidate][2], command=['python3', '-B', candidate])
            try: inventory(repo, bad)
            except ValueError: pass
            else: raise AssertionError('unsupported CLI role accepted: ' + name)
        for field, value in (('entry_line', 1), ('required_options', ['--invented']), ('source_blob', '0' * 40),
                             ('command', ['python3', '-B', path, '--input', 'tests/input.txt'])):
            bad = copy.deepcopy(catalog); bad['standalone'][0][field] = value
            try: inventory(repo, bad)
            except ValueError: pass
            else: raise AssertionError('unsupported CLI command/provenance accepted')
        bad = copy.deepcopy(catalog); bad['reads'] = [{'runner': 'committed-cli:' + path, 'input_revision': repo.ref,
            'frames': [{'path': path, 'blob': repo.tree[path][2], 'line': 7}], 'target': 'tests/input.txt',
            'target_blob': repo.tree['tests/input.txt'][2], 'operation': 'validated Python read of measured bytes'}]
        try: inventory(repo, bad)
        except ValueError as error: assert 'no validated runner' in str(error)
        else: raise AssertionError('CLI source-only root granted observed-read credit')


def skipped_runner_boundary_controls():
    import copy
    with tempfile.TemporaryDirectory(prefix='tests-used-skipped-controls-') as directory:
        root = Path(directory)
        programs = {
            'tests/skipped.py': 'import unittest\n@unittest.skip("optional backend unavailable")\nclass T(unittest.TestCase):\n def test_value(self): self.fail("must not execute")\nif __name__ == "__main__": unittest.main()\n',
            'tests/partial.py': 'import unittest\nclass T(unittest.TestCase):\n def test_active(self): self.assertEqual(1 + 1, 2)\n @unittest.skip("optional backend unavailable")\n def test_skipped(self): self.fail("must not execute")\nif __name__ == "__main__": unittest.main()\n',
            'tests/helper.py': 'def helper(): return 1\n',
            'tests/input.txt': 'fixture\n',
        }
        for path, source in programs.items():
            target = root/path; target.parent.mkdir(parents=True, exist_ok=True); target.write_text(source)
        git(root, 'init', '-q'); git(root, 'add', '.')
        git(root, '-c', 'user.name=Control', '-c', 'user.email=control@example.invalid', 'commit', '-qm', 'skip controls')
        repo = Repository(root, 'HEAD')
        for path, count in (('tests/skipped.py', 1), ('tests/partial.py', 2)):
            run = subprocess.run(['python3', '-B', path], cwd=root, capture_output=True)
            assert run.returncode == 0 and b'skipped=1' in run.stderr
            assert re.search(rb'Ran ' + str(count).encode() + rb' tests? in ', run.stderr)
        path = 'tests/skipped.py'
        entry = {'path': path, 'input_revision': repo.ref, 'source_blob': repo.tree[path][2],
                 'command': ['python3', '-B', path], 'kind': 'skipped-unittest',
                 'purpose': 'All cases skipped; committed runner source only, no exercised test validation.'}
        catalog = {'schema_version': 1, 'standalone': [entry], 'generators': [], 'reads': [], 'orphans': []}
        model = inventory(repo, catalog); rows = {r['path']: r for r in model['records']}
        source = rows[path]['runner_chain']['entry']
        assert rows[path]['class'] == 'keep' and source['source_only']
        assert source['validation_at_measured_revision']['status'] == 'unavailable'
        graph = Graph(repo); validated_routes(graph, catalog)
        graph.edge(path, 'tests/helper.py', 5, 'unrelated static invocation', kind='executes')
        assert 'tests/helper.py' not in graph.chains()
        for identity in ('skipped:' + path, 'validated:' + path):
            bad = copy.deepcopy(catalog)
            bad['reads'] = [{'runner': identity, 'input_revision': repo.ref,
                'frames': [{'path': path, 'blob': repo.tree[path][2], 'line': 5}],
                'target': 'tests/input.txt', 'target_blob': repo.tree['tests/input.txt'][2],
                'operation': 'validated Python read of measured bytes'}]
            try: inventory(repo, bad)
            except ValueError as error: assert 'no validated runner' in str(error)
            else: raise AssertionError('all-skipped root granted read credit')
        for field, value in (('source_blob', '0' * 40), ('kind', 'invented-skipped-kind')):
            bad = copy.deepcopy(catalog); bad['standalone'][0][field] = value
            try: inventory(repo, bad)
            except ValueError: pass
            else: raise AssertionError('unsupported skipped definition accepted')
        stale = copy.deepcopy(catalog); stale['standalone'][0]['input_revision'] = '0' * 40
        graph = Graph(repo); validated_routes(graph, stale); assert not graph.roots
        partial = 'tests/partial.py'
        catalog['standalone'].append({'path': partial, 'input_revision': repo.ref,
            'source_blob': repo.tree[partial][2], 'command': ['python3', '-B', partial], 'kind': 'unittest'})
        rows = {r['path']: r for r in inventory(repo, catalog)['records']}
        assert rows[partial]['runner_chain']['entry']['kind'] == 'validated standalone runner'
        assert not rows[partial]['runner_chain']['entry'].get('source_only')


def self_test():
    if not __debug__: raise ValueError("self-test requires Python assertions; omit -O")
    import copy
    skipped_runner_boundary_controls()
    configured_cli_boundary_controls()
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
    intake = {'guardedRegression': 'Historical sourceBuild1e8 intake is not current H90 qualification',
              'inputDirectory': '/external/archive', 'inputs': {k: 'a' * 64 for k in ('evidence.tar.gz', 'runtime-artifacts.tar.gz', 'files.json')},
              'evidenceFiles': 505, 'recordedSourceModules': 343, 'recordedSourceArraysEqual': True,
              'binaries': {k: {'sha256': 'b' * 64, 'bytes': 10} for k in ('native/direct-check', 'direct/direct.wasm', 'direct/direct.js')},
              'gitSourceIdentityVerified': False, 'execution': False, 'extraction': False, 'boundary': 'Archive consistency only.'}
    assert reviewed_archive_report(intake)
    for key, bad in (('execution', True), ('evidenceFiles', True), ('inputs', {'files.json': 'a' * 64}), ('binaries', {})):
        assert reviewed_archive_report(dict(intake, **{key: bad})) is None
    occurrence = {'checkpoint': 'Historical control observation',
                  'command': 'PYTHONDONTWRITEBYTECODE=1 python3 tests/directruntime-20261104/shared-translator/occurrence-integrity-controls.py',
                  'exit': 0, 'wallSeconds': 1.25, 'boundary': 'No Lean proof.',
                  'results': {'boundary': 'External controls only.', 'controls': [{'case': 'healthy', 'result': 'accepted'}]
                      + [{'case': name, 'result': 'rejected', 'line': 14} for name in ('missing-occurrence', 'case-identity', 'pointer', 'node-hash', 'route')]},
                  'bulk': [{'path': '/external/controls.json', 'bytes': 20, 'sha256': 'c' * 64}]}
    assert reviewed_archive_report(occurrence)
    for key, bad in (('exit', False), ('wallSeconds', float('nan')), ('bulk', []), ('command', 'echo expected')):
        assert reviewed_archive_report(dict(occurrence, **{key: bad})) is None
    expected_cases = copy.deepcopy(occurrence); expected_cases['results']['controls'][1]['result'] = 'expected'
    assert reviewed_archive_report(expected_cases) is None
    duplicate_case = copy.deepcopy(occurrence); duplicate_case['results']['controls'][2]['case'] = 'healthy'
    assert reviewed_archive_report(duplicate_case) is None
    # Exercise the narrow exception's revocation boundary without executing
    # either real source. Repository's object/content binding is tested below.
    import types
    wildcard_test = 'tests/h62/item2/audit-bytecode-selection/test_kernel_metadata.py'
    wildcard_helper = 'scripts/h62/item2/audit-bytecode-selection/kernel_metadata.py'
    wildcard_tree = {wildcard_test: ('100644', 'blob', 'a259a155420d7f88a902cee9745c7ee2942ae87d'),
                     wildcard_helper: ('100644', 'blob', '2d86485ff102d8bf983e89a315a565d5cf05275d')}
    wildcard_node = ast.parse('\n' * 5 + 'from kernel_metadata import *').body[0]
    assert reviewed_unittest_wildcard(types.SimpleNamespace(tree=wildcard_tree), wildcard_test, wildcard_node)
    for path in (wildcard_test, wildcard_helper):
        changed = dict(wildcard_tree); changed[path] = ('100644', 'blob', '0' * 40)
        assert not reviewed_unittest_wildcard(types.SimpleNamespace(tree=changed), wildcard_test, wildcard_node)
    assert not reviewed_unittest_wildcard(types.SimpleNamespace(tree=wildcard_tree), wildcard_test,
                                         ast.parse('from kernel_metadata import *').body[0])
    failed_log = gzip.compress(b'', mtime=0)
    failed_index = {'exitCode': 1, 'failedGate': ['git', 'diff', '--cached', '--check'], 'failedGateExitCode': 2,
                    'reason': 'Initial whitespace failure; exact archived outputs retained.',
                    'logs': [{'path': 'initial-failed.log.gz', 'sha256': hashlib.sha256(failed_log).hexdigest()}]}
    assert failed_validation_logs(failed_index) and evidence_role(json.dumps(failed_index).encode())
    lake_text = '⚠ [2/8] Built Solidity.AST (11s)\nwarning: Solidity/AST.lean:354:4: unused variable `k`\nbody of diagnostic\n✔ [77/77] Built Solidity.Tools.Upstream (4.2s)\nBuild completed successfully (77 jobs).\n'
    assert lake_build_transcript(lake_text) and evidence_role(lake_text.encode())
    assert evidence_role(gzip.compress(lake_text.encode()))
    for bad in (lake_text.rsplit('Build completed', 1)[0], '```\n' + lake_text + '```\n',
                lake_text + 'trailing source\n', lake_text + lake_text,
                lake_text.replace('[2/8]', '[9/8]'), lake_text.replace('[2/8]', '[0/8]'),
                lake_text.replace('[2/8]', '[2/88]'),
                lake_text.replace('✔ [77/77] Built Solidity.Tools.Upstream (4.2s)', '⚠ [2/8] Built Solidity.AST (11s)'),
                lake_text.replace('[2/8]', '[999999999999/999999999999]'),
                lake_text.replace('(11s)', '(NaNs)'), lake_text.replace('(11s)', '(' + '9' * 5000 + 's)'),
                lake_text.replace('Solidity.AST', 'Solidity.AST\x00'),
                lake_text.replace('Build completed successfully (77 jobs).', 'Build completed successfully (0 jobs).')):
        assert not lake_build_transcript(bad), repr(bad)
    node_text = '✔ first (1.2ms)\n✔ second (0ms)\nℹ tests 2\nℹ suites 0\nℹ pass 2\nℹ fail 0\nℹ cancelled 0\nℹ skipped 0\nℹ todo 0\nℹ duration_ms 3.4\n'
    assert flat_node_transcript(node_text) and evidence_role(node_text.encode())
    assert flat_node_transcript(node_text.replace('✔ second', '✖ second').replace('ℹ pass 2', 'ℹ pass 1').replace('ℹ fail 0', 'ℹ fail 1'))
    assert evidence_role(gzip.compress(node_text.encode()))
    for bad in (node_text.rsplit('ℹ duration_ms', 1)[0], node_text + 'source wrapper\n', '```\n' + node_text + '```\n',
                node_text.replace('ℹ tests 2', 'ℹ tests 3'), node_text.replace('ℹ fail 0', 'ℹ fail 1'),
                node_text.replace('3.4', 'NaN'), node_text.replace('3.4', 'Infinity'),
                node_text.replace('ℹ suites 0', 'ℹ suites -1'), node_text.replace('ℹ todo 0', 'ℹ todo 1'),
                node_text.replace('ℹ tests 2', 'ℹ tests ' + '9' * 5000),
                node_text.replace('1.2ms', '9' * 5000 + 'ms'),
                node_text + node_text, 'prefix\n' + node_text, node_text.replace('first', 'first\x00')):
        assert not flat_node_transcript(bad), repr(bad)
    attributed_failure = dict(failed_index, status='failed-whitespace-check', command=['python3', 'tests/upstream/baseline-20261028/attribution/validate.py'])
    assert failed_validation_logs(attributed_failure)
    for field, bad in (('exitCode', 0), ('exitCode', True), ('failedGateExitCode', False),
                       ('failedGate', ['echo', 'expected']), ('reason', ' '), ('logs', [])):
        assert not failed_validation_logs(dict(failed_index, **{field: bad}))
    for path in ('/external/log.gz', '../log.gz', 'C:/external/log.gz', 'bad\0name', 'a//log.gz'):
        assert not failed_validation_logs(dict(failed_index, logs=[{'path': path, 'sha256': 'a' * 64}]))
    assert not failed_validation_logs(dict(failed_index, logs=failed_index['logs'] * 2))
    assert not failed_validation_logs(dict(attributed_failure, command=['python3', 'obsolete.py']))
    assert not failed_validation_logs(dict(failed_index, expectedExitCode=1))
    proposal = {'command': ['node', 'tests/h28-sol/non-vacuity/prepare-pin-proposal.mjs', 'private-output'],
        'generator_sha256': 'a' * 64, 'source_head': 'b' * 40, 'base': 'c' * 40,
        'shared_inventory': 'scripts/g07-axiom-pins.json', 'shared_inventory_sha256': 'd' * 64,
        'source_pins': 'tests/h28-sol/non-vacuity/lean/Solidity/Assurance/NonVacuityH28/Pins.lean',
        'source_pins_sha256': 'e' * 64, 'old_count': 3, 'added_count': 2, 'candidate_count': 5,
        'old_entries_unchanged': True, 'before': {'errors': [], 'notes': ['new pin one', 'new pin two']},
        'after': {'errors': [], 'notes': []}, 'candidate_sha256': 'f' * 64, 'boundary': 'UNAPPLIED proposal only.'}
    assert unapplied_pin_comparison(proposal) and evidence_role(json.dumps(proposal).encode())
    assert unapplied_pin_comparison(dict(proposal, registry_base='1' * 40, external_unregistered_count=7))
    for field, bad in (('command', ['node', 'prepare-pin-proposal.mjs', 'out']),
                       ('command', ['node', 'tests/h28-sol/non-vacuity/prepare-pin-proposal.mjs']),
                       ('source_head', 'partial'), ('generator_sha256', 'missing'), ('registry_base', 'bad'),
                       ('old_count', True), ('added_count', -1), ('candidate_count', 4),
                       ('old_entries_unchanged', False), ('shared_inventory', 'other.json'),
                       ('source_pins', 'other.lean'), ('before', {'errors': [], 'notes': 'expected'}),
                       ('after', {'expected': 'pass'}), ('after', {'errors': ['failure'], 'notes': []}),
                       ('before', {'errors': [], 'notes': []}),
                       ('boundary', 'Applied successfully'), ('extra', 'unsupported')):
        assert not unapplied_pin_comparison(dict(proposal, **{field: bad})), field
    missing = dict(proposal); del missing['candidate_sha256']; assert not unapplied_pin_comparison(missing)
    def control_archive(entries):
        output = io.BytesIO()
        with tarfile.open(fileobj=output, mode='w:gz') as archive:
            for name, data, kind in entries:
                member = tarfile.TarInfo(name); member.type = kind
                member.size = len(data) if kind == tarfile.REGTYPE else 0
                if kind == tarfile.SYMTYPE: member.linkname = 'elsewhere'
                archive.addfile(member, io.BytesIO(data) if kind == tarfile.REGTYPE else None)
        return output.getvalue()
    body = b'{"historical":true}\n'; member_sha = hashlib.sha256(body).hexdigest()
    archive_bytes = control_archive([('records/result.json', body, tarfile.REGTYPE)])
    assert archive_member_matches(archive_bytes, 'records/result.json', member_sha)
    assert not archive_member_matches(archive_bytes, 'records/result.json', '0' * 64)
    assert not archive_member_matches(archive_bytes, 'missing.json', member_sha)
    for entries in ([('records/result.json', body, tarfile.REGTYPE)] * 2,
                    [('records/result.json', b'', tarfile.SYMTYPE)],
                    [('../escape', body, tarfile.REGTYPE)], [('/absolute', body, tarfile.REGTYPE)],
                    [('records/result.json', body, tarfile.REGTYPE), ('special', b'', tarfile.FIFOTYPE)],
                    [('records/result.json', body, tarfile.REGTYPE), ('dir', b'', tarfile.DIRTYPE), ('dir/', b'', tarfile.DIRTYPE)]):
        assert not archive_member_matches(control_archive(entries), 'records/result.json', member_sha)
    assert not archive_member_matches(b'not a gzip archive', 'records/result.json', member_sha)
    assert not archive_member_matches(gzip.compress(b'x' * 8_000_001), 'records/result.json', member_sha)
    from types import SimpleNamespace
    note_path = 'tests/captured-prompt.md'; note_blob = 'c' * 40
    note_repo = SimpleNamespace(tree={note_path: ('100644', 'blob', note_blob)}, texts={note_path: '# Captured old assignment\nDo the old work.\n'})
    note_row = {'path': note_path, 'blob': note_blob, 'anchor': '# Captured old assignment',
                'role': 'Historical record: captured assignment, not current instructions.'}
    note_defs = {'schema_version': 1, 'records': [note_row]}
    assert note_path in reviewed_historical_notes(note_repo, note_defs)
    assert not reviewed_historical_notes(note_repo, dict(note_defs, records=[dict(note_row, blob='0' * 40)]))
    for bad in (dict(note_defs, records=[note_row, note_row]), dict(note_defs, schema_version=True),
                dict(note_defs, records=[dict(note_row, anchor='# Not in source')]),
                dict(note_defs, records=[dict(note_row, path='outside.md')]),
                dict(note_defs, records=[dict(note_row, role='Keep because filename')]),
                dict(note_defs, records=[dict(note_row, blob='partial')]),
                dict(note_defs, records=[dict(note_row, extra='unsupported')])):
        try: reviewed_historical_notes(note_repo, bad)
        except ValueError: pass
        else: raise AssertionError('unsupported historical prose claim accepted')
    typed_expected = {'schema_version': 1, 'measured_revision': 'a' * 40, 'records': [],
                      'analysis_gaps': [], 'totals': {**{c: 0 for c in CLASSES}, 'unresolved': 0, 'paths': 0}}
    verify(typed_expected, typed_expected)
    for bad in (dict(typed_expected, schema_version=True), dict(typed_expected, schema_version=1.0),
                dict(typed_expected, totals=dict(typed_expected['totals'], unresolved=False)),
                dict(typed_expected, totals=dict(typed_expected['totals'], paths=0.0))):
        try: verify(bad, typed_expected)
        except ValueError: pass
        else: raise AssertionError('non-integer schema/counter accepted through Python equality')
    for raw in ('{"schema_version":0,"schema_version":1}', '{"recovery":{"blob":"fake","blob":"real"}}'):
        try: json.loads(raw, object_pairs_hook=unique_json_object)
        except ValueError: pass
        else: raise AssertionError('duplicate JSON object key accepted')
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
    baseline_row = {'command': ['archived-check'], 'exitCode': 2, 'elapsedSeconds': 1.5,
                    'cumulativeChildrenMaxRssKiB': 100, 'log': 'gate-00.log.gz', 'uncompressedSha256': 'a' * 64}
    baseline_report = {'commands': [baseline_row], 'memoryMetric': 'Cumulative children RSS; not aggregate peak', 'noLeanNoBuild': True}
    assert reviewed_receipt_rows(baseline_report) == [('/commands/0', baseline_row)]
    assert evidence_role(json.dumps(baseline_report).encode())
    for key, bad in (('uncompressedSha256', 'missing'), ('cumulativeChildrenMaxRssKiB', True), ('command', 'unrun')):
        assert not reviewed_receipt_rows(dict(baseline_report, commands=[dict(baseline_row, **{key: bad})]))
    assert not reviewed_receipt_rows(dict(baseline_report, noLeanNoBuild=False))
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
        sources['tests/failed-index.json'] = json.dumps(dict(failed_index, logs=[
            {'path': 'initial-failed.log.gz', 'sha256': hashlib.sha256(failed_log).hexdigest()},
            {'path': 'same-text-other-gzip.log.gz', 'sha256': hashlib.sha256(failed_log).hexdigest()}]))
        sources['tests/initial-failed.log.gz'] = failed_log
        sources['tests/same-text-other-gzip.log.gz'] = gzip.compress(b'', mtime=1)
        sources['tests/cumulative-history.json'] = json.dumps(dict(baseline_report, commands=[
            dict(baseline_row, log='compressed-history.gz', uncompressedSha256=hashlib.sha256(b'').hexdigest()),
            dict(baseline_row, log='wrong-history.gz', uncompressedSha256=hashlib.sha256(b'other').hexdigest()),
            dict(baseline_row, log='/external/absolute-history.gz', uncompressedSha256=hashlib.sha256(b'').hexdigest())]))
        for target in ('compressed-history.gz', 'wrong-history.gz', 'absolute-history.gz'):
            sources['tests/' + target] = gzip.compress(b'', mtime=0)
        sources['tests/magic-name-unit.py'] = 'import unittest as u\nimport unittest as __name__\nclass T(u.TestCase):\n def test_value(self): pass\nif __name__ == "__main__": u.main()\n'
        sources['tests/import-shadow-unit.py'] = 'import unittest\nimport json as unittest\nclass T(unittest.TestCase):\n def test_value(self): pass\nif __name__ == "__main__": unittest.main()\n'
        sources['tests/from-shadow-unit.py'] = 'from unittest import TestCase, main\nfrom json import loads as main\nclass T(TestCase):\n def test_value(self): pass\nif __name__ == "__main__": main()\n'
        sources['tests/exit-before-unit.py'] = 'import unittest,sys\nclass T(unittest.TestCase):\n def test_value(self): pass\nsys.exit(0)\nif __name__ == "__main__": unittest.main()\n'
        sources['tests/direct-unit.py'] = 'import unittest\nclass T(unittest.TestCase):\n def test_value(self): pass\nunittest.main()\n'
        sources['tests/nested-unit.py'] = 'import unittest\nclass T(unittest.TestCase):\n def test_value(self): pass\ndef never(): unittest.main()\n'
        sources['tests/early-main-unit.py'] = 'import unittest\nunittest.main()\nclass T(unittest.TestCase):\n def test_value(self): pass\n'
        sources['tests/double-main-unit.py'] = 'import unittest\nunittest.main()\nclass T(unittest.TestCase):\n def test_value(self): pass\nunittest.main()\n'
        sources['tests/guarded-early-main-unit.py'] = 'import unittest\nif __name__ == "__main__": unittest.main()\nclass T(unittest.TestCase):\n def test_value(self): pass\nunittest.main()\n'
        sources['tests/wildcard-unit.py'] = 'from exports import *\nimport unittest\nclass T(unittest.TestCase):\n def test_value(self): pass\nif __name__ == "__main__": unittest.main()\n'
        sources['tests/exports.py'] = '__all__=["__name__"]\n__name__="foreign"\n'
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
            'command': ['python3', '-B', 'tests/pass.py'], 'kind': 'unittest',
            'purpose': 'Read explicit generated and source fixtures under the passing regression test.',
            'input_scope': ['tests/generated.txt', 'tests/helper.py', 'tests/dead.lean'], 'other_reads': 'unresolved'}],
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
        unreviewed = copy.deepcopy(catalog)
        for key in ('purpose', 'input_scope', 'other_reads'): del unreviewed['standalone'][0][key]
        unreviewed_rows = {r['path']: r for r in inventory(repo, unreviewed)['records']}
        assert unreviewed_rows['tests/generated.txt']['class'] is None
        assert unreviewed_rows['tests/generated.txt']['secondary']['unreviewed_readers']
        assert unreviewed_rows['tests/live.py']['class'] == 'keep'  # actually observed helper frame
        expected = inventory(repo, catalog)
        rows = {r['path']: r for r in expected['records']}
        ordered = copy.deepcopy(catalog)
        ordered['reads'] = sorted(ordered['reads'], key=lambda r: json.dumps(r, sort_keys=True))
        grouped = copy.deepcopy(ordered)
        grouped['schema_version'] = 2; grouped['reads'] = compact_read_routes(ordered['reads'])
        assert list(read_routes(grouped)) == ordered['reads']
        assert inventory(repo, grouped) == inventory(repo, ordered)
        context = copy.deepcopy(ordered['reads'][0])
        context['frames'] = [{'path': 'tests/pass.py', 'blob': repo.tree['tests/pass.py'][2], 'line': 3},
                             {'path': 'tests/helper.py', 'blob': repo.tree['tests/helper.py'][2], 'line': 1}]
        def ordered_target(path):
            return {**context, 'target': path, 'target_blob': repo.tree[path][2]}
        reverse = [ordered_target('tests/helper.py'), ordered_target('tests/generated.txt')]
        alternate = copy.deepcopy(ordered_target('tests/generated.txt')); alternate['frames'][-1]['line'] = 2
        interleaved = [ordered_target('tests/mention.txt'), alternate, ordered_target('tests/dead.lean')]
        for routes in (reverse, interleaved):
            try: compact_read_routes(routes)
            except ValueError as error: assert 'route order' in str(error)
            else: raise AssertionError('compaction reordered equal-length helper provenance')
        for scenario in ('duplicate-target', 'unordered-target', 'empty-targets', 'bad-pin', 'extra-field', 'duplicate-context', 'forged-pin'):
            bad = copy.deepcopy(grouped); group = bad['reads'][0]
            if scenario == 'duplicate-target': group['targets'].append(copy.deepcopy(group['targets'][0]))
            elif scenario == 'unordered-target': group['targets'].append({'path': '', 'blob': 'a' * 40})
            elif scenario == 'empty-targets': group['targets'] = []
            elif scenario == 'bad-pin': group['targets'][0]['blob'] = None
            elif scenario == 'extra-field': group['targets'][0]['invented'] = True
            elif scenario == 'duplicate-context': bad['reads'].append(copy.deepcopy(group))
            else: group['targets'][0]['blob'] = '0' * 40
            try: inventory(repo, bad)
            except ValueError: pass
            else: raise AssertionError('unsupported grouped provenance accepted: ' + scenario)
        for p in ('tests/live.py', 'tests/helper.py', 'tests/pass.py', 'tests/generated.txt'):
            assert rows[p]['class'] == 'keep', p
        assert rows['tests/generated.txt']['generator']
        assert subprocess.run(['python3', '-B', 'tests/failing-unit.py'], cwd=root, capture_output=True).returncode == 1
        assert rows['tests/failing-unit.py']['class'] == 'keep'
        assert rows['tests/direct-unit.py']['class'] == 'keep' and rows['tests/direct-unit.py']['runner_chain']['entry']['source_only']
        assert rows['tests/failing-unit.py']['runner_chain']['entry']['source_only']
        assert rows['tests/failing-unit.py']['runner_chain']['entry']['validation_at_measured_revision']['status'] == 'unavailable'
        for name in ('dead-unit.py', 'quoted-unit.py', 'shadowed-unit.py', 'import-shadow-unit.py', 'from-shadow-unit.py', 'exit-before-unit.py', 'magic-name-unit.py', 'nested-unit.py', 'early-main-unit.py', 'double-main-unit.py', 'guarded-early-main-unit.py', 'wildcard-unit.py'): assert rows['tests/' + name]['class'] is None
        # Even a zero-exit dead/nested/early-main command cannot certify a
        # unittest root. Ordinary success is not proof that a test entry ran.
        for name in ('dead-unit.py', 'nested-unit.py', 'early-main-unit.py', 'import-shadow-unit.py', 'exit-before-unit.py', 'wildcard-unit.py', 'double-main-unit.py', 'guarded-early-main-unit.py'):
            path = 'tests/' + name
            bad = copy.deepcopy(catalog)
            bad['standalone'].append({'path': path, 'input_revision': repo.ref, 'source_blob': repo.tree[path][2],
                                      'command': ['python3', '-B', path], 'kind': 'unittest'})
            try: inventory(repo, bad)
            except ValueError as error: assert 'declared unittest entry point' in str(error)
            else: raise AssertionError('unsupported unittest root accepted: ' + name)
        for name in ('dead-unit.py', 'nested-unit.py'):
            assert subprocess.run(['python3', '-B', 'tests/' + name], cwd=root, capture_output=True).returncode == 0
        assert subprocess.run(['python3', '-B', 'tests/direct-unit.py'], cwd=root, capture_output=True).returncode == 0
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
        assert rows['tests/failed-index.json']['class'] == 'evidence'
        assert rows['tests/initial-failed.log.gz']['class'] == 'evidence'
        assert '/logs/0' in rows['tests/initial-failed.log.gz']['reason'] and 'stored-byte SHA256' in rows['tests/initial-failed.log.gz']['reason']
        assert rows['tests/same-text-other-gzip.log.gz']['class'] is None
        assert rows['tests/compressed-history.gz']['class'] == 'evidence'
        assert 'uncompressed SHA256' in rows['tests/compressed-history.gz']['reason']
        assert rows['tests/wrong-history.gz']['class'] is None
        assert rows['tests/absolute-history.gz']['class'] is None
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
    nonpassing_boundary_controls()
    passing_scan_boundary_controls()
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
            actual = json.loads(target.read_bytes(), object_pairs_hook=unique_json_object)
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
