"""Deterministic additive census classification fragments."""
import ast
import bisect
import hashlib
import json
import posixpath
import re
import shlex
import tempfile
from functools import lru_cache
from pathlib import Path


def unique_json_object(pairs):
    result = {}
    for key, value in pairs:
        if key in result: raise ValueError('duplicate JSON object key: ' + key)
        result[key] = value
    return result


def canonical(value):
    return (json.dumps(value, ensure_ascii=True, indent=2, sort_keys=True) + '\n').encode()



def _clean(path):
    path = posixpath.normpath(path)
    return path if path != '..' and not path.startswith(('../', '/')) else None

# A fragment is an additive object with schema_version 1 and any of routes,
# catalog_extensions, roles and fixtures. Route sections use expanded catalog
# entries; roles and fixtures are lists of the existing record formats. Files
# are read in filename order. Classification validators remain authoritative.
FRAGMENT_SECTIONS = ('standalone', 'generators', 'reads', 'orphans', 'module_entries')
# Opt-in consumer routes (H938/H951/H954/H955) live under a separate
# `consumer_routes` object, never in the legacy catalog sections, so their
# absence leaves every existing classification and output byte unchanged.
# persistent_reads: ordinary read definitions, re-credited at later refs while
#   runner definition, frames and target are the same blobs (H938).
# static_routes: {runner, frames, form, target, target_blob, purpose}, form one
#   of node-import, node-readFileSync, lean-readFile (H951/H955).
# git_policies: {path, blob, purpose, matches: [{line, output, writer}]} (H954).
# Standalone kind committed-module-cli (main script) is the H955 argparse role.
# H978 (x1g): static forms lean-library-readFile and node-readFileSync-walk, and
#   standalone kind source-only-program (revision-independent no-pass role).
# H996 (x1i): standalone kind python-argument-source-role, a reviewed
#   argument-bearing Python program as a source-only role that anchors nothing.
# H997 (x1j): standalone kind nonpython-entry-source-role, a reviewed live shell
#   or Node program as a source-only role that anchors nothing.
# H999 (x1k): standalone kind lean-check-source-role, a reviewed live non-root
#   Lean check source bound to its blob and drivers; anchors nothing.
# H1015 (x1o): standalone kind lean-fixture-source-role, the H999 rules for a
#   reviewed Lean fixture source (roles.py); consumption only, anchors nothing.
# H1051 (x1q): standalone kind python-import-source-role, a reviewed Python helper
#   imported by kept python3 -B entry roots (roles.py); consumption only.
# H1050 (x1q): standalone kind documentation-reference-role, a reviewed Markdown
#   document read by the documentation navigation check (roles.py); reference only.
# persistent_module_entries (H979): exact routes.module_entries claims that
#   persist while every recorded object is unchanged.
# H1009 (x1r): persistent_reads may carry a reviewed nonpassing read (roles.py);
#   source-only failed-run root, the named in-scope read only, no pass credit.
CONSUMER_SECTIONS = ('persistent_reads', 'static_routes', 'git_policies', 'persistent_module_entries')


def fragment_identity(section, row):
    if not isinstance(row, dict): raise ValueError('fragment entry must be an object')
    if section in ('roles', 'fixtures', 'git_policies'):
        keys = ('path',)
    elif section in ('standalone', 'generators', 'orphans'):
        keys = ('path', 'input_revision')
    elif section in ('module_entries', 'reads', 'persistent_reads', 'persistent_module_entries'):
        keys = ('runner', 'input_revision', 'target', 'frames')
    elif section == 'static_routes':
        keys = ('runner', 'form', 'target', 'frames')
    else:
        raise ValueError('unknown fragment section')
    if any(k not in row for k in keys): raise ValueError('fragment entry lacks identity: ' + section)
    values = [row[k] for k in keys]
    if section in ('module_entries', 'reads', 'persistent_reads', 'static_routes', 'persistent_module_entries'):
        frames = row['frames']
        if not isinstance(frames, list) or any(not isinstance(f, dict) for f in frames):
            raise ValueError('invalid fragment frames')
        values[-1] = [{k: v for k, v in frame.items() if k != 'blob'} for frame in frames]
    return canonical(values)


def read_fragments(directory):
    result = {key: [] for key in FRAGMENT_SECTIONS + ('roles', 'fixtures') + CONSUMER_SECTIONS}
    for path in sorted(directory.glob('*.json')):
        document = json.loads(path.read_bytes(), object_pairs_hook=unique_json_object)
        if (not isinstance(document, dict) or type(document.get('schema_version')) is not int
                or document['schema_version'] != 1
                or not set(document) <= {'schema_version', 'routes', 'catalog_extensions', 'roles', 'fixtures', 'consumer_routes'}):
            raise ValueError('invalid classification fragment: ' + str(path))
        for group in ('routes', 'catalog_extensions'):
            sections = document.get(group, {})
            if not isinstance(sections, dict) or not set(sections) <= set(FRAGMENT_SECTIONS):
                raise ValueError('invalid fragment catalog sections: ' + str(path))
            for section, entries in sections.items():
                if not isinstance(entries, list): raise ValueError('fragment section must be a list')
                result[section].extend(entries)
        for section in ('roles', 'fixtures'):
            entries = document.get(section, [])
            if not isinstance(entries, list): raise ValueError('fragment section must be a list')
            result[section].extend(entries)
        consumers = document.get('consumer_routes', {})
        if not isinstance(consumers, dict) or not set(consumers) <= set(CONSUMER_SECTIONS):
            raise ValueError('invalid fragment consumer route sections: ' + str(path))
        for section, entries in consumers.items():
            if not isinstance(entries, list): raise ValueError('fragment section must be a list')
            result[section].extend(entries)
    return result


def merge_fragment_entries(section, existing, additions):
    # Repeated identical claims are harmless; a different claim for the same
    # identity is ambiguous and rejected, regardless of file order.
    seen = {}
    for row in existing:
        key = fragment_identity(section, row)
        if key in seen and canonical(seen[key]) != canonical(row): raise ValueError('conflicting existing ' + section + ' entries')
        seen[key] = row
    result = list(existing)
    for row in additions:
        key = fragment_identity(section, row)
        if key in seen:
            if canonical(seen[key]) != canonical(row): raise ValueError('conflicting ' + section + ' fragment entries')
            continue
        seen[key] = row
        result.append(row)
    return result


# ---------------------------------------------------------------------------
# Opt-in consumer routes. Every row is blob-bound: a changed or missing object
# makes the declaration stale and grants nothing (never an error, so a later
# --ref still checks). A row whose objects match but whose claimed form does
# not hold is malformed and rejected. None of these rows certifies passing
# validation at the measured revision, proof, or any read not named exactly.

PERSISTED_OPERATION = 'blob-bound persisted Python read of unchanged measured bytes'
STATIC_FORMS = {
    'node-import': ('Node static import of literal module-relative path', 'executes'),
    'node-readFileSync': ('Node readFileSync of literal path', 'consumes'),
    'lean-readFile': ('Lean IO.FS.readFile of literal cwd-relative path', 'consumes'),
    'lean-library-readFile': ('Lean IO.FS.readFile of literal cwd-relative path in a top-level #eval/run_elab elaborated by a library build', 'consumes'),
    'node-readFileSync-walk': ('Node readFileSync of each file a local recursive suffix walker yields', 'consumes'),
}
# Demonstrated passing runner kinds whose committed source may anchor a route.
DEMONSTRATED_KINDS = ('unittest', 'node-test', 'runnable-entrypoint')
NODE_SUFFIXES = ('.mjs', '.js', '.cjs')
GIT_POLICY_ROLE = 'Git ignore policy consumed by git (exclude-standard) for a committed writer output'


def _current(repo, path, blob):
    return path in repo.tree and repo.tree[path][1] == 'blob' and repo.tree[path][2] == blob


def _frames_current(repo, frames, extra=()):
    if not isinstance(frames, list) or not frames: raise ValueError('consumer route lacks frames')
    for frame in frames:
        if (not isinstance(frame, dict) or set(frame) != {'path', 'blob', 'line'} or not isinstance(frame['path'], str)
                or not isinstance(frame['blob'], str) or type(frame['line']) is not int):
            raise ValueError('invalid consumer route frame')
    return all(_current(repo, f['path'], f['blob']) for f in frames) and all(_current(repo, p, b) for p, b in extra)


def _check_lines(repo, frames):
    for frame in frames:
        if frame['path'] not in repo.texts or not 1 <= frame['line'] <= len(repo.texts[frame['path']].splitlines()):
            raise ValueError('consumer route location mismatch')


def _anchor_root(graph, runner, frames, walk=False):
    """A current non-source-only root, or a demonstrated passing committed runner.

    A runner named validated:P or committed:P resolves to whichever of the two
    exists at the measured revision. Any other root (undemonstrated committed
    source, CLI/policy source role, derived claim) anchors nothing, except that
    a reviewed Node mode entry (H992) anchors the walker form alone (walk).
    """
    if runner.startswith(NODE_MODE_PREFIX):
        root = graph.roots.get(runner) if walk else None
        if root is None or 'derived_from' in root or not root.get('node_mode_root'): return None, None
        if root['path'] != frames[0]['path']: raise ValueError('consumer route does not start at its runner')
        return runner, root
    if runner.startswith(('validated:', 'committed:')):
        path = runner.split(':', 1)[1]
        runner = 'validated:' + path if 'validated:' + path in graph.roots else 'committed:' + path
    root = graph.roots.get(runner)
    if root is None or 'derived_from' in root: return None, None
    if root['path'] != frames[0]['path']: raise ValueError('consumer route does not start at its runner')
    if root.get('source_only') and not (runner.startswith('committed:') and root.get('runner_kind') in DEMONSTRATED_KINDS
                                        and 'source_demonstration_revision' in root):
        return None, None
    return runner, root


def _observe(graph, original, row, frames, target, operation, kind, hop, details):
    identity = original + ':' + details['kind'] + ':' + hashlib.sha256(canonical(row)).hexdigest()
    graph.roots[identity] = {**graph.roots[original], 'derived_from': original, 'observed_target': target,
                             'consumer_route': details}
    chain = {'root': identity, 'entry': graph.roots[identity], 'edges': []}
    for caller, callee in zip(frames, frames[1:]):
        chain = {**chain, 'edges': chain['edges'] + [{'source': caller['path'], 'target': callee['path'],
            'line': caller['line'], 'operation': hop, 'kind': 'executes', 'validated_for': identity}]}
        graph.observed.append((callee['path'], chain))
    reader = frames[-1]
    chain = {**chain, 'edges': chain['edges'] + [{'source': reader['path'], 'target': target, 'line': reader['line'],
        'operation': operation, 'kind': kind, 'validated_for': identity}]}
    graph.observed.append((target, chain))


def _historical_objects(classifier, repo, revision, pins):
    """True iff every (path, blob) is that path's object in the revision's tree."""
    if not isinstance(revision, str) or not classifier['hex_pin'](revision, 40):
        raise ValueError('persisted route requires a full commit revision')
    requests = [revision] + [revision + ':' + p for p, _ in pins]
    raw = classifier['git'](repo.root, 'cat-file', '--batch-check', '-Z',
                            data=b''.join(r.encode('utf-8', 'surrogateescape') + b'\0' for r in requests))
    lines = raw.rstrip(b'\0').split(b'\0')
    if len(lines) != len(requests): raise ValueError('persisted route object batch mismatch')
    expected = [(revision, b'commit')] + [(b, b'blob') for _, b in pins]
    for (oid, kind), line in zip(expected, lines):
        fields = line.split()
        if len(fields) != 3 or fields[0].decode() != oid or fields[1] != kind: return False
    return True


def persisted_reads(classifier, graph, catalog, rows):
    """H938: a validated read declaration persists while every object is unchanged.

    The row is an ordinary read definition recorded at its validation revision.
    At that revision it is processed exactly like a read; at any later --ref it
    credits the read only if the runner definition at that revision, every frame
    and the target are the same blobs now and at the recorded revision. Scope
    eligibility is the definition's own reviewed scope; nothing is widened.
    """
    repo = graph.repo
    for row in rows:
        if not isinstance(row, dict) or set(row) != {'runner', 'input_revision', 'frames', 'target', 'target_blob', 'operation'}:
            raise ValueError('invalid persisted read route')
        if row['input_revision'] == repo.ref: continue
        if row['operation'] == NONPASS_READ_OPERATION: persisted_nonpassing_read(classifier, graph, catalog, row); continue  # H1009, roles.py
        if row['operation'] != 'validated Python read of measured bytes': raise ValueError('unsupported persisted read operation')
        runner = row['runner']
        if not isinstance(runner, str) or not runner.startswith('validated:'): raise ValueError('persisted read needs a validated runner')
        path = runner[len('validated:'):]
        definitions = [e for e in catalog['standalone'] if e.get('path') == path and e.get('input_revision') == row['input_revision']]
        if (len(definitions) != 1 or definitions[0].get('kind') not in DEMONSTRATED_KINDS
                or not isinstance(definitions[0].get('source_blob'), str)):
            raise ValueError('persisted read lacks its passing runner definition')
        definition = definitions[0]
        target = row['target']
        if not isinstance(target, str) or not isinstance(row['target_blob'], str): raise ValueError('invalid persisted read target')
        if not _frames_current(repo, row['frames'], [(path, definition['source_blob']), (target, row['target_blob'])]):
            continue
        frames = row['frames']
        _check_lines(repo, frames)
        if not _historical_objects(classifier, repo, row['input_revision'],
                sorted({(f['path'], f['blob']) for f in frames} | {(path, definition['source_blob']), (target, row['target_blob'])})):
            raise ValueError('persisted route objects differ at recorded revision ' + row['input_revision'])
        original = 'validated:' + path if 'validated:' + path in graph.roots else 'committed:' + path
        root = graph.roots.get(original)
        if root is None: continue
        if root['path'] != frames[0]['path']: raise ValueError('persisted read does not start at its runner')
        if classifier['excluded'](target) or any(classifier['excluded'](f['path']) for f in frames): continue
        if 'input_scope' in definition: scopes, other = definition['input_scope'], definition['other_reads'] if 'other_reads' in definition else 'unresolved'
        elif definition['kind'] in ('unittest', 'node-test'): scopes, other = [], 'unresolved'
        else: scopes, other = None, None
        eligible = scopes is None or any(target == s or s.endswith('/') and target.startswith(s) for s in scopes)
        if not eligible:
            if other == 'unresolved': graph.uncertain_reads[target].add(original)
            continue
        _observe(graph, original, row, frames, target, PERSISTED_OPERATION, 'consumes', 'validated Python call stack (persisted)',
                 {'kind': 'persisted-read', 'validated_revision': row['input_revision'], 'runner_definition_blob': definition['source_blob']})


_NODE_IMPORT = re.compile(r"""^\s*(?:import\s+(?:[\w$*{}\s,]+?\s+from\s+)?|export\s+[\w$*{}\s,]+?\s+from\s+|(?:const|let|var)\s+[\w${}\s,:]+=\s*require\(\s*)(["'])(\.{1,2}/[^"'\\]+)\1\s*(\))?\s*;?\s*$""")
_NODE_FS = re.compile(r"""(?:\bimport\s*\{[^}]*\breadFileSync\b[^}]*\}\s*from\s*|\bconst\s*\{[^}]*\breadFileSync\b[^}]*\}\s*=\s*require\(\s*)(["'])(?:node:)?fs\1""")


@lru_cache(maxsize=16)
def _js_mask(text, regex=False):
    """Blank JS comments, templates and quoted strings; keep string literal spans.

    Regular-expression literals are not modelled unless regex: then a slash
    where an operand starts opens a single-line literal, blanked like a
    comment (the walker form needs exact brace and comment structure).
    Callers locate keywords in the masked code and accept an operand only at
    a recorded literal start, so commented, quoted or templated text never
    yields a route.
    """
    out = []; literals = {}; at = 0; n = len(text); last = ''
    while at < n:
        c = text[at]
        if regex and c == '/' and not text.startswith(('//', '/*'), at) and (not last or last in '(,=:[!&|?{};+-*%<>~^'):
            end = at + 1; within = False
            while end < n and text[end] != '\n' and (within or text[end] != '/'):
                if text[end] == '\\': end += 1
                elif text[end] == '[': within = True
                elif text[end] == ']': within = False
                end += 1
            if end >= n or text[end] != '/':
                out.append(c); last = c; at += 1; continue
            end += 1
            while end < n and text[end].isalpha(): end += 1
            out.append(re.sub(r'[^\n]', ' ', text[at:end])); at = end; last = 'x'; continue
        if text.startswith('//', at):
            end = text.find('\n', at); end = n if end < 0 else end
        elif text.startswith('/*', at):
            end = text.find('*/', at + 2); end = n if end < 0 else end + 2
        elif c in '"\'`':
            end = at + 1
            while end < n and text[end] != c and (c == '`' or text[end] != '\n'):
                end += 2 if text[end] == '\\' else 1
            end = min(end + 1, n)
            if c != '`': literals[at] = text[at:end]
            last = 'x'
        else:
            out.append(c); at += 1
            if not c.isspace(): last = c
            continue
        out.append(re.sub(r'[^\n]', ' ', text[at:end])); at = end
    return ''.join(out), literals


def _js_line(text, number, regex=False):
    """The line, its masked code, line-relative literal spans, and whole-file mask."""
    code, literals = _js_mask(text, regex)
    starts = [0] + [m.end() for m in re.finditer('\n', text)]
    begin = starts[number - 1]; line = text.splitlines()[number - 1]; masked = code[begin:begin + len(line)]
    spans = {start - begin: len(token) for start, token in literals.items() if begin <= start < begin + len(line)}
    return line, masked, spans, code, literals


def _node_import(source, text, number):
    line, masked, spans, _, _ = _js_line(text, number)
    match = _NODE_IMPORT.match(line)
    if match and masked[:match.start(1)] != line[:match.start(1)]: return None
    if not match or match.start(1) not in spans or ('require(' in line) != bool(match[3]): return None
    if 'require(' in line and not source.endswith(('.cjs', '.js')): return None
    return _clean(posixpath.join(posixpath.dirname(source), match[2]))


def _node_read(source, text, number, cwd):
    found = _js_line(text, number)
    line, masked, spans, code, literals = found
    calls = [m for m in re.finditer(r'readFileSync\(', masked)]
    if len(calls) != 1 or calls[0].start() and re.match(r'[\w$.]', masked[calls[0].start() - 1]): return None
    if re.search(r'\b(?:function|const|let|var|class)\s+readFileSync\b|\breadFileSync\s*=', code): return None
    if not any(code[m.start()] == text[m.start()] and m.start(1) in literals for m in _NODE_FS.finditer(text)): return None
    offset = calls[0].end(); argument = line[offset:]
    forms = ((r"""new URL\(\s*(["'])([^"'\\]+)\1\s*,\s*import\.meta\.url\s*\)""", True),
             (r"""(?:path\.)?(?:join|resolve)\(\s*__dirname\s*,\s*(["'])([^"'\\/][^"'\\]*)\1\s*\)""", True),
             (r"""(["'])([^"'\\/][^"'\\]*)\1""", False))
    for pattern, relative in forms:
        match = re.match(r'\s*' + pattern + r'\s*[,)]', argument)
        if match and offset + match.start(1) in spans:
            base = posixpath.dirname(source) if relative else cwd
            return _clean(posixpath.join(base, match[2]))
    return None


def _lean_read(classifier, repo, source, number, cwd, commands=r'#eval'):
    """One literal read inside a top-level #eval command of this file.

    Only the elaborated runner file itself is accepted: an imported module's
    #eval does not run when its importer runs, and a def runs only if called.
    A library build elaborates every imported module; that form also accepts
    run_elab (commands) and reaches the module through header imports.
    """
    code, literals = classifier['lean_lex'](repo.texts[source])
    starts = [0] + [m.end() for m in re.finditer('\n', code)]
    lines = code.splitlines()
    command = next((lines[k] for k in range(number - 1, -1, -1) if lines[k][:1].strip()), '')
    if not re.match(r'(?:' + commands + r')\b', command): return None
    found = []; positions = dict(literals)
    for match in re.finditer(r'(?<![\w.])IO\.FS\.(?:readFile|readBinFile)(?![\w.!?\'])', code):
        if bisect.bisect_right(starts, match.start()) != number: continue
        at = match.end()
        # Literals are blanked in code, so stop at the first literal start.
        while at < len(code) and at not in positions and code[at] in ' \t\n': at += 1
        literal = positions.get(at)
        if literal is None: return None
        try: value = json.loads(literal)
        except ValueError: return None
        if not isinstance(value, str) or value.startswith('/'): return None
        found.append(_clean(posixpath.join(cwd, value)))
    return found[0] if len(found) == 1 else None


def static_routes(classifier, graph, rows):
    """H951/H955: exact Node import/readFileSync and Lean IO.FS.readFile routes.

    Each hop is re-derived from the measured bytes: frames[i] statically imports
    frames[i+1] (a literal relative Node import in code, never a comment, string
    or template) and the last frame names the target with one literal in the
    claimed form. A Lean read is a single frame: a literal IO.FS.readFile inside
    a top-level #eval of the elaborated runner file. The root is a current entry
    point or a demonstrated passing committed runner; for the latter every frame
    and target object must be the one at its demonstration revision.
    """
    repo = graph.repo
    for row in rows:
        if (not isinstance(row, dict) or set(row) != {'runner', 'frames', 'form', 'target', 'target_blob', 'purpose'}
                or row['form'] not in STATIC_FORMS or not isinstance(row['target'], str) or not isinstance(row['target_blob'], str)
                or not isinstance(row['runner'], str) or not isinstance(row['purpose'], str) or not row['purpose'].strip()):
            raise ValueError('invalid static consumer route')
        frames = row['frames']; target = row['target']; form = row['form']
        if not _frames_current(repo, frames, [(target, row['target_blob'])]): continue
        _check_lines(repo, frames)
        original, root = _anchor_root(graph, row['runner'], frames, form == 'node-readFileSync-walk')
        if root is None: continue
        if root.get('source_only') and root.get('source_blob') != frames[0]['blob']: continue
        language = 'lean' if form.startswith('lean') else 'node'
        library = form == 'lean-library-readFile'
        if form == 'lean-readFile' and len(frames) != 1: raise ValueError('Lean read must be in the elaborated runner file')
        # A library build elaborates its root's import closure; nothing else does.
        if library and (root.get('kind') != 'Lean root' or root.get('source_only') or root.get('lake_package')
                        or root.get('cwd', '.') != '.' or not _default_library(repo, root, frames[0]['path'])):
            raise ValueError('Lean library read requires a repository Lean library root')
        reader_text = repo.texts[frames[-1]['path']]
        if library and (any(not _plain_lines(repo.texts[f['path']]) for f in frames)
                        or re.search(r'(?m)^#exit\b', classifier['lean_code'](reader_text)[:_offset(reader_text, frames[-1]['line'])])):
            raise ValueError('Lean library read follows #exit or ambiguous line breaks')
        suffixes = ('.lean',) if language == 'lean' else NODE_SUFFIXES
        if any(not f['path'].endswith(suffixes) for f in frames): raise ValueError('static route frame language mismatch')
        for caller, callee in zip(frames, frames[1:]):
            if library:
                if callee['path'] not in _lean_header_imports(classifier, repo, caller['path'], caller['line']):
                    raise ValueError('static route hop is not a Lean header import')
            elif _node_import(caller['path'], repo.texts[caller['path']], caller['line']) != callee['path']: raise ValueError('static route hop is not a literal import')
        reader = frames[-1]; cwd = root.get('cwd', '.')
        if form == 'node-import': resolved = _node_import(reader['path'], repo.texts[reader['path']], reader['line'])
        elif form == 'node-readFileSync': resolved = _node_read(reader['path'], repo.texts[reader['path']], reader['line'], cwd)
        elif form == 'node-readFileSync-walk': resolved = _node_walk_read(reader['path'], repo, reader['line'], target, root, frames[0]['path'])
        elif library: resolved = _lean_read(classifier, repo, reader['path'], reader['line'], cwd, r'#eval|run_elab')
        else: resolved = _lean_read(classifier, repo, reader['path'], reader['line'], cwd)
        if resolved is None or resolved != target: raise ValueError('static route target is not the literal ' + form + ' operand')
        if form == 'node-import' and not target.endswith(NODE_SUFFIXES): raise ValueError('Node import target is not a module')
        if classifier['excluded'](target) or any(classifier['excluded'](f['path']) for f in frames): continue
        # A historical runner demonstrated these exact objects, or nothing.
        if root.get('source_only') and not _historical_objects(classifier, repo, root['source_demonstration_revision'],
                sorted({(f['path'], f['blob']) for f in frames} | {(target, row['target_blob'])})): continue
        operation, kind = STATIC_FORMS[form]
        hop = 'Lean header import elaborated by the library build' if library else 'Node static import'
        _observe(graph, original, row, frames, target, operation, kind, hop,
                 {'kind': 'static-' + form, 'purpose': row['purpose']})


def _ignored_by(repo, directory, output):
    """git check-ignore with this tree's ancestor .gitignore blobs only.

    Returns (source, line, pattern) for the output, or None; the policy file's
    own directory must not itself be ignored, or git never reads the file.
    """
    import subprocess
    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp)
        subprocess.run(['git', 'init', '-q', str(root)], check=True)
        parts = directory.split('/') if directory else []
        for k in range(len(parts) + 1):
            name = '/'.join(parts[:k] + ['.gitignore'])
            if name in repo.tree and repo.tree[name][1] == 'blob':
                (root / name).parent.mkdir(parents=True, exist_ok=True); (root / name).write_bytes(repo.bytes(name))
        def check(path):
            run = subprocess.run(['git', '--no-replace-objects', '-C', str(root), '-c', 'core.excludesFile=/dev/null', 'check-ignore',
                                  '-v', '-z', '--no-index', '--stdin'], input=path.encode('utf-8', 'surrogateescape') + b'\0',
                                 stdout=subprocess.PIPE, stderr=subprocess.PIPE)
            if run.returncode not in (0, 1): raise ValueError('git check-ignore failed')
            fields = run.stdout.split(b'\0')
            # Verbose output also lists negated (not ignored) matches.
            if run.returncode or len(fields) < 4 or fields[2].startswith(b'!'): return None
            return fields[0].decode('utf-8', 'surrogateescape'), int(fields[1]), fields[2].decode('utf-8', 'surrogateescape')
        for k in range(1, len(parts) + 1):
            if check('/'.join(parts[:k]) + '/'): return None
        return check(posixpath.join(directory, output) if directory else output)


def _writer_names(repo, path, number, literal):
    """The literal occurs inside a string literal on that code line."""
    text = repo.texts[path]; line = text.splitlines()[number - 1]
    if path.endswith('.py'):
        import io, tokenize
        try: tokens = list(tokenize.generate_tokens(io.StringIO(text).readline))
        except (tokenize.TokenError, SyntaxError, IndentationError): return False
        return any(t.type == tokenize.STRING and t.start[0] == number and literal in t.string for t in tokens)
    if path.endswith(NODE_SUFFIXES):
        found = _js_line(text, number)
        return any(literal in found[0][at:at + size] for at, size in found[2].items())
    if path.endswith('.sh'):
        code = line.split(' #', 1)[0]
        return not line.lstrip().startswith('#') and literal in code
    return False


def git_policies(classifier, graph, rows):
    """H954: an exact in-use .gitignore is a Git policy consumer role.

    Each match names an ignore line, an uncommitted output below the file's
    directory that git, with only this tree's ancestor .gitignore files, ignores
    by exactly that line (the directory itself not ignored), and a string
    literal naming the output on an exact line of an entry-point source. A
    negated or unmatched rule, a tracked output, or a changed writer grants
    nothing. Whether the writer line executes is a reviewed claim. This root is source-only policy: no fixture, child or test credit.
    """
    repo = graph.repo
    for row in rows:
        if (not isinstance(row, dict) or set(row) != {'path', 'blob', 'purpose', 'matches'} or not isinstance(row['path'], str)
                or not isinstance(row['purpose'], str) or not row['purpose'].strip()
                or not isinstance(row['matches'], list) or not row['matches']):
            raise ValueError('invalid Git policy role')
        path = row['path']
        if posixpath.basename(path) != '.gitignore': raise ValueError('Git policy role requires a .gitignore')
        if not _current(repo, path, row['blob']) or repo.tree[path][0] != '100644': continue
        directory = posixpath.dirname(path); text = repo.texts.get(path)
        if text is None: raise ValueError('Git policy file is not text')
        lines = text.splitlines(); verified = []; stale = False
        for match in row['matches']:
            if (not isinstance(match, dict) or set(match) != {'line', 'output', 'writer'} or type(match['line']) is not int
                    or not isinstance(match['output'], str) or not isinstance(match['writer'], dict)
                    or set(match['writer']) != {'path', 'blob', 'line', 'literal'}):
                raise ValueError('invalid Git policy match')
            writer = match['writer']; output = match['output']
            if (not isinstance(writer['path'], str) or not isinstance(writer['blob'], str) or type(writer['line']) is not int
                    or not isinstance(writer['literal'], str) or not writer['literal'] or re.search(r'[*?\[\]!\\]', output + writer['literal'])):
                raise ValueError('invalid Git policy match')
            full = _clean(posixpath.join(directory, output)) if directory else _clean(output)
            if (full is None or (directory and not full.startswith(directory + '/')) or full != (directory + '/' + output if directory else output)
                    or not 1 <= match['line'] <= len(lines) or lines[match['line'] - 1].lstrip().startswith(('#', '!'))):
                raise ValueError('invalid Git policy output or line')
            if not _current(repo, writer['path'], writer['blob']): stale = True; break
            if posixpath.basename(writer['path']) == '.gitignore' or not any(
                    r['path'] == writer['path'] and 'derived_from' not in r and not k.startswith('git-policy:')
                    and not r.get('python_argument_role') and not r.get('nonpython_entry_role') and not r.get('lean_check_role')
                    and not r.get('lean_fixture_role') for k, r in graph.roots.items()):
                raise ValueError('Git policy writer is not an entry point source')
            if full in repo.tree or any(p.startswith(full + '/') for p in repo.tree):
                raise ValueError('Git policy output is tracked: ' + full)
            literal = writer['literal']
            if (writer['path'] not in repo.texts
                    or not 1 <= writer['line'] <= len(repo.texts[writer['path']].splitlines())
                    or not _writer_names(repo, writer['path'], writer['line'], literal)
                    or not (output == literal or output.endswith('/' + literal) or output.startswith(literal.rstrip('/') + '/'))):
                raise ValueError('Git policy writer does not name the output')
            if _ignored_by(repo, directory, output) != (path, match['line'], lines[match['line'] - 1].strip()):
                raise ValueError('Git policy line does not ignore the output')
            verified.append({'line': match['line'], 'output': full, 'writer': writer})
        if stale or classifier['excluded'](path): continue
        identity = 'git-policy:' + path
        first = verified[0]['writer']
        graph.root(path, 'Git ignore policy consumer', 'git (exclude-standard) applies ' + path, first['path'], first['line'], root_id=identity)
        graph.roots[identity].update({'source_only': True, 'source_blob': row['blob'], 'purpose': row['purpose'],
            'policy_role': GIT_POLICY_ROLE, 'policy_matches': verified,
            'validation_at_measured_revision': {'status': 'policy', 'reason': 'git check-ignore of this exact blob in isolation; no test, fixture or proof credit.'}})


def declared_module_cli(repo, path):
    """H955 module-level argparse role: the other curated CLI shape.

    The parser is built at module top level: only imports, definitions and
    assignments without exit calls precede `P = argparse.ArgumentParser(...)`,
    which is followed solely by literal `P.add_argument(...)` statements and
    `A = P.parse_args()`. At least one long option is required=True, so the bare
    command is an entry prefix, never a configured run. Positional, computed or
    duplicate options, star imports and rebinding argparse/P are refused.
    """
    if path not in repo.texts or not path.endswith('.py') or repo.tree[path][0] not in ('100644', '100755'): return None
    try:
        tree = ast.parse(repo.texts[path]); compile(repo.texts[path], path, 'exec', dont_inherit=True)
    except (SyntaxError, ValueError, RecursionError): return None
    modules = {alias.asname or 'argparse' for node in tree.body if isinstance(node, ast.Import)
               for alias in node.names if alias.name == 'argparse'}
    if not modules: return None
    # Any argv access may pre-configure parse_args; the role is then refused.
    if any(isinstance(n, ast.Name) and n.id == 'argv' or isinstance(n, ast.Attribute) and n.attr == 'argv'
           or isinstance(n, ast.alias) and (n.asname or n.name) == 'argv' for n in ast.walk(tree)): return None
    def exits(node):
        return any(isinstance(n, ast.Call) and (isinstance(n.func, ast.Name) and n.func.id in ('exit', 'quit')
                   or isinstance(n.func, ast.Attribute) and n.func.attr in ('exit', '_exit', 'abort')) for n in ast.walk(node))
    index = 0; body = tree.body
    while index < len(body):
        node = body[index]
        if (isinstance(node, ast.Assign) and len(node.targets) == 1 and isinstance(node.targets[0], ast.Name)
                and isinstance(node.value, ast.Call) and isinstance(node.value.func, ast.Attribute)
                and isinstance(node.value.func.value, ast.Name) and node.value.func.value.id in modules
                and node.value.func.attr == 'ArgumentParser'): break
        if isinstance(node, ast.Expr) and isinstance(node.value, ast.Constant) and isinstance(node.value.value, str) and index == 0: pass
        elif isinstance(node, ast.Import): pass
        elif isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)) and not any(
                exits(d) for d in node.decorator_list + node.args.defaults + node.args.kw_defaults if d is not None): pass
        elif isinstance(node, ast.ClassDef) and not exits(node): pass
        elif isinstance(node, ast.ImportFrom) and all(a.name != '*' for a in node.names): pass
        elif isinstance(node, (ast.Assign, ast.AnnAssign)) and not exits(node): pass
        else: return None
        index += 1
    if index == len(body): return None
    parser_node = body[index]; parser = parser_node.targets[0].id
    protected = modules | {parser}
    for node in ast.walk(tree):
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)) and node.name in protected: return None
        if isinstance(node, ast.Name) and isinstance(node.ctx, (ast.Store, ast.Del)) and node.id in protected and node is not parser_node.targets[0]: return None
        if isinstance(node, ast.ImportFrom) and any(a.name == '*' or (a.asname or a.name) in protected for a in node.names): return None
        if isinstance(node, ast.Import) and any((a.asname or a.name.split('.')[0]) in protected and not (a.name == 'argparse' and (a.asname or 'argparse') in modules) for a in node.names): return None
        if isinstance(node, (ast.Global, ast.Nonlocal)) and set(node.names) & protected: return None
        if isinstance(node, ast.Attribute) and isinstance(node.ctx, (ast.Store, ast.Del)) and isinstance(node.value, ast.Name) and node.value.id in protected: return None
    required = set(); declared = set()
    for node in body[index + 1:]:
        if (isinstance(node, ast.Assign) and len(node.targets) == 1 and isinstance(node.targets[0], ast.Name)
                and isinstance(node.value, ast.Call) and isinstance(node.value.func, ast.Attribute)
                and isinstance(node.value.func.value, ast.Name) and node.value.func.value.id == parser
                and node.value.func.attr == 'parse_args' and not node.value.args and not node.value.keywords):
            if not required: return None
            return {'kind': 'curated module-level argparse entry', 'revision': repo.ref, 'parser_line': parser_node.lineno,
                    'main_line': node.lineno, 'parse_args_line': node.lineno, 'required_options': sorted(required)}
        if not (isinstance(node, ast.Expr) and isinstance(node.value, ast.Call) and isinstance(node.value.func, ast.Attribute)
                and isinstance(node.value.func.value, ast.Name) and node.value.func.value.id == parser
                and node.value.func.attr == 'add_argument'): return None
        call = node.value
        if not call.args or any(not isinstance(a, ast.Constant) or not isinstance(a.value, str)
                                or not re.fullmatch(r'--?[A-Za-z][A-Za-z0-9-]*', a.value) for a in call.args): return None
        options = [a.value for a in call.args]
        if len(set(options)) != len(options) or set(options) & declared: return None
        declared.update(options)
        if any(k.arg is None for k in call.keywords): return None
        flags = [k.value for k in call.keywords if k.arg == 'required']
        if flags and not (len(flags) == 1 and isinstance(flags[0], ast.Constant) and type(flags[0].value) is bool): return None
        if flags and flags[0].value is True:
            if len(options) != 1 or not options[0].startswith('--'): return None
            required.add(options[0])
    return None

# ---------------------------------------------------------------------------
# H978/H979 successor forms (x1g). Each is opt-in through a static-route form,
# a consumer section or a standalone kind that no earlier fragment uses, so
# without such rows every classification and output byte is unchanged. None
# grants execution, passing-validation or proof credit beyond the named object.

SOURCE_ONLY_KIND = 'source-only-program'
MODULE_ENTRY_KEYS = frozenset({'runner', 'input_revision', 'frames', 'target', 'target_blob', 'operation',
                               'module_code_sha256', 'module_frame_line', 'python', 'collector_sha256'})
MODULE_ENTRY_OPERATION = 'entered measured Python module; no fixture consumption credit'


def _offset(text, number):
    return sum(len(line) + 1 for line in text.split('\n')[:number - 1])


def _default_library(repo, root, path):
    """A default lean_lib of the repository lakefile, sources at the root."""
    import tomllib
    match = re.fullmatch(r'lake build (\S+)', root.get('command', ''))
    if match is None or root.get('location', '').split(':')[0] != 'lakefile.toml' or 'lakefile.toml' not in repo.texts: return False
    try: config = tomllib.loads(repo.texts['lakefile.toml'])
    except ValueError: return False
    entries = [e for e in config.get('lean_lib', []) if isinstance(e, dict) and e.get('name') == match[1]]
    if len(entries) != 1 or match[1] not in config.get('defaultTargets', []) or entries[0].get('srcDir', '.') not in ('.', './'): return False
    names = entries[0].get('roots', [entries[0].get('root', match[1])])
    return isinstance(names, list) and path in [n.replace('.', '/') + '.lean' for n in names if isinstance(n, str)]


def _lean_header_imports(classifier, repo, source, number):
    """Module paths named by a header import line: only imports precede it."""
    lines = classifier['lean_code'](repo.texts[source]).splitlines()
    pattern = r'\s*(?:(?:public|private|meta)\s+)*import(?:\s+all)?\s+(.+)'
    for k, line in enumerate(lines[:number], 1):
        if not line.strip() or re.fullmatch(r'\s*(?:module|prelude)\s*', line): continue
        match = re.fullmatch(pattern, line)
        if not match: return []
        if k == number: return [m.replace('.', '/') + '.lean' for m in match[1].split()]
    return []


def _js_code(text, number):
    """(code, literal spans): the line is code and string literals, optionally
    followed by one trailing // comment, which is cut off."""
    line, masked, spans, _, _ = _js_line(text, number, True)
    inside = {at for start, size in spans.items() for at in range(start, start + size)}
    bad = [at for at, c in enumerate(line) if masked[at] != c and at not in inside]
    if bad:
        if not line.startswith('//', bad[0]) or masked[bad[0]:].strip(): return None
        line = line[:bad[0]]
    return line, spans


def _js_match(text, number, pattern):
    """Full-line match of a code line whose quoted groups are real literals."""
    found = _js_code(text, number)
    if found is None: return None
    match = re.fullmatch(r'\s*' + pattern + r'\s*', found[0])
    if match is None: return None
    for k in range(1, (match.re.groups or 0) + 1):
        if match.group(k) in ('"', "'") and match.start(k) not in found[1]: return None
    return match


def _plain_lines(text):
    """Newline is the only line separator, so splitlines and offsets agree."""
    return not re.search('[\r\x0b\x0c\x1c\x1d\x1e\x85\u2028\u2029]', text)


def _js_destructured(code, name):
    """name is bound by a destructuring pattern or a parameter list."""
    n = r'(?<![\w$.])' + re.escape(name) + r'(?![\w$])'
    return bool(re.search(r'[{\[][^{}\[\];]*' + n + r'[^{}\[\];]*[}\]]\s*=(?![=>])', code)
                or re.search(r'(?:\bfunction\b[^(]*|\bcatch\s*)\([^()]*' + n + r'[^()]*\)|\([^()]*' + n + r'[^()]*\)\s*=>|' + n + r'\s*=>', code))


def _js_unique(text, code, name, pattern):
    """The match of the one top-level line defining name; never rebound."""
    lines = text.splitlines()
    hits = [m for m in (_js_match(text, n, pattern) for n, line in enumerate(lines, 1) if name in line) if m]
    if len(hits) != 1 or hits[0].string[:1].isspace(): return None
    if len(re.findall(r'(?<![\w$.])' + re.escape(name) + r'\s*=(?!=)', code)) != 1: return None
    if re.search(r'\b(?:function|let|var|class)\s+' + re.escape(name) + r'\b', code): return None
    return hits[0]


def _js_imported(text, code, names, module):
    """Every name comes from one literal import of node:<module>, never rebound."""
    for match in re.finditer(r'\bimport\s*\{([^}]*)\}\s*from\s*(["\'])(?:node:)?' + module + r'\2', text):
        if code[match.start()] != text[match.start()] or match.start(2) not in _js_mask(text, True)[1]: continue
        imported = {n.strip() for n in match[1].split(',')}
        if not set(names) <= imported: continue
        return not any(re.search(r'\b(?:function|const|let|var|class)\s+' + re.escape(n) + r'\b|(?<![\w$.])' + re.escape(n) + r'\s*=(?!=)', code)
                       for n in names)
    return False


def _node_walk_read(source, repo, number, target, root, entry):
    """H978: readFileSync(P) of each file a local recursive suffix walker yields.

    Accepted shape, all re-derived from code lines (never comments, strings or
    templates): `for (const P of W(resolve(ROOT, "dir"))[.sort()]) {` encloses
    the read line directly (brace depth one) as `[const x =] readFileSync(P[,
    "enc"])`, not as a conditional operand; W is the only local
    `function W(d, out = []) {` with the readdirSync/join/statSync/endsWith
    suffix body; ROOT is a top-level `const ROOT = resolve(dirname(
    fileURLToPath(import.meta.url)), "rel")`. Early exits before the read are
    only `if (P.startsWith(C)) continue;` with top-level `const C = resolve(ROOT,
    "x")`, and the target lies outside each such C. Enclosing blocks are only
    `if (MODE === "lit") {` with top-level `const MODE = process.argv[2];`, and
    the root command passes that literal. The target is one tracked regular
    file below dir with the suffix; nothing else is credited.
    """
    text = repo.texts[source]
    if not _plain_lines(text): return None
    code, _ = _js_mask(text, True); lines = text.splitlines()
    if not (_js_imported(text, code, ('readFileSync', 'readdirSync', 'statSync'), 'fs')
            and _js_imported(text, code, ('resolve', 'dirname', 'join'), 'path')
            and _js_imported(text, code, ('fileURLToPath',), 'url')):
        return None
    read = _js_match(text, number, r'(?:(?:const|let|var)\s+[\w$]+\s*=\s*)?readFileSync\(\s*([\w$]+)\s*(?:,\s*(["\'])[\w-]+\2\s*)?\)[\s,;)]*')
    if read is None: return None
    variable = read[1]
    # Brace stack over code before the read: the line of each open brace.
    starts = [0] + [m.end() for m in re.finditer('\n', text)]
    stack = []
    for at in range(starts[number - 1]):
        if code[at] == '{': stack.append(bisect.bisect_right(starts, at))
        elif code[at] == '}':
            if not stack: return None
            stack.pop()
    if not stack: return None
    loop_line = stack[-1]
    loop = _js_match(text, loop_line, r'for\s*\(\s*const\s+([\w$]+)\s+of\s+([\w$]+)\(\s*resolve\(\s*([\w$]+)\s*,\s*(["\'])([^"\'\\]+)\4\s*\)\s*\)(?:\.sort\(\))?\s*\)\s*\{')
    if loop is None or loop[1] != variable: return None
    walker, base_name, directory = loop[2], loop[3], loop[5]
    code_line = lambda n: code[starts[n - 1]:starts[n - 1] + len(lines[n - 1])]
    def statement_start(n):
        """The previous code line ends a statement or opens a block (no braceless if/else/arrow)."""
        previous = next((code_line(k).rstrip() for k in range(n - 1, 0, -1) if code_line(k).strip()), ';')
        return previous.endswith((';', '{', '}'))
    # The read is a statement or a direct argument of the call that starts its statement.
    k = number - 1
    while k > loop_line and code_line(k).strip() and not code_line(k).rstrip().endswith((';', '{', '}')): k -= 1
    if k > loop_line and not code_line(k).strip(): return None
    prefix = ''.join(code_line(n) + '\n' for n in range(k + 1, number))
    if prefix.strip():
        call = re.match(r'\s*(?!(?:if|while|for|switch|catch|with|return|else|do|throw|typeof|await|yield|new)\b)[\w$.]+\(', prefix)
        if call is None or re.search(r'=>|\bfunction\b', prefix) or prefix.rstrip()[-1:] not in (',', '('): return None
        depth = 0
        for at, c in enumerate(prefix):
            if c in '([{': depth += 1
            elif c in ')]}': depth -= 1
            if at >= call.end() - 1 and depth < 1: return None
        if depth != 1: return None
    elif not statement_start(number): return None
    if not all(statement_start(n) for n in stack): return None
    protected = (variable, walker, base_name, 'readFileSync', 'readdirSync', 'statSync', 'resolve', 'dirname', 'join', 'fileURLToPath')
    if any(_js_destructured(code, name) for name in protected): return None
    rel = _js_unique(text, code, base_name, r'const\s+' + re.escape(base_name) + r'\s*=\s*resolve\(\s*dirname\(\s*fileURLToPath\(\s*import\.meta\.url\s*\)\s*\)\s*,\s*(["\'])([^"\'\\]+)\1\s*\)\s*;?')
    if rel is None: return None
    base_dir = _clean(posixpath.join(posixpath.dirname(source), rel[2]))
    walked = _clean(posixpath.join(base_dir, directory)) if base_dir is not None else None
    # The walker definition, line by line.
    definitions = [n for n in range(1, len(lines) + 1) if re.search(r'\bfunction\s+' + re.escape(walker) + r'\b', code_line(n))]
    if len(definitions) != 1 or re.search(r'(?<![\w$.])' + re.escape(walker) + r'\s*=(?!=)', code): return None
    head = definitions[0]
    header = _js_match(text, head, r'function\s+' + re.escape(walker) + r'\s*\(\s*([\w$]+)\s*,\s*([\w$]+)\s*=\s*\[\s*\]\s*\)\s*\{')
    if header is None or lines[head - 1][:1].isspace() or head + 7 > len(lines) or not statement_start(head): return None
    d, out = map(re.escape, (header[1], header[2])); w = re.escape(walker)
    body = [r'for\s*\(\s*const\s+([\w$]+)\s+of\s+readdirSync\(\s*' + d + r'\s*\)\s*\)\s*\{',
            r'const\s+([\w$]+)\s*=\s*join\(\s*' + d + r'\s*,\s*([\w$]+)\s*\)\s*;?',
            r'if\s*\(\s*statSync\(\s*([\w$]+)\s*\)\.isDirectory\(\)\s*\)\s*' + w + r'\(\s*([\w$]+)\s*,\s*' + out + r'\s*\)\s*;?',
            r'else\s+if\s*\(\s*([\w$]+)\.endsWith\(\s*(["\'])(\.[\w.-]+)\2\s*\)\s*\)\s*' + out + r'\.push\(\s*([\w$]+)\s*\)\s*;?',
            r'\}', r'return\s+' + out + r'\s*;?', r'\}']
    found = [_js_match(text, head + k, pattern) for k, pattern in enumerate(body, 1)]
    if any(m is None for m in found): return None
    entry_name, path_name = found[0][1], found[1][1]
    if (found[1][2] != entry_name or {found[2][1], found[2][2], found[3][1], found[3][4]} != {path_name}): return None
    suffix = found[3][3]
    if (walked is None or not target.startswith(walked + '/') or not target.endswith(suffix)
            or target not in repo.tree or repo.tree[target][0] not in ('100644', '100755')): return None
    # Early exits in the loop body before the read.
    for n in range(loop_line + 1, number):
        if not re.search(r'\b(?:continue|break|return|throw|exit|yield|await)\b', code_line(n)): continue
        guard = _js_match(text, n, r'if\s*\(\s*' + re.escape(variable) + r'\.startsWith\(\s*([\w$]+)\s*\)\s*\)\s*continue\s*;?')
        if guard is None or _js_destructured(code, guard[1]): return None
        at = _js_unique(text, code, guard[1], r'const\s+' + re.escape(guard[1]) + r'\s*=\s*resolve\(\s*' + re.escape(base_name) + r'\s*,\s*(["\'])([^"\'\\]+)\1\s*\)\s*;?')
        if at is None: return None
        # JavaScript startsWith is a string prefix test on resolved paths.
        skipped = _clean(posixpath.join(base_dir, at[2]))
        if skipped is None or target.startswith(skipped): return None
    # Enclosing blocks: only plain (never else) argv mode branches satisfied by the root command.
    for opener in stack[:-1]:
        branch = _js_match(text, opener, r'if\s*\(\s*([\w$]+)\s*===\s*(["\'])([^"\'\\]+)\2\s*\)\s*\{')
        if (branch is None or _js_destructured(code, branch[1])
                or _js_unique(text, code, branch[1], r'const\s+' + re.escape(branch[1]) + r'\s*=\s*process\.argv\[2\]\s*;?') is None): return None
        try: words = shlex.split(root['command'])
        except ValueError: return None
        if words[:2] != ['node', entry] or len(words) < 3 or words[2] != branch[3]: return None
    return target


def source_only_program(classifier, graph, catalog, entry):
    """H978: a no-pass default program as a revision-independent source role.

    The definition binds an unchanged Python source and its genuine top-level
    default entry line; the program matches no configured CLI or unittest form.
    Unlike runnable-entrypoint it is never a validated runner, at its own
    revision or any later one: no passing run, read anchor, fixture, helper,
    child, generated-output, proof or runtime credit. A later revision keeps it
    while the blob is unchanged and the recorded commit holds that blob; a
    current definition of the same path supersedes it.
    """
    repo = graph.repo
    required = {'path', 'input_revision', 'source_blob', 'command', 'kind', 'entry_line', 'purpose'}
    if (set(entry) != required or not isinstance(entry['path'], str) or not isinstance(entry['source_blob'], str)
            or not isinstance(entry['purpose'], str) or not entry['purpose'].strip()):
        raise ValueError('invalid source-only program definition')
    p = entry['path']; revision = entry['input_revision']
    if not isinstance(revision, str) or not classifier['hex_pin'](revision, 40): raise ValueError('source-only program requires a full commit revision')
    if any(e.get('path') == p and e.get('input_revision') == revision and e.get('kind') != SOURCE_ONLY_KIND for e in catalog['standalone']):
        raise ValueError('conflicting standalone definitions: ' + p)
    if revision != repo.ref:
        if any(e.get('path') == p and e.get('input_revision') == repo.ref for e in catalog['standalone']): return
        if not _current(repo, p, entry['source_blob']): return
        if not _historical_objects(classifier, repo, revision, [(p, entry['source_blob'])]):
            raise ValueError('unverifiable historical runner demonstration: ' + revision + ':' + p)
    elif not _current(repo, p, entry['source_blob']): raise ValueError('standalone definition source mismatch: ' + p)
    command = entry['command']
    if command != ['python3', '-B', p] or not p.endswith('.py') or repo.tree[p][0] not in ('100644', '100755') or p not in repo.texts:
        raise ValueError('unsupported source-only program invocation: ' + p)
    try: lines = classifier['entrypoint_lines'](repo.bytes(p))
    except (SyntaxError, ValueError, RecursionError): lines = set()
    if type(entry['entry_line']) is not int or entry['entry_line'] not in lines:
        raise ValueError('source-only program lacks its default top-level entry: ' + p)
    if any(classifier[f](repo, p) is not None for f in ('declared_configured_cli', 'declared_module_cli', 'declared_unittest')):
        raise ValueError('source-only program matches a configured CLI or unittest form: ' + p)
    identity = 'source-only:' + p
    graph.root(p, 'source-only default program', shlex.join(command), p, entry['entry_line'], root_id=identity)
    if identity not in graph.roots: return
    graph.roots[identity].update({'source_only': True, 'source_blob': entry['source_blob'], 'purpose': entry['purpose'],
        'program_role': SOURCE_ONLY_KIND, 'source_declaration_revision': revision,
        'validation_at_measured_revision': {'status': 'unavailable', 'command': command,
            'reason': 'Default invocation is not certified to pass and matches no configured CLI form; revision-independent source role only. No read anchor, fixture, helper, child, generated-output, proof or runtime credit.'}})



NODE_MODE_KIND = 'node-mode-source-root'
NODE_MODE_PREFIX = 'node-mode:'
# H992 (gh coord#1319): each reviewed argument-bearing Node entry, bound to
# (path, source blob, mode, provenance line in that same blob). Nothing else
# is promoted: another file, blob, mode, argument or documentation line fails.
REVIEWED_NODE_MODES = frozenset({('scripts/parse-corpus.mjs', 'dd1093f6fe8bfe00ae772e0b8b4a0bc0dd4b265a', 'prepare', 17)})


def node_mode_root(classifier, graph, catalog, entry, reviewed=None):
    """H992: a reviewed `node P MODE` command as a source-only entry root.

    The definition binds the exact command ['node', P, MODE], the source blob,
    and its provenance: a whole-line // comment of that same blob that starts
    with the verbatim command. P has a top-level `const M = process.argv[2];`
    and a top-level `if (M === "MODE") {`. The root is never a validated or
    passing runner and carries no execution, fixture, proof or runtime credit;
    it anchors only node-readFileSync-walk routes, whose own checks still bind
    every frame and target to their objects at the recorded revision. A later
    revision keeps it while the blob is unchanged and the recorded commit
    holds it.
    """
    repo = graph.repo
    reviewed = REVIEWED_NODE_MODES if reviewed is None else reviewed
    required = {'path', 'input_revision', 'source_blob', 'command', 'kind', 'provenance', 'purpose'}
    if (set(entry) != required or not isinstance(entry['path'], str) or not isinstance(entry['source_blob'], str)
            or not isinstance(entry['purpose'], str) or not entry['purpose'].strip()
            or not isinstance(entry['provenance'], dict) or set(entry['provenance']) != {'path', 'blob', 'line', 'invocation'}):
        raise ValueError('invalid Node mode root definition')
    p = entry['path']; revision = entry['input_revision']; command = entry['command']; doc = entry['provenance']
    if not isinstance(revision, str) or not classifier['hex_pin'](revision, 40): raise ValueError('Node mode root requires a full commit revision')
    if any(e.get('path') == p and e.get('input_revision') == revision and e is not entry for e in catalog['standalone']):
        raise ValueError('conflicting standalone definitions: ' + p)
    if (not isinstance(command, list) or len(command) != 3 or command[:2] != ['node', p] or not isinstance(command[2], str)
            or not re.fullmatch(r'[a-z][\w-]*', command[2]) or not p.endswith(NODE_SUFFIXES)):
        raise ValueError('unsupported Node mode root invocation: ' + str(p))
    mode = command[2]
    if (doc['path'] != p or doc['blob'] != entry['source_blob'] or doc['invocation'] != shlex.join(command)
            or (p, entry['source_blob'], mode, doc['line']) not in reviewed):
        raise ValueError('unreviewed Node mode root: ' + p)
    if revision != repo.ref:
        if any(e.get('path') == p and e.get('input_revision') == repo.ref for e in catalog['standalone']): return
        if not _current(repo, p, entry['source_blob']): return
        if not _historical_objects(classifier, repo, revision, [(p, entry['source_blob'])]):
            raise ValueError('unverifiable historical runner demonstration: ' + revision + ':' + p)
    elif not _current(repo, p, entry['source_blob']): raise ValueError('standalone definition source mismatch: ' + p)
    text = repo.texts.get(p)
    if text is None or repo.tree[p][0] not in ('100644', '100755') or not _plain_lines(text):
        raise ValueError('unsupported Node mode root invocation: ' + p)
    code, _ = _js_mask(text, True); lines = text.splitlines(); line = doc['line']
    # Provenance: a comment-only line of the measured blob, command first.
    if (type(line) is not int or not 1 <= line <= len(lines) or _js_line(text, line, True)[1].strip()
            or not re.match(r'\s*//\s*' + re.escape(doc['invocation']) + r'(?:\s|$)', lines[line - 1])):
        raise ValueError('Node mode root lacks its verbatim source provenance: ' + p)
    branches = [m for m in (_js_match(text, n, r'if\s*\(\s*([\w$]+)\s*===\s*(["\'])' + re.escape(mode) + r'\2\s*\)\s*\{')
                            for n in range(1, len(lines) + 1) if mode in lines[n - 1]) if m and not m.string[:1].isspace()]
    if (len(branches) != 1 or _js_destructured(code, branches[0][1])
            or _js_unique(text, code, branches[0][1], r'const\s+' + re.escape(branches[0][1]) + r'\s*=\s*process\.argv\[2\]\s*;?') is None):
        raise ValueError('Node mode root lacks its top-level argv mode branch: ' + p)
    entry_line = next(n for n in range(1, len(lines) + 1) if not lines[n - 1][:1].isspace() and _js_match(text, n, re.escape(branches[0].group(0))))
    identity = NODE_MODE_PREFIX + p
    graph.root(p, 'source-only Node mode entry', shlex.join(command), p, entry_line, root_id=identity)
    if identity not in graph.roots: return
    graph.roots[identity].update({'source_only': True, 'node_mode_root': True, 'source_blob': entry['source_blob'],
        'purpose': entry['purpose'], 'node_mode': mode, 'provenance': doc, 'source_demonstration_revision': revision,
        'validation_at_measured_revision': {'status': 'unavailable', 'command': command,
            'reason': 'Reviewed argument-bearing entry command; source role only, never run or certified to pass. Anchors only literal walker reads in its mode; no execution, helper, child, generated-output, proof or runtime credit.'}})


# Reviewed (path, source blob, introducing commit) tables: an @COMMIT line,
# then one `path blob` row per file it introduced; each path starts with an
# abbreviation from _REVIEW_DIRECTORIES.
_REVIEW_DIRECTORIES = {'N:': 'tests/directruntime-20261104/native-browser/', 'D:': 'tests/directruntime-20261104/', 'U:': 'tests/upstream/',
                       'T:': 'tests/', 'H:': 'scripts/h62/'}


def _review_table(text):
    rows, commit = set(), None
    for line in filter(str.strip, text.split('\n')):
        if line.startswith('@'): commit = line[1:]; continue
        path, blob = line.split()
        if commit is None: raise ValueError('invalid review table')
        rows.add((_REVIEW_DIRECTORIES[path[:2]] + path[2:], blob, commit))
    return frozenset(rows)


PYTHON_ARGS_KIND = 'python-argument-source-role'
PYTHON_ARGS_PREFIX = 'py-args:'
# H996 (gh coord#1329, X1E-CONFIGURED-ROLE): each reviewed live Python program
# that needs positional arguments, a forwarded command or a subcommand, bound to
# (path, source blob, commit that introduced that blob at that path). Nothing
# else is promoted: another file, blob or provenance commit fails, and no
# argument, read, helper or output is ever recorded or credited.
REVIEWED_PYTHON_ARGS = _review_table('''
@15302eb51e3df48b9d8d46eaf50348dd1deddfb2
N:validation-admission.py 1d56a3dc820b8ae3e503fedfbd4151ff530539bd
@17f2902cdc6ab848317fc82e31a90ad2d7c4fba8
D:memory-references/bounded-check.py d9f1b14c51c9011736f0fb484f4fcf96d55cd615
@2207c1bba286538fd63e4a0ff4960ed4a593a8ab
U:baseline-20261028/invocations/bulk/timed.py c543b7aef3f458d0765b11b19741406a7ff78415
U:baseline-20261028/invocations/retries/selector.py 5b7a49f863f7c6fad8231d17d68628623948a00e
@3bdd5ea4f35abb365b6bb57da56db7c23b645ac5
D:memory-references/browser-result-intake.py fbb3489b8a38e1e8a8e96fa37d95fbea09d88903
@3c3346709988f245ee64b8ffc606dfec56e6c6e1
D:memory-references/pack-cache.py c10c9d9b34044d11582ab507e76bf017a9034449
@44fa1c785b3168551c9f9589da56b5314b4ef740
D:memory-references/census-controls.py 08e1714023fc1f8e49ca09a8601d899ed54155f8
D:memory-references/runtime-boundary-census.py 526851b6c2b502a149b80d2f7f1f0c8ae87b1113
@4d4407dbbd3e5fed9ed20fe8f76dde8bc0577e89
D:memory-references/linker-attribution-controls.py 06166345217a40838f67fc52998333cfafd4bbbd
D:memory-references/linker-attribution.py 3b487c691ab3b1710149a25eef37d14301bcd563
@5a2afc72aca1a35cf555fa1b462b9de4c2ef79b7
D:shared-translator/measure.py 57c6a2f51633f72cf79c063740eff1f6ade3a26b
D:shared-translator/outer_guard.py e33bbf7efee05de73e793c8f872e2e821d8c6421
@6479617481ce020d41f7061d9dcf4dbfe9bd1ab8
D:memory-references/native-closure-evidence.py 1872f7842f78468b9d617f000e3469a7781a7fe2
@9be4ce0a089f0888ac165ff770ac90e3879ece0d
D:memory-references/inspect-browser-evidence.py 6f747cfa705fc346a6aedfb162e4e84df8978565
@ca73d1a4e1aecbcbc566acaa1aa7392cad472b3d
N:environment/test-known-stack-continuation.py 0224c0f28316d02a1489016c0e13c0fa20e6e80c
N:prepare-image-cache.py c9695f1c0bf66b40be1f138f3da7e1ebc147ffde
@ae8062cfb0f028667485e6f1a621ff69e62724fd
N:bounded-command.py 3c9e6eb7c60bf7906c7f605bdf0fa58f65f6a3df
@c9230cc9692a5974728959907afa1f60733409ad
D:memory-references/native-boundary-audit.py 8c0601e110ec1c779e759456d05d64ca045a6232
D:memory-references/native-refusal-controls.py c2f89053088d9f5f615c75f408b6711c5f7b99dd
@e49c71436470851e0a3b295fa56b3b6c749e09b1
N:environment/known-stack-continuation.py 7898e125b8addd4b3badbb0d80e7001481c15741
@e6849d3bdf516099d20c33d3581d523449764018
D:control-tuples/measure-native.py c24f1113690cc7a6611d8f8d412ce5f8e77b5b1e
D:control-tuples/run-bounded.py 629db80c898eb6a19b1dc58a7bf1153bf65214dd
@f11ae9a9025990629aaed70012fc71ebb0ba295d
N:h109/docker-probe.py 2c67207ea5ce6c3d55e59f3ee2341b764028aedf
''')


def python_argument_interface(text):
    """The argument-bearing interface of a Python program, or None.

    Recorded from the AST: lines that read `sys.argv` (through `import sys`
    only), lines among them that take an open argv tail `sys.argv[k:]`
    (variadic or forwarded command), literal positional `add_argument` names
    and literal `add_parser` subcommand names. Not audited, giving None: any
    write, delete or method call on argv; `from sys import argv`; an argv
    attribute of anything but the sys module; any other binding of the sys
    name; `getattr` on sys; `parse_args` or `parse_known_args` with explicit
    arguments; a computed positional or subcommand name. A program with none
    of the recorded forms also gives None (a default program is
    source-only-program's role).
    """
    try: tree = ast.parse(text)
    except (SyntaxError, ValueError, RecursionError): return None
    imports = [a for n in ast.walk(tree) if isinstance(n, ast.Import) for a in n.names]
    modules = {a.asname or a.name for a in imports if a.name == 'sys'}
    if any((a.asname or a.name.split('.')[0]) in modules and a.name != 'sys' for a in imports): return None
    parents = {child: node for node in ast.walk(tree) for child in ast.iter_child_nodes(node)}
    argv, tails, positionals, subcommands = set(), set(), set(), set()
    for n in ast.walk(tree):
        if isinstance(n, ast.ImportFrom) and (n.module == 'sys' and any(a.name in ('argv', '*') for a in n.names)
                                             or any((a.asname or a.name) in modules for a in n.names)): return None
        if isinstance(n, (ast.Global, ast.Nonlocal)) and set(n.names) & modules: return None
        if isinstance(n, ast.Name) and n.id in modules and not isinstance(n.ctx, ast.Load): return None
        if isinstance(n, ast.arg) and n.arg in modules: return None
        if isinstance(n, ast.ExceptHandler) and n.name in modules: return None
        if isinstance(n, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)) and n.name in modules: return None
        if isinstance(n, ast.MatchAs) and n.name in modules or isinstance(n, ast.MatchStar) and n.name in modules: return None
        if (isinstance(n, ast.Call) and isinstance(n.func, ast.Name) and n.func.id in ('getattr', 'setattr', 'delattr', 'vars')
                and n.args and isinstance(n.args[0], ast.Name) and n.args[0].id in modules): return None
        if isinstance(n, ast.Attribute) and n.attr == 'argv':
            if not (isinstance(n.value, ast.Name) and n.value.id in modules and isinstance(n.ctx, ast.Load)): return None
            parent = parents.get(n)
            if isinstance(parent, ast.Attribute) and parent.value is n: return None  # argv.append(...) and the like
            if isinstance(parent, ast.Subscript) and parent.value is n and not isinstance(parent.ctx, ast.Load): return None
            argv.add(n.lineno)
            if (isinstance(parent, ast.Subscript) and parent.value is n and isinstance(parent.slice, ast.Slice)
                    and parent.slice.upper is None and parent.slice.step is None): tails.add(n.lineno)
        if isinstance(n, ast.Call) and isinstance(n.func, ast.Attribute):
            if n.func.attr in ('parse_args', 'parse_known_args', 'parse_intermixed_args') and (n.args or n.keywords): return None
            if n.func.attr in ('add_argument', 'add_parser'):
                first = n.args[0] if n.args else None
                literal = isinstance(first, ast.Constant) and isinstance(first.value, str)
                if not literal: return None
                if n.func.attr == 'add_parser': subcommands.add((n.lineno, first.value))
                elif not first.value.startswith('-'): positionals.add((n.lineno, first.value))
    if not (argv or positionals or subcommands): return None
    return {'argv_lines': sorted(argv), 'argv_tail_lines': sorted(tails),
            'positionals': [list(x) for x in sorted(positionals)], 'subcommands': [list(x) for x in sorted(subcommands)]}


def _introduced(classifier, repo, commit, path, blob):
    """True iff commit holds blob at path and none of its parents does."""
    if not classifier['hex_pin'](commit, 40) or commit in repo.boundaries: return False
    try: parents = classifier['git'](repo.root, 'rev-list', '--parents', '-n', '1', commit, '--').decode().split()
    except ValueError: return False
    if not parents or parents[0] != commit: return False
    requests = [commit + ':' + path] + [p + ':' + path for p in parents[1:]]
    raw = classifier['git'](repo.root, 'cat-file', '--batch-check', '-Z',
                            data=b''.join(r.encode('utf-8', 'surrogateescape') + b'\0' for r in requests))
    lines = raw.rstrip(b'\0').split(b'\0')
    if len(lines) != len(requests): raise ValueError('Python argument role provenance batch mismatch')
    held = [line.split()[0].decode() == blob and line.split()[1:2] == [b'blob'] if len(line.split()) == 3 else False for line in lines]
    return held[0] and not any(held[1:])


def _role_schema(classifier, catalog, entry, required, label):
    """Schema, revision and conflict checks of the reviewed source roles."""
    if (set(entry) != required or not isinstance(entry['path'], str) or not isinstance(entry['source_blob'], str)
            or not isinstance(entry['purpose'], str) or not entry['purpose'].strip() or not isinstance(entry['interface'], dict)
            or not isinstance(entry['provenance'], dict) or set(entry['provenance']) != {'commit', 'path', 'blob'}
            or not all(isinstance(v, str) for v in entry['provenance'].values())):
        raise ValueError('invalid ' + label + ' definition')
    p = entry['path']; revision = entry['input_revision']
    if not isinstance(revision, str) or not classifier['hex_pin'](revision, 40): raise ValueError(label + ' requires a full commit revision')
    if any(e.get('path') == p and e.get('input_revision') == revision and e is not entry for e in catalog['standalone']):
        raise ValueError('conflicting standalone definitions: ' + p)


def _role_current(classifier, repo, catalog, entry, pins):
    """False when a later revision supersedes or changed a pinned object."""
    p = entry['path']; revision = entry['input_revision']
    if revision != repo.ref:
        if any(e.get('path') == p and e.get('input_revision') == repo.ref for e in catalog['standalone']): return False
        if not all(_current(repo, q, b) for q, b in pins): return False
        if not _historical_objects(classifier, repo, revision, pins):
            raise ValueError('unverifiable historical runner demonstration: ' + revision + ':' + p)
    elif not all(_current(repo, q, b) for q, b in pins): raise ValueError('standalone definition source mismatch: ' + p)
    return True


def python_argument_root(classifier, graph, catalog, entry, reviewed=None):
    """H996: a reviewed argument-bearing Python program as a source-only role.

    The definition binds the bare entry prefix ['python3', '-B', P] (never a
    concrete argument), the source blob, its genuine top-level entry line, the
    interface python_argument_interface records for that blob, and provenance:
    the commit that introduced that blob at P, which must be in the reviewed
    set. The configured CLI, module CLI and unittest guards are unchanged: a
    program matching one is refused here. The root is never a validated or
    passing runner and anchors nothing: no execution, pass, read-anchor,
    fixture, helper, child, generated-output, proof or runtime credit. A later
    revision keeps it while the blob is unchanged and the recorded commit holds
    it; a current definition of the same path supersedes it.
    """
    repo = graph.repo
    reviewed = REVIEWED_PYTHON_ARGS if reviewed is None else reviewed
    required = {'path', 'input_revision', 'source_blob', 'command', 'kind', 'entry_line', 'interface', 'provenance', 'purpose'}
    _role_schema(classifier, catalog, entry, required, 'Python argument role')
    p = entry['path']; revision = entry['input_revision']; doc = entry['provenance']
    if entry['command'] != ['python3', '-B', p] or not p.endswith('.py'):
        raise ValueError('unsupported Python argument role invocation: ' + p)
    if doc['path'] != p or doc['blob'] != entry['source_blob'] or (p, entry['source_blob'], doc['commit']) not in reviewed:
        raise ValueError('unreviewed Python argument role: ' + p)
    if not _role_current(classifier, repo, catalog, entry, [(p, entry['source_blob'])]): return
    if repo.tree[p][0] not in ('100644', '100755') or p not in repo.texts:
        raise ValueError('unsupported Python argument role invocation: ' + p)
    if not _introduced(classifier, repo, doc['commit'], p, entry['source_blob']):
        raise ValueError('Python argument role lacks its introducing provenance: ' + p)
    try: lines = classifier['entrypoint_lines'](repo.bytes(p))
    except (SyntaxError, ValueError, RecursionError): lines = set()
    if type(entry['entry_line']) is not int or entry['entry_line'] not in lines:
        raise ValueError('Python argument role lacks its top-level entry: ' + p)
    if any(classifier[f](repo, p) is not None for f in ('declared_configured_cli', 'declared_module_cli', 'declared_unittest')):
        raise ValueError('Python argument role matches a configured CLI or unittest form: ' + p)
    interface = python_argument_interface(repo.texts[p])
    if interface is None: raise ValueError('Python argument role lacks an audited argument interface: ' + p)
    if canonical(interface) != canonical(entry['interface']): raise ValueError('Python argument role interface mismatch: ' + p)
    identity = PYTHON_ARGS_PREFIX + p
    graph.root(p, 'source-only Python argument entry', shlex.join(entry['command']), p, entry['entry_line'], root_id=identity)
    if identity not in graph.roots: return
    graph.roots[identity].update({'source_only': True, 'python_argument_role': True, 'source_blob': entry['source_blob'],
        'purpose': entry['purpose'], 'interface': interface, 'provenance': doc, 'source_declaration_revision': revision,
        'validation_at_measured_revision': {'status': 'unavailable', 'command': entry['command'],
            'reason': 'Reviewed argument-bearing Python entry; the bare prefix needs arguments and no argument is recorded. Source role only, never run or certified to pass. No read anchor, fixture, helper, child, generated-output, proof or runtime credit.'}})


NONPY_ENTRY_KIND = 'nonpython-entry-source-role'
NONPY_ENTRY_PREFIX = 'nonpy-entry:'
# H997 (gh coord#1331, X1E-NONPY-ROLE): the one shebang each interpreter is
# accepted with; the command names that interpreter explicitly.
NONPY_SHEBANGS = {'.sh': ('bash', '#!/usr/bin/env bash', True), '.mjs': ('node', '#!/usr/bin/env node', False),
                  '.cjs': ('node', '#!/usr/bin/env node', False)}
# Each reviewed live shell or Node program, bound to (path, source blob, one
# commit that introduced that blob at that path; where cherry-picks introduce
# the same blob twice, the earlier one, and the other is refused as unreviewed). Nothing else is
# promoted: another file, blob or provenance commit fails, and no argument,
# read, helper, child or output is ever recorded or credited.
REVIEWED_NONPY_ENTRIES = _review_table('''
@0834bc67b042a63a8c804162781802245ae59c98
D:shared-translator/address-fixture.mjs 7b43c79b13a92043dc9c6576fd1b45c6a574026d
D:shared-translator/address-validate.sh 6f9014aa569e25b415aba09f7ef1c37f4a4dd3ea
@0bdac88bfacec822c7157b7d5a3e713894571888
N:h81-memory-controls.mjs f923767bff5e51583c3a445950cc22e978bd6505
N:primitive-return/functional83.mjs 017a361b9d7ba28570a1ea323ff2da2f11e35530
@15302eb51e3df48b9d8d46eaf50348dd1deddfb2
D:shared-translator/read-bounds-validate.sh 05994407de7956849db17f9c7188b90376a3556d
N:h109/scripts/registration-parent-checks.sh 63e8cc7662f430c985a20d7147a4dd404b043a5c
@17f2902cdc6ab848317fc82e31a90ad2d7c4fba8
D:memory-references/fixtures.cjs 903cd31f868d6af169e7e743519131eb0e63131e
D:memory-references/prepare-admission.cjs 50a6ff09bbe39b55d8914427ea1f242db898c554
D:memory-references/source-transport.mjs 880d9e38ef8476e5543075ee1fc4c703b6917880
@18df52507a1cb6136e1340aee565964cdf6f012b
N:browser-baseline-checks.sh b12fe571b40579d911cbe4b4103446524e7597a9
N:browser-edit-controls.sh c941f40a9ea94ecef7b1855f33872426349baeec
N:browser-smoke-checks.sh 1e6b7d76f5cc553ab1aa64f0147408bad52057f5
N:browser-wire-audit.cjs 4c0ac946c684d5b825ab2c5d3b839b370522c832
N:build-browser-baseline.sh 6945c2448ded7e30723144a1e71607f21b68847c
N:link-symbol-diagnostic.sh 5e5c708c97d011052ae1e98cdddde9689a84e913
N:mcp-baseline-checks.sh 26574e91841f4e49d3125f56ca287688aaeb93b8
N:native-lsp-baseline.sh f3991cada4632b3bedc72fcd09b105b84a93386b
@2207c1bba286538fd63e4a0ff4960ed4a593a8ab
U:baseline-20261028/invocations/retries/harness.sh 67db42718e4d578b56d910e7e82fac1b732c23e0
@23a42307b1b336e5477c0bb5c8d8bfe6415b6ea6
N:published-f77-browser-build.sh b5361e73f7027cab3d7393477ab97f9239ac00cc
N:published-f77-browser-checks.sh a310340cbbd46a253914122b15fa58c10b505230
N:published-f77-browser-edit.sh 71f5edd301dd1fd34b38d4e837fc688c20a7e8a1
N:published-f77-browser-extras.sh 416c6c9d7a3719ed67920b64c8542162c7c1628d
N:published-f77-browser-smoke.sh cf153c3b1865aa6895202676bf29c0882980c959
N:published-f77-mcp.sh f3f3c9ece70022adeb854c9532df41f3b6337d93
N:published-f77-native-build.sh a0d99da1154b1e1bde0e38b63ffc7cd543c04bd0
N:published-f77-native-lsp.sh 08d725fe11cf9be46012e40d0f5f8c538adb680b
N:published-f77-validation.sh 515fd0bb1a379970d49bd411c7cfba586534758d
N:published-f77-wasm-build.sh 31c07b3799d6cd108bf29e5593bfdf2dad655386
@252be5a095f50a75c91e7b9ae55650eb4f6d7463
N:published-8495-controls.mjs c1e0b5e9be554992cdfa67ec097ceeb9b43ce322
N:request-identity/selector-negatives.mjs f79858cb61bf4a126b71dcd7cebeea2fa55dfc02
@354dadf752721c3caffeaf916c3ccf07a243c449
N:published-b86a-api.sh 807d5d2b9437c62910b0dfda56e95e241b3a5f97
N:published-b86a-mcp.sh d1b955a0bc0ebdcc8d5de0ad2f8071d164cb534e
@369739e39533161cdd077a06bf6842bf71d1baa3
N:h35-gates.sh bb70b12b4b5552bf525c128602c9ba61301aec46
@3ff9a2ea968af583d54f83defa62f537b28c235b
N:browser-control-completion.cjs 82ecd2d5a0e038c2cf8ef4949a72837a335ff9cf
N:hardening-browser-build.sh 6fd0f7517a5046993958792bd08f0df7a66a8315
N:hardening-browser-checks.sh a3fda3aa57ad433c25f74c987902dc428d99bf89
N:hardening-browser-controls.sh 53265ee586aa6620934ef84749c37aab62f9521c
N:hardening-browser-edit.sh ce5cd598f667ab741c3dfd68fbe3412fab7cdb0b
N:hardening-browser-smoke.sh 478ac8cd2e128af109dd094abf148a59498bf881
N:hardening-native-build.sh 5f516e8b52f5a3bdc1fd7b151c75ed48fec2b7bd
N:hardening-native-checks.mjs 2f13d3d616921e271ae7cb1f2dfe99ee0454c382
N:hardening-native-checks.sh ab70817d323bfa5c25dbba5b80aae363e1d1a699
N:hardening-validation.sh 169e84907b0e34ec25750b0a70d3ffe97509865f
N:sort-conformance.sh a66c463a355476c8c906e4ba46807881f96bbac1
N:startup-investigation.mjs a918cd39a422c15d82869a7f4b587dc2ab7d9d83
@40bcc364c4f0caf313ebe8c65e1da66d2ad75b1b
N:published-9584-api.sh 8d95e992c635c46c4971fa65dbcf5befe646e7c3
N:published-9584-mcp.sh 8b0f45ccbe12441d761f7b9bdd3bbfb5ce0d32c1
@44d89439afd8fe7aca251cd5693b5b7ea36cf603
D:shared-translator/environment-fixture.mjs 03b2c7c55004a710a0d7a053df0550e48eeeaf40
D:shared-translator/environment-validate.sh 9460e5febcad1c954204902e5b7a505c5a5f79da
@4a66db87c8ed848aef4c2ac1732b1df326c6fa97
D:shared-translator/fixed-byte-fixture.mjs 207f8ff6474cfed3a6443223eac989976bb3d9bb
D:shared-translator/fixed-byte-validate.sh b4d495f62a04cab7ec344489563d20f63f832f33
@4f5e84d8d3f90919c78e904697e5779fd3d0ce66
N:readbounds/scripts/additional-functional.sh 54fddfe266f4d61562dc867195421d1819ba6419
N:readbounds/scripts/axiom-gates-post-rebase.sh bdffe31da9f3c37864b74b8bf0f349654409db64
N:readbounds/scripts/capture-gate.sh da4a38d9db9a361b9f304a5f2adeafdde9b44d95
N:readbounds/scripts/dependency-gate.sh 1727e98a8e6d2b3bb0f4b79dc84cc5739746754f
N:readbounds/scripts/functional-checks-recovered.sh bbad552d675f721adb47df555ac86b85916b8606
N:readbounds/scripts/functional-checks.sh 46ac712e7df5083892b5634418b3aa9c2b874589
N:readbounds/scripts/native-build.sh dfa96b4d7f60f7dd4f78ed60a44114a93de21fdf
N:readbounds/scripts/proof-gates-post-rebase.sh 05160602dbedd46107efa412c8838bf14c0787d1
@5a21cb291a6d2f0bd2e1aa6574c14e895453c78b
N:environment/scripts/B-kernel-controls.sh 971e181a0d2b877229eeefb48306e9e6fa86f62d
N:environment/scripts/address-marker-gate.sh a3fd70679b39c94289498f6900b24ad6495dc517
N:environment/scripts/browser-build.sh 9a4017546027af0c77eef544ea3ba29f8198cde4
N:environment/scripts/compile-producer-args.mjs e60007cd18e4f58d829c5cd85da0f5766cf34c6d
N:environment/scripts/finite-gate.sh 78e4b5909d6dd81671cedb28178437804072e407
N:environment/scripts/fixed-byte-gate.sh d4197132f138040fc277bd006f6393e0455ec9b9
N:environment/scripts/lake-prefix.sh 2f2f8473b56c00259bcd400d6770c373bfea38cb
N:environment/scripts/marker-gate.sh 1f6e42cf641de1003b3d9dca483f4aa47af9ff7d
N:environment/scripts/mcp.sh 72cf3794cda2352c1fba6fc5bfbc02295b8a9b73
N:environment/scripts/state-refusal-controls.mjs d65587568f7e0fe0cb3b5b15b19b76d386eb2152
N:environment/scripts/wasm-build.sh 3450e74ddad66d1deaf08e1c93f82023ce75cd85
@6842e804ce6a3605e31274d1746483b65eddeb09
D:shared-translator/dynamic-bytes-fixture.mjs e823ea06bac4e522d24ff13eac1ffaff3342066f
@6fceb880a8696cedecd6f2a55801c853e193ce2d
U:repairs/group02-init-commands.sh fafe6ea30e62fdd93d33fefb3218567a66724617
@77913ac1cff1147d1129caea943c881b4aa61ec7
D:shared-translator/environment-decoder-validate.sh c9e849741ec9f96867766ecf7346f02c4d2389cf
@7ce3c2a5ba098b705fca1c39c01fef467477fe6c
U:repairs/group02-commands.sh af739fcdacb228adf9160e09b2b6c15918f77234
@85f39a01073565da7edef0a778abec2b7df9b1d7
N:hardening-wasm-build.sh 8c614bf7504ee59a1da79326f8408b4dec94e095
@9465af2e2b24c438d98bc46b1dfaf890fb9adcb3
N:h40-corpus-check.sh 2e9202333efe8ddc8d9ad0fc20f67af1c11ee11e
N:h40-full-gates.sh ee21b4e3f0534d4282108db2d6ef38148527b3a8
N:h40-mcp-checks.sh d2250ce009385237b7836fb88730724eeeffb295
N:h40-policy-checks.sh ee410e7d961e8e65077e722eaa676df651265329
N:h40-testsuite-check.sh 5e37e8524625eb35d21f977c842e4f5084799070
@957e5defaa3c2e32df1e692d8781e0d89fed5199
D:shared-translator/primitive-return-control-tuple-fixture.mjs a756a8e23bf3b19577268e44e960782928fe23b9
D:shared-translator/primitive-return-fixture.mjs 20f5d5f88b83ddfda3de8cc8168c69908a71d0dd
D:shared-translator/primitive-return-validate.sh 074e6d15f01d4bfd67c2bd0af103663f96231923
@a1729b9c6283b199d3249b11c6224165798a00bb
N:build-wasm-baseline.sh 579f45953b9ad98e4a5e8934aad0f54009d4dea5
@ae8062cfb0f028667485e6f1a621ff69e62724fd
N:bounded-keys.sh c530a67b2b5ef6283bbfe9113d88c39e655f21c6
N:build-native-baseline.sh a9b7a2401b3bafae04de86bcb707eecd60e44e26
N:fresh-spec-controls.mjs 667daf209b2060a60c0c3079502c320f138b05b0
N:native-baseline-checks.sh 63a3811ce26da1c4bcfd5435781e65f9ea9c6d07
N:prepare-baseline.mjs 086f041b6ffd9ecb7451479bf7d0c20e8799d33e
@b44f0de87c2ab845b79c9d84004dcb7c91babded
D:shared-translator/bounded.sh a6686039c6dec3b35d2f06a2b8403be31ff9dd42
D:shared-translator/h90-base-census.sh 299ca2604fb7206c03d98bd084ca2b714158e078
D:shared-translator/h90-census-command.sh 1004774e354dd25b941d6331ec0c52d92a2c86f6
D:shared-translator/h90-validate.sh a67ec66c28490d60be84f27466897389d27dc82c
D:shared-translator/narrow-local-fixture.mjs 8fb3e82889a9bef284ecd92f2c9cf71be89b2a25
@bc4cb33ff40e97e88c04787419aaa0a16b618026
D:shared-translator/fresh-construct-fixtures.mjs f6731c57f457a2b2b0fbbe57d6e67dbbafde9f40
@c21364ef94c9f9102065b51edd00dd1cb904661d
N:address/state-refusal-controls.mjs d65587568f7e0fe0cb3b5b15b19b76d386eb2152
@c9230cc9692a5974728959907afa1f60733409ad
D:memory-references/native-source-controls.mjs 3e46b94bea4cff0efe8f108ffd61d99838d79c63
@d74b24de8dd2560366ed47ec8a5d96e3351e9378
D:shared-translator/environment-proof-validate.sh db00b98f108dd43cbe5e9d46c01f405ae22f4a18
@dc3f0ffc0431f87441e7bc3b8f263b38d02d229b
N:published-8495-api.sh 9022e73f1b542446eae3c5e61ebd6197d0a2262a
N:published-8495-controls.sh 74b1ebf5ffd8efc6b6ee01c8c24d398071eb42d0
@e01ff4a52ffa532e47d3cb163bb97245f436e3b2
N:compact-runtime-cache.sh 05e0333828e32952e0ff2af01265d7dd7b4ef324
N:gmp-serial.sh c6defb5a7ac2f5e6cf98a114d8d6bfe69884280c
N:wasm-inside.sh c7400f29384cfd151e157ff709a4707545d731a2
@e49c71436470851e0a3b295fa56b3b6c749e09b1
N:environment/scripts/checks.sh 63f4e50b51509f7a6273aa53fec3c9357c880ecc
N:environment/scripts/historical/checks.sh 0887f3a28631e1853e860a9355d69580fcb5f615
N:environment/scripts/historical/remaining-checks.sh c37ac7de446ea7c9f83c6fde04013ce82801695b
N:environment/scripts/remaining-checks.sh 83e197d395972de024ac087aad4ebb3203a14732
@e6865a2c7347df62db74bfc8b30aa00dce409c74
N:h109/scripts/registration-lake.sh 9ac8f8bece17c2d01dd2653578f24f97de1dd24e
@e778f14e03877c102aaaf739c60ecaccc9a989e5
D:shared-translator/compatibility-fixtures.mjs 7eb7688e61d8f342b8549078635414d79f577e82
D:shared-translator/compiler-coverage-fixtures.mjs dda8193f85512314ae76a2b7740d8591990f26dd
D:shared-translator/composed-fixture.mjs b0af1badf585f4023819027bb1d8c6b3f85ba1cd
D:shared-translator/modality-fixture.mjs 1e2484febd93269030f7d7956e7f9958dd448b21
@eef016814a3deddf5e9ea85a97fadfc0ec73a114
N:readbounds/axiom-gates.sh 6d77f69e2a86fa3d1ab1121b4cc9408aeb19fabd
N:readbounds/module-gates.sh bd84543e2eab25c0fc8db0de1d7cff7cf27718f8
N:readbounds/proof-gates.sh d1c49af7756b40057993698f72fb3394367d0b37
''')


def nonpython_entry_interface(path, text):
    """The audited entry interface of a shell or Node program, or None.

    Recorded: the interpreter, the shebang line (required for bash, optional
    for Node) and the first top-level statement line (column 0; for Node the
    first one that is not an import declaration). Not audited, giving None:
    another suffix (`.js` depends on a package type), a `.test.` name (the
    node-test kind keeps that naming), any other shebang, ambiguous line
    breaks, a NUL byte, a column-0 shell line with a `return` command (a
    sourced library), a shell file whose column-0 lines are all function
    definitions, assignments or set/shopt, any Node `export` declaration,
    in a `.cjs` file any bare `exports` reference, `module.exports` or
    `module[...]` access or Object.assign/defineProperty on module (a CommonJS
    library), or no top-level statement. The shell check is lexical: an
    indented `return` is not distinguished from one in a function body, so
    the review set, not this parser, is the gate.
    """
    suffix = posixpath.splitext(path)[1]
    if suffix not in NONPY_SHEBANGS or '.test.' in posixpath.basename(path): return None
    if not isinstance(text, str) or not _plain_lines(text) or '\0' in text: return None
    interpreter, shebang, required = NONPY_SHEBANGS[suffix]
    lines = text.split('\n'); first = lines[0]
    if first.startswith('#!'):
        if first != shebang: return None
    elif required: return None
    else: shebang = None
    if interpreter == 'bash':
        top, until = [], None  # column-0 lines outside here-document bodies
        for n, line in enumerate(lines[1:], 2):
            if until is not None:
                if line.lstrip('\t') == until: until = None
                continue
            if line[:1] not in ('', '#', ' ', '\t'): top.append((n, line))
            heredoc = re.search(r'<<-?\s*(["\']?)(\w+)\1', line)
            if heredoc and '<<<' not in line: until = heredoc[2]
        if until is not None: return None
        if any(re.search(r'(?<![\w$-])return\b', line) for _, line in top): return None
        definition = r'(?:function\s+[\w-]+|[\w-]+\s*\(\s*\))\s*\{?\s*$|\}\s*$|(?:export\s+|readonly\s+|declare\s+(?:-\w+\s+)*)?\w+=|(?:set|shopt)\s'
        entry = top[0][0] if any(not re.match(definition, line) for _, line in top) else None
    else:
        masked = (' ' * len(first) + text[len(first):]) if shebang else text
        code = _js_mask(masked, True)[0]
        if re.search(r'(?<![\w$.])export\b', code): return None
        if suffix == '.cjs' and re.search(r'(?<![\w$.])exports\b(?!\s*:)|(?<![\w$.])module\s*(?:\.\s*exports\b|\[)'
                                         r'|\bObject\s*\.\s*(?:assign|defineProperty|defineProperties)\s*\(\s*module\b', code): return None
        imports = {code.count('\n', 0, m.start()) + 1 + k for m in re.finditer(r'(?m)^import\b(?!\s*[(.])(?:[^{};\n]*\{[^}]*\}[^;\n]*|[^{};\n]*)', code)
                   for k in range(m.group(0).count('\n') + 1)}
        entry = next((n for n, line in enumerate(code.split('\n'), 1) if line[:1] not in ('', ' ', '\t') and n not in imports), None)
    if entry is None: return None
    return {'interpreter': interpreter, 'shebang': shebang, 'entry_line': entry}


def nonpython_entry_root(classifier, graph, catalog, entry, reviewed=None):
    """H997: a reviewed live shell or Node program as a source-only role.

    The definition binds the exact command [interpreter, P] (never an
    argument), the source blob, the interface nonpython_entry_interface
    records for that blob (interpreter, shebang, top-level entry line) and
    provenance: the commit that introduced that blob at P, which must be in
    the reviewed set. Python programs keep source-only-program and the H996
    role, `.test.` Node files keep node-test, manual reproducers are
    unchanged. The root is never a validated or passing runner and anchors
    nothing: no execution, pass, read-anchor, fixture, helper, child,
    generated-output, proof or runtime credit. A later revision keeps it while
    the blob is unchanged and the recorded commit holds it; a current
    definition of the same path supersedes it.
    """
    repo = graph.repo
    reviewed = REVIEWED_NONPY_ENTRIES if reviewed is None else reviewed
    required = {'path', 'input_revision', 'source_blob', 'command', 'kind', 'interface', 'provenance', 'purpose'}
    _role_schema(classifier, catalog, entry, required, 'non-Python entry role')
    p = entry['path']; revision = entry['input_revision']; doc = entry['provenance']
    shape = NONPY_SHEBANGS.get(posixpath.splitext(p)[1])
    if shape is None or entry['command'] != [shape[0], p] or '.test.' in posixpath.basename(p):
        raise ValueError('unsupported non-Python entry role invocation: ' + p)
    if doc['path'] != p or doc['blob'] != entry['source_blob'] or (p, entry['source_blob'], doc['commit']) not in reviewed:
        raise ValueError('unreviewed non-Python entry role: ' + p)
    if not _role_current(classifier, repo, catalog, entry, [(p, entry['source_blob'])]): return
    if repo.tree[p][0] not in ('100644', '100755') or p not in repo.texts:
        raise ValueError('unsupported non-Python entry role invocation: ' + p)
    if not _introduced(classifier, repo, doc['commit'], p, entry['source_blob']):
        raise ValueError('non-Python entry role lacks its introducing provenance: ' + p)
    interface = nonpython_entry_interface(p, repo.texts[p])
    if interface is None: raise ValueError('non-Python entry role lacks an audited entry interface: ' + p)
    if canonical(interface) != canonical(entry['interface']): raise ValueError('non-Python entry role interface mismatch: ' + p)
    identity = NONPY_ENTRY_PREFIX + p
    graph.root(p, 'source-only non-Python entry', shlex.join(entry['command']), p, interface['entry_line'], root_id=identity)
    if identity not in graph.roots: return
    graph.roots[identity].update({'source_only': True, 'nonpython_entry_role': True, 'source_blob': entry['source_blob'],
        'purpose': entry['purpose'], 'interface': interface, 'provenance': doc, 'source_declaration_revision': revision,
        'validation_at_measured_revision': {'status': 'unavailable', 'command': entry['command'],
            'reason': 'Reviewed live shell or Node program; the command is the bare interpreter prefix, which may need arguments, and no argument is recorded. Source role only, never run or certified to pass. No read anchor, fixture, helper, child, generated-output, proof or runtime credit.'}})


_roles = Path(__file__).with_name('roles.py')  # H999/H1015 Lean gate and H1051 Python import source roles
exec(compile(_roles.read_bytes(), str(_roles), 'exec'))



SOURCE_ROLE_KINDS = {SOURCE_ONLY_KIND: source_only_program, NODE_MODE_KIND: node_mode_root, PYTHON_ARGS_KIND: python_argument_root,
                     NONPY_ENTRY_KIND: nonpython_entry_root, LEAN_CHECK_KIND: lean_check_root,
                     LEAN_FIXTURE_KIND: lean_fixture_root, DOC_REF_KIND: documentation_reference_root}
# Kinds dispatched after every other standalone definition, so they can bind
# the roots those definitions create (H1051 importers).
LATE_SOURCE_ROLE_KINDS = {PY_IMPORT_KIND: python_import_root}


def persisted_module_entries(classifier, graph, catalog, rows):
    """H979: opt-in persistence of reviewed routes.module_entries claims.

    Each row is an exact claim already present in routes.module_entries. At
    its own revision the ordinary check applies and the row adds nothing. At a
    later --ref it is credited only if the passing runner definition at that
    revision (unittest or runnable entry point), every frame and the target
    are the same blobs now and at the recorded revision, and the collector,
    exact CPython version, operation, frame line and entered code hash checks
    of the ordinary claim pass on the measured bytes. A changed or missing
    object grants nothing; a mismatch of the recorded objects is rejected.
    Module entry is execution coverage only, never fixture or proof credit.
    """
    repo = graph.repo
    if not rows: return
    if not isinstance(rows, list): raise ValueError('invalid persisted module entries')
    reviewed = {canonical(e) for e in catalog.get('module_entries', []) if isinstance(e, dict)}
    seen = set(); observer = None
    for row in rows:
        if not isinstance(row, dict) or set(row) != MODULE_ENTRY_KEYS: raise ValueError('invalid persisted module entry')
        key = canonical(row)
        if key in seen: raise ValueError('duplicate persisted module entry')
        seen.add(key)
        if key not in reviewed: raise ValueError('persisted module entry is not a reviewed routes.module_entries claim')
        if row['input_revision'] == repo.ref: continue
        runner = row['runner']
        if not isinstance(runner, str) or not runner.startswith('validated:'): raise ValueError('persisted module entry needs a validated runner')
        path = runner[len('validated:'):]
        definitions = [e for e in catalog['standalone'] if e.get('path') == path and e.get('input_revision') == row['input_revision']]
        if (len(definitions) != 1 or definitions[0].get('kind') not in ('unittest', 'runnable-entrypoint')
                or not isinstance(definitions[0].get('source_blob'), str)):
            raise ValueError('persisted module entry lacks its passing runner definition')
        source_blob = definitions[0]['source_blob']; target = row['target']; frames = row['frames']
        if not isinstance(target, str) or not target.endswith('.py') or not isinstance(row['target_blob'], str):
            raise ValueError('invalid persisted module entry target')
        if not _frames_current(repo, frames, [(path, source_blob), (target, row['target_blob'])]): continue
        _check_lines(repo, frames)
        if frames[0]['path'] != path: raise ValueError('entered module chain lacks root')
        if not _historical_objects(classifier, repo, row['input_revision'],
                sorted({(f['path'], f['blob']) for f in frames} | {(path, source_blob), (target, row['target_blob'])})):
            raise ValueError('persisted route objects differ at recorded revision ' + row['input_revision'])
        original, root = _anchor_root(graph, runner, frames)
        if root is None or root.get('runner_kind') not in ('unittest', 'runnable-entrypoint'): continue
        if root.get('source_only') and root.get('source_blob') != source_blob: continue
        if observer is None: observer = _module_observer(classifier)
        _credit_module_entry(classifier, graph, row, original, root, key, observer, ':persisted-module:',
            {'consumer_route': {'kind': 'persisted-module-entry', 'validated_revision': row['input_revision'], 'runner_definition_blob': source_blob}})


def _module_observer(classifier):
    """The trace helper that fingerprints code, and its own collector pin."""
    helper = Path(classifier['__file__']).with_name('check-tests-used-trace.py')
    spec = classifier['importlib'].util.spec_from_file_location('tests_used_module_identity', helper)
    observer = classifier['importlib'].util.module_from_spec(spec); spec.loader.exec_module(observer)
    return observer, hashlib.sha256(helper.read_bytes()).hexdigest()


def _credit_module_entry(classifier, graph, entry, original, root, key, observer, label, extra=None):
    """The one entered-module identity check, then its execution chain.

    Shared by current claims and H979 persisted ones; the caller has checked
    the claim's schema, revision, runner root and target pin. The collector is
    reviewed, the CPython version exact, the operation the module-entry one,
    the frame line in range and the module code hash one of the measured
    bytes' compilations; every frame is the measured object from the root.
    """
    repo = graph.repo; target = entry['target']; observer, collector = observer
    if not classifier['reviewed_module_collector'](repo, entry['collector_sha256'], collector): raise ValueError('unreviewed module entry collector')
    if (entry['python'] != list(classifier['sys'].version_info[:3]) or any(type(n) is not int for n in entry['python'])
            or classifier['sys'].implementation.name != 'cpython'):
        raise ValueError('UNVERIFIABLE module code identity: exact CPython version required')
    if entry['operation'] != MODULE_ENTRY_OPERATION: raise ValueError('unsupported module entry operation')
    if type(entry['module_frame_line']) is not int or not 0 <= entry['module_frame_line'] <= len(repo.texts[target].splitlines()):
        raise ValueError('invalid entered module frame location')
    fingerprints = observer.source_code_hashes(repo.texts[target].encode('utf-8', 'surrogateescape'), '<measured>')
    if entry['module_code_sha256'] not in fingerprints['module_code_hashes']: raise ValueError('entered module code mismatch')
    frames = entry['frames']
    if not isinstance(frames, list) or not frames or not isinstance(frames[0], dict) or frames[0].get('path') != root['path']:
        raise ValueError('entered module chain lacks root')
    for frame in frames:
        if (not isinstance(frame, dict) or set(frame) != {'path', 'blob', 'line'}
                or frame['path'] not in repo.tree or repo.tree[frame['path']][2] != frame['blob']
                or type(frame['line']) is not int or not 1 <= frame['line'] <= len(repo.texts.get(frame['path'], '').splitlines())):
            raise ValueError('invalid entered module caller')
    excluded = classifier['excluded']
    if excluded(target) or any(excluded(f['path']) for f in frames): return
    identity = original + label + hashlib.sha256(key).hexdigest()
    graph.roots[identity] = {**root, 'derived_from': original, 'entered_module': target,
        'module_entry': {k: entry[k] for k in ('module_code_sha256', 'module_frame_line', 'python', 'collector_sha256')}, **(extra or {})}
    chain = {'root': identity, 'entry': graph.roots[identity], 'edges': []}
    for caller, callee in zip(frames, frames[1:] + [{'path': target}]):
        chain = {**chain, 'edges': chain['edges'] + [{'source': caller['path'], 'target': callee['path'],
            'line': caller['line'], 'operation': entry['operation'], 'kind': 'executes', 'validated_for': identity}]}
        graph.observed.append((callee['path'], chain))


def validated_module_entries(classifier, graph, entries):
    """Reviewed positive execution claims, never static imports or data edges.

    Exact entered module code, native reads preceding entry, successful paired
    runs and collector provenance are validated deliberately outside inventory.
    These deterministic definitions retain source/code/interpreter bindings;
    ordinary inventory only compiles bytes to compare code, never executes them.
    """
    if not isinstance(entries, list): raise ValueError('invalid module entry definitions')
    if not entries: return
    repo = graph.repo; observer = _module_observer(classifier); seen = set()
    for entry in entries:
        if not isinstance(entry, dict) or set(entry) != MODULE_ENTRY_KEYS: raise ValueError('invalid entered module claim')
        key = canonical(entry)
        if key in seen: raise ValueError('duplicate entered module claim')
        seen.add(key)
        if entry['input_revision'] != repo.ref: continue
        root = graph.roots.get(entry['runner'])
        if root is None or root['kind'] != 'validated standalone runner' or root.get('source_only'):
            raise ValueError('entered module requires passing current runner')
        target = entry['target']
        if target not in repo.tree or not target.endswith('.py') or repo.tree[target][2] != entry['target_blob']:
            raise ValueError('entered module source pin mismatch')
        _credit_module_entry(classifier, graph, entry, entry['runner'], root, key, observer, ':module:')


def same_revision_reads(ref, fragments):
    """Persisted reads recorded at the measured revision join the ordinary reads."""
    for section in CONSUMER_SECTIONS: merge_fragment_entries(section, [], fragments[section])
    fragments['reads'] = fragments['reads'] + [row for row in fragments['persistent_reads']
                                               if isinstance(row, dict) and row.get('input_revision') == ref]


def isolated(classifier, controls):
    """Synthetic controls supply their own catalogs, never committed fragments."""
    committed = classifier['read_fragments']
    classifier['read_fragments'] = lambda _: {key: [] for key in FRAGMENT_SECTIONS + ('roles', 'fixtures') + CONSUMER_SECTIONS}
    try: controls()
    finally: classifier['read_fragments'] = committed


def add_consumer_routes(classifier, graph, catalog, fragments):
    """Entry point from inventory(), after every other root is known."""
    persisted_reads(classifier, graph, catalog, fragments['persistent_reads'])
    static_routes(classifier, graph, fragments['static_routes'])
    git_policies(classifier, graph, fragments['git_policies'])
    persisted_module_entries(classifier, graph, catalog, fragments['persistent_module_entries'])


def _control_repository(classifier, root):
    """A fresh Git repository at root; commit(changes, message) returns its Repository."""
    git = classifier['git']
    root.mkdir(); git(root, 'init', '-q')
    def commit(changes, message):
        for path, text in changes.items():
            (root / path).parent.mkdir(parents=True, exist_ok=True); (root / path).write_text(text)
        git(root, 'add', '-A', '-f')
        git(root, '-c', 'user.name=Control', '-c', 'user.email=control@example.invalid', 'commit', '-qm', message)
        return classifier['Repository'](root, 'HEAD')
    return commit


def fragment_controls(classifier):
    import copy
    read_fragments = classifier["read_fragments"]
    merge_fragment_entries = classifier["merge_fragment_entries"]
    with tempfile.TemporaryDirectory() as tmp:
        directory = Path(tmp)
        first = {'path': 'tests/a', 'input_revision': 'a' * 40, 'source_blob': 'b' * 40}
        second = {'path': 'tests/b', 'input_revision': 'a' * 40, 'source_blob': 'c' * 40}
        (directory / 'z.json').write_text(json.dumps({'schema_version': 1, 'catalog_extensions': {'standalone': [second]}}))
        (directory / 'a.json').write_text(json.dumps({'schema_version': 1, 'routes': {'standalone': [first]},
                                                        'roles': [{'path': 'tests/note'}],
                                                        'fixtures': [{'path': 'tests/fixture'}]}))
        fragments = read_fragments(directory)
        assert fragments['standalone'] == [first, second]
        assert fragments['roles'][0]['path'] == 'tests/note'
        assert fragments['fixtures'][0]['path'] == 'tests/fixture'
        assert merge_fragment_entries('standalone', [first], [copy.deepcopy(first), second]) == [first, second]
        # JSON booleans and numbers compare equal in Python but are distinct claims.
        try: merge_fragment_entries('standalone', [dict(first, entry_line=1)], [dict(first, entry_line=True)])
        except ValueError: pass
        else: raise AssertionError('boolean/number conflict accepted')
        conflict = dict(first, source_blob='d' * 40)
        try: merge_fragment_entries('standalone', [first], [conflict])
        except ValueError: pass
        else: raise AssertionError('conflicting fragment accepted')
        for invalid in ('{"schema_version":1,"schema_version":1}',
                        '{"schema_version":1,"routes":{"unknown":[]}}',
                        '{"schema_version":1,"roles":{}}'):
            (directory / 'bad.json').write_text(invalid)
            try: read_fragments(directory)
            except ValueError: pass
            else: raise AssertionError('invalid fragment accepted')
        (directory / 'bad.json').unlink()
        assert read_fragments(directory) == fragments



    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp) / 'repo'
        (root / 'tests').mkdir(parents=True)
        runner = 'tests/check.py'
        source = "import unittest\nclass T(unittest.TestCase):\n def test_it(self):\n  open('tests/data.txt').read()\nif __name__ == '__main__': unittest.main()\n"
        (root / runner).write_text(source)
        (root / 'tests/data.txt').write_text('fixture content\n')
        (root / 'tests/note.txt').write_text('reviewed note anchor\n')
        (root / 'tests/receipt.txt').write_text('....\n----------------------------------------------------------------------\nRan 4 tests in 0.001s\n\nOK\n')
        git = classifier['git']
        git(root, 'init', '-q'); git(root, 'add', '.')
        git(root, '-c', 'user.name=Control', '-c', 'user.email=control@example.invalid', 'commit', '-qm', 'fragment controls')
        repo = classifier['Repository'](root, 'HEAD')
        blob = lambda path: repo.tree[path][2]
        catalog = {'schema_version': 1, 'standalone': [], 'reads': [], 'generators': [], 'orphans': []}
        standalone = {'path': runner, 'input_revision': repo.ref, 'source_blob': blob(runner),
                      'command': ['python3', '-B', runner], 'kind': 'unittest',
                      'purpose': 'Check the named fixture.', 'input_scope': ['tests/data.txt'], 'other_reads': 'unresolved'}
        route = {'runner': 'validated:' + runner, 'input_revision': repo.ref,
                 'frames': [{'path': runner, 'blob': blob(runner), 'line': 4}],
                 'target': 'tests/data.txt', 'target_blob': blob('tests/data.txt'),
                 'operation': 'validated Python read of measured bytes'}
        role = {'path': 'tests/note.txt', 'blob': blob('tests/note.txt'), 'anchor': 'reviewed note anchor',
                'role': 'Historical record: Synthetic reviewed note.'}
        fixture = {'path': 'tests/receipt.txt', 'blob': blob('tests/receipt.txt'),
                   'consumers': [{'path': runner, 'blob': blob(runner), 'anchors': [' def test_it(self):']}],
                   'reason': 'Synthetic receipt is also a regression fixture.'}
        directory = Path(tmp) / 'fragments'; directory.mkdir()
        (directory / 'step.json').write_text(json.dumps({'schema_version': 1, 'routes': {'standalone': [standalone]},
            'catalog_extensions': {'reads': [route]}, 'roles': [role], 'fixtures': [fixture]}))
        original = classifier['read_fragments']
        try:
            classifier['read_fragments'] = lambda _: original(directory)
            model = classifier['inventory'](repo, catalog)
            rows = {r['path']: r for r in model['records']}
            assert rows['tests/data.txt']['class'] == 'keep'
            assert rows['tests/note.txt']['class'] == 'evidence'
            assert rows['tests/receipt.txt']['class'] is None
            assert 'reviewed_fixture_refusal' in rows['tests/receipt.txt']['secondary']
            conflicting = dict(standalone, source_blob='0' * 40)
            (directory / 'other.json').write_text(json.dumps({'schema_version': 1, 'routes': {'standalone': [conflicting]}}))
            try: classifier['inventory'](repo, catalog)
            except ValueError as error: assert 'conflicting' in str(error)
            else: raise AssertionError('end-to-end conflict accepted')
            (directory / 'other.json').unlink()
            home = Path(classifier['__file__']).parent
            legacy_role = json.loads((home / 'check-tests-used-roles.json').read_bytes())['records'][0]
            legacy_fixture = json.loads((home / 'check-tests-used-fixtures.json').read_bytes())['records'][0]
            spec = classifier['importlib'].util.spec_from_file_location('fragment_extension_control', home / 'check-tests-used-catalog-extension.py')
            extension = classifier['importlib'].util.module_from_spec(spec); spec.loader.exec_module(extension)
            legacy_extension = extension.load_catalog()['standalone'][-1]
            assert legacy_extension not in json.loads((home / 'check-tests-used-routes.json').read_bytes())['standalone']
            conflicts = [
                {'roles': [dict(legacy_role, role=legacy_role['role'] + ' changed')]},
                {'fixtures': [dict(legacy_fixture, reason=legacy_fixture['reason'] + ' changed')]},
                {'catalog_extensions': {'standalone': [dict(legacy_extension, source_blob='0' * 40)]}},
            ]
            for conflict in conflicts:
                (directory / 'step.json').write_text(json.dumps({'schema_version': 1, **conflict}))
                try: classifier['inventory'](repo, catalog)
                except ValueError as error: assert 'conflicting' in str(error)
                else: raise AssertionError('legacy catalog conflict accepted')
        finally:
            classifier['read_fragments'] = original


def consumer_route_controls(classifier):
    """Positive and negative controls for every opt-in consumer route."""
    inventory = classifier['inventory']
    original = classifier['read_fragments']
    unittest_source = ("import unittest\nOUT = 'tests/gen/result.json'\nclass T(unittest.TestCase):\n"
                       " def test_it(self):\n  open('tests/data.txt').read()\n  open('tests/other.txt').read()\n"
                       "if __name__ == '__main__': unittest.main()\n# tests/gen/result.json\nOUT2 = 'tests/gen2/result.json'\n")
    files = {
        'tests/run_test.py': unittest_source,
        'tests/data.txt': 'fixture\n', 'tests/other.txt': 'other\n', 'tests/unrelated.txt': 'one\n',
        'tests/n.test.mjs': ("import { helper } from './helper.mjs';\n// readFileSync(new URL('./fixture.json', import.meta.url))\nhelper();\n"
                             "/*\nimport { helper } from './helper.mjs';\n*/\nconst h = require('./helper.mjs');\n"
                             "const t = `\nimport './helper.mjs';\n`;\n"),
        'tests/helper.mjs': ("import { readFileSync } from 'node:fs';\nexport function helper() {\n  return readFileSync(new URL('./fixture.json', import.meta.url), 'utf8');\n}\n"
                             "const x = readFileSync(computed());\n"
                             "foo(); // readFileSync(new URL('./fixture.json', import.meta.url))\n"
                             "console.log(\"readFileSync('tests/fixture.json')\");\n/*\n readFileSync('tests/fixture.json');\n*/\n"
                             "const t = `\n readFileSync('tests/fixture.json');\n`;\nmock.readFileSync('tests/fixture.json');\n"
                             "const y = readFileSync('tests/fixture.json'); // reviewed trailing note\n"),
        'tests/fixture.json': '{}\n',
        'tests/R.lean': ('import tests.LeanHelper\n-- IO.FS.readFile "tests/lean-data.txt"\n#eval show IO Unit from do\n  let s ← IO.FS.readFile "tests/lean-data.txt"\n  IO.println s\n'
                         'def unused : IO String := IO.FS.readFile "tests/lean-data.txt"\n'),
        'tests/LeanHelper.lean': 'def root := "tests/"\ndef load : IO String := IO.FS.readFile\n  "tests/lean-helper.txt"\ndef bad : IO String := IO.FS.readFile (root ++ "x")\n',
        'tests/lean-data.txt': 'lean\n', 'tests/lean-helper.txt': 'helper\n',
        '.github/workflows/lean.yml': 'jobs:\n  t:\n    steps:\n      - run: lean tests/R.lean\n',
        'tests/cli.py': "import argparse\nparser = argparse.ArgumentParser()\nparser.add_argument('--input', required=True)\nparser.add_argument('--quiet', action='store_true')\nargs = parser.parse_args()\nprint(args.input)\n",
        'tests/gen/.gitignore': '# outputs\n*.json\n!keep.json\nkept.txt\n',
        'tests/gen/kept.txt': 'tracked\n',
        '.gitignore': 'tests/gen2/\n', 'tests/gen2/.gitignore': '*.json\n',
    }
    variants = {  # module CLI shapes that must stay outside the role
        'positional': "import argparse\nparser = argparse.ArgumentParser()\nparser.add_argument('input')\nparser.add_argument('--x', required=True)\nargs = parser.parse_args()\n",
        'optional': "import argparse\nparser = argparse.ArgumentParser()\nparser.add_argument('--x')\nargs = parser.parse_args()\n",
        'exit-first': "import argparse, sys\nsys.exit(0)\nparser = argparse.ArgumentParser()\nparser.add_argument('--x', required=True)\nargs = parser.parse_args()\n",
        'rebound': "import argparse\nparser = argparse.ArgumentParser()\nparser.add_argument('--x', required=True)\nargs = parser.parse_args()\nparser = None\n",
        'mutated': "import argparse\nparser = argparse.ArgumentParser()\nparser.set_defaults(x=1)\nparser.add_argument('--x', required=True)\nargs = parser.parse_args()\n",
        'argv': "import argparse, sys\nsys.argv[1:] = ['--x', 'y']\nparser = argparse.ArgumentParser()\nparser.add_argument('--x', required=True)\nargs = parser.parse_args()\n",
        'class-body': "import argparse, sys\nclass C:\n    sys.exit(0)\nparser = argparse.ArgumentParser()\nparser.add_argument('--x', required=True)\nargs = parser.parse_args()\n",
        'star': "from os import *\nimport argparse\nparser = argparse.ArgumentParser()\nparser.add_argument('--x', required=True)\nargs = parser.parse_args()\n",
    }
    for name, text in variants.items(): files['tests/cli-' + name + '.py'] = text
    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp) / 'repo'
        commit = _control_repository(classifier, root)
        first = commit(files, 'validated')
        blob = lambda repo, path: repo.tree[path][2]
        for name in variants: assert classifier['declared_module_cli'](first, 'tests/cli-' + name + '.py') is None, name
        declaration = classifier['declared_module_cli'](first, 'tests/cli.py')
        assert declaration['required_options'] == ['--input'] and declaration['main_line'] == 5
        A = first.ref
        catalog = {'schema_version': 1, 'reads': [], 'generators': [], 'orphans': [], 'standalone': [
            {'path': 'tests/run_test.py', 'input_revision': A, 'source_blob': blob(first, 'tests/run_test.py'),
             'command': ['python3', '-B', 'tests/run_test.py'], 'kind': 'unittest', 'purpose': 'Synthetic data check.',
             'input_scope': ['tests/data.txt'], 'other_reads': 'unresolved'},
            {'path': 'tests/n.test.mjs', 'input_revision': A, 'source_blob': blob(first, 'tests/n.test.mjs'),
             'command': ['node', '--test', 'tests/n.test.mjs'], 'kind': 'node-test'},
            {'path': 'tests/cli.py', 'input_revision': A, 'source_blob': blob(first, 'tests/cli.py'),
             'command': ['python3', '-B', 'tests/cli.py'], 'kind': 'committed-module-cli', 'purpose': 'Synthetic configured CLI.',
             'entry_line': 5, 'required_options': ['--input']}]}
        frame = lambda repo, path, line: {'path': path, 'blob': blob(repo, path), 'line': line}
        def read(repo, target, line=5):
            return {'runner': 'validated:tests/run_test.py', 'input_revision': A, 'frames': [frame(repo, 'tests/run_test.py', line)],
                    'target': target, 'target_blob': blob(repo, target), 'operation': 'validated Python read of measured bytes'}
        def node(repo, form, target, frames, purpose='Synthetic Node fixture.'):
            return {'runner': 'committed:tests/n.test.mjs', 'form': form, 'frames': frames, 'target': target,
                    'target_blob': blob(repo, target), 'purpose': purpose}
        later = commit({'tests/unrelated.txt': 'two\n'}, 'later')
        def lean(repo, frames, target):
            return {'runner': roots['lean'], 'form': 'lean-readFile', 'frames': frames, 'target': target,
                    'target_blob': blob(repo, target), 'purpose': 'Synthetic Lean fixture.'}
        roots = {}
        def run(repo, consumers):
            fragments = {key: [] for key in FRAGMENT_SECTIONS + ('roles', 'fixtures') + CONSUMER_SECTIONS}
            fragments.update(consumers)
            classifier['read_fragments'] = lambda _: fragments
            try: return inventory(repo, catalog)
            finally: classifier['read_fragments'] = original
        baseline = run(later, {})
        roots['lean'] = next(k for k, v in baseline['entry_points'].items() if v['path'] == 'tests/R.lean')
        writer = {'path': 'tests/run_test.py', 'blob': blob(first, 'tests/run_test.py'), 'line': 2, 'literal': 'result.json'}
        policy = {'path': 'tests/gen/.gitignore', 'blob': blob(first, 'tests/gen/.gitignore'), 'purpose': 'Synthetic output policy.',
                  'matches': [{'line': 2, 'output': 'result.json', 'writer': writer}]}
        good = {'persistent_reads': [read(first, 'tests/data.txt'), read(first, 'tests/other.txt', 6)],
                'static_routes': [node(first, 'node-import', 'tests/helper.mjs', [frame(first, 'tests/n.test.mjs', 1)]),
                                  node(first, 'node-readFileSync', 'tests/fixture.json',
                                       [frame(first, 'tests/n.test.mjs', 1), frame(first, 'tests/helper.mjs', 3)]),
                                  lean(first, [frame(first, 'tests/R.lean', 4)], 'tests/lean-data.txt')],
                'git_policies': [policy]}
        def rejected(repo, consumers, text):
            try: run(repo, consumers)
            except ValueError as error: assert text in str(error), (text, str(error))
            else: raise AssertionError('accepted: ' + text)
        assert canonical(run(later, {key: [] for key in CONSUMER_SECTIONS})) == canonical(baseline)
        before = {r['path']: r for r in baseline['records']}
        for path in ('tests/data.txt', 'tests/helper.mjs', 'tests/fixture.json', 'tests/lean-data.txt', 'tests/gen/.gitignore'):
            assert before[path]['class'] != 'keep', path
        assert 'committed-cli:tests/cli.py' in baseline['entry_points']
        assert baseline['entry_points']['committed-cli:tests/cli.py']['role_provenance']['kind'] == 'curated module-level argparse entry'
        model = run(later, good); rows = {r['path']: r for r in model['records']}
        for path in ('tests/data.txt', 'tests/helper.mjs', 'tests/fixture.json', 'tests/lean-data.txt', 'tests/gen/.gitignore'):
            assert rows[path]['class'] == 'keep', path
        assert rows['tests/data.txt']['runner_chain']['entry']['consumer_route']['validated_revision'] == A
        assert rows['tests/helper.mjs']['runner_chain']['edges'][-1]['kind'] == 'executes'
        # Out-of-scope persisted read stays an unreviewed read, never keep.
        assert rows['tests/other.txt']['class'] is None and 'unreviewed_readers' in rows['tests/other.txt']['secondary']
        assert model['entry_points']['git-policy:tests/gen/.gitignore']['source_only']
        assert rows['tests/lean-helper.txt']['class'] != 'keep'
        trailing = node(first, 'node-readFileSync', 'tests/fixture.json', [frame(first, 'tests/n.test.mjs', 1), frame(first, 'tests/helper.mjs', 15)])
        assert {r['path']: r for r in run(later, {'static_routes': [trailing]})['records']}['tests/fixture.json']['class'] == 'keep'
        # The same rows at the validated revision are ordinary reads/routes.
        assert {r['path']: r for r in run(first, good)['records']}['tests/data.txt']['class'] == 'keep'
        # Negative controls: malformed forms are rejected.
        bad_read = dict(read(first, 'tests/data.txt'), input_revision='0' * 40)
        rejected(later, {'persistent_reads': [bad_read]}, 'lacks its passing runner definition')
        rejected(later, {'persistent_reads': [dict(read(first, 'tests/data.txt'), operation='guessed')]}, 'unsupported persisted read operation')
        rejected(later, {'static_routes': [node(first, 'node-readFileSync', 'tests/fixture.json', [frame(first, 'tests/n.test.mjs', 2)])]}, 'literal node-readFileSync')
        rejected(later, {'static_routes': [node(first, 'node-readFileSync', 'tests/fixture.json',
                 [frame(first, 'tests/n.test.mjs', 1), frame(first, 'tests/helper.mjs', 5)])]}, 'literal node-readFileSync')
        rejected(later, {'static_routes': [node(first, 'node-import', 'tests/fixture.json', [frame(first, 'tests/n.test.mjs', 1)])]}, 'literal node-import')
        rejected(later, {'static_routes': [node(first, 'node-readFileSync', 'tests/fixture.json',
                 [frame(first, 'tests/n.test.mjs', 3), frame(first, 'tests/helper.mjs', 3)])]}, 'not a literal import')
        rejected(later, {'static_routes': [node(first, 'node-import', 'tests/helper.mjs', [frame(first, 'tests/n.test.mjs', 1)], purpose=' ')]}, 'invalid static')
        rejected(later, {'static_routes': [lean(first, [frame(first, 'tests/R.lean', 2)], 'tests/lean-data.txt')]}, 'literal lean-readFile')
        rejected(later, {'static_routes': [lean(first, [frame(first, 'tests/R.lean', 6)], 'tests/lean-data.txt')]}, 'literal lean-readFile')
        # An imported module's defs and #evals do not run when the runner runs.
        rejected(later, {'static_routes': [lean(first, [frame(first, 'tests/R.lean', 1), frame(first, 'tests/LeanHelper.lean', 2)], 'tests/lean-helper.txt')]}, 'elaborated runner file')
        # Comments, strings, templates, receivers and require in ESM never count.
        for line in (6, 7, 9, 12, 14):
            rejected(later, {'static_routes': [node(first, 'node-readFileSync', 'tests/fixture.json',
                     [frame(first, 'tests/n.test.mjs', 1), frame(first, 'tests/helper.mjs', line)])]}, 'literal node-readFileSync')
        for line in (5, 7, 9):
            rejected(later, {'static_routes': [node(first, 'node-import', 'tests/helper.mjs', [frame(first, 'tests/n.test.mjs', line)])]}, 'literal node-import')
        for line, text in ((1, 'invalid Git policy output or line'), (3, 'invalid Git policy output or line'), (4, 'does not ignore')):
            rejected(later, {'git_policies': [dict(policy, matches=[{'line': line, 'output': 'result.json', 'writer': writer}])]}, text)
        rejected(later, {'git_policies': [dict(policy, matches=[{'line': 4, 'output': 'kept.txt', 'writer': dict(writer, literal='kept.txt')}])]}, 'tracked')
        rejected(later, {'git_policies': [dict(policy, matches=[{'line': 2, 'output': 'result.json', 'writer': dict(writer, literal='other.json')}])]}, 'does not name')
        rejected(later, {'git_policies': [dict(policy, matches=[{'line': 2, 'output': '../x.json', 'writer': writer}])]}, 'invalid Git policy output')
        rejected(later, {'git_policies': [dict(policy, matches=[{'line': 2, 'output': '*.json', 'writer': dict(writer, literal='*.json')}])]}, 'invalid Git policy match')
        self_writer = {'path': 'tests/gen/.gitignore', 'blob': policy['blob'], 'line': 2, 'literal': 'result.json'}
        rejected(later, {'git_policies': [dict(policy, matches=[{'line': 2, 'output': 'result.json', 'writer': self_writer}])]}, 'not an entry point source')
        rejected(later, {'git_policies': [dict(policy, matches=[{'line': 2, 'output': 'result.json', 'writer': dict(writer, line=8)}])]}, 'does not name')
        rejected(later, {'git_policies': [dict(policy, matches=[{'line': 2, 'output': 'result.json', 'writer': dict(writer, path=['x'])}])]}, 'invalid Git policy match')
        # git never reads a .gitignore inside an ignored directory.
        rejected(later, {'git_policies': [{'path': 'tests/gen2/.gitignore', 'blob': blob(first, 'tests/gen2/.gitignore'), 'purpose': 'Ignored.',
                 'matches': [{'line': 1, 'output': 'result.json', 'writer': dict(writer, line=9)}]}]}, 'does not ignore')
        rejected(later, {'static_routes': good['static_routes'] + [dict(good['static_routes'][0], purpose='changed')]}, 'conflicting')
        # Unreviewed or undemonstrated anchors grant nothing.
        unanchored = dict(good['static_routes'][0], runner='committed:tests/missing.mjs')
        assert {r['path']: r for r in run(later, {'static_routes': [unanchored]})['records']}['tests/helper.mjs']['class'] != 'keep'
        # A source-only CLI role anchors nothing.
        cli_anchor = dict(good['static_routes'][0], runner='committed-cli:tests/cli.py', frames=[frame(first, 'tests/cli.py', 1)])
        assert {r['path']: r for r in run(later, {'static_routes': [cli_anchor]})['records']}['tests/helper.mjs']['class'] != 'keep'
        # Stale objects (blob-bound) grant nothing at a later revision.
        changed = commit({'tests/data.txt': 'changed\n', 'tests/fixture.json': '[]\n', 'tests/lean-data.txt': 'changed\n',
                          'tests/run_test.py': unittest_source + '# changed\n'}, 'changed inputs')
        stale = {r['path']: r for r in run(changed, good)['records']}
        for path in ('tests/data.txt', 'tests/fixture.json', 'tests/lean-data.txt', 'tests/gen/.gitignore'):
            assert stale[path]['class'] != 'keep', path
        assert stale['tests/helper.mjs']['class'] == 'keep'
        # A fabricated declaration of current objects never observed at A is refused.
        forged = read(changed, 'tests/data.txt')
        forged['frames'] = [frame(first, 'tests/run_test.py', 5)]
        reverted = commit({'tests/run_test.py': unittest_source}, 'revert runner')
        rejected(reverted, {'persistent_reads': [forged]}, 'objects differ at recorded revision')
        # A helper rewritten after the demonstration is not credited from it.
        helper = files['tests/helper.mjs'].replace("'./fixture.json', import.meta.url), 'utf8')", "'./fixture2.json', import.meta.url), 'utf8')")
        rewritten = commit({'tests/helper.mjs': helper, 'tests/fixture2.json': '{}\n', 'tests/gen/.gitignore': '# outputs changed\n*.json\n'}, 'rewrite helper')
        late = node(rewritten, 'node-readFileSync', 'tests/fixture2.json',
                    [frame(rewritten, 'tests/n.test.mjs', 1), frame(rewritten, 'tests/helper.mjs', 3)])
        rows = {r['path']: r for r in run(rewritten, {'static_routes': [late], 'git_policies': [policy]})['records']}
        assert rows['tests/fixture2.json']['class'] != 'keep'
        # A changed .gitignore blob is stale: the policy role is gone.
        assert rows['tests/gen/.gitignore']['class'] != 'keep'
    successor_controls(classifier)


def successor_controls(classifier):
    """x1g positive and negative controls: library Lean reads, Node walker
    reads, source-only programs and persisted module entries."""
    inventory = classifier['inventory']
    original = classifier['read_fragments']; sys = classifier['sys']
    helper = Path(classifier['__file__']).with_name('check-tests-used-trace.py')
    spec = classifier['importlib'].util.spec_from_file_location('successor_control_observer', helper)
    observer = classifier['importlib'].util.module_from_spec(spec); spec.loader.exec_module(observer)
    walk = ('import { readFileSync, readdirSync, statSync } from "node:fs";\nimport { resolve, dirname, join } from "node:path";\n'
            'import { fileURLToPath } from "node:url";\n\nconst root = resolve(dirname(fileURLToPath(import.meta.url)), "..");\n'
            'const cache = resolve(root, "tests/corpus/skip");\nconst mode = process.argv[2];\n\n'
            'function walk(dir, out = []) {\n  for (const f of readdirSync(dir)) {\n    const p = join(dir, f);\n'
            '    if (statSync(p).isDirectory()) walk(p, out);\n    else if (p.endsWith(".sol")) out.push(p);\n  }\n  return out;\n}\n\n'
            'if (mode === "prepare") {\n  for (const p of walk(resolve(root, "tests/corpus")).sort()) {\n    if (p.startsWith(cache)) continue;\n'
            '    const rel = p;\n    console.log(rel,\n      readFileSync(p, "latin1")); // POSITIVE\n  }\n'
            '  // readFileSync(p, "latin1"); COMMENT\n  for (const p of walk(resolve(root, "tests/corpus")).sort()) {\n'
            '    if (p.length > 3) {\n      readFileSync(p, "latin1"); // NESTED\n    }\n    if (p.endsWith("x.sol")) break;\n'
            '    readFileSync(p); // AFTER-BREAK\n    const s = p.length > 3 ?\n      readFileSync(p) : ""; // CONDITIONAL\n  }\n'
            '} else if (mode === "other") {\n  for (const p of walk(resolve(root, "tests/corpus"))) {\n    readFileSync(p); // OTHER-MODE\n  }\n}\n')
    head = walk[:walk.index('if (mode === "prepare") {')]
    loop = '  for (const p of walk(resolve(root, "tests/corpus"))) {\n'
    adversarial = {  # each body places a read marked READ that must not be credited
        'else-if': 'if (mode === "prepare") {\n} else if (mode === "prepare") {\n' + loop + '    readFileSync(p); // READ\n  }\n}\n',
        'braceless-if': 'if (mode === "prepare") {\n' + loop + '    if (false)\n      readFileSync(p); // READ\n  }\n}\n',
        'arrow': 'if (mode === "prepare") {\n' + loop + '    const f = () =>\n      readFileSync(p); // READ\n  }\n}\n',
        'braceless-loop': 'if (mode === "prepare") {\n  if (false)\n' + loop + '    readFileSync(p); // READ\n  }\n}\n',
        'regex-brace': 'if (mode === "other") {\n  "x".replace(/}/, "");\n' + loop + '    readFileSync(p); // READ\n  }\n}\n',
        'regex-backtick': 'if (mode === "other") {\n  "x".replace(/`/, "");\n' + loop + '    readFileSync(p); // READ\n  }\n  "y".replace(/`/, "");\n}\n',
        'destructured': 'if (mode === "prepare") {\n  const { readFileSync } = { readFileSync: () => "" };\n' + loop + '    readFileSync(p); // READ\n  }\n}\n',
        'function': 'function never() {\n' + loop + '    readFileSync(p); // READ\n  }\n}\n',
        'conditional': 'if (mode === "prepare") {\n' + loop + '    const s = p.length > 3 ?\n      readFileSync(p) : ""; // READ\n  }\n}\n',
        'form-feed': 'if (mode === "prepare") {\n' + loop + '    readFileSync(p); // READ\n  }\n}\f\n',
    }
    plain = 'if (mode === "prepare") {\n' + loop + '    readFileSync(p); // READ\n  }\n}\n'
    files = {
        **{'tests/adv-' + name + '.mjs': head + body for name, body in adversarial.items()}, 'tests/adv-plain.mjs': head + plain,
        'lakefile.toml': 'defaultTargets = ["Lib"]\n[[lean_lib]]\nname = "Lib"\n[[lean_lib]]\nname = "Extra"\n[[lean_lib]]\nname = "Src"\nsrcDir = "src"\n',
        'Lib.lean': '/-! library root -/\nimport Lib.Mod Lib.Late\n-- import Lib.Mod\n', 'Extra.lean': 'import Lib.Mod\n',
        'src/Src.lean': 'import Lib.Mod\n', 'Lib/Late.lean': 'import Lean\n#exit\n#eval IO.FS.readFile "tests/lib-eval.txt"\n',
        'Lib/Mod.lean': ('import Lean\nopen Lean\n-- IO.FS.readFile "tests/lib-data.txt"\nrun_elab do\n  let s ← IO.FS.readFile\n    "tests/lib-data.txt"\n'
                         '  logInfo s\ndef unused : IO String := IO.FS.readFile "tests/lib-data.txt"\n#eval IO.FS.readFile "tests/lib-eval.txt"\n'),
        'tests/lib-data.txt': 'lib\n', 'tests/lib-eval.txt': 'eval\n',
        'tests/R.lean': 'import Lib.Mod\n#eval IO.FS.readFile "tests/lib-eval.txt"\n',
        '.github/workflows/lean.yml': 'jobs:\n  t:\n    steps:\n      - run: lean tests/R.lean\n',
        'tests/walk.mjs': walk, 'tests/walk-bad.mjs': walk.replace('    if (statSync(p).isDirectory()) walk(p, out);\n', '    if (statSync(p).isDirectory()) return out;\n'),
        'tests/walk.test.mjs': walk,
        'tests/mode.mjs': '//   node tests/mode.mjs prepare   synthetic step\n// node tests/mode.mjs other\n' + walk,
        'tests/mode-flat.mjs': '// node tests/mode-flat.mjs prepare\n' + walk.replace('if (mode === "prepare") {', 'if (true) {'),
        'tests/corpus/a.sol': 'contract A {}\n', 'tests/corpus/sub/b.sol': 'contract B {}\n', 'tests/corpus/c.txt': 'c\n',
        'tests/corpus/skip/d.sol': 'contract D {}\n', 'tests/data.txt': 'data\n',
        'tests/README.md': 'Run `node tests/walk.mjs prepare`.\nRun `node tests/walk-bad.mjs prepare`.\nRun `node tests/walk.mjs other`.\n',
        'tests/prog.py': 'import json\ndef main():\n    print(json.dumps(1))\nmain()\n',
        'tests/prog_test.py': 'import unittest\nclass T(unittest.TestCase):\n def test_it(self): pass\nif __name__ == "__main__": unittest.main()\n',
        'tests/prog_cli.py': "import argparse\nparser = argparse.ArgumentParser()\nparser.add_argument('--input', required=True)\nargs = parser.parse_args()\nprint(args.input)\n",
        'tests/helper.py': 'VALUE = 3\n',
        'tests/args.py': 'import sys\nlabel, *command = sys.argv[1:]\nif not command:\n    raise SystemExit("usage: args.py LABEL COMMAND")\nprint(label, command)\n',
        'tests/args_sub.py': ("import argparse\ndef main():\n    parser = argparse.ArgumentParser()\n    sub = parser.add_subparsers(dest='mode', required=True)\n"
                              "    pick = sub.add_parser('pick')\n    pick.add_argument('results')\n    pick.add_argument('--out', required=True)\n"
                              "    return parser.parse_args()\nif __name__ == '__main__':\n    main()\n"),
        'tests/args_alias.py': 'from sys import argv\nprint(argv[1])\n',
        'tests/args_rebind.py': 'import sys\nsys.argv = ["x", "y"]\nprint(sys.argv[1])\n',
        'tests/gen/.gitignore': 'out.json\n',
        'tests/drive.sh': '#!/usr/bin/env bash\nset -euo pipefail\npython3 tests/helper.py "$@" > tests/gen/out.json\n',
        'tests/drive-sh.sh': '#!/bin/sh\necho drive\n',
        'tests/lib.sh': '#!/usr/bin/env bash\nhelper() {\n  echo helper\n}\nreturn 0\n',
        'tests/drive.mjs': "import { readFileSync } from 'node:fs';\nconst [input] = process.argv.slice(2);\nconsole.log(readFileSync(input, 'utf8'));\n",
        'tests/drive.cjs': "#!/usr/bin/env node\n// drive\nconst fs = require('node:fs');\nconsole.log(fs.readFileSync('tests/helper.py', 'utf8'));\n",
        'tests/drive.test.mjs': "import { readFileSync } from 'node:fs';\nconsole.log(readFileSync('tests/helper.py', 'utf8'));\n",
        'tests/drive.js': "console.log('drive');\n",
        'tests/lib.mjs': 'export const value = 1;\n',
        'tests/lib.cjs': 'module.exports = { value: 1 };\n',
        'tests/test_entry.py': 'import unittest\nclass T(unittest.TestCase):\n def test_import(self):\n  import helper\n  self.assertEqual(helper.VALUE, 3)\nif __name__ == "__main__": unittest.main()\n',
    }
    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp) / 'repo'
        commit = _control_repository(classifier, root)
        first = commit(files, 'validated'); A = first.ref
        blob = lambda repo, path: repo.tree[path][2]
        frame = lambda repo, path, line: {'path': path, 'blob': blob(repo, path), 'line': line}
        line_of = lambda path, marker: next(n for n, l in enumerate(files[path].splitlines(), 1) if marker in l)
        doc = lambda n, invocation: {'path': 'tests/README.md', 'blob': blob(first, 'tests/README.md'), 'line': n,
                                     'invocation': invocation, 'normalization': 'verbatim'}
        manual = lambda path, mode, n, repo=first: {'path': path, 'input_revision': repo.ref, 'source_blob': blob(repo, path), 'kind': 'manual-reproducer',
                                                    'command': ['node', path, mode], 'documentation': doc(n, 'node ' + path + ' ' + mode)}
        program = {'path': 'tests/prog.py', 'input_revision': A, 'source_blob': blob(first, 'tests/prog.py'),
                   'command': ['python3', '-B', 'tests/prog.py'], 'kind': SOURCE_ONLY_KIND, 'entry_line': 4,
                   'purpose': 'Synthetic default program whose run is not certified.'}
        catalog = {'schema_version': 3, 'reads': [], 'generators': [], 'orphans': [], 'module_entries': [], 'standalone': [
            manual('tests/walk.mjs', 'prepare', 1), manual('tests/walk-bad.mjs', 'prepare', 2),
            {'path': 'tests/walk.test.mjs', 'input_revision': A, 'source_blob': blob(first, 'tests/walk.test.mjs'),
             'command': ['node', '--test', 'tests/walk.test.mjs'], 'kind': 'node-test'},
            {'path': 'tests/test_entry.py', 'input_revision': A, 'source_blob': blob(first, 'tests/test_entry.py'),
             'command': ['python3', '-B', 'tests/test_entry.py'], 'kind': 'unittest'}]}
        claim = {'runner': 'validated:tests/test_entry.py', 'input_revision': A, 'frames': [frame(first, 'tests/test_entry.py', 4)],
                 'target': 'tests/helper.py', 'target_blob': blob(first, 'tests/helper.py'), 'operation': MODULE_ENTRY_OPERATION,
                 'module_code_sha256': observer.code_fingerprint(compile(files['tests/helper.py'], '<measured>', 'exec', dont_inherit=True)),
                 'module_frame_line': 0, 'python': list(sys.version_info[:3]), 'collector_sha256': hashlib.sha256(helper.read_bytes()).hexdigest()}
        def run(repo, consumers=None, standalone=(), entries=None):
            fragments = {key: [] for key in FRAGMENT_SECTIONS + ('roles', 'fixtures') + CONSUMER_SECTIONS}
            fragments.update(consumers or {})
            classifier['read_fragments'] = lambda _: fragments
            local = dict(catalog, standalone=catalog['standalone'] + list(standalone),
                         module_entries=[claim] if entries is None else entries)
            try: model = inventory(repo, local)
            finally: classifier['read_fragments'] = original
            return model, {r['path']: r for r in model['records']}
        def rejected(repo, text, consumers=None, standalone=(), entries=None):
            try: run(repo, consumers, standalone, entries)
            except ValueError as error: assert text in str(error), (text, str(error))
            else: raise AssertionError('accepted: ' + text)
        def route(repo, runner, form, frames, target):
            return {'runner': runner, 'form': form, 'frames': frames, 'target': target,
                    'target_blob': blob(repo, target), 'purpose': 'Synthetic successor route.'}
        later = commit({'tests/unrelated.txt': 'later\n'}, 'later')
        baseline_model, baseline = run(later, entries=[])
        # Fragments of the earlier shape (no persistent_module_entries key) give the same model.
        classifier['read_fragments'] = lambda _: {key: [] for key in FRAGMENT_SECTIONS + ('roles', 'fixtures') + CONSUMER_SECTIONS[:3]}
        try: assert canonical(inventory(later, dict(catalog, module_entries=[]))) == canonical(baseline_model)
        finally: classifier['read_fragments'] = original
        for path in ('tests/lib-data.txt', 'tests/corpus/a.sol', 'tests/corpus/sub/b.sol', 'tests/prog.py', 'tests/helper.py'):
            assert baseline[path]['class'] != 'keep', path
        assert 'Lib.lean' in baseline_model['entry_points'] and baseline_model['entry_points']['Lib.lean']['kind'] == 'Lean root'

        # (1) H978 Lean library run_elab read through header imports.
        lib = lambda frames, target='tests/lib-data.txt', runner='Lib.lean': route(first, runner, 'lean-library-readFile', frames, target)
        good_lib = lib([frame(first, 'Lib.lean', 2), frame(first, 'Lib/Mod.lean', 5)])
        _, rows = run(later, {'static_routes': [good_lib]})
        assert rows['tests/lib-data.txt']['class'] == 'keep'
        assert rows['tests/lib-data.txt']['runner_chain']['edges'][0]['operation'] == 'Lean header import elaborated by the library build'
        _, rows = run(later, {'static_routes': [lib([frame(first, 'Lib.lean', 2), frame(first, 'Lib/Mod.lean', 9)], 'tests/lib-eval.txt')]})
        assert rows['tests/lib-eval.txt']['class'] == 'keep'
        rejected(later, 'not a Lean header import', {'static_routes': [lib([frame(first, 'Lib.lean', 3), frame(first, 'Lib/Mod.lean', 5)])]})
        rejected(later, 'not a Lean header import', {'static_routes': [lib([frame(first, 'Lib.lean', 1), frame(first, 'Lib/Mod.lean', 5)])]})
        for n in (3, 6, 8):  # comment, literal line, def body
            rejected(later, 'literal lean-library-readFile', {'static_routes': [lib([frame(first, 'Lib.lean', 2), frame(first, 'Lib/Mod.lean', n)])]})
        rejected(later, 'repository Lean library root', {'static_routes': [lib([frame(first, 'tests/R.lean', 1), frame(first, 'Lib/Mod.lean', 5)], runner='tests/R.lean')]})
        # Only a default lean_lib with root-relative sources is built by the default build.
        rejected(later, 'repository Lean library root', {'static_routes': [lib([frame(first, 'Extra.lean', 1), frame(first, 'Lib/Mod.lean', 5)], runner='Extra.lean')]})
        rejected(later, 'repository Lean library root', {'static_routes': [lib([frame(first, 'src/Src.lean', 1), frame(first, 'Lib/Mod.lean', 5)], runner='src/Src.lean')]})
        rejected(later, 'follows #exit', {'static_routes': [lib([frame(first, 'Lib.lean', 2), frame(first, 'Lib/Late.lean', 3)], 'tests/lib-eval.txt')]})
        # The single-file form still refuses an imported module.
        rejected(later, 'elaborated runner file', {'static_routes': [route(first, 'tests/R.lean', 'lean-readFile',
                 [frame(first, 'tests/R.lean', 1), frame(first, 'Lib/Mod.lean', 9)], 'tests/lib-eval.txt')]})

        # (2) H978 Node readFileSync over a computed recursive walker; the
        # manual reproducers are current roots only at their own revision.
        node = lambda target, marker, path='tests/walk.mjs', runner='validated:tests/walk.mjs': route(
            first, runner, 'node-readFileSync-walk', [frame(first, path, line_of(path, marker))], target)
        _, rows = run(first, {'static_routes': [node('tests/corpus/a.sol', 'POSITIVE'), node('tests/corpus/sub/b.sol', 'POSITIVE')]})
        assert rows['tests/corpus/a.sol']['class'] == 'keep' and rows['tests/corpus/sub/b.sol']['class'] == 'keep'
        assert rows['tests/corpus/skip/d.sol']['class'] != 'keep'
        for target, marker in (('tests/corpus/c.txt', 'POSITIVE'), ('tests/corpus/skip/d.sol', 'POSITIVE'), ('tests/data.txt', 'POSITIVE'),
                               ('tests/corpus/a.sol', 'COMMENT'), ('tests/corpus/a.sol', 'NESTED'), ('tests/corpus/a.sol', 'AFTER-BREAK'),
                               ('tests/corpus/a.sol', 'CONDITIONAL'), ('tests/corpus/a.sol', 'OTHER-MODE')):
            rejected(first, 'literal node-readFileSync-walk', {'static_routes': [node(target, marker)]})
        rejected(first, 'literal node-readFileSync-walk', {'static_routes': [node('tests/corpus/a.sol', 'POSITIVE', 'tests/walk-bad.mjs', 'validated:tests/walk-bad.mjs')]})
        # A Node test root passes no prepare mode argument.
        rejected(first, 'literal node-readFileSync-walk', {'static_routes': [node('tests/corpus/a.sol', 'POSITIVE', 'tests/walk.test.mjs', 'validated:tests/walk.test.mjs')]})
        for name in ['plain'] + list(adversarial):
            path = 'tests/adv-' + name + '.mjs'
            got = _node_walk_read(path, first, line_of(path, '// READ'), 'tests/corpus/a.sol', {'command': 'node ' + path + ' prepare'}, path)
            assert got == ('tests/corpus/a.sol' if name == 'plain' else None), name
        moved = commit({'tests/corpus/a.sol': 'contract A2 {}\n'}, 'changed corpus')
        _, rows = run(moved, {'static_routes': [node('tests/corpus/a.sol', 'POSITIVE'), node('tests/corpus/sub/b.sol', 'POSITIVE')]},
                      standalone=[manual('tests/walk.mjs', 'prepare', 1, moved)])
        assert rows['tests/corpus/a.sol']['class'] != 'keep' and rows['tests/corpus/sub/b.sol']['class'] == 'keep'

        # (3) H978 source-only no-pass programs: never a validated runner.
        model, rows = run(first, standalone=[program])
        assert rows['tests/prog.py']['class'] == 'keep'
        entry = model['entry_points']['source-only:tests/prog.py']
        assert entry['source_only'] and entry['validation_at_measured_revision']['status'] == 'unavailable'
        assert not any(k.endswith(':tests/prog.py') and not k.startswith('source-only:') for k in model['entry_points'])
        model, rows = run(later, standalone=[program])
        assert rows['tests/prog.py']['class'] == 'keep' and 'source-only:tests/prog.py' in model['entry_points']
        # A source-only program anchors no route: the malformed row is never even inspected.
        _, rows = run(later, {'static_routes': [route(first, 'source-only:tests/prog.py', 'node-import', [frame(first, 'tests/prog.py', 1)], 'tests/corpus/c.txt')]},
                      standalone=[program])
        assert rows['tests/corpus/c.txt']['class'] != 'keep'
        rejected(later, 'unverifiable historical runner demonstration', standalone=[dict(program, input_revision='0' * 40)])
        for change, text in (({'entry_line': 2}, 'default top-level entry'), ({'command': ['node', 'tests/prog.py']}, 'unsupported source-only'),
                             ({'purpose': ' '}, 'invalid source-only'), ({'input_revision': 'HEAD'}, 'full commit revision'),
                             ({'source_blob': '0' * 40}, 'source mismatch')):
            rejected(first, text, standalone=[dict(program, **change)])
        rejected(first, 'invalid source-only', standalone=[dict(program, input_scope=[])])
        for path, line in (('tests/prog_test.py', 4), ('tests/prog_cli.py', 5)):
            rejected(first, 'matches a configured CLI or unittest form', standalone=[dict(program, path=path, source_blob=blob(first, path),
                     command=['python3', '-B', path], entry_line=line)])
        rejected(first, 'conflicting standalone', standalone=[program, dict(program, kind='runnable-entrypoint', input_scope=[], other_reads='unresolved')])
        rewritten = commit({'tests/prog.py': files['tests/prog.py'] + '# changed\n'}, 'changed program')
        model, rows = run(rewritten, standalone=[program])
        assert 'source-only:tests/prog.py' not in model['entry_points'] and rows['tests/prog.py']['class'] != 'keep'

        # (5) H992 reviewed argument-bearing Node mode root: anchors the walker
        # form only, as a source-only role with no passing-runner credit.
        global REVIEWED_NODE_MODES
        reviewed = REVIEWED_NODE_MODES
        assert ('scripts/parse-corpus.mjs', 'dd1093f6fe8bfe00ae772e0b8b4a0bc0dd4b265a', 'prepare', 17) in reviewed and len(reviewed) == 1
        mode_root = {'path': 'tests/mode.mjs', 'input_revision': A, 'source_blob': blob(first, 'tests/mode.mjs'), 'kind': NODE_MODE_KIND,
                     'command': ['node', 'tests/mode.mjs', 'prepare'], 'purpose': 'Synthetic reviewed prepare step.',
                     'provenance': {'path': 'tests/mode.mjs', 'blob': blob(first, 'tests/mode.mjs'), 'line': 1, 'invocation': 'node tests/mode.mjs prepare'}}
        walked = lambda target, marker='POSITIVE', form='node-readFileSync-walk', runner='node-mode:tests/mode.mjs': route(
            first, runner, form, [frame(first, 'tests/mode.mjs', line_of('tests/mode.mjs', marker))], target)
        walks = {'static_routes': [walked('tests/corpus/a.sol'), walked('tests/corpus/sub/b.sol')]}
        REVIEWED_NODE_MODES = frozenset({('tests/mode.mjs', blob(first, 'tests/mode.mjs'), 'prepare', 1),
                                         ('tests/mode.mjs', blob(first, 'tests/mode.mjs'), 'other', 2),
                                         ('tests/mode.mjs', blob(first, 'tests/mode.mjs'), 'prepare', 3),
                                         ('tests/mode-flat.mjs', blob(first, 'tests/mode-flat.mjs'), 'prepare', 1)})
        try:
            assert run(first, walks)[1]['tests/corpus/a.sol']['class'] != 'keep'  # no root, no anchor
            for repo in (first, later):
                model, rows = run(repo, walks, standalone=[mode_root])
                assert rows['tests/corpus/a.sol']['class'] == 'keep' and rows['tests/corpus/sub/b.sol']['class'] == 'keep'
                assert rows['tests/corpus/skip/d.sol']['class'] != 'keep' and rows['tests/corpus/c.txt']['class'] != 'keep'
                entry = model['entry_points']['node-mode:tests/mode.mjs']
                assert entry['source_only'] and entry['validation_at_measured_revision']['status'] == 'unavailable'
                assert entry['command'] == 'node tests/mode.mjs prepare' and entry['location'] == 'tests/mode.mjs:' + str(line_of('tests/mode.mjs', 'if (mode'))
                assert not any(k.endswith(':tests/mode.mjs') and not k.startswith('node-mode:') for k in model['entry_points'])
                assert rows['tests/corpus/a.sol']['runner_chain']['entry']['derived_from'] == 'node-mode:tests/mode.mjs'
            # Without new rows the root adds nothing to the reads.
            assert canonical(run(later, standalone=[mode_root])[1]['tests/corpus/a.sol']) == canonical(baseline['tests/corpus/a.sol'])
            # The root anchors no other form, mode or reader line.
            _, rows = run(first, {'static_routes': [walked('tests/corpus/c.txt', 'POSITIVE', 'node-readFileSync')]}, standalone=[mode_root])
            assert rows['tests/corpus/c.txt']['class'] != 'keep'
            for target, marker in (('tests/corpus/a.sol', 'OTHER-MODE'), ('tests/corpus/skip/d.sol', 'POSITIVE'), ('tests/corpus/a.sol', 'COMMENT')):
                rejected(first, 'literal node-readFileSync-walk', {'static_routes': [walked(target, marker)]}, standalone=[mode_root])
            other = dict(mode_root, command=['node', 'tests/mode.mjs', 'other'], provenance=dict(mode_root['provenance'], line=2, invocation='node tests/mode.mjs other'))
            rejected(first, 'argv mode branch', walks, standalone=[other])  # an else-if mode is not a top-level branch
            # Negative controls on the binding: schema, revision, command, provenance, review set, source, branch.
            for change, text in (({'extra': 1}, 'invalid Node mode root'), ({'purpose': ' '}, 'invalid Node mode root'),
                                 ({'input_revision': 'HEAD'}, 'full commit revision'),
                                 ({'command': ['node', 'tests/mode.mjs']}, 'unsupported Node mode root'),
                                 ({'command': ['node', 'tests/mode.mjs', 'prepare', '--x']}, 'unsupported Node mode root'),
                                 ({'command': ['node', 'tests/mode.mjs', '--prepare']}, 'unsupported Node mode root'),
                                 ({'command': ['node', '--test', 'tests/mode.mjs']}, 'unsupported Node mode root'),
                                 ({'command': ['node', 'tests/mode.mjs', 'report']}, 'unreviewed Node mode root'),
                                 ({'source_blob': '0' * 40}, 'unreviewed Node mode root'),
                                 ({'provenance': dict(mode_root['provenance'], line=2)}, 'unreviewed Node mode root'),
                                 ({'provenance': dict(mode_root['provenance'], line=3)}, 'verbatim source provenance'),
                                 ({'provenance': dict(mode_root['provenance'], invocation='node tests/mode.mjs  prepare')}, 'unreviewed Node mode root'),
                                 ({'provenance': dict(mode_root['provenance'], path='tests/README.md')}, 'unreviewed Node mode root'),
                                 ({'provenance': {'path': 'tests/mode.mjs'}}, 'invalid Node mode root')):
                rejected(first, text, walks, standalone=[dict(mode_root, **change)])
            rejected(first, 'unverifiable historical runner demonstration', walks, standalone=[dict(mode_root, input_revision='0' * 40)])
            rejected(first, 'conflicting standalone', walks, standalone=[mode_root, manual('tests/walk.mjs', 'prepare', 1) | {'path': 'tests/mode.mjs'}])
            flat = {'path': 'tests/mode-flat.mjs', 'input_revision': A, 'source_blob': blob(first, 'tests/mode-flat.mjs'), 'kind': NODE_MODE_KIND,
                    'command': ['node', 'tests/mode-flat.mjs', 'prepare'], 'purpose': 'No mode branch.',
                    'provenance': {'path': 'tests/mode-flat.mjs', 'blob': blob(first, 'tests/mode-flat.mjs'), 'line': 1, 'invocation': 'node tests/mode-flat.mjs prepare'}}
            rejected(first, 'argv mode branch', standalone=[flat])
            REVIEWED_NODE_MODES = frozenset()
            rejected(first, 'unreviewed Node mode root', walks, standalone=[mode_root])
        finally: REVIEWED_NODE_MODES = reviewed
        # A changed source drops the root and its reads.
        edited = commit({'tests/mode.mjs': files['tests/mode.mjs'] + '// changed\n'}, 'changed mode root')
        REVIEWED_NODE_MODES = reviewed | {('tests/mode.mjs', blob(first, 'tests/mode.mjs'), 'prepare', 1)}
        try:
            model, rows = run(edited, walks, standalone=[mode_root])
            assert 'node-mode:tests/mode.mjs' not in model['entry_points'] and rows['tests/corpus/a.sol']['class'] != 'keep'
        finally: REVIEWED_NODE_MODES = reviewed

        # (6) H996 reviewed argument-bearing Python source role: a source-only
        # root bound to blob, recorded interface and introducing commit that
        # anchors nothing and credits no read, argument, helper or output.
        global REVIEWED_PYTHON_ARGS
        reviewed_args = REVIEWED_PYTHON_ARGS
        assert len(reviewed_args) == 23 and all(p.startswith(('tests/directruntime-20261104/', 'tests/upstream/')) and p.endswith('.py')
                                                for p, _, _ in reviewed_args)
        assert ('tests/upstream/baseline-20261028/invocations/retries/selector.py', '5b7a49f863f7c6fad8231d17d68628623948a00e',
                '2207c1bba286538fd63e4a0ff4960ed4a593a8ab') in reviewed_args
        nb = 'tests/directruntime-20261104/native-browser/'  # H1006
        assert (nb + 'prepare-image-cache.py', 'c9695f1c0bf66b40be1f138f3da7e1ebc147ffde', 'ca73d1a4e1aecbcbc566acaa1aa7392cad472b3d') in reviewed_args
        assert not {p for p, _, _ in reviewed_args} & {nb + p for p in ('h109/input-inventory.py', 'h109/source-snapshot.py',
                                                                      'hardening-native-audit.py', 'readbounds/serial-build.py')}
        args_interface = {'argv_lines': [2], 'argv_tail_lines': [2], 'positionals': [], 'subcommands': []}
        assert python_argument_interface(files['tests/args.py']) == args_interface
        assert python_argument_interface(files['tests/args_sub.py']) == {'argv_lines': [], 'argv_tail_lines': [], 'positionals': [[6, 'results']], 'subcommands': [[5, 'pick']]}
        for path in ('tests/prog.py', 'tests/helper.py', 'tests/args_alias.py', 'tests/args_rebind.py'):
            assert python_argument_interface(files[path]) is None, path
        assert python_argument_interface('import sys as s\nprint(s.argv[1:])\n') == {'argv_lines': [2], 'argv_tail_lines': [2], 'positionals': [], 'subcommands': []}
        assert python_argument_interface('import sys\nclass O: argv = 1\nprint(O().argv)\n') is None
        assert python_argument_interface('import argparse\np = argparse.ArgumentParser()\ns = p.add_subparsers()\ns.add_parser(NAME)\n') is None
        for unaudited in ('import sys\nsys.argv[1:] = []\n', 'import sys\nsys.argv[1] = "x"\n', 'import sys\ndel sys.argv[1:]\n',
                          'import sys\nsys.argv.append("x")\n', 'import sys\ndef f(sys): return sys.argv[1]\n',
                          'import sys\ntry: pass\nexcept OSError as sys: pass\nprint(sys.argv[1])\n',
                          'import sys\nfrom os import path as sys\nprint(sys.argv[1])\n', 'import sys\nprint(getattr(sys, "argv"), sys.argv[1])\n',
                          'import argparse\np = argparse.ArgumentParser()\np.add_argument(NAME)\n',
                          'import argparse\np = argparse.ArgumentParser()\np.add_argument("x")\np.parse_args(["y"])\n'):
            assert python_argument_interface(unaudited) is None, unaudited
        py_role = lambda path, line, interface, repo=first, commit=A: {
            'path': path, 'input_revision': repo.ref, 'source_blob': blob(repo, path), 'kind': PYTHON_ARGS_KIND,
            'command': ['python3', '-B', path], 'entry_line': line, 'interface': interface,
            'provenance': {'commit': commit, 'path': path, 'blob': blob(repo, path)}, 'purpose': 'Synthetic reviewed argument-bearing program.'}
        args_role = py_role('tests/args.py', 3, args_interface)
        sub_role = py_role('tests/args_sub.py', 9, python_argument_interface(files['tests/args_sub.py']))
        assert baseline['tests/args.py']['class'] != 'keep' and baseline['tests/args_sub.py']['class'] != 'keep'
        REVIEWED_PYTHON_ARGS = frozenset({(p, blob(first, p), A) for p in ('tests/args.py', 'tests/args_sub.py', 'tests/args_alias.py',
                                                                            'tests/args_rebind.py', 'tests/prog.py', 'tests/prog_cli.py', 'tests/prog_test.py')}
                                         | {('tests/args.py', blob(first, 'tests/args.py'), later.ref)})
        try:
            for repo in (first, later):
                model, rows = run(repo, standalone=[args_role, sub_role])
                for path, role, line in (('tests/args.py', args_role, 3), ('tests/args_sub.py', sub_role, 9)):
                    assert rows[path]['class'] == 'keep', path
                    entry = model['entry_points']['py-args:' + path]
                    assert entry['source_only'] and entry['python_argument_role'] and entry['validation_at_measured_revision']['status'] == 'unavailable'
                    assert entry['command'] == 'python3 -B ' + path and entry['location'] == path + ':' + str(line)
                    assert entry['interface'] == role['interface'] and entry['provenance'] == role['provenance']
                    assert not any(k.endswith(':' + path) and not k.startswith('py-args:') for k in model['entry_points'])
                # Nothing else changes: no read, helper, child or output credit.
                assert all(canonical(r) == canonical(baseline[p]) for p, r in rows.items() if p not in ('tests/args.py', 'tests/args_sub.py')
                           and p in baseline and repo is later)
            # The role anchors no route: the malformed row is never even inspected.
            _, rows = run(later, {'static_routes': [route(first, 'py-args:tests/args.py', 'node-import', [frame(first, 'tests/args.py', 2)], 'tests/corpus/c.txt')]},
                          standalone=[args_role])
            assert rows['tests/corpus/c.txt']['class'] != 'keep'
            # Negative controls: schema, revision, command, review set, provenance, source, entry, interface.
            for change, text in (({'extra': 1}, 'invalid Python argument role'), ({'purpose': ' '}, 'invalid Python argument role'),
                                 ({'interface': []}, 'invalid Python argument role'),
                                 ({'provenance': {'commit': A, 'path': 'tests/args.py'}}, 'invalid Python argument role'),
                                 ({'provenance': dict(args_role['provenance'], commit=[A])}, 'invalid Python argument role'),
                                 ({'input_revision': 'HEAD'}, 'full commit revision'),
                                 ({'command': ['python3', '-B', 'tests/args.py', 'label', 'true']}, 'unsupported Python argument role'),
                                 ({'command': ['python3', 'tests/args.py']}, 'unsupported Python argument role'),
                                 ({'command': ['python3', '-m', 'unittest', 'tests/args.py']}, 'unsupported Python argument role'),
                                 ({'source_blob': '0' * 40}, 'unreviewed Python argument role'),
                                 ({'provenance': dict(args_role['provenance'], commit='0' * 40)}, 'unreviewed Python argument role'),
                                 ({'provenance': dict(args_role['provenance'], path='tests/args_sub.py')}, 'unreviewed Python argument role'),
                                 ({'provenance': dict(args_role['provenance'], commit=later.ref)}, 'introducing provenance'),
                                 ({'entry_line': 2}, 'top-level entry'), ({'entry_line': True}, 'top-level entry'),
                                 ({'interface': dict(args_interface, argv_lines=[3])}, 'interface mismatch'),
                                 ({'interface': dict(args_interface, positionals=[[2, 'label']])}, 'interface mismatch')):
                rejected(first, text, standalone=[dict(args_role, **change)])
            rejected(first, 'unverifiable historical runner demonstration', standalone=[dict(args_role, input_revision='0' * 40)])
            # The configured CLI, module CLI and unittest guards are unchanged and refuse the role.
            for path, line in (('tests/prog_test.py', 4), ('tests/prog_cli.py', 5)):
                rejected(first, 'matches a configured CLI or unittest form', standalone=[py_role(path, line, {})])
            # A default program or an unaudited argv form has no argument interface.
            for path, line in (('tests/prog.py', 4), ('tests/args_alias.py', 2), ('tests/args_rebind.py', 3)):
                rejected(first, 'audited argument interface', standalone=[py_role(path, line, {})])
            # No promotion beside another role for the same path and revision.
            rejected(first, 'conflicting standalone', standalone=[args_role, dict(program, path='tests/args.py', source_blob=blob(first, 'tests/args.py'),
                     command=['python3', '-B', 'tests/args.py'], entry_line=3)])
            rejected(first, 'conflicting standalone', standalone=[dict(program, path='tests/args.py', source_blob=blob(first, 'tests/args.py'),
                     command=['python3', '-B', 'tests/args.py'], entry_line=3), args_role])
            # A current definition of the same path supersedes the role at a later revision.
            current_program = dict(program, path='tests/args.py', input_revision=later.ref, source_blob=blob(later, 'tests/args.py'),
                                   command=['python3', '-B', 'tests/args.py'], entry_line=3)
            model, _ = run(later, standalone=[args_role, current_program])
            assert 'py-args:tests/args.py' not in model['entry_points'] and 'source-only:tests/args.py' in model['entry_points']
            # The role is no Git policy writer: it credits no generated output.
            writer = {'path': 'tests/args.py', 'blob': blob(first, 'tests/args.py'), 'line': 5, 'literal': 'out.json'}
            policy = {'path': 'tests/gen/.gitignore', 'blob': blob(first, 'tests/gen/.gitignore'), 'purpose': 'Synthetic output policy.',
                      'matches': [{'line': 1, 'output': 'out.json', 'writer': writer}]}
            rejected(first, 'not an entry point source', {'git_policies': [policy]}, standalone=[args_role])
            REVIEWED_PYTHON_ARGS = frozenset()
            rejected(first, 'unreviewed Python argument role', standalone=[args_role])
        finally: REVIEWED_PYTHON_ARGS = reviewed_args
        # A changed source drops the root at a later revision.
        args_edited = commit({'tests/args.py': files['tests/args.py'] + '# changed\n'}, 'changed argument program')
        REVIEWED_PYTHON_ARGS = reviewed_args | {('tests/args.py', blob(first, 'tests/args.py'), A)}
        try:
            model, rows = run(args_edited, standalone=[args_role])
            assert 'py-args:tests/args.py' not in model['entry_points'] and rows['tests/args.py']['class'] != 'keep'
            rejected(args_edited, 'source mismatch', standalone=[dict(args_role, input_revision=args_edited.ref)])
        finally: REVIEWED_PYTHON_ARGS = reviewed_args

        # (7) H997 reviewed live shell/Node entry-source role: a source-only
        # root bound to blob, interpreter, recorded interface and introducing
        # commit that anchors nothing and credits no read, helper or output.
        global REVIEWED_NONPY_ENTRIES
        reviewed_nonpy = REVIEWED_NONPY_ENTRIES
        assert len(reviewed_nonpy) == 178 and len({p for p, _, _ in reviewed_nonpy}) == 178  # H997 115, H1025 61, H1004 2
        assert all(p.startswith('tests/') and posixpath.splitext(p)[1] in NONPY_SHEBANGS
                   and '.test.' not in p and classifier['hex_pin'](b, 40) and classifier['hex_pin'](c, 40) for p, b, c in reviewed_nonpy)
        assert all(p.startswith(('tests/directruntime-20261104/', 'tests/upstream/')) for p, _, _ in reviewed_nonpy - REVIEWED_NONPY_ENTRIES_H1025 - REVIEWED_NONPY_ENTRIES_H1004)
        witnesses = {'tests/directruntime-20261104/shared-translator/bounded.sh', 'tests/directruntime-20261104/native-browser/readbounds/module-gates.sh',
                     'tests/directruntime-20261104/memory-references/native-source-controls.mjs'}
        assert witnesses <= {p for p, _, _ in reviewed_nonpy}
        assert ('tests/directruntime-20261104/shared-translator/bounded.sh', 'a6686039c6dec3b35d2f06a2b8403be31ff9dd42',
                'b44f0de87c2ab845b79c9d84004dcb7c91babded') in reviewed_nonpy
        sh_interface = {'interpreter': 'bash', 'shebang': '#!/usr/bin/env bash', 'entry_line': 2}
        mjs_interface = {'interpreter': 'node', 'shebang': None, 'entry_line': 2}
        cjs_interface = {'interpreter': 'node', 'shebang': '#!/usr/bin/env node', 'entry_line': 3}
        assert nonpython_entry_interface('tests/drive.sh', files['tests/drive.sh']) == sh_interface
        assert nonpython_entry_interface('tests/drive.mjs', files['tests/drive.mjs']) == mjs_interface
        assert nonpython_entry_interface('tests/drive.cjs', files['tests/drive.cjs']) == cjs_interface
        for path in ('tests/lib.sh', 'tests/drive-sh.sh', 'tests/lib.mjs', 'tests/lib.cjs', 'tests/drive.test.mjs', 'tests/drive.js', 'tests/prog.py'):
            assert nonpython_entry_interface(path, files[path]) is None, path
        for path, text in (('x.mjs', "import 'node:fs';\n// only imports\n"), ('x.mjs', 'const a = 1;\nexport { a };\n'),
                           ('x.mjs', 'const a = 1;\nexport default a;\n'), ('x.cjs', 'const a = 1;\nexports.a = a;\n'),
                           ('x.cjs', 'const a = 1;\nmodule .exports = a;\n'), ('x.mjs', '#!/usr/bin/node\nconsole.log(1);\n'),
                           ('x.sh', '#!/usr/bin/env bash\n# only comments\n  indented\n'), ('x.sh', '#!/usr/bin/env bash\necho a\r\n'),
                           ('x.sh', '#!/usr/bin/env  bash\necho a\n'), ('x.sh', '#!/usr/bin/env bash\nf() { :; }\nreturn 0 2>/dev/null\n'),
                           ('x.test.cjs', 'console.log(1);\n'), ('x.py', 'print(1)\n'), ('x.mjs', 'console.log(1);\0\n'),
                           ('x.sh', '#!/usr/bin/env bash\nf() {\n  echo f\n}\nfunction g {\n  :\n}\nX=1\nexport Y=2\nset -e\n'),
                           ('x.sh', '#!/usr/bin/env bash\n[[ -n ${X:-} ]] && return 0\necho a\n'), ('x.sh', '#!/usr/bin/env bash\ncat <<EOF\nunterminated\n'), ('x.sh', '#!/usr/bin/env bash\necho a; return\n'),
                           ('x.cjs', 'Object.assign(exports, { a: 1 });\n'), ('x.cjs', "module['exports'] = 1;\n"),
                           ('x.cjs', "Object.defineProperty(module, 'exports', { value: 1 });\n"), ('x.cjs', 'const e = exports;\ne.a = 1;\n')):
            assert nonpython_entry_interface(path, text) is None, text
        # Commented or quoted keywords are not declarations; a dynamic import is code.
        assert nonpython_entry_interface('x.mjs', '// export const a = 1;\nconsole.log("export", `module.exports`);\n')['entry_line'] == 2
        assert nonpython_entry_interface('x.mjs', "import a from './a.mjs';\nimport('./b.mjs');\n")['entry_line'] == 2
        assert nonpython_entry_interface('x.mjs', "import {\n  a,\n  b,\n} from './a.mjs';\nconsole.log(a, b);\n")['entry_line'] == 5
        assert nonpython_entry_interface('x.cjs', 'const report = { exports: 1 };\nconst module = 2;\nconsole.log(module, report);\n')['entry_line'] == 1
        assert nonpython_entry_interface('x.sh', '#!/usr/bin/env bash\nset -e\nf() {\n  return 0\n}\nX=1\nf\n')['entry_line'] == 2
        assert nonpython_entry_interface('x.sh', "#!/usr/bin/env bash\ncat > m.c <<'EOF'\nint main(void){return 0;}\nEOF\ncc m.c\n")['entry_line'] == 2
        nonpy = lambda path, interface, command=None, repo=first, commit=A: {
            'path': path, 'input_revision': repo.ref, 'source_blob': blob(repo, path), 'kind': NONPY_ENTRY_KIND,
            'command': command or [interface['interpreter'], path], 'interface': interface,
            'provenance': {'commit': commit, 'path': path, 'blob': blob(repo, path)}, 'purpose': 'Synthetic reviewed live program.'}
        sh_role = nonpy('tests/drive.sh', sh_interface); mjs_role = nonpy('tests/drive.mjs', mjs_interface); cjs_role = nonpy('tests/drive.cjs', cjs_interface)
        roles = (('tests/drive.sh', sh_role, 2), ('tests/drive.mjs', mjs_role, 2), ('tests/drive.cjs', cjs_role, 3))
        assert all(baseline[path]['class'] != 'keep' for path, _, _ in roles)
        REVIEWED_NONPY_ENTRIES = frozenset({(p, blob(first, p), A) for p in ('tests/drive.sh', 'tests/drive.mjs', 'tests/drive.cjs', 'tests/lib.sh',
                                                                              'tests/drive-sh.sh', 'tests/lib.mjs', 'tests/drive.js', 'tests/walk.mjs')}
                                           | {('tests/drive.sh', blob(first, 'tests/drive.sh'), later.ref)})
        try:
            for repo in (first, later):
                model, rows = run(repo, standalone=[role for _, role, _ in roles])
                for path, role, line in roles:
                    assert rows[path]['class'] == 'keep', path
                    entry = model['entry_points']['nonpy-entry:' + path]
                    assert entry['source_only'] and entry['nonpython_entry_role'] and entry['validation_at_measured_revision']['status'] == 'unavailable'
                    assert entry['command'] == role['command'][0] + ' ' + path and entry['location'] == path + ':' + str(line)
                    assert entry['interface'] == role['interface'] and entry['provenance'] == role['provenance']
                    assert not any(k.endswith(':' + path) and not k.startswith('nonpy-entry:') for k in model['entry_points'])
                # Nothing else changes: no read, helper, child or output credit.
                assert all(canonical(r) == canonical(baseline[p]) for p, r in rows.items() if p not in [p for p, _, _ in roles]
                           and p in baseline and repo is later)
            # The role anchors no route: the malformed row is never even inspected.
            _, rows = run(later, {'static_routes': [route(first, 'nonpy-entry:tests/drive.mjs', 'node-import', [frame(first, 'tests/drive.mjs', 2)], 'tests/corpus/c.txt')]},
                          standalone=[mjs_role])
            assert rows['tests/corpus/c.txt']['class'] != 'keep'
            # Negative controls: schema, revision, interpreter, review set, provenance, source, interface.
            for change, text in (({'extra': 1}, 'invalid non-Python entry role'), ({'purpose': ' '}, 'invalid non-Python entry role'),
                                 ({'interface': []}, 'invalid non-Python entry role'),
                                 ({'provenance': {'commit': A, 'path': 'tests/drive.sh'}}, 'invalid non-Python entry role'),
                                 ({'provenance': dict(sh_role['provenance'], commit=[A])}, 'invalid non-Python entry role'),
                                 ({'input_revision': 'HEAD'}, 'full commit revision'),
                                 ({'command': ['bash', 'tests/drive.sh', 'arg']}, 'unsupported non-Python entry role'),
                                 ({'command': ['bash', '-x', 'tests/drive.sh']}, 'unsupported non-Python entry role'),
                                 ({'command': ['sh', 'tests/drive.sh']}, 'unsupported non-Python entry role'),
                                 ({'command': ['node', 'tests/drive.sh']}, 'unsupported non-Python entry role'),
                                 ({'command': ['tests/drive.sh']}, 'unsupported non-Python entry role'),
                                 ({'source_blob': '0' * 40}, 'unreviewed non-Python entry role'),
                                 ({'provenance': dict(sh_role['provenance'], commit='0' * 40)}, 'unreviewed non-Python entry role'),
                                 ({'provenance': dict(sh_role['provenance'], path='tests/drive.mjs')}, 'unreviewed non-Python entry role'),
                                 ({'provenance': dict(sh_role['provenance'], commit=later.ref)}, 'introducing provenance'),
                                 ({'interface': dict(sh_interface, entry_line=3)}, 'interface mismatch'),
                                 ({'interface': dict(sh_interface, shebang=None)}, 'interface mismatch'),
                                 ({'interface': dict(sh_interface, interpreter='sh')}, 'interface mismatch')):
                rejected(first, text, standalone=[dict(sh_role, **change)])
            rejected(first, 'unverifiable historical runner demonstration', standalone=[dict(sh_role, input_revision='0' * 40)])
            for change in ({'command': ['node', '--test', 'tests/drive.mjs']}, {'command': ['node', 'tests/drive.mjs', 'prepare']},
                           {'command': ['bash', 'tests/drive.mjs']}):
                rejected(first, 'unsupported non-Python entry role', standalone=[dict(mjs_role, **change)])
            # Other suffixes, Python and the node-test naming are refused before review.
            for path, interpreter in (('tests/drive.js', 'node'), ('tests/drive.test.mjs', 'node'), ('tests/prog.py', 'python3')):
                rejected(first, 'unsupported non-Python entry role', standalone=[nonpy(path, dict(mjs_interface, interpreter=interpreter))])
            # A library or an unaudited shebang has no entry interface, even when reviewed.
            for path in ('tests/lib.sh', 'tests/drive-sh.sh', 'tests/lib.mjs'):
                rejected(first, 'audited entry interface', standalone=[nonpy(path, sh_interface, [NONPY_SHEBANGS[posixpath.splitext(path)[1]][0], path])])
            # source-only-program and the H996 role stay Python-only.
            rejected(first, 'unsupported source-only program', standalone=[dict(program, path='tests/drive.sh', source_blob=blob(first, 'tests/drive.sh'),
                     command=['bash', 'tests/drive.sh'], entry_line=2)])
            rejected(first, 'unsupported Python argument role', standalone=[dict(sh_role, kind=PYTHON_ARGS_KIND, entry_line=2)])
            # No promotion beside another role for the same path and revision; a manual reproducer stays as it is.
            rejected(first, 'conflicting standalone', standalone=[nonpy('tests/walk.mjs', {'interpreter': 'node', 'shebang': None, 'entry_line': 1})])
            # A current definition of the same path supersedes the role at a later revision.
            for order in (1, -1):
                model, _ = run(later, standalone=[dict(sh_role, input_revision=later.ref, purpose='Current definition.'), sh_role][::order])
                assert model['entry_points']['nonpy-entry:tests/drive.sh']['source_declaration_revision'] == later.ref
                assert model['entry_points']['nonpy-entry:tests/drive.sh']['purpose'] == 'Current definition.'
            # The role is no Git policy writer: it credits no generated output.
            writer = {'path': 'tests/drive.sh', 'blob': blob(first, 'tests/drive.sh'), 'line': 3, 'literal': 'out.json'}
            policy = {'path': 'tests/gen/.gitignore', 'blob': blob(first, 'tests/gen/.gitignore'), 'purpose': 'Synthetic output policy.',
                      'matches': [{'line': 1, 'output': 'out.json', 'writer': writer}]}
            rejected(first, 'not an entry point source', {'git_policies': [policy]}, standalone=[sh_role])
            REVIEWED_NONPY_ENTRIES = frozenset()
            rejected(first, 'unreviewed non-Python entry role', standalone=[sh_role])
        finally: REVIEWED_NONPY_ENTRIES = reviewed_nonpy
        # A changed source drops the root at a later revision.
        sh_edited = commit({'tests/drive.sh': files['tests/drive.sh'] + '# changed\n'}, 'changed shell program')
        REVIEWED_NONPY_ENTRIES = reviewed_nonpy | {('tests/drive.sh', blob(first, 'tests/drive.sh'), A)}
        try:
            model, rows = run(sh_edited, standalone=[sh_role])
            assert 'nonpy-entry:tests/drive.sh' not in model['entry_points'] and rows['tests/drive.sh']['class'] != 'keep'
            rejected(sh_edited, 'source mismatch', standalone=[dict(sh_role, input_revision=sh_edited.ref)])
        finally: REVIEWED_NONPY_ENTRIES = reviewed_nonpy
        nonpy_roleset_controls(locals())  # H1025, in roles.py

        # (4) H979 persisted entered-module claims.
        assert run(first)[1]['tests/helper.py']['class'] == 'keep'
        persisted = {'persistent_module_entries': [claim]}
        assert run(later)[1]['tests/helper.py']['class'] != 'keep'
        model, rows = run(later, persisted)
        assert rows['tests/helper.py']['class'] == 'keep'
        details = rows['tests/helper.py']['runner_chain']['entry']['consumer_route']
        assert details == {'kind': 'persisted-module-entry', 'validated_revision': A, 'runner_definition_blob': blob(first, 'tests/test_entry.py')}
        assert rows['tests/helper.py']['runner_chain']['root'].startswith('committed:tests/test_entry.py:persisted-module:')
        assert run(first, persisted)[1]['tests/helper.py']['class'] == 'keep'
        rejected(later, 'not a reviewed routes.module_entries claim', persisted, entries=[])
        rejected(later, 'duplicate persisted module entry', {'persistent_module_entries': [claim, dict(claim)]})
        rejected(later, 'invalid persisted module entry', {'persistent_module_entries': [dict(claim, extra=1)]})
        for key, value, text in (('runner', 'nonpassing:tests/test_entry.py', 'needs a validated runner'),
                                 ('input_revision', '0' * 40, 'lacks its passing runner definition'),
                                 ('python', [0, 0, 0], 'UNVERIFIABLE module code identity'),
                                 ('collector_sha256', '0' * 64, 'unreviewed module entry collector'),
                                 ('module_code_sha256', '0' * 64, 'entered module code mismatch'),
                                 ('operation', 'validated Python read of measured bytes', 'unsupported module entry operation'),
                                 ('module_frame_line', True, 'invalid entered module frame location')):
            mutated = dict(claim, **{key: value})
            rejected(later, text, {'persistent_module_entries': [mutated]}, entries=[mutated])
        node_runner = dict(claim, runner='validated:tests/walk.test.mjs', frames=[frame(first, 'tests/walk.test.mjs', 1)])
        rejected(later, 'lacks its passing runner definition', {'persistent_module_entries': [node_runner]}, entries=[node_runner])
        # A changed target or runner grants nothing; forged current objects are refused.
        changed = commit({'tests/helper.py': 'VALUE = 4\n'}, 'changed helper')
        assert run(changed, persisted)[1]['tests/helper.py']['class'] != 'keep'
        forged = dict(claim, target_blob=blob(changed, 'tests/helper.py'),
                      module_code_sha256=observer.code_fingerprint(compile('VALUE = 4\n', '<measured>', 'exec', dont_inherit=True)))
        rejected(changed, 'objects differ at recorded revision', {'persistent_module_entries': [forged]}, entries=[forged])
        runner_changed = commit({'tests/helper.py': files['tests/helper.py'], 'tests/test_entry.py': files['tests/test_entry.py'] + '# changed\n'}, 'changed runner')
        assert run(runner_changed, persisted)[1]['tests/helper.py']['class'] != 'keep'

        # (8) H999 reviewed live non-root Lean check source: source-only root
        # bound to blob, interface, introducing commit and reviewed drivers.
        global REVIEWED_LEAN_CHECKS, REVIEWED_LEAN_CHECK_INVOCATIONS
        saved = REVIEWED_LEAN_CHECKS, REVIEWED_LEAN_CHECK_INVOCATIONS, reviewed_nonpy
        pa, pb = 'tests/directruntime-20261104/control-tuples/ProofAudit.lean', 'c60ce39b40db0e4a797d0afa4c1a8f14c40df466'
        assert REVIEWED_LEAN_CHECKS == {(pa, pb, 'e6849d3bdf516099d20c33d3581d523449764018')} and len(REVIEWED_LEAN_CHECK_INVOCATIONS) == 5
        assert all(q == pa and b == pb and (d, db) in {(p, b) for p, b, _ in reviewed_nonpy} and d.endswith('-validate.sh')
                   and not d.endswith('/read-bounds-validate.sh') for q, b, d, db, _ in REVIEWED_LEAN_CHECK_INVOCATIONS)
        G, X = LEAN_CHECK_DRIVER_LINE, 'tests/c/A.lean'
        gate = '#!/usr/bin/env bash\n' + LEAN_CHECK_GATE_BRANCH + '\n' + LEAN_CHECK_GATE_LINE + '\nfi\n'
        head = ('#!/usr/bin/env bash\n# driver\nset -euo pipefail\nfor t in Lib.Mod; do\n  lake build "$t"\ndone\nfiles=(tests/c/S.lean)\n'
                'for n in P Q; do\n files+=("tests/c/$n.lean")\ndone\nfiles+=(tests/c/A.lean tests/c/T.lean)\n'
                'files+=(tests/c/E.lean tests/c/I.lean tests/pkg/A.lean)\n')
        driver = head + G + '\npython3 tests/helper.py\n'; gl = head.count('\n') + 1
        audit = 'import tests.d.Dep Lib.Mod\n-- c\n/- block\n   c -/\n#check @D.v\n#print axioms D.v\n#check D.v  -- t\n'
        add = {'scripts/coord-tools/gate.sh': gate, 'tests/c/run.sh': driver, X: audit, 'tests/d/Dep.lean': 'def D.v : Nat := 1\n',
               'tests/c/E.lean': audit + '#eval IO.FS.readFile "tests/data.txt"\n', 'tests/c/I.lean': audit, 'tests/c/J.lean': 'import tests.c.I\n',
               'tests/pkg/lakefile.toml': 'name = "pkg"\n', 'tests/pkg/A.lean': audit,
               'tests/c/exec.sh': driver.replace('set -euo pipefail\n', 'set -euo pipefail\nexec true\n')}
        lf = commit(add, 'Lean checks'); L = lf.ref; ll = commit({'tests/unrelated.txt': 'L\n'}, 'Lean later')
        face = {'imports': ['tests.d.Dep', 'Lib.Mod'], 'check_lines': [5, 7], 'axiom_lines': [6]}
        code = classifier['lean_code']
        assert lean_check_interface(code, X, audit) == face and lean_check_invocation(driver, X, gl)
        for t in ('#eval 1', 'theorem t : True := trivial', 'set_option x true', 'open D', '#check (D.v)', '#check D.v + 1', ' #check D.v',
                  '#check\n  D.v', 'import Lean', '#check "x"', '"x"', '#print D.v', 'run_cmd pure ()', '#check a\r', '#check a\0'):
            assert lean_check_interface(code, X, audit + t + '\n') is None, t
        assert lean_check_interface(code, X, 'import D\n') is None and lean_check_interface(code, 'x.py', audit) is None
        assert lean_check_interface(code, X, 'prelude\n' + audit) is None
        for t in ('exec bash x.sh', 'cd tests', 'files=(tests/c/O.lean)', ' files=(tests/c/O.lean)', 'unset files', 'files[0]=x', 'bash() { :; }',
                  'export PATH="$PWD/b:$PATH"', 'cat <<EOF\nx\nEOF', 'source l.sh', '. l.sh', 'false && \\', 'exit 0', 'eval "$x"', 'trap f EXIT',
                  'files=(tests/c/A.lean ); files=( )', 'files=(x) # tests/c/A.lean )', 'echo "\nfiles+=(tests/c/A.lean)\n"', 'echo \\', ": '",
                  'hash -p /bin/true bash', 'kill $$', 'declare -n f=fil""es', 'files=("tests/c/A.lean")'):
            assert not lean_check_invocation(head + t + '\n' + G + '\n', X, gl + t.count('\n') + 1), t
        for t in (head + 'if false; then\n' + G + '\nfi\n', head + 'for x in a; do\n' + G + '\ndone\n', head + ' ' + G + '\n'):
            assert not lean_check_invocation(t, X, gl + 1 - t.startswith(head + ' ')), t
        for old, new in (('files+=(tests/c/A.lean ', 'files+=('), ('files+=(tests/c/A.lean', ' files+=(tests/c/A.lean'),
                         ('files+=(tests/c/A.lean', ' files=(tests/c/S.lean)\nfiles+=(tests/c/A.lean')):
            t = head.replace(old, new) + G + '\n'; assert not lean_check_invocation(t, X, t.count('\n')), new
        assert not lean_check_invocation(head + G.replace('per-file', 'touched') + '\n', X, gl)
        libs = lambda t: type('R', (), {'texts': {'lakefile.toml': t}})()
        assert _outside_root_libraries(libs('[[lean_lib]]\nname = "Lib"\n[[lean_exe]]\nname = "x"\nroot = "Main"\n'), X)
        for t in ('name = "tests"', 'name = "L"\nsrcDir = "tests"', 'name = "L"\nsrcDir = "/r/tests"', 'name = "L"\nroots = "tests.c.A"', 'name = "L"\nsrcDir = "./tests/c"', 'name = "L"\nglobs = ["tests.+"]',
                  'name = "L"\nroots = ["L", "tests.c.A"]', 'name = "L"\nsrcDir = ".."', 'name = "L"\nroot = 1'):
            assert not _outside_root_libraries(libs('[[lean_lib]]\n' + t + '\n'), X), t
        assert not _outside_root_libraries(libs('[[lean_lib]\n'), X)
        call = lambda d='tests/c/run.sh', **k: dict({'driver': d, 'driver_blob': blob(lf, d), 'driver_commit': L, 'line': gl}, **k)
        mk = lambda p=X: {'path': p, 'input_revision': L, 'source_blob': blob(lf, p), 'kind': LEAN_CHECK_KIND, 'command': lean_check_command(p),
                          'interface': face, 'provenance': {'commit': L, 'path': p, 'blob': blob(lf, p)}, 'invocations': [call()], 'purpose': 'Synthetic.'}
        role = mk(); base_model, base = run(ll, entries=[])
        assert base[X]['class'] != 'keep' and base['tests/d/Dep.lean']['class'] != 'keep'
        srcs = (X, 'tests/c/E.lean', 'tests/c/I.lean', 'tests/pkg/A.lean')
        REVIEWED_LEAN_CHECKS = frozenset({(p, blob(lf, p), L) for p in srcs})
        REVIEWED_LEAN_CHECK_INVOCATIONS = frozenset({(p, blob(lf, p), d, blob(lf, d), gl) for p in srcs for d in ('tests/c/run.sh', 'tests/c/exec.sh')})
        drivers = {(d, blob(lf, d), L) for d in ('tests/c/run.sh', 'tests/c/exec.sh')}
        REVIEWED_NONPY_ENTRIES = reviewed_nonpy | drivers
        try:
            for repo in (lf, ll):
                model, rows = run(repo, standalone=[role]); entry = model['entry_points']['lean-check:' + X]
                assert rows[X]['class'] == 'keep' and entry['source_only'] and entry['lean_check_role']
                assert entry['validation_at_measured_revision']['status'] == 'unavailable' and entry['location'] == 'tests/c/run.sh:%d' % gl
                assert entry['command'] == 'lake lean tests/c/A.lean -- --tstack=131072' and entry['invocations'] == role['invocations']
                assert entry['interface'] == face and entry['provenance'] == role['provenance']
                if repo is ll:  # no import-dependency, driver, read or proof credit
                    assert all(canonical(r) == canonical(base[p]) for p, r in rows.items() if p != X)
                    assert set(model['entry_points']) == set(base_model['entry_points']) | {'lean-check:' + X}
            _, rows = run(ll, {'static_routes': [route(lf, 'lean-check:' + X, 'lean-readFile', [frame(lf, X, 5)], 'tests/data.txt')]}, standalone=[role])
            assert rows['tests/data.txt']['class'] != 'keep'
            Z = '0' * 40
            for change, text in (({'extra': 1}, 'invalid Lean check'), ({'purpose': ' '}, 'invalid Lean check'), ({'invocations': []}, 'invalid Lean check'),
                                 ({'invocations': [call(), call()]}, 'invalid Lean check'), ({'invocations': [call(line=str(gl))]}, 'invalid Lean check'),
                                 ({'invocations': [call(command=['bash'])]}, 'invalid Lean check'), ({'provenance': {'commit': L}}, 'invalid Lean check'),
                                 ({'input_revision': 'HEAD'}, 'full commit revision'), ({'command': ['lean', X]}, 'unsupported Lean check role invocation'),
                                 ({'command': ['lake', 'env', 'lean', X]}, 'unsupported Lean check role invocation'),
                                 ({'command': lean_check_command(X) + ['x']}, 'unsupported Lean check role invocation'),
                                 ({'source_blob': Z}, 'unreviewed Lean check role'), ({'provenance': dict(role['provenance'], commit=Z)}, 'unreviewed Lean check role'),
                                 ({'invocations': [call(line=gl - 1)]}, 'role invocation'), ({'invocations': [call(driver_blob=Z)]}, 'role invocation'),
                                 ({'invocations': [call(driver_commit=Z)]}, 'role invocation'),
                                 ({'invocations': [call(), call('tests/c/exec.sh')]}, 'driver does not run the source'),
                                 ({'interface': dict(face, check_lines=[5])}, 'interface mismatch'), ({'interface': dict(face, imports=['Lib.Mod'])}, 'interface mismatch'),
                                 ({'input_revision': Z}, 'unverifiable historical')):
                rejected(lf, text, standalone=[dict(role, **change)])
            rejected(lf, 'conflicting standalone', standalone=[role, dict(role, purpose='Other.')])
            rejected(lf, 'check-only interface', standalone=[mk('tests/c/E.lean')])
            for path in ('tests/c/I.lean', 'tests/pkg/A.lean'):  # importer, Lake package: stale
                assert 'lean-check:' + path not in run(lf, standalone=[mk(path)])[0]['entry_points']
            REVIEWED_NONPY_ENTRIES = reviewed_nonpy
            rejected(lf, 'role invocation', standalone=[role])
            REVIEWED_NONPY_ENTRIES = reviewed_nonpy | {('tests/c/run.sh', blob(lf, 'tests/c/run.sh'), A)}
            rejected(lf, 'driver lacks its introducing provenance', standalone=[dict(role, invocations=[call(driver_commit=A)])])
            REVIEWED_NONPY_ENTRIES = reviewed_nonpy | drivers
            for order in (1, -1):  # a current definition supersedes
                model, _ = run(ll, standalone=[dict(role, input_revision=ll.ref, purpose='Now.'), role][::order])
                assert model['entry_points']['lean-check:' + X]['purpose'] == 'Now.'
            # Other kinds and the manual-reproducer prefixes keep excluding Lean and Lake.
            src = {'path': X, 'input_revision': L, 'source_blob': blob(lf, X)}
            rejected(lf, 'unsupported source-only program', standalone=[dict(program, **src, command=['python3', '-B', X])])
            rejected(lf, 'unsupported non-Python entry role', standalone=[{**{k: v for k, v in role.items() if k != 'invocations'}, 'kind': NONPY_ENTRY_KIND}])
            for command in (lean_check_command(X), ['lean', X], ['lake', 'env', 'lean', X]):
                rejected(lf, 'unsupported manual reproducer', standalone=[{**src, 'kind': 'manual-reproducer', 'command': command, 'documentation': doc(1, ' '.join(command))}])
            rejected(lf, 'unsupported standalone invocation', standalone=[{**src, 'kind': 'unittest', 'command': lean_check_command(X)}])
            writer = {'path': X, 'blob': blob(lf, X), 'line': 5, 'literal': 'out.json'}
            policy = {'path': 'tests/gen/.gitignore', 'blob': blob(lf, 'tests/gen/.gitignore'), 'purpose': 'P.', 'matches': [{'line': 1, 'output': 'out.json', 'writer': writer}]}
            rejected(lf, 'not an entry point source', {'git_policies': [policy]}, standalone=[role])
            # A root library, changed gate.sh, source or driver drops the root later; a current claim on changed bytes is refused.
            for changes in ({'lakefile.toml': files['lakefile.toml'] + '[[lean_lib]]\nname = "tests"\n'}, {'scripts/coord-tools/gate.sh': gate.replace('131072', '65536')},
                            {'scripts/coord-tools/gate.sh': gate.replace('per-file ]', 'full ]')}, {X: audit + '#check D.v\n'}, {'tests/c/run.sh': driver + 'echo\n'}):
                edited = commit(changes, 'edited')
                model, rows = run(edited, standalone=[role])
                assert 'lean-check:' + X not in model['entry_points'] and rows[X]['class'] != 'keep'
                if X in changes or 'tests/c/run.sh' in changes: rejected(edited, 'source mismatch', standalone=[dict(role, input_revision=edited.ref)])
                commit({'scripts/coord-tools/gate.sh': gate, X: audit, 'tests/c/run.sh': driver, 'lakefile.toml': files['lakefile.toml']}, 'restored')
            REVIEWED_LEAN_CHECKS = frozenset()
            rejected(lf, 'unreviewed Lean check role', standalone=[role])
        finally: REVIEWED_LEAN_CHECKS, REVIEWED_LEAN_CHECK_INVOCATIONS, REVIEWED_NONPY_ENTRIES = saved
        lean_fixture_controls(locals())  # (9) H1015, in roles.py
        python_import_controls(locals())  # (10) H1051, in roles.py
        documentation_reference_controls(locals())  # (11) H1050, in roles.py
        nonpassing_persistence_controls(locals())  # (12) H1009, in roles.py
