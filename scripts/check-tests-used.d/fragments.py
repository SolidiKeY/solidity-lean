"""Deterministic additive census classification fragments."""
import ast
import bisect
import hashlib
import json
import posixpath
import re
import tempfile
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
CONSUMER_SECTIONS = ('persistent_reads', 'static_routes', 'git_policies')


def fragment_identity(section, row):
    if not isinstance(row, dict): raise ValueError('fragment entry must be an object')
    if section in ('roles', 'fixtures', 'git_policies'):
        keys = ('path',)
    elif section in ('standalone', 'generators', 'orphans'):
        keys = ('path', 'input_revision')
    elif section in ('module_entries', 'reads', 'persistent_reads'):
        keys = ('runner', 'input_revision', 'target', 'frames')
    elif section == 'static_routes':
        keys = ('runner', 'form', 'target', 'frames')
    else:
        raise ValueError('unknown fragment section')
    if any(k not in row for k in keys): raise ValueError('fragment entry lacks identity: ' + section)
    values = [row[k] for k in keys]
    if section in ('module_entries', 'reads', 'persistent_reads', 'static_routes'):
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


def _anchor_root(graph, runner, frames):
    """A current non-source-only root, or a demonstrated passing committed runner.

    A runner named validated:P or committed:P resolves to whichever of the two
    exists at the measured revision. Any other root (undemonstrated committed
    source, CLI/policy source role, derived claim) anchors nothing.
    """
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


def _js_mask(text):
    """Blank JS comments, templates and quoted strings; keep string literal spans.

    Regular-expression literals are not modelled. Callers locate keywords in
    the masked code and accept an operand only at a recorded literal start, so
    commented, quoted or templated text never yields a route.
    """
    out = []; literals = {}; at = 0; n = len(text)
    while at < n:
        c = text[at]
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
        else:
            out.append(c); at += 1; continue
        out.append(re.sub(r'[^\n]', ' ', text[at:end])); at = end
    return ''.join(out), literals


def _js_line(text, number):
    """The line, its masked code, line-relative literal spans, and whole-file mask."""
    code, literals = _js_mask(text)
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


def _lean_read(classifier, repo, source, number, cwd):
    """One literal read inside a top-level #eval command of this file.

    Only the elaborated runner file itself is accepted: an imported module's
    #eval does not run when its importer runs, and a def runs only if called.
    """
    code, literals = classifier['lean_lex'](repo.texts[source])
    starts = [0] + [m.end() for m in re.finditer('\n', code)]
    lines = code.splitlines()
    command = next((lines[k] for k in range(number - 1, -1, -1) if lines[k][:1].strip()), '')
    if not re.match(r'#eval\b', command): return None
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
        original, root = _anchor_root(graph, row['runner'], frames)
        if root is None: continue
        if root.get('source_only') and root.get('source_blob') != frames[0]['blob']: continue
        language = 'lean' if form.startswith('lean') else 'node'
        if language == 'lean' and len(frames) != 1: raise ValueError('Lean read must be in the elaborated runner file')
        suffixes = ('.lean',) if language == 'lean' else NODE_SUFFIXES
        if any(not f['path'].endswith(suffixes) for f in frames): raise ValueError('static route frame language mismatch')
        for caller, callee in zip(frames, frames[1:]):
            if _node_import(caller['path'], repo.texts[caller['path']], caller['line']) != callee['path']: raise ValueError('static route hop is not a literal import')
        reader = frames[-1]; cwd = root.get('cwd', '.')
        if form == 'node-import': resolved = _node_import(reader['path'], repo.texts[reader['path']], reader['line'])
        elif form == 'node-readFileSync': resolved = _node_read(reader['path'], repo.texts[reader['path']], reader['line'], cwd)
        else: resolved = _lean_read(classifier, repo, reader['path'], reader['line'], cwd)
        if resolved is None or resolved != target: raise ValueError('static route target is not the literal ' + form + ' operand')
        if form == 'node-import' and not target.endswith(NODE_SUFFIXES): raise ValueError('Node import target is not a module')
        if classifier['excluded'](target) or any(classifier['excluded'](f['path']) for f in frames): continue
        # A historical runner demonstrated these exact objects, or nothing.
        if root.get('source_only') and not _historical_objects(classifier, repo, root['source_demonstration_revision'],
                sorted({(f['path'], f['blob']) for f in frames} | {(target, row['target_blob'])})): continue
        operation, kind = STATIC_FORMS[form]
        hop = 'Node static import'
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
                    r['path'] == writer['path'] and 'derived_from' not in r and not k.startswith('git-policy:') for k, r in graph.roots.items()):
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
    git = classifier['git']; Repository = classifier['Repository']; inventory = classifier['inventory']
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
        def commit(changes, message):
            for path, text in changes.items():
                (root / path).parent.mkdir(parents=True, exist_ok=True); (root / path).write_text(text)
            git(root, 'add', '-A', '-f')
            git(root, '-c', 'user.name=Control', '-c', 'user.email=control@example.invalid', 'commit', '-qm', message)
            return Repository(root, 'HEAD')
        root.mkdir(); git(root, 'init', '-q')
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
