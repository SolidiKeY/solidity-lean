# H1113 (gh#1464, H62-REMAINING-INPUT-OWNER, A) census form: source-only roles for reviewed handoff and manifest
# witnesses of scripts/h62. Exec'd by registry.py in the namespace of fragments.py (see registry.py's header); it
# registers one late standalone kind and one control and binds no shared name. Opt-in: without a standalone row of
# this kind every classification and output byte is unchanged.
#
# Each role binds one exact (witness, blob) to the actual operation that reads it, re-derived from the syntax trees of
# the exact reader blobs, and to the identity of a current python3 -B entry root that imports the module involved:
#   pinned-history-show  the entry program runs `git ... show <BASE>:<rel>` with rel = <alias>.<PREFIX> / name inside a
#                        `for name in <alias>.<PINS>` loop, BASE a 40-hex class constant, alias the entry's sibling
#                        import of the module; the module binds PINS = {basename: (size, sha256)} pinning the witness
#                        bytes and PREFIX = Path(<witness directory>); BASE is an ancestor of the measured revision
#                        holding the same blob. Reviewed: the three SHA-pinned audit-theories handoff records read by
#                        test_current_replay.py and pinned by paired_evidence.py.
#   main-root-read       the module's top-level `if __name__ == '__main__':` block calls F(ROOT), ROOT bound once to
#                        Path(__file__).resolve().parents[depth], and F(r) binds V = r / '<witness>' and reads
#                        V.read_text(); the entry program loads the module with importlib.util.spec_from_file_location
#                        (<name>, ROOT / '<module>'), module_from_spec and exec_module. Reviewed: bulk-manifest.json,
#                        read by public-api-inventory.py's main path and entered by test_public_api_inventory.py.
#                        Provenance by position: whether the main path runs is not decided (its H44 archive is
#                        unavailable); H1074 refused it as a consumer route, this is a source role only.
# Row shape (all keys required): {'kind': 'handoff-witness-role', 'path': P, 'input_revision': R, 'source_blob',
#   'command': ['python3', '-B', E], 'operation', 'entry': {'path': E, 'blob', 'import_line'},
#   'module': {'path': M, 'blob', 'line' (the pin line, or the main call line)}, 'read': {'path', 'line'}, 'purpose'}.
# Refused, left unresolved (reported back, never classified here):
#   audit-theories/handoff/scope-manifest.json: paired_evidence.py export packages it from the argument-supplied
#     --current-repository with no blob pin, no committed invocation binds that argument to this checkout, and the one
#     committed test packs a synthetic stand-in; no exact binding.
#   audit-precompiles/serial.toml (H1074): bin/lake reads it only through $H62_AUDIT_CONFIG; no literal, pin or
#     committed driver binds the path, and bin/lake itself has no role; no exact binding or independent role.
# A changed witness, entry or module blob, another reader, line, alias, operation or commit is refused (an
# unreviewed tuple) or stale (a historical row). Source-only: no consumer, invocation, execution, pass, read anchor,
# fixture, output, proof or runtime credit; another root of the path is never displaced.
import ast
import hashlib
import posixpath
import shlex
from pathlib import Path

HANDOFF_WITNESS_KIND = 'handoff-witness-role'
HANDOFF_WITNESS_PREFIX = 'handoff-witness:'
HANDOFF_WITNESS_OPERATIONS = {
    'pinned-history-show': 'git show of the exact witness blob at a pinned ancestor commit by a kept entry program, '
                           'authenticated by the size and SHA-256 pin of the module it imports',
    'main-root-read': 'repository-root read_text of the literal witness path on the main path of a module a kept entry '
                      'program loads by file location',
}
_HW_THEORIES = 'scripts/h62/item2/audit-theories/'
_HW_REPLAY = (_HW_THEORIES + 'test_current_replay.py', '57f9d543e4e0c5108f3392bf51b02152e8245877', 4)
_HW_PAIRED = (_HW_THEORIES + 'paired_evidence.py', 'be36e9615801d394d83697e3ba58a07fea4ae568')
_HW_GATE = 'scripts/h62/item6/migrate-root-gate/'
# (witness, blob, operation, entry, entry blob, import line, module, module blob, module line, read path, read line)
HANDOFF_WITNESS_REVIEWED = frozenset({
    (_HW_THEORIES + 'handoff/original-frozen-assignment.txt', '18e25bf3280604b02fc0877400b343a4749d9ea3', 'pinned-history-show',
     *_HW_REPLAY, *_HW_PAIRED, 22, _HW_REPLAY[0], 38),
    (_HW_THEORIES + 'handoff/original-work-and-backfill-queue.md', '73326fc36de3421854174f16e5cf62a7976ca29e', 'pinned-history-show',
     *_HW_REPLAY, *_HW_PAIRED, 23, _HW_REPLAY[0], 38),
    (_HW_THEORIES + 'handoff/CONFLICT-RESOLUTION-20261108.md', 'e824c7f9512b45028b20371048ad0de6fb75d436', 'pinned-history-show',
     *_HW_REPLAY, *_HW_PAIRED, 24, _HW_REPLAY[0], 38),
    (_HW_GATE + 'bulk-manifest.json', '225df645d3ebfc2903b2f54fce53b2e2f8295e87', 'main-root-read',
     'tests/h62/item6/migrate-root-gate/test_public_api_inventory.py', 'c4e0b487f0a70e1d8f6435bc8ea8a38e6b5ac7cd', 20,
     _HW_GATE + 'public-api-inventory.py', 'a5d6dde5be926751371f820ea6afb463281d515a', 349, _HW_GATE + 'public-api-inventory.py', 200),
})
HANDOFF_WITNESS_UNRESOLVED = ('scripts/h62/item2/audit-theories/handoff/scope-manifest.json', 'scripts/h62/item2/audit-precompiles/serial.toml')
_HW_RUNS = ('check_output', 'run')


def _hw_shared(name):
    """A name of the fragments.py namespace this module is exec'd in."""
    return globals()[name]


def _hw_parse(text):
    try: return ast.parse(text)
    except (SyntaxError, ValueError, RecursionError): return None


def _hw_bindings(tree, name):
    """How many places in tree bind name: stores, deletions, parameters, imports, defs, handlers, patterns, global/nonlocal."""
    count = 0
    for node in ast.walk(tree):
        if isinstance(node, ast.Name): count += node.id == name and isinstance(node.ctx, (ast.Store, ast.Del))
        elif isinstance(node, ast.arg): count += node.arg == name
        elif isinstance(node, (ast.Import, ast.ImportFrom)): count += sum((a.asname or a.name).split('.')[0] == name for a in node.names)
        elif isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef, ast.ExceptHandler, ast.MatchAs, ast.MatchStar)):
            count += getattr(node, 'name', None) == name
        elif isinstance(node, ast.MatchMapping): count += node.rest == name
        elif isinstance(node, (ast.Global, ast.Nonlocal)): count += name in node.names
    return count


def _hw_module_value(tree, name):
    """The value of the one module-level `name = value`, when nothing else in the module binds name."""
    values = [n.value for n in tree.body if isinstance(n, ast.Assign) and len(n.targets) == 1 and isinstance(n.targets[0], ast.Name)
              and n.targets[0].id == name]
    return values[0] if len(values) == 1 and _hw_bindings(tree, name) == 1 else None


def _hw_imported(tree, name, module):
    """True iff name's one binding is `from <module> import name` (unaliased, absolute)."""
    return _hw_bindings(tree, name) == 1 and any(isinstance(n, ast.ImportFrom) and n.module == module and n.level == 0
                                                 and any(a.name == name and a.asname is None for a in n.names) for n in tree.body)


def _hw_plain_import(tree, name):
    """True iff name's one binding is a top-level plain `import name` (or `import name.sub`)."""
    return _hw_bindings(tree, name) == 1 and any(isinstance(n, ast.Import) and any(
        a.asname is None and a.name.split('.')[0] == name for a in n.names) for n in tree.body)


def _hw_const(node, kind=str):
    return node.value if isinstance(node, ast.Constant) and type(node.value) is kind else None


def _hw_attr(node, base, attr):
    """True iff node is the attribute base.attr of a plain name."""
    return isinstance(node, ast.Attribute) and node.attr == attr and isinstance(node.value, ast.Name) and node.value.id == base


def _hw_root(tree, node, path):
    """True iff node is a name bound once to Path(__file__).resolve().parents[k], the repository root of path."""
    value = _hw_module_value(tree, node.id) if isinstance(node, ast.Name) else None
    if not (isinstance(value, ast.Subscript) and _hw_const(value.slice, int) == path.count('/')
            and isinstance(value.value, ast.Attribute) and value.value.attr == 'parents'):
        return False
    resolve = value.value.value
    if not (isinstance(resolve, ast.Call) and not resolve.args and not resolve.keywords and isinstance(resolve.func, ast.Attribute)
            and resolve.func.attr == 'resolve'):
        return False
    call = resolve.func.value
    return (isinstance(call, ast.Call) and isinstance(call.func, ast.Name) and call.func.id == 'Path' and not call.keywords
            and len(call.args) == 1 and isinstance(call.args[0], ast.Name) and call.args[0].id == '__file__'
            and _hw_bindings(tree, '__file__') == 0 and _hw_imported(tree, 'Path', 'pathlib'))


def _hw_parents(tree):
    parents = {}
    for node in ast.walk(tree):
        for child in ast.iter_child_nodes(node): parents[child] = node
    return parents


def _hw_ancestors(parents, node):
    while node in parents:
        node = parents[node]; yield node


def _hw_calls(tree, line):
    return [n for n in ast.walk(tree) if isinstance(n, ast.Call) and n.lineno == line]


def handoff_pin(module_text, witness, data, pin_line):
    """The (PINS, PREFIX) names of a module pinning witness's bytes at pin_line, else None.

    PINS is one module-level dict whose one key basename(witness), on pin_line,
    maps to (len(data), sha256(data)); PREFIX is one module-level name bound to
    Path(<witness directory>), Path imported from pathlib."""
    tree = _hw_parse(module_text)
    if tree is None: return None
    base, directory = posixpath.basename(witness), posixpath.dirname(witness)
    pins = None
    for node in tree.body:
        if not (isinstance(node, ast.Assign) and len(node.targets) == 1 and isinstance(node.targets[0], ast.Name)
                and isinstance(node.value, ast.Dict)): continue
        keys = [_hw_const(k) for k in node.value.keys]
        if keys.count(base) != 1 or None in keys or len(set(keys)) != len(keys): continue
        key = node.value.keys[keys.index(base)]; value = node.value.values[keys.index(base)]
        if (key.lineno == pin_line and isinstance(value, ast.Tuple) and len(value.elts) == 2
                and _hw_const(value.elts[0], int) == len(data) and _hw_const(value.elts[1]) == hashlib.sha256(data).hexdigest()
                and _hw_module_value(tree, node.targets[0].id) is node.value):
            pins = node.targets[0].id
    prefixes = [n.targets[0].id for n in tree.body if isinstance(n, ast.Assign) and len(n.targets) == 1 and isinstance(n.targets[0], ast.Name)
                and isinstance(n.value, ast.Call) and isinstance(n.value.func, ast.Name) and n.value.func.id == 'Path'
                and len(n.value.args) == 1 and not n.value.keywords and _hw_const(n.value.args[0]) == directory]
    if pins is None or len(prefixes) != 1 or _hw_module_value(tree, prefixes[0]) is None or not _hw_imported(tree, 'Path', 'pathlib'):
        return None
    return pins, prefixes[0]


def handoff_pinned_show(entry_text, entry_path, module_path, import_line, read_line, pins, prefix):
    """The 40-hex BASE commit of the entry's pinned `git show BASE:rel` read, else None (see the header)."""
    tree = _hw_parse(entry_text)
    if tree is None or posixpath.dirname(entry_path) != posixpath.dirname(module_path) or not _hw_plain_import(tree, 'subprocess'): return None
    name = posixpath.basename(module_path)[:-3]
    imports = [n for n in tree.body if isinstance(n, ast.Import) and n.lineno == import_line and len(n.names) == 1 and n.names[0].name == name]
    if len(imports) != 1: return None
    alias = imports[0].names[0].asname or name
    if _hw_bindings(tree, alias) != 1: return None
    parents = _hw_parents(tree)
    for call in _hw_calls(tree, read_line):
        if not (isinstance(call.func, ast.Attribute) and call.func.attr in _HW_RUNS and isinstance(call.func.value, ast.Name)
                and call.func.value.id == 'subprocess' and len(call.args) == 1 and isinstance(call.args[0], ast.List)
                and [k.arg for k in call.keywords] == ['cwd'] and _hw_attr(call.keywords[0].value, alias, 'ROOT')):
            continue
        words = call.args[0].elts
        options = [_hw_const(w) for w in words[1:-2]]
        if (len(words) < 3 or _hw_const(words[0]) != 'git' or _hw_const(words[-2]) != 'show'
                or not all(isinstance(o, str) and o.startswith('--') for o in options)):
            continue
        spec = words[-1]
        if not (isinstance(spec, ast.BinOp) and isinstance(spec.op, ast.Add) and isinstance(spec.left, ast.BinOp)
                and isinstance(spec.left.op, ast.Add) and _hw_const(spec.left.right) == ':' and isinstance(spec.right, ast.Call)
                and not spec.right.args and not spec.right.keywords and isinstance(spec.right.func, ast.Attribute)
                and spec.right.func.attr == 'as_posix' and isinstance(spec.right.func.value, ast.Name)
                and isinstance(spec.left.left, ast.Attribute) and _hw_attr(spec.left.left, 'self', spec.left.left.attr)):
            continue
        rel, constant = spec.right.func.value.id, spec.left.left.attr
        chain = list(_hw_ancestors(parents, call))
        loops = [n for n in chain if isinstance(n, ast.For)]; functions = [n for n in chain if isinstance(n, (ast.FunctionDef, ast.AsyncFunctionDef))]
        classes = [n for n in chain if isinstance(n, ast.ClassDef)]
        if not loops or not functions or not classes or not (chain.index(loops[0]) < chain.index(functions[0]) < chain.index(classes[0])):
            continue
        loop, function, owner = loops[0], functions[0], classes[0]
        if not (_hw_attr(loop.iter, alias, pins) and isinstance(loop.target, ast.Name)) or _hw_bindings(function, rel) != 1: continue
        index = loop.target.id
        bound = [s for s in loop.body if isinstance(s, ast.Assign) and len(s.targets) == 1 and isinstance(s.targets[0], ast.Name)
                 and s.targets[0].id == rel and s.lineno < read_line and isinstance(s.value, ast.BinOp) and isinstance(s.value.op, ast.Div)
                 and _hw_attr(s.value.left, alias, prefix) and isinstance(s.value.right, ast.Name) and s.value.right.id == index]
        if len(bound) != 1 or _hw_bindings(function, index) != 1: continue
        values = [s.value for s in owner.body if isinstance(s, ast.Assign) and len(s.targets) == 1 and isinstance(s.targets[0], ast.Name)
                  and s.targets[0].id == constant]
        stores = [n for n in ast.walk(tree) if isinstance(n, ast.Attribute) and n.attr == constant and not isinstance(n.ctx, ast.Load)]
        commit = _hw_const(values[0]) if len(values) == 1 and not stores and _hw_bindings(owner, constant) == 1 else None
        if isinstance(commit, str) and len(commit) == 40 and all(c in '0123456789abcdef' for c in commit): return commit
    return None


def handoff_main_read(module_text, module_path, witness, main_line, read_line):
    """True iff the module's main block calls F(ROOT) on main_line and F(r) reads (r / witness).read_text() on read_line."""
    tree = _hw_parse(module_text)
    if tree is None: return False
    functions = {n.name: n for n in tree.body if isinstance(n, ast.FunctionDef) and _hw_bindings(tree, n.name) == 1}
    mains = [n for n in tree.body if isinstance(n, ast.If) and isinstance(n.test, ast.Compare) and isinstance(n.test.left, ast.Name)
             and n.test.left.id == '__name__' and len(n.test.ops) == 1 and isinstance(n.test.ops[0], ast.Eq)
             and _hw_const(n.test.comparators[0]) == '__main__']
    if _hw_bindings(tree, '__name__') or len(mains) != 1: return False
    for call in (c for c in _hw_calls(mains[0], main_line)):
        if not (isinstance(call.func, ast.Name) and call.func.id in functions and len(call.args) == 1 and not call.keywords
                and _hw_root(tree, call.args[0], module_path)):
            continue
        function = functions[call.func.id]; params = function.args
        if (params.posonlyargs or params.vararg or params.kwonlyargs or params.kwarg or params.defaults or len(params.args) != 1
                or _hw_bindings(function, params.args[0].arg) != 1):
            continue
        root = params.args[0].arg
        for read in _hw_calls(function, read_line):
            if not (isinstance(read.func, ast.Attribute) and read.func.attr == 'read_text' and not read.args and not read.keywords
                    and isinstance(read.func.value, ast.Name)): continue
            name = read.func.value.id
            bound = [s for s in function.body if isinstance(s, ast.Assign) and len(s.targets) == 1 and isinstance(s.targets[0], ast.Name)
                     and s.targets[0].id == name and s.lineno < read_line and isinstance(s.value, ast.BinOp) and isinstance(s.value.op, ast.Div)
                     and isinstance(s.value.left, ast.Name) and s.value.left.id == root and _hw_const(s.value.right) == witness]
            if len(bound) == 1 and _hw_bindings(function, name) == 1: return True
    return False


def handoff_file_import(entry_text, entry_path, module_path, import_line):
    """True iff the entry loads module_path once at module level: spec_from_file_location(name, ROOT / module_path) on
    import_line, module_from_spec(spec) and spec.loader.exec_module(module), ROOT the entry's repository root."""
    tree = _hw_parse(entry_text)
    if tree is None or not _hw_plain_import(tree, 'importlib') or not any(
            isinstance(n, ast.Import) and any(a.name == 'importlib.util' and a.asname is None for a in n.names) for n in tree.body):
        return False
    util = lambda node, attr: (isinstance(node, ast.Call) and isinstance(node.func, ast.Attribute) and node.func.attr == attr
                               and isinstance(node.func.value, ast.Attribute) and node.func.value.attr == 'util'
                               and isinstance(node.func.value.value, ast.Name) and node.func.value.value.id == 'importlib' and not node.keywords)
    specs = [n for n in tree.body if isinstance(n, ast.Assign) and n.lineno == import_line and len(n.targets) == 1
             and isinstance(n.targets[0], ast.Name) and util(n.value, 'spec_from_file_location') and len(n.value.args) == 2
             and _hw_const(n.value.args[0]) is not None and isinstance(n.value.args[1], ast.BinOp) and isinstance(n.value.args[1].op, ast.Div)
             and _hw_const(n.value.args[1].right) == module_path and _hw_root(tree, n.value.args[1].left, entry_path)]
    if len(specs) != 1 or _hw_bindings(tree, specs[0].targets[0].id) != 1: return False
    spec = specs[0].targets[0].id
    modules = [n.targets[0].id for n in tree.body if isinstance(n, ast.Assign) and len(n.targets) == 1 and isinstance(n.targets[0], ast.Name)
               and util(n.value, 'module_from_spec') and len(n.value.args) == 1 and isinstance(n.value.args[0], ast.Name) and n.value.args[0].id == spec]
    if len(modules) != 1 or _hw_bindings(tree, modules[0]) != 1: return False
    return any(isinstance(n, ast.Expr) and isinstance(n.value, ast.Call) and isinstance(n.value.func, ast.Attribute)
               and n.value.func.attr == 'exec_module' and _hw_attr(n.value.func.value, spec, 'loader') and not n.value.keywords
               and len(n.value.args) == 1 and isinstance(n.value.args[0], ast.Name) and n.value.args[0].id == modules[0] for n in tree.body)


def handoff_operation(operation, entry_text, module_text, row, data):
    """The re-derived operation of a reviewed row: the BASE commit (pinned-history-show), True (main-root-read) or None."""
    e, m, r = row['entry'], row['module'], row['read']
    if operation == 'pinned-history-show':
        names = handoff_pin(module_text, row['path'], data, m['line'])
        return names and handoff_pinned_show(entry_text, e['path'], m['path'], e['import_line'], r['line'], *names)
    if operation == 'main-root-read':
        return (handoff_file_import(entry_text, e['path'], m['path'], e['import_line'])
                and handoff_main_read(module_text, m['path'], row['path'], m['line'], r['line']) or None)
    return None


def handoff_witness_root(classifier, graph, catalog, entry, reviewed=None):
    """H1113: a reviewed handoff or manifest witness as a source-only root of its exact blob.

    Late (after every other standalone definition) so the entry root exists.
    The row must be one reviewed tuple; its witness, entry and module blobs are
    current (a historical row with a changed blob is stale, a current one an
    error); the operation is re-derived on the measured bytes; the entry is a
    current python3 -B entry root of exactly its blob (else refused now, stale
    later); for pinned-history-show the BASE commit is an ancestor of the
    measured revision and holds the same witness blob. Never displaces another
    root of the path; anchors nothing.
    """
    repo = graph.repo; role = 'handoff witness role'
    reviewed = HANDOFF_WITNESS_REVIEWED if reviewed is None else reviewed
    required = {'kind', 'path', 'input_revision', 'source_blob', 'command', 'operation', 'entry', 'module', 'read', 'purpose'}
    e, m, r = entry.get('entry'), entry.get('module'), entry.get('read')
    if (set(entry) != required or not all(isinstance(entry[k], str) for k in ('path', 'source_blob', 'operation', 'purpose'))
            or not entry['purpose'].strip() or not isinstance(e, dict) or set(e) != {'path', 'blob', 'import_line'}
            or not isinstance(m, dict) or set(m) != {'path', 'blob', 'line'} or not isinstance(r, dict) or set(r) != {'path', 'line'}
            or not all(isinstance(x[k], str) for x, k in ((e, 'path'), (e, 'blob'), (m, 'path'), (m, 'blob'), (r, 'path')))
            or not all(type(n) is int for n in (e['import_line'], m['line'], r['line']))):
        raise ValueError('invalid ' + role + ' definition')
    p = entry['path']; revision = entry['input_revision']; blob = entry['source_blob']; operation = entry['operation']
    if not isinstance(revision, str) or not classifier['hex_pin'](revision, 40): raise ValueError(role + ' requires a full commit revision')
    if any(x is not entry and x.get('path') == p and x.get('input_revision') == revision for x in catalog['standalone']):
        raise ValueError('conflicting standalone definitions: ' + p)
    reader = e['path'] if operation == 'pinned-history-show' else m['path']
    if (operation not in HANDOFF_WITNESS_OPERATIONS or entry['command'] != ['python3', '-B', e['path']] or _hw_shared('_clean')(p) != p
            or p.endswith('.py') or e['path'] == m['path'] or not all(q.endswith('.py') for q in (e['path'], m['path'])) or r['path'] != reader):
        raise ValueError('unsupported ' + role + ' invocation: ' + p)
    if (p, blob, operation, e['path'], e['blob'], e['import_line'], m['path'], m['blob'], m['line'], r['path'], r['line']) not in reviewed:
        raise ValueError('unreviewed ' + role + ': ' + p)
    if not _hw_shared('_role_current')(classifier, repo, catalog, entry, [(p, blob), (e['path'], e['blob']), (m['path'], m['blob'])]): return
    if not all(q in repo.texts for q in (e['path'], m['path'])) or any(repo.tree[q][0] not in ('100644', '100755') for q in (p, e['path'], m['path'])):
        raise ValueError('unsupported ' + role + ' invocation: ' + p)
    held = handoff_operation(operation, repo.texts[e['path']], repo.texts[m['path']], entry, repo.bytes(p))
    if not held: raise ValueError(role + ' reader does not perform its operation: ' + r['path'] + ':' + str(r['line']))
    if operation == 'pinned-history-show':
        try:
            classifier['git'](repo.root, 'merge-base', '--is-ancestor', held, repo.ref)
            pinned = classifier['git'](repo.root, 'rev-parse', '--verify', '-q', held + ':' + p).decode().strip()
        except ValueError: pinned = None
        if pinned != blob: raise ValueError(role + ' pinned commit does not hold the witness blob: ' + held + ':' + p)
    if not _hw_shared('_entry_root')(graph, e['path'], e['blob']):
        if revision == repo.ref: raise ValueError(role + ' entry is not a python3 -B entry root: ' + e['path'])
        return
    if any(x['path'] == p for x in graph.roots.values()): return
    identity = HANDOFF_WITNESS_PREFIX + p
    graph.root(p, 'reviewed handoff witness source role', shlex.join(entry['command']), r['path'], r['line'], root_id=identity)
    if identity not in graph.roots: return
    graph.roots[identity].update({'source_only': True, 'handoff_witness_role': True, 'source_blob': blob, 'purpose': entry['purpose'],
        'program_role': HANDOFF_WITNESS_KIND, 'interface': {'operation': operation, 'description': HANDOFF_WITNESS_OPERATIONS[operation]},
        'entry': e, 'module': m, 'read': r, 'source_declaration_revision': revision,
        **({'pinned_commit': held} if operation == 'pinned-history-show' else {}),
        'validation_at_measured_revision': {'status': 'unavailable', 'command': entry['command'],
            'reason': 'Reviewed witness bound to the exact operation of a reviewed reader and the identity of a kept entry program; '
                      'nothing is run or certified to pass here. Source role only: no consumer, invocation, execution, pass, read anchor, '
                      'fixture, output, proof or runtime credit.'}})


def handoff_witness_controls(env):
    """H1113 controls, run by successor_controls with its helpers: the reviewed
    rows on their pinned blobs, both operations on synthetic witnesses, and
    refusals (changed blob, another reader, line, alias, operation or commit,
    unreviewed rows, a missing entry root, schema and conflict errors)."""
    global HANDOFF_WITNESS_REVIEWED
    commit, run, rejected, blob, classifier, root = (env[k] for k in ('commit', 'run', 'rejected', 'blob', 'classifier', 'root'))
    git = classifier['git']; canonical = _hw_shared('canonical')
    assert HANDOFF_WITNESS_KIND in _hw_shared('LATE_SOURCE_ROLE_KINDS') and HANDOFF_WITNESS_KIND not in _hw_shared('SOURCE_ROLE_KINDS')
    # The reviewed rows: four witnesses, never the two refused ones, each re-derived on its pinned blobs when held.
    assert len(HANDOFF_WITNESS_REVIEWED) == 4 and not {t[0] for t in HANDOFF_WITNESS_REVIEWED} & set(HANDOFF_WITNESS_UNRESOLVED)
    home = Path(classifier['__file__']).resolve().parents[1]
    def held(b):
        try: return git(home, 'cat-file', 'blob', b)
        except ValueError: return None
    for p, b, op, ep, eb, il, mp, mb, ml, rp, rl in sorted(HANDOFF_WITNESS_REVIEWED):
        data, etext, mtext = held(b), held(eb), held(mb)
        if None in (data, etext, mtext): continue
        row = {'path': p, 'entry': {'path': ep, 'blob': eb, 'import_line': il}, 'module': {'path': mp, 'blob': mb, 'line': ml}, 'read': {'path': rp, 'line': rl}}
        assert handoff_operation(op, etext.decode(), mtext.decode(), row, data), p
        other = 'main-root-read' if op == 'pinned-history-show' else 'pinned-history-show'
        assert not handoff_operation(other, etext.decode(), mtext.decode(), row, data), p
        if op == 'pinned-history-show':  # other witness bytes break the size and SHA-256 pin
            assert not handoff_operation(op, etext.decode(), mtext.decode(), row, data + b'\n'), p
    D = 'scripts/h62/hw/'; H = D + 'handoff/'; W = H + 'a.md'; X = H + 'b.md'; B = D + 'bulk.json'
    PM = D + 'pins.py'; PE = D + 'test_pins.py'; IM = D + 'inv.py'; IE = D + 'test_inv.py'
    w_data = b'# Witness a\n'
    witnesses = commit({W: w_data.decode(), X: '# Witness b\n', B: '{"archive": "/external/x.tar.gz"}\n', D + 'other.json': '{}\n'}, 'handoff witnesses')
    C = witnesses.ref
    pins = ('"""Synthetic pins."""\nfrom pathlib import Path\nfrom base import ROOT\nPREFIX = Path("scripts/h62/hw/handoff")\nPINS = {\n'
            '    "a.md": (%d, "%s"),\n    "b.md": (1, "%s"),\n}\nOTHER = Path("scripts/h62/hw")\n') % (len(w_data), hashlib.sha256(w_data).hexdigest(), '0' * 64)
    test = ('import subprocess, unittest\nimport pins as p\n\n\nclass T(unittest.TestCase):\n    BASE = "%s"\n    LATER = "%s"\n\n'
            '    def test_pins(self):\n        for name in p.PINS:\n            relative = p.PREFIX / name\n'
            '            raw = subprocess.check_output(["git", "--no-replace-objects", "show", self.BASE + ":" + relative.as_posix()], cwd=p.ROOT)\n'
            '            # raw = subprocess.check_output(["git", "show", self.BASE + ":" + relative.as_posix()], cwd=p.ROOT)\n'
            '            other = subprocess.check_output(["git", "show", self.LATER + ":" + relative.as_posix()], cwd=p.ROOT)\n'
            '            self.assertTrue(raw and other)\n\n    def test_unlooped(self):\n        relative = p.OTHER / "x"\n'
            '        raw = subprocess.check_output(["git", "show", self.BASE + ":" + relative.as_posix()], cwd=p.ROOT)\n'
            '        self.assertTrue(raw)\n\n\nif __name__ == "__main__":\n    unittest.main()\n') % (C, '1' * 40)
    inv = ('"""Synthetic inventory."""\nimport json\nfrom pathlib import Path\nROOT = Path(__file__).resolve().parents[3]\n\n\n'
           'def archived(root):\n    manifest_path = root / "scripts/h62/hw/bulk.json"\n    return json.loads(manifest_path.read_text())\n\n\n'
           'def other(root):\n    path = root / "scripts/h62/hw/other.json"\n    note = "scripts/h62/hw/bulk.json"\n    return path.read_text(), note\n\n\n'
           'def never():\n    return archived(ROOT)\n\n\nif __name__ == "__main__":\n    data = archived(ROOT)\n    rest = other(ROOT)\n'
           '    # archived(ROOT)\n    print(data, rest)\n')
    inv_test = ('import importlib.util\nimport unittest\nfrom pathlib import Path\nROOT = Path(__file__).resolve().parents[3]\n'
                'spec = importlib.util.spec_from_file_location("inv", ROOT / "scripts/h62/hw/inv.py")\n'
                'inventory = importlib.util.module_from_spec(spec)\nspec.loader.exec_module(inventory)\n'
                'other = importlib.util.spec_from_file_location("inv2", ROOT / "scripts/h62/hw/pins.py")\n\n\n'
                'class T(unittest.TestCase):\n    def test_it(self):\n        self.assertTrue(inventory.archived)\n\n\n'
                'if __name__ == "__main__":\n    unittest.main()\n')
    readers = commit({PM: pins, PE: test, IM: inv, IE: inv_test}, 'handoff witness readers')
    later = commit({'tests/hw-later.txt': 'L\n'}, 'handoff witness later')
    R = readers.ref
    line = lambda text, marker: next(n for n, l in enumerate(text.splitlines(), 1) if l.lstrip().startswith(marker))
    show, main, read = line(test, 'raw = subprocess.check_output(["git", "--no'), line(inv, 'data = archived(ROOT)'), line(inv, 'return json.loads(manifest_path')
    def row(path, op, repo=readers, revision=None, **changes):
        pinned = op == 'pinned-history-show'
        e, m = (PE, PM) if pinned else (IE, IM)
        x = {'kind': HANDOFF_WITNESS_KIND, 'path': path, 'input_revision': revision or repo.ref, 'source_blob': blob(repo, path),
             'command': ['python3', '-B', e], 'operation': op,
             'entry': {'path': e, 'blob': blob(repo, e), 'import_line': 2 if pinned else 5},
             'module': {'path': m, 'blob': blob(repo, m), 'line': 6 if pinned else main},
             'read': {'path': e if pinned else m, 'line': show if pinned else read}, 'purpose': 'Synthetic handoff witness role.'}
        for k, v in changes.items(): x[k] = dict(x[k], **v) if isinstance(v, dict) and isinstance(x.get(k), dict) else v
        return x
    tuple_of = lambda x: (x['path'], x['source_blob'], x['operation'], x['entry']['path'], x['entry']['blob'], x['entry']['import_line'],
                          x['module']['path'], x['module']['blob'], x['module']['line'], x['read']['path'], x['read']['line'])
    unit = lambda path, repo=readers: {'path': path, 'input_revision': repo.ref, 'source_blob': blob(repo, path),
                                       'command': ['python3', '-B', path], 'kind': 'unittest'}
    runners = [unit(PE), unit(IE)]
    good = [row(W, 'pinned-history-show'), row(B, 'main-root-read')]
    # Variants a reviewer could list: each must still fail on the bytes (another reader, line, operation, alias or commit).
    variants = [row(W, 'pinned-history-show', read={'line': show + 1}),
                row(W, 'pinned-history-show', read={'line': line(test, 'raw = subprocess.check_output(["git", "show"')}),
                row(X, 'pinned-history-show', module={'line': 7}), row(W, 'pinned-history-show', module={'line': 7}),
                row(W, 'pinned-history-show', entry={'import_line': 1}),
                row(B, 'main-root-read', read={'line': line(inv, 'return path.read_text')}),
                row(B, 'main-root-read', module={'line': line(inv, 'rest = other(ROOT)')}),
                row(B, 'main-root-read', module={'line': line(inv, 'return archived(ROOT)')}),
                row(B, 'main-root-read', module={'line': line(inv, '# archived(ROOT)')}),
                row(B, 'main-root-read', entry={'import_line': line(inv_test, 'other = importlib')}),
                row(D + 'other.json', 'main-root-read', read={'line': line(inv, 'return path.read_text')}),
                row(W, 'main-root-read', module={'path': PM, 'blob': blob(readers, PM)}, read={'path': PM})]
    saved = HANDOFF_WITNESS_REVIEWED
    HANDOFF_WITNESS_REVIEWED = frozenset(tuple_of(x) for x in good + variants)
    try:
        base_model, base = run(later, standalone=runners)
        assert all(base[q]['class'] != 'keep' for q in (W, X, B))
        for repo in (readers, later):
            model, rows = run(repo, standalone=runners + good)
            for x in good:
                p = x['path']; e = model['entry_points'][HANDOFF_WITNESS_PREFIX + p]
                assert rows[p]['class'] == 'keep' and rows[p]['runner_chain']['edges'] == [], p
                assert e['source_only'] and e['handoff_witness_role'] and e['validation_at_measured_revision']['status'] == 'unavailable'
                assert e['location'] == x['read']['path'] + ':' + str(x['read']['line']) and e['interface']['operation'] == x['operation']
                assert e['command'] != shlex.join(['python3', '-B', p]) and e.get('pinned_commit', C) == C
            if repo is later:  # source-only: no other record changes and no other root appears
                assert all(canonical(v) == canonical(base[q]) for q, v in rows.items() if q not in (W, B))
                assert set(model['entry_points']) - set(base_model['entry_points']) == {HANDOFF_WITNESS_PREFIX + q for q in (W, B)}
        for x in variants: rejected(readers, 'does not perform its operation', standalone=runners + [x])
        # The other loop read names a commit (LATER) that is not the reviewed pinned one: refused by the commit check.
        later_read = row(W, 'pinned-history-show', read={'line': show + 2})
        HANDOFF_WITNESS_REVIEWED = HANDOFF_WITNESS_REVIEWED | {tuple_of(later_read)}
        rejected(readers, 'pinned commit does not hold the witness blob', standalone=runners + [later_read])
        # Unreviewed: another blob, reader, line, operation, entry or module, and the real table on synthetic rows.
        for change in ({'source_blob': blob(readers, X)}, {'read': {'line': show + 3}},
                       {'entry': {'import_line': 3}}, {'module': {'line': 5}}):
            rejected(readers, 'unreviewed handoff witness role', standalone=runners + [row(W, 'pinned-history-show', **change)])
        rejected(readers, 'unsupported handoff witness role invocation', standalone=runners + [row(W, 'pinned-history-show', command=['python3', '-B', IE])])
        rejected(readers, 'unsupported handoff witness role invocation', standalone=runners + [row(W, 'pinned-history-show', read={'path': PM})])
        rejected(readers, 'unsupported handoff witness role invocation', standalone=runners + [row(W, 'other-operation')])
        rejected(readers, 'unsupported handoff witness role invocation', standalone=runners + [row(W, 'pinned-history-show', operation='main-root-read')])
        rejected(readers, 'invalid handoff witness role definition', standalone=runners + [dict(good[0], extra=1)])
        rejected(readers, 'invalid handoff witness role definition', standalone=runners + [row(W, 'pinned-history-show', purpose=' ')])
        rejected(readers, 'invalid handoff witness role definition', standalone=runners + [row(W, 'pinned-history-show', read={'line': True})])
        rejected(readers, 'invalid handoff witness role definition', standalone=runners + [row(W, 'pinned-history-show', entry={'extra': 1})])
        rejected(readers, 'full commit revision', standalone=runners + [row(W, 'pinned-history-show', revision=R[:12])])
        rejected(readers, 'conflicting standalone definitions', standalone=runners + [good[0], dict(good[0], purpose='Other.')])
        # The entry identity: without its python3 -B entry root a current row is refused and a historical one is stale.
        rejected(readers, 'not a python3 -B entry root', standalone=[runners[1], good[0]])
        model, rows = run(later, standalone=[runners[1]] + good)
        assert HANDOFF_WITNESS_PREFIX + W not in model['entry_points'] and rows[W]['class'] != 'keep' and rows[B]['class'] == 'keep'
        # A changed witness, entry or module blob: stale later, refused when claimed now.
        for changes in ({W: '# Witness a changed\n'}, {PE: test + '# changed\n'}, {PM: pins + '# changed\n'}, {B: '{}\n'}, {IM: inv + '# changed\n'}):
            edited = commit(changes, 'handoff witness edited')
            model, rows = run(edited, standalone=[unit(PE, edited), unit(IE, edited)] + good)
            for x in good:
                touched = bool({x['path'], x['entry']['path'], x['module']['path']} & set(changes))
                assert (HANDOFF_WITNESS_PREFIX + x['path'] in model['entry_points']) != touched, (changes, x['path'])
            rejected(edited, 'source mismatch', standalone=[unit(PE, edited), unit(IE, edited)] + [dict(x, input_revision=edited.ref) for x in good
                     if {x['path'], x['entry']['path'], x['module']['path']} & set(changes)])
            commit({k: {W: w_data.decode(), PE: test, PM: pins, B: '{"archive": "/external/x.tar.gz"}\n', IM: inv}[k] for k in changes}, 'handoff witness restored')
        # The pinned commit must hold the witness blob and be an ancestor: a BASE naming another commit is refused.
        tree = git(root, 'rev-parse', C + '^{tree}').decode().strip()
        orphan = git(root, '-c', 'user.name=Control', '-c', 'user.email=control@example.invalid', 'commit-tree', tree, '-m', 'orphan').decode().strip()
        for base_commit in (git(root, 'rev-parse', C + '^').decode().strip(), orphan, 'f' * 40):  # without W, no ancestor, unknown
            moved = test.replace(C, base_commit)
            other = commit({PE: moved}, 'handoff witness moved base')
            x = row(W, 'pinned-history-show', repo=other)
            HANDOFF_WITNESS_REVIEWED = HANDOFF_WITNESS_REVIEWED | {tuple_of(x)}
            rejected(other, 'pinned commit does not hold the witness blob', standalone=[unit(PE, other), unit(IE, other), x])
        commit({PE: test}, 'handoff witness base restored')
        # A rebound alias, PINS, root or __main__ guard names nothing.
        for tail, path, x in (('p = None\n', PE, good[0]), ('PINS = {}\n', PM, good[0]), ('ROOT = None\n', IM, good[1]),
                              ('__name__ = "__main__"\n', IM, good[1]), ('spec = None\n', IE, good[1])):
            rebound = commit({path: {PE: test, PM: pins, IM: inv, IE: inv_test}[path] + tail}, 'handoff witness rebound')
            y = row(x['path'], x['operation'], repo=rebound)
            HANDOFF_WITNESS_REVIEWED = HANDOFF_WITNESS_REVIEWED | {tuple_of(y)}
            rejected(rebound, 'does not perform its operation', standalone=[unit(PE, rebound), unit(IE, rebound), y])
            commit({path: {PE: test, PM: pins, IM: inv, IE: inv_test}[path]}, 'handoff witness rebound restored')
        # A current definition of the path supersedes a historical one, in either order.
        now = dict(good[0], input_revision=later.ref, purpose='Now.')
        for order in (1, -1):
            model, _ = run(later, standalone=runners + [good[0], now][::order])
            assert model['entry_points'][HANDOFF_WITNESS_PREFIX + W]['purpose'] == 'Now.'
        HANDOFF_WITNESS_REVIEWED = saved
        rejected(readers, 'unreviewed handoff witness role', standalone=runners + [good[0]])
    finally:
        HANDOFF_WITNESS_REVIEWED = saved
        git(root, 'rm', '-q', '-r', '--ignore-unmatch', '--', D, 'tests/hw-later.txt')
        git(root, '-c', 'user.name=Control', '-c', 'user.email=control@example.invalid', 'commit', '-qm', 'handoff witnesses removed')


_hw_shared('register_source_role')(HANDOFF_WITNESS_KIND, handoff_witness_root, late=True)
_hw_shared('FORM_CONTROLS').append(handoff_witness_controls)
