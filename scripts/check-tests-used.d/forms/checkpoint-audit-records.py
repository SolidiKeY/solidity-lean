# H1075 (gh#1428) census form: historical checkpoint audit record. Exec'd by registry.py in the namespace of
# fragments.py (see registry.py's header); it registers one standalone kind and one control and binds no shared name.
# Opt-in: without a standalone row of this kind every classification and output byte is unchanged.
#
# A row records that a validator and the audit it invokes were run unchanged in a detached checkout at a recorded
# checkpoint commit (never the measured revision), and credits only historical provenance of exact blobs at that
# commit. It creates one source-only root for the target path and nothing else: no current-revision validation,
# execution, pass, read anchor, fixture, child, output, proof or runtime credit. Row shape (all keys required):
#   {'kind': 'checkpoint-audit-record', 'path': P, 'input_revision': C (the checkpoint), 'source_blob': blob of P,
#    'command': ['python3', '-B', V], 'validator': {'path': V, 'blob', 'entry_line', 'invocation_line'},
#    'audit': {'path': A, 'blob'}, 'provenance': {'reader': V or A, 'line'}, 'purpose': text}
# P is V (provenance: V at its entry line), A (V at its invocation line) or a path read by V or A at the line.
import ast
import shlex

CHECKPOINT_AUDIT_KIND = 'checkpoint-audit-record'
CHECKPOINT_AUDIT_PREFIX = 'checkpoint-audit:'
_CHECKPOINT_RUNS = ('run', 'call', 'check_call', 'check_output')
_CHECKPOINT_READS = ('read_text', 'read_bytes')


def _checkpoint_shared(name):
    """A name of the fragments.py namespace this module is exec'd in."""
    return globals()[name]


def _checkpoint_tree(text):
    try: return ast.parse(text)
    except (SyntaxError, ValueError, RecursionError): return None


def _checkpoint_bound(tree, name):
    """The value of a unique module-level `name = value` assignment, else None."""
    values = [node.value for node in tree.body if isinstance(node, ast.Assign) and len(node.targets) == 1
              and isinstance(node.targets[0], ast.Name) and node.targets[0].id == name]
    rebound = [node for node in ast.walk(tree) if isinstance(node, (ast.Name, ast.arg)) and getattr(node, 'id', getattr(node, 'arg', None)) == name
               and isinstance(getattr(node, 'ctx', ast.Store()), (ast.Store, ast.Del))]
    return values[0] if len(values) == 1 and len(rebound) == 1 else None


def _checkpoint_string(tree, node):
    """A string literal, or a name bound once at module level to one."""
    if isinstance(node, ast.Name): node = _checkpoint_bound(tree, node.id)
    return node.value if isinstance(node, ast.Constant) and isinstance(node.value, str) else None


def _checkpoint_root(tree, node, reader):
    """True iff node is a name bound once to Path(__file__).resolve().parents[k], the repository root of reader."""
    value = _checkpoint_bound(tree, node.id) if isinstance(node, ast.Name) else None
    if not (isinstance(value, ast.Subscript) and isinstance(value.slice, ast.Constant) and type(value.slice.value) is int
            and value.slice.value == reader.count('/') and isinstance(value.value, ast.Attribute) and value.value.attr == 'parents'):
        return False
    resolve = value.value.value
    if not (isinstance(resolve, ast.Call) and not resolve.args and not resolve.keywords and isinstance(resolve.func, ast.Attribute)
            and resolve.func.attr == 'resolve'):
        return False
    path = resolve.func.value
    if not (isinstance(path, ast.Call) and len(path.args) == 1 and not path.keywords and isinstance(path.args[0], ast.Name)
            and path.args[0].id == '__file__'):
        return False
    func = path.func
    return (isinstance(func, ast.Name) and func.id == 'Path' or isinstance(func, ast.Attribute) and func.attr == 'Path'
            and isinstance(func.value, ast.Name) and func.value.id == 'pathlib')


def checkpoint_invocation(text, audit, line):
    """True iff line holds subprocess.<run>(['python3', audit], ...) of the audit, as a literal argument list."""
    tree = _checkpoint_tree(text)
    if tree is None: return False
    for node in ast.walk(tree):
        if (isinstance(node, ast.Call) and node.lineno == line and isinstance(node.func, ast.Attribute) and node.func.attr in _CHECKPOINT_RUNS
                and isinstance(node.func.value, ast.Name) and node.func.value.id == 'subprocess' and node.args
                and isinstance(node.args[0], ast.List)):
            words = [_checkpoint_string(tree, e) if isinstance(e, ast.Constant) else None for e in node.args[0].elts]
            if words in (['python3', audit], ['python3', '-B', audit]): return True
    return False


def checkpoint_read(text, reader, target, line):
    """True iff line holds (ROOT / target).read_text() or .read_bytes(), ROOT the repository root of reader."""
    tree = _checkpoint_tree(text)
    if tree is None: return False
    for node in ast.walk(tree):
        if (isinstance(node, ast.Call) and node.lineno == line and not node.args and not node.keywords
                and isinstance(node.func, ast.Attribute) and node.func.attr in _CHECKPOINT_READS
                and isinstance(node.func.value, ast.BinOp) and isinstance(node.func.value.op, ast.Div)
                and _checkpoint_string(tree, node.func.value.right) == target and _checkpoint_root(tree, node.func.value.left, reader)):
            return True
    return False


def checkpoint_audit_root(classifier, graph, catalog, entry):
    """H1075: a historical checkpoint audit record as a source-only root of its target.

    The checkpoint C is a full commit, a strict ancestor of the measured
    revision and never the measured revision itself; the target, validator and
    audit blobs are those paths' objects both at C and now (a changed blob makes
    the record stale; a blob C does not hold is an error). The validator has its
    top-level default entry and literally invokes the audit; the target is the
    validator, the audit, or a literal repository-root read of either. Neither
    is run here: historical provenance only, never a validated runner.
    """
    repo = graph.repo; role = 'checkpoint audit record'
    required = {'path', 'input_revision', 'source_blob', 'command', 'kind', 'validator', 'audit', 'provenance', 'purpose'}
    v, a, doc = entry.get('validator'), entry.get('audit'), entry.get('provenance')
    if (set(entry) != required or not all(isinstance(entry[k], str) for k in ('path', 'source_blob', 'purpose')) or not entry['purpose'].strip()
            or not isinstance(v, dict) or set(v) != {'path', 'blob', 'entry_line', 'invocation_line'} or not isinstance(a, dict)
            or set(a) != {'path', 'blob'} or not isinstance(doc, dict) or set(doc) != {'reader', 'line'}
            or not all(isinstance(x[k], str) for x in (v, a) for k in ('path', 'blob')) or not isinstance(doc['reader'], str)
            or not all(type(n) is int for n in (v['entry_line'], v['invocation_line'], doc['line']))):
        raise ValueError('invalid ' + role + ' definition')
    p = entry['path']; checkpoint = entry['input_revision']; blob = entry['source_blob']
    if not isinstance(checkpoint, str) or not classifier['hex_pin'](checkpoint, 40): raise ValueError(role + ' requires a full checkpoint commit')
    if checkpoint == repo.ref: raise ValueError(role + ' checkpoint is the measured revision, not a historical checkpoint: ' + p)
    if any(e is not entry and e.get('kind') == CHECKPOINT_AUDIT_KIND and e.get('path') == p and e.get('input_revision') == checkpoint
           for e in catalog['standalone']):
        raise ValueError('conflicting standalone definitions: ' + p)
    paths = (v['path'], a['path'])
    if (entry['command'] != ['python3', '-B', v['path']] or len(set(paths)) != 2 or not all(q.endswith('.py') for q in paths)
            or doc['reader'] not in paths or not p.startswith(classifier['SCOPE']) or _checkpoint_shared('_clean')(p) != p):
        raise ValueError('unsupported ' + role + ' invocation: ' + p)
    pins = sorted({(p, blob), (v['path'], v['blob']), (a['path'], a['blob'])})
    if len({q for q, _ in pins}) != len(pins): raise ValueError('inconsistent ' + role + ' blobs: ' + p)
    # Stale (superseded or a changed blob) grants nothing; a blob the checkpoint does not hold is an error.
    if not _checkpoint_shared('_role_current')(classifier, repo, catalog, entry, pins): return
    try: classifier['git'](repo.root, 'merge-base', '--is-ancestor', checkpoint, repo.ref)
    except ValueError: raise ValueError(role + ' checkpoint is not an ancestor of the measured revision: ' + checkpoint) from None
    if not all(q in repo.texts for q in paths): raise ValueError('unsupported ' + role + ' invocation: ' + p)
    try: entries = classifier['entrypoint_lines'](repo.bytes(v['path']))
    except (SyntaxError, ValueError, RecursionError): entries = set()
    if v['entry_line'] not in entries: raise ValueError(role + ' validator lacks its default top-level entry: ' + v['path'])
    if not checkpoint_invocation(repo.texts[v['path']], a['path'], v['invocation_line']):
        raise ValueError(role + ' validator does not invoke its audit: ' + v['path'])
    reader, line = doc['reader'], doc['line']
    if p == v['path']: held = reader == p and line == v['entry_line']
    elif p == a['path']: held = reader == v['path'] and line == v['invocation_line']
    else: held = checkpoint_read(repo.texts[reader], reader, p, line)
    if not held: raise ValueError(role + ' provenance does not name its target: ' + reader + ':' + str(line))
    identity = CHECKPOINT_AUDIT_PREFIX + p + '@' + checkpoint
    graph.root(p, 'historical checkpoint audit record', shlex.join(entry['command']), reader, line, root_id=identity)
    if identity not in graph.roots: return
    graph.roots[identity].update({'source_only': True, 'checkpoint_audit_record': True, 'source_blob': blob, 'purpose': entry['purpose'],
        'program_role': CHECKPOINT_AUDIT_KIND, 'checkpoint': checkpoint, 'validator': v, 'audit': a, 'provenance': doc,
        'source_declaration_revision': checkpoint,
        'validation_at_measured_revision': {'status': 'unavailable', 'command': entry['command'],
            'reason': 'Historical checkpoint audit record: the validator and audit ran unchanged in a detached checkout at the recorded checkpoint, '
                      'not at the measured revision. Historical provenance of the exact blobs only: no current-revision validation, execution, '
                      'pass, read anchor, fixture, child, output, proof or runtime credit.'}})


def checkpoint_audit_controls(env):
    """H1075 controls, run by successor_controls with its helpers: the record
    form at a later revision, and stale or rejected records (changed blob,
    wrong commit, checkpoint that is not an ancestor, the measured revision,
    comment/string/foreign-root lines, wrong command, reader or schema)."""
    commit, run, rejected, blob, classifier, root = (env[k] for k in ('commit', 'run', 'rejected', 'blob', 'classifier', 'root'))
    git = classifier['git']; canonical = _checkpoint_shared('canonical')
    D = 'scripts/h62/cpa/'; V = D + 'validate.py'; A = 'tests/cpa/audit.py'; T = 'tests/cpa/pin.json'; O = 'tests/cpa/other.json'
    validator = ('"""Synthetic validator."""\nimport pathlib, subprocess\nROOT = pathlib.Path(__file__).resolve().parents[3]\n'
                 "PIN = 'tests/cpa/pin.json'\ndef scope():\n    data = (ROOT / PIN).read_text()\n"
                 "    # subprocess.run(['python3', 'tests/cpa/audit.py'])\n"
                 "    subprocess.run(['python3', 'tests/cpa/audit.py'], cwd=ROOT, check=True)\n    return data\n"
                 "if __name__ == '__main__':\n    scope()\ndef other():\n    subprocess.run(['python3', 'tests/cpa/other.py'])\n")
    audit = ('"""Synthetic audit."""\nimport json, pathlib\nroot = pathlib.Path(__file__).resolve().parents[2]\n'
             "pin = json.loads((root / 'tests/cpa/pin.json').read_text())\n"
             "other = (root.parent / 'tests/cpa/other.json').read_text()\nnote = 'tests/cpa/other.json'\n"
             "# (root / 'tests/cpa/other.json').read_text()\nprint(pin, other)\n")
    added = {V: validator, A: audit, T: '{"commit": "x"}\n', O: '{}\n'}
    before = commit({'tests/cpa-before.txt': 'B\n'}, 'checkpoint audit before'); C = commit(added, 'checkpoint audit').ref
    later = commit({'tests/cpa-later.txt': 'L\n'}, 'checkpoint audit later')
    after = commit({'tests/cpa-after.txt': 'A\n'}, 'checkpoint audit after')  # a descendant of later
    entry_line = max(classifier['entrypoint_lines'](validator.encode()))
    def record(path, reader, line, repo=later, checkpoint=C, **changes):
        row = {'kind': CHECKPOINT_AUDIT_KIND, 'path': path, 'input_revision': checkpoint, 'source_blob': blob(repo, path),
               'command': ['python3', '-B', V], 'audit': {'path': A, 'blob': blob(repo, A)},
               'validator': {'path': V, 'blob': blob(repo, V), 'entry_line': entry_line, 'invocation_line': 8},
               'provenance': {'reader': reader, 'line': line}, 'purpose': 'Synthetic checkpoint audit record.'}
        row.update(changes); return row
    try:
        assert CHECKPOINT_AUDIT_KIND in _checkpoint_shared('SOURCE_ROLE_KINDS') and CHECKPOINT_AUDIT_KIND not in _checkpoint_shared('LATE_SOURCE_ROLE_KINDS')
        base_model, base = run(later)
        assert all(base[q]['class'] != 'keep' for q in (T, O))
        positives = ((T, V, 6), (T, A, 4), (A, V, 8), (V, V, entry_line))
        for path, reader, line in positives:
            model, rows = run(later, standalone=[record(path, reader, line)])
            root_row = model['entry_points'][CHECKPOINT_AUDIT_PREFIX + path + '@' + C]
            assert rows[path]['class'] == 'keep' and rows[path]['runner_chain']['edges'] == [], path
            assert root_row['source_only'] and root_row['validation_at_measured_revision']['status'] == 'unavailable'
            assert root_row['location'] == reader + ':' + str(line) and root_row['checkpoint'] == C
            # Source-only provenance of the one target: no other record changes and no other root appears.
            assert all(canonical(r) == canonical(base[q]) for q, r in rows.items() if q != path), path
            assert set(model['entry_points']) - set(base_model['entry_points']) == {CHECKPOINT_AUDIT_PREFIX + path + '@' + C}
        good = record(T, A, 4)
        # A changed target, audit or validator blob makes the record stale: nothing is credited.
        changed = commit({T: '{"commit": "y"}\n'}, 'checkpoint audit changed pin')
        _, rows = run(changed, standalone=[good]); assert rows[T]['class'] != 'keep'
        moved = commit({T: added[T], A: audit + '# changed\n'}, 'checkpoint audit changed audit')
        _, rows = run(moved, standalone=[good]); assert rows[T]['class'] != 'keep'
        # The current blobs claimed at a checkpoint that held other blobs, a wrong or unknown commit: rejected.
        rejected(moved, 'unverifiable historical', standalone=[record(T, A, 4, repo=moved)])
        rejected(later, 'unverifiable historical', standalone=[record(T, A, 4, checkpoint=before.ref)])
        rejected(later, 'unverifiable historical', standalone=[record(T, A, 4, checkpoint='f' * 40)])
        rejected(later, 'full checkpoint commit', standalone=[record(T, A, 4, checkpoint=C[:12])])
        # A checkpoint holding the same blobs that is not an ancestor of the measured revision.
        tree = git(root, 'rev-parse', C + '^{tree}').decode().strip()
        orphan = git(root, '-c', 'user.name=Control', '-c', 'user.email=control@example.invalid', 'commit-tree', tree, '-m', 'orphan').decode().strip()
        rejected(later, 'not an ancestor', standalone=[record(T, A, 4, checkpoint=orphan)])
        # A descendant checkpoint holding the same blobs, and the measured revision itself.
        rejected(later, 'not an ancestor', standalone=[record(T, A, 4, checkpoint=after.ref)])
        rejected(later, 'not a historical checkpoint', standalone=[record(T, A, 4, checkpoint=later.ref)])
        # Provenance lines: commented invocation, string-only path, foreign root, commented read, wrong reader.
        for line in (7, 13):  # a commented invocation, another program's
            rejected(later, 'does not invoke its audit', standalone=[record(T, A, 4, validator=dict(good['validator'], invocation_line=line))])
        rejected(later, 'lacks its default top-level entry', standalone=[record(T, A, 4, validator=dict(good['validator'], entry_line=6))])
        for path, reader, line in ((O, A, 5), (O, A, 6), (O, A, 7), (T, V, 7), (T, A, 5), (A, A, 8), (V, A, entry_line)):
            rejected(later, 'does not name its target', standalone=[record(path, reader, line)])
        rejected(later, 'unsupported checkpoint audit record invocation', standalone=[record(T, A, 4, command=['python3', '-B', A])])
        rejected(later, 'unsupported checkpoint audit record invocation', standalone=[record(T, 'tests/cpa/x.py', 4)])
        rejected(later, 'invalid checkpoint audit record definition', standalone=[dict(good, entry_line=4)])
        rejected(later, 'invalid checkpoint audit record definition', standalone=[record(T, A, 4, purpose=' ')])
        rejected(later, 'conflicting standalone definitions', standalone=[good, dict(good, purpose='Other.')])
    finally:
        git(root, 'rm', '-q', '-r', '--ignore-unmatch', '--', D, 'tests/cpa', 'tests/cpa-before.txt', 'tests/cpa-later.txt', 'tests/cpa-after.txt')
        git(root, '-c', 'user.name=Control', '-c', 'user.email=control@example.invalid', 'commit', '-qm', 'checkpoint audit removed')


_checkpoint_shared('register_source_role')(CHECKPOINT_AUDIT_KIND, checkpoint_audit_root)
_checkpoint_shared('FORM_CONTROLS').append(checkpoint_audit_controls)
