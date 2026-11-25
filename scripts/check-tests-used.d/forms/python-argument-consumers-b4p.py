# H1234 (gh#1544, Q-X1ERR-7, Option C), form (3): reads of an argument-bearing
# Python consumer (B4p) observed in a demonstrated passing run with an exact,
# all-literal argv. consumer_routes section python_argument_consumer_reads:
#   {runner: R, input_revision: D, command: [python3, -B, P, ARG...],
#    frames: [{path: P, blob, line}, ...], target, target_blob, operation:
#    PYC_OPERATION, purpose}
# R names P's existing source root (committed:P, validated:P or the H996
# py-args:P role, whichever the measured model holds); it must be current,
# not derived, with source blob = the P frame blob. The command is never a
# certified validation of R: the review records that `command` (only literal
# arguments, no off-Git input or output) passed in a clean scratch checkout at
# D, ordinary and under the official tracer (scripts/check-tests-used-trace.py:
# Python open stacks intersected with strace reads), that the tracer observed
# the read with exactly these frames (outermost first), and that the run left
# the checkout byte-identical. Re-derived from the measured bytes: every frame
# is in P, frames[0] lies in P's one top-level `if __name__ == "__main__":`
# block, each later frame lies in a uniquely named function that the previous
# frame line calls, and the last frame line names a read (read_bytes/read_text/open/
# tarfile.open). Opt-in twice by exact tuple: the run (P, blob, D, command) in
# REVIEWED_PY_ARG_CONSUMER_RUNS and the read (P, command, frames, target, target
# blob) in REVIEWED_PY_ARG_CONSUMER_READS; anything else is rejected. At any
# measured --ref a row credits its target alone (frames are provenance, H1108)
# while P, every frame and the target are the same blobs now and at D (stale
# otherwise: no credit, no error). Consumption credit only: no validation,
# argument, pass, output, generated-file, helper, child, proof or runtime
# credit; R is unchanged, and no other path P reads or writes is credited.
# Reviewed on master abec4d99 from x1e-classify-rest-rest's B4p list (02e437a0).
# Admitted (3): `python3 -B tests/terra-20261103/gate/freeze_acceptance.py
# inventory` (exit 0; rewrites old_to_new.json byte-identically) reads
# gate/history/tf-gate-9cc85b14.tar.gz (archive(), line 39), gate/test_cases.py
# (inventory(), line 75) and gate/test_contract.py (inventory(), line 98).
# Refused, left unresolved (68): old_to_new.json (written, not read: a
# generator output, not a consumer read) and every other B4p path, whose
# consumers need off-Git inputs or outputs (archives, gate/build logs, --report,
# --evidence, --head commits, /workspace paths), fail on deleted evidence or a
# moved writer lock, fail as unittests, or rewrite the target differently
# (refresh-audit.py inventory rewrites audit-runs.json); none has an all-literal
# argv that passes read-only here. Details in the H1234 result.
import ast, hashlib
(FORM_CONTROLS, PYTHON_ARGS_PREFIX, _check_lines, _frames_current, _historical_objects, canonical, register_consumer_section) = (
    globals()[name] for name in ('FORM_CONTROLS', 'PYTHON_ARGS_PREFIX', '_check_lines', '_frames_current', '_historical_objects',
                                 'canonical', 'register_consumer_section'))
PYC_SECTION = 'python_argument_consumer_reads'
PYC_OPERATION = 'blob-bound persisted read observed in a demonstrated passing run of a reviewed argument-bearing Python consumer with a literal argv'
PYC_HOP = 'Python call stack of the demonstrated run'
_PYC_P = 'tests/terra-20261103/gate/freeze_acceptance.py'
_PYC_BLOB = '88c5bfb3260b9617024ed76686d5a7bd0ba9080a'
_PYC_REVISION = 'abec4d99f58359480428d46e832ade9db3f0fc62'
_PYC_COMMAND = ('python3', '-B', _PYC_P, 'inventory')
# (program, blob, demonstration revision, command)
REVIEWED_PY_ARG_CONSUMER_RUNS = frozenset({(_PYC_P, _PYC_BLOB, _PYC_REVISION, _PYC_COMMAND)})
# (program, command, ((frame path, blob, line), ...), target, target blob)
REVIEWED_PY_ARG_CONSUMER_READS = frozenset(
    (_PYC_P, _PYC_COMMAND, tuple((_PYC_P, _PYC_BLOB, n) for n in lines), 'tests/terra-20261103/gate/' + t, b) for lines, t, b in (
        ((257, 75, 39), 'history/tf-gate-9cc85b14.tar.gz', '4c5e3bad971c6298f844afaac5b8407d40957af6'),
        ((257, 75), 'test_cases.py', '8f827f78831c67e9e163996cd1f67a6ec119c952'),
        ((257, 98), 'test_contract.py', 'b54ee31dbcf355f5d28aadde553014ee30333206')))
_PYC_READ = re.compile(r'\.read_bytes\(|\.read_text\(|(?<![\w.])open\(|\btarfile\.open\(')


def pyc_main_lines(text):
    """Line span (first, last) of the body of the one top-level `if __name__ == "__main__":`, else None."""
    try: tree = ast.parse(text)
    except (SyntaxError, ValueError, RecursionError): return None
    mains = [n for n in tree.body if isinstance(n, ast.If) and not n.orelse and isinstance(n.test, ast.Compare)
             and isinstance(n.test.left, ast.Name) and n.test.left.id == '__name__' and len(n.test.ops) == 1
             and isinstance(n.test.ops[0], ast.Eq) and len(n.test.comparators) == 1
             and isinstance(n.test.comparators[0], ast.Constant) and n.test.comparators[0].value == '__main__']
    return (mains[0].body[0].lineno, mains[0].end_lineno) if len(mains) == 1 else None


def pyc_calls_chain(text, lines):
    """Each later frame line lies in a function whose name the previous frame line calls."""
    try: tree = ast.parse(text)
    except (SyntaxError, ValueError, RecursionError): return False
    functions = [n for n in ast.walk(tree) if isinstance(n, (ast.FunctionDef, ast.AsyncFunctionDef))]
    source = text.split('\n')
    for caller, callee in zip(lines, lines[1:]):
        enclosing = [n for n in functions if n.lineno <= callee <= n.end_lineno]
        if not enclosing: return False
        name = max(enclosing, key=lambda n: n.lineno).name
        if sum(n.name == name for n in functions) != 1 or not re.search(r'(?<![\w.])' + re.escape(name) + r'\s*\(', source[caller - 1]): return False
    return True


def python_argument_consumer_reads(classifier, graph, rows, runs=None, reads=None):
    """H1234 (3): exact reads observed in a demonstrated literal-argv run of a Python consumer."""
    repo = graph.repo
    runs = REVIEWED_PY_ARG_CONSUMER_RUNS if runs is None else runs
    reads = REVIEWED_PY_ARG_CONSUMER_READS if reads is None else reads
    for row in rows:
        if (not isinstance(row, dict) or set(row) != {'runner', 'input_revision', 'command', 'frames', 'target', 'target_blob', 'operation', 'purpose'}
                or row['operation'] != PYC_OPERATION or not isinstance(row['runner'], str) or not isinstance(row['command'], list)
                or not all(isinstance(a, str) for a in row['command']) or not isinstance(row['target'], str) or not isinstance(row['target_blob'], str)
                or not isinstance(row['purpose'], str) or not row['purpose'].strip() or not isinstance(row['input_revision'], str)):
            raise ValueError('invalid Python argument consumer read route')
        frames = row['frames']; target = row['target']; command = tuple(row['command'])
        prefix, _, p = row['runner'].partition(':')
        if prefix + ':' not in ('committed:', 'validated:', PYTHON_ARGS_PREFIX) or command[:3] != ('python3', '-B', p):
            raise ValueError('invalid Python argument consumer read route')
        if not _frames_current(repo, frames, [(target, row['target_blob'])]): continue
        if any(f['path'] != p for f in frames): raise ValueError('Python argument consumer read frames leave the program')
        if (p, command, tuple((f['path'], f['blob'], f['line']) for f in frames), target, row['target_blob']) not in reads:
            raise ValueError('unreviewed Python argument consumer read: ' + p)
        if (p, frames[0]['blob'], row['input_revision'], command) not in runs:
            raise ValueError('Python argument consumer read lacks its demonstrated run: ' + p)
        roots = [graph.roots[k] for k in ('validated:' + p, 'committed:' + p, PYTHON_ARGS_PREFIX + p) if k in graph.roots]
        if row['runner'] not in graph.roots or graph.roots[row['runner']] is not (roots[0] if roots else None): continue
        root = roots[0]
        if 'derived_from' in root or root.get('path') != p or root.get('source_blob') != frames[0]['blob']: continue
        _check_lines(repo, frames)
        text = repo.texts[p]; span = pyc_main_lines(text); lines = text.split('\n')
        if (span is None or not span[0] <= frames[0]['line'] <= span[1] or not _PYC_READ.search(lines[frames[-1]['line'] - 1])
                or not pyc_calls_chain(text, [f['line'] for f in frames])):
            raise ValueError('Python argument consumer read is not a main-block call stack ending at a read')
        if classifier['excluded'](target) or classifier['excluded'](p): continue
        if not _historical_objects(classifier, repo, row['input_revision'], sorted({(p, frames[0]['blob']), (target, row['target_blob'])})): continue
        details = {'kind': 'python-argument-consumer-read', 'purpose': row['purpose'], 'demonstration_revision': row['input_revision'],
                   'demonstrated_command': list(command)}
        identity = row['runner'] + ':' + details['kind'] + ':' + hashlib.sha256(canonical(row)).hexdigest()
        graph.roots[identity] = {**root, 'derived_from': row['runner'], 'observed_target': target, 'consumer_route': details}
        edges = [{'source': a['path'], 'target': b['path'], 'line': a['line'], 'operation': PYC_HOP, 'kind': 'executes', 'validated_for': identity}
                 for a, b in zip(frames, frames[1:])]
        edges.append({'source': p, 'target': target, 'line': frames[-1]['line'], 'operation': PYC_OPERATION, 'kind': 'consumes', 'validated_for': identity})
        graph.observed.append((target, {'root': identity, 'entry': graph.roots[identity], 'edges': edges}))  # the target alone (H1108)


register_consumer_section(PYC_SECTION, ('runner', 'input_revision', 'target', 'frames'), True,
                          lambda c, g, _, rows: python_argument_consumer_reads(c, g, rows))


def python_argument_consumer_controls(env):
    """H1234 (3) controls: the reviewed tables, a synthetic H996 consumer whose
    observed read is credited only with both reviews, and the refused shapes."""
    global REVIEWED_PY_ARG_CONSUMER_RUNS, REVIEWED_PY_ARG_CONSUMER_READS, REVIEWED_PYTHON_ARGS
    commit, run, rejected, blob = (env[k] for k in ('commit', 'run', 'rejected', 'blob'))
    assert len(REVIEWED_PY_ARG_CONSUMER_RUNS) == 1 and len(REVIEWED_PY_ARG_CONSUMER_READS) == 3
    assert all(r[0] == _PYC_P and r[1] == _PYC_COMMAND and r[2][0][2] == 257 for r in REVIEWED_PY_ARG_CONSUMER_READS)
    P = 'tests/pyc/consume.py'
    program = ('import sys\nfrom pathlib import Path\nHERE = Path(__file__).resolve().parent\n'
               'def inventory():\n    data = (HERE / "data.txt").read_text()\n    print(len(data))\n'
               'def other():\n    return (HERE / "other.txt").read_text()\n'
               'if __name__ == "__main__":\n    assert sys.argv[1:] in (["inventory"],), "usage"\n    inventory()\n')
    assert pyc_main_lines(program) == (10, 11) and pyc_main_lines(program.replace('if __name__', 'if True or __name__')) is None
    assert pyc_main_lines(program + 'if __name__ == "__main__":\n    pass\n') is None
    pc = commit({P: program, 'tests/pyc/data.txt': 'data\n', 'tests/pyc/other.txt': 'other\n'}, 'python argument consumer'); D = pc.ref
    pl = commit({'tests/unrelated.txt': 'pyc later\n'}, 'python argument consumer later')
    interface = python_argument_interface(program); assert interface is not None
    role = {'path': P, 'input_revision': D, 'source_blob': blob(pc, P), 'kind': PYTHON_ARGS_KIND, 'command': ['python3', '-B', P], 'entry_line': 9,
            'interface': interface, 'provenance': {'commit': D, 'path': P, 'blob': blob(pc, P)}, 'purpose': 'Synthetic argument-bearing consumer.'}
    T = 'tests/pyc/data.txt'; cmd = ['python3', '-B', P, 'inventory']
    def row(lines=(11, 5), target=T, **k):
        return dict({'runner': PYTHON_ARGS_PREFIX + P, 'input_revision': D, 'command': cmd, 'frames': [{'path': P, 'blob': blob(pc, P), 'line': n} for n in lines],
                     'target': target, 'target_blob': blob(pc, target), 'operation': PYC_OPERATION, 'purpose': 'Synthetic consumer read.'}, **k)
    key = lambda r: (P, tuple(r['command']), tuple((f['path'], f['blob'], f['line']) for f in r['frames']), r['target'], r['target_blob'])
    reads = lambda *rows: {PYC_SECTION: list(rows)}
    saved = REVIEWED_PY_ARG_CONSUMER_RUNS, REVIEWED_PY_ARG_CONSUMER_READS, REVIEWED_PYTHON_ARGS
    REVIEWED_PYTHON_ARGS = REVIEWED_PYTHON_ARGS | {(P, blob(pc, P), D)}
    try:
        base = run(pl, standalone=[role])[1]; assert base[T]['class'] != 'keep'
        rejected(pl, 'unreviewed Python argument consumer read', reads(row()), standalone=[role])
        bad = [row((9, 5)), row((11, 4)), row((8,), "tests/pyc/other.txt"), row((11, 8), "tests/pyc/other.txt")]
        REVIEWED_PY_ARG_CONSUMER_READS = frozenset(key(r) for r in [row()] + bad)
        rejected(pl, 'lacks its demonstrated run', reads(row()), standalone=[role])
        REVIEWED_PY_ARG_CONSUMER_RUNS = frozenset({(P, blob(pc, P), D, tuple(cmd))})
        model, rows = run(pl, reads(row()), standalone=[role])
        chain = rows[T]['runner_chain']
        assert rows[T]['class'] == 'keep' and chain['entry']['derived_from'] == PYTHON_ARGS_PREFIX + P
        assert chain['entry']['consumer_route']['demonstrated_command'] == cmd and chain['edges'][-1]['operation'] == PYC_OPERATION
        assert model['entry_points'][PYTHON_ARGS_PREFIX + P]['source_only']
        assert sorted(p for p, r in rows.items() if canonical(r) != canonical(base[p])) == [T]  # the target alone
        for r, message in zip(bad, ('main-block call stack ending at a read',) * 4):
            rejected(pl, message, reads(r), standalone=[role])
        for r, message in ((row(operation='x'), 'invalid Python argument consumer read route'), (dict(row(), extra=1), 'invalid Python argument consumer read route'),
                           (row(runner='nonpy-entry:' + P), 'invalid Python argument consumer read route'),
                           (row(command=['python3', P, 'inventory']), 'invalid Python argument consumer read route'),
                           (row(command=cmd[:3] + ['freeze']), 'unreviewed Python argument consumer read'),
                           (dict(row(), frames=[{'path': 'tests/pyc/other.txt', 'blob': blob(pc, 'tests/pyc/other.txt'), 'line': 1}]), 'leave the program')):
            rejected(pl, message, reads(r), standalone=[role])
        # A runner naming a root the model does not hold, or no root at all: no credit, no error.
        assert run(pl, reads(row(runner='committed:' + P)), standalone=[role])[1][T]['class'] != 'keep'
        assert run(pl, reads(row()))[1][T]['class'] != 'keep'
        # The objects must be the ones at the demonstration revision.
        changed = commit({T: 'changed\n'}, 'pyc data changed'); restored = commit({T: 'data\n'}, 'pyc data restored')
        assert run(changed, reads(row()), standalone=[role])[1][T]['class'] != 'keep'
        assert run(restored, reads(row()), standalone=[role])[1][T]['class'] == 'keep'
        REVIEWED_PY_ARG_CONSUMER_RUNS = frozenset({(P, blob(pc, P), changed.ref, tuple(cmd))})
        assert run(restored, reads(dict(row(), input_revision=changed.ref)), standalone=[role])[1][T]['class'] != 'keep'
    finally: REVIEWED_PY_ARG_CONSUMER_RUNS, REVIEWED_PY_ARG_CONSUMER_READS, REVIEWED_PYTHON_ARGS = saved


FORM_CONTROLS.append(python_argument_consumer_controls)
