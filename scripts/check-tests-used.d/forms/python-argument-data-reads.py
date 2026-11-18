# H1094 (gh#1446, Q-H62-ARGUMENT-JSON-READS, Option A), x1w form: an opt-in,
# exact-blob, argument-bearing Python data read. consumer_routes section
# python_argument_reads, one row per reviewed read:
#   {runner: 'committed-cli:P', input_revision, frames: [{path, blob, line}],
#    target, target_blob, command, operation, purpose}
# command is the exact argv with the placeholder EXTERNAL for the off-git
# output path; operation is PY_ARG_READ_KEY. Every row must equal a reviewed
# tuple (source, blob, argv, target, blob, frames, revision); anything else is
# rejected. Each tuple was reviewed against a complete ordinary and traced
# (audit hook + strace) pass at its revision whose external output stayed
# outside the checkout and under PY_ARG_OUTPUT_BOUND bytes.
# At any measured --ref the row credits its one target while the source, every
# frame and the target are the same blobs now and at the recorded revision
# (stale otherwise: no credit, no error), P's committed-cli root is current
# with that blob and exactly the argv's options as its required options, and
# P's syntax tree still shows the reviewed form: frames[0] is the live main()
# call, main() refuses an --output inside the repository (parser.error), and
# the last frame is `NAME.read_text()` in main() for a module-level
# NAME = <root> / "<target>". Recorded frames are provenance only.
# Source-data read credit only: no current validation, native, semantic, pass,
# output or proof credit; the committed-cli root, the other source-only roles
# and their premises are unchanged.
import ast, hashlib
# Checker names this form uses, bound by fragments.py, roles.py and registry.py
# (rebound to the same objects, so the registry's collision check is unaffected).
(CONSUMER_HANDLERS, FORM_CONTROLS, PERSISTED_OPERATION, _check_lines, _current, _historical_objects, _module_name, _rooted,
 canonical, register_consumer_section) = (globals()[name] for name in (
    'CONSUMER_HANDLERS', 'FORM_CONTROLS', 'PERSISTED_OPERATION', '_check_lines', '_current', '_historical_objects', '_module_name',
    '_rooted', 'canonical', 'register_consumer_section'))
PY_ARG_READ_SECTION = 'python_argument_reads'
PY_ARG_READ_KEY = 'argument-bearing Python data read'
PY_ARG_READ_OPERATION = 'blob-bound persisted read_text of a reviewed argument-bearing Python program run with external output'
PY_ARG_READ_PLACEHOLDER = 'EXTERNAL'
PY_ARG_OUTPUT_BOUND = 32 * 1024 * 1024
_PY_ARG_ITEM4 = 'scripts/h62/item4/generic-storageops/'
_PY_ARG_TESTS = 'tests/h62/item4/generic-storageops/'
_PY_ARG_PASS = '76d20f61085aaaf0ad0ec6955b6e662c09f68bc2'
# (source, blob, argv, target, target blob, ((frame path, blob, line), ...), revision, observed output bytes)
REVIEWED_PY_ARG_READS = frozenset({
    (_PY_ARG_ITEM4 + 'classify.py', '7116e793c6272010254e5c4b1ae58c7a687fbbed',
     ('python3', '-B', _PY_ARG_ITEM4 + 'classify.py', '--output', PY_ARG_READ_PLACEHOLDER),
     _PY_ARG_TESTS + 'classification-manifest.json', '59f41b8c4d1c65552354c76fbcdd1e9c43787f77',
     ((_PY_ARG_ITEM4 + 'classify.py', '7116e793c6272010254e5c4b1ae58c7a687fbbed', 326),
      (_PY_ARG_ITEM4 + 'classify.py', '7116e793c6272010254e5c4b1ae58c7a687fbbed', 320)), _PY_ARG_PASS, 22408949),
    (_PY_ARG_ITEM4 + 'fixture_plan.py', '6173be757c5088e47bf1548a055cd186abb77699',
     ('python3', '-B', _PY_ARG_ITEM4 + 'fixture_plan.py', '--output', PY_ARG_READ_PLACEHOLDER),
     _PY_ARG_TESTS + 'fixture-plan-manifest.json', 'ed1cdb424ac5ec2e97b003a80edc31d42ce667ed',
     ((_PY_ARG_ITEM4 + 'fixture_plan.py', '6173be757c5088e47bf1548a055cd186abb77699', 97),
      (_PY_ARG_ITEM4 + 'fixture_plan.py', '6173be757c5088e47bf1548a055cd186abb77699', 91)), _PY_ARG_PASS, 5981746),
})


def _py_arg_main(tree):
    mains = [n for n in tree.body if isinstance(n, ast.FunctionDef) and n.name == 'main']
    return mains[0] if len(mains) == 1 else None


def _py_arg_external_guard(function):
    """main() calls <parser>.error when <args>.output.resolve().is_relative_to(...)."""
    for node in ast.walk(function):
        if not isinstance(node, ast.If) or not isinstance(node.test, ast.Call) or len(node.test.args) != 1: continue
        test = node.test.func
        if not (isinstance(test, ast.Attribute) and test.attr == 'is_relative_to' and isinstance(test.value, ast.Call)
                and not test.value.args and isinstance(test.value.func, ast.Attribute) and test.value.func.attr == 'resolve'
                and isinstance(test.value.func.value, ast.Attribute) and test.value.func.value.attr == 'output'
                and isinstance(test.value.func.value.value, ast.Name)): continue
        body = node.body
        if (len(body) == 1 and isinstance(body[0], ast.Expr) and isinstance(body[0].value, ast.Call)
                and isinstance(body[0].value.func, ast.Attribute) and body[0].value.func.attr == 'error'
                and isinstance(body[0].value.func.value, ast.Name)):
            return True
    return False


def python_argument_read_form(text, target, main_line, reader_line):
    """True iff the source shows the reviewed form (see the comment above)."""
    try: tree = ast.parse(text)
    except (SyntaxError, ValueError, RecursionError): return False
    function = _py_arg_main(tree)
    if function is None or function.decorator_list or not _py_arg_external_guard(function): return False
    if not any(isinstance(n, ast.Expr) and isinstance(n.value, ast.Call) and isinstance(n.value.func, ast.Name)
               and n.value.func.id == 'main' and not n.value.args and n.lineno == main_line
               for node in tree.body for n in [node] + (node.body if isinstance(node, ast.If) else [])):
        return False
    nested = {id(n) for d in ast.walk(function) if d is not function and isinstance(d, (ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda, ast.ClassDef))
              for n in ast.walk(d)}
    for call in ast.walk(function):
        if (id(call) in nested or not isinstance(call, ast.Call) or call.args or call.keywords or call.lineno != reader_line
                or not isinstance(call.func, ast.Attribute) or call.func.attr != 'read_text' or not isinstance(call.func.value, ast.Name)):
            continue
        name = call.func.value.id
        assigns = [n for n in tree.body if isinstance(n, ast.Assign) and len(n.targets) == 1 and isinstance(n.targets[0], ast.Name)
                   and n.targets[0].id == name and isinstance(n.value, ast.BinOp) and _rooted(n.value, target)]
        if len(assigns) == 1 and _module_name(tree, name, assigns[0].lineno) is not None: return True
    return False


def python_argument_reads(classifier, graph, catalog, rows, reviewed=None):
    """H1094 handler for consumer_routes.python_argument_reads."""
    repo = graph.repo; reviewed = REVIEWED_PY_ARG_READS if reviewed is None else reviewed
    for row in rows:
        if not isinstance(row, dict) or set(row) != {'runner', 'input_revision', 'frames', 'target', 'target_blob', 'command', 'operation', 'purpose'}:
            raise ValueError('invalid argument-bearing Python read route')
        runner, revision, frames, target = row['runner'], row['input_revision'], row['frames'], row['target']
        if (not isinstance(runner, str) or not runner.startswith('committed-cli:') or row['operation'] != PY_ARG_READ_KEY
                or not isinstance(row['command'], list) or not all(isinstance(a, str) for a in row['command'])
                or not isinstance(row['purpose'], str) or not row['purpose'].strip()
                or not isinstance(target, str) or not isinstance(row['target_blob'], str) or not isinstance(revision, str)):
            raise ValueError('invalid argument-bearing Python read route')
        if not isinstance(frames, list) or not frames or any(
                not isinstance(f, dict) or set(f) != {'path', 'blob', 'line'} or not isinstance(f['path'], str)
                or not isinstance(f['blob'], str) or type(f['line']) is not int for f in frames):
            raise ValueError('invalid argument-bearing Python read frame')
        p = runner[len('committed-cli:'):]
        matches = [r for r in reviewed if r[0] == p and r[2] == tuple(row['command']) and r[3] == target and r[4] == row['target_blob']
                   and r[5] == tuple((f['path'], f['blob'], f['line']) for f in frames) and r[6] == revision]
        if len(matches) != 1: raise ValueError('unreviewed argument-bearing Python read: ' + p + ' -> ' + target)
        _, blob, argv, _, target_blob, _, _, output_bytes = matches[0]
        if frames[0]['path'] != p or any(f['path'] != p or f['blob'] != blob for f in frames):
            raise ValueError('argument-bearing Python read leaves its runner source: ' + p)
        if argv[:3] != ('python3', '-B', p) or len(argv) % 2 == 0 or any(not a.startswith('--') for a in argv[3::2]):
            raise ValueError('unsupported argument-bearing Python read invocation: ' + p)
        if not output_bytes <= PY_ARG_OUTPUT_BOUND: raise ValueError('unbounded argument-bearing Python read output: ' + p)
        pins = sorted({(p, blob), (target, target_blob)})
        if not all(_current(repo, q, b) for q, b in pins): continue
        _check_lines(repo, frames)
        if not _historical_objects(classifier, repo, revision, pins):
            raise ValueError('persisted route objects differ at recorded revision ' + revision)
        root = graph.roots.get(runner)
        if root is None or 'derived_from' in root or root.get('source_blob') != blob or root['path'] != p: continue
        provenance = root.get('role_provenance') or {}
        if root.get('required_options') != sorted(argv[3::2]) or provenance.get('main_line') != frames[0]['line']:
            raise ValueError('argument-bearing Python read does not supply its runner configuration: ' + p)
        if argv[4::2] != (PY_ARG_READ_PLACEHOLDER,) * len(argv[4::2]) or argv[3::2] != ('--output',):
            raise ValueError('argument-bearing Python read needs only an external --output: ' + p)
        if not python_argument_read_form(repo.texts[p], target, frames[0]['line'], frames[-1]['line']):
            raise ValueError('argument-bearing Python program does not read its target: ' + p)
        if classifier['excluded'](target) or classifier['excluded'](p): continue
        details = {'kind': 'argument-bearing-python-read', 'observed_revision': revision, 'command': list(argv),
                   'validation_at_observed_revision': 'ordinary and traced runs passed (reviewed)', 'runner_definition_blob': blob,
                   'external_output': {'option': '--output', 'placement': 'outside the repository, refused inside by the program',
                                       'observed_bytes': output_bytes, 'bound_bytes': PY_ARG_OUTPUT_BOUND, 'credited': False},
                   'purpose': row['purpose'], 'credit': 'source-data read of the named target only; no current, native, semantic, pass, output or proof credit'}
        derived = runner + ':' + details['kind'] + ':' + hashlib.sha256(canonical(row)).hexdigest()
        graph.roots[derived] = {**root, 'derived_from': runner, 'observed_target': target, 'consumer_route': details,
            'validation_at_measured_revision': {'status': 'unavailable', 'command': list(argv),
                'reason': 'Ordinary and traced runs passed at the observed revision (reviewed); not run here. Source-data read of the named target only: no current, native, semantic, pass, output or proof credit.'}}
        edges = [{'source': a['path'], 'target': b['path'], 'line': a['line'], 'operation': 'Recorded Python call stack (persisted; no credit)',
                  'kind': 'executes', 'validated_for': derived} for a, b in zip(frames, frames[1:])]
        edges.append({'source': p, 'target': target, 'line': frames[-1]['line'], 'operation': PY_ARG_READ_OPERATION,
                      'kind': 'consumes', 'validated_for': derived})
        graph.observed.append((target, {'root': derived, 'entry': graph.roots[derived], 'edges': edges}))


register_consumer_section(PY_ARG_READ_SECTION, ('runner', 'input_revision', 'target', 'frames'), True,
                          lambda c, g, k, rows: python_argument_reads(c, g, k, rows))


def python_argument_read_controls(env):
    """x1w H1094 controls: one reviewed argument-bearing read is credited, nothing else."""
    global REVIEWED_PY_ARG_READS
    commit, run, rejected, blob = (env[k] for k in ('commit', 'run', 'rejected', 'blob'))
    assert CONSUMER_HANDLERS[PY_ARG_READ_SECTION][:2] == (('runner', 'input_revision', 'target', 'frames'), True)
    assert len(REVIEWED_PY_ARG_READS) == 2 and {r[3] for r in REVIEWED_PY_ARG_READS} == {
        _PY_ARG_TESTS + 'classification-manifest.json', _PY_ARG_TESTS + 'fixture-plan-manifest.json'}
    assert all(r[2][3:] == ('--output', PY_ARG_READ_PLACEHOLDER) and r[6] == _PY_ARG_PASS and r[7] <= PY_ARG_OUTPUT_BOUND for r in REVIEWED_PY_ARG_READS)
    P = 'tests/argread.py'; T = 'tests/argread-pin.json'; O = 'tests/argread-other.json'
    text = ('import argparse\nfrom pathlib import Path\nROOT = Path(__file__).resolve().parent.parent\n'
            'PIN = ROOT / "tests/argread-pin.json"\nOTHER = ROOT / "tests/argread-other.json"\n'
            'def main():\n    p = argparse.ArgumentParser()\n    p.add_argument("--output", type=Path, required=True)\n'
            '    p.add_argument("--write", action="store_true")\n    a = p.parse_args()\n'
            '    if a.output.resolve().is_relative_to(ROOT): p.error("output must be off git")\n'
            '    if a.write: PIN.write_text("pin\\n")\n    elif PIN.read_text() != "pin\\n": raise SystemExit("drift")\n'
            '    def later(): return OTHER.read_text()\n    a.output.write_text(OTHER.read_text())\n'
            'if __name__ == "__main__": main()\n')
    unguarded = text.replace('    if a.output.resolve().is_relative_to(ROOT): p.error("output must be off git")\n', '    pass\n')
    ar = commit({P: text, T: 'pin\n', O: 'other\n', 'tests/argread-unguarded.py': unguarded}, 'argument-bearing reads')
    cli = lambda path=P, repo=ar: {'path': path, 'input_revision': repo.ref, 'source_blob': blob(repo, path), 'command': ['python3', '-B', path],
                                   'kind': 'committed-cli', 'entry_line': 16, 'required_options': ['--output'], 'purpose': 'Synthetic pinned checker.'}
    frames = lambda line=13, path=P, main=16: [{'path': path, 'blob': blob(ar, path), 'line': main}, {'path': path, 'blob': blob(ar, path), 'line': line}]
    def row(target=T, line=13, path=P, main=16, **extra):
        return {'runner': 'committed-cli:' + path, 'input_revision': ar.ref, 'frames': frames(line, path, main), 'target': target,
                'target_blob': blob(ar, target), 'command': ['python3', '-B', path, '--output', PY_ARG_READ_PLACEHOLDER],
                'operation': PY_ARG_READ_KEY, 'purpose': 'Synthetic pin read.', **extra}
    def review(target=T, line=13, path=P, argv=None, revision=None, size=10, main=16):
        return (path, blob(ar, path), tuple(argv or ('python3', '-B', path, '--output', PY_ARG_READ_PLACEHOLDER)), target, blob(ar, target),
                tuple((f['path'], f['blob'], f['line']) for f in frames(line, path, main)), revision or ar.ref, size)
    reads = lambda *rows: {PY_ARG_READ_SECTION: list(rows)}
    saved = REVIEWED_PY_ARG_READS
    try:
        later = commit({'tests/argread-unrelated.txt': 'later\n'}, 'later')
        base_model, base = run(later, standalone=[cli()])
        assert base[T]['class'] != 'keep' and 'committed-cli:' + P in base_model['entry_points']
        REVIEWED_PY_ARG_READS = frozenset({review(), review(O, 15), review(O, 14), review(line=11), review(path='tests/argread-unguarded.py'),
                                           review(argv=('python3', '-B', P, '--output', '/tmp/out')), review(size=PY_ARG_OUTPUT_BOUND + 1, line=12),
                                           review(main=15), review(revision=env['first'].ref)})
        model, rows = run(later, reads(row()), standalone=[cli()])
        chain = rows[T]['runner_chain']; route = chain['entry']['consumer_route']
        assert rows[T]['class'] == 'keep' and chain['edges'][-1]['operation'] == PY_ARG_READ_OPERATION and chain['edges'][-1]['kind'] == 'consumes'
        assert route['observed_revision'] == ar.ref and route['command'][3:] == ['--output', PY_ARG_READ_PLACEHOLDER] and not route['external_output']['credited']
        assert chain['entry']['source_only'] and chain['entry']['validation_at_measured_revision']['status'] == 'unavailable'
        # Source-data read only: no other record, root or premise changes.
        assert all(canonical(r) == canonical(base[q]) for q, r in rows.items() if q != T)
        assert {k: v for k, v in model['entry_points'].items() if 'derived_from' not in v} == base_model['entry_points']
        # Repeated identical rows are one claim; a different claim for the same identity is ambiguous.
        assert canonical(run(later, reads(row(), row()), standalone=[cli()])) == canonical((model, rows))
        rejected(later, 'conflicting', reads(row(), row(purpose='Other.')), standalone=[cli()])
        # Refusals: unreviewed argv, line or target; malformed rows; another form at a reviewed line.
        rejected(later, 'unreviewed argument-bearing', reads(dict(row(), command=['python3', '-B', P, '--output', 'out.json'])), standalone=[cli()])
        rejected(later, 'unreviewed argument-bearing', reads(dict(row(), command=['python3', '-B', P, '--write', '--output', PY_ARG_READ_PLACEHOLDER])), standalone=[cli()])
        rejected(later, 'unreviewed argument-bearing', reads(row(line=10)), standalone=[cli()])
        rejected(later, 'invalid argument-bearing', reads(dict(row(), runner='validated:' + P)), standalone=[cli()])
        rejected(later, 'invalid argument-bearing', reads(row(extra=1)), standalone=[cli()])
        rejected(later, 'invalid argument-bearing', reads(dict(row(), operation=PERSISTED_OPERATION)), standalone=[cli()])
        rejected(later, 'invalid argument-bearing Python read frame', reads(dict(row(), frames=[dict(f, code_qualname='main') for f in frames()])), standalone=[cli()])
        # A read passed as an argument is still the reader call at its line.
        _, rows = run(later, reads(row(O, 15)), standalone=[cli()])
        assert rows[O]['class'] == 'keep' and rows[T]['class'] != 'keep'
        rejected(later, 'does not read its target', reads(row(O, 14)), standalone=[cli()])  # nested def
        rejected(later, 'does not read its target', reads(row(line=11)), standalone=[cli()])  # the guard line, no read
        rejected(later, 'does not read its target', reads(row(path='tests/argread-unguarded.py')), standalone=[cli('tests/argread-unguarded.py')])
        rejected(later, 'needs only an external --output', reads(dict(row(), command=['python3', '-B', P, '--output', '/tmp/out'])), standalone=[cli()])
        rejected(later, 'unbounded', reads(row(line=12)), standalone=[cli()])
        rejected(later, 'runner configuration', reads(row(main=15)), standalone=[cli()])
        rejected(later, 'differ at recorded revision', reads(dict(row(), input_revision=env['first'].ref)), standalone=[cli()])
        # No committed-cli root (or one for other bytes), or a changed target or source: stale, no credit.
        REVIEWED_PY_ARG_READS = frozenset({review()})
        _, rows = run(later, reads(row()))
        assert rows[T]['class'] != 'keep'
        for changes in ({T: 'pin2\n'}, {P: text + '# changed\n'}):
            edited = commit(changes, 'changed')
            model, rows = run(edited, reads(row()), standalone=[cli(repo=edited)])
            assert rows[T]['class'] != 'keep' and not any('derived_from' in v for v in model['entry_points'].values() if v['path'] == P)
            commit({T: 'pin\n', P: text}, 'restored')
        # An empty table credits nothing and refuses every row.
        REVIEWED_PY_ARG_READS = frozenset()
        rejected(later, 'unreviewed argument-bearing', reads(row()), standalone=[cli()])
    finally: REVIEWED_PY_ARG_READS = saved


FORM_CONTROLS.append(python_argument_read_controls)
