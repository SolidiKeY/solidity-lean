# H1212 (gh#1526, Q-X1ERR-3, Option A), form (c): a literal IO.FS.readFile inside a
# top-level run_elab of a Lean file that a workflow elaborates directly (CI root
# `[lake env] lean [flags] FILE`). lean-readFile (H951) accepts only #eval and
# lean-library-readFile (H978/H1070) only library roots; elaborating FILE runs its
# run_elab commands too. consumer_routes section lean_run_elab_reads, one row per
# reviewed read:
#   {runner: FILE, frames: [{path: FILE, blob, line}], form: 'lean-run-elab-readFile',
#    target, target_blob, purpose}
# Opt-in by exact tuple (FILE, blob, line, target, target blob) in
# REVIEWED_RUN_ELAB_READS; anything else is rejected. At a measured --ref the row
# credits its one target while FILE and the target are those blobs (stale
# otherwise: no credit, no error), FILE is a current CI root whose command
# elaborates exactly FILE from the repository root, nothing in FILE before the
# line is #exit, and the line re-derives, through the H951 reader, to one literal
# read in a column-0 run_elab command. Consumption credit only: no elaboration,
# pass, proof, import or runtime credit; the CI root and every other form are
# unchanged.
# Reviewed on master 57c3b2f7: tests/automation/DirectRuntime.lean (pages.yml
# `lake env lean -j1 --tstack=131072 tests/automation/DirectRuntime.lean`) reads
# DirectRuntimeAdmission.ast.json at lines 24 and 45 and ClosedSpecs.ast.json at
# line 5, each the one IO.FS.readFile of a column-0 `run_elab do` block.
import shlex
RUN_ELAB_SECTION = 'lean_run_elab_reads'
RUN_ELAB_FORM = 'lean-run-elab-readFile'
RUN_ELAB_OPERATION = 'Lean IO.FS.readFile of literal cwd-relative path in a top-level run_elab of a file elaborated by its CI command'
_RUN_ELAB_FILE = 'tests/automation/DirectRuntime.lean'
_RUN_ELAB_BLOB = 'a912b3a4bcb9b79e91245301b16e2b6abe9df422'
# (file, file blob, read line, target, target blob)
REVIEWED_RUN_ELAB_READS = frozenset({
    (_RUN_ELAB_FILE, _RUN_ELAB_BLOB, 5, 'tests/automation/ClosedSpecs.ast.json', '5005e5a34af8a460c20b0b3d319f2a455f117f8f'),
    (_RUN_ELAB_FILE, _RUN_ELAB_BLOB, 24, 'tests/automation/DirectRuntimeAdmission.ast.json', '3e13c01a230936adf3d721a173fdc7549323d7d5'),
    (_RUN_ELAB_FILE, _RUN_ELAB_BLOB, 45, 'tests/automation/DirectRuntimeAdmission.ast.json', '3e13c01a230936adf3d721a173fdc7549323d7d5'),
})


def _run_elab_command(command, path):
    """The CI command elaborates exactly path: `[lake env] lean [-j1|--tstack=N]... path`."""
    try: words = shlex.split(command)
    except ValueError: return False
    if words[:2] == ['lake', 'env']: words = words[2:]
    if words[:1] != ['lean'] or words[-1:] != [path]: return False
    return all(w == '-j1' or re.fullmatch(r'--tstack=\d+', w) for w in words[1:-1])


def lean_run_elab_reads(classifier, graph, rows, reviewed=None):
    """H1212 (c): exact run_elab reads of a CI-elaborated Lean file (see above)."""
    repo = graph.repo
    reviewed = REVIEWED_RUN_ELAB_READS if reviewed is None else reviewed
    for row in rows:
        if (not isinstance(row, dict) or set(row) != {'runner', 'frames', 'form', 'target', 'target_blob', 'purpose'}
                or row['form'] != RUN_ELAB_FORM or not isinstance(row['runner'], str) or not isinstance(row['target'], str)
                or not isinstance(row['target_blob'], str) or not isinstance(row['purpose'], str) or not row['purpose'].strip()):
            raise ValueError('invalid Lean run_elab read route')
        frames = row['frames']; target = row['target']; runner = row['runner']
        if not _frames_current(repo, frames, [(target, row['target_blob'])]): continue
        if len(frames) != 1 or frames[0]['path'] != runner: raise ValueError('Lean run_elab read must be in the elaborated CI file')
        reader = frames[0]; path = reader['path']
        if (path, reader['blob'], reader['line'], target, row['target_blob']) not in reviewed:
            raise ValueError('unreviewed Lean run_elab read: ' + path)
        _check_lines(repo, frames)
        root = graph.roots.get(runner)
        if (root is None or root.get('kind') != 'CI' or root.get('path') != path or 'derived_from' in root or root.get('source_only')
                or root.get('cwd', '.') != '.' or not path.endswith('.lean') or not _run_elab_command(root.get('command', ''), path)):
            raise ValueError('Lean run_elab read requires a CI root elaborating the file')
        text = repo.texts[path]
        if not _plain_lines(text) or re.search(r'(?m)^#exit\b', classifier['lean_code'](text)[:_offset(text, reader['line'])]):
            raise ValueError('Lean run_elab read follows #exit or ambiguous line breaks')
        if _lean_read(classifier, repo, path, reader['line'], '.', r'run_elab') != target:
            raise ValueError('Lean run_elab read target is not the literal run_elab operand')
        if classifier['excluded'](target) or classifier['excluded'](path): continue
        _observe(graph, runner, row, frames, target, RUN_ELAB_OPERATION, 'consumes', 'Lean file elaborated by its CI command',
                 {'kind': 'lean-run-elab-read', 'purpose': row['purpose']})


register_consumer_section(RUN_ELAB_SECTION, ('runner', 'form', 'target', 'frames'), True,
                          lambda c, g, _, rows: lean_run_elab_reads(c, g, rows))


def lean_run_elab_controls(env):
    """H1212 (c) controls: the reviewed rows, a synthetic CI file whose run_elab
    read is credited only with its exact review, and the refused shapes."""
    global REVIEWED_RUN_ELAB_READS
    commit, run, rejected, blob, frame = (env[k] for k in ('commit', 'run', 'rejected', 'blob', 'frame'))
    assert len(REVIEWED_RUN_ELAB_READS) == 3 and {r[0] for r in REVIEWED_RUN_ELAB_READS} == {_RUN_ELAB_FILE}
    assert RUN_ELAB_SECTION in CONSUMER_SECTIONS and RUN_ELAB_FORM not in STATIC_FORMS
    assert _run_elab_command('lake env lean -j1 --tstack=131072 tests/E.lean', 'tests/E.lean')
    for c in ('lake env lean tests/F.lean', 'lake lean tests/E.lean', 'lean --run tests/E.lean', 'lean tests/E.lean x', 'lean "tests/E.lean', 'node tests/E.lean'):
        assert not _run_elab_command(c, 'tests/E.lean'), c
    E, F, D, V, W = 'tests/elab/E.lean', 'tests/elab/F.lean', 'tests/elab/data.txt', 'tests/elab/eval.txt', 'tests/elab/late.txt'
    elab = ('import Lean\nopen Lean\nrun_elab do\n  let s ← IO.FS.readFile "tests/elab/data.txt"\n  logInfo s\n'
            '#eval IO.FS.readFile "tests/elab/eval.txt"\n-- run_elab IO.FS.readFile "tests/elab/data.txt"\n'
            'def f : IO String := IO.FS.readFile "tests/elab/data.txt"\nrun_elab do\n  let a ← IO.FS.readFile "tests/elab/data.txt"\n'
            '  let b ← IO.FS.readFile "tests/elab/eval.txt"\n  logInfo (a ++ b)\n#exit\nrun_elab do\n  let s ← IO.FS.readFile "tests/elab/late.txt"\n')
    ec = commit({'.github/workflows/elab.yml': 'jobs:\n  t:\n    steps:\n      - run: lake env lean -j1 --tstack=131072 tests/elab/E.lean\n'
                 '      - run: lean tests/elab/F.lean extra\n', E: elab, F: elab, D: 'd\n', V: 'v\n', W: 'w\n'}, 'run_elab reads')
    el = commit({'tests/unrelated.txt': 'run_elab later\n'}, 'run_elab later')
    row = lambda line=4, target=D, path=E, **k: dict({'runner': path, 'frames': [frame(ec, path, line)], 'form': RUN_ELAB_FORM, 'target': target,
                                                      'target_blob': blob(ec, target), 'purpose': 'Synthetic run_elab read.'}, **k)
    reads = lambda *rows: {RUN_ELAB_SECTION: list(rows)}
    _, base = run(el)
    assert base[D]['class'] != 'keep' and base[W]['class'] != 'keep'
    saved = REVIEWED_RUN_ELAB_READS
    try:
        rejected(el, 'unreviewed Lean run_elab read', reads(row()))
        REVIEWED_RUN_ELAB_READS = frozenset((p, blob(ec, p), n, t, blob(ec, t)) for p in (E, F) for n, t in ((4, D), (6, V), (7, D), (8, D), (10, D), (11, V), (15, W)))
        for repo in (ec, el):
            model, rows = run(repo, reads(row())); plain = run(repo)[1]
            chain = rows[D]['runner_chain']
            assert rows[D]['class'] == 'keep' and chain['entry']['derived_from'] == E and chain['entry']['consumer_route']['kind'] == 'lean-run-elab-read'
            assert chain['edges'] == [{'source': E, 'target': D, 'line': 4, 'operation': RUN_ELAB_OPERATION, 'kind': 'consumes', 'validated_for': chain['root']}]
            changed = sorted(p for p, r in rows.items() if canonical(r) != canonical(plain[p]))
            assert changed == [D], changed  # one read, nothing else
        # Refused shapes: the #eval line (H951's lean-readFile form), a comment, a def body, two reads on one
        # line, a read after #exit, a non-CI file, extra frames, a wrong runner or target, a malformed row.
        for line, target, text in ((6, V, 'literal run_elab operand'), (7, D, 'literal run_elab operand'), (8, D, 'literal run_elab operand'),
                                   (15, W, '#exit'), (4, V, 'unreviewed')):
            rejected(el, text, reads(row(line, target)))
        rejected(el, 'CI root elaborating the file', reads(row(path=F)))
        rejected(el, 'elaborated CI file', reads(row(frames=[frame(ec, E, 3), frame(ec, E, 4)])))
        rejected(el, 'elaborated CI file', reads(row(runner=F)))
        for bad in (row(form='lean-readFile'), row(purpose=' '), dict(row(), extra=1), row(target_blob=None)):
            rejected(el, 'invalid Lean run_elab read route', reads(bad))
        rejected(el, 'literal lean-readFile', {'static_routes': [row(form='lean-readFile')]})  # H951 itself is unchanged
        for change in ({D: 'd2\n'}, {E: elab + '-- edited\n'}):  # stale objects grant nothing, never an error
            edited = commit(change, 'run_elab edited')
            assert run(edited, reads(row()))[1][D]['class'] != 'keep', change
            commit({k: (elab if k == E else 'd\n') for k in change}, 'run_elab restored')
        moved = commit({'.github/workflows/elab.yml': 'jobs:\n  t:\n    steps:\n      - run: lean tests/elab/F.lean\n'}, 'run_elab moved')
        rejected(moved, 'CI root elaborating the file', reads(row()))
    finally: REVIEWED_RUN_ELAB_READS = saved


FORM_CONTROLS.append(lean_run_elab_controls)
