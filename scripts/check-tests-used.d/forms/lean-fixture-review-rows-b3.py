# H1212 (gh#1526, Q-X1ERR-3, Option A), form (d): H1015 Lean fixture review rows
# for x1e-classify-rest-rest's B3 list, with one further driver line form. A
# reviewed H997 driver (REVIEWED_NONPY_ENTRIES) reaches, at top level, its
# column-0 line
#   LEAN_NUM_THREADS=1 lake "${A[@]}" env lean -j1 --tstack=131072 --setup "$work/setup.json"  PATH
# where A is only ever `A=()` and the exact optional-config line
#   if [ -n "${LAKE_CONFIG:-}" ]; then A=(-f "$LAKE_CONFIG"); fi
# work is only `work=$(mktemp -d)`, and the working directory is only ever the
# repository root (`cd "$(git rev-parse --show-toplevel)"`, or `cd "$root"` after
# the one `root=$(git rev-parse --show-toplevel)`). Before the line: here-document
# bodies are skipped to their exact terminator; other lines have balanced quotes,
# no backquote or continuation, no other cd/pushd/popd, no alias, eval, source,
# exec, exit, return, function definition or declare/unset of a variable, and
# every block is closed. Lexical; the review set gates. The driver's environment
# (LAKE_CONFIG, PATH, the generated setup file) is not audited: it only bounds
# consumption credit. Rows go through the registry's lean-fixtures part (the H1015
# rules of lean_fixture_root, unchanged): consumption only, no elaboration, pass,
# read, import, proof or runtime credit.
# Reviewed on master 57c3b2f7: UnsignedMul/Observations.lean (driver
# primitive-packets-1104/UnsignedMul/run.sh, line 21) and CheckedSub/
# Observations.lean (primitive-packets-1105/CheckedSub/run.sh, line 17); both
# drivers are H1025 entries, both sources pass lean_fixture_interface, and each
# blob was introduced once, with its driver. Refused, left unresolved (91):
# vt1/DialectChecks.lean (check-dialect.sh runs it inside `exec flock ... docker
# run ... bash -c '...'`, a quoted script in another container, not a top-level
# driver line); the sources driven only by Python programs (check.py,
# measured-checks.py, check-files.py, validate-fresh.py, check-spec-proposal.py,
# measure-replay-costs.py, the h55 module-time controls, roadmap-v16 scripts,
# test_components.py), since H1015 drivers are reviewed shell entries; and the
# sources no committed program names by path (roadmap-g19/g36, v14-constructor,
# v14-help, vo1, most of vt1, roadmap-v16 controls, automation, ...).
_B3_SETUP_LINE = (r'LEAN_NUM_THREADS=1 lake "\$\{([A-Za-z_]\w*)\[@\]\}" env lean -j1 --tstack=131072 --setup "\$work/setup\.json"'
                  r'[ \t]+([A-Za-z0-9_][\w./+-]*)')
_B3_TOPLEVEL = 'root=$(git rev-parse --show-toplevel)'
_B3_REPOSITORY_CD = ('cd "$(git rev-parse --show-toplevel)"', 'cd "$root"')


def lean_setup_env_invocation(text, path, line):
    """The driver reaches its column-0 setup-file `lake env lean` line for path (see above)."""
    if not isinstance(text, str) or not _plain_lines(text) or '\0' in text: return False
    lines = text.split('\n')
    if type(line) is not int or not 1 <= line <= len(lines): return False
    match = re.fullmatch(_B3_SETUP_LINE, lines[line - 1])
    if match is None or match[2] != path or _clean(path) != path: return False
    array = match[1]; before = lines[:line - 1]
    expected = {array + '=()': 1, 'if [ -n "${LAKE_CONFIG:-}" ]; then ' + array + '=(-f "$LAKE_CONFIG"); fi': 1, 'work=$(mktemp -d)': 1}
    if any(before.count(k) != v for k, v in expected.items()): return False
    assignment = lambda name: r'(?<![\w$])' + name + r'(?:\[[^\]]*\])?\+?='
    depth = 0; heredoc = None; root = False; seen = []
    for n, raw in enumerate(before, 1):
        if heredoc is not None:
            if (raw.lstrip('\t') if heredoc[0] else raw) == heredoc[1]: heredoc = None
            continue
        if n == 1 and raw.startswith('#!') or not raw.strip() or raw.strip().startswith('#'): continue
        if raw in expected: seen.append(raw)
        elif re.search(assignment(re.escape(array)) + '|' + assignment('work'), raw): return False
        if raw == _B3_TOPLEVEL: root = True
        elif re.search(assignment('root'), raw): return False
        if raw in _B3_REPOSITORY_CD and (raw == _B3_REPOSITORY_CD[0] or root): continue
        try: words = shlex.split(raw, comments=True)
        except ValueError: return False
        if '`' in raw or raw.rstrip().endswith('\\') or re.search(r'\w\s*\(\s*\)', raw): return False
        if re.search(r'(?<![\w$./-])(?:cd|pushd|popd|alias|eval|source|function|exit|return|exec|unalias|enable|builtin|hash|declare|typeset'
                     r'|unset|readonly|local|mapfile|readarray|read)(?![\w-])|(?:^|[;&|]\s*)\.\s', raw): return False
        unquoted = re.sub(r'\'[^\']*\'|"(?:[^"\\]|\\.)*"', '', raw)
        if raw.count('<<') != unquoted.count('<<'): return False  # a quoted << is never a here-document
        here = re.findall(r'(?<!<)<<(-?)[ \t]*([\'"]?)([A-Za-z_]\w*)\2', raw)
        if len(here) > 1: return False
        for word in words:
            depth += word in ('for', 'while', 'until', 'if', 'case', 'select', '{') or 0
            depth -= word in ('done', 'fi', 'esac', '}') or 0
            if depth < 0: return False
        if here: heredoc = (here[0][0] == '-', here[0][2])
    empty, optional = list(expected)[:2]
    return depth == 0 and heredoc is None and sorted(seen) == sorted(expected) and seen.index(empty) < seen.index(optional)


LEAN_FIXTURE_FORMS.append(lean_setup_env_invocation)

# (source, blob, introducing commit) and (source, blob, driver, driver blob, driver line)
_B3_FIXTURES = frozenset({
    ('tests/primitive-packets-1104/UnsignedMul/Observations.lean', 'e345de82cb367e6c9f209f4c4cc31bf97e6bea0b', '1b695516b853974ceb57be3a2ae82682c405fde5'),
    ('tests/primitive-packets-1105/CheckedSub/Observations.lean', 'bb1f391ce89f93f21b05ec3e29e8201604df805e', '7b0fc88517223bae9e98ddee11941af50834f691')})
_B3_INVOCATIONS = frozenset({
    ('tests/primitive-packets-1104/UnsignedMul/Observations.lean', 'e345de82cb367e6c9f209f4c4cc31bf97e6bea0b',
     'tests/primitive-packets-1104/UnsignedMul/run.sh', 'b4f27c0a8fd5d3cf2cf60a3e88f8de12eb17b54e', 21),
    ('tests/primitive-packets-1105/CheckedSub/Observations.lean', 'bb1f391ce89f93f21b05ec3e29e8201604df805e',
     'tests/primitive-packets-1105/CheckedSub/run.sh', '8e529c0bcc5ba9c28793683ad758b0ce0f7501c3', 17)})
REVIEW_TABLE_PARTS['lean-fixtures'].append(('H1212-B3', _B3_FIXTURES, _B3_INVOCATIONS, ('tests/primitive-packets-1104/', 'tests/primitive-packets-1105/')))


def lean_fixture_b3_controls(env):
    """H1212 (d) controls: the reviewed rows, the lexical setup-file form and a
    synthetic driver whose line keeps the fixture role while a cd before it is refused."""
    global REVIEWED_LEAN_FIXTURES, REVIEWED_LEAN_FIXTURE_INVOCATIONS, REVIEWED_NONPY_ENTRIES
    commit, run, rejected, blob, gate, reviewed_nonpy = (env[k] for k in ('commit', 'run', 'rejected', 'blob', 'gate', 'reviewed_nonpy'))
    assert _B3_FIXTURES <= REVIEWED_LEAN_FIXTURES and _B3_INVOCATIONS <= REVIEWED_LEAN_FIXTURE_INVOCATIONS and len(_B3_INVOCATIONS) == 2
    assert all((d, db) in {(q, b) for q, b, _ in reviewed_nonpy} and (p, b) in {(q, c) for q, c, _ in _B3_FIXTURES} for p, b, d, db, _ in _B3_INVOCATIONS)
    assert not {p for p, *_ in REVIEWED_LEAN_FIXTURES} & {'tests/fullscope-20261104/vt1/DialectChecks.lean'}
    X = 'tests/b3/Obs.lean'
    L1 = 'LEAN_NUM_THREADS=1 lake "${args[@]}" env lean -j1 --tstack=131072 --setup "$work/setup.json"   ' + X
    pre = ('#!/usr/bin/env bash\n# driver\nset -euo pipefail\nroot=$(git rev-parse --show-toplevel)\ncd "$root"\nwork=$(mktemp -d)\n'
           'trap \'rm -rf "$work"\' EXIT\npython3 - "$work/setup.json" <<\'PYSETUP\'\nimport os\nos.chdir("x")  # cd; exit; f() {\nPYSETUP\n'
           'args=()\nif [ -n "${LAKE_CONFIG:-}" ]; then args=(-f "$LAKE_CONFIG"); fi\n')
    lit = pre + L1 + '\n'; n1 = lit.count('\n')
    alt = lit.replace('root=$(git rev-parse --show-toplevel)\ncd "$root"\n', 'cd "$(git rev-parse --show-toplevel)"\n')
    assert lean_setup_env_invocation(lit, X, n1) and lean_setup_env_invocation(alt, X, alt.count('\n'))
    assert not lean_setup_env_invocation(lit, 'tests/b3/Other.lean', n1) and not lean_setup_env_invocation(lit, X, n1 - 1)
    assert not lean_check_invocation(lit, X, n1) and lean_gate_invocation(LEAN_FIXTURE_FORM, lit, X, n1) and not lean_gate_invocation(LEAN_CHECK_FORM, lit, X, n1)
    head, tail = pre.split('args=()\n')
    for t in ('cd tests', 'cd "$root"', 'pushd x', 'exec bash x.sh', 'exit 0', 'return 0', 'f() { :; }', 'function f { :; }', 'alias lake=true', 'eval "$x"',
              'source x.sh', '. x.sh', 'echo `x`', 'echo \\', ": '", 'for x in a; do', 'if true; then', '{', 'cat <<EOF\nx', 'args+=(x)', 'args[0]=x',
              'declare -n a=args', 'unset args', 'work=/tmp', 'root=/tmp', 'readarray args < f', 'read -a args'):
        bad = head.replace('cd "$root"\n', '') if t == 'cd "$root"' else head
        if t == 'cd "$root"': bad = bad.replace('root=$(git rev-parse --show-toplevel)\n', '')
        text = bad + t + '\nargs=()\n' + tail + L1 + '\n'
        assert not lean_setup_env_invocation(text, X, text.count('\n')), t
    for t in (L1 + ' && true', L1 + ' # c', ' ' + L1, L1.replace(X, '"' + X + '"'), L1 + ' $X', L1.replace(X, '../Obs.lean'), L1.replace('--setup', '--set'),
              L1.replace('"${args[@]}"', '${args[@]}'), L1.replace('"${args[@]}"', '"${other[@]}"'), L1.replace('lake ', 'lake2 '), L1 + '\r'):
        assert not lean_setup_env_invocation(pre + t + '\n', X, n1), t
    for t in (pre.replace('args=()\n', ''), pre.replace('args=()\nif', 'if').replace('fi\n', 'fi\nargs=()\n'), pre + 'args=()\n',
              pre.replace('(-f "$LAKE_CONFIG")', '(-f "$OTHER")'), pre.replace('work=$(mktemp -d)\n', '')):
        assert not lean_setup_env_invocation(t + L1 + '\n', X, t.count('\n') + 1), t
    assert not lean_setup_env_invocation(lit.replace('\n', '\0\n', 1), X, n1) and not lean_setup_env_invocation(None, X, 1) and not lean_setup_env_invocation(lit, X, '1')
    fixture = 'import Lib.Mod\n-- fixture\n\ndef F.v : Nat := 1\n'
    lf = commit({'scripts/coord-tools/gate.sh': gate, 'tests/b3/run.sh': lit, 'tests/b3/run-cd.sh': pre + 'cd tests\n' + L1 + '\n', X: fixture}, 'B3 fixture')
    L = lf.ref; ll = commit({'tests/unrelated.txt': 'B3\n'}, 'B3 later')
    call = lambda d='tests/b3/run.sh', line=n1: {'driver': d, 'driver_blob': blob(lf, d), 'driver_commit': L, 'line': line}
    role = {'path': X, 'input_revision': L, 'source_blob': blob(lf, X), 'kind': LEAN_FIXTURE_KIND, 'command': lean_check_command(X),
            'interface': {'imports': ['Lib.Mod'], 'body_line': 4}, 'provenance': {'commit': L, 'path': X, 'blob': blob(lf, X)}, 'invocations': [call()],
            'purpose': 'Synthetic setup-file fixture.'}
    saved = REVIEWED_LEAN_FIXTURES, REVIEWED_LEAN_FIXTURE_INVOCATIONS, REVIEWED_NONPY_ENTRIES
    REVIEWED_LEAN_FIXTURES = frozenset({(X, blob(lf, X), L)})
    REVIEWED_LEAN_FIXTURE_INVOCATIONS = frozenset({(X, blob(lf, X), d, blob(lf, d), n) for d, n in (('tests/b3/run.sh', n1), ('tests/b3/run-cd.sh', n1 + 1))})
    REVIEWED_NONPY_ENTRIES = reviewed_nonpy | {(d, blob(lf, d), L) for d in ('tests/b3/run.sh', 'tests/b3/run-cd.sh')}
    try:
        model, rows = run(ll, standalone=[role]); entry = model['entry_points'][LEAN_FIXTURE_PREFIX + X]
        assert entry['source_only'] and entry['lean_fixture_role'] and entry['validation_at_measured_revision']['status'] == 'unavailable'
        assert rows[X]['class'] == 'keep' and not any(k.startswith('lean-check:') for k in model['entry_points'])
        rejected(ll, 'driver does not run the source', standalone=[dict(role, invocations=[call('tests/b3/run-cd.sh', n1 + 1)])])
        rejected(ll, 'unreviewed Lean fixture role invocation', standalone=[dict(role, invocations=[call(line=n1 - 1)])])
        REVIEWED_LEAN_FIXTURES = frozenset()
        rejected(ll, 'unreviewed Lean fixture role', standalone=[role])
    finally: REVIEWED_LEAN_FIXTURES, REVIEWED_LEAN_FIXTURE_INVOCATIONS, REVIEWED_NONPY_ENTRIES = saved


FORM_CONTROLS.append(lean_fixture_b3_controls)
