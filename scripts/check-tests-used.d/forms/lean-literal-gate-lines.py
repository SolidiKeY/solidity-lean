# H1019 (gh#1366, Q-X1O-1, Option B): a reviewed driver's literal column-0 line
# `bash scripts/coord-tools/gate.sh per-file <path> ...` invokes a reviewed Lean
# fixture. Ported from x1o commit 27e01ea23; every blob re-checked on master
# d573a760b. Consumption credit only; the driver's environment is not audited.
# ApiSignatures and AxiomInventory fit no interface; the 16 shell-loop-word paths
# stay unresolved.

LEAN_LITERAL_LINE = r'bash scripts/coord-tools/gate\.sh per-file((?: [A-Za-z0-9_][\w./+-]*)+)'


def lean_literal_invocation(text, path, line):
    """The driver reaches its column-0 line `bash scripts/coord-tools/gate.sh
    per-file W...` (plain words, path one of them) at top level. Before it:
    here-document bodies are skipped to their exact terminator; other lines
    have balanced quotes, no backquote or continuation, no cd/pushd/popd/alias/
    eval/function definition, no exit or return, no exec but a pure
    redirection, and every for/while/until/if/case/select/{ is closed.
    Lexical; the review set gates."""
    if not isinstance(text, str) or not _plain_lines(text) or '\0' in text: return False
    lines = text.split('\n')
    if type(line) is not int or not 1 <= line <= len(lines): return False
    match = re.fullmatch(LEAN_LITERAL_LINE, lines[line - 1])
    if match is None or path not in match[1].split() or any(_clean(w) != w for w in match[1].split()): return False
    depth = 0; heredoc = None
    for n, raw in enumerate(lines[:line - 1], 1):
        if heredoc is not None:
            if (raw.lstrip('\t') if heredoc[0] else raw) == heredoc[1]: heredoc = None
            continue
        if n == 1 and raw.startswith('#!') or not raw.strip() or raw.strip().startswith('#'): continue
        try: words = shlex.split(raw, comments=True)
        except ValueError: return False
        if '`' in raw or raw.rstrip().endswith('\\') or re.search(r'\w\s*\(\s*\)', raw): return False
        if re.search(r'(?<![\w$./-])(?:cd|pushd|popd|alias|eval|function|exit|return|unalias|enable|builtin|hash)(?![\w-])', raw): return False
        if re.search(r'(?<![\w$./-])exec(?![\w-])', raw) and not re.fullmatch(r'exec(?:[ \t]+\d*[<>]&?[^\s;&|]+)+[ \t]*', raw): return False
        here = re.findall(r'(?<!<)<<(-?)[ \t]*([\'"]?)([A-Za-z_]\w*)\2', raw)
        if len(here) > 1: return False
        for word in words:
            depth += word in ('for', 'while', 'until', 'if', 'case', 'select', '{') or 0
            depth -= word in ('done', 'fi', 'esac', '}') or 0
            if depth < 0: return False
        if here: heredoc = (here[0][0] == '-', here[0][2])
    return depth == 0 and heredoc is None


LEAN_FIXTURE_FORMS.append(lean_literal_invocation)

_H1019_FIXTURES = _review_table('''
@0bdac88bfacec822c7157b7d5a3e713894571888
N:primitive-return/FiniteControls.lean b05e60df2a805d814f29e745990ff6c4b7338965
@17f2902cdc6ab848317fc82e31a90ad2d7c4fba8
D:memory-references/KernelControls.lean 4814aadd49ceaa76564a6e6564ecb6cb1093db25
@4234b74778787f681ebb50f2890355d99f37731a
N:address/MarkerIdentityControls.lean 83b03faacdba2782a670aa428520abf7fc760413
@4d7285b80e89741e9da8cb49ce7ab8b62a828a72
N:environment/MetadataControls.lean 970ded15d40473c5605348fb5d93ac112273a582
@b35ed6a63ad9767f9cb63c4d748b52dc1a287218
D:shared-translator/ReadBoundsStackControls.lean 75383e5889553439e949ae17338253d39f0d4635
@df6565c9a168d72395ce6aeea34a79782e31275f
N:fixed-byte/MarkerControls.lean 794ead752a929293a52ae0acac24aadae9dcd594
''')
_H1019_DRIVER_LINES = (
    ('memory-references/KernelControls', 'native-browser/environment/scripts/B-kernel-controls.sh', '971e181a0d2b877229eeefb48306e9e6fa86f62d', 9),
    ('native-browser/address/MarkerIdentityControls', 'native-browser/environment/scripts/address-marker-gate.sh', 'a3fd70679b39c94289498f6900b24ad6495dc517', 9),
    ('native-browser/environment/MetadataControls', 'native-browser/environment/scripts/marker-gate.sh', '1f6e42cf641de1003b3d9dca483f4aa47af9ff7d', 9),
    ('native-browser/fixed-byte/MarkerControls', 'native-browser/environment/scripts/fixed-byte-gate.sh', 'd4197132f138040fc277bd006f6393e0455ec9b9', 9),
    ('native-browser/primitive-return/FiniteControls', 'native-browser/environment/scripts/finite-gate.sh', '78e4b5909d6dd81671cedb28178437804072e407', 9),
    ('shared-translator/ReadBoundsStackControls', 'native-browser/readbounds/axiom-gates.sh', '6d77f69e2a86fa3d1ab1121b4cc9408aeb19fabd', 15),
    ('shared-translator/ReadBoundsStackControls', 'native-browser/readbounds/scripts/axiom-gates-post-rebase.sh', 'bdffe31da9f3c37864b74b8bf0f349654409db64', 15),
    ('shared-translator/AddressLocalControls', 'shared-translator/environment-decoder-validate.sh', 'c9e849741ec9f96867766ecf7346f02c4d2389cf', 48),
    ('shared-translator/AddressLocalControls', 'shared-translator/environment-proof-validate.sh', 'db00b98f108dd43cbe5e9d46c01f405ae22f4a18', 27),
    ('shared-translator/EnvironmentMemberControls', 'shared-translator/environment-decoder-validate.sh', 'c9e849741ec9f96867766ecf7346f02c4d2389cf', 48),
    ('shared-translator/EnvironmentMemberControls', 'shared-translator/environment-proof-validate.sh', 'db00b98f108dd43cbe5e9d46c01f405ae22f4a18', 27))
_H1019_INVOCATIONS = frozenset(
    (p, b, 'tests/directruntime-20261104/' + d, db, n) for p, b, _ in _H1019_FIXTURES | REVIEW_TABLE_PARTS['lean-fixtures'][0][1]
    for q, d, db, n in _H1019_DRIVER_LINES if p == 'tests/directruntime-20261104/' + q + '.lean')
REVIEW_TABLE_PARTS['lean-fixtures'].append(('H1019', _H1019_FIXTURES, _H1019_INVOCATIONS, ('tests/directruntime-20261104/',)))


def lean_literal_controls(env):
    """H1019 controls: the reviewed rows, the lexical form and a synthetic driver
    whose literal line keeps the fixture role while a cd before it is refused."""
    global REVIEWED_LEAN_FIXTURES, REVIEWED_LEAN_FIXTURE_INVOCATIONS, REVIEWED_NONPY_ENTRIES
    commit, run, rejected, blob, gate, reviewed_nonpy = (env[k] for k in ('commit', 'run', 'rejected', 'blob', 'gate', 'reviewed_nonpy'))
    assert len(_H1019_FIXTURES) == 6 and len(_H1019_INVOCATIONS) == 11 and _H1019_INVOCATIONS <= REVIEWED_LEAN_FIXTURE_INVOCATIONS
    assert all((d, db) in {(q, b) for q, b, _ in reviewed_nonpy} and d.endswith('.sh') for _, _, d, db, _ in _H1019_INVOCATIONS)
    assert not {p for p, *_ in REVIEWED_LEAN_FIXTURES} & {'tests/directruntime-20261104/shared-translator/' + n + '.lean' for n in ('ApiSignatures', 'AxiomInventory')}
    L1 = 'bash scripts/coord-tools/gate.sh per-file Lib/M.lean tests/f/F.lean'
    lit = ('#!/usr/bin/env bash\nset -euo pipefail\n[[ ${GATE:-} == 1 ]]\nsource /setup/activate.sh\nexport PATH="$PWD/b:$PATH"\n'
           'exec 9>/tmp/w.lock\nflock 9\ntrap \'echo stop\' EXIT\npython3 - <<\'PY\'\nimport os\nos.chdir("x")  # cd; exit; f() {\nPY\n'
           'for t in A B; do\n  lake build "$t"\ndone\nif true; then echo; fi\n' + L1 + '\n')
    ll1 = lit.count('\n'); X = 'tests/f/F.lean'
    assert lean_literal_invocation(lit, X, ll1) and lean_literal_invocation(lit, 'Lib/M.lean', ll1)
    assert not lean_literal_invocation(lit, 'tests/f/G.lean', ll1) and not lean_literal_invocation(lit, X, ll1 - 1)
    assert not lean_check_invocation(lit, X, ll1) and not lean_gate_invocation(LEAN_CHECK_FORM, lit, X, ll1) and lean_gate_invocation(LEAN_FIXTURE_FORM, lit, X, ll1)
    pre = lit[:-len(L1) - 1]
    for t in ('cd tests', 'pushd x', 'exec bash x.sh', 'exit 0', 'true || exit 1', 'return 0', 'f() { :; }', 'function f { :; }', 'alias bash=true',
              'eval "$x"', 'echo `x`', 'echo \\', ": '", 'for x in a; do', 'if true; then', 'while true; do', '{', 'case x in', 'echo done\nfor x in a; do',
              'cat <<EOF\nx', 'cat <<A <<B\nA\nB', 'hash -p /bin/true bash', 'builtin cd x', 'enable -n echo'):
        assert not lean_literal_invocation(pre + t + '\n' + L1 + '\n', X, ll1 + t.count('\n') + 1), t
    for t in (L1 + ' && true', L1 + ' # c', ' ' + L1, L1.replace('tests/f/F.lean', '"tests/f/F.lean"'), L1 + ' $X',
              L1.replace('Lib/M.lean', '../M.lean'), L1.replace('per-file', 'touched'), 'bash scripts/coord-tools/gate.sh per-file "${files[@]}" tests/f/F.lean',
              L1.replace('bash ', 'sh '), L1 + ' > log', L1 + '\r'):
        assert not lean_literal_invocation(pre + t + '\n', X, ll1), t
    assert not lean_literal_invocation(pre + L1 + '\0\n', X, ll1) and not lean_literal_invocation(None, X, 1) and not lean_literal_invocation(lit, X, '1')
    fixture = 'import Lib.Mod\n-- fixture\n\ndef F.v : Nat := 1\n'
    lf = commit({'scripts/coord-tools/gate.sh': gate, 'tests/f/lit.sh': lit, 'tests/f/lit-cd.sh': pre + 'cd tests\n' + L1 + '\n', X: fixture}, 'Lean literal')
    L = lf.ref; ll = commit({'tests/unrelated.txt': 'F\n'}, 'Lean literal later')
    call = lambda d='tests/f/lit.sh', line=ll1: {'driver': d, 'driver_blob': blob(lf, d), 'driver_commit': L, 'line': line}
    role = {'path': X, 'input_revision': L, 'source_blob': blob(lf, X), 'kind': LEAN_FIXTURE_KIND, 'command': lean_check_command(X),
            'interface': {'imports': ['Lib.Mod'], 'body_line': 4}, 'provenance': {'commit': L, 'path': X, 'blob': blob(lf, X)}, 'invocations': [call()],
            'purpose': 'Synthetic literal fixture.'}
    saved = REVIEWED_LEAN_FIXTURES, REVIEWED_LEAN_FIXTURE_INVOCATIONS, REVIEWED_NONPY_ENTRIES
    REVIEWED_LEAN_FIXTURES = frozenset({(X, blob(lf, X), L)})
    REVIEWED_LEAN_FIXTURE_INVOCATIONS = frozenset({(X, blob(lf, X), d, blob(lf, d), n) for d, n in (('tests/f/lit.sh', ll1), ('tests/f/lit-cd.sh', ll1 + 1))})
    REVIEWED_NONPY_ENTRIES = reviewed_nonpy | {(d, blob(lf, d), L) for d in ('tests/f/lit.sh', 'tests/f/lit-cd.sh')}
    try:
        model, rows = run(ll, standalone=[role]); entry = model['entry_points']['lean-fixture:' + X]
        assert rows[X]['class'] == 'keep' and entry['lean_fixture_role'] and entry['location'] == 'tests/f/lit.sh:%d' % ll1
        assert entry['validation_at_measured_revision']['status'] == 'unavailable'
        rejected(lf, 'Lean fixture role driver does not run the source', standalone=[dict(role, invocations=[call('tests/f/lit-cd.sh', ll1 + 1)])])
        rejected(lf, 'role invocation', standalone=[dict(role, invocations=[call(line=ll1 - 1)])])
        rejected(lf, 'unreviewed Lean check role', standalone=[dict(role, kind=LEAN_CHECK_KIND)])
    finally: REVIEWED_LEAN_FIXTURES, REVIEWED_LEAN_FIXTURE_INVOCATIONS, REVIEWED_NONPY_ENTRIES = saved


FORM_CONTROLS.append(lean_literal_controls)
