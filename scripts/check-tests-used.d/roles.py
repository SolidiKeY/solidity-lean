"""Reviewed Lean gate source roles: H999 check sources and H1015 fixture sources.

Executed by fragments.py in its own namespace (helpers, review tables and the
self-test rebinding of REVIEWED_* names are shared). Classifier path: excluded
from candidate discovery like the rest of scripts/check-tests-used*."""


LEAN_CHECK_KIND = 'lean-check-source-role'
LEAN_CHECK_PREFIX = 'lean-check:'
# H999 (gh#1334, X1E-LEAN-CHECK-ROLE): the driver line and the gate.sh
# per-file branch that forms the one command.
LEAN_CHECK_GATE = 'scripts/coord-tools/gate.sh'
LEAN_CHECK_DRIVER_LINE = 'bash scripts/coord-tools/gate.sh per-file "${files[@]}"'
LEAN_CHECK_GATE_BRANCH = 'if [ "$mode" = per-file ]; then'
LEAN_CHECK_GATE_LINE = '  for file in "${files[@]}"; do run_gate "lean:$file" lake lean "$file" -- --tstack=131072; done'
lean_check_command = lambda path: ['lake', 'lean', path, '--', '--tstack=131072']
# Reviewed sources (path, blob, introducing commit) and invocations (path,
# blob, driver, driver blob, gate line); each driver is a reviewed H997 entry.
# read-bounds-validate.sh is not reviewed: a top-level exec hands its gate line
# to validation-admission.py's recipe runner, which this audit does not follow.
REVIEWED_LEAN_CHECKS = frozenset({
    ('tests/directruntime-20261104/control-tuples/ProofAudit.lean', 'c60ce39b40db0e4a797d0afa4c1a8f14c40df466', 'e6849d3bdf516099d20c33d3581d523449764018'),
})
REVIEWED_LEAN_CHECK_INVOCATIONS = frozenset(
    ('tests/directruntime-20261104/control-tuples/ProofAudit.lean', 'c60ce39b40db0e4a797d0afa4c1a8f14c40df466', 'tests/directruntime-20261104/shared-translator/' + d, b, n)
    for d, b, n in (('address-validate.sh', '6f9014aa569e25b415aba09f7ef1c37f4a4dd3ea', 20),
                    ('environment-validate.sh', '9460e5febcad1c954204902e5b7a505c5a5f79da', 21),
                    ('fixed-byte-validate.sh', 'b4d495f62a04cab7ec344489563d20f63f832f33', 17),
                    ('h90-validate.sh', 'a67ec66c28490d60be84f27466897389d27dc82c', 17),
                    ('primitive-return-validate.sh', '074e6d15f01d4bfd67c2bd0af103663f96231923', 17)))
_LEAN_NAME = r"[A-Za-z_][\w']*(?:\.[A-Za-z_][\w']*)*"


def lean_check_interface(lean_code, path, text):
    """Header imports and the lines of `#check [@]NAME` and `#print axioms NAME`,
    or None. Every other line is blank or comment only: any other command or
    declaration (#eval, run_cmd, set_option, open, def, ...), a term that is
    not one identifier, an indented or continued line, a late import, a
    double quote, ambiguous line breaks, NUL or no check command gives None."""
    if not path.endswith('.lean') or not isinstance(text, str) or not _plain_lines(text) or '\0' in text: return None
    code = lean_code(text)
    if code.count('\n') != text.count('\n'): return None
    imports, checks, axioms = [], [], []
    for n, (line, raw) in enumerate(zip(code.split('\n'), text.split('\n')), 1):
        line = line.rstrip()
        if '"' in raw: return None
        if not line: continue
        match = re.fullmatch(r'import((?:[ \t]+' + _LEAN_NAME + r')+)', line)
        if not raw.startswith(line) or match and (checks or axioms): return None
        if match: imports.extend(match[1].split())
        elif re.fullmatch(r'#check[ \t]+@?' + _LEAN_NAME, line): checks.append(n)
        elif re.fullmatch(r'#print[ \t]+axioms[ \t]+' + _LEAN_NAME, line): axioms.append(n)
        else: return None
    return {'imports': imports, 'check_lines': checks, 'axiom_lines': axioms} if checks or axioms else None


def lean_check_invocation(text, path, line):
    """The driver reaches its column-0 LEAN_CHECK_DRIVER_LINE with path listed.

    Before it: balanced quotes per line; no continuation, here-document, exec,
    cd, PATH change, function, other builtin listed below, or compound command
    but column-0 `for ...; do`/`done`; `files` only as a whole-line files=(...)
    or files+=(...) without ; # ( ), reset only at column 0, path an unquoted
    word of a later column-0 assignment. Lexical; the review set gates."""
    if not isinstance(text, str) or not _plain_lines(text) or '\0' in text: return False
    lines = text.split('\n')
    if type(line) is not int or not 1 <= line <= len(lines) or lines[line - 1] != LEAN_CHECK_DRIVER_LINE: return False
    depth = 0; named = None
    for n, raw in enumerate(lines[:line - 1], 1):
        if n == 1 and raw.startswith('#!') or not raw.strip() or raw.strip().startswith('#'): continue
        try: shlex.split(raw, comments=True)
        except ValueError: return False
        if '<<' in raw or '`' in raw or raw.rstrip().endswith('\\') or '$(' in raw and re.search(r'(?<![\w$-])files\b', raw): return False
        if re.search(r'(?<![\w$-])(?:exec|exit|return|source|eval|trap|alias|hash|kill|declare|typeset|local|readonly|unset|builtin|command|enable|cd|pushd|popd|function|if|then|else|elif|fi|while|until|case|esac|select|shift)(?![\w-])'
                     r'|^\s*\.\s|(?<![\w$])PATH\+?=|\w\s*\(\s*\)|[{}]|&&|\|\||;\s*$|(?:^|[;&|]\s*)\(', raw): return False
        if re.match(r'for\s', raw):
            if depth or not re.search(r';\s*do\s*$', raw): return False
            depth = 1; continue
        if re.fullmatch(r'done\s*', raw):
            if not depth: return False
            depth = 0; continue
        if re.search(r'(?<![\w$-])do(?![\w-])', raw): return False
        if not re.search(r'(?<![\w$/-])files(?![\w./-])', raw): continue
        match = re.fullmatch(r'(\s*)files(\+?)=\(([^;#()]*)\)\s*', raw)
        if match is None or not match[2] and match[1] or not match[1] and re.search('["\'$]', match[3]): return False
        try: words = shlex.split(match[3])
        except ValueError: return False
        if not match[2]: named = False
        if not match[1] and not depth and path in words: named = True
    return depth == 0 and named is True


LEAN_FIXTURE_KIND = 'lean-fixture-source-role'
LEAN_FIXTURE_PREFIX = 'lean-fixture:'
# H1015 (gh#1359, X1E-LEAN-FIXTURE-REMAINDER, Option A): Lean fixture sources
# (definitions, #eval, examples, run_elab or main) that a reviewed H997 driver
# hands to the same gate.sh per-file line, audited one by one. Sources
# (path, blob, introducing commit) and invocations (path, blob, driver, driver
# blob, driver line), as for H999. Consumption only: no elaboration, pass,
# read, import, proof or runtime credit.
REVIEWED_LEAN_FIXTURES = _review_table('''
@0834bc67b042a63a8c804162781802245ae59c98
D:shared-translator/AddressLocalControls.lean 1b967893ecac51c9e5dfb437dd3596febd1ad291
@2366c57f099b27d4673dda504d258ba77ff3fcaf
D:control-tuples/ProductionControls.lean ca25c4ca010fa72c0512c2b7523fabcccbbad7e7
@44d89439afd8fe7aca251cd5693b5b7ea36cf603
D:shared-translator/EnvironmentMemberControls.lean 5180d8e8c04ac5e1e86ed13c4fef65f801c5afa0
@4a66db87c8ed848aef4c2ac1732b1df326c6fa97
D:shared-translator/FixedByteLocalControls.lean 49901e395dd580a8682dfdaa1dc38c610b3fad54
@957e5defaa3c2e32df1e692d8781e0d89fed5199
D:control-tuples/ObligationControls.lean 4195775c23abafdc47ec3ebabe1a6e011e3777cb
D:shared-translator/PrimitiveReturnControls.lean 73cb82f3ed73ec1ba4e0e69fb591f347fd6c3d0d
@b44f0de87c2ab845b79c9d84004dcb7c91babded
D:shared-translator/H90Census.lean e41529cb06d93c593259cb2714d02c51fd96a022
''')
# The H999 driver lines (address 20, environment 21, others 17); each driver
# lists the source in a column-0 files+=(...) word before its gate line.
_LEAN_GATE_DRIVERS = {d: (b, n) for _, _, d, b, n in REVIEWED_LEAN_CHECK_INVOCATIONS}
REVIEWED_LEAN_FIXTURE_INVOCATIONS = frozenset(
    (p, b, 'tests/directruntime-20261104/shared-translator/' + d + '-validate.sh') + _LEAN_GATE_DRIVERS['tests/directruntime-20261104/shared-translator/' + d + '-validate.sh']
    for p, b, _ in REVIEWED_LEAN_FIXTURES for d in {
        'ObligationControls': 'address environment fixed-byte h90 primitive-return', 'ProductionControls': 'address environment fixed-byte h90 primitive-return',
        'AddressLocalControls': 'address environment', 'EnvironmentMemberControls': 'environment', 'FixedByteLocalControls': 'address environment fixed-byte',
        'H90Census': 'address environment', 'PrimitiveReturnControls': 'address environment fixed-byte primitive-return'}[posixpath.basename(p)[:-5]].split())


# Column-0 commands that make a body a fixture (declaration, evaluation, elaboration).
FIXTURE_COMMAND = (r'(?:@\[[^\]]*\][ \t]*)?(?:(?:private|protected|noncomputable|partial|unsafe|nonrec)[ \t]+)*'
                   r'(?:def|theorem|lemma|abbrev|instance|structure|inductive|class|example|opaque|axiom|#eval|#guard|#reduce'
                   r'|run_elab|run_cmd|run_meta|elab|macro|syntax|macro_rules|elab_rules)(?![\w.\'])')


def lean_fixture_interface(lean_code, path, text):
    """Header imports and the first body line of a Lean fixture source, or None.

    Only column-0 `import NAMES` lines and blank or comment lines precede the
    body; the body follows at least one import and holds no later import,
    prelude or module line and no #exit anywhere. The body must hold a
    column-0 declaration or evaluation command (FIXTURE_COMMAND), so a source
    of only #check/#print/open/set_option lines is never a fixture, whether or
    not the H999 grammar accepts it. NUL or ambiguous line breaks give None."""
    if not path.endswith('.lean') or not isinstance(text, str) or not _plain_lines(text) or '\0' in text: return None
    code = lean_code(text)
    if code.count('\n') != text.count('\n') or lean_check_interface(lean_code, path, text) is not None: return None
    if re.search(r'#exit(?![\w.\'])', code): return None
    imports, body, command = [], None, False
    for n, (line, raw) in enumerate(zip(code.split('\n'), text.split('\n')), 1):
        line = line.rstrip()
        if not line: continue
        header = re.match(r'\s*(?:(?:public|private|meta)\s+)*(?:import|prelude|module)(?![\w.\'])', line)
        match = re.fullmatch(r'import((?:[ \t]+' + _LEAN_NAME + r')+)', line)
        if body is None and match and raw.startswith(line) and 'all' not in match[1].split(): imports.extend(match[1].split()); continue
        if header: return None
        if body is None: body = n
        command = command or re.match(FIXTURE_COMMAND, line) is not None
    return {'imports': imports, 'body_line': body} if imports and body and command else None


LEAN_CHECK_FORM = {'role': 'Lean check role', 'shape': 'check-only', 'interface': lean_check_interface, 'prefix': LEAN_CHECK_PREFIX,
    'flag': 'lean_check_role', 'source': 'Lean check source',
    'reason': 'Reviewed Lean check source run by reviewed drivers via gate.sh per-file; never run or certified to elaborate or pass. No execution, read, fixture, helper, import-dependency, output, proof or runtime credit.'}
LEAN_FIXTURE_FORM = {'role': 'Lean fixture role', 'shape': 'fixture', 'interface': lean_fixture_interface, 'prefix': LEAN_FIXTURE_PREFIX,
    'flag': 'lean_fixture_role', 'source': 'Lean fixture source',
    'reason': 'Reviewed Lean fixture source (definitions, #eval, examples, run_elab or main) consumed by reviewed drivers via gate.sh per-file; never run or certified to elaborate or pass. Consumption role only: no execution, read, fixture-read, helper, import-dependency, output, proof or runtime credit.'}


def _lean_gate_root(classifier, graph, catalog, entry, reviewed, invocations, form):
    """H999/H1015: a reviewed live non-root Lean source run by gate.sh per-file.

    Binds lean_check_command(P), the blob, its interface (form['interface']),
    the reviewed introducing commit and each invocation: a reviewed H997
    driver (blob, commit) whose gate line runs P. P is under tests/; a Lake
    package, root library, importer or changed gate.sh per-file line makes it
    stale. Never a validated runner; anchors nothing. Kept later while source
    and drivers are unchanged; a current definition of the path supersedes it."""
    repo = graph.repo; role = form['role']
    required = {'path', 'input_revision', 'source_blob', 'command', 'kind', 'interface', 'provenance', 'invocations', 'purpose'}
    _role_schema(classifier, catalog, entry, required, role); calls = entry['invocations']
    if (not isinstance(calls, list) or not calls or any(not isinstance(c, dict) or set(c) != {'driver', 'driver_blob', 'driver_commit', 'line'} or type(c['line']) is not int
                   or not all(isinstance(c[k], str) for k in ('driver', 'driver_blob', 'driver_commit')) for c in calls)
            or len({canonical(c) for c in calls}) != len(calls)):
        raise ValueError('invalid ' + role + ' definition')
    p = entry['path']; revision = entry['input_revision']; doc = entry['provenance']; blob = entry['source_blob']
    if entry['command'] != lean_check_command(p) or not p.endswith('.lean') or not p.startswith('tests/') or _clean(p) != p:
        raise ValueError('unsupported ' + role + ' invocation: ' + p)
    if doc['path'] != p or doc['blob'] != blob or (p, blob, doc['commit']) not in reviewed: raise ValueError('unreviewed ' + role + ': ' + p)
    if any((p, blob, c['driver'], c['driver_blob'], c['line']) not in invocations or not c['driver'].endswith('.sh')
           or (c['driver'], c['driver_blob'], c['driver_commit']) not in REVIEWED_NONPY_ENTRIES for c in calls):
        raise ValueError('unreviewed ' + role + ' invocation: ' + p)
    pins = [(p, blob)] + [(c['driver'], c['driver_blob']) for c in calls]
    if not _role_current(classifier, repo, catalog, entry, pins): return
    if repo.tree[p][0] != '100644' or p not in repo.texts or any(repo.tree[c['driver']][0] not in ('100644', '100755') for c in calls):
        raise ValueError('unsupported ' + role + ' invocation: ' + p)
    if not _introduced(classifier, repo, doc['commit'], p, blob): raise ValueError(role + ' lacks its introducing provenance: ' + p)
    if not all(_introduced(classifier, repo, c['driver_commit'], c['driver'], c['driver_blob']) for c in calls):
        raise ValueError(role + ' driver lacks its introducing provenance: ' + p)
    # Lake packages, root libraries and importers are not pinned: they make the role stale.
    parts = p.split('/')
    if (any('/'.join(parts[:k]) + '/' + name in repo.tree for k in range(1, len(parts)) for name in ('lakefile.toml', 'lakefile.lean'))
            or 'lakefile.lean' in repo.tree or not _outside_root_libraries(repo, p)
            or any(e['target'] == p and e['operation'] == 'Lean import' for edges in graph.edges.values() for e in edges)): return
    interface = form['interface'](classifier['lean_code'], p, repo.texts[p])
    if interface is None: raise ValueError(role + ' lacks an audited ' + form['shape'] + ' interface: ' + p)
    if canonical(interface) != canonical(entry['interface']): raise ValueError(role + ' interface mismatch: ' + p)
    for c in calls:
        if c['driver'] not in repo.texts or nonpython_entry_interface(c['driver'], repo.texts[c['driver']]) is None:
            raise ValueError(role + ' driver lacks an audited entry interface: ' + c['driver'])
        if not lean_check_invocation(repo.texts[c['driver']], p, c['line']): raise ValueError(role + ' driver does not run the source: ' + c['driver'])
    if '\n' + LEAN_CHECK_GATE_BRANCH + '\n' + LEAN_CHECK_GATE_LINE + '\n' not in repo.texts.get(LEAN_CHECK_GATE, ''): return
    identity = form['prefix'] + p
    graph.root(p, 'source-only ' + form['source'], shlex.join(entry['command']), calls[0]['driver'], calls[0]['line'], root_id=identity)
    if identity not in graph.roots: return
    graph.roots[identity].update({'source_only': True, form['flag']: True, 'source_blob': blob, 'purpose': entry['purpose'],
        'interface': interface, 'provenance': doc, 'invocations': calls, 'source_declaration_revision': revision,
        'validation_at_measured_revision': {'status': 'unavailable', 'command': entry['command'], 'reason': form['reason']}})


def lean_check_root(classifier, graph, catalog, entry, reviewed=None, invocations=None):
    """H999: a reviewed live non-root Lean check source as a source-only role."""
    _lean_gate_root(classifier, graph, catalog, entry, REVIEWED_LEAN_CHECKS if reviewed is None else reviewed,
                    REVIEWED_LEAN_CHECK_INVOCATIONS if invocations is None else invocations, LEAN_CHECK_FORM)


def lean_fixture_root(classifier, graph, catalog, entry, reviewed=None, invocations=None):
    """H1015: a reviewed live non-root Lean fixture source as a source-only role.

    The H999 rules with lean_fixture_interface: consumption by its drivers
    only, never a check-only source and never elaboration, pass or proof."""
    _lean_gate_root(classifier, graph, catalog, entry, REVIEWED_LEAN_FIXTURES if reviewed is None else reviewed,
                    REVIEWED_LEAN_FIXTURE_INVOCATIONS if invocations is None else invocations, LEAN_FIXTURE_FORM)


def _outside_root_libraries(repo, path):
    """No root lakefile*.toml library or executable can name path's module."""
    import tomllib
    top = path.split('/')[0]
    for name in sorted(n for n in repo.texts if '/' not in n and re.fullmatch(r'lakefile.*\.toml', n)):
        try: config = tomllib.loads(repo.texts[name])
        except ValueError: return False
        for target in config.get('lean_lib', []) + config.get('lean_exe', []):
            source = target.get('srcDir', '.') if isinstance(target, dict) else None
            if not isinstance(source, str): return False
            source = posixpath.normpath(source)
            if source != '.':
                if path.startswith(source + '/') or source.startswith(('..', '/')): return False
                continue
            lists = [target.get(k, []) for k in ('roots', 'globs')]
            if any(not isinstance(x, list) for x in lists): return False
            names = [target.get('name'), target.get('root')] + lists[0] + lists[1]
            if any(not isinstance(n, str) or n.split('.')[0] in (top, '*', '+') for n in names if n is not None): return False
    return True


def lean_fixture_controls(env):
    """(9) H1015 controls, run by successor_controls with its helpers: the
    reviewed set, the fixture interface, the role and its negative controls."""
    global REVIEWED_LEAN_FIXTURES, REVIEWED_LEAN_FIXTURE_INVOCATIONS, REVIEWED_NONPY_ENTRIES
    commit, run, rejected, blob, route, frame, gate, reviewed_nonpy, files = (env[k] for k in (
        'commit', 'run', 'rejected', 'blob', 'route', 'frame', 'gate', 'reviewed_nonpy', 'files'))
    code = env['classifier']['lean_code']
    # The audited witnesses: 7 sources, 22 driver lines, all reviewed H997 drivers, disjoint from H999.
    assert len(REVIEWED_LEAN_FIXTURES) == 7 and len(REVIEWED_LEAN_FIXTURE_INVOCATIONS) == 22
    assert {(p, b) for p, b, _ in REVIEWED_LEAN_FIXTURES} == {(p, b) for p, b, _, _, _ in REVIEWED_LEAN_FIXTURE_INVOCATIONS}
    assert not {p for p, _, _ in REVIEWED_LEAN_FIXTURES} & {p for p, _, _ in REVIEWED_LEAN_CHECKS}
    assert all((d, db) in {(q, b) for q, b, _ in reviewed_nonpy} and (d, db, n) in {(d, b, n) for _, _, d, b, n in REVIEWED_LEAN_CHECK_INVOCATIONS}
               for _, _, d, db, n in REVIEWED_LEAN_FIXTURE_INVOCATIONS)
    assert ('tests/directruntime-20261104/control-tuples/ProductionControls.lean', 'ca25c4ca010fa72c0512c2b7523fabcccbbad7e7',
            '2366c57f099b27d4673dda504d258ba77ff3fcaf') in REVIEWED_LEAN_FIXTURES
    G, X = LEAN_CHECK_DRIVER_LINE, 'tests/f/F.lean'
    fixture = 'import Lib.Mod tests.f.Dep\n-- fixture\n\ndef F.v : Nat := 1\n#eval IO.FS.readFile "tests/data.txt"\ntheorem F.t : F.v = 1 := rfl\n'
    check = 'import Lib.Mod\n#check D.v\n'
    face = {'imports': ['Lib.Mod', 'tests.f.Dep'], 'body_line': 4}
    assert lean_fixture_interface(code, X, fixture) == face
    assert lean_fixture_interface(code, X, 'import A B -- c\n/- x -/\nrun_elab pure ()\n') == {'imports': ['A', 'B'], 'body_line': 3}
    assert lean_fixture_interface(code, X, 'import A\nopen A\n@[simp] private def x := 1\n#check x\n') == {'imports': ['A'], 'body_line': 2}
    for t in ('', 'import A\n', '-- c\n', 'def x := 1\n', fixture + 'import B\n', 'prelude\n' + fixture, fixture.replace('-- fixture', 'module'),
              fixture + '#exit\n', fixture + '  #exit\n', ' import A\n#eval 1\n', 'import A\r\n#eval 1\n', fixture + '\0\n', 'import A.\n#eval 1\n',
              check, 'import A\n#print axioms A\n', fixture.replace('\n', '\n\x0b', 1), 'import A\n#check Foo -- see "x"\n',
              'import A\n#check (Foo)\n', 'import A\nopen A\n#check Foo\n', 'import A\nset_option x true\n#print A\n', 'import A\n  def x := 1\n',
              'import A\ndef x := 1 #exit\n', 'import A\nset_option x true in #exit\n#eval 1\n', 'import all A\n#eval 1\n', 'import A\n#evaluate 1\n'):
        assert lean_fixture_interface(code, X, t) is None, t
    assert lean_fixture_interface(code, 'x.py', fixture) is None and lean_check_interface(code, X, fixture) is None
    head = '#!/usr/bin/env bash\nset -euo pipefail\nfiles=(tests/f/F.lean tests/f/C.lean tests/f/I.lean tests/f/X.lean tests/fpkg/F.lean)\n'
    driver = head + G + '\n'; gl = 4
    add = {'scripts/coord-tools/gate.sh': gate, 'tests/f/run.sh': driver, 'tests/f/exec.sh': driver.replace('set -euo pipefail\n', 'exec true\n'),
           X: fixture, 'tests/f/Dep.lean': 'def Dep.v : Nat := 1\n', 'tests/f/C.lean': check, 'tests/f/I.lean': fixture, 'tests/f/J.lean': 'import tests.f.I\n',
           'tests/f/X.lean': fixture + '#exit\n', 'tests/fpkg/lakefile.toml': 'name = "fpkg"\n', 'tests/fpkg/F.lean': fixture}
    lf = commit(add, 'Lean fixtures'); L = lf.ref; ll = commit({'tests/unrelated.txt': 'F\n'}, 'Lean fixtures later')
    assert lean_check_invocation(driver, X, gl) and not lean_check_invocation(add['tests/f/exec.sh'], X, gl)
    call = lambda d='tests/f/run.sh', **k: dict({'driver': d, 'driver_blob': blob(lf, d), 'driver_commit': L, 'line': gl}, **k)
    mk = lambda p=X, kind=LEAN_FIXTURE_KIND, interface=face: {
        'path': p, 'input_revision': L, 'source_blob': blob(lf, p), 'kind': kind, 'command': lean_check_command(p), 'interface': interface,
        'provenance': {'commit': L, 'path': p, 'blob': blob(lf, p)}, 'invocations': [call()], 'purpose': 'Synthetic fixture.'}
    role = mk(); base_model, base = run(ll, entries=[])
    assert base[X]['class'] != 'keep' and base['tests/f/Dep.lean']['class'] != 'keep'
    srcs = (X, 'tests/f/C.lean', 'tests/f/I.lean', 'tests/f/X.lean', 'tests/fpkg/F.lean')
    drivers = {(d, blob(lf, d), L) for d in ('tests/f/run.sh', 'tests/f/exec.sh')}
    saved = REVIEWED_LEAN_FIXTURES, REVIEWED_LEAN_FIXTURE_INVOCATIONS, REVIEWED_NONPY_ENTRIES
    REVIEWED_LEAN_FIXTURES = frozenset({(p, blob(lf, p), L) for p in srcs})
    REVIEWED_LEAN_FIXTURE_INVOCATIONS = frozenset({(p, blob(lf, p), d, blob(lf, d), gl) for p in srcs for d in ('tests/f/run.sh', 'tests/f/exec.sh')})
    REVIEWED_NONPY_ENTRIES = reviewed_nonpy | drivers
    try:
        for repo in (lf, ll):
            model, rows = run(repo, standalone=[role]); entry = model['entry_points']['lean-fixture:' + X]
            assert rows[X]['class'] == 'keep' and entry['source_only'] and entry['lean_fixture_role'] and not entry.get('lean_check_role')
            assert entry['validation_at_measured_revision']['status'] == 'unavailable' and entry['location'] == 'tests/f/run.sh:%d' % gl
            assert entry['command'] == 'lake lean tests/f/F.lean -- --tstack=131072' and entry['invocations'] == role['invocations']
            assert entry['interface'] == face and entry['provenance'] == role['provenance']
            if repo is ll:  # no import-dependency, driver, read, proof or runtime credit
                assert all(canonical(r) == canonical(base[p]) for p, r in rows.items() if p != X)
                assert set(model['entry_points']) == set(base_model['entry_points']) | {'lean-fixture:' + X}
        _, rows = run(ll, {'static_routes': [route(lf, 'lean-fixture:' + X, 'lean-readFile', [frame(lf, X, 5)], 'tests/data.txt')]}, standalone=[role])
        assert rows['tests/data.txt']['class'] != 'keep'
        Z = '0' * 40
        for change, text in (({'extra': 1}, 'invalid Lean fixture'), ({'purpose': ' '}, 'invalid Lean fixture'), ({'invocations': []}, 'invalid Lean fixture'),
                             ({'invocations': [call(), call()]}, 'invalid Lean fixture'), ({'invocations': [call(line=str(gl))]}, 'invalid Lean fixture'),
                             ({'invocations': [call(command=['bash'])]}, 'invalid Lean fixture'), ({'provenance': {'commit': L}}, 'invalid Lean fixture'),
                             ({'input_revision': 'HEAD'}, 'full commit revision'), ({'command': ['lean', X]}, 'unsupported Lean fixture role invocation'),
                             ({'command': ['lake', 'env', 'lean', X]}, 'unsupported Lean fixture role invocation'),
                             ({'command': lean_check_command(X) + ['x']}, 'unsupported Lean fixture role invocation'),
                             ({'source_blob': Z}, 'unreviewed Lean fixture role'), ({'provenance': dict(role['provenance'], commit=Z)}, 'unreviewed Lean fixture role'),
                             ({'invocations': [call(line=gl - 1)]}, 'role invocation'), ({'invocations': [call(driver_blob=Z)]}, 'role invocation'),
                             ({'invocations': [call(driver_commit=Z)]}, 'role invocation'),
                             ({'invocations': [call(), call('tests/f/exec.sh')]}, 'Lean fixture role driver does not run the source'),
                             ({'interface': dict(face, body_line=2)}, 'Lean fixture role interface mismatch'),
                             ({'interface': {'imports': ['Lib.Mod'], 'check_lines': [2], 'axiom_lines': []}}, 'interface mismatch'),
                             ({'input_revision': Z}, 'unverifiable historical')):
            rejected(lf, text, standalone=[dict(role, **change)])
        rejected(lf, 'conflicting standalone', standalone=[role, dict(role, purpose='Other.')])
        # One path, one role: a check-only source is never a fixture; a fixture is never a check role.
        rejected(lf, 'conflicting standalone', standalone=[role, mk(kind=LEAN_CHECK_KIND)])
        rejected(lf, 'audited fixture interface', standalone=[mk('tests/f/C.lean')])
        rejected(lf, 'audited fixture interface', standalone=[mk('tests/f/X.lean')])
        rejected(lf, 'unreviewed Lean check role', standalone=[mk(kind=LEAN_CHECK_KIND)])
        for path in ('tests/f/I.lean', 'tests/fpkg/F.lean'):  # importer, Lake package: stale
            assert 'lean-fixture:' + path not in run(lf, standalone=[mk(path)])[0]['entry_points']
        REVIEWED_NONPY_ENTRIES = reviewed_nonpy
        rejected(lf, 'unreviewed Lean fixture role invocation', standalone=[role])
        REVIEWED_NONPY_ENTRIES = reviewed_nonpy | {('tests/f/run.sh', blob(lf, 'tests/f/run.sh'), env['A'])}
        rejected(lf, 'Lean fixture role driver lacks its introducing provenance', standalone=[dict(role, invocations=[call(driver_commit=env['A'])])])
        REVIEWED_NONPY_ENTRIES = reviewed_nonpy | drivers
        for order in (1, -1):  # a current definition supersedes
            model, _ = run(ll, standalone=[dict(role, input_revision=ll.ref, purpose='Now.'), role][::order])
            assert model['entry_points']['lean-fixture:' + X]['purpose'] == 'Now.'
        writer = {'path': X, 'blob': blob(lf, X), 'line': 5, 'literal': 'out.json'}
        policy = {'path': 'tests/gen/.gitignore', 'blob': blob(lf, 'tests/gen/.gitignore'), 'purpose': 'P.', 'matches': [{'line': 1, 'output': 'out.json', 'writer': writer}]}
        rejected(lf, 'not an entry point source', {'git_policies': [policy]}, standalone=[role])
        # A root library, changed gate.sh, source or driver drops the root later; a current claim on changed bytes is refused.
        for changes in ({'lakefile.toml': files['lakefile.toml'] + '[[lean_lib]]\nname = "tests"\n'}, {'scripts/coord-tools/gate.sh': gate.replace('131072', '65536')},
                        {X: fixture + '#eval 2\n'}, {'tests/f/run.sh': driver + 'echo\n'}, {'tests/f/J.lean': 'import tests.f.F\n'}):
            edited = commit(changes, 'edited')
            model, rows = run(edited, standalone=[role])
            assert 'lean-fixture:' + X not in model['entry_points'] and rows[X]['class'] != 'keep', changes
            if X in changes or 'tests/f/run.sh' in changes: rejected(edited, 'source mismatch', standalone=[dict(role, input_revision=edited.ref)])
            commit({'scripts/coord-tools/gate.sh': gate, X: fixture, 'tests/f/run.sh': driver, 'tests/f/J.lean': 'import tests.f.I\n',
                    'lakefile.toml': files['lakefile.toml']}, 'restored')
        REVIEWED_LEAN_FIXTURES = frozenset()
        rejected(lf, 'unreviewed Lean fixture role', standalone=[role])
    finally: REVIEWED_LEAN_FIXTURES, REVIEWED_LEAN_FIXTURE_INVOCATIONS, REVIEWED_NONPY_ENTRIES = saved
