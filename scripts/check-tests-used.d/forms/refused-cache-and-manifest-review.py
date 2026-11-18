# H1221 (gh#1533, H62-FINAL-REFUSED-DISPOSITION, Option B) census form (planned as h62-refused-forms-review.py; named
# after its content because the hygiene path check refuses an h62 segment, as for implicit-cache-and-manifest-roles.py):
# the second review of the exact refused producer and input forms of the ten scripts/h62 paths that H1203 (x1af-rest)
# left unresolved. Exec'd by registry.py in the namespace of fragments.py (see registry.py's header) after the other
# forms; it registers no source-role kind, no consumer section, no review table part and no argument form, only one
# control, and binds no shared name. Every classification and output byte is unchanged with or without it.
#
# Outcome at RR_BASE: none of the ten is admitted. Each path was reviewed case by case against every committed launch
# of a Python program in its directory (RR_CANDIDATES: each interpreter-headed argument list without an interpreter
# option, found by the syntax scan rr_interpreter_lists over every .py blob of the nine directories; RR_OPTIONED: the
# lists that pass -B, -c or -m), the H1053 guards (roles.py) and the H1203 launch and import forms
# (implicit-cache-and-manifest-roles.py), all kept unchanged. A role needs one exact real producer: a kept python3 -B
# entry root reaching a bytecode-enabled child launch of a program that imports a module of the policy directory, or,
# for the manifest, a committed binding of its exact path. Refused, left unresolved (reported back, never classified):
#   audit-abi-world (interpreter-option): every launch of a Python program passes -B (measure, resume_measure,
#     receipts, resume_accept, test_bounded, test_coverage) or runs -c code; no bytecode-enabled program launch.
#   audit-evm-compiler (policy-rules): *.olean and *.ilean are no CPython cache rules (H1053 narrow-role guard). Its
#     six bytecode-enabled launches of bounded.py (build_census:37, check_memory_premises:53, closed_census:28,
#     inspect:16, inspect_bridge:20, measure:6) match no launch form and bounded.py imports no sibling module.
#   audit-yul (no-sibling-import): generate.py:15,34 and test_staleness.py:17 launch check_serial.py, census.py and
#     acceptance.py with a bare 'python3' and a cwd-relative path (no launch form); none of the three imports a sibling
#     module. generate.py itself imports census (line 4) but is no kept root and no committed text invokes it.
#   migrate-backend, migrate-counterexamples, migrate-solkey (no-program-launch): no Python program launch at all
#     (backend's only interpreter use is `-m lean_lsp_mcp`, a non-sibling module, through StdioServerParameters). Their
#     sibling importers (backend capture_root_exit_proposal, check_fixture_mcp, reconcile_imports; counterexamples
#     measure, summarize; solkey measure) are no kept roots, and the tests that load modules by file location run in
#     python3 -B roots.
#   migrate-corpus (no-sibling-import): acceptance.py:23,28,47,71 launch bounded.py and compare.py; neither imports a
#     sibling module (bounded.py also names ctypes); acceptance.py loads census.py by file location but is no kept root
#     and no committed text invokes it.
#   migrate-frontend (argument-module): measure.py:222 relaunches `__file__` (no launch form; driver = program) and the
#     worker loads its module from Path(sys.argv[2]), no exact binding; the launch sits in SignalRaceTest, reached only
#     under a `--signal-test` argument that no kept root or committed invocation passes (the kept root
#     `python3 -B .../measure.py` runs main()).
#   migrate-testsuite (environment-mapping): export-interfaces.py:18 launches generate-interface.py (static sibling
#     import of expr_dag at line 8) with env=env, a copied and edited os.environ mapping (outside the H1053 env-keyword
#     guard and every H1203 form), and export-interfaces.py is no kept root and no committed text invokes it.
#   audit-theories/handoff/scope-manifest.json (argument-repository): paired_evidence.py export reads it only as
#     a.current_repository/HISTORICAL_INPUT_PREFIX/name, the argument-supplied --current-repository, with no size and
#     SHA-256 pin (HISTORICAL_PINS holds the other three records); the only other committed reader,
#     test_current_replay.py, writes a synthetic stand-in; no committed invocation binds the argument to this
#     checkout. No exact binding (H1113/H1203 exact-binding rule).
# Documentation commands (docs/feature-work) are no kept roots (_entry_root refuses documentation reference roles);
# the bytecode-enabled ones there (abi-world census.py, yul record_h69/census/acceptance) import no sibling module.
# The control re-derives every refusal on the pinned blobs when RR_BASE is held, exercises each refused shape against
# the H1203 recognisers next to an accepted twin, and checks that rows claiming the ten paths are refused by the H1053,
# H1203 and H1113 handlers. Source-only limits unchanged: no consumer, invocation, pass or proof credit is granted.
import ast
import posixpath
from pathlib import Path

RR_BASE = '57c3b2f77d4b62bb9373286447fd344d6b7dc746'
_RR2, _RR6 = 'scripts/h62/item2/', 'scripts/h62/item6/'
_RR_PLAIN = 'c18dd8d83ceed1806b50b0aaa46beb7e335fff13'  # '__pycache__/\n'
RR_REASONS = {
    'interpreter-option': 'every Python program launch passes an interpreter option (-B) or runs -c code',
    'policy-rules': 'the policy holds rules outside the CPython cache rules',
    'no-sibling-import': 'no bytecode-enabled launched program imports a module of the policy directory',
    'no-program-launch': 'no committed launch of a Python program; sibling importers are no kept roots',
    'argument-module': 'the relaunched child loads its module from an argument path, on a branch no kept root takes',
    'environment-mapping': 'the only sibling-importing child is launched with an env= mapping by a driver that is no kept root',
    'argument-repository': 'read only below the argument-supplied --current-repository, unpinned and bound by no committed invocation',
}
# path -> (blob at RR_BASE, reason)
RR_REFUSED = {
    _RR2 + 'audit-abi-world/.gitignore': (_RR_PLAIN, 'interpreter-option'),
    _RR2 + 'audit-evm-compiler/.gitignore': ('7103ca592fe949a192db5c692ad868710d5c6832', 'policy-rules'),
    _RR2 + 'audit-yul/.gitignore': (_RR_PLAIN, 'no-sibling-import'),
    _RR6 + 'migrate-backend/.gitignore': (_RR_PLAIN, 'no-program-launch'),
    _RR6 + 'migrate-corpus/.gitignore': ('7a60b85e148f80966a550e5ab6a762a907c69ca6', 'no-sibling-import'),
    _RR6 + 'migrate-counterexamples/.gitignore': (_RR_PLAIN, 'no-program-launch'),
    _RR6 + 'migrate-frontend/.gitignore': (_RR_PLAIN, 'argument-module'),
    _RR6 + 'migrate-solkey/.gitignore': (_RR_PLAIN, 'no-program-launch'),
    _RR6 + 'migrate-testsuite/.gitignore': (_RR_PLAIN, 'environment-mapping'),
    _RR2 + 'audit-theories/handoff/scope-manifest.json': ('7956f6dcdbf2390caba66f9128e6d67ebf4dcea1', 'argument-repository'),
}
_EVM, _YUL, _COR = _RR2 + 'audit-evm-compiler/', _RR2 + 'audit-yul/', _RR6 + 'migrate-corpus/'
_FRO, _TST = _RR6 + 'migrate-frontend/', _RR6 + 'migrate-testsuite/'
_EVM_BOUNDED = (_EVM + 'bounded.py', 'b2fd29a6c9b8067e3f9351b502dca9d6ce8de00d', ())
# (driver, driver blob, line, program, program blob, sibling import lines of the program) at RR_BASE
RR_CANDIDATES = frozenset({
    (_EVM + 'build_census.py', '2113ef6716311a8cb78df04bcd421a6262bd9862', 37, *_EVM_BOUNDED),
    (_EVM + 'check_memory_premises.py', '1e28065b82cb401921e43d53ee530df9c3046213', 53, *_EVM_BOUNDED),
    (_EVM + 'closed_census.py', '3798c99de0c5773d733ed69ef2a9af0c422f94a3', 28, *_EVM_BOUNDED),
    (_EVM + 'inspect.py', '3884ee420a9a9cfccd9d76388e6a06f243d551ce', 16, *_EVM_BOUNDED),
    (_EVM + 'inspect_bridge.py', '12276aaf30cbd92d243a1e4d9e9b905e986e3d63', 20, *_EVM_BOUNDED),
    (_EVM + 'measure.py', '7d2c9a7d2132df4f5c4267d4646e8fe1e1ea45f1', 6, *_EVM_BOUNDED),
    (_YUL + 'generate.py', 'ddf28646ad7c6adfbfbfbbc92a52dcbceeba86ff', 15, _YUL + 'check_serial.py', '696c8ed780f6d7cd4c9eb1ac5d01b268ec4351a3', ()),
    (_YUL + 'generate.py', 'ddf28646ad7c6adfbfbfbbc92a52dcbceeba86ff', 34, _YUL + 'census.py', 'b3d08f94bdeff0e62bf6c6a7072024a43801eb64', ()),
    (_YUL + 'test_staleness.py', '936a12b7730b6646c794dc433ce9303b5f9c93c0', 17, _YUL + 'acceptance.py', '80218632a185729980e02f88c539ccbd8ea727b4', ()),
    *((_COR + 'acceptance.py', '1b00c034ef2db9609c3a46377151c2fc339858f0', n, _COR + 'bounded.py', '21ae4112516a7d32dfd590c229128048ed165dbb', ())
      for n in (23, 28, 47)),
    (_COR + 'acceptance.py', '1b00c034ef2db9609c3a46377151c2fc339858f0', 71, _COR + 'compare.py', 'fb4429b621629c235041d37fd95021d63b79b2a4', ()),
    (_FRO + 'measure.py', '505dfe2874e25035c3c2ea92fa71575f99da846e', 222, _FRO + 'measure.py', '505dfe2874e25035c3c2ea92fa71575f99da846e', ()),
    (_TST + 'export-interfaces.py', 'bb6978a67cc3dbe0d2638aef7b92a20cdc77ef85', 18, _TST + 'generate-interface.py',
     '10c2aa3f124af8fe56b4d6112ab0399f0a1bc5c8', (8,)),
})
_ABI = _RR2 + 'audit-abi-world/'
# (driver, line, option) of every interpreter-headed list with an interpreter option, or the keyword form
RR_OPTIONED = frozenset({
    (_ABI + 'measure.py', 20, '-B'), (_ABI + 'measure.py', 26, '-B'), (_ABI + 'receipts.py', 40, '-B'), (_ABI + 'receipts.py', 42, '-B'),
    (_ABI + 'receipts.py', 45, '-B'), (_ABI + 'resume_accept.py', 41, '-B'), (_ABI + 'resume_measure.py', 20, '-B'),
    (_ABI + 'resume_measure.py', 26, '-B'), (_ABI + 'test_bounded.py', 26, '-B'), (_ABI + 'test_coverage.py', 29, '-B'),
    (_FRO + 'measure.py', 194, '-c'), (_RR6 + 'migrate-backend/check_fixture_mcp.py', 100, 'keyword'),
})
_RR_THEORIES = _RR2 + 'audit-theories/'
_RR_PAIRED = (_RR_THEORIES + 'paired_evidence.py', 'be36e9615801d394d83697e3ba58a07fea4ae568')
# Hypothetical claims of each policy from its nearest real launch (form, driver, line, literal, program, import form,
# import line, module): each must be refused by the H1203 handler (unsupported, or unreviewed) and the H1053 one.
RR_CLAIMS = {
    _ABI + '.gitignore': ('argv-wrapper', _ABI + 'measure.py', 26, 'bounded.py', _ABI + 'bounded.py', 'static', 1, _ABI + 'census.py'),
    _EVM + '.gitignore': ('argv-wrapper', _EVM + 'check_memory_premises.py', 53, 'bounded.py', _EVM + 'bounded.py', 'static', 1, _EVM + 'census.py'),
    _YUL + '.gitignore': ('flock-cwd', _YUL + 'generate.py', 15, _YUL + 'check_serial.py', _YUL + 'check_serial.py', 'static', 6, _YUL + 'census.py'),
    _RR6 + 'migrate-backend/.gitignore': ('program-wrapper', _RR6 + 'migrate-backend/run_gate.py', 84, 'check_fixture_mcp.py',
                                          _RR6 + 'migrate-backend/check_fixture_mcp.py', 'static', 18, _RR6 + 'migrate-backend/census.py'),
    _COR + '.gitignore': ('program-wrapper', _COR + 'acceptance.py', 71, 'compare.py', _COR + 'compare.py', 'static', 3, _COR + 'census.py'),
    _RR6 + 'migrate-counterexamples/.gitignore': ('program-wrapper', _RR6 + 'migrate-counterexamples/verify.py', 27, 'measure.py',
                                                  _RR6 + 'migrate-counterexamples/measure.py', 'static', 7, _RR6 + 'migrate-counterexamples/census.py'),
    _FRO + '.gitignore': ('argv-wrapper', _FRO + 'measure.py', 222, 'measure.py', _FRO + 'measure.py', 'file-location', 181, _FRO + 'census.py'),
    _RR6 + 'migrate-solkey/.gitignore': ('program-wrapper', _RR6 + 'migrate-solkey/check-api.py', 45, 'measure.py',
                                         _RR6 + 'migrate-solkey/measure.py', 'static', 17, _RR6 + 'migrate-solkey/census.py'),
    _TST + '.gitignore': ('argv-wrapper', _TST + 'export-interfaces.py', 18, 'generate-interface.py', _TST + 'generate-interface.py',
                          'static', 8, _TST + 'expr_dag.py'),
}


def _rr(name):
    """A name of the fragments.py namespace this module is exec'd in."""
    return globals()[name]


def _rr_interpreter(node):
    return (isinstance(node, ast.Attribute) and node.attr == 'executable' and isinstance(node.value, ast.Name) and node.value.id == 'sys'
            or isinstance(node, ast.Constant) and type(node.value) is str and posixpath.basename(node.value).startswith('python'))


def rr_interpreter_lists(text):
    """(line, option) of each list or tuple headed by sys.executable or a python path literal (option: its second element
    when that is a '-' literal, else None) and (line, 'keyword') of each command=<interpreter> keyword; None if unparsable."""
    try: tree = ast.parse(text)
    except (SyntaxError, ValueError, RecursionError): return None
    found = set()
    for n in ast.walk(tree):
        if isinstance(n, (ast.List, ast.Tuple)) and n.elts and _rr_interpreter(n.elts[0]):
            second = n.elts[1] if len(n.elts) > 1 else None
            option = second.value if isinstance(second, ast.Constant) and type(second.value) is str and second.value.startswith('-') else None
            found.add((n.lineno, option))
        elif isinstance(n, ast.keyword) and n.arg == 'command' and _rr_interpreter(n.value): found.add((n.value.lineno, 'keyword'))
    return found


def _rr_sibling_imports(text, program, tree):
    """Lines of the program that perform an H1203 import form of a sibling .py module listed in tree."""
    siblings = [q for q in tree if q.endswith('.py') and q != program and posixpath.dirname(q) == posixpath.dirname(program)]
    return tuple(sorted({n for n in range(1, text.count('\n') + 2) for q in siblings for form in _rr('H62_CACHE_IMPORTS')
                         if _rr('h62_cache_import')(form, text, program, n, q, tree)}))


def _rr_refused(call, message):
    try: call()
    except ValueError as error: assert message in str(error), (message, str(error))
    else: raise AssertionError('accepted: ' + message)


def _rr_claim(path, revision):
    form, driver, line, literal, program, imp, il, module = RR_CLAIMS[path]
    return {'kind': _rr('H62_CACHE_KIND'), 'path': path, 'input_revision': revision, 'source_blob': RR_REFUSED[path][0],
            'command': ['python3', '-B', driver], 'provenance': revision, 'line': 1,
            'launch': {'form': form, 'path': driver, 'blob': '0' * 40, 'line': line, 'literal': literal},
            'program': {'path': program, 'blob': '0' * 40, 'import': imp, 'import_line': il},
            'module': {'path': module, 'blob': '0' * 40}, 'purpose': 'Hypothetical claim of a refused policy (H1221 control).'}


def _rr_policy_row(path, revision):
    form, driver, line, literal, program, _, il, module = RR_CLAIMS[path]
    producer = {'root': driver, 'root_blob': '0' * 40, 'root_line': 0, 'driver': driver, 'driver_blob': '0' * 40, 'driver_line': line,
                'literal': program, 'program': program, 'program_blob': '0' * 40, 'import_line': il, 'module': module, 'module_blob': '0' * 40}
    return {'path': path, 'blob': RR_REFUSED[path][0], 'purpose': 'Hypothetical H1053 claim (H1221 control).',
            'provenance': {'commit': revision, 'path': path, 'blob': RR_REFUSED[path][0]},
            'matches': [{'line': 1, 'output': '__pycache__/', 'producer': producer}]}


def _rr_manifest_row(revision, operation):
    replay, paired = _rr('_HW_REPLAY'), _RR_PAIRED
    path = _RR_THEORIES + 'handoff/scope-manifest.json'; entry = replay[0] if operation == 'pinned-history-show' else _RR_THEORIES + 'check_paired_evidence.py'
    return {'kind': _rr('HANDOFF_WITNESS_KIND'), 'path': path, 'input_revision': revision, 'source_blob': RR_REFUSED[path][0],
            'command': ['python3', '-B', entry], 'operation': operation, 'entry': {'path': entry, 'blob': replay[1], 'import_line': replay[2]},
            'module': {'path': paired[0], 'blob': paired[1], 'line': 110},
            'read': {'path': entry if operation == 'pinned-history-show' else paired[0], 'line': 110},
            'purpose': 'Hypothetical claim of the refused manifest (H1221 control).'}


def _rr_shape_controls():
    """Each refused shape against the H1203 recognisers, next to an accepted twin (so no refusal is vacuous)."""
    launch, imports = _rr('h62_cache_launch'), _rr('h62_cache_import')
    forms = tuple(_rr('H62_CACHE_LAUNCHES'))
    D = 'scripts/h62/rr/'
    drv = ('import os\nimport subprocess\nimport sys\nfrom pathlib import Path\n\ndef run(argv, root):\n'
           '    result = subprocess.run(argv, cwd=root, text=True, capture_output=True)\n    return result.returncode\n\n'
           'def main():\n    run([sys.executable, str(Path(__file__).with_name("prog.py"))], ".")\n\nif __name__ == "__main__":\n    main()\n')
    good = launch('argv-wrapper', drv, D + 'drv.py', 11, 'prog.py')
    assert good == D + 'prog.py' and rr_interpreter_lists(drv) == {(11, None)}
    shapes = {  # refusal -> driver text (the launch stays on line 11)
        'interpreter-option': drv.replace('[sys.executable, str(', '[sys.executable, "-B", str('),
        'environment-mapping': drv.replace('capture_output=True)', 'capture_output=True, env=env)').replace(
            '    result = ', '    env = os.environ.copy(); env.pop("LEAN_PATH", None)\n    result = ').replace('\n\ndef main', '\ndef main'),
        'no-program-launch': drv.replace('str(Path(__file__).with_name("prog.py"))', '"-m", "lean_lsp_mcp"'),
        'argument-module': drv.replace('str(Path(__file__).with_name("prog.py"))', '__file__, "--worker", str(Path(__file__).with_name("prog.py"))'),
        'no-sibling-import': drv.replace('run([sys.executable, str(Path(__file__).with_name("prog.py"))], ".")',
                                         'subprocess.run(["python3", "scripts/h62/rr/prog.py"])'),
    }
    assert set(shapes) == set(RR_REASONS) - {'policy-rules', 'argument-repository'}
    for reason, text in shapes.items():
        assert text != drv and 11 in {n for n, _ in rr_interpreter_lists(text)}, reason
        for form in forms:
            for literal in ('prog.py', D + 'prog.py'):
                assert launch(form, text, D + 'drv.py', 11, literal) is None, (reason, form, literal)
    tree = {D + q: ('100644', 'blob', c * 40) for q, c in (('prog.py', 'a'), ('mod.py', 'b'), ('drv.py', 'c'))}
    static, plain = 'import argparse\nfrom mod import VALUE\nprint(VALUE)\n', 'import argparse\nimport json\nprint(json)\n'
    located = ('import importlib.util\nimport sys\nfrom pathlib import Path\n'
               'spec = importlib.util.spec_from_file_location("mod", Path(__file__).with_name("mod.py"))\n'
               'mod = importlib.util.module_from_spec(spec)\nspec.loader.exec_module(mod)\nprint(mod.VALUE)\n')
    argument = located.replace('Path(__file__).with_name("mod.py")', 'Path(sys.argv[2])')
    assert _rr_sibling_imports(static, D + 'prog.py', tree) == (2,) and _rr_sibling_imports(located, D + 'prog.py', tree) == (4,)
    assert _rr_sibling_imports(plain, D + 'prog.py', tree) == () and _rr_sibling_imports(argument, D + 'prog.py', tree) == ()
    assert imports('file-location', located, D + 'prog.py', 4, D + 'mod.py', tree) and not imports('file-location', argument, D + 'prog.py', 4, D + 'mod.py', tree)
    rules, cpython = _rr('_cache_rules'), _rr('CPYTHON_CACHE_RULES')
    assert all(r in cpython for _, r in rules('__pycache__/\n*.pyc\n')) and not all(r in cpython for _, r in rules('__pycache__/\n*.olean\n*.ilean\n'))
    assert rr_interpreter_lists('x = [sys.executable, "-c", "pass"]\ny = ("python3", "a.py")\nS(command=sys.executable, args=[])\n') == {
        (1, '-c'), (2, None), (3, 'keyword')}
    assert rr_interpreter_lists('[') is None and rr_interpreter_lists('x = ["lean", "python3"]\n') == set()


def _rr_blob_controls(git, home):
    """The refusals re-derived on the pinned blobs at RR_BASE (skipped when this checkout does not hold RR_BASE)."""
    try: git(home, 'cat-file', '-e', RR_BASE + '^{commit}')
    except ValueError: return False
    show = lambda b: git(home, 'cat-file', 'blob', b).decode()
    for path, (b, _) in RR_REFUSED.items():
        assert git(home, 'rev-parse', RR_BASE + ':' + path).decode().strip() == b, path
    directories = sorted({posixpath.dirname(p) + '/' for p in RR_REFUSED if p.endswith('.gitignore')})
    candidates, optioned = set(), set()
    trees = {}
    for d in directories:
        listing = git(home, 'ls-tree', '-r', RR_BASE, '--', d).decode().splitlines()
        tree = trees[d] = {line.split('\t', 1)[1]: tuple(line.split('\t', 1)[0].split()) for line in listing}
        for path, (_, kind, b) in sorted(tree.items()):
            if not path.endswith('.py') or kind != 'blob': continue
            found = rr_interpreter_lists(show(b))
            assert found is not None, path
            candidates |= {(path, b, n) for n, option in found if option is None}
            optioned |= {(path, n, option) for n, option in found if option is not None}
    assert candidates == {c[:3] for c in RR_CANDIDATES} and optioned == RR_OPTIONED, (candidates ^ {c[:3] for c in RR_CANDIDATES}, optioned ^ RR_OPTIONED)
    for driver, db, line, program, pb, sibling in sorted(RR_CANDIDATES):
        tree = trees[posixpath.dirname(driver) + '/']
        assert tree[program][2] == pb, program
        dtext, ptext = show(db), show(pb)
        for form in _rr('H62_CACHE_LAUNCHES'):
            for literal in (posixpath.basename(program), program):
                assert _rr('h62_cache_launch')(form, dtext, driver, line, literal) is None, (driver, line, form, literal)
        assert _rr_sibling_imports(ptext, program, tree) == sibling, (program, sibling)
    rules, cpython = _rr('_cache_rules'), _rr('CPYTHON_CACHE_RULES')
    for path, (b, reason) in RR_REFUSED.items():
        if not path.endswith('.gitignore'): continue
        parsed = rules(show(b))
        assert parsed and (reason == 'policy-rules') == any(r not in cpython for _, r in parsed), path
        assert any(r in _rr('CPYTHON_CACHE_DIRECTORY_RULES') for _, r in parsed), path
    # The reasons follow the candidates: only migrate-testsuite has a launched sibling importer, and it passes env=.
    with_import = {posixpath.dirname(c[0]) for c in RR_CANDIDATES if c[5]}
    assert with_import == {_TST[:-1]}
    launch_line = show(dict((c[0], c[1]) for c in RR_CANDIDATES)[_TST + 'export-interfaces.py']).split('\n')[17]
    assert 'env=env' in launch_line and 'sys.executable' in launch_line
    for path, (_, reason) in RR_REFUSED.items():
        d = posixpath.dirname(path)
        if reason == 'no-program-launch': assert not any(posixpath.dirname(c[0]) == d for c in RR_CANDIDATES), path
        if reason == 'interpreter-option': assert not any(posixpath.dirname(c[0]) == d for c in RR_CANDIDATES) and any(
            posixpath.dirname(o[0]) == d for o in RR_OPTIONED), path
    # The manifest: unpinned, read below the argument-supplied repository, and no other committed reader binds it.
    paired = show(_RR_PAIRED[1])
    pins = [n for n in ast.parse(paired).body if isinstance(n, ast.Assign) and any(isinstance(t, ast.Name) and t.id == 'HISTORICAL_PINS' for t in n.targets)]
    assert len(pins) == 1 and isinstance(pins[0].value, ast.Dict)
    keys = {k.value for k in pins[0].value.keys}
    assert len(keys) == 3 and 'scope-manifest.json' not in keys
    assert paired.count('a.current_repository/HISTORICAL_INPUT_PREFIX/name') == 1 and paired.count('scope-manifest.json') == 2  # the export list and verify's archive lookup
    readers = set()
    for line in git(home, 'grep', '-l', 'scope-manifest.json', RR_BASE, '--', 'scripts', 'tests').decode().splitlines():
        path = line.split(':', 1)[1]
        if path.startswith('scripts/check-tests-used') or path == 'scripts/tests-inventory.json': continue
        if 'audit-theories' in git(home, 'show', RR_BASE + ':' + path).decode(errors='replace'): readers.add(path)
    assert readers == {_RR_PAIRED[0], _RR_THEORIES + 'test_current_replay.py'}, readers
    replay = git(home, 'show', RR_BASE + ':' + _RR_THEORIES + 'test_current_replay.py').decode()
    assert '"synthetic_repository_bound_input"' in replay
    return True


def refused_review_controls(env):
    """H1221 controls, run by successor_controls with its helpers: the ten paths stay unresolved and unreviewed, each
    refused shape is refused by the kept recognisers, the refusals hold on the pinned blobs, and rows claiming the paths
    are refused by the H1053, H1203 and H1113 handlers, directly and through the inventory."""
    commit, rejected, classifier, root = (env[k] for k in ('commit', 'rejected', 'classifier', 'root'))
    git = classifier['git']
    # Nothing here is admitted or registered: the ten are exactly the paths H1203 left unresolved, in no review table.
    assert set(RR_REFUSED) == set(_rr('H62_CACHE_UNRESOLVED')) and len(RR_REFUSED) == 10
    assert all(reason in RR_REASONS for _, reason in RR_REFUSED.values()) and set(RR_CLAIMS) == {p for p in RR_REFUSED if p.endswith('.gitignore')}
    reviewed = ({t[0] for t in _rr('H62_CACHE_REVIEWED')} | set(_rr('REVIEWED_CACHE_POLICIES')) | {t[0] for t in _rr('HANDOFF_WITNESS_REVIEWED')}
                | {r[0] for r in _rr('REVIEWED_NONPY_ENTRIES')} | {r[0] for r in _rr('REVIEWED_PYTHON_ARGS')})
    assert not reviewed & set(RR_REFUSED)
    assert _RR_THEORIES + 'handoff/scope-manifest.json' in _rr('HANDOFF_WITNESS_UNRESOLVED') and _rr('_HW_PAIRED') == _RR_PAIRED
    assert not any(getattr(f, '__name__', '').startswith('rr_') for f in (*_rr('SOURCE_ROLE_KINDS').values(), *_rr('LATE_SOURCE_ROLE_KINDS').values()))
    _rr_shape_controls()
    _rr_blob_controls(git, Path(classifier['__file__']).resolve().parents[1])
    # Direct handler refusals of hypothetical claims of every path.
    revision = '1' * 40; graph = type('RRGraph', (), {'repo': None})(); catalog = {'standalone': []}
    for path in sorted(RR_CLAIMS):
        claim = _rr_claim(path, revision); driver = claim['launch']['path']
        self_launch = claim['launch']['path'] == claim['program']['path']
        message = 'unsupported h62 cache policy role invocation' if self_launch else 'unreviewed h62 cache policy role'
        _rr_refused(lambda: _rr('h62_cache_policy_root')(classifier, graph, catalog, claim), message)
        _rr_refused(lambda: _rr('cache_policies')(classifier, graph, [_rr_policy_row(path, revision)]), 'unreviewed cache policy role: ' + path)
        if not self_launch:  # an exact claim of the very tuple shape is refused only by review, never by a wider form
            _rr_refused(lambda: _rr('h62_cache_policy_root')(classifier, graph, catalog, dict(claim, command=['python3', driver])),
                        'unsupported h62 cache policy role invocation')
    for operation in ('pinned-history-show', 'main-root-read'):
        _rr_refused(lambda: _rr('handoff_witness_root')(classifier, graph, catalog, _rr_manifest_row(revision, operation)),
                    'unreviewed handoff witness role')
    # Through the inventory, with the exact policy and manifest texts committed at their paths.
    texts = {p: '__pycache__/\n' for p in RR_CLAIMS}
    texts[_EVM + '.gitignore'] = '__pycache__/\n*.olean\n*.ilean\n'; texts[_COR + '.gitignore'] = '__pycache__/\n*.pyc\n'
    texts[_RR_THEORIES + 'handoff/scope-manifest.json'] = '{}\n'
    try:
        repo = commit(texts, 'h62 refused paths')
        assert all(repo.tree[p][2] == RR_REFUSED[p][0] for p in RR_CLAIMS if p != _EVM + '.gitignore' and p != _COR + '.gitignore')
        for path in (_TST + '.gitignore', _RR6 + 'migrate-solkey/.gitignore'):
            rejected(repo, 'unreviewed h62 cache policy role', standalone=[_rr_claim(path, repo.ref)])
            rejected(repo, 'unreviewed cache policy role', consumers={'cache_policies': [_rr_policy_row(path, repo.ref)]})
        rejected(repo, 'unreviewed handoff witness role', standalone=[_rr_manifest_row(repo.ref, 'pinned-history-show')])
    finally:
        git(root, 'rm', '-q', '-r', '--ignore-unmatch', '--', *texts)
        git(root, '-c', 'user.name=Control', '-c', 'user.email=control@example.invalid', 'commit', '-q', '--allow-empty', '-m', 'h62 refused paths removed')


_rr('FORM_CONTROLS').append(refused_review_controls)
