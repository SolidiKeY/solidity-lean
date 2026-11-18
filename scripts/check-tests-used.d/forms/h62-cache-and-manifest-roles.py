# H1203 (gh#1518, H62-X1AF-COVERAGE, A) census form: source-only roles for the implicit CPython cache .gitignore
# policies of scripts/h62 that H1053 (roles.py, cache_policies) refused, and the review of the audit-theories
# scope-manifest.json. Exec'd by registry.py in the namespace of fragments.py (see registry.py's header); it registers
# one late standalone kind and one control and binds no shared name. Opt-in: without a standalone row of this kind
# every classification and output byte is unchanged.
#
# A row binds one exact .gitignore blob (and the commit that introduced it at that path) to the cache directory that
# CPython writes for one reviewed bytecode-enabled child: the kept python3 -B entry root is the driver itself (so
# __file__ is absolute), the driver line launches the program with sys.executable and no interpreter option, and the
# program imports a module of the policy directory, so CPython writes MODULE_DIR/__pycache__/. The H1053 guards hold
# unchanged: every rule of the policy is a CPython cache rule, the matched line is a directory rule that native
# `git check-ignore` (this tree's ancestor .gitignore blobs only) reports for the untracked cache directory, and no
# driver or program text mentions a bytecode switch or writes the environment; the one refinement is that a
# statement `os.environ['KEY'] = value` with KEY a literal outside PYTHON* is not an environment write here (it
# cannot name a CPython switch). Launch forms, re-derived from the syntax tree of the exact driver blob:
#   program-wrapper  line L is a module-level statement W('<name>.py', ...) and W is the one module-level
#                    `def W(p, *rest): subprocess.F([sys.executable, str(D / p), *map(str, rest)], ...)`, D bound
#                    once to Path(__file__).resolve().parent; the program is the driver's sibling <name>.py.
#   argv-wrapper     line L holds W([sys.executable, str(Path(__file__).with_name('<name>.py')), ...], ...) and W is
#                    the one module-level def whose body statement subprocess.F(argv, ...) passes its first parameter
#                    (never rebound or mutated); a cwd keyword is allowed because the program path is absolute.
#   flock-cwd        line L is the module-level `cmd = ['flock', '<lock>', sys.executable, str(R / '<path>'), ...]`,
#                    cmd bound once, never mutated or passed to another call than one subprocess.F(cmd, ...) whose
#                    cwd, if any, is R, and R bound once to Path.cwd(): the repository root (a reviewed claim, as the
#                    H1053 str(ROOT / path) form); flock runs the command with the inherited environment.
# The subprocess call never carries env, executable, args or ** keywords. Import forms of the exact program blob:
#   static           the H1053 exact sibling import (python_import_statement, roles.py) at line I.
#   file-location    line I is the module-level `S = importlib.util.spec_from_file_location('<n>',
#                    Path(__file__).with_name('<module>'))`, followed by module-level `M = importlib.util.
#                    module_from_spec(S)` and `S.loader.exec_module(M)`; S, M and importlib are bound once and used
#                    only there (SourceFileLoader writes the cache beside the module).
# Row shape (all keys required): {'kind': 'h62-cache-policy-role', 'path': P, 'input_revision': R, 'source_blob',
#   'command': ['python3', '-B', DRIVER], 'provenance': introducing commit, 'line': policy line, 'launch': {'form',
#   'path': DRIVER, 'blob', 'line', 'literal'}, 'program': {'path', 'blob', 'import', 'import_line'}, 'module':
#   {'path', 'blob'}, 'purpose'}.
# Not audited (documented limits, as H1053): whether the launch line and the import run, and the interpreter
# environment outside the committed texts (scripts/hygiene/run_changed.py sets PYTHONDONTWRITEBYTECODE for the
# commands gate.sh runs). Refused, left unresolved (reported back, never classified here), at 519932356a0e:
#   audit-abi-world: every child launch passes -B (measure, resume_measure, test_bounded, test_coverage, fidelity_call,
#     vectors_call) or runs -c code; its sibling imports run in python3 -B roots or under sys.dont_write_bytecode.
#   audit-evm-compiler: *.olean and *.ilean rules are no CPython cache rules; its bytecode-enabled children
#     (bounded.py) import no sibling module.
#   audit-yul: the bytecode-enabled children (check_serial.py, census.py, acceptance.py) import no sibling module;
#     record_resume/resume_inventory/census imports run only in python3 -B roots.
#   migrate-backend, migrate-counterexamples, migrate-solkey: no bytecode-enabled launch of a Python program (only
#     `-m lean_lsp_mcp`, a non-sibling module); importlib and sys.path loads run in python3 -B roots.
#   migrate-corpus: the bytecode-enabled children bounded.py and compare.py import no sibling module.
#   migrate-frontend: measure.py relaunches itself (`__file__`) and the child loads its module through importlib
#     from the argument-supplied path Path(sys.argv[2]): no exact literal binding of the module.
#   migrate-testsuite: export-interfaces.py launches generate-interface.py with an explicit env= mapping (a copied
#     environment also passed to measure.bounded), outside the H1053 env-keyword guard.
#   audit-theories/handoff/scope-manifest.json: paired_evidence.py export packages it from the argument-supplied
#     --current-repository with no blob pin; no committed invocation binds that argument to this checkout, and the
#     one committed test (test_current_replay.py) writes a synthetic stand-in. No exact binding, so no role.
# Source-policy credit only: no consumer, invocation, execution, pass, helper, output, proof or runtime credit; a
# changed object makes a historical row stale and a current one an error; another root of the path is never displaced.
import ast
import posixpath
import shlex
from pathlib import Path

H62_CACHE_KIND = 'h62-cache-policy-role'
H62_CACHE_PREFIX = 'h62-cache-policy:'
H62_CACHE_ROLE = ('Git ignore policy consumed by git (exclude-standard) for the implicit CPython bytecode cache of a reviewed '
                  'bytecode-enabled child launch of a kept python3 -B entry program')
H62_CACHE_LAUNCHES = {
    'program-wrapper': 'a module-level call of a one-statement wrapper that launches the driver sibling named by its literal',
    'argv-wrapper': 'a wrapper call whose argument list launches Path(__file__).with_name(literal)',
    'flock-cwd': 'a flock command list run with cwd at the current directory that launches the repository path literal',
}
H62_CACHE_IMPORTS = {
    'static': 'an exact static sibling import of the module',
    'file-location': 'importlib.util.spec_from_file_location of Path(__file__).with_name(module) executed by its loader',
}
_CM_KEYWORDS = {'program-wrapper': frozenset({'check', 'capture_output', 'text', 'timeout'}),
                'argv-wrapper': frozenset({'cwd', 'check', 'capture_output', 'text', 'timeout', 'stdin', 'stdout', 'stderr'}),
                'flock-cwd': frozenset({'cwd', 'check', 'capture_output', 'text', 'stdin', 'stdout', 'stderr', 'start_new_session'})}
_CM_CT = 'scripts/h62/item2/audit-compiler-transport/'
_CM_GV = 'scripts/h62/item4/generic-yul-views/'
_CM_MH = 'scripts/h62/item6/migrate-hash/'
# (policy, blob, introducing commit, line, launch form, driver, driver blob, driver line, literal, program, program
#  blob, import form, import line, module, module blob): reviewed at 519932356a0e.
H62_CACHE_REVIEWED = frozenset({
    (_CM_CT + '.gitignore', 'c18dd8d83ceed1806b50b0aaa46beb7e335fff13', 'd02bd456c9961bed758f6078f51032b115729476', 1,
     'program-wrapper', _CM_CT + 'h69_validate.py', 'de305187fbff497525095db65992b02f5cb13463', 43, 'generate_reflection.py',
     _CM_CT + 'generate_reflection.py', '8d883515e9c99761411f79100ba9366890a7f4a8', 'static', 6,
     _CM_CT + 'census.py', 'fb8a158c1461dea8f3a565f834d84557ea713ee9'),
    (_CM_GV + '.gitignore', 'c18dd8d83ceed1806b50b0aaa46beb7e335fff13', '7689952982335b4d8212db983704ecbdca7c1df2', 1,
     'argv-wrapper', _CM_GV + 'acceptance.py', 'ef73cc19f9a708c9e3ee21c6e8bf8b5584a253a1', 46, 'test_census.py',
     _CM_GV + 'test_census.py', 'e99157ce8cef667474d1de620e33451d1c38be73', 'file-location', 8,
     _CM_GV + 'census.py', '24df327e36cf9bfe537da98d10734c7c45ffc56a'),
    (_CM_MH + '.gitignore', 'a348e5040c3d2ac0cee5da2f21942aa68f106669', '2a18afcdba00a85645b0b3079704f78ffcd78860', 1,
     'flock-cwd', _CM_MH + 'launch_baseline.py', '7c3887ee53e84f07b3561f6200b673db3d865036', 16, _CM_MH + 'full_measure.py',
     _CM_MH + 'full_measure.py', 'cae845b44b6c50bd6ea69065b113099fe40eb73d', 'static', 9,
     _CM_MH + 'lean_lex.py', '98e527e654c4ed29919d56c4d343a72e75fca3fa'),
})
H62_CACHE_UNRESOLVED = tuple('scripts/h62/' + p for p in (
    'item2/audit-abi-world/.gitignore', 'item2/audit-evm-compiler/.gitignore', 'item2/audit-yul/.gitignore',
    'item6/migrate-backend/.gitignore', 'item6/migrate-corpus/.gitignore', 'item6/migrate-counterexamples/.gitignore',
    'item6/migrate-frontend/.gitignore', 'item6/migrate-solkey/.gitignore', 'item6/migrate-testsuite/.gitignore',
    'item2/audit-theories/handoff/scope-manifest.json'))


def _cm(name):
    """A name of the fragments.py namespace this module is exec'd in."""
    return globals()[name]


def _cm_parse(text):
    try: return ast.parse(text)
    except (SyntaxError, ValueError, RecursionError): return None


def _cm_bindings(tree, name): return _cm('_checkpoint_bindings')(tree, name)


def _cm_const(node):
    return node.value if isinstance(node, ast.Constant) and type(node.value) is str else None


def _cm_attr(node, base, attr):
    return isinstance(node, ast.Attribute) and node.attr == attr and isinstance(node.value, ast.Name) and node.value.id == base


def _cm_plain(tree, name):
    """name is bound once, by a plain `import name`."""
    return _cm('_checkpoint_imported')(tree, name, lambda n: isinstance(n, ast.Import))


def _cm_path_name(tree):
    """Path is bound once, by `from pathlib import Path`."""
    return _cm('_checkpoint_imported')(tree, 'Path', lambda n: isinstance(n, ast.ImportFrom) and n.module == 'pathlib' and n.level == 0)


def _cm_file(tree, node):
    """node is Path(__file__), Path from pathlib and __file__ never bound."""
    return (isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id == 'Path' and len(node.args) == 1
            and not node.keywords and isinstance(node.args[0], ast.Name) and node.args[0].id == '__file__'
            and _cm_bindings(tree, '__file__') == 0 and _cm_path_name(tree))


def _cm_with_name(tree, node):
    """The literal of Path(__file__).with_name('<literal>'), else None."""
    if not (isinstance(node, ast.Call) and isinstance(node.func, ast.Attribute) and node.func.attr == 'with_name'
            and _cm_file(tree, node.func.value) and len(node.args) == 1 and not node.keywords):
        return None
    return _cm_const(node.args[0])


def _cm_str(tree, node):
    """The single argument of str(x), str never bound, else None."""
    if (isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id == 'str' and len(node.args) == 1
            and not node.keywords and _cm_bindings(tree, 'str') == 0):
        return node.args[0]
    return None


def _cm_executable(tree, node): return _cm_attr(node, 'sys', 'executable') and _cm_plain(tree, 'sys')


def _cm_launch_call(tree, node, form):
    """node is subprocess.F(...) (F a run/call/Popen form, subprocess a plain import) with only the form's keywords."""
    return (isinstance(node, ast.Call) and isinstance(node.func, ast.Attribute) and node.func.attr in _cm('_SUBPROCESS_CALLS')
            and isinstance(node.func.value, ast.Name) and node.func.value.id == 'subprocess' and _cm_plain(tree, 'subprocess')
            and len(node.args) == 1 and all(k.arg in _CM_KEYWORDS[form] for k in node.keywords))


def _cm_module_def(tree, name):
    """The one undecorated module-level def of name, bound nowhere else."""
    defs = [n for n in tree.body if isinstance(n, ast.FunctionDef) and n.name == name]
    if len(defs) != 1 or _cm_bindings(tree, name) != 1 or defs[0].decorator_list: return None
    a = defs[0].args
    return None if a.posonlyargs or a.kwonlyargs or a.kwarg or a.defaults or a.kw_defaults else defs[0]


def _cm_unmutated(tree, scope, name, allowed=()):
    """name is never the base of an attribute, subscript, starred or call argument other than the nodes in allowed and
    the copying builtins dict and repr (never bound in tree)."""
    for n in ast.walk(scope):
        if isinstance(n, (ast.Attribute, ast.Subscript)) and isinstance(n.value, ast.Name) and n.value.id == name: return False
        pure = isinstance(n, ast.Call) and isinstance(n.func, ast.Name) and n.func.id in ('dict', 'repr') and _cm_bindings(tree, n.func.id) == 0
        if isinstance(n, ast.Call) and n not in allowed and not pure and any(
                isinstance(a, ast.Name) and a.id == name for a in list(n.args) + [k.value for k in n.keywords]):
            return False
        if isinstance(n, ast.Starred) and isinstance(n.value, ast.Name) and n.value.id == name: return False
    return True


def _cm_cwd(tree, name):
    """name is bound once at module level to Path.cwd() (or pathlib.Path.cwd())."""
    value = _cm('_checkpoint_bound')(tree, name)
    if not (isinstance(value, ast.Call) and not value.args and not value.keywords and isinstance(value.func, ast.Attribute)
            and value.func.attr == 'cwd'):
        return False
    base = value.func.value
    if isinstance(base, ast.Name) and base.id == 'Path': return _cm_path_name(tree)
    return _cm_attr(base, 'pathlib', 'Path') and _cm_plain(tree, 'pathlib')


def _cm_parent(tree, name):
    """name is bound once at module level to Path(__file__).resolve().parent."""
    value = _cm('_checkpoint_bound')(tree, name)
    return (isinstance(value, ast.Attribute) and value.attr == 'parent' and isinstance(value.value, ast.Call)
            and not value.value.args and not value.value.keywords and isinstance(value.value.func, ast.Attribute)
            and value.value.func.attr == 'resolve' and _cm_file(tree, value.value.func.value))


def _cm_program_wrapper(tree, driver, line, literal):
    calls = [n.value for n in tree.body if isinstance(n, ast.Expr) and isinstance(n.value, ast.Call) and n.lineno == line]
    if len(calls) != 1 or '/' in literal or not literal.endswith('.py'): return None
    call = calls[0]
    if (not isinstance(call.func, ast.Name) or not call.args or _cm_const(call.args[0]) != literal or call.keywords
            or any(isinstance(a, ast.Starred) for a in call.args)):
        return None
    f = _cm_module_def(tree, call.func.id)
    if f is None or len(f.args.args) != 1 or f.args.vararg is None or len(f.body) != 1 or not isinstance(f.body[0], ast.Expr): return None
    p, rest = f.args.args[0].arg, f.args.vararg.arg
    launch = f.body[0].value
    if not _cm_launch_call(tree, launch, 'program-wrapper') or not isinstance(launch.args[0], ast.List): return None
    elts = launch.args[0].elts; div = len(elts) == 3 and _cm_str(tree, elts[1])
    if not (div and _cm_executable(tree, elts[0]) and isinstance(div, ast.BinOp) and isinstance(div.op, ast.Div)
            and isinstance(div.left, ast.Name) and _cm_parent(tree, div.left.id) and isinstance(div.right, ast.Name) and div.right.id == p):
        return None
    tail = elts[2]
    if not (isinstance(tail, ast.Starred) and isinstance(tail.value, ast.Call) and isinstance(tail.value.func, ast.Name)
            and tail.value.func.id == 'map' and _cm_bindings(tree, 'map') == 0 and not tail.value.keywords
            and [type(a) for a in tail.value.args] == [ast.Name, ast.Name] and tail.value.args[0].id == 'str' and tail.value.args[1].id == rest):
        return None
    if _cm_bindings(f, p) != 1 or _cm_bindings(f, rest) != 1: return None
    return posixpath.join(posixpath.dirname(driver), literal)


def _cm_argv_wrapper(tree, driver, line, literal):
    calls = [n for n in ast.walk(tree) if isinstance(n, ast.Call) and isinstance(n.func, ast.Name) and n.args
             and isinstance(n.args[0], ast.List) and n.args[0].lineno == line]
    if len(calls) != 1 or '/' in literal or not literal.endswith('.py'): return None
    call = calls[0]
    if call.keywords or any(isinstance(a, ast.Starred) for a in call.args): return None
    f = _cm_module_def(tree, call.func.id)
    if f is None or f.args.vararg is not None or len(f.args.args) != len(call.args): return None
    argv = f.args.args[0].arg
    launches = [n for n in ast.walk(f) if isinstance(n, ast.Call) and isinstance(n.func, ast.Attribute)
                and isinstance(n.func.value, ast.Name) and n.func.value.id == 'subprocess']
    if (len(launches) != 1 or not _cm_launch_call(tree, launches[0], 'argv-wrapper') or not isinstance(launches[0].args[0], ast.Name)
            or launches[0].args[0].id != argv or _cm_bindings(f, argv) != 1 or not _cm_unmutated(tree, f, argv, launches)
            or not any(isinstance(s, (ast.Expr, ast.Assign)) and s.value is launches[0] for s in f.body)):
        return None
    elts = call.args[0].elts
    if len(elts) < 2 or any(isinstance(e, ast.Starred) for e in elts[:2]) or not _cm_executable(tree, elts[0]): return None
    named = _cm_str(tree, elts[1])
    if named is None or _cm_with_name(tree, named) != literal: return None
    return posixpath.join(posixpath.dirname(driver), literal)


def _cm_flock(tree, driver, line, literal):
    assigns = [n for n in tree.body if isinstance(n, ast.Assign) and n.lineno == line and len(n.targets) == 1
               and isinstance(n.targets[0], ast.Name) and isinstance(n.value, ast.List)]
    if len(assigns) != 1 or '/' not in literal or not literal.endswith('.py'): return None
    name = assigns[0].targets[0].id; elts = assigns[0].value.elts
    if _cm_bindings(tree, name) != 1 or len(elts) < 4 or any(isinstance(e, ast.Starred) for e in elts[:4]): return None
    lock = _cm_const(elts[1]); div = _cm_str(tree, elts[3])
    if (_cm_const(elts[0]) != 'flock' or not lock or lock.startswith('-') or not _cm_executable(tree, elts[2])
            or not (isinstance(div, ast.BinOp) and isinstance(div.op, ast.Div) and isinstance(div.left, ast.Name)
                    and _cm_cwd(tree, div.left.id) and _cm_const(div.right) == literal)):
        return None
    launches = [n for n in ast.walk(tree) if isinstance(n, ast.Call) and n.args and isinstance(n.args[0], ast.Name) and n.args[0].id == name]
    if len(launches) != 1 or not _cm_launch_call(tree, launches[0], 'flock-cwd') or not _cm_unmutated(tree, tree, name, launches): return None
    if any(k.arg == 'cwd' and not (isinstance(k.value, ast.Name) and k.value.id == div.left.id) for k in launches[0].keywords): return None
    return literal


_CM_LAUNCH = {'program-wrapper': _cm_program_wrapper, 'argv-wrapper': _cm_argv_wrapper, 'flock-cwd': _cm_flock}


def h62_cache_launch(form, text, driver, line, literal):
    """The program the driver line launches bytecode-enabled in that form, else None."""
    tree = _cm_parse(text)
    return None if tree is None or form not in _CM_LAUNCH else _CM_LAUNCH[form](tree, driver, line, literal)


def _cm_file_location(text, program, line, module):
    tree = _cm_parse(text)
    if tree is None or posixpath.dirname(program) != posixpath.dirname(module): return False
    at = [k for k, n in enumerate(tree.body) if isinstance(n, ast.Assign) and n.lineno == line]
    if len(at) != 1 or len(tree.body[at[0]].targets) != 1 or not isinstance(tree.body[at[0]].targets[0], ast.Name): return False
    k = at[0]; spec = tree.body[k].targets[0].id; value = tree.body[k].value
    util = lambda node, attr: isinstance(node, ast.Attribute) and node.attr == attr and _cm_attr(node.value, 'importlib', 'util')
    if not (isinstance(value, ast.Call) and util(value.func, 'spec_from_file_location') and len(value.args) == 2 and not value.keywords
            and _cm_const(value.args[0]) and _cm_with_name(tree, value.args[1]) == posixpath.basename(module)):
        return False
    if not (_cm_bindings(tree, 'importlib') == 1 and any(isinstance(n, ast.Import) and any(a.name == 'importlib.util' and a.asname is None for a in n.names)
                                                       for n in tree.body)):
        return False
    made = [n for n in tree.body[k + 1:] if isinstance(n, ast.Assign) and len(n.targets) == 1 and isinstance(n.targets[0], ast.Name)
            and isinstance(n.value, ast.Call) and util(n.value.func, 'module_from_spec') and len(n.value.args) == 1 and not n.value.keywords
            and isinstance(n.value.args[0], ast.Name) and n.value.args[0].id == spec]
    if len(made) != 1: return False
    loaded = made[0].targets[0].id
    run = [n for n in tree.body[tree.body.index(made[0]) + 1:] if isinstance(n, ast.Expr) and isinstance(n.value, ast.Call)
           and isinstance(n.value.func, ast.Attribute) and n.value.func.attr == 'exec_module' and _cm_attr(n.value.func.value, spec, 'loader')
           and len(n.value.args) == 1 and not n.value.keywords and isinstance(n.value.args[0], ast.Name) and n.value.args[0].id == loaded]
    uses = lambda name: sum(isinstance(n, ast.Name) and n.id == name and isinstance(n.ctx, ast.Load) for n in ast.walk(tree))
    return (len(run) == 1 and _cm_bindings(tree, spec) == 1 and _cm_bindings(tree, loaded) == 1 and uses(spec) == 2 and uses('importlib') == 2
            and not any(isinstance(n, ast.Attribute) and isinstance(n.value, ast.Name) and n.value.id == 'sys' and n.attr in _cm('_SYS_IMPORT_STATE')
                        for n in ast.walk(tree)))


def h62_cache_import(form, text, program, line, module, tree):
    """True iff the program's line performs that import form of the module."""
    if form == 'static': return _cm('python_import_statement')(text, program, line, module, tree) is not None
    return form == 'file-location' and _cm_file_location(text, program, line, module)


def h62_cache_switches_off(text):
    """True iff the text mentions a bytecode switch or writes the environment (H1053 guards); an assignment statement
    os.environ['KEY'] = value with a literal KEY outside PYTHON* is blanked first (it names no CPython switch)."""
    if any(s in text.lower() for s in _cm('BYTECODE_SWITCHES')): return True
    tree = _cm_parse(text)
    if tree is None: return True
    lines = [bytearray(line.encode('utf-8', 'surrogateescape')) for line in text.split('\n')]
    if _cm_plain(tree, 'os'):
        for n in ast.walk(tree):
            if not (isinstance(n, ast.Assign) and len(n.targets) == 1): continue
            t = n.targets[0]; key = isinstance(t, ast.Subscript) and _cm_attr(t.value, 'os', 'environ') and _cm_const(t.slice)
            if key and not key.upper().startswith('PYTHON') and t.lineno == t.end_lineno:
                lines[t.lineno - 1][t.col_offset:t.end_col_offset] = b' ' * (t.end_col_offset - t.col_offset)
    blanked = b'\n'.join(lines).decode('utf-8', 'surrogateescape')
    return bool(_cm('_ENVIRONMENT_WRITE').search(blanked))


def h62_cache_policy_root(classifier, graph, catalog, entry, reviewed=None):
    """H1203: a reviewed .gitignore as the source-only policy of one exact bytecode-enabled child's cache directory.

    Late (after every other standalone definition) so the driver's entry root exists. The row must be one reviewed
    tuple; its policy, driver, program and module blobs are current (a historical row with a changed blob is stale, a
    current one an error); the policy blob was introduced at its path by the reviewed commit; the launch and import
    forms are re-derived on the measured bytes under the H1053 guards and native git check-ignore must report the
    reviewed line for the untracked cache directory; the driver is a current python3 -B entry root of exactly its
    blob (else refused now, stale later). Never displaces another root of the path; anchors nothing.
    """
    repo = graph.repo; role = 'h62 cache policy role'
    reviewed = H62_CACHE_REVIEWED if reviewed is None else reviewed
    required = {'kind', 'path', 'input_revision', 'source_blob', 'command', 'provenance', 'line', 'launch', 'program', 'module', 'purpose'}
    d, g, m = entry.get('launch'), entry.get('program'), entry.get('module')
    if (set(entry) != required or not all(isinstance(entry[k], str) for k in ('path', 'source_blob', 'provenance', 'purpose'))
            or not entry['purpose'].strip() or type(entry['line']) is not int
            or not isinstance(d, dict) or set(d) != {'form', 'path', 'blob', 'line', 'literal'}
            or not isinstance(g, dict) or set(g) != {'path', 'blob', 'import', 'import_line'}
            or not isinstance(m, dict) or set(m) != {'path', 'blob'}
            or not all(isinstance(x[k], str) for x, k in ((d, 'form'), (d, 'path'), (d, 'blob'), (d, 'literal'), (g, 'path'), (g, 'blob'),
                                                          (g, 'import'), (m, 'path'), (m, 'blob')))
            or not all(type(n) is int for n in (d['line'], g['import_line']))):
        raise ValueError('invalid ' + role + ' definition')
    p = entry['path']; revision = entry['input_revision']; blob = entry['source_blob']
    if not isinstance(revision, str) or not classifier['hex_pin'](revision, 40): raise ValueError(role + ' requires a full commit revision')
    if any(x is not entry and x.get('path') == p and x.get('input_revision') == revision for x in catalog['standalone']):
        raise ValueError('conflicting standalone definitions: ' + p)
    directory = posixpath.dirname(p)
    if (d['form'] not in H62_CACHE_LAUNCHES or g['import'] not in H62_CACHE_IMPORTS or entry['command'] != ['python3', '-B', d['path']]
            or _cm('_clean')(p) != p or posixpath.basename(p) != '.gitignore' or len({d['path'], g['path'], m['path']}) != 3
            or not all(q.endswith('.py') for q in (d['path'], g['path'], m['path']))
            or directory and not m['path'].startswith(directory + '/')):
        raise ValueError('unsupported ' + role + ' invocation: ' + p)
    if (p, blob, entry['provenance'], entry['line'], d['form'], d['path'], d['blob'], d['line'], d['literal'], g['path'], g['blob'],
            g['import'], g['import_line'], m['path'], m['blob']) not in reviewed:
        raise ValueError('unreviewed ' + role + ': ' + p)
    pins = [(p, blob), (d['path'], d['blob']), (g['path'], g['blob']), (m['path'], m['blob'])]
    if not _cm('_role_current')(classifier, repo, catalog, entry, pins): return
    if repo.tree[p][0] != '100644' or any(q not in repo.texts for q, _ in pins): raise ValueError('unsupported ' + role + ' invocation: ' + p)
    if not _cm('_introduced')(classifier, repo, entry['provenance'], p, blob): raise ValueError(role + ' lacks its introducing provenance: ' + p)
    rules = _cm('_cache_rules')(repo.texts[p])
    if not rules or any(rule not in _cm('CPYTHON_CACHE_RULES') for _, rule in rules):
        raise ValueError(role + ' has a rule outside the CPython cache rules: ' + p)
    rule = dict(rules).get(entry['line'])
    if rule not in _cm('CPYTHON_CACHE_DIRECTORY_RULES'): raise ValueError(role + ' line names no cache directory rule: ' + p)
    home = posixpath.dirname(m['path']); cache = posixpath.join(home, '__pycache__')
    if cache in repo.tree or any(q.startswith(cache + '/') for q in repo.tree): raise ValueError(role + ' output is tracked: ' + p)
    if any(h62_cache_switches_off(repo.texts[q]) for q in (d['path'], g['path'])): raise ValueError(role + ' producer switches bytecode off: ' + p)
    if not h62_cache_import(g['import'], repo.texts[g['path']], g['path'], g['import_line'], m['path'], repo.tree):
        raise ValueError(role + ' program does not import its module: ' + g['path'] + ':' + str(g['import_line']))
    if h62_cache_launch(d['form'], repo.texts[d['path']], d['path'], d['line'], d['literal']) != g['path']:
        raise ValueError(role + ' driver line is no bytecode-enabled launch: ' + d['path'] + ':' + str(d['line']))
    if _cm('_ignored_by')(repo, home, '__pycache__/') != (p, entry['line'], rule):
        raise ValueError(role + ' line does not ignore the cache directory: ' + p)
    if not _cm('_entry_root')(graph, d['path'], d['blob']):
        if revision == repo.ref: raise ValueError(role + ' driver is not a python3 -B entry root: ' + d['path'])
        return
    if classifier['excluded'](p) or any(x['path'] == p for x in graph.roots.values()): return
    identity = H62_CACHE_PREFIX + p
    graph.root(p, 'implicit CPython cache policy consumer', 'git (exclude-standard) applies ' + p, g['path'], g['import_line'], root_id=identity)
    if identity not in graph.roots: return
    graph.roots[identity].update({'source_only': True, 'cache_policy_role': True, 'source_blob': blob, 'purpose': entry['purpose'],
        'policy_role': H62_CACHE_ROLE, 'program_role': H62_CACHE_KIND, 'provenance': {'commit': entry['provenance'], 'path': p, 'blob': blob},
        'policy_matches': [{'line': entry['line'], 'output': cache + '/', 'launch': d, 'program': g, 'module': m,
                            'interface': {'launch': H62_CACHE_LAUNCHES[d['form']], 'import': H62_CACHE_IMPORTS[g['import']]}}],
        'source_declaration_revision': revision,
        'validation_at_measured_revision': {'status': 'policy', 'command': shlex.join(entry['command']),
            'reason': 'git check-ignore of this exact blob in isolation for the cache directory of a reviewed bytecode-enabled child of a kept '
                      'entry program; the launch, the import and the interpreter environment are not run or audited. Source-policy credit '
                      'only: no consumer, invocation, execution, pass, helper, output, proof or runtime credit.'}})


def h62_cache_controls(env):
    """H1203 controls, run by successor_controls with its helpers: the reviewed tuples on their pinned blobs, each
    launch and import form on synthetic policies, and refusals (other lines, interpreter options, keywords, rebinding,
    mutation, switches, policy rules, tracked caches, provenance, entry roots, staleness, schema and conflicts)."""
    global H62_CACHE_REVIEWED
    commit, run, rejected, blob, classifier, root = (env[k] for k in ('commit', 'run', 'rejected', 'blob', 'classifier', 'root'))
    git = classifier['git']; canonical = _cm('canonical')
    assert H62_CACHE_KIND in _cm('LATE_SOURCE_ROLE_KINDS') and H62_CACHE_KIND not in _cm('SOURCE_ROLE_KINDS')
    # The reviewed tuples: three of the twelve refused policies, never an unresolved path, each re-derived on its blobs when held.
    assert len(H62_CACHE_REVIEWED) == 3 and len(H62_CACHE_UNRESOLVED) == 10 and not {t[0] for t in H62_CACHE_REVIEWED} & set(H62_CACHE_UNRESOLVED)
    assert not {t[0] for t in H62_CACHE_REVIEWED} & set(_cm('REVIEWED_CACHE_POLICIES'))
    home = Path(classifier['__file__']).resolve().parents[1]
    def held(b):
        try: return git(home, 'cat-file', 'blob', b).decode()
        except ValueError: return None
    for p, _, _, _, form, dp, db, dl, lit, gp, gb, imp, il, mp, mb in sorted(H62_CACHE_REVIEWED):
        dtext, gtext = held(db), held(gb)
        if None in (dtext, gtext, held(mb)): continue
        assert h62_cache_launch(form, dtext, dp, dl, lit) == gp and not h62_cache_switches_off(dtext) and not h62_cache_switches_off(gtext), p
        assert all(h62_cache_launch(f, dtext, dp, dl, lit) is None for f in _CM_LAUNCH if f != form), p
        assert h62_cache_launch(form, dtext, dp, dl + 1, lit) is None, p
        assert h62_cache_import(imp, gtext, gp, il, mp, {gp: ('100644', 'blob', gb), mp: ('100644', 'blob', mb)}), p
    D = 'scripts/h62/cm/'; PW, AW, FL = D + 'pw/', D + 'aw/', D + 'fl/'
    pw_drv = ('import os\nimport subprocess\nimport sys\nfrom pathlib import Path\nscripts = Path(__file__).resolve().parent\n'
              "os.environ['LEAN_NUM_THREADS'] = '1'\ndef python(script, *args):\n"
              '    subprocess.run([sys.executable, str(scripts / script), *map(str, args)], check=True)\n'
              "python('prog.py', '--x', 1)\nif False:\n    python('prog.py')\npython('prog' + '.py')\nx = python('prog.py')\n")
    aw_drv = ('import subprocess\nimport sys\nfrom pathlib import Path\n\ndef run(argv, root):\n'
              '    result = subprocess.run(argv, cwd=root, text=True, capture_output=True)\n    return dict(command=argv, exit=result.returncode)\n\n'
              'def main():\n    run([sys.executable, str(Path(__file__).with_name("prog.py"))], ".")\n'
              '    run([sys.executable, "-B", str(Path(__file__).with_name("prog.py"))], ".")\n'
              '    run([sys.executable, str(Path.cwd() / "prog.py")], ".")\n'
              '    print([sys.executable, str(Path(__file__).with_name("prog.py"))])\n\nif __name__ == "__main__":\n    main()\n')
    aw_prog = ('import importlib.util\nfrom pathlib import Path\n'
               'spec = importlib.util.spec_from_file_location("mod", Path(__file__).with_name("mod.py"))\n'
               'mod = importlib.util.module_from_spec(spec)\nspec.loader.exec_module(mod)\nprint(mod.VALUE)\n')
    fl_drv = ('import pathlib, subprocess, sys\nroot = pathlib.Path.cwd()\n'
              'cmd = ["flock", "/tmp/cm.lock", sys.executable, str(root / "scripts/h62/cm/fl/prog.py"), "--x"]\n'
              'child = subprocess.Popen(cmd, cwd=root, stdin=subprocess.DEVNULL, start_new_session=True)\ndata = {"command": cmd}\n'
              'other = ["flock", "-n", "/tmp/cm.lock", sys.executable, str(root / "scripts/h62/cm/fl/prog.py")]\nprint(child)\n')
    static_prog = 'import argparse\nfrom mod import VALUE\nprint(VALUE)\n'
    files = {PW + '.gitignore': '__pycache__/\n', PW + 'mod.py': 'VALUE = 1\n', PW + 'prog.py': static_prog, PW + 'drv.py': pw_drv,
             AW + '.gitignore': '# CPython cache\n__pycache__/\n*.py[cod]\n', AW + 'mod.py': 'VALUE = 2\n', AW + 'prog.py': aw_prog, AW + 'drv.py': aw_drv,
             FL + '.gitignore': '/__pycache__/\n', FL + 'mod.py': 'VALUE = 3\n', FL + 'prog.py': static_prog, FL + 'drv.py': fl_drv}
    cm = commit(files, 'h62 cache policies'); C = cm.ref
    later = commit({'tests/cm-later.txt': 'L\n'}, 'h62 cache policies later')
    def source_root(path, repo=cm, text=None):
        return {'path': path, 'input_revision': repo.ref, 'source_blob': blob(repo, path), 'command': ['python3', '-B', path], 'kind': _cm('SOURCE_ONLY_KIND'),
                'entry_line': max(classifier['entrypoint_lines']((text or files[path]).encode())), 'purpose': 'Synthetic kept root.'}
    shapes = {PW: ('program-wrapper', 9, 'prog.py', 'static', 2, 1), AW: ('argv-wrapper', 10, 'prog.py', 'file-location', 3, 2),
              FL: ('flock-cwd', 3, FL + 'prog.py', 'static', 2, 1)}
    def row(base, repo=cm, provenance=None, revision=None, **changes):
        form, dl, lit, imp, il, line = shapes[base]
        x = {'kind': H62_CACHE_KIND, 'path': base + '.gitignore', 'input_revision': revision or repo.ref, 'source_blob': blob(repo, base + '.gitignore'),
             'command': ['python3', '-B', base + 'drv.py'], 'provenance': provenance or C, 'line': line,
             'launch': {'form': form, 'path': base + 'drv.py', 'blob': blob(repo, base + 'drv.py'), 'line': dl, 'literal': lit},
             'program': {'path': base + 'prog.py', 'blob': blob(repo, base + 'prog.py'), 'import': imp, 'import_line': il},
             'module': {'path': base + 'mod.py', 'blob': blob(repo, base + 'mod.py')}, 'purpose': 'Synthetic cache policy role.'}
        for k, v in changes.items(): x[k] = dict(x[k], **v) if isinstance(v, dict) and isinstance(x.get(k), dict) else v
        return x
    tuple_of = lambda x: (x['path'], x['source_blob'], x['provenance'], x['line'], x['launch']['form'], x['launch']['path'], x['launch']['blob'],
                          x['launch']['line'], x['launch']['literal'], x['program']['path'], x['program']['blob'], x['program']['import'],
                          x['program']['import_line'], x['module']['path'], x['module']['blob'])
    roots = lambda repo=cm, texts=None: [source_root(b + 'drv.py', repo, (texts or {}).get(b + 'drv.py')) for b in (PW, AW, FL)]
    good = [row(b) for b in (PW, AW, FL)]
    saved = H62_CACHE_REVIEWED
    def review(*rows): return frozenset(tuple_of(x) for x in rows)
    try:
        H62_CACHE_REVIEWED = review(*good)
        base_model, base = run(later, standalone=roots(later))
        assert all(base[x['path']]['class'] != 'keep' for x in good)
        for repo in (cm, later):  # each form on its own and together, at the policy's revision and later
            for rows_ in ([good[0]], [good[1]], [good[2]], good):
                model, rows = run(repo, standalone=roots(repo) + rows_)
                for x in rows_:
                    e = model['entry_points'][H62_CACHE_PREFIX + x['path']]
                    assert rows[x['path']]['class'] == 'keep' and e['source_only'] and e['cache_policy_role'] and e['validation_at_measured_revision']['status'] == 'policy'
                    assert e['policy_matches'][0]['output'] == posixpath.dirname(x['path']) + '/__pycache__/' and e['provenance']['commit'] == C
                if repo is later and rows_ is good:  # source-policy credit only: nothing else changes
                    assert all(canonical(v) == canonical(base[q]) for q, v in rows.items() if q not in {x['path'] for x in good})
                    assert set(model['entry_points']) - set(base_model['entry_points']) == {H62_CACHE_PREFIX + x['path'] for x in good}
        # Other lines of the same drivers: nested, computed, assigned, -B, a non-sibling path, a print, a flock option.
        variants = [row(PW, launch={'line': n}) for n in (11, 12, 13)] + [row(AW, launch={'line': n}) for n in (11, 12, 13)] + [
            row(FL, launch={'line': 6}), row(PW, launch={'literal': 'mod.py'}), row(FL, program={'import_line': 1}),
            row(AW, launch={'form': 'program-wrapper'}), row(PW, launch={'form': 'argv-wrapper'}), row(FL, launch={'literal': 'prog.py'})]
        H62_CACHE_REVIEWED = review(*good, *variants)
        for x in variants: rejected(cm, 'does not import its module' if x['program']['import_line'] == 1 else 'no bytecode-enabled launch', standalone=roots() + [x])
        # Mutants of one blob each (still reviewed): every one must fail on the bytes with the named refusal.
        launch, imports, off = 'no bytecode-enabled launch', 'does not import its module', 'switches bytecode off'
        mutants = (
            (PW, PW + 'drv.py', pw_drv.replace('[sys.executable, str(', '[sys.executable, "-B", str('), launch),
            (PW, PW + 'drv.py', pw_drv.replace('check=True)\n', 'check=True, env={})\n', 1), launch),
            (PW, PW + 'drv.py', pw_drv.replace('check=True)\n', 'check=True, cwd="/tmp")\n', 1), launch),
            (PW, PW + 'drv.py', pw_drv + 'scripts = Path.cwd()\n', launch),
            (PW, PW + 'drv.py', pw_drv.replace('scripts = Path(__file__).resolve().parent', 'scripts = Path.cwd()'), launch),
            (PW, PW + 'drv.py', pw_drv.replace('def python', '@staticmethod\ndef python'), launch, {'launch': {'line': 10}}),
            (PW, PW + 'drv.py', pw_drv + 'def python(script, *args): pass\n', launch),
            (PW, PW + 'drv.py', pw_drv.replace("'LEAN_NUM_THREADS'", "'PYTHONSAFEPATH'"), off),
            (PW, PW + 'drv.py', pw_drv.replace("os.environ['LEAN_NUM_THREADS'] = '1'", "KEY = 'X'; os.environ[KEY] = '1'"), off),
            (PW, PW + 'drv.py', pw_drv.replace("os.environ['LEAN_NUM_THREADS'] = '1'", "os.putenv('X', '1')"), off),
            (PW, PW + 'prog.py', static_prog.replace('import argparse', 'import sys; sys.dont_write_bytecode = True'), off),
            (PW, PW + 'prog.py', static_prog.replace('import argparse', 'import importlib'), imports),
            (AW, AW + 'drv.py', aw_drv.replace('capture_output=True)', 'capture_output=True, env={})'), launch),
            (AW, AW + 'drv.py', aw_drv.replace('    result = ', '    argv.insert(1, "-B")\n    result = '), launch, {'launch': {'line': 11}}),
            (AW, AW + 'drv.py', aw_drv.replace('    result = ', '    argv = ["python3", "-B"] + argv\n    result = '), launch, {'launch': {'line': 11}}),
            (AW, AW + 'drv.py', aw_drv.replace('    result = subprocess.run(argv,', '    result = subprocess.run(argv, executable="/bin/sh",'), launch),
            (AW, AW + 'drv.py', aw_drv.replace('def run(argv, root)', 'def run(argv, root, *more)'), launch),
            (AW, AW + 'drv.py', aw_drv.replace('    result = subprocess.run(argv,', '    result = None\n    if root: result = subprocess.run(argv,'), launch,
             {'launch': {'line': 11}}),
            (AW, AW + 'prog.py', aw_prog.replace('with_name("mod.py")', 'with_name("prog.py")'), imports),
            (AW, AW + 'prog.py', aw_prog.replace('spec.loader.exec_module(mod)\n', ''), imports),
            (AW, AW + 'prog.py', aw_prog + 'spec = None\n', imports),
            (AW, AW + 'prog.py', aw_prog + 'import sys\nsys.modules["mod"] = mod\n', imports),
            (AW, AW + 'prog.py', aw_prog + 'other = importlib.util.find_spec("mod")\n', imports),
            (FL, FL + 'drv.py', fl_drv.replace('cwd=root,', 'cwd="/tmp",'), launch),
            (FL, FL + 'drv.py', fl_drv + 'cmd.insert(3, "-B")\n', launch),
            (FL, FL + 'drv.py', fl_drv + 'cmd += ["x"]\n', launch),
            (FL, FL + 'drv.py', fl_drv + 'subprocess.run(cmd)\n', launch),
            (FL, FL + 'drv.py', fl_drv + 'print(len(cmd))\n', launch),
            (FL, FL + 'drv.py', fl_drv.replace('root = pathlib.Path.cwd()', 'root = pathlib.Path("/tmp")'), launch),
            (FL, FL + 'drv.py', fl_drv.replace('"flock", "/tmp', '"nice", "/tmp'), launch),
            (FL, FL + 'drv.py', fl_drv.replace('child = subprocess.Popen(cmd,', 'child = subprocess.Popen(cmd, env={},'), launch))
        for base_, path, text, message, *overrides in mutants:
            assert text != files[path], path
            mutant = commit({path: text}, 'h62 cache policy mutant')
            texts = {path: text}
            y = row(base_, repo=mutant, **(overrides[0] if overrides else {}))
            H62_CACHE_REVIEWED = review(*good, y)
            rejected(mutant, message, standalone=roots(mutant, texts) + [y])
            commit({path: files[path]}, 'h62 cache policy mutant restored')
        # Policy refusals: another rule, a file rule at the line, a tracked cache, a non-directory match.
        for text, line, extra, message in (('__pycache__/\n*.olean\n', 1, {}, 'outside the CPython cache rules'),
                                           ('*.pyc\n__pycache__/\n', 1, {}, 'names no cache directory rule'),
                                           ('__pycache__/\n!keep.pyc\n', 1, {}, 'outside the CPython cache rules'),
                                           ('__pycache__/\n', 1, {PW + '__pycache__/note.txt': 'tracked\n'}, 'output is tracked')):
            policy = commit({PW + '.gitignore': text, **extra}, 'h62 cache policy rule')
            y = row(PW, repo=policy, provenance=C if text == files[PW + '.gitignore'] else policy.ref, line=line)
            H62_CACHE_REVIEWED = review(*good, y)
            rejected(policy, message, standalone=roots(policy) + [y])
            git(root, 'rm', '-q', '-r', '--ignore-unmatch', '--', PW + '__pycache__')
            commit({PW + '.gitignore': files[PW + '.gitignore']}, 'h62 cache policy rule restored')
        # A reviewed blob whose commit did not introduce it, and a missing entry root (current: refused; historical: stale).
        y = row(PW, provenance=later.ref)
        H62_CACHE_REVIEWED = review(*good, y)
        rejected(cm, 'introducing provenance', standalone=roots() + [y])
        H62_CACHE_REVIEWED = review(*good)
        rejected(cm, 'not a python3 -B entry root', standalone=roots()[1:] + [good[0]])
        model, rows = run(later, standalone=roots(later)[1:] + good)
        assert H62_CACHE_PREFIX + good[0]['path'] not in model['entry_points'] and rows[good[1]['path']]['class'] == 'keep'
        # A changed policy, driver, program or module: stale later, refused when claimed now.
        for x, path in ((good[0], PW + '.gitignore'), (good[0], PW + 'drv.py'), (good[1], AW + 'prog.py'), (good[2], FL + 'mod.py')):
            edited = commit({path: files[path] + '\n'}, 'h62 cache policy edited')
            texts = {path: files[path] + '\n'}
            model, rows = run(edited, standalone=roots(edited, texts) + good)
            assert H62_CACHE_PREFIX + x['path'] not in model['entry_points'] and rows[x['path']]['class'] != 'keep', path
            rejected(edited, 'source mismatch', standalone=roots(edited, texts) + [dict(x, input_revision=edited.ref)])
            commit({path: files[path]}, 'h62 cache policy restored')
        # Schema, invocation, review and conflict errors.
        x = good[0]
        for change, message in (({'extra': 1}, 'invalid h62 cache policy role definition'), ({'purpose': ' '}, 'invalid h62 cache policy role definition'),
                                ({'line': '1'}, 'invalid h62 cache policy role definition'), ({'launch': {'line': True}}, 'invalid h62 cache policy role definition'),
                                ({'program': {'extra': 1}}, 'invalid h62 cache policy role definition'),
                                ({'input_revision': C[:12]}, 'full commit revision'),
                                ({'command': ['python3', PW + 'drv.py']}, 'unsupported h62 cache policy role invocation'),
                                ({'launch': {'form': 'other'}}, 'unsupported h62 cache policy role invocation'),
                                ({'program': {'import': 'other'}}, 'unsupported h62 cache policy role invocation'),
                                ({'module': {'path': AW + 'mod.py'}}, 'unsupported h62 cache policy role invocation'),
                                ({'path': PW + 'prog.py'}, 'unsupported h62 cache policy role invocation'),
                                ({'line': 2}, 'unreviewed h62 cache policy role'), ({'launch': {'line': 11}}, 'unreviewed h62 cache policy role'),
                                ({'provenance': later.ref}, 'unreviewed h62 cache policy role')):
            y = dict(x, **{k: dict(x[k], **v) if isinstance(v, dict) else v for k, v in change.items()})
            rejected(cm, message, standalone=roots() + [y])
        rejected(cm, 'conflicting standalone definitions', standalone=roots() + [x, dict(x, purpose='Other.')])
        # A current definition of the path supersedes a historical one, in either order.
        now = dict(x, input_revision=later.ref, purpose='Now.')
        for order in (1, -1):
            model, _ = run(later, standalone=roots(later) + [x, now][::order])
            assert model['entry_points'][H62_CACHE_PREFIX + x['path']]['purpose'] == 'Now.'
        H62_CACHE_REVIEWED = saved
        rejected(cm, 'unreviewed h62 cache policy role', standalone=roots() + [x])
    finally:
        H62_CACHE_REVIEWED = saved
        git(root, 'rm', '-q', '-r', '--ignore-unmatch', '--', D, 'tests/cm-later.txt')
        git(root, '-c', 'user.name=Control', '-c', 'user.email=control@example.invalid', 'commit', '-qm', 'h62 cache policies removed')


_cm('register_source_role')(H62_CACHE_KIND, h62_cache_policy_root, late=True)
_cm('FORM_CONTROLS').append(h62_cache_controls)
