# Census form registry (x1y), exec'd by fragments.py in its namespace after roles.py and the kind tables.
# Every forms/*.py (sorted) is exec'd in that namespace; a form never edits a shared checker file. It may:
#   register_source_role(kind, root, late=False)  -> SOURCE_ROLE_KINDS / LATE_SOURCE_ROLE_KINDS (no duplicate kind)
#   FORM_CONTROLS.append(control)                  -> control(env) runs at the end of successor_controls, env = its locals()
#   register_consumer_section(section, keys, framed, handler)  -> CONSUMER_HANDLERS: section -> (identity keys,
#       frames-normalised flag, handler(classifier, graph, catalog, rows)); CONSUMER_SECTIONS, fragment_identity,
#       read_fragments' consumer_routes, same_revision_reads and add_consumer_routes derive from it
#   REVIEW_TABLE_PARTS[t].append(part): 'nonpy' -> REVIEWED_NONPY_ENTRIES, 'python-args' -> REVIEWED_PYTHON_ARGS with
#       part (label, rows, path prefixes); 'lean-fixtures' -> REVIEWED_LEAN_FIXTURES / _INVOCATIONS with part
#       (label, fixture rows, driver rows, path prefixes). Tables are unions; a path in two rows, a repeated row or
#       a path outside its part's prefixes is a ValueError; the self-test counts come from the parts
#   LEAN_LIBRARY_COMMANDS += (command,)            -> top-level Lean commands of the lean-library-readFile form
#   PYTHON_ARGUMENT_FORMS[source blob] = recogniser(text) -> interface or None, before python_argument_interface
#   LEAN_FIXTURE_FORMS.append(predicate(text, path, line)) -> Lean fixture driver invocation after lean_check_invocation
# A form binding a name another form, fragments.py, roles.py or this file binds is a ValueError naming both files,
# unless the name is a registry table above or listed in the form's REBINDS tuple. Errors name the form module.
# Controls: registry_controls (first FORM_CONTROLS entry) loads synthetic forms directories.
import ast, json, tempfile
from pathlib import Path
FORMS_DIRECTORY = Path(__file__).with_name('forms')
_REGISTRY_TABLES = ('SOURCE_ROLE_KINDS', 'LATE_SOURCE_ROLE_KINDS', 'FORM_CONTROLS', 'CONSUMER_HANDLERS', 'REVIEW_TABLE_PARTS',
                    'LEAN_LIBRARY_COMMANDS', 'PYTHON_ARGUMENT_FORMS', 'LEAN_FIXTURE_FORMS', '_FORM_MODULE')
_FORM_MODULE = 'registry.py'
FORM_CONTROLS = []
CONSUMER_HANDLERS = {
    'persistent_reads': (('runner', 'input_revision', 'target', 'frames'), True, persisted_reads),
    'static_routes': (('runner', 'form', 'target', 'frames'), True, lambda c, g, _, rows: static_routes(c, g, rows)),
    'git_policies': (('path',), False, lambda c, g, _, rows: git_policies(c, g, rows)),
    'persistent_module_entries': (('runner', 'input_revision', 'target', 'frames'), True,
                                  lambda c, g, k, rows: persisted_module_entries(c, g, k, rows)),
    'cache_policies': (('path',), False, lambda c, g, _, rows: cache_policies(c, g, rows))}
REVIEW_TABLE_PARTS = {
    'nonpy': [('H997', REVIEWED_NONPY_ENTRIES, ('tests/directruntime-20261104/', 'tests/upstream/')),
              ('H1025', REVIEWED_NONPY_ENTRIES_H1025, ('tests/',)), ('H1004', REVIEWED_NONPY_ENTRIES_H1004, ('tests/h28-sol/',)),
              ('H1032', REVIEWED_NONPY_ENTRIES_H1032, ('tests/', 'scripts/h62/'))],
    'python-args': [('H996', REVIEWED_PYTHON_ARGS, ('tests/directruntime-20261104/', 'tests/upstream/'))],
    'lean-fixtures': [('H1015', REVIEWED_LEAN_FIXTURES, REVIEWED_LEAN_FIXTURE_INVOCATIONS, ('tests/directruntime-20261104/',))]}
LEAN_LIBRARY_COMMANDS = ('#eval', 'run_elab', 'run_cmd')
PYTHON_ARGUMENT_FORMS = {}
LEAN_FIXTURE_FORMS = []


def register_source_role(kind, root, late=False):
    if kind in SOURCE_ROLE_KINDS or kind in LATE_SOURCE_ROLE_KINDS:
        raise ValueError('duplicate source role kind ' + repr(kind) + ' in ' + _FORM_MODULE)
    (LATE_SOURCE_ROLE_KINDS if late else SOURCE_ROLE_KINDS)[kind] = root


def register_consumer_section(section, keys, framed, handler):
    if section in CONSUMER_HANDLERS or section in FRAGMENT_SECTIONS + ('roles', 'fixtures'):
        raise ValueError('duplicate consumer section ' + repr(section) + ' in ' + _FORM_MODULE)
    if not keys or (framed and keys[-1] != 'frames'): raise ValueError('invalid consumer identity in ' + _FORM_MODULE)
    CONSUMER_HANDLERS[section] = (tuple(keys), framed, handler)


def review_union(name, column=1):
    """Column `column` of REVIEW_TABLE_PARTS[name] as one table, checked against its parts."""
    parts = REVIEW_TABLE_PARTS[name]; rows = [row for part in parts for row in part[column]]
    if (len(set(rows)) != len(rows) or column == 1 and len({row[0] for row in rows}) != len(rows)
            or any(not row[0].startswith(part[-1]) for part in parts for row in part[column])):
        raise ValueError('invalid review table parts: ' + name)
    return frozenset(rows)


def python_argument_form(blob, text):
    """H996 interface of a Python argument role: a registered form for its blob, else the audited one."""
    form = PYTHON_ARGUMENT_FORMS.get(blob)
    return form and form(text) or python_argument_interface(text)


def lean_gate_invocation(form, text, path, line):
    return lean_check_invocation(text, path, line) or form is LEAN_FIXTURE_FORM and any(f(text, path, line) for f in LEAN_FIXTURE_FORMS)


def _derive():
    global CONSUMER_SECTIONS, REVIEWED_NONPY_ENTRIES, REVIEWED_PYTHON_ARGS, REVIEWED_LEAN_FIXTURES, REVIEWED_LEAN_FIXTURE_INVOCATIONS
    CONSUMER_SECTIONS = tuple(CONSUMER_HANDLERS)
    REVIEWED_NONPY_ENTRIES = review_union('nonpy'); REVIEWED_PYTHON_ARGS = review_union('python-args')
    REVIEWED_LEAN_FIXTURES = review_union('lean-fixtures'); REVIEWED_LEAN_FIXTURE_INVOCATIONS = review_union('lean-fixtures', 2)


def _owners():
    """Module-level names of fragments.py, roles.py and this file, with the file that binds them."""
    owners = {}
    for name in ('fragments.py', 'roles.py', 'registry.py'):
        for node in ast.parse(Path(__file__).with_name(name).read_bytes()).body:
            targets = getattr(node, 'targets', None) or [getattr(node, 'target', None)]
            while targets:
                target = targets.pop()
                if isinstance(target, ast.Name): owners.setdefault(target.id, name)
                targets.extend(getattr(target, 'elts', ()))
            if isinstance(node, (ast.FunctionDef, ast.ClassDef)): owners.setdefault(node.name, name)
            if isinstance(node, (ast.Import, ast.ImportFrom)):
                for alias in node.names: owners.setdefault((alias.asname or alias.name).split('.')[0], name)
    return owners


def load_forms(directory):
    """Exec every directory/*.py in sorted order here, then derive the registry views."""
    global _FORM_MODULE
    modules = sorted(directory.glob('*.py')) if directory.is_dir() else []
    namespace = globals(); owners = _owners() if modules else {}
    for module in modules:
        label = directory.name + '/' + module.name; _FORM_MODULE = label; before = dict(namespace)
        try:
            try: exec(compile(module.read_bytes(), str(module), 'exec'), namespace)
            except Exception as error: raise ValueError('forms module ' + label + ' failed: ' + repr(error)) from error
            rebinds = namespace.pop('REBINDS', ())
            for name in sorted(k for k, v in namespace.items() if k not in before or before[k] is not v):
                if name in owners and name not in _REGISTRY_TABLES and name not in rebinds:
                    raise ValueError('forms module ' + label + ' binds ' + name + ', already bound by ' + owners[name])
                owners.setdefault(name, label)
        finally: _FORM_MODULE = 'registry.py'
    _derive()


def registry_controls(env):
    """x1y: synthetic forms directories are loaded, exercised and rejected with the module named."""
    namespace = globals(); saved = dict(namespace); scratch = tempfile.TemporaryDirectory(); tmp = Path(scratch.name)
    def load(name, modules):
        directory = tmp / name; directory.mkdir()
        for file, text in modules.items(): (directory / file).write_text(text)
        namespace.update(SOURCE_ROLE_KINDS=dict(saved['SOURCE_ROLE_KINDS']), LATE_SOURCE_ROLE_KINDS=dict(saved['LATE_SOURCE_ROLE_KINDS']),
                         FORM_CONTROLS=[], CONSUMER_HANDLERS=dict(saved['CONSUMER_HANDLERS']), PYTHON_ARGUMENT_FORMS={}, LEAN_FIXTURE_FORMS=[],
                         REVIEW_TABLE_PARTS={k: list(v) for k, v in saved['REVIEW_TABLE_PARTS'].items()})
        load_forms(directory)
    def rejected(name, modules, *needles):
        try: load(name, modules)
        except ValueError as error: assert all(n in str(error) for n in needles), (name, error)
        else: raise AssertionError('forms directory accepted: ' + name)
    try:
        assert CONSUMER_SECTIONS == tuple(CONSUMER_HANDLERS) and CONSUMER_SECTIONS[:5] == (
            'persistent_reads', 'static_routes', 'git_policies', 'persistent_module_entries', 'cache_policies')
        assert LEAN_LIBRARY_COMMANDS[:3] == ('#eval', 'run_elab', 'run_cmd')
        load_forms(tmp / 'missing'); load('empty', {})
        assert CONSUMER_SECTIONS == saved['CONSUMER_SECTIONS'] and REVIEWED_NONPY_ENTRIES == saved['REVIEWED_NONPY_ENTRIES']
        ran = []
        load('good', {'b.py': 'B_SEEN = A_SEEN\n', 'a.py': '''A_SEEN = True
def synthetic_root(classifier, graph, catalog, entry): pass
register_source_role('synthetic-role', synthetic_root, late=True)
register_consumer_section('synthetic_routes', ('path', 'note'), False, lambda c, g, k, rows: RAN.append(('handler', rows)))
REVIEW_TABLE_PARTS['nonpy'].append(('X1Y', frozenset({('tests/x1y/run.sh', 'b' * 40, 'c' * 40)}), ('tests/x1y/',)))
PYTHON_ARGUMENT_FORMS['d' * 40] = lambda text: {'synthetic': text}
LEAN_FIXTURE_FORMS.append(lambda text, path, line: text == path)
FORM_CONTROLS.append(lambda env: RAN.append(('control', env['marker'])))
LEAN_LIBRARY_COMMANDS += ('run_meta',)
_REVIEW_DIRECTORIES = dict(_REVIEW_DIRECTORIES)
REBINDS = ('_REVIEW_DIRECTORIES',)
'''.replace('RAN', 'env_ran')})
        assert namespace['B_SEEN'] and LATE_SOURCE_ROLE_KINDS['synthetic-role'] is namespace['synthetic_root'] and 'synthetic-role' not in SOURCE_ROLE_KINDS
        assert CONSUMER_SECTIONS[-1] == 'synthetic_routes' and 'REBINDS' not in namespace
        row = {'path': 'tests/a', 'note': 'n', 'other': 1}
        assert fragment_identity('synthetic_routes', row) == canonical(['tests/a', 'n'])
        try: fragment_identity('synthetic_routes', {'path': 'tests/a'}); raise AssertionError('identity')
        except ValueError: pass
        (tmp / 'json').mkdir(); (tmp / 'json' / 'forms').mkdir()
        (tmp / 'json' / 'a.json').write_text(json.dumps({'schema_version': 1, 'consumer_routes': {'synthetic_routes': [row]}}))
        (tmp / 'json' / 'forms' / 'b.json').write_text('not json')
        fragments = read_fragments(tmp / 'json'); assert fragments['synthetic_routes'] == [row]
        same_revision_reads('a' * 40, fragments)
        assert LEAN_LIBRARY_COMMANDS[-1] == 'run_meta' and _REVIEW_DIRECTORIES is not saved['_REVIEW_DIRECTORIES']
        namespace['env_ran'] = ran
        for section, (keys, framed, _) in list(CONSUMER_HANDLERS.items())[:-1]:
            CONSUMER_HANDLERS[section] = (keys, framed, lambda c, g, k, rows, s=section: ran.append((s, rows)))
        add_consumer_routes({}, None, None, fragments)
        for control in FORM_CONTROLS: control({'marker': 1})
        assert ran == [(s, []) for s in saved['CONSUMER_SECTIONS']] + [('handler', [row]), ('control', 1)]
        assert ('tests/x1y/run.sh', 'b' * 40, 'c' * 40) in REVIEWED_NONPY_ENTRIES and len(REVIEWED_NONPY_ENTRIES) == len(saved['REVIEWED_NONPY_ENTRIES']) + 1
        assert python_argument_form('d' * 40, 'x') == {'synthetic': 'x'} and python_argument_form('e' * 40, 'x = 1\n') is None
        assert lean_gate_invocation(LEAN_FIXTURE_FORM, 'p', 'p', 1) and not lean_gate_invocation(LEAN_CHECK_FORM, 'p', 'p', 1)
        rejected('kind', {'k.py': 'register_source_role(SOURCE_ONLY_KIND, None)\n'}, 'kind/k.py', SOURCE_ONLY_KIND)
        rejected('late', {'l.py': 'register_source_role(PY_IMPORT_KIND, None)\n'}, 'late/l.py')
        rejected('section', {'s.py': 'register_consumer_section("git_policies", ("path",), False, None)\n'}, 'section/s.py', 'git_policies')
        rejected('raises', {'r.py': 'raise RuntimeError("boom")\n'}, 'raises/r.py', 'boom')
        rejected('helper', {'a.py': 'def helper(): pass\n', 'b.py': 'def helper(): pass\n'}, 'helper/b.py', 'helper/a.py')
        rejected('shadow', {'a.py': 'def static_routes(*_): pass\n'}, 'shadow/a.py', 'fragments.py')
        rejected('part', {'a.py': 'REVIEW_TABLE_PARTS["nonpy"].append(("X", frozenset({("docs/x.sh", "b", "c")}), ("tests/",)))\n'}, 'nonpy')
    finally:
        namespace.clear(); namespace.update(saved); scratch.cleanup()


FORM_CONTROLS.append(registry_controls)
load_forms(FORMS_DIRECTORY)
