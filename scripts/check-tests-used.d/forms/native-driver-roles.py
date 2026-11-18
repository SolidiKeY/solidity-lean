# H1082 (gh#1433, Q-H62-NATIVE-CONSUMER-ROLES, Option A), x1aa: the native
# driver source role. Exec'd by registry.load_forms in the namespace of
# fragments.py after roles.py (see registry.py's header for the interface).
#
# Standalone kind native-driver-source-role: a reviewed live Lean source under
# tests/ whose exact repository path a reviewed Python driver hands to the Lean
# MCP server (lean_lsp_mcp) as the file_path of a lean_diagnostic_messages
# call, in one of two audited driver forms:
#   mcp-client  the driver itself is the MCP client: it imports ClientSession,
#               StdioServerParameters and stdio_client from mcp, spawns
#               `-m lean_lsp_mcp`, calls call_tool('lean_diagnostic_messages',
#               {'file_path': ...}) and holds the path once, at the reviewed
#               line, as an argparse --default (bare or in Path(...)) or as a
#               module-level NAME = 'P' binding;
#   mcp-relay   the driver binds NAME = 'P' once at the reviewed line, builds
#               dict(file_path=NAME, ...) and runs a command list naming a
#               reviewed relay script followed by the tool name; the relay is an
#               MCP client spawning lean_lsp_mcp whose only call is
#               call_tool(sys.argv[1], json.loads(sys.argv[2])).
# Rows (source, blob, introducing commit) and invocations (source, blob,
# driver, driver blob, driver introducing commit, line, form, relay, relay
# blob, relay introducing commit) are reviewed one by one; the dataflow from
# the literal to file_path is part of that per-blob review, the recogniser
# only re-checks the form. The H1015 staleness rules apply (Lake package,
# root library or Lean importer of the source: no root).
# Source-retention credit only: never run, never certified to elaborate or
# pass; no execution, pass, proof, driver, relay, read, import or output credit.
import ast, re, shlex

# The fragments.py, roles.py and registry.py names this form uses, bound to the same objects (the loader sees no
# rebinding) so that they are defined names here; the derived REVIEWED_LEAN_FIXTURES is read at call time.
_native_driver_namespace = globals()
(FIXTURE_COMMAND, FORM_CONTROLS, LATE_SOURCE_ROLE_KINDS, LEAN_FIXTURE_KIND, REVIEWED_LEAN_CHECKS, SOURCE_ROLE_KINDS, _LEAN_NAME, _REVIEW_DIRECTORIES, _clean, _introduced, _outside_root_libraries, _plain_lines, _review_table, _role_current, _role_schema, canonical, register_source_role) = (
    _native_driver_namespace[name] for name in ('FIXTURE_COMMAND', 'FORM_CONTROLS', 'LATE_SOURCE_ROLE_KINDS', 'LEAN_FIXTURE_KIND', 'REVIEWED_LEAN_CHECKS', 'SOURCE_ROLE_KINDS', '_LEAN_NAME', '_REVIEW_DIRECTORIES', '_clean', '_introduced', '_outside_root_libraries', '_plain_lines', '_review_table', '_role_current', '_role_schema', 'canonical', 'register_source_role'))

NATIVE_DRIVER_KIND = 'native-driver-source-role'
NATIVE_DRIVER_PREFIX = 'native-driver:'
NATIVE_DRIVER_TOOLS = ('lean_diagnostic_messages',)
NATIVE_DRIVER_FORMS = ('mcp-client', 'mcp-relay')
NATIVE_DRIVER_SOURCES = _review_table('''
@8786d84e4d52ff645d8d7fb01cd08a9b509f54d2
T:h62/item6/migrate-backend/TernaryDependency.lean e2abcf2765c28e019c9e8b67512dde6e4ea50fd4
@b97125425c8eadbe2174b07fcda96c99c9088469
T:h62/item2/audit-abi-world/H62AbiWorld/CodecWitnesses.lean 964af62f95acb6dae17a164a50236a782ff23701
''')
_NATIVE_DRIVER_CALLS = '''
T:h62/item6/migrate-backend/TernaryDependency.lean
 H:item6/migrate-backend/check_fixture_mcp.py 780f4b52735d7c16371af0903dc14c8cb661d21c 33dcda9f8b3b5d45e12f788b0f208ec9a6b24b28 23 mcp-client
T:h62/item2/audit-abi-world/H62AbiWorld/CodecWitnesses.lean
 H:item2/audit-abi-world/measure.py b054f2db8c19e7127f4e7856070e625775d9b5b0 ae2df853a300afd910e86bc09e6c82eca3999141 18 mcp-relay H:item2/audit-abi-world/mcp_call.py 2ca1426faff254135184084f149b45ddfbd0397a b97125425c8eadbe2174b07fcda96c99c9088469
 H:item2/audit-abi-world/resume_measure.py d09224104d04d8704551adf2a37c81e6b5a53f55 8e3023d10b62574b7be84630c064b53b8dcfbb09 18 mcp-relay H:item2/audit-abi-world/resume_mcp_call.py 68a3a88a246c7da9a75e247c890bedb87206a28e 8e3023d10b62574b7be84630c064b53b8dcfbb09
'''


def native_driver_table(text, sources):
    """`source` lines (relative to _REVIEW_DIRECTORIES), each followed by
    indented `driver blob commit line form [relay blob commit]` rows; every
    source is a reviewed (path, blob, commit) row of `sources`."""
    blobs, rows, source = {p: b for p, b, _ in sources}, set(), None
    expand = lambda word: _REVIEW_DIRECTORIES[word[:2]] + word[2:]
    for line in filter(str.strip, text.split('\n')):
        words = line.split()
        if not line.startswith(' '):
            if len(words) != 1 or expand(words[0]) not in blobs: raise ValueError('invalid native driver review table')
            source = expand(words[0]); continue
        if source is None or len(words) not in (5, 8) or words[4] not in NATIVE_DRIVER_FORMS or (len(words) == 8) != (words[4] == 'mcp-relay'):
            raise ValueError('invalid native driver review table')
        relay = (expand(words[5]), words[6], words[7]) if len(words) == 8 else (None, None, None)
        rows.add((source, blobs[source], expand(words[0]), words[1], words[2], int(words[3]), words[4]) + relay)
    if {r[0] for r in rows} != set(blobs): raise ValueError('native driver source without a reviewed invocation')
    return frozenset(rows)


NATIVE_DRIVER_INVOCATIONS = native_driver_table(_NATIVE_DRIVER_CALLS, NATIVE_DRIVER_SOURCES)


def native_driver_command(path):
    """The recorded MCP call of the role: tool and source, never run."""
    return ['lean_lsp_mcp', NATIVE_DRIVER_TOOLS[0], path]


def native_driver_source_interface(lean_code, path, text):
    """Header imports (possibly none) and the first body line of a driven Lean
    source, or None: lean_fixture_interface's rules, except that the body may
    follow no import (a self-contained fixture); still no later import,
    prelude or module line, no #exit, and a column-0 declaration or evaluation
    command (FIXTURE_COMMAND) in the body."""
    if not path.endswith('.lean') or not isinstance(text, str) or not _plain_lines(text) or '\0' in text: return None
    code = lean_code(text)
    if code.count('\n') != text.count('\n') or re.search(r'#exit(?![\w.\'])', code): return None
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
    return {'imports': imports, 'body_line': body} if body and command else None


_NATIVE_DRIVER_DYNAMIC = frozenset({'exec', 'eval', 'compile', '__import__', 'importlib', 'runpy', 'globals', 'locals', 'vars', 'setattr'})


def _native_driver_tree(text):
    """The parsed module, or None for unparsable, NUL or dynamic-code text."""
    if not isinstance(text, str) or '\0' in text or not _plain_lines(text): return None
    try: tree = ast.parse(text)
    except (SyntaxError, ValueError): return None
    if any(isinstance(n, ast.Name) and n.id in _NATIVE_DRIVER_DYNAMIC or isinstance(n, ast.Attribute) and n.attr in _NATIVE_DRIVER_DYNAMIC
           or isinstance(n, (ast.Import, ast.ImportFrom)) and any(a.name.split('.')[0] in _NATIVE_DRIVER_DYNAMIC for a in n.names)
           or isinstance(n, ast.ImportFrom) and (n.module or '').split('.')[0] in _NATIVE_DRIVER_DYNAMIC for n in ast.walk(tree)):
        return None
    return tree


def _native_driver_client(tree):
    """An MCP client module: the three mcp names imported exactly, rebound
    nowhere, and one StdioServerParameters call spawning `-m lean_lsp_mcp`."""
    wanted = {('mcp', 'ClientSession'), ('mcp', 'StdioServerParameters'), ('mcp.client.stdio', 'stdio_client')}
    found = {(n.module, a.name) for n in tree.body if isinstance(n, ast.ImportFrom) and n.level == 0 for a in n.names if a.asname is None}
    if not wanted <= found: return False
    names = {name for _, name in wanted}
    if any(isinstance(n, ast.Name) and n.id in names and not isinstance(n.ctx, ast.Load)
           or isinstance(n, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)) and n.name in names
           or isinstance(n, (ast.Import, ast.ImportFrom)) and any((a.asname or a.name) in names for a in n.names) and n not in tree.body
           or isinstance(n, ast.arg) and n.arg in names for n in ast.walk(tree)): return False
    spawns = [n for n in ast.walk(tree) if isinstance(n, ast.Call) and isinstance(n.func, ast.Name) and n.func.id == 'StdioServerParameters']
    if len(spawns) != 1: return False
    args = [k.value for k in spawns[0].keywords if k.arg == 'args']
    if len(args) != 1 or not isinstance(args[0], ast.List): return False
    words = [e.value if isinstance(e, ast.Constant) else None for e in args[0].elts]
    return any(words[i:i + 2] == ['-m', 'lean_lsp_mcp'] for i in range(len(words)))


def _native_driver_literal(tree, path, line):
    """The one string constant equal to path, on the single line `line`, or None."""
    hits = [n for n in ast.walk(tree) if isinstance(n, ast.Constant) and n.value == path]
    if len(hits) != 1 or hits[0].lineno != line or hits[0].end_lineno != line: return None
    return hits[0]


def _native_driver_binding(tree, literal):
    """NAME when `NAME = literal` is a module-level single-target binding and NAME is bound nowhere else."""
    for node in tree.body:
        if isinstance(node, ast.Assign) and node.value is literal and len(node.targets) == 1 and isinstance(node.targets[0], ast.Name):
            name = node.targets[0].id
            stores = [n for n in ast.walk(tree) if isinstance(n, ast.Name) and n.id == name and not isinstance(n.ctx, ast.Load)]
            rebound = [n for n in ast.walk(tree) if isinstance(n, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef, ast.arg, ast.alias))
                       and name in (getattr(n, 'name', None), getattr(n, 'arg', None), getattr(n, 'asname', None))]
            if len(stores) == 1 and not rebound and not any(isinstance(n, (ast.Global, ast.Nonlocal)) and name in n.names for n in ast.walk(tree)):
                return name
    return None


def _native_driver_default(tree, literal):
    """True when literal is the default= of an add_argument call, bare or as Path(literal)."""
    for node in ast.walk(tree):
        if isinstance(node, ast.Call) and isinstance(node.func, ast.Attribute) and node.func.attr == 'add_argument':
            for k in node.keywords:
                if k.arg != 'default': continue
                value = k.value
                if value is literal: return True
                if (isinstance(value, ast.Call) and isinstance(value.func, ast.Name) and value.func.id == 'Path'
                        and len(value.args) == 1 and value.args[0] is literal and not value.keywords): return True
    return False


def _native_driver_tool_call(node):
    """call_tool(TOOL, {...'file_path': ...}) with a reviewed constant tool."""
    return (isinstance(node, ast.Call) and isinstance(node.func, ast.Attribute) and node.func.attr == 'call_tool' and len(node.args) == 2
            and not node.keywords and isinstance(node.args[0], ast.Constant) and node.args[0].value in NATIVE_DRIVER_TOOLS
            and isinstance(node.args[1], ast.Dict) and any(isinstance(k, ast.Constant) and k.value == 'file_path' for k in node.args[1].keys))


def _native_driver_argv(node, index):
    return (isinstance(node, ast.Subscript) and isinstance(node.value, ast.Attribute) and node.value.attr == 'argv'
            and isinstance(node.value.value, ast.Name) and node.value.value.id == 'sys' and isinstance(node.slice, ast.Constant)
            and node.slice.value == index and type(index) is int)


def native_driver_relay(text):
    """An audited relay: an MCP client whose one call_tool is
    call_tool(sys.argv[1], json.loads(sys.argv[2]))."""
    tree = _native_driver_tree(text)
    if tree is None or not _native_driver_client(tree): return False
    calls = [n for n in ast.walk(tree) if isinstance(n, ast.Call) and isinstance(n.func, ast.Attribute) and n.func.attr == 'call_tool']
    if len(calls) != 1 or calls[0].keywords or len(calls[0].args) != 2: return False
    tool, params = calls[0].args
    return (_native_driver_argv(tool, 1) and isinstance(params, ast.Call) and isinstance(params.func, ast.Attribute)
            and params.func.attr == 'loads' and isinstance(params.func.value, ast.Name) and params.func.value.id == 'json'
            and len(params.args) == 1 and not params.keywords and _native_driver_argv(params.args[0], 2))


def native_driver_invocation(text, path, line, form, relay=None, relay_text=None):
    """True when the driver text hands path to lean_lsp_mcp in the audited form."""
    tree = _native_driver_tree(text)
    literal = None if tree is None else _native_driver_literal(tree, path, line)
    if literal is None: return False
    if form == 'mcp-client':
        return (relay is None and _native_driver_client(tree) and (_native_driver_default(tree, literal) or _native_driver_binding(tree, literal) is not None)
                and any(_native_driver_tool_call(n) for n in ast.walk(tree)))
    if form != 'mcp-relay' or not isinstance(relay, str) or relay == path or not native_driver_relay(relay_text): return False
    name = _native_driver_binding(tree, literal)
    if name is None: return False
    def file_path(node):
        is_name = lambda v: isinstance(v, ast.Name) and v.id == name
        if isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id == 'dict' and not node.args:
            return any(k.arg == 'file_path' and is_name(k.value) for k in node.keywords)
        return isinstance(node, ast.Dict) and any(isinstance(k, ast.Constant) and k.value == 'file_path' and is_name(v) for k, v in zip(node.keys, node.values))
    if not any(file_path(n) for n in ast.walk(tree)): return False
    for node in ast.walk(tree):
        if isinstance(node, ast.List):
            words = [e.value if isinstance(e, ast.Constant) else None for e in node.elts]
            if any(words[i] == relay and words[i + 1] in NATIVE_DRIVER_TOOLS for i in range(len(words) - 1)): return True
    return False


def native_driver_root(classifier, graph, catalog, entry, reviewed=None, invocations=None):
    """H1082: a reviewed Lean source driven through lean_lsp_mcp by reviewed
    Python drivers, as a source-only role.

    Binds native_driver_command(P), the blob, its interface, the reviewed
    introducing commit and each invocation (driver, blob, introducing commit,
    line, form and, for mcp-relay, the relay's path, blob and introducing
    commit). A Lake package, root library or Lean importer of P makes it stale.
    Never a validated runner; anchors nothing. Kept later while source, drivers
    and relays are unchanged; a current definition of the path supersedes it."""
    reviewed = NATIVE_DRIVER_SOURCES if reviewed is None else reviewed
    invocations = NATIVE_DRIVER_INVOCATIONS if invocations is None else invocations
    repo = graph.repo; role = 'native driver role'
    required = {'path', 'input_revision', 'source_blob', 'command', 'kind', 'interface', 'provenance', 'invocations', 'purpose'}
    _role_schema(classifier, catalog, entry, required, role); calls = entry['invocations']
    base, relayed = {'driver', 'driver_blob', 'driver_commit', 'line', 'form'}, {'relay', 'relay_blob', 'relay_commit'}
    if (not isinstance(calls, list) or not calls
            or any(not isinstance(c, dict) or c.get('form') not in NATIVE_DRIVER_FORMS or set(c) != (base | relayed if c['form'] == 'mcp-relay' else base)
                   or type(c['line']) is not int or not all(isinstance(v, str) for k, v in c.items() if k != 'line') for c in calls)
            or len({canonical(c) for c in calls}) != len(calls)):
        raise ValueError('invalid ' + role + ' definition')
    p = entry['path']; revision = entry['input_revision']; doc = entry['provenance']; blob = entry['source_blob']
    if entry['command'] != native_driver_command(p) or not p.endswith('.lean') or not p.startswith('tests/') or _clean(p) != p:
        raise ValueError('unsupported ' + role + ' invocation: ' + p)
    if doc['path'] != p or doc['blob'] != blob or (p, blob, doc['commit']) not in reviewed: raise ValueError('unreviewed ' + role + ': ' + p)
    row = lambda c: (p, blob, c['driver'], c['driver_blob'], c['driver_commit'], c['line'], c['form'], c.get('relay'), c.get('relay_blob'), c.get('relay_commit'))
    if any(row(c) not in invocations or not c['driver'].endswith('.py') or c.get('relay', '.py')[-3:] != '.py' for c in calls):
        raise ValueError('unreviewed ' + role + ' invocation: ' + p)
    programs = sorted({(c['driver'], c['driver_blob'], c['driver_commit']) for c in calls}
                      | {(c['relay'], c['relay_blob'], c['relay_commit']) for c in calls if 'relay' in c})
    if not _role_current(classifier, repo, catalog, entry, [(p, blob)] + [(q, b) for q, b, _ in programs]): return
    if repo.tree[p][0] != '100644' or p not in repo.texts or any(repo.tree[q][0] not in ('100644', '100755') or q not in repo.texts for q, _, _ in programs):
        raise ValueError('unsupported ' + role + ' invocation: ' + p)
    if not _introduced(classifier, repo, doc['commit'], p, blob): raise ValueError(role + ' lacks its introducing provenance: ' + p)
    if not all(_introduced(classifier, repo, c, q, b) for q, b, c in programs): raise ValueError(role + ' driver lacks its introducing provenance: ' + p)
    parts = p.split('/')
    if (any('/'.join(parts[:k]) + '/' + name in repo.tree for k in range(1, len(parts)) for name in ('lakefile.toml', 'lakefile.lean'))
            or 'lakefile.lean' in repo.tree or not _outside_root_libraries(repo, p)
            or any(e['target'] == p and e['operation'] == 'Lean import' for edges in graph.edges.values() for e in edges)): return
    interface = native_driver_source_interface(classifier['lean_code'], p, repo.texts[p])
    if interface is None: raise ValueError(role + ' lacks an audited driven-source interface: ' + p)
    if canonical(interface) != canonical(entry['interface']): raise ValueError(role + ' interface mismatch: ' + p)
    for c in calls:
        if not native_driver_invocation(repo.texts[c['driver']], p, c['line'], c['form'], c.get('relay'), repo.texts.get(c.get('relay'))):
            raise ValueError(role + ' driver does not run the source: ' + c['driver'])
    identity = NATIVE_DRIVER_PREFIX + p
    graph.root(p, 'source-only native driver source', shlex.join(entry['command']), calls[0]['driver'], calls[0]['line'], root_id=identity)
    if identity not in graph.roots: return
    graph.roots[identity].update({'source_only': True, 'native_driver_role': True, 'source_blob': blob, 'purpose': entry['purpose'],
        'interface': interface, 'provenance': doc, 'invocations': calls, 'source_declaration_revision': revision,
        'validation_at_measured_revision': {'status': 'unavailable', 'command': entry['command'],
            'reason': 'Reviewed Lean source handed by reviewed Python drivers to the Lean MCP server (lean_diagnostic_messages); never run or certified to elaborate or pass. Source-retention role only: no execution, pass, proof, driver, relay, read, import, output or runtime credit.'}})


register_source_role(NATIVE_DRIVER_KIND, native_driver_root)


def native_driver_controls(env):
    """H1082 controls, run at the end of successor_controls: the reviewed
    tables, both driver forms, the role and its negative controls."""
    commit, run, rejected, blob, files = (env[k] for k in ('commit', 'run', 'rejected', 'blob', 'files'))
    code = env['classifier']['lean_code']
    # The audited witnesses: 2 sources, 3 driver lines, disjoint from the Lean gate roles.
    assert len(NATIVE_DRIVER_SOURCES) == 2 and len(NATIVE_DRIVER_INVOCATIONS) == 3
    assert {(p, b) for p, b, _ in NATIVE_DRIVER_SOURCES} == {r[:2] for r in NATIVE_DRIVER_INVOCATIONS}
    assert not {p for p, _, _ in NATIVE_DRIVER_SOURCES} & {p for p, _, _ in REVIEWED_LEAN_CHECKS | _native_driver_namespace['REVIEWED_LEAN_FIXTURES']}
    assert ('tests/h62/item2/audit-abi-world/H62AbiWorld/CodecWitnesses.lean', '964af62f95acb6dae17a164a50236a782ff23701',
            'scripts/h62/item2/audit-abi-world/measure.py', 'b054f2db8c19e7127f4e7856070e625775d9b5b0', 'ae2df853a300afd910e86bc09e6c82eca3999141',
            18, 'mcp-relay', 'scripts/h62/item2/audit-abi-world/mcp_call.py', '2ca1426faff254135184084f149b45ddfbd0397a',
            'b97125425c8eadbe2174b07fcda96c99c9088469') in NATIVE_DRIVER_INVOCATIONS
    assert SOURCE_ROLE_KINDS[NATIVE_DRIVER_KIND] is native_driver_root and NATIVE_DRIVER_KIND not in LATE_SOURCE_ROLE_KINDS
    for table in ('T:h62/x.lean\n', 'T:h62/item6/migrate-backend/TernaryDependency.lean\n H:a.py b c 1 mcp-relay\n',
                  'T:h62/item6/migrate-backend/TernaryDependency.lean\n H:a.py b c 1 mcp-client H:r.py b c\n',
                  ' H:a.py b c 1 mcp-client\n', 'T:h62/item6/migrate-backend/TernaryDependency.lean\n H:a.py b c 1 other\n'):
        try: native_driver_table(table, NATIVE_DRIVER_SOURCES); raise AssertionError('native driver table accepted: ' + table)
        except ValueError: pass
    # The driven-source interface.
    X, M, R = 'tests/n/F.lean', 'tests/n/measure.py', 'tests/n/call.py'
    fixture = '/-! driven -/\nnamespace F\ndef v : Nat := 1\ntheorem t : v = 1 := rfl\nend F\n'
    face = {'imports': [], 'body_line': 2}
    assert native_driver_source_interface(code, X, fixture) == face
    assert native_driver_source_interface(code, X, 'import A B\n#eval 1\n') == {'imports': ['A', 'B'], 'body_line': 2}
    for t in ('', '-- c\n', 'import A\n', 'import A\n#check A\n', fixture + 'import B\n', 'prelude\n' + fixture, fixture + '#exit\n',
              fixture + '\0\n', 'import A\r\n#eval 1\n', 'module\n' + fixture, ' import A\n#eval 1\n', 'import all A\n#eval 1\n'):
        assert native_driver_source_interface(code, X, t) is None, t
    assert native_driver_source_interface(code, 'x.py', fixture) is None
    # Driver forms.
    head = ('import argparse, asyncio, json, sys\nfrom pathlib import Path\nfrom mcp import ClientSession, StdioServerParameters\n'
            'from mcp.client.stdio import stdio_client\n')
    tail = ('async def main(path):\n    server = StdioServerParameters(command=sys.executable, args=["-m", "lean_lsp_mcp", "--lean-project-path", "."])\n'
            '    async with stdio_client(server) as (r, w):\n        async with ClientSession(r, w) as session:\n'
            '            await session.call_tool("lean_diagnostic_messages", {"file_path": path, "interactive": False})\n')
    client = (head + 'parser = argparse.ArgumentParser()\nparser.add_argument("--file", type=Path, default=Path("' + X + '"))\n'
              'args = parser.parse_args()\n' + tail + 'asyncio.run(main(str(args.file)))\n')
    bound = head + 'TARGET = "' + X + '"\n' + tail + 'asyncio.run(main(TARGET))\n'
    relay = (head + 'async def main():\n    server = StdioServerParameters(command=sys.executable, args=["-m", "lean_lsp_mcp"])\n'
             '    async with stdio_client(server) as (r, w):\n        async with ClientSession(r, w) as session:\n'
             '            print(await session.call_tool(sys.argv[1], json.loads(sys.argv[2])))\nasyncio.run(main())\n')
    measure = ('import json, subprocess, sys\nmodule = "' + X + '"\nparams = json.dumps(dict(file_path=module, interactive=False))\n'
               'command = [sys.executable, "-B", "' + R + '", "lean_diagnostic_messages", params]\nsubprocess.run(command, check=True)\n')
    cl, bl, ml = 6, 5, 2
    assert native_driver_invocation(client, X, cl, 'mcp-client') and native_driver_invocation(bound, X, bl, 'mcp-client')
    assert native_driver_invocation(measure, X, ml, 'mcp-relay', R, relay) and native_driver_relay(relay)
    computed = client.replace('Path("' + X + '")', 'Path("tests/n") / "F.lean"')
    adversarial = {  # (text, line, form, relay, relay text): each must be refused
        'computed': (computed, cl, 'mcp-client', None, None), 'wrong-line': (client, cl + 1, 'mcp-client', None, None),
        'twice': (client.replace('args = parser', 'SUPPORT = ["' + X + '"]\nargs = parser'), cl, 'mcp-client', None, None),
        'support-list': (head + 'SUPPORT = ["' + X + '"]\n' + tail, 5, 'mcp-client', None, None),
        'tool': (client.replace('"lean_diagnostic_messages"', '"lean_run_code"'), cl, 'mcp-client', None, None),
        'no-file-path': (client.replace('{"file_path": path,', '{"path": path,'), cl, 'mcp-client', None, None),
        'no-mcp': (client.replace('from mcp import ClientSession, StdioServerParameters', 'from mcpx import ClientSession, StdioServerParameters'), cl, 'mcp-client', None, None),
        'aliased-mcp': (client.replace('ClientSession, StdioServerParameters', 'ClientSession as C, StdioServerParameters'), cl, 'mcp-client', None, None),
        'rebound-mcp': (client.replace('args = parser.parse_args()', 'args = parser.parse_args()\nstdio_client = None'), cl, 'mcp-client', None, None),
        'no-server': (client.replace('"lean_lsp_mcp"', '"other_server"'), cl, 'mcp-client', None, None),
        'two-servers': (client.replace('asyncio.run', 'StdioServerParameters(command="x", args=["-m", "lean_lsp_mcp"])\nasyncio.run'), cl, 'mcp-client', None, None),
        'eval': (client.replace('args = parser.parse_args()', 'args = parser.parse_args()\neval("1")'), cl, 'mcp-client', None, None),
        'importlib': ('import importlib\n' + client, cl + 1, 'mcp-client', None, None),
        'rebound-name': (bound.replace('asyncio.run(main(TARGET))', 'TARGET = sys.argv[1]\nasyncio.run(main(TARGET))'), bl, 'mcp-client', None, None),
        'positional-default': (client.replace('default=Path("' + X + '")', 'help="' + X + '"'), cl, 'mcp-client', None, None),
        'unparsable': (client + 'def (\n', cl, 'mcp-client', None, None),
        'client-with-relay': (client, cl, 'mcp-client', R, relay), 'unknown-form': (client, cl, 'mcp-shell', None, None),
        'relay-missing': (measure, ml, 'mcp-relay', R, None),
        'relay-fixed-tool': (measure, ml, 'mcp-relay', R, relay.replace('call_tool(sys.argv[1]', 'call_tool("lean_run_code"')),
        'relay-argv-shift': (measure, ml, 'mcp-relay', R, relay.replace('sys.argv[2]', 'sys.argv[3]')),
        'relay-two-calls': (measure, ml, 'mcp-relay', R, relay.replace('asyncio.run(main())', 'session = None\nasyncio.run(main())\nsession.call_tool(sys.argv[1], json.loads(sys.argv[2]))')),
        'relay-no-server': (measure, ml, 'mcp-relay', R, relay.replace('"lean_lsp_mcp"', '"x"')),
        'relay-other-path': (measure, ml, 'mcp-relay', 'tests/n/other.py', relay),
        'relay-other-tool': (measure.replace('"' + R + '", "lean_diagnostic_messages"', '"' + R + '", "lean_build"'), ml, 'mcp-relay', R, relay),
        'relay-not-adjacent': (measure.replace('"' + R + '", "lean_diagnostic_messages"', '"' + R + '", "--", "lean_diagnostic_messages"'), ml, 'mcp-relay', R, relay),
        'relay-no-file-path': (measure.replace('dict(file_path=module', 'dict(path=module'), ml, 'mcp-relay', R, relay),
        'relay-other-name': (measure.replace('dict(file_path=module', 'dict(file_path=other'), ml, 'mcp-relay', R, relay),
        'relay-default-only': (client, cl, 'mcp-relay', R, relay), 'relay-is-source': (measure, ml, 'mcp-relay', X, relay),
        'relay-local': (measure.replace('module = "' + X + '"\n', 'def f():\n    module = "' + X + '"\n'), ml + 1, 'mcp-relay', R, relay),
    }
    for name, (text, n, form, rel, rtext) in adversarial.items():
        assert not native_driver_invocation(text, X, n, form, rel, rtext), name
    # The role on a synthetic repository.
    D, B = 'tests/n/drive.py', 'tests/n/bound.py'
    add = {X: fixture, D: client, B: bound, M: measure, R: relay, 'tests/n/I.lean': fixture.replace('F', 'I'),
           'tests/n/J.lean': 'import tests.n.I\n#eval 1\n', 'tests/n/C.lean': 'import A\n#check A\n', 'tests/npkg/lakefile.toml': 'name = "npkg"\n',
           'tests/npkg/F.lean': fixture, 'tests/n/other.py': client.replace(X, 'tests/n/I.lean')}
    nd = commit(add, 'native drivers'); L = nd.ref; nl = commit({'tests/unrelated-native.txt': 'n\n'}, 'native drivers later')
    call = lambda d=D, n=cl, form='mcp-client', **k: dict({'driver': d, 'driver_blob': blob(nd, d), 'driver_commit': L, 'line': n, 'form': form}, **k)
    relayed = lambda **k: call(M, ml, 'mcp-relay', **dict({'relay': R, 'relay_blob': blob(nd, R), 'relay_commit': L}, **k))
    mk = lambda p=X, interface=face, calls=None: {
        'path': p, 'input_revision': L, 'source_blob': blob(nd, p), 'kind': NATIVE_DRIVER_KIND, 'command': native_driver_command(p),
        'interface': interface, 'provenance': {'commit': L, 'path': p, 'blob': blob(nd, p)}, 'invocations': calls or [call()],
        'purpose': 'Synthetic driven source.'}
    srcs = (X, 'tests/n/I.lean', 'tests/n/C.lean', 'tests/npkg/F.lean')
    sources = frozenset({(p, blob(nd, p), L) for p in srcs})
    def calls_for(p):
        rows = {(p, blob(nd, p), d, blob(nd, d), L, n, 'mcp-client', None, None, None) for d, n in ((D, cl), (B, bl), ('tests/n/other.py', cl))}
        return rows | {(p, blob(nd, p), M, blob(nd, M), L, ml, 'mcp-relay', R, blob(nd, R), L)}
    invocations = frozenset(r for p in srcs for r in calls_for(p))
    role = mk(); base_model, base = run(nl, entries=[])
    assert base[X]['class'] != 'keep' and base[D]['class'] != 'keep'
    saved = SOURCE_ROLE_KINDS[NATIVE_DRIVER_KIND]
    SOURCE_ROLE_KINDS[NATIVE_DRIVER_KIND] = lambda c, g, k, e: native_driver_root(c, g, k, e, sources, invocations)
    try:
        everything = mk(calls=[call(), call(B, bl), relayed()])
        for repo in (nd, nl):
            for definition in (role, everything, mk(calls=[relayed()])):
                model, rows = run(repo, standalone=[definition]); entry = model['entry_points'][NATIVE_DRIVER_PREFIX + X]
                assert rows[X]['class'] == 'keep' and entry['source_only'] and entry['native_driver_role'] and not entry.get('lean_fixture_role')
                assert entry['validation_at_measured_revision']['status'] == 'unavailable' and entry['invocations'] == definition['invocations']
                assert entry['command'] == 'lean_lsp_mcp lean_diagnostic_messages ' + X and entry['interface'] == face
                assert entry['location'] == '%s:%d' % (definition['invocations'][0]['driver'], definition['invocations'][0]['line'])
                if repo is nl:  # no driver, relay, import, read, proof or runtime credit
                    assert all(canonical(r) == canonical(base[p]) for p, r in rows.items() if p != X)
                    assert set(model['entry_points']) == set(base_model['entry_points']) | {NATIVE_DRIVER_PREFIX + X}
        Z = '0' * 40
        for change, text in (({'extra': 1}, 'invalid native driver'), ({'purpose': ' '}, 'invalid native driver'), ({'invocations': []}, 'invalid native driver'),
                             ({'invocations': [call(), call()]}, 'invalid native driver'), ({'invocations': [call(n=str(cl))]}, 'invalid native driver'),
                             ({'invocations': [call(form='mcp-shell')]}, 'invalid native driver'), ({'invocations': [call(relay=R)]}, 'invalid native driver'),
                             ({'invocations': [relayed(relay_blob=None)]}, 'invalid native driver'), ({'invocations': [call(command=['python3'])]}, 'invalid native driver'),
                             ({'provenance': {'commit': L}}, 'invalid native driver'), ({'input_revision': 'HEAD'}, 'full commit revision'),
                             ({'command': ['lake', 'lean', X]}, 'unsupported native driver role invocation'),
                             ({'command': native_driver_command(X) + ['x']}, 'unsupported native driver role invocation'),
                             ({'source_blob': Z}, 'unreviewed native driver role'), ({'provenance': dict(role['provenance'], commit=Z)}, 'unreviewed native driver role'),
                             ({'invocations': [call(n=cl + 1)]}, 'role invocation'), ({'invocations': [call(driver_blob=Z)]}, 'role invocation'),
                             ({'invocations': [call(driver_commit=Z)]}, 'role invocation'), ({'invocations': [relayed(relay_commit=Z)]}, 'role invocation'),
                             ({'invocations': [call(M, ml)]}, 'role invocation'), ({'invocations': [call(D, cl, 'mcp-relay', relay=R, relay_blob=blob(nd, R), relay_commit=L)]}, 'role invocation'),
                             ({'invocations': [call('tests/n/other.py')]}, 'native driver role driver does not run the source'),
                             ({'interface': dict(face, body_line=3)}, 'native driver role interface mismatch'),
                             ({'input_revision': Z}, 'unverifiable historical')):
            rejected(nd, text, standalone=[dict(role, **change)])
        rejected(nd, 'conflicting standalone', standalone=[role, dict(role, purpose='Other.')])
        rejected(nd, 'conflicting standalone', standalone=[role, dict(role, kind=LEAN_FIXTURE_KIND)])
        rejected(nd, 'audited driven-source interface', standalone=[mk('tests/n/C.lean', calls=[call(n=cl)])])
        for path in ('tests/n/I.lean', 'tests/npkg/F.lean'):  # importer, Lake package: stale, never a root
            assert NATIVE_DRIVER_PREFIX + path not in run(nd, standalone=[mk(path)])[0]['entry_points']
        # Reviewed rows naming a commit that did not introduce the blob are refused.
        late = {(X, blob(nd, X), D, blob(nd, D), nl.ref, cl, 'mcp-client', None, None, None),
                (X, blob(nd, X), M, blob(nd, M), L, ml, 'mcp-relay', R, blob(nd, R), nl.ref)}
        SOURCE_ROLE_KINDS[NATIVE_DRIVER_KIND] = lambda c, g, k, e: native_driver_root(c, g, k, e, sources | {(X, blob(nd, X), nl.ref)}, invocations | late)
        rejected(nl, 'native driver role driver lacks its introducing provenance', standalone=[dict(role, invocations=[call(driver_commit=nl.ref)])])
        rejected(nl, 'native driver role driver lacks its introducing provenance', standalone=[mk(calls=[relayed(relay_commit=nl.ref)])])
        rejected(nl, 'native driver role lacks its introducing provenance',
                 standalone=[dict(role, provenance=dict(role['provenance'], commit=nl.ref), invocations=[call(driver_commit=L)])])
        SOURCE_ROLE_KINDS[NATIVE_DRIVER_KIND] = lambda c, g, k, e: native_driver_root(c, g, k, e, sources, invocations)
        for order in (1, -1):  # a current definition supersedes
            model, _ = run(nl, standalone=[dict(role, input_revision=nl.ref, purpose='Now.'), role][::order])
            assert model['entry_points'][NATIVE_DRIVER_PREFIX + X]['purpose'] == 'Now.'
        # A root library, a new importer, changed source, driver or relay drops the root later; a current claim on changed bytes is refused.
        for changes, definition in (({'lakefile.toml': files['lakefile.toml'] + '[[lean_lib]]\nname = "tests"\n'}, role),
                                    ({'tests/n/J.lean': 'import tests.n.F\n#eval 1\n'}, role), ({X: fixture + '#eval 2\n'}, role),
                                    ({D: client + '\n'}, role), ({R: relay + '\n'}, mk(calls=[relayed()]))):
            edited = commit(changes, 'edited')
            model, rows = run(edited, standalone=[definition])
            assert NATIVE_DRIVER_PREFIX + X not in model['entry_points'] and rows[X]['class'] != 'keep', changes
            if set(changes) & {X, D, R}: rejected(edited, 'source mismatch', standalone=[dict(definition, input_revision=edited.ref)])
            commit({X: fixture, D: client, R: relay, 'tests/n/J.lean': add['tests/n/J.lean'], 'lakefile.toml': files['lakefile.toml']}, 'restored')
        SOURCE_ROLE_KINDS[NATIVE_DRIVER_KIND] = lambda c, g, k, e: native_driver_root(c, g, k, e, frozenset(), invocations)
        rejected(nd, 'unreviewed native driver role', standalone=[role])
        SOURCE_ROLE_KINDS[NATIVE_DRIVER_KIND] = lambda c, g, k, e: native_driver_root(c, g, k, e, sources, frozenset())
        rejected(nd, 'unreviewed native driver role invocation', standalone=[role])
    finally: SOURCE_ROLE_KINDS[NATIVE_DRIVER_KIND] = saved
    # The default tables refuse the synthetic role: nothing is credited without a reviewed row.
    rejected(nd, 'unreviewed native driver role', standalone=[role])


FORM_CONTROLS.append(native_driver_controls)
