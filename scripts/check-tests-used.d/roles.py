"""Reviewed source roles of the census checker (H978, H992, H996, H997, H999).

Split out of fragments.py for size (H1013), unchanged in behaviour. fragments.py
executes this file in its own namespace: it uses that module's helpers and
imports, and the self-tests there patch these review sets as module globals.
"""


def source_only_program(classifier, graph, catalog, entry):
    """H978: a no-pass default program as a revision-independent source role.

    The definition binds an unchanged Python source and its genuine top-level
    default entry line; the program matches no configured CLI or unittest form.
    Unlike runnable-entrypoint it is never a validated runner, at its own
    revision or any later one: no passing run, read anchor, fixture, helper,
    child, generated-output, proof or runtime credit. A later revision keeps it
    while the blob is unchanged and the recorded commit holds that blob; a
    current definition of the same path supersedes it.
    """
    repo = graph.repo
    required = {'path', 'input_revision', 'source_blob', 'command', 'kind', 'entry_line', 'purpose'}
    if (set(entry) != required or not isinstance(entry['path'], str) or not isinstance(entry['source_blob'], str)
            or not isinstance(entry['purpose'], str) or not entry['purpose'].strip()):
        raise ValueError('invalid source-only program definition')
    p = entry['path']; revision = entry['input_revision']
    if not isinstance(revision, str) or not classifier['hex_pin'](revision, 40): raise ValueError('source-only program requires a full commit revision')
    if any(e.get('path') == p and e.get('input_revision') == revision and e.get('kind') != SOURCE_ONLY_KIND for e in catalog['standalone']):
        raise ValueError('conflicting standalone definitions: ' + p)
    if revision != repo.ref:
        if any(e.get('path') == p and e.get('input_revision') == repo.ref for e in catalog['standalone']): return
        if not _current(repo, p, entry['source_blob']): return
        if not _historical_objects(classifier, repo, revision, [(p, entry['source_blob'])]):
            raise ValueError('unverifiable historical runner demonstration: ' + revision + ':' + p)
    elif not _current(repo, p, entry['source_blob']): raise ValueError('standalone definition source mismatch: ' + p)
    command = entry['command']
    if command != ['python3', '-B', p] or not p.endswith('.py') or repo.tree[p][0] not in ('100644', '100755') or p not in repo.texts:
        raise ValueError('unsupported source-only program invocation: ' + p)
    try: lines = classifier['entrypoint_lines'](repo.bytes(p))
    except (SyntaxError, ValueError, RecursionError): lines = set()
    if type(entry['entry_line']) is not int or entry['entry_line'] not in lines:
        raise ValueError('source-only program lacks its default top-level entry: ' + p)
    if any(classifier[f](repo, p) is not None for f in ('declared_configured_cli', 'declared_module_cli', 'declared_unittest')):
        raise ValueError('source-only program matches a configured CLI or unittest form: ' + p)
    identity = 'source-only:' + p
    graph.root(p, 'source-only default program', shlex.join(command), p, entry['entry_line'], root_id=identity)
    if identity not in graph.roots: return
    graph.roots[identity].update({'source_only': True, 'source_blob': entry['source_blob'], 'purpose': entry['purpose'],
        'program_role': SOURCE_ONLY_KIND, 'source_declaration_revision': revision,
        'validation_at_measured_revision': {'status': 'unavailable', 'command': command,
            'reason': 'Default invocation is not certified to pass and matches no configured CLI form; revision-independent source role only. No read anchor, fixture, helper, child, generated-output, proof or runtime credit.'}})



NODE_MODE_KIND = 'node-mode-source-root'
NODE_MODE_PREFIX = 'node-mode:'
# H992 (gh coord#1319): each reviewed argument-bearing Node entry, bound to
# (path, source blob, mode, provenance line in that same blob). Nothing else
# is promoted: another file, blob, mode, argument or documentation line fails.
REVIEWED_NODE_MODES = frozenset({('scripts/parse-corpus.mjs', 'dd1093f6fe8bfe00ae772e0b8b4a0bc0dd4b265a', 'prepare', 17)})


def node_mode_root(classifier, graph, catalog, entry, reviewed=None):
    """H992: a reviewed `node P MODE` command as a source-only entry root.

    The definition binds the exact command ['node', P, MODE], the source blob,
    and its provenance: a whole-line // comment of that same blob that starts
    with the verbatim command. P has a top-level `const M = process.argv[2];`
    and a top-level `if (M === "MODE") {`. The root is never a validated or
    passing runner and carries no execution, fixture, proof or runtime credit;
    it anchors only node-readFileSync-walk routes, whose own checks still bind
    every frame and target to their objects at the recorded revision. A later
    revision keeps it while the blob is unchanged and the recorded commit
    holds it.
    """
    repo = graph.repo
    reviewed = REVIEWED_NODE_MODES if reviewed is None else reviewed
    required = {'path', 'input_revision', 'source_blob', 'command', 'kind', 'provenance', 'purpose'}
    if (set(entry) != required or not isinstance(entry['path'], str) or not isinstance(entry['source_blob'], str)
            or not isinstance(entry['purpose'], str) or not entry['purpose'].strip()
            or not isinstance(entry['provenance'], dict) or set(entry['provenance']) != {'path', 'blob', 'line', 'invocation'}):
        raise ValueError('invalid Node mode root definition')
    p = entry['path']; revision = entry['input_revision']; command = entry['command']; doc = entry['provenance']
    if not isinstance(revision, str) or not classifier['hex_pin'](revision, 40): raise ValueError('Node mode root requires a full commit revision')
    if any(e.get('path') == p and e.get('input_revision') == revision and e is not entry for e in catalog['standalone']):
        raise ValueError('conflicting standalone definitions: ' + p)
    if (not isinstance(command, list) or len(command) != 3 or command[:2] != ['node', p] or not isinstance(command[2], str)
            or not re.fullmatch(r'[a-z][\w-]*', command[2]) or not p.endswith(NODE_SUFFIXES)):
        raise ValueError('unsupported Node mode root invocation: ' + str(p))
    mode = command[2]
    if (doc['path'] != p or doc['blob'] != entry['source_blob'] or doc['invocation'] != shlex.join(command)
            or (p, entry['source_blob'], mode, doc['line']) not in reviewed):
        raise ValueError('unreviewed Node mode root: ' + p)
    if revision != repo.ref:
        if any(e.get('path') == p and e.get('input_revision') == repo.ref for e in catalog['standalone']): return
        if not _current(repo, p, entry['source_blob']): return
        if not _historical_objects(classifier, repo, revision, [(p, entry['source_blob'])]):
            raise ValueError('unverifiable historical runner demonstration: ' + revision + ':' + p)
    elif not _current(repo, p, entry['source_blob']): raise ValueError('standalone definition source mismatch: ' + p)
    text = repo.texts.get(p)
    if text is None or repo.tree[p][0] not in ('100644', '100755') or not _plain_lines(text):
        raise ValueError('unsupported Node mode root invocation: ' + p)
    code, _ = _js_mask(text, True); lines = text.splitlines(); line = doc['line']
    # Provenance: a comment-only line of the measured blob, command first.
    if (type(line) is not int or not 1 <= line <= len(lines) or _js_line(text, line, True)[1].strip()
            or not re.match(r'\s*//\s*' + re.escape(doc['invocation']) + r'(?:\s|$)', lines[line - 1])):
        raise ValueError('Node mode root lacks its verbatim source provenance: ' + p)
    branches = [m for m in (_js_match(text, n, r'if\s*\(\s*([\w$]+)\s*===\s*(["\'])' + re.escape(mode) + r'\2\s*\)\s*\{')
                            for n in range(1, len(lines) + 1) if mode in lines[n - 1]) if m and not m.string[:1].isspace()]
    if (len(branches) != 1 or _js_destructured(code, branches[0][1])
            or _js_unique(text, code, branches[0][1], r'const\s+' + re.escape(branches[0][1]) + r'\s*=\s*process\.argv\[2\]\s*;?') is None):
        raise ValueError('Node mode root lacks its top-level argv mode branch: ' + p)
    entry_line = next(n for n in range(1, len(lines) + 1) if not lines[n - 1][:1].isspace() and _js_match(text, n, re.escape(branches[0].group(0))))
    identity = NODE_MODE_PREFIX + p
    graph.root(p, 'source-only Node mode entry', shlex.join(command), p, entry_line, root_id=identity)
    if identity not in graph.roots: return
    graph.roots[identity].update({'source_only': True, 'node_mode_root': True, 'source_blob': entry['source_blob'],
        'purpose': entry['purpose'], 'node_mode': mode, 'provenance': doc, 'source_demonstration_revision': revision,
        'validation_at_measured_revision': {'status': 'unavailable', 'command': command,
            'reason': 'Reviewed argument-bearing entry command; source role only, never run or certified to pass. Anchors only literal walker reads in its mode; no execution, helper, child, generated-output, proof or runtime credit.'}})


# Reviewed (path, source blob, introducing commit) tables: an @COMMIT line,
# then one `path blob` row per file it introduced; each path starts with an
# abbreviation from _REVIEW_DIRECTORIES.
_REVIEW_DIRECTORIES = {'N:': 'tests/directruntime-20261104/native-browser/', 'D:': 'tests/directruntime-20261104/', 'U:': 'tests/upstream/'}


def _review_table(text):
    rows, commit = set(), None
    for line in filter(str.strip, text.split('\n')):
        if line.startswith('@'): commit = line[1:]; continue
        path, blob = line.split()
        if commit is None: raise ValueError('invalid review table')
        rows.add((_REVIEW_DIRECTORIES[path[:2]] + path[2:], blob, commit))
    return frozenset(rows)


PYTHON_ARGS_KIND = 'python-argument-source-role'
PYTHON_ARGS_PREFIX = 'py-args:'
# H996 (gh coord#1329, X1E-CONFIGURED-ROLE): each reviewed live Python program
# that needs positional arguments, a forwarded command or a subcommand, bound to
# (path, source blob, commit that introduced that blob at that path). Nothing
# else is promoted: another file, blob or provenance commit fails, and no
# argument, read, helper or output is ever recorded or credited.
REVIEWED_PYTHON_ARGS = _review_table('''
@15302eb51e3df48b9d8d46eaf50348dd1deddfb2
N:validation-admission.py 1d56a3dc820b8ae3e503fedfbd4151ff530539bd
@17f2902cdc6ab848317fc82e31a90ad2d7c4fba8
D:memory-references/bounded-check.py d9f1b14c51c9011736f0fb484f4fcf96d55cd615
@2207c1bba286538fd63e4a0ff4960ed4a593a8ab
U:baseline-20261028/invocations/bulk/timed.py c543b7aef3f458d0765b11b19741406a7ff78415
U:baseline-20261028/invocations/retries/selector.py 5b7a49f863f7c6fad8231d17d68628623948a00e
@23a42307b1b336e5477c0bb5c8d8bfe6415b6ea6
N:hardening-native-audit.py 36dd7768f98e954babdb111a2dd780a4b09877a6
@3bdd5ea4f35abb365b6bb57da56db7c23b645ac5
D:memory-references/browser-result-intake.py fbb3489b8a38e1e8a8e96fa37d95fbea09d88903
@3c3346709988f245ee64b8ffc606dfec56e6c6e1
D:memory-references/pack-cache.py c10c9d9b34044d11582ab507e76bf017a9034449
@44fa1c785b3168551c9f9589da56b5314b4ef740
D:memory-references/census-controls.py 08e1714023fc1f8e49ca09a8601d899ed54155f8
D:memory-references/runtime-boundary-census.py 526851b6c2b502a149b80d2f7f1f0c8ae87b1113
@4d4407dbbd3e5fed9ed20fe8f76dde8bc0577e89
D:memory-references/linker-attribution-controls.py 06166345217a40838f67fc52998333cfafd4bbbd
D:memory-references/linker-attribution.py 3b487c691ab3b1710149a25eef37d14301bcd563
@5a2afc72aca1a35cf555fa1b462b9de4c2ef79b7
D:shared-translator/measure.py 57c6a2f51633f72cf79c063740eff1f6ade3a26b
D:shared-translator/outer_guard.py e33bbf7efee05de73e793c8f872e2e821d8c6421
@6479617481ce020d41f7061d9dcf4dbfe9bd1ab8
D:memory-references/native-closure-evidence.py 1872f7842f78468b9d617f000e3469a7781a7fe2
@937167b745b8a2d41d3a138581d7a9931ae039e3
N:h109/input-inventory.py 2bbde0bd62a3cb448e752e521d7761937d80a240
@9be4ce0a089f0888ac165ff770ac90e3879ece0d
D:memory-references/inspect-browser-evidence.py 6f747cfa705fc346a6aedfb162e4e84df8978565
@ae8062cfb0f028667485e6f1a621ff69e62724fd
N:bounded-command.py 3c9e6eb7c60bf7906c7f605bdf0fa58f65f6a3df
@c3a7094cc0c1f8b625a5a7a6a9eae61ec64444d0
N:readbounds/serial-build.py 071755cc6574cfb9c5f97ad5703072486ffc9249
@c9230cc9692a5974728959907afa1f60733409ad
D:memory-references/native-boundary-audit.py 8c0601e110ec1c779e759456d05d64ca045a6232
D:memory-references/native-refusal-controls.py c2f89053088d9f5f615c75f408b6711c5f7b99dd
@e49c71436470851e0a3b295fa56b3b6c749e09b1
N:environment/known-stack-continuation.py 7898e125b8addd4b3badbb0d80e7001481c15741
@e6849d3bdf516099d20c33d3581d523449764018
D:control-tuples/measure-native.py c24f1113690cc7a6611d8f8d412ce5f8e77b5b1e
D:control-tuples/run-bounded.py 629db80c898eb6a19b1dc58a7bf1153bf65214dd
@f11ae9a9025990629aaed70012fc71ebb0ba295d
N:h109/docker-probe.py 2c67207ea5ce6c3d55e59f3ee2341b764028aedf
@f8329bf24319a8056b0c95927d35444a11c3e84b
N:h109/source-snapshot.py 32870f0d2fde915a2dfff0177fdb9d8b7acb1489
''')


def python_argument_interface(text):
    """The argument-bearing interface of a Python program, or None.

    Recorded from the AST: lines that read `sys.argv` (through `import sys`
    only), lines among them that take an open argv tail `sys.argv[k:]`
    (variadic or forwarded command), literal positional `add_argument` names
    and literal `add_parser` subcommand names. Not audited, giving None: any
    write, delete or method call on argv; `from sys import argv`; an argv
    attribute of anything but the sys module; any other binding of the sys
    name; `getattr` on sys; `parse_args` or `parse_known_args` with explicit
    arguments; a computed positional or subcommand name. A program with none
    of the recorded forms also gives None (a default program is
    source-only-program's role).
    """
    try: tree = ast.parse(text)
    except (SyntaxError, ValueError, RecursionError): return None
    imports = [a for n in ast.walk(tree) if isinstance(n, ast.Import) for a in n.names]
    modules = {a.asname or a.name for a in imports if a.name == 'sys'}
    if any((a.asname or a.name.split('.')[0]) in modules and a.name != 'sys' for a in imports): return None
    parents = {child: node for node in ast.walk(tree) for child in ast.iter_child_nodes(node)}
    argv, tails, positionals, subcommands = set(), set(), set(), set()
    for n in ast.walk(tree):
        if isinstance(n, ast.ImportFrom) and (n.module == 'sys' and any(a.name in ('argv', '*') for a in n.names)
                                             or any((a.asname or a.name) in modules for a in n.names)): return None
        if isinstance(n, (ast.Global, ast.Nonlocal)) and set(n.names) & modules: return None
        if isinstance(n, ast.Name) and n.id in modules and not isinstance(n.ctx, ast.Load): return None
        if isinstance(n, ast.arg) and n.arg in modules: return None
        if isinstance(n, ast.ExceptHandler) and n.name in modules: return None
        if isinstance(n, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)) and n.name in modules: return None
        if isinstance(n, ast.MatchAs) and n.name in modules or isinstance(n, ast.MatchStar) and n.name in modules: return None
        if (isinstance(n, ast.Call) and isinstance(n.func, ast.Name) and n.func.id in ('getattr', 'setattr', 'delattr', 'vars')
                and n.args and isinstance(n.args[0], ast.Name) and n.args[0].id in modules): return None
        if isinstance(n, ast.Attribute) and n.attr == 'argv':
            if not (isinstance(n.value, ast.Name) and n.value.id in modules and isinstance(n.ctx, ast.Load)): return None
            parent = parents.get(n)
            if isinstance(parent, ast.Attribute) and parent.value is n: return None  # argv.append(...) and the like
            if isinstance(parent, ast.Subscript) and parent.value is n and not isinstance(parent.ctx, ast.Load): return None
            argv.add(n.lineno)
            if (isinstance(parent, ast.Subscript) and parent.value is n and isinstance(parent.slice, ast.Slice)
                    and parent.slice.upper is None and parent.slice.step is None): tails.add(n.lineno)
        if isinstance(n, ast.Call) and isinstance(n.func, ast.Attribute):
            if n.func.attr in ('parse_args', 'parse_known_args', 'parse_intermixed_args') and (n.args or n.keywords): return None
            if n.func.attr in ('add_argument', 'add_parser'):
                first = n.args[0] if n.args else None
                literal = isinstance(first, ast.Constant) and isinstance(first.value, str)
                if not literal: return None
                if n.func.attr == 'add_parser': subcommands.add((n.lineno, first.value))
                elif not first.value.startswith('-'): positionals.add((n.lineno, first.value))
    if not (argv or positionals or subcommands): return None
    return {'argv_lines': sorted(argv), 'argv_tail_lines': sorted(tails),
            'positionals': [list(x) for x in sorted(positionals)], 'subcommands': [list(x) for x in sorted(subcommands)]}


def _introduced(classifier, repo, commit, path, blob):
    """True iff commit holds blob at path and none of its parents does."""
    if not classifier['hex_pin'](commit, 40) or commit in repo.boundaries: return False
    try: parents = classifier['git'](repo.root, 'rev-list', '--parents', '-n', '1', commit, '--').decode().split()
    except ValueError: return False
    if not parents or parents[0] != commit: return False
    requests = [commit + ':' + path] + [p + ':' + path for p in parents[1:]]
    raw = classifier['git'](repo.root, 'cat-file', '--batch-check', '-Z',
                            data=b''.join(r.encode('utf-8', 'surrogateescape') + b'\0' for r in requests))
    lines = raw.rstrip(b'\0').split(b'\0')
    if len(lines) != len(requests): raise ValueError('Python argument role provenance batch mismatch')
    held = [line.split()[0].decode() == blob and line.split()[1:2] == [b'blob'] if len(line.split()) == 3 else False for line in lines]
    return held[0] and not any(held[1:])


def _role_schema(classifier, catalog, entry, required, label):
    """Schema, revision and conflict checks of the reviewed source roles."""
    if (set(entry) != required or not isinstance(entry['path'], str) or not isinstance(entry['source_blob'], str)
            or not isinstance(entry['purpose'], str) or not entry['purpose'].strip() or not isinstance(entry['interface'], dict)
            or not isinstance(entry['provenance'], dict) or set(entry['provenance']) != {'commit', 'path', 'blob'}
            or not all(isinstance(v, str) for v in entry['provenance'].values())):
        raise ValueError('invalid ' + label + ' definition')
    p = entry['path']; revision = entry['input_revision']
    if not isinstance(revision, str) or not classifier['hex_pin'](revision, 40): raise ValueError(label + ' requires a full commit revision')
    if any(e.get('path') == p and e.get('input_revision') == revision and e is not entry for e in catalog['standalone']):
        raise ValueError('conflicting standalone definitions: ' + p)


def _role_current(classifier, repo, catalog, entry, pins):
    """False when a later revision supersedes or changed a pinned object."""
    p = entry['path']; revision = entry['input_revision']
    if revision != repo.ref:
        if any(e.get('path') == p and e.get('input_revision') == repo.ref for e in catalog['standalone']): return False
        if not all(_current(repo, q, b) for q, b in pins): return False
        if not _historical_objects(classifier, repo, revision, pins):
            raise ValueError('unverifiable historical runner demonstration: ' + revision + ':' + p)
    elif not all(_current(repo, q, b) for q, b in pins): raise ValueError('standalone definition source mismatch: ' + p)
    return True


def python_argument_root(classifier, graph, catalog, entry, reviewed=None):
    """H996: a reviewed argument-bearing Python program as a source-only role.

    The definition binds the bare entry prefix ['python3', '-B', P] (never a
    concrete argument), the source blob, its genuine top-level entry line, the
    interface python_argument_interface records for that blob, and provenance:
    the commit that introduced that blob at P, which must be in the reviewed
    set. The configured CLI, module CLI and unittest guards are unchanged: a
    program matching one is refused here. The root is never a validated or
    passing runner and anchors nothing: no execution, pass, read-anchor,
    fixture, helper, child, generated-output, proof or runtime credit. A later
    revision keeps it while the blob is unchanged and the recorded commit holds
    it; a current definition of the same path supersedes it.
    """
    repo = graph.repo
    reviewed = REVIEWED_PYTHON_ARGS if reviewed is None else reviewed
    required = {'path', 'input_revision', 'source_blob', 'command', 'kind', 'entry_line', 'interface', 'provenance', 'purpose'}
    _role_schema(classifier, catalog, entry, required, 'Python argument role')
    p = entry['path']; revision = entry['input_revision']; doc = entry['provenance']
    if entry['command'] != ['python3', '-B', p] or not p.endswith('.py'):
        raise ValueError('unsupported Python argument role invocation: ' + p)
    if doc['path'] != p or doc['blob'] != entry['source_blob'] or (p, entry['source_blob'], doc['commit']) not in reviewed:
        raise ValueError('unreviewed Python argument role: ' + p)
    if not _role_current(classifier, repo, catalog, entry, [(p, entry['source_blob'])]): return
    if repo.tree[p][0] not in ('100644', '100755') or p not in repo.texts:
        raise ValueError('unsupported Python argument role invocation: ' + p)
    if not _introduced(classifier, repo, doc['commit'], p, entry['source_blob']):
        raise ValueError('Python argument role lacks its introducing provenance: ' + p)
    try: lines = classifier['entrypoint_lines'](repo.bytes(p))
    except (SyntaxError, ValueError, RecursionError): lines = set()
    if type(entry['entry_line']) is not int or entry['entry_line'] not in lines:
        raise ValueError('Python argument role lacks its top-level entry: ' + p)
    if any(classifier[f](repo, p) is not None for f in ('declared_configured_cli', 'declared_module_cli', 'declared_unittest')):
        raise ValueError('Python argument role matches a configured CLI or unittest form: ' + p)
    interface = python_argument_interface(repo.texts[p])
    if interface is None: raise ValueError('Python argument role lacks an audited argument interface: ' + p)
    if canonical(interface) != canonical(entry['interface']): raise ValueError('Python argument role interface mismatch: ' + p)
    identity = PYTHON_ARGS_PREFIX + p
    graph.root(p, 'source-only Python argument entry', shlex.join(entry['command']), p, entry['entry_line'], root_id=identity)
    if identity not in graph.roots: return
    graph.roots[identity].update({'source_only': True, 'python_argument_role': True, 'source_blob': entry['source_blob'],
        'purpose': entry['purpose'], 'interface': interface, 'provenance': doc, 'source_declaration_revision': revision,
        'validation_at_measured_revision': {'status': 'unavailable', 'command': entry['command'],
            'reason': 'Reviewed argument-bearing Python entry; the bare prefix needs arguments and no argument is recorded. Source role only, never run or certified to pass. No read anchor, fixture, helper, child, generated-output, proof or runtime credit.'}})


NONPY_ENTRY_KIND = 'nonpython-entry-source-role'
NONPY_ENTRY_PREFIX = 'nonpy-entry:'
# H997 (gh coord#1331, X1E-NONPY-ROLE): the one shebang each interpreter is
# accepted with; the command names that interpreter explicitly.
NONPY_SHEBANGS = {'.sh': ('bash', '#!/usr/bin/env bash', True), '.mjs': ('node', '#!/usr/bin/env node', False),
                  '.cjs': ('node', '#!/usr/bin/env node', False)}
# Each reviewed live shell or Node program, bound to (path, source blob, one
# commit that introduced that blob at that path; where cherry-picks introduce
# the same blob twice, the earlier one, and the other is refused as unreviewed). Nothing else is
# promoted: another file, blob or provenance commit fails, and no argument,
# read, helper, child or output is ever recorded or credited.
REVIEWED_NONPY_ENTRIES = _review_table('''
@0834bc67b042a63a8c804162781802245ae59c98
D:shared-translator/address-fixture.mjs 7b43c79b13a92043dc9c6576fd1b45c6a574026d
D:shared-translator/address-validate.sh 6f9014aa569e25b415aba09f7ef1c37f4a4dd3ea
@0bdac88bfacec822c7157b7d5a3e713894571888
N:h81-memory-controls.mjs f923767bff5e51583c3a445950cc22e978bd6505
N:primitive-return/functional83.mjs 017a361b9d7ba28570a1ea323ff2da2f11e35530
@15302eb51e3df48b9d8d46eaf50348dd1deddfb2
D:shared-translator/read-bounds-validate.sh 05994407de7956849db17f9c7188b90376a3556d
N:h109/scripts/registration-parent-checks.sh 63e8cc7662f430c985a20d7147a4dd404b043a5c
@17f2902cdc6ab848317fc82e31a90ad2d7c4fba8
D:memory-references/fixtures.cjs 903cd31f868d6af169e7e743519131eb0e63131e
D:memory-references/prepare-admission.cjs 50a6ff09bbe39b55d8914427ea1f242db898c554
D:memory-references/source-transport.mjs 880d9e38ef8476e5543075ee1fc4c703b6917880
@18df52507a1cb6136e1340aee565964cdf6f012b
N:browser-baseline-checks.sh b12fe571b40579d911cbe4b4103446524e7597a9
N:browser-edit-controls.sh c941f40a9ea94ecef7b1855f33872426349baeec
N:browser-smoke-checks.sh 1e6b7d76f5cc553ab1aa64f0147408bad52057f5
N:browser-wire-audit.cjs 4c0ac946c684d5b825ab2c5d3b839b370522c832
N:build-browser-baseline.sh 6945c2448ded7e30723144a1e71607f21b68847c
N:link-symbol-diagnostic.sh 5e5c708c97d011052ae1e98cdddde9689a84e913
N:mcp-baseline-checks.sh 26574e91841f4e49d3125f56ca287688aaeb93b8
N:native-lsp-baseline.sh f3991cada4632b3bedc72fcd09b105b84a93386b
@2207c1bba286538fd63e4a0ff4960ed4a593a8ab
U:baseline-20261028/invocations/retries/harness.sh 67db42718e4d578b56d910e7e82fac1b732c23e0
@23a42307b1b336e5477c0bb5c8d8bfe6415b6ea6
N:published-f77-browser-build.sh b5361e73f7027cab3d7393477ab97f9239ac00cc
N:published-f77-browser-checks.sh a310340cbbd46a253914122b15fa58c10b505230
N:published-f77-browser-edit.sh 71f5edd301dd1fd34b38d4e837fc688c20a7e8a1
N:published-f77-browser-extras.sh 416c6c9d7a3719ed67920b64c8542162c7c1628d
N:published-f77-browser-smoke.sh cf153c3b1865aa6895202676bf29c0882980c959
N:published-f77-mcp.sh f3f3c9ece70022adeb854c9532df41f3b6337d93
N:published-f77-native-build.sh a0d99da1154b1e1bde0e38b63ffc7cd543c04bd0
N:published-f77-native-lsp.sh 08d725fe11cf9be46012e40d0f5f8c538adb680b
N:published-f77-validation.sh 515fd0bb1a379970d49bd411c7cfba586534758d
N:published-f77-wasm-build.sh 31c07b3799d6cd108bf29e5593bfdf2dad655386
@252be5a095f50a75c91e7b9ae55650eb4f6d7463
N:published-8495-controls.mjs c1e0b5e9be554992cdfa67ec097ceeb9b43ce322
N:request-identity/selector-negatives.mjs f79858cb61bf4a126b71dcd7cebeea2fa55dfc02
@354dadf752721c3caffeaf916c3ccf07a243c449
N:published-b86a-api.sh 807d5d2b9437c62910b0dfda56e95e241b3a5f97
N:published-b86a-mcp.sh d1b955a0bc0ebdcc8d5de0ad2f8071d164cb534e
@369739e39533161cdd077a06bf6842bf71d1baa3
N:h35-gates.sh bb70b12b4b5552bf525c128602c9ba61301aec46
@3ff9a2ea968af583d54f83defa62f537b28c235b
N:browser-control-completion.cjs 82ecd2d5a0e038c2cf8ef4949a72837a335ff9cf
N:hardening-browser-build.sh 6fd0f7517a5046993958792bd08f0df7a66a8315
N:hardening-browser-checks.sh a3fda3aa57ad433c25f74c987902dc428d99bf89
N:hardening-browser-controls.sh 53265ee586aa6620934ef84749c37aab62f9521c
N:hardening-browser-edit.sh ce5cd598f667ab741c3dfd68fbe3412fab7cdb0b
N:hardening-browser-smoke.sh 478ac8cd2e128af109dd094abf148a59498bf881
N:hardening-native-build.sh 5f516e8b52f5a3bdc1fd7b151c75ed48fec2b7bd
N:hardening-native-checks.mjs 2f13d3d616921e271ae7cb1f2dfe99ee0454c382
N:hardening-native-checks.sh ab70817d323bfa5c25dbba5b80aae363e1d1a699
N:hardening-validation.sh 169e84907b0e34ec25750b0a70d3ffe97509865f
N:sort-conformance.sh a66c463a355476c8c906e4ba46807881f96bbac1
N:startup-investigation.mjs a918cd39a422c15d82869a7f4b587dc2ab7d9d83
@40bcc364c4f0caf313ebe8c65e1da66d2ad75b1b
N:published-9584-api.sh 8d95e992c635c46c4971fa65dbcf5befe646e7c3
N:published-9584-mcp.sh 8b0f45ccbe12441d761f7b9bdd3bbfb5ce0d32c1
@44d89439afd8fe7aca251cd5693b5b7ea36cf603
D:shared-translator/environment-fixture.mjs 03b2c7c55004a710a0d7a053df0550e48eeeaf40
D:shared-translator/environment-validate.sh 9460e5febcad1c954204902e5b7a505c5a5f79da
@4a66db87c8ed848aef4c2ac1732b1df326c6fa97
D:shared-translator/fixed-byte-fixture.mjs 207f8ff6474cfed3a6443223eac989976bb3d9bb
D:shared-translator/fixed-byte-validate.sh b4d495f62a04cab7ec344489563d20f63f832f33
@4f5e84d8d3f90919c78e904697e5779fd3d0ce66
N:readbounds/scripts/additional-functional.sh 54fddfe266f4d61562dc867195421d1819ba6419
N:readbounds/scripts/axiom-gates-post-rebase.sh bdffe31da9f3c37864b74b8bf0f349654409db64
N:readbounds/scripts/capture-gate.sh da4a38d9db9a361b9f304a5f2adeafdde9b44d95
N:readbounds/scripts/dependency-gate.sh 1727e98a8e6d2b3bb0f4b79dc84cc5739746754f
N:readbounds/scripts/functional-checks-recovered.sh bbad552d675f721adb47df555ac86b85916b8606
N:readbounds/scripts/functional-checks.sh 46ac712e7df5083892b5634418b3aa9c2b874589
N:readbounds/scripts/native-build.sh dfa96b4d7f60f7dd4f78ed60a44114a93de21fdf
N:readbounds/scripts/proof-gates-post-rebase.sh 05160602dbedd46107efa412c8838bf14c0787d1
@5a21cb291a6d2f0bd2e1aa6574c14e895453c78b
N:environment/scripts/B-kernel-controls.sh 971e181a0d2b877229eeefb48306e9e6fa86f62d
N:environment/scripts/address-marker-gate.sh a3fd70679b39c94289498f6900b24ad6495dc517
N:environment/scripts/browser-build.sh 9a4017546027af0c77eef544ea3ba29f8198cde4
N:environment/scripts/compile-producer-args.mjs e60007cd18e4f58d829c5cd85da0f5766cf34c6d
N:environment/scripts/finite-gate.sh 78e4b5909d6dd81671cedb28178437804072e407
N:environment/scripts/fixed-byte-gate.sh d4197132f138040fc277bd006f6393e0455ec9b9
N:environment/scripts/lake-prefix.sh 2f2f8473b56c00259bcd400d6770c373bfea38cb
N:environment/scripts/marker-gate.sh 1f6e42cf641de1003b3d9dca483f4aa47af9ff7d
N:environment/scripts/mcp.sh 72cf3794cda2352c1fba6fc5bfbc02295b8a9b73
N:environment/scripts/state-refusal-controls.mjs d65587568f7e0fe0cb3b5b15b19b76d386eb2152
N:environment/scripts/wasm-build.sh 3450e74ddad66d1deaf08e1c93f82023ce75cd85
@6842e804ce6a3605e31274d1746483b65eddeb09
D:shared-translator/dynamic-bytes-fixture.mjs e823ea06bac4e522d24ff13eac1ffaff3342066f
@6fceb880a8696cedecd6f2a55801c853e193ce2d
U:repairs/group02-init-commands.sh fafe6ea30e62fdd93d33fefb3218567a66724617
@77913ac1cff1147d1129caea943c881b4aa61ec7
D:shared-translator/environment-decoder-validate.sh c9e849741ec9f96867766ecf7346f02c4d2389cf
@7ce3c2a5ba098b705fca1c39c01fef467477fe6c
U:repairs/group02-commands.sh af739fcdacb228adf9160e09b2b6c15918f77234
@85f39a01073565da7edef0a778abec2b7df9b1d7
N:hardening-wasm-build.sh 8c614bf7504ee59a1da79326f8408b4dec94e095
@9465af2e2b24c438d98bc46b1dfaf890fb9adcb3
N:h40-corpus-check.sh 2e9202333efe8ddc8d9ad0fc20f67af1c11ee11e
N:h40-full-gates.sh ee21b4e3f0534d4282108db2d6ef38148527b3a8
N:h40-mcp-checks.sh d2250ce009385237b7836fb88730724eeeffb295
N:h40-policy-checks.sh ee410e7d961e8e65077e722eaa676df651265329
N:h40-testsuite-check.sh 5e37e8524625eb35d21f977c842e4f5084799070
@957e5defaa3c2e32df1e692d8781e0d89fed5199
D:shared-translator/primitive-return-control-tuple-fixture.mjs a756a8e23bf3b19577268e44e960782928fe23b9
D:shared-translator/primitive-return-fixture.mjs 20f5d5f88b83ddfda3de8cc8168c69908a71d0dd
D:shared-translator/primitive-return-validate.sh 074e6d15f01d4bfd67c2bd0af103663f96231923
@a1729b9c6283b199d3249b11c6224165798a00bb
N:build-wasm-baseline.sh 579f45953b9ad98e4a5e8934aad0f54009d4dea5
@ae8062cfb0f028667485e6f1a621ff69e62724fd
N:bounded-keys.sh c530a67b2b5ef6283bbfe9113d88c39e655f21c6
N:build-native-baseline.sh a9b7a2401b3bafae04de86bcb707eecd60e44e26
N:fresh-spec-controls.mjs 667daf209b2060a60c0c3079502c320f138b05b0
N:native-baseline-checks.sh 63a3811ce26da1c4bcfd5435781e65f9ea9c6d07
N:prepare-baseline.mjs 086f041b6ffd9ecb7451479bf7d0c20e8799d33e
@b44f0de87c2ab845b79c9d84004dcb7c91babded
D:shared-translator/bounded.sh a6686039c6dec3b35d2f06a2b8403be31ff9dd42
D:shared-translator/h90-base-census.sh 299ca2604fb7206c03d98bd084ca2b714158e078
D:shared-translator/h90-census-command.sh 1004774e354dd25b941d6331ec0c52d92a2c86f6
D:shared-translator/h90-validate.sh a67ec66c28490d60be84f27466897389d27dc82c
D:shared-translator/narrow-local-fixture.mjs 8fb3e82889a9bef284ecd92f2c9cf71be89b2a25
@bc4cb33ff40e97e88c04787419aaa0a16b618026
D:shared-translator/fresh-construct-fixtures.mjs f6731c57f457a2b2b0fbbe57d6e67dbbafde9f40
@c21364ef94c9f9102065b51edd00dd1cb904661d
N:address/state-refusal-controls.mjs d65587568f7e0fe0cb3b5b15b19b76d386eb2152
@c9230cc9692a5974728959907afa1f60733409ad
D:memory-references/native-source-controls.mjs 3e46b94bea4cff0efe8f108ffd61d99838d79c63
@d74b24de8dd2560366ed47ec8a5d96e3351e9378
D:shared-translator/environment-proof-validate.sh db00b98f108dd43cbe5e9d46c01f405ae22f4a18
@dc3f0ffc0431f87441e7bc3b8f263b38d02d229b
N:published-8495-api.sh 9022e73f1b542446eae3c5e61ebd6197d0a2262a
N:published-8495-controls.sh 74b1ebf5ffd8efc6b6ee01c8c24d398071eb42d0
@e01ff4a52ffa532e47d3cb163bb97245f436e3b2
N:compact-runtime-cache.sh 05e0333828e32952e0ff2af01265d7dd7b4ef324
N:gmp-serial.sh c6defb5a7ac2f5e6cf98a114d8d6bfe69884280c
N:wasm-inside.sh c7400f29384cfd151e157ff709a4707545d731a2
@e49c71436470851e0a3b295fa56b3b6c749e09b1
N:environment/scripts/checks.sh 63f4e50b51509f7a6273aa53fec3c9357c880ecc
N:environment/scripts/historical/checks.sh 0887f3a28631e1853e860a9355d69580fcb5f615
N:environment/scripts/historical/remaining-checks.sh c37ac7de446ea7c9f83c6fde04013ce82801695b
N:environment/scripts/remaining-checks.sh 83e197d395972de024ac087aad4ebb3203a14732
@e6865a2c7347df62db74bfc8b30aa00dce409c74
N:h109/scripts/registration-lake.sh 9ac8f8bece17c2d01dd2653578f24f97de1dd24e
@e778f14e03877c102aaaf739c60ecaccc9a989e5
D:shared-translator/compatibility-fixtures.mjs 7eb7688e61d8f342b8549078635414d79f577e82
D:shared-translator/compiler-coverage-fixtures.mjs dda8193f85512314ae76a2b7740d8591990f26dd
D:shared-translator/composed-fixture.mjs b0af1badf585f4023819027bb1d8c6b3f85ba1cd
D:shared-translator/modality-fixture.mjs 1e2484febd93269030f7d7956e7f9958dd448b21
@eef016814a3deddf5e9ea85a97fadfc0ec73a114
N:readbounds/axiom-gates.sh 6d77f69e2a86fa3d1ab1121b4cc9408aeb19fabd
N:readbounds/module-gates.sh bd84543e2eab25c0fc8db0de1d7cff7cf27718f8
N:readbounds/proof-gates.sh d1c49af7756b40057993698f72fb3394367d0b37
''')


def nonpython_entry_interface(path, text):
    """The audited entry interface of a shell or Node program, or None.

    Recorded: the interpreter, the shebang line (required for bash, optional
    for Node) and the first top-level statement line (column 0; for Node the
    first one that is not an import declaration). Not audited, giving None:
    another suffix (`.js` depends on a package type), a `.test.` name (the
    node-test kind keeps that naming), any other shebang, ambiguous line
    breaks, a NUL byte, a column-0 shell line with a `return` command (a
    sourced library), a shell file whose column-0 lines are all function
    definitions, assignments or set/shopt, any Node `export` declaration,
    in a `.cjs` file any bare `exports` reference, `module.exports` or
    `module[...]` access or Object.assign/defineProperty on module (a CommonJS
    library), or no top-level statement. The shell check is lexical: an
    indented `return` is not distinguished from one in a function body, so
    the review set, not this parser, is the gate.
    """
    suffix = posixpath.splitext(path)[1]
    if suffix not in NONPY_SHEBANGS or '.test.' in posixpath.basename(path): return None
    if not isinstance(text, str) or not _plain_lines(text) or '\0' in text: return None
    interpreter, shebang, required = NONPY_SHEBANGS[suffix]
    lines = text.split('\n'); first = lines[0]
    if first.startswith('#!'):
        if first != shebang: return None
    elif required: return None
    else: shebang = None
    if interpreter == 'bash':
        top, until = [], None  # column-0 lines outside here-document bodies
        for n, line in enumerate(lines[1:], 2):
            if until is not None:
                if line.lstrip('\t') == until: until = None
                continue
            if line[:1] not in ('', '#', ' ', '\t'): top.append((n, line))
            heredoc = re.search(r'<<-?\s*(["\']?)(\w+)\1', line)
            if heredoc and '<<<' not in line: until = heredoc[2]
        if until is not None: return None
        if any(re.search(r'(?<![\w$-])return\b', line) for _, line in top): return None
        definition = r'(?:function\s+[\w-]+|[\w-]+\s*\(\s*\))\s*\{?\s*$|\}\s*$|(?:export\s+|readonly\s+|declare\s+(?:-\w+\s+)*)?\w+=|(?:set|shopt)\s'
        entry = top[0][0] if any(not re.match(definition, line) for _, line in top) else None
    else:
        masked = (' ' * len(first) + text[len(first):]) if shebang else text
        code = _js_mask(masked, True)[0]
        if re.search(r'(?<![\w$.])export\b', code): return None
        if suffix == '.cjs' and re.search(r'(?<![\w$.])exports\b(?!\s*:)|(?<![\w$.])module\s*(?:\.\s*exports\b|\[)'
                                         r'|\bObject\s*\.\s*(?:assign|defineProperty|defineProperties)\s*\(\s*module\b', code): return None
        imports = {code.count('\n', 0, m.start()) + 1 + k for m in re.finditer(r'(?m)^import\b(?!\s*[(.])(?:[^{};\n]*\{[^}]*\}[^;\n]*|[^{};\n]*)', code)
                   for k in range(m.group(0).count('\n') + 1)}
        entry = next((n for n, line in enumerate(code.split('\n'), 1) if line[:1] not in ('', ' ', '\t') and n not in imports), None)
    if entry is None: return None
    return {'interpreter': interpreter, 'shebang': shebang, 'entry_line': entry}


def nonpython_entry_root(classifier, graph, catalog, entry, reviewed=None):
    """H997: a reviewed live shell or Node program as a source-only role.

    The definition binds the exact command [interpreter, P] (never an
    argument), the source blob, the interface nonpython_entry_interface
    records for that blob (interpreter, shebang, top-level entry line) and
    provenance: the commit that introduced that blob at P, which must be in
    the reviewed set. Python programs keep source-only-program and the H996
    role, `.test.` Node files keep node-test, manual reproducers are
    unchanged. The root is never a validated or passing runner and anchors
    nothing: no execution, pass, read-anchor, fixture, helper, child,
    generated-output, proof or runtime credit. A later revision keeps it while
    the blob is unchanged and the recorded commit holds it; a current
    definition of the same path supersedes it.
    """
    repo = graph.repo
    reviewed = REVIEWED_NONPY_ENTRIES if reviewed is None else reviewed
    required = {'path', 'input_revision', 'source_blob', 'command', 'kind', 'interface', 'provenance', 'purpose'}
    _role_schema(classifier, catalog, entry, required, 'non-Python entry role')
    p = entry['path']; revision = entry['input_revision']; doc = entry['provenance']
    shape = NONPY_SHEBANGS.get(posixpath.splitext(p)[1])
    if shape is None or entry['command'] != [shape[0], p] or '.test.' in posixpath.basename(p):
        raise ValueError('unsupported non-Python entry role invocation: ' + p)
    if doc['path'] != p or doc['blob'] != entry['source_blob'] or (p, entry['source_blob'], doc['commit']) not in reviewed:
        raise ValueError('unreviewed non-Python entry role: ' + p)
    if not _role_current(classifier, repo, catalog, entry, [(p, entry['source_blob'])]): return
    if repo.tree[p][0] not in ('100644', '100755') or p not in repo.texts:
        raise ValueError('unsupported non-Python entry role invocation: ' + p)
    if not _introduced(classifier, repo, doc['commit'], p, entry['source_blob']):
        raise ValueError('non-Python entry role lacks its introducing provenance: ' + p)
    interface = nonpython_entry_interface(p, repo.texts[p])
    if interface is None: raise ValueError('non-Python entry role lacks an audited entry interface: ' + p)
    if canonical(interface) != canonical(entry['interface']): raise ValueError('non-Python entry role interface mismatch: ' + p)
    identity = NONPY_ENTRY_PREFIX + p
    graph.root(p, 'source-only non-Python entry', shlex.join(entry['command']), p, interface['entry_line'], root_id=identity)
    if identity not in graph.roots: return
    graph.roots[identity].update({'source_only': True, 'nonpython_entry_role': True, 'source_blob': entry['source_blob'],
        'purpose': entry['purpose'], 'interface': interface, 'provenance': doc, 'source_declaration_revision': revision,
        'validation_at_measured_revision': {'status': 'unavailable', 'command': entry['command'],
            'reason': 'Reviewed live shell or Node program; the command is the bare interpreter prefix, which may need arguments, and no argument is recorded. Source role only, never run or certified to pass. No read anchor, fixture, helper, child, generated-output, proof or runtime credit.'}})


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


def lean_check_root(classifier, graph, catalog, entry, reviewed=None, invocations=None):
    """H999: a reviewed live non-root Lean check source as a source-only role.

    Binds lean_check_command(P), the blob, its interface, the reviewed
    introducing commit and each invocation: a reviewed H997 driver (blob,
    commit) whose gate line runs P. P is under tests/; a Lake package, root
    library, importer or changed gate.sh per-file line makes it stale. Never a
    validated runner; anchors nothing. Kept later while source and drivers are
    unchanged; a current definition of the path supersedes it."""
    repo = graph.repo
    reviewed = REVIEWED_LEAN_CHECKS if reviewed is None else reviewed
    invocations = REVIEWED_LEAN_CHECK_INVOCATIONS if invocations is None else invocations
    required = {'path', 'input_revision', 'source_blob', 'command', 'kind', 'interface', 'provenance', 'invocations', 'purpose'}
    _role_schema(classifier, catalog, entry, required, 'Lean check role'); calls = entry['invocations']
    if (not isinstance(calls, list) or not calls or any(not isinstance(c, dict) or set(c) != {'driver', 'driver_blob', 'driver_commit', 'line'} or type(c['line']) is not int
                   or not all(isinstance(c[k], str) for k in ('driver', 'driver_blob', 'driver_commit')) for c in calls)
            or len({canonical(c) for c in calls}) != len(calls)):
        raise ValueError('invalid Lean check role definition')
    p = entry['path']; revision = entry['input_revision']; doc = entry['provenance']; blob = entry['source_blob']
    if entry['command'] != lean_check_command(p) or not p.endswith('.lean') or not p.startswith('tests/') or _clean(p) != p:
        raise ValueError('unsupported Lean check role invocation: ' + p)
    if doc['path'] != p or doc['blob'] != blob or (p, blob, doc['commit']) not in reviewed: raise ValueError('unreviewed Lean check role: ' + p)
    if any((p, blob, c['driver'], c['driver_blob'], c['line']) not in invocations or not c['driver'].endswith('.sh')
           or (c['driver'], c['driver_blob'], c['driver_commit']) not in REVIEWED_NONPY_ENTRIES for c in calls):
        raise ValueError('unreviewed Lean check role invocation: ' + p)
    pins = [(p, blob)] + [(c['driver'], c['driver_blob']) for c in calls]
    if not _role_current(classifier, repo, catalog, entry, pins): return
    if repo.tree[p][0] != '100644' or p not in repo.texts or any(repo.tree[c['driver']][0] not in ('100644', '100755') for c in calls):
        raise ValueError('unsupported Lean check role invocation: ' + p)
    if not _introduced(classifier, repo, doc['commit'], p, blob): raise ValueError('Lean check role lacks its introducing provenance: ' + p)
    if not all(_introduced(classifier, repo, c['driver_commit'], c['driver'], c['driver_blob']) for c in calls):
        raise ValueError('Lean check role driver lacks its introducing provenance: ' + p)
    # Lake packages, root libraries and importers are not pinned: they make the role stale.
    parts = p.split('/')
    if (any('/'.join(parts[:k]) + '/' + name in repo.tree for k in range(1, len(parts)) for name in ('lakefile.toml', 'lakefile.lean'))
            or 'lakefile.lean' in repo.tree or not _outside_root_libraries(repo, p)
            or any(e['target'] == p and e['operation'] == 'Lean import' for edges in graph.edges.values() for e in edges)): return
    interface = lean_check_interface(classifier['lean_code'], p, repo.texts[p])
    if interface is None: raise ValueError('Lean check role lacks an audited check-only interface: ' + p)
    if canonical(interface) != canonical(entry['interface']): raise ValueError('Lean check role interface mismatch: ' + p)
    for c in calls:
        if c['driver'] not in repo.texts or nonpython_entry_interface(c['driver'], repo.texts[c['driver']]) is None:
            raise ValueError('Lean check role driver lacks an audited entry interface: ' + c['driver'])
        if not lean_check_invocation(repo.texts[c['driver']], p, c['line']): raise ValueError('Lean check role driver does not run the source: ' + c['driver'])
    if '\n' + LEAN_CHECK_GATE_BRANCH + '\n' + LEAN_CHECK_GATE_LINE + '\n' not in repo.texts.get(LEAN_CHECK_GATE, ''): return
    identity = LEAN_CHECK_PREFIX + p
    graph.root(p, 'source-only Lean check source', shlex.join(entry['command']), calls[0]['driver'], calls[0]['line'], root_id=identity)
    if identity not in graph.roots: return
    graph.roots[identity].update({'source_only': True, 'lean_check_role': True, 'source_blob': blob, 'purpose': entry['purpose'],
        'interface': interface, 'provenance': doc, 'invocations': calls, 'source_declaration_revision': revision,
        'validation_at_measured_revision': {'status': 'unavailable', 'command': entry['command'],
            'reason': 'Reviewed Lean check source run by reviewed drivers via gate.sh per-file; never run or certified to elaborate or pass. No execution, read, fixture, helper, import-dependency, output, proof or runtime credit.'}})


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


SOURCE_ROLE_KINDS = {SOURCE_ONLY_KIND: source_only_program, NODE_MODE_KIND: node_mode_root, PYTHON_ARGS_KIND: python_argument_root,
                     NONPY_ENTRY_KIND: nonpython_entry_root, LEAN_CHECK_KIND: lean_check_root}
