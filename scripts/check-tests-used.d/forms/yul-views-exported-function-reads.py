# H1234 (gh#1544, Q-X1ERR-7, Option C), form (4): a literal Node readFileSync
# that is the first statement of an exported function which a reviewed,
# demonstrated source-only Node producer (an H997 nonpython-entry role, P)
# calls at its top level. consumer_routes section exported_function_reads:
#   {runner: 'nonpy-entry:P', frames: [{path: P, blob, line: CALL}, {path: M,
#    blob, line: READ}], form: 'node-exported-function-read', target,
#    target_blob, purpose}
# Re-derived from the measured bytes:
# - CALL is a top-level statement of P `[const|let|var NAME =] [await] FN(ARG);`
#   (column 0, bracket depth 0, after a line ending ';' or '}'), FN is named
#   exactly once in a column-0 static `import {..., FN, ...} from './M';` of P
#   (the H951 reader resolves it to M; no alias) and never rebound in P;
# - M has exactly one column-0 `export [async] function FN(IDENTIFIERS) {`
#   (plain parameters, no defaults that run code first), FN is never rebound in
#   M, and READ is the very next line: `[const|let|var NAME =] readFileSync(new
#   URL('REL', import.meta.url)[, ...])...;`, the only read on the line, naming
#   the target (H951 literal reader). A function body runs its first statement
#   on every call (an async one synchronously, before its first await);
# - P and M show no way to end the run early (the form (a) lexical audit
#   node_producer_quiet: no exit/abort/kill/reallyExit name, `process` only as
#   process.argv/env/exitCode, no process module, also in template
#   substitutions), and both are .mjs ES modules.
# So a run of P that completed made the call and the read. Modules off the
# frame path are not audited lexically, so P's whole local static import
# closure (node_local_import_closure, every module that can run before the
# read) must be the same objects now and at the demonstration revision, and a
# closure module with a dynamic import( is never credited (stale otherwise);
# off-Git packages are covered only by the recorded demonstration. Opt-in twice by exact tuple: the
# producer (P, blob, demonstration revision, argv) in
# REVIEWED_EXPORTED_FUNCTION_PRODUCERS and the route (P, frames, target, target
# blob) in REVIEWED_EXPORTED_FUNCTION_READS; anything else is rejected. At a
# measured --ref a row credits its target while P's H997 root is current with
# that blob and every frame and the target are the same blobs now and at the
# demonstration revision (stale otherwise: no credit, no error). Consumption
# credit only, for the target alone (the call edge is provenance, H1108; the
# module frame gets no credit): the H997 root stays source-only, with no pass,
# read anchor for other forms, helper, child, output, proof or runtime credit; form (a) and
# static_routes are unchanged, and each section refuses the other's table.
# Reviewed on master abec4d99 from x1e-classify-rest-rest's B1 list (02e437a0):
# the producer is tests/yul-views/physical-reference.mjs (H1025 entry, blob
# 37d22700), the same run form (a) records: demonstrated at 181972c6 by that
# lane (`node tests/yul-views/physical-reference.mjs PINNED_COMPILER REPORT`,
# pinned solc 0.8.38), and its report holds every replay result below. The
# producer calls replayX(compile) at top level for each of the 18 remaining B1
# sources, and each replayX reads its source as its first statement. Admitted
# (18): AggregateWriteback, DynamicUint, Finite, HeapBytes, HeapResize,
# JointMemory, MemberArrays, MemoryScalarWords, MixedHeap, OwnedInventory,
# PackedResidual, Residual, RetainedHeap, RetainedMemberArrays,
# ScalarMemoryAlias, ScalarMemoryOps, WordWriteback and Writeback (.sol).
# Physical.sol stays with form (a). Nothing else is admitted; second reads in a
# function (e.g. the parent source of heap-resize) are not credited by this form.
import hashlib
(FORM_CONTROLS, NONPY_ENTRY_PREFIX, _check_lines, _frames_current, _historical_objects, _js_destructured, _js_mask,
 _node_import, _node_read, _plain_lines, canonical, register_consumer_section) = (globals()[name] for name in (
    'FORM_CONTROLS', 'NONPY_ENTRY_PREFIX', '_check_lines', '_frames_current', '_historical_objects', '_js_destructured',
    '_js_mask', '_node_import', '_node_read', '_plain_lines', 'canonical', 'register_consumer_section'))
EFR_SECTION = 'exported_function_reads'
EFR_FORM = 'node-exported-function-read'
EFR_OPERATION = 'Node readFileSync of a literal module-relative path as the first statement of an exported function a demonstrated producer calls at top level'
EFR_HOP = 'Node top-level call of an imported exported function by the reviewed producer'
_EFR_P = 'tests/yul-views/physical-reference.mjs'
_EFR_P_BLOB = '37d2270025ea6fd3c5819cc708b6a0608d5ffeb7'
# (producer, blob, demonstration revision, argv with placeholders for off-Git arguments)
REVIEWED_EXPORTED_FUNCTION_PRODUCERS = frozenset({
    (_EFR_P, _EFR_P_BLOB, '181972c695c3ad4008e1e119ee80af54c750123b', ('node', _EFR_P, 'PINNED_COMPILER', 'REPORT'))})
# producer call line, module, module blob, read line, target, target blob
_EFR_ROWS = '''
69 aggregate-writeback-reference.mjs 1d0267fa5dbebaef85025ce3da28de51f2275b5e 44 AggregateWriteback.sol 1ec7e87368174d74b6516f8facd9dd2b9ff0e11d
68 dynamic-uint-reference.mjs 578a36101df231ff7eb86cb249d79d28a584bcae 41 DynamicUint.sol 530885e000d35a7db40c9f5c42623fcae3a21d8f
62 finite-reference.mjs 910f11690fb6b9577dbf1c5220aa207f65e8c812 49 Finite.sol dd72c652eda328788a4d5adccd5028e06b8f22b3
63 heap-bytes-reference.mjs 8e19029b565358985e03fb24e450866e5164d720 48 HeapBytes.sol 9c92a3179b6b1f10b3da7926c6227d93d7a26360
64 heap-resize-reference.mjs ad06d33ac4f97a25e77730c894e7114570ca9afa 49 HeapResize.sol 7ecffcd1414d17e134d02d94ab0d28d655bf34c0
75 joint-memory-reference.mjs 3caa1e56fc8f1ced78539f32c9a5b6da6e084c91 43 JointMemory.sol a4cf57ed68db66388deed857c7614c98deef9707
70 member-arrays-reference.mjs 5c3464bd079252b9945bf2aefb5c7c5f6cf8a7a9 44 MemberArrays.sol 7b0f3889a8f235a52c66fac651bf5e051f1f2d2d
72 memory-scalar-words-reference.mjs 6fc93fbe64e09bbc443de1c297fc32bc9730a685 39 MemoryScalarWords.sol 1f63327a7c9f8d09db802c0212c3b53f0327b84e
66 mixed-heap-reference.mjs 3cf1ba746eb5023d253d3dc82fc052d686e8f06a 46 MixedHeap.sol 7850d631b5d450d70c5346997684676ba46e0a80
74 owned-inventory-reference.mjs c18eaa1e1674b7ecb3d1cff6e8c1629cf2dfd7d6 43 OwnedInventory.sol dbdd9f57b6336b977fe1c58b0e86c27bc7f08d71
77 packed-residual-reference.mjs 7889dd7e650a583d92eb0728a7e3447280d236d2 72 PackedResidual.sol cc32e4713e8126de32b5f4c5b122777fe200face
61 residual-reference.mjs 532a94dc55c226de7db789d2dd21abceacf79550 32 Residual.sol 4cc366ea5073194abf5ad92cbb5472baa407efbd
65 retained-heap-reference.mjs 255fc97c021c5d7917d0691fc5df63f16cc1ce9b 46 RetainedHeap.sol 4f05e4a2634d2d7bbe6face4350e5732d22c7655
71 retained-member-arrays-reference.mjs 749febbe92107157b27595a55e7355588b0cad78 41 RetainedMemberArrays.sol c50ce81927a1921b0184aa2bdac5fd0ff2e49d3d
76 scalar-memory-alias-reference.mjs 090279e74d4091f87942c8d30b8ed4af8744a529 39 ScalarMemoryAlias.sol 6964c4d98a3bd1408eacb754bfcb9168cea908b0
73 scalar-memory-ops-reference.mjs bbf43a5a2f4f94d3e4bdf0340ed0508fbc1665a1 39 ScalarMemoryOps.sol 5a1b1454cb10663ae04bf4eb4dede7866e2bfc3b
67 word-writeback-reference.mjs f99356702a358ed7764f708eb554140c6cd8109f 44 WordWriteback.sol 7aa8f1bbeb31477cfdfae735541dc8898af2cecf
60 writeback-reference.mjs 3a56702c53698b2aee2c6073cc0a473a2306b6da 17 Writeback.sol 7e5a0f39644fd4eaf379324745cb3aa4d34b4056
'''
REVIEWED_EXPORTED_FUNCTION_READS = frozenset(
    (_EFR_P, ((_EFR_P, _EFR_P_BLOB, int(call)), ('tests/yul-views/' + m, mb, int(read))), 'tests/yul-views/' + t, tb)
    for call, m, mb, read, t, tb in (line.split() for line in _EFR_ROWS.split('\n') if line))
_EFR_CALL = r'(?:(?:const|let|var)[ \t]+[\w$]+[ \t]*=[ \t]*)?(?:await[ \t]+)?([\w$]+)\([ \t]*[\w$]*[ \t]*\)[ \t]*;[ \t]*'
_EFR_READ = (r'[ \t]*(?:(?:const|let|var)[ \t]+[\w$]+[ \t]*=[ \t]*)?readFileSync\([ \t]*new URL\([^;]*;[ \t]*')


def efr_top_level_call(text, number):
    """The function name a top-level statement `[const X =] [await] FN(ARG);` of text calls at that line, else None."""
    if not isinstance(text, str) or not _plain_lines(text) or '\0' in text: return None
    lines = text.split('\n')
    if type(number) is not int or not 1 <= number <= len(lines): return None
    code, _ = _js_mask(text, True); masked = code.split('\n')
    if len(masked) != len(lines): return None
    match = re.fullmatch(_EFR_CALL, masked[number - 1])
    if match is None or masked[number - 1] != lines[number - 1]: return None
    before = '\n'.join(masked[:number - 1])
    if sum(before.count(c) for c in '([{') != sum(before.count(c) for c in ')]}'): return None
    previous = [m.rstrip() for m in masked[:number - 1] if m.strip()]
    if previous and not previous[-1].endswith((';', '}')): return None
    return match[1]


def _efr_bound_once(code, name, definition):
    """name is defined only by definition (one match) and never assigned or destructured."""
    n = re.escape(name)
    return (len(re.findall(definition, code)) == 1 and not re.search(r'(?<![\w$.])' + n + r'\s*=(?![=>])', code)
            and not _js_destructured(code, name) and len(re.findall(r'\b(?:function|let|var|const|class)\s+' + n + r'(?![\w$])', code)) <= 1)


def efr_import(source, text, name):
    """The module path of the one column-0 static import binding name in source, unaliased, else None."""
    code, _ = _js_mask(text, True); lines = text.split('\n'); masked = code.split('\n')
    hits = [n for n, line in enumerate(masked, 1) if re.match(r'import\s*\{[^{}]*\}\s*from\s', line)
            and re.search(r'[{,]\s*' + re.escape(name) + r'\s*[,}]', lines[n - 1])]
    others = [n for n, line in enumerate(lines, 1) if re.search(r'(?<![\w$.])' + re.escape(name) + r'\s+as\b|\bas\s+' + re.escape(name) + r'(?![\w$])', masked[n - 1])]
    if len(hits) != 1 or others or not _efr_bound_once(code, name, r'(?m)^import\s*\{[^{}]*(?<![\w$])' + re.escape(name) + r'(?![\w$])[^{}]*\}'):
        return None
    return _node_import(source, text, hits[0])


def efr_first_read(text, name, number):
    """Line number is the first statement of the one column-0 `export [async] function name(IDS) {` of text."""
    if not isinstance(text, str) or not _plain_lines(text) or '\0' in text: return False
    lines = text.split('\n')
    if type(number) is not int or not 2 <= number <= len(lines): return False
    code, _ = _js_mask(text, True); masked = code.split('\n')
    header = r'export[ \t]+(?:async[ \t]+)?function[ \t]+' + re.escape(name) + r'[ \t]*\([ \t]*(?:[\w$]+[ \t]*(?:,[ \t]*[\w$]+[ \t]*)*)?\)[ \t]*\{[ \t]*'
    heads = [n for n, line in enumerate(masked, 1) if re.fullmatch(header, line) and line == lines[n - 1]]
    if heads != [number - 1] or not _efr_bound_once(code, name, r'(?m)^export[ \t]+(?:async[ \t]+)?function[ \t]+' + re.escape(name) + r'(?![\w$])'):
        return False
    before = '\n'.join(masked[:number - 2])
    if sum(before.count(c) for c in '([{') != sum(before.count(c) for c in ')]}'): return False
    return re.fullmatch(_EFR_READ, masked[number - 1]) is not None


def exported_function_reads(classifier, graph, rows, producers=None, reads=None):
    """H1234 (4): exact first-statement reads of exported functions a demonstrated producer calls."""
    repo = graph.repo
    producers = REVIEWED_EXPORTED_FUNCTION_PRODUCERS if producers is None else producers
    reads = REVIEWED_EXPORTED_FUNCTION_READS if reads is None else reads
    for row in rows:
        if (not isinstance(row, dict) or set(row) != {'runner', 'frames', 'form', 'target', 'target_blob', 'purpose'}
                or row['form'] != EFR_FORM or not isinstance(row['runner'], str) or not row['runner'].startswith(NONPY_ENTRY_PREFIX)
                or not isinstance(row['target'], str) or not isinstance(row['target_blob'], str)
                or not isinstance(row['purpose'], str) or not row['purpose'].strip()):
            raise ValueError('invalid exported function read route')
        frames = row['frames']; target = row['target']; p = row['runner'][len(NONPY_ENTRY_PREFIX):]
        if not _frames_current(repo, frames, [(target, row['target_blob'])]): continue
        if len(frames) != 2 or frames[0]['path'] != p: raise ValueError('exported function read is not a producer call and a module read')
        if (p, tuple((f['path'], f['blob'], f['line']) for f in frames), target, row['target_blob']) not in reads:
            raise ValueError('unreviewed exported function read: ' + p)
        demonstrated = [d for d in producers if d[:2] == (p, frames[0]['blob'])]
        if len(demonstrated) != 1: raise ValueError('exported function read lacks a demonstrated producer: ' + p)
        root = graph.roots.get(row['runner'])
        if (root is None or 'derived_from' in root or not root.get('nonpython_entry_role') or not root.get('source_only')
                or root.get('source_blob') != frames[0]['blob'] or root.get('path') != p): continue
        _check_lines(repo, frames)
        caller, module = frames
        if any(not f['path'].endswith('.mjs') or not node_producer_quiet(repo.texts[f['path']]) for f in frames):
            raise ValueError('exported function read frames must be quiet ES modules')
        name = efr_top_level_call(repo.texts[p], caller['line'])
        if name is None or efr_import(p, repo.texts[p], name) != module['path']:
            raise ValueError('exported function read call is not a top-level call of an imported function')
        text = repo.texts[module['path']]
        if not efr_first_read(text, name, module['line']) or _node_read(module['path'], text, module['line'], '/') != target:
            raise ValueError('exported function read is not the first-statement literal readFileSync of its target')
        if classifier['excluded'](target) or any(classifier['excluded'](f['path']) for f in frames): continue
        revision, argv = demonstrated[0][2:]
        closure = node_local_import_closure(repo, p)  # mjs-checker-demonstrated-run.py
        if closure is None or not _historical_objects(classifier, repo, revision, sorted(set(closure) | {(f['path'], f['blob']) for f in frames} | {(target, row['target_blob'])})):
            continue
        _efr_observe(graph, row['runner'], row, frames, target,
                     {'kind': 'exported-function-read', 'purpose': row['purpose'], 'demonstration_revision': revision, 'demonstrated_command': list(argv)})


def _efr_observe(graph, original, row, frames, target, details):
    """Like _observe, but the call edge is provenance only: the target alone is credited (H1108), never the module."""
    identity = original + ':' + details['kind'] + ':' + hashlib.sha256(canonical(row)).hexdigest()
    graph.roots[identity] = {**graph.roots[original], 'derived_from': original, 'observed_target': target, 'consumer_route': details}
    caller, reader = frames
    edges = [{'source': caller['path'], 'target': reader['path'], 'line': caller['line'], 'operation': EFR_HOP, 'kind': 'executes', 'validated_for': identity},
             {'source': reader['path'], 'target': target, 'line': reader['line'], 'operation': EFR_OPERATION, 'kind': 'consumes', 'validated_for': identity}]
    graph.observed.append((target, {'root': identity, 'entry': graph.roots[identity], 'edges': edges}))


register_consumer_section(EFR_SECTION, ('runner', 'form', 'target', 'frames'), True,
                          lambda c, g, _, rows: exported_function_reads(c, g, rows))


def exported_function_controls(env):
    """H1234 (4) controls: the reviewed rows, a synthetic producer whose call of
    an imported function's first-statement read is credited only with both
    reviews, and the refused shapes."""
    global REVIEWED_EXPORTED_FUNCTION_PRODUCERS, REVIEWED_EXPORTED_FUNCTION_READS, REVIEWED_NONPY_ENTRIES
    commit, run, rejected, blob, frame, reviewed_nonpy = (env[k] for k in ('commit', 'run', 'rejected', 'blob', 'frame', 'reviewed_nonpy'))
    assert len(REVIEWED_EXPORTED_FUNCTION_PRODUCERS) == 1 and len(REVIEWED_EXPORTED_FUNCTION_READS) == 18
    assert REVIEWED_EXPORTED_FUNCTION_PRODUCERS <= REVIEWED_NODE_PRODUCERS  # the same demonstrated run as form (a)
    assert all((p, b) in {(q, c) for q, c, _ in reviewed_nonpy} for p, b, *_ in REVIEWED_EXPORTED_FUNCTION_PRODUCERS)
    assert all(r[1][0][:2] == (_EFR_P, _EFR_P_BLOB) and r[2].endswith('.sol') for r in REVIEWED_EXPORTED_FUNCTION_READS)
    assert not {r[2] for r in REVIEWED_EXPORTED_FUNCTION_READS} & {r[2] for r in REVIEWED_NODE_PRODUCER_READS}
    P = 'tests/efr/prod.mjs'; module = lambda name, first='', header=None: (
        "import {readFileSync} from 'node:fs';\nexport const unused=1;\n"
        + (header or 'export async function replay' + name + '(compile){') + '\n' + first
        + " const source=readFileSync(new URL('./" + name + ".sol',import.meta.url),'utf8'),variants=[];\n return compile(source);\n}\n")
    prod = ("import {replayA} from './a-reference.mjs';\nimport {replayB as replayAlias} from './b-reference.mjs';\n"
            "import {replayD} from './d-reference.mjs';\nimport {replayE} from './e-reference.mjs';\nimport {replayF} from './f-reference.mjs';\n"
            "const [x,y]=process.argv.slice(2);\nif(!x||!y)throw Error('usage');\n"
            "const a=await replayA(x);\n"            # 8 POSITIVE
            "if(x) await replayA(x);\n"              # 9 conditional
            "const c=x?\nawait replayA(x):0;\n"      # 11 conditional operand
            "const b=await replayAlias(x);\n"        # 12 aliased import
            "const d=await replayD(x);\n"            # 13 read is the second statement
            "const e=await replayE(x);\n"            # 14 defaults run first
            "const f=await replayF(x);\n"            # 15 module can exit
            "function g(){ return replayA(x); }\n"
            "process.exitCode=0;\n")
    files = {P: prod, 'tests/efr/a-reference.mjs': module('A'), 'tests/efr/b-reference.mjs': module('B'),
             'tests/efr/d-reference.mjs': module('D', ' const v=1;\n'), 'tests/efr/e-reference.mjs': module('E', '', 'export async function replayE(compile,on=()=>{}){'),
             'tests/efr/f-reference.mjs': module('F') + 'export function stop(){ process.exit(0); }\n',
             **{'tests/efr/' + n + '.sol': n + '\n' for n in 'ABDEF'}}
    assert efr_top_level_call(prod, 8) == 'replayA' and efr_import(P, prod, 'replayA') == 'tests/efr/a-reference.mjs'
    for n in (9, 11, 16): assert efr_top_level_call(prod, n) is None, n
    assert efr_top_level_call(prod, 12) == 'replayAlias' and efr_import(P, prod, 'replayAlias') is None and efr_import(P, prod, 'replayB') is None
    assert efr_first_read(files['tests/efr/a-reference.mjs'], 'replayA', 4) and not efr_first_read(files['tests/efr/d-reference.mjs'], 'replayD', 5)
    assert not efr_first_read(files['tests/efr/e-reference.mjs'], 'replayE', 4) and not efr_first_read(files['tests/efr/a-reference.mjs'], 'replayA', 5)
    for old, new in (('export async function replayA(compile){', 'export async function replayA(compile){}\nexport async function replayA(compile){'),
                     ("export const unused=1;", 'export let replayA=null;'), ("export const unused=1;", '/*'), ('compile){\n', 'compile){ if(compile) return;\n')):
        text = files['tests/efr/a-reference.mjs'].replace(old, new) + ('*/\n' if new == '/*' else '')
        assert not any(efr_first_read(text, 'replayA', n) for n in range(2, 8)), old
    assert not node_producer_quiet(files['tests/efr/f-reference.mjs']) and efr_top_level_call(prod.replace('\n', '\r\n'), 8) is None
    nc = commit(files, 'exported function producer'); N = nc.ref; nl = commit({'tests/unrelated.txt': 'efr later\n'}, 'exported function later')
    iface = nonpython_entry_interface(P, prod); assert iface is not None
    role = {'path': P, 'input_revision': N, 'source_blob': blob(nc, P), 'kind': NONPY_ENTRY_KIND, 'command': ['node', P], 'interface': iface,
            'provenance': {'commit': N, 'path': P, 'blob': blob(nc, P)}, 'purpose': 'Synthetic producer.'}
    def row(call=8, name='A', line=4, form=EFR_FORM, **k):
        target = 'tests/efr/' + name + '.sol'
        return dict({'runner': NONPY_ENTRY_PREFIX + P, 'frames': [frame(nc, P, call), frame(nc, 'tests/efr/' + name.lower() + '-reference.mjs', line)],
                     'form': form, 'target': target, 'target_blob': blob(nc, target), 'purpose': 'Synthetic exported function read.'}, **k)
    key = lambda r: (P, tuple((f['path'], f['blob'], f['line']) for f in r['frames']), r['target'], r['target_blob'])
    reads = lambda *rows: {EFR_SECTION: list(rows)}
    T = 'tests/efr/A.sol'
    saved = REVIEWED_EXPORTED_FUNCTION_PRODUCERS, REVIEWED_EXPORTED_FUNCTION_READS, REVIEWED_NONPY_ENTRIES
    REVIEWED_NONPY_ENTRIES = reviewed_nonpy | {(P, blob(nc, P), N)}
    try:
        base_model, base = run(nl, standalone=[role])
        assert base[T]['class'] != 'keep' and NONPY_ENTRY_PREFIX + P in base_model['entry_points']
        rejected(nl, 'unreviewed exported function read', reads(row()), standalone=[role])
        bad = [row(9), row(11), row(12, 'B'), row(13, 'D', 5), row(14, 'E'), row(15, 'F'), row(8, 'A', 5)]
        REVIEWED_EXPORTED_FUNCTION_READS = frozenset(key(r) for r in [row()] + bad)
        rejected(nl, 'lacks a demonstrated producer', reads(row()), standalone=[role])
        REVIEWED_EXPORTED_FUNCTION_PRODUCERS = frozenset({(P, blob(nc, P), N, ('node', P, 'IN', 'OUT'))})
        model, rows = run(nl, reads(row()), standalone=[role])
        chain = rows[T]['runner_chain']
        assert rows[T]['class'] == 'keep' and chain['entry']['derived_from'] == NONPY_ENTRY_PREFIX + P
        assert chain['entry']['consumer_route']['kind'] == 'exported-function-read' and [e['operation'] for e in chain['edges']] == [EFR_HOP, EFR_OPERATION]
        assert model['entry_points'][NONPY_ENTRY_PREFIX + P]['source_only']
        assert sorted(p for p, r in rows.items() if canonical(r) != canonical(base[p])) == [T]  # one read only
        for r, message in zip(bad, ['top-level call of an imported function'] * 3 + ['first-statement literal readFileSync'] * 2
                              + ['quiet ES modules', 'first-statement literal readFileSync']):
            rejected(nl, message, reads(r), standalone=[role])
        for r, message in ((row(form='node-readFileSync'), 'invalid exported function read route'), (row(runner='validated:' + P), 'invalid exported function read route'),
                           (dict(row(), extra=1), 'invalid exported function read route'), (row(purpose=' '), 'invalid exported function read route'),
                           (dict(row(), frames=row()['frames'][:1]), 'not a producer call and a module read')):
            rejected(nl, message, reads(r), standalone=[role])
        # Form (a)'s section refuses these rows (form and table); no H997 role gives no credit.
        rejected(nl, 'invalid Node producer read route', {NODE_PRODUCER_SECTION: [row()]}, standalone=[role])
        rejected(nl, 'unreviewed Node producer read', {NODE_PRODUCER_SECTION: [row(form='node-readFileSync')]}, standalone=[role])
        assert run(nl, reads(row()))[1][T]['class'] != 'keep'
        # The objects must be the ones at the demonstration revision.
        later = commit({T: 'A changed\n'}, 'efr data changed'); restored = commit({T: 'A\n'}, 'efr data restored')
        REVIEWED_EXPORTED_FUNCTION_PRODUCERS = frozenset({(P, blob(nc, P), later.ref, ('node', P))})
        assert run(restored, reads(row()), standalone=[role])[1][T]['class'] != 'keep'
        REVIEWED_EXPORTED_FUNCTION_PRODUCERS = frozenset({(P, blob(nc, P), N, ('node', P))})
        assert run(later, reads(row()), standalone=[role])[1][T]['class'] != 'keep'  # stale target: no credit, no error
        assert run(restored, reads(row()), standalone=[role])[1][T]['class'] == 'keep'
        # A module the producer runs before the read (here D's) changed: every row goes stale, no error.
        other = commit({'tests/efr/d-reference.mjs': files['tests/efr/d-reference.mjs'] + '// changed\n'}, 'efr closure changed')
        assert run(other, reads(row()), standalone=[role])[1][T]['class'] != 'keep'
    finally: REVIEWED_EXPORTED_FUNCTION_PRODUCERS, REVIEWED_EXPORTED_FUNCTION_READS, REVIEWED_NONPY_ENTRIES = saved


FORM_CONTROLS.append(exported_function_controls)
