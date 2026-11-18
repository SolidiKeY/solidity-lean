# H1212 (gh#1526, Q-X1ERR-3, Option A), form (a): a literal Node readFileSync that
# a reviewed source-only Node producer (an H997 nonpython-entry role, P) performs
# on every successful run. consumer_routes section node_producer_reads:
#   {runner: 'nonpy-entry:P', frames: [{path, blob, line}, ...], form: 'node-readFileSync',
#    target, target_blob, purpose}
# frames[0] is P; each later frame is reached by a column-0 static ESM `import`
# line of the previous one (re-derived by the H951 reader), and the last frame's
# line is a top-level statement `[const|let|var NAME =] readFileSync(new URL('REL',
# import.meta.url) | join/resolve(__dirname, 'REL')[, ...]);` (H951 literal reader;
# a cwd-relative literal is refused, since the run's cwd is not recorded): column 0,
# bracket depth 0, after a line ending a statement (';' or '}'). No frame module
# shows a way to end the run early anywhere (functions are hoisted): no
# exit/abort/kill/reallyExit name, `process` only as process.argv/env/exitCode, no
# process module import, also inside template substitutions. ESM evaluates static
# imports before the importer's body and runs top-level statements in order, so
# a run of these exact objects that completed performed the read; modules the
# producer imports off the frame path are not audited (one could exit early), so
# the recorded demonstration of the exact objects remains the gate. All frames are .mjs. Opt-in twice by exact
# tuple: the producer (P, blob, demonstration revision, argv) in
# REVIEWED_NODE_PRODUCERS and the route (P, frames, target, target blob) in
# REVIEWED_NODE_PRODUCER_READS; anything else is rejected. At a measured --ref the
# row credits its target while P's H997 root is current with that blob and every
# frame and the target are the same blobs now and at the demonstration revision
# (stale otherwise: no credit, no error). Consumption credit only: the H997 root
# stays source-only with no pass, read anchor for other forms, helper, child,
# output, proof or runtime credit; static_routes are unchanged.
# Reviewed on master 57c3b2f7 from x1e-classify-rest-rest's B1 and B4n lists:
# tests/yul-views/physical-reference.mjs (H1025 entry), demonstrated at 181972c6
# (`node tests/yul-views/physical-reference.mjs PINNED_COMPILER REPORT` with
# pinned solc 0.8.38, reported in that lane's result 02e437a0), reads
# Physical.sol at top level, line 31. Refused, left unresolved: the other 18 B1
# .sol files (each read only inside an exported replay function body of a
# *-reference.mjs module, so a successful run does not by itself show the read),
# and all 39 B4n paths (their scripts/*.mjs checkers have no reviewed role and no
# demonstrated run).
NODE_PRODUCER_SECTION = 'node_producer_reads'
NODE_PRODUCER_OPERATION = 'Node readFileSync of a literal module-relative path at top level of a reviewed producer whose run was demonstrated'
NODE_PRODUCER_HOP = 'Node static import evaluated before the reviewed producer body'
_NODE_PRODUCER = 'tests/yul-views/physical-reference.mjs'
_NODE_PRODUCER_BLOB = '37d2270025ea6fd3c5819cc708b6a0608d5ffeb7'
# (producer, blob, demonstration revision, argv with placeholders for off-Git arguments)
REVIEWED_NODE_PRODUCERS = frozenset({
    (_NODE_PRODUCER, _NODE_PRODUCER_BLOB, '181972c695c3ad4008e1e119ee80af54c750123b', ('node', _NODE_PRODUCER, 'PINNED_COMPILER', 'REPORT'))})
# (producer, ((frame path, blob, line), ...), target, target blob)
REVIEWED_NODE_PRODUCER_READS = frozenset({
    (_NODE_PRODUCER, ((_NODE_PRODUCER, _NODE_PRODUCER_BLOB, 31),), 'tests/yul-views/Physical.sol', 'a15c05a0df66751a17d0f2e213dc05b6a30b3adc')})
_NODE_PRODUCER_READ = (r'(?:(?:const|let|var)[ \t]+[\w$]+[ \t]*=[ \t]*)?readFileSync\((?:[ \t]*new URL\(|[ \t]*(?:path\.)?(?:join|resolve)\([ \t]*__dirname)'
                       r'[^;]*\)[ \t]*;[ \t]*')


def node_producer_quiet(text):
    """No way to end the run early that this lexical audit can see, anywhere in
    the module (functions are hoisted): no exit/abort/kill/reallyExit name, no
    `process` but process.argv/env/exitCode, no `process` module import or
    require, also inside template substitutions (which must hold no braces)."""
    code, literals = _js_mask(text, True)
    forbidden = r'(?<![\w$])(?:exit|abort|kill|reallyExit)(?![\w$])|(?<![\w$])process(?![\w$])(?!\s*\.\s*(?:argv|env|exitCode)(?![\w$]))'
    substitutions = re.findall(r'\$\{([^{}`]*)\}', text)
    return not (re.search(forbidden, code) or any(re.search(forbidden, x) for x in substitutions) or text.count('${') != len(substitutions)
                or any(v[1:-1] in ('process', 'node:process') for v in literals.values()))


def node_producer_top_level(text, number):
    """Line number of text is an unconditional top-level read statement (see above)."""
    if not isinstance(text, str) or not _plain_lines(text) or '\0' in text: return False
    lines = text.split('\n')
    if type(number) is not int or not 1 <= number <= len(lines): return False
    code, _ = _js_mask(text, True); masked = code.split('\n')
    if len(masked) != len(lines) or not re.fullmatch(_NODE_PRODUCER_READ, masked[number - 1]): return False
    before = '\n'.join(masked[:number - 1])
    if sum(before.count(c) for c in '([{') != sum(before.count(c) for c in ')]}'): return False
    previous = [m.rstrip() for m in masked[:number - 1] if m.strip()]
    if previous and not previous[-1].endswith((';', '}')): return False
    return node_producer_quiet(text)


def node_producer_reads(classifier, graph, rows, producers=None, reads=None):
    """H1212 (a): exact top-level reads of a reviewed demonstrated Node producer."""
    repo = graph.repo
    producers = REVIEWED_NODE_PRODUCERS if producers is None else producers
    reads = REVIEWED_NODE_PRODUCER_READS if reads is None else reads
    for row in rows:
        if (not isinstance(row, dict) or set(row) != {'runner', 'frames', 'form', 'target', 'target_blob', 'purpose'}
                or row['form'] != 'node-readFileSync' or not isinstance(row['runner'], str) or not row['runner'].startswith(NONPY_ENTRY_PREFIX)
                or not isinstance(row['target'], str) or not isinstance(row['target_blob'], str)
                or not isinstance(row['purpose'], str) or not row['purpose'].strip()):
            raise ValueError('invalid Node producer read route')
        frames = row['frames']; target = row['target']; p = row['runner'][len(NONPY_ENTRY_PREFIX):]
        if not _frames_current(repo, frames, [(target, row['target_blob'])]): continue
        if frames[0]['path'] != p: raise ValueError('Node producer read does not start at its producer')
        if (p, tuple((f['path'], f['blob'], f['line']) for f in frames), target, row['target_blob']) not in reads:
            raise ValueError('unreviewed Node producer read: ' + p)
        demonstrated = [d for d in producers if d[:2] == (p, frames[0]['blob'])]
        if len(demonstrated) != 1: raise ValueError('Node producer read lacks a demonstrated producer: ' + p)
        root = graph.roots.get(row['runner'])
        if (root is None or 'derived_from' in root or not root.get('nonpython_entry_role') or not root.get('source_only')
                or root.get('source_blob') != frames[0]['blob'] or root.get('path') != p): continue
        _check_lines(repo, frames)
        if any(not f['path'].endswith('.mjs') or not _plain_lines(repo.texts[f['path']]) or not node_producer_quiet(repo.texts[f['path']]) for f in frames):
            raise ValueError('Node producer read frames must be ES modules')
        for caller, callee in zip(frames, frames[1:]):
            line = repo.texts[caller['path']].split('\n')[caller['line'] - 1]
            if not line.startswith('import') or _node_import(caller['path'], repo.texts[caller['path']], caller['line']) != callee['path']:
                raise ValueError('Node producer hop is not a top-level static import')
        reader = frames[-1]; text = repo.texts[reader['path']]
        if not node_producer_top_level(text, reader['line']) or _node_read(reader['path'], text, reader['line'], '/') != target:
            raise ValueError('Node producer read is not a top-level literal readFileSync of its target')
        if classifier['excluded'](target) or any(classifier['excluded'](f['path']) for f in frames): continue
        revision, argv = demonstrated[0][2:]
        if not _historical_objects(classifier, repo, revision, sorted({(f['path'], f['blob']) for f in frames} | {(target, row['target_blob'])})): continue
        _observe(graph, row['runner'], row, frames, target, NODE_PRODUCER_OPERATION, 'consumes', NODE_PRODUCER_HOP,
                 {'kind': 'node-producer-read', 'purpose': row['purpose'], 'demonstration_revision': revision, 'demonstrated_command': list(argv)})


register_consumer_section(NODE_PRODUCER_SECTION, ('runner', 'form', 'target', 'frames'), True,
                          lambda c, g, _, rows: node_producer_reads(c, g, rows))


def node_producer_controls(env):
    """H1212 (a) controls: the reviewed rows, a synthetic producer whose top-level
    read is credited only with both reviews, and the refused shapes."""
    global REVIEWED_NODE_PRODUCERS, REVIEWED_NODE_PRODUCER_READS, REVIEWED_NONPY_ENTRIES
    commit, run, rejected, blob, frame, reviewed_nonpy = (env[k] for k in ('commit', 'run', 'rejected', 'blob', 'frame', 'reviewed_nonpy'))
    assert len(REVIEWED_NODE_PRODUCERS) == len(REVIEWED_NODE_PRODUCER_READS) == 1
    assert all((p, b) in {(q, c) for q, c, _ in reviewed_nonpy} for p, b, *_ in REVIEWED_NODE_PRODUCERS)
    assert all(r[1][0][:2] in {d[:2] for d in REVIEWED_NODE_PRODUCERS} for r in REVIEWED_NODE_PRODUCER_READS)
    P, H = 'tests/nprod/prod.mjs', 'tests/nprod/helper.mjs'
    prod = ("import {readFileSync} from 'node:fs';\nimport {helper} from './helper.mjs';\nconst [a,b]=process.argv.slice(2);\n"
            "if(!a||!b)throw Error('usage');\nconst top=readFileSync(new URL('./top.sol',import.meta.url),'utf8');\n"   # 5 POSITIVE
            "function f(){\nreturn readFileSync(new URL('./inner.sol',import.meta.url),'utf8');\n}\n"                      # 7 function body
            "const c=a?\nreadFileSync(new URL('./cond.sol',import.meta.url),'utf8'):'';\n"                                # 10 conditional
            "if(a)\nreadFileSync(new URL('./cond.sol',import.meta.url));\n"                                                # 12 braceless if
            "const plain=readFileSync('tests/nprod/top.sol','utf8');\n"                                                    # 13 cwd-relative
            "// readFileSync(new URL('./top.sol',import.meta.url));\n"                                                     # 14 comment
            "const both=readFileSync(new URL('./top.sol',import.meta.url))||readFileSync(new URL('./cond.sol',import.meta.url));\n"  # 15 two reads
            "process.exitCode=0;\n")
    helper = "import {readFileSync} from 'node:fs';\nconst h=readFileSync(new URL('./helper.sol',import.meta.url),'utf8');\nexport const helper=()=>h;\n"
    files = {P: prod, H: helper, **{'tests/nprod/' + n + '.sol': n + '\n' for n in ('top', 'inner', 'cond', 'helper')}}
    assert node_producer_top_level(prod, 5) and node_producer_top_level(helper, 2)
    for n in (3, 7, 10, 12, 14): assert not node_producer_top_level(prod, n), n
    # Any visible way to end the run early, anywhere in the module, refuses every line.
    for t in ('process.exit(0);', 'function g(){ process.exit(0); }', 'const {exit}=process;', "import {exit} from 'node:process';",
              'const p=process;', 'process["exit"](0);', 'const s=`${process.exit(0)}`;', 'const s=`${{a:1}.a}`;', 'x.abort();', "const q=require('process');"):
        assert not node_producer_top_level(prod + t + '\n', 5) and not node_producer_top_level(prod.replace('if(!a', t + '\nif(!a'), 6), t
    assert not node_producer_top_level(prod.replace('\n', '\r\n'), 5) and not node_producer_top_level(None, 5) and not node_producer_top_level(prod, '5')
    nc = commit(files, 'Node producer'); N = nc.ref; nl = commit({'tests/unrelated.txt': 'nprod later\n'}, 'Node producer later')
    iface = nonpython_entry_interface(P, prod); assert iface is not None
    role = {'path': P, 'input_revision': N, 'source_blob': blob(nc, P), 'kind': NONPY_ENTRY_KIND, 'command': ['node', P], 'interface': iface,
            'provenance': {'commit': N, 'path': P, 'blob': blob(nc, P)}, 'purpose': 'Synthetic producer.'}
    T = 'tests/nprod/top.sol'
    row = lambda frames=None, target=T, **k: dict({'runner': NONPY_ENTRY_PREFIX + P, 'frames': frames or [frame(nc, P, 5)], 'form': 'node-readFileSync',
                                                  'target': target, 'target_blob': blob(nc, target), 'purpose': 'Synthetic producer read.'}, **k)
    reads = lambda *rows: {NODE_PRODUCER_SECTION: list(rows)}
    key = lambda r: (P, tuple((f['path'], f['blob'], f['line']) for f in r['frames']), r['target'], r['target_blob'])
    hop = row([frame(nc, P, 2), frame(nc, H, 2)], 'tests/nprod/helper.sol')
    saved = REVIEWED_NODE_PRODUCERS, REVIEWED_NODE_PRODUCER_READS, REVIEWED_NONPY_ENTRIES
    REVIEWED_NONPY_ENTRIES = reviewed_nonpy | {(P, blob(nc, P), N)}
    try:
        base_model, base = run(nl, standalone=[role])
        assert base[T]['class'] != 'keep' and NONPY_ENTRY_PREFIX + P in base_model['entry_points']
        rejected(nl, 'unreviewed Node producer read', reads(row()), standalone=[role])
        REVIEWED_NODE_PRODUCER_READS = frozenset(key(r) for r in [row(), hop] + [row([frame(nc, P, n)], t) for n, t in (
            (7, 'tests/nprod/inner.sol'), (10, 'tests/nprod/cond.sol'), (12, 'tests/nprod/cond.sol'), (13, T), (14, T), (15, T))])
        rejected(nl, 'lacks a demonstrated producer', reads(row()), standalone=[role])
        REVIEWED_NODE_PRODUCERS = frozenset({(P, blob(nc, P), N, ('node', P, 'IN', 'OUT'))})
        for good, target in ((row(), T), (hop, 'tests/nprod/helper.sol')):
            model, rows = run(nl, reads(good), standalone=[role])
            chain = rows[target]['runner_chain']
            assert rows[target]['class'] == 'keep' and chain['entry']['derived_from'] == NONPY_ENTRY_PREFIX + P
            assert chain['entry']['consumer_route']['kind'] == 'node-producer-read' and chain['edges'][-1]['operation'] == NODE_PRODUCER_OPERATION
            assert model['entry_points'][NONPY_ENTRY_PREFIX + P]['source_only'] and 'validated:' + P not in model['entry_points']
        assert sorted(p for p, r in run(nl, reads(row()), standalone=[role])[1].items() if canonical(r) != canonical(base[p])) == [T]  # one read only
        for n, t in ((7, 'tests/nprod/inner.sol'), (10, 'tests/nprod/cond.sol'), (12, 'tests/nprod/cond.sol'), (13, T), (14, T), (15, T)):
            rejected(nl, 'top-level literal readFileSync', reads(row([frame(nc, P, n)], t)), standalone=[role])
        # No H997 role, or the role anchoring the ordinary static form: no credit.
        assert run(nl, reads(row()))[1][T]['class'] != 'keep'
        assert run(nl, {'static_routes': [dict(row(), runner=NONPY_ENTRY_PREFIX + P)]}, standalone=[role])[1][T]['class'] != 'keep'
        for bad, message in ((row(form='node-import'), 'invalid Node producer read route'), (row(runner='validated:' + P), 'invalid Node producer read route'),
                             (dict(row(), extra=1), 'invalid Node producer read route'), (row(purpose=' '), 'invalid Node producer read route'),
                             (row([frame(nc, H, 2)], 'tests/nprod/helper.sol'), 'does not start at its producer')):
            rejected(nl, message, reads(bad), standalone=[role])
        # The frame and target objects must be the ones at the demonstration revision.
        later = commit({T: 'top changed\n'}, 'Node producer data changed'); restored = commit({T: 'top\n'}, 'Node producer data restored')
        REVIEWED_NODE_PRODUCERS = frozenset({(P, blob(nc, P), later.ref, ('node', P))})
        assert run(restored, reads(row()), standalone=[role])[1][T]['class'] != 'keep'
        REVIEWED_NODE_PRODUCERS = frozenset({(P, blob(nc, P), N, ('node', P))})
        assert run(later, reads(row()), standalone=[role])[1][T]['class'] != 'keep'  # stale target: no credit, no error
        assert run(restored, reads(row()), standalone=[role])[1][T]['class'] == 'keep'
    finally: REVIEWED_NODE_PRODUCERS, REVIEWED_NODE_PRODUCER_READS, REVIEWED_NONPY_ENTRIES = saved


FORM_CONTROLS.append(node_producer_controls)
