# H1234 (gh#1544, Q-X1ERR-7, Option C), form (2): demonstrated-run roles for
# scripts/*.mjs checkers (B4n). consumer_routes section mjs_checker_reads, one
# row per reviewed read, in the form (a) row shape:
#   {runner: 'nonpy-entry:C', frames: [{path: C, blob, line}], form:
#    'node-readFileSync', target, target_blob, purpose}
# C is a reviewed live Node checker under scripts/ with an H997
# nonpython-entry role: this module adds the 'nonpy' review part H1234 (exact
# (C, blob, introducing commit) rows, prefix scripts/) through the registry,
# and the census owner adds the role definitions. A row is checked by the
# unchanged form (a) handler node_producer_reads (node-source-producer-reads.py)
# against this module's own tables: frames[0] is C, the frame line is a
# top-level unconditional literal readFileSync(new URL(..., import.meta.url))
# statement of the quiet module C (no exit/abort/kill name, `process` only as
# argv/env/exitCode), and C, frames and target are the same blobs now and at the
# demonstration revision. So that nothing unpinned runs before the read, C's whole
# local static import closure (node_local_import_closure) must also be the same
# objects now and at the demonstration revision (stale otherwise), and a closure
# module with a dynamic import( is never credited; off-Git packages and
# createRequire loads are covered only by the demonstration. Opt-in twice by exact tuple: the checker (C, blob,
# demonstration revision, argv with placeholders for off-Git arguments) in
# REVIEWED_MJS_CHECKERS and the route (C, frames, target, target blob) in
# REVIEWED_MJS_CHECKER_READS; anything else is rejected, and each section
# refuses the other's table. Consumption credit only: the H997 roots stay
# source-only, with no pass, read anchor, helper, child, output, proof or
# runtime credit; static_routes and form (a) are unchanged.
# Demonstrations, all at master abec4d99 in a clean scratch worktree, exit 0:
# - check-creation-artifacts-vectors.mjs, `node C` with tests/creation-artifacts/evm
#   dependencies from its lockfile (npm ci --ignore-scripts): 16/16 Osaka creation vectors;
# - check-abi-hex-call.mjs MODULES C38 C34: 36 EVM runs, 40 compiler rejections;
# - check-memory-reference-arrays.mjs C34 MODULES: 92 source fixture executions;
# - check-modifier-frames.mjs C38 MODULES: 40 pinned solc/EVM modifier vectors;
# - check-public-getters.mjs C38 MODULES (also C34): 62 executions, 7 rejections;
# - evm-reference/slice-reference-copies.mjs C38 (scripts/evm-reference deps).
# C38/C34 are the pinned soljson 0.8.38/0.8.34 files (sha256 6c74ffba...d390 and
# c8649f8d...d1d8, from the solidity GitHub releases), MODULES is
# scripts/evm-vectors/node_modules from its lockfile, as scripts/evm-vectors/run.sh does.
# Admitted (6): tests/creation-artifacts/vectors.jsonl, tests/abi-0.8.38/HexCall.sol,
# tests/memory-reference-arrays/ReferenceArrays.sol, tests/solc/ModifierFrames.sol,
# tests/solc/PublicGetters.sol, tests/solc/SliceReferenceCopies.sol.
# Refused, left unresolved (33 of the 39 B4n paths): reads inside functions,
# loops or conditional code (abi-0.8.38 AccessEntry, EnumArrays(.vectors.json),
# Features, InheritedSelectors, LazyEntry, V1Entry; recursive-0.8.38; solc
# CallExceptions, FunctionValueReferences, Loops, MemoryCompilerLoops,
# SelfPowerData, SignedNumeric, SliceCopies, TransientFactory, TransientStorage,
# TransientWorldScenario); readers that export names, so no H997 interface
# (abi-entry-probe, host1-finalization, check-p6-memory, solkey-migration and
# yul-composition sources, check-trust); `.test.mjs` readers, which are node-test
# runners, not checkers (ContractWorld, GuardedCancellation, MemoryStorageCopies,
# PaymentInvalidCallee, PaymentReferences, SpecConstants, TransientSource,
# source-units). tests/trust-inventory.json is read by the CI trust check, but
# the reviewed route in check-tests-used.py pins gate.sh/checks-fast.sh blobs
# that master has since changed (checker-owner refresh, not a form).
(FORM_CONTROLS, NODE_SUFFIXES, NONPY_ENTRY_PREFIX, REVIEW_TABLE_PARTS, _current, _historical_objects, _js_mask, _node_import, _plain_lines,
 register_consumer_section) = (globals()[name] for name in (
    'FORM_CONTROLS', 'NODE_SUFFIXES', 'NONPY_ENTRY_PREFIX', 'REVIEW_TABLE_PARTS', '_current', '_historical_objects', '_js_mask', '_node_import',
    '_plain_lines', 'register_consumer_section'))
MJS_CHECKER_SECTION = 'mjs_checker_reads'
_MJS_REVISION = 'abec4d99f58359480428d46e832ade9db3f0fc62'
# checker (under scripts/), blob, introducing commit, read line, target (under tests/), target blob, argv after `node C`
_MJS_ROWS = (
    ('check-creation-artifacts-vectors.mjs', 'a6fb83eadb1ba8fd368fe5766f38a11e4ff9534c', '7cc60bc05db248cdbf2cbdbbe041c2fa5d3555a3', 10,
     'creation-artifacts/vectors.jsonl', '2e48ce9aa4375539a7ba957cc38445ee3505b3f7', ()),
    ('check-abi-hex-call.mjs', '31689b02805fc5a1a55e6b3f54380ac2fa01f629', '0f92a28a0b32fe12d0187d3df51c8830e4998a77', 25,
     'abi-0.8.38/HexCall.sol', '9f2955e3a36d1f3dca726d4dee28ef0c1cec29b7', ('EXTERNAL_NODE_MODULES', 'PINNED_COMPILER_0_8_38', 'PINNED_COMPILER_0_8_34')),
    ('check-memory-reference-arrays.mjs', '8f82e17da5ebeee7da1411379ed9f6e65b347c24', 'f93e1e981f0eeed1e51b132bea669f92d74955e9', 23,
     'memory-reference-arrays/ReferenceArrays.sol', 'c6b0a30bd2669f43a8228839539ed7cc884e404f', ('PINNED_COMPILER_0_8_34', 'EXTERNAL_NODE_MODULES')),
    ('check-modifier-frames.mjs', 'db120a3a3a97c4bb4f5dc8e65bb8d9955a3381ce', '0f92a28a0b32fe12d0187d3df51c8830e4998a77', 22,
     'solc/ModifierFrames.sol', '4262a94a849fa579d4a6d88d0b625c9d397f8ba6', ('PINNED_COMPILER_0_8_38', 'EXTERNAL_NODE_MODULES')),
    ('check-public-getters.mjs', 'fa184e5d5dfb57af830a18789a0e2dd8a6e8386c', '0f92a28a0b32fe12d0187d3df51c8830e4998a77', 27,
     'solc/PublicGetters.sol', '4dc98b1240ab0e18e0c7223448c1c62211eea8a6', ('PINNED_COMPILER_0_8_38', 'EXTERNAL_NODE_MODULES')),
    ('evm-reference/slice-reference-copies.mjs', '68dc55da4ca2b66d4d90fb96505ef001a34ba9ff', 'a958a7470b2177216c97ee619fbf5b1254ab8d79', 18,
     'solc/SliceReferenceCopies.sol', '62bef224fc9ba65d8475f4637af325f4d2cc4f09', ('PINNED_COMPILER_0_8_38',)))
REVIEWED_MJS_CHECKERS = frozenset(('scripts/' + c, b, _MJS_REVISION, ('node', 'scripts/' + c) + argv) for c, b, _, _, _, _, argv in _MJS_ROWS)
REVIEWED_MJS_CHECKER_READS = frozenset(('scripts/' + c, (('scripts/' + c, b, line),), 'tests/' + t, tb) for c, b, _, line, t, tb, _ in _MJS_ROWS)
REVIEW_TABLE_PARTS['nonpy'].append(('H1234', frozenset(('scripts/' + c, b, intro) for c, b, intro, *_ in _MJS_ROWS), ('scripts/',)))


def node_local_import_closure(repo, path):
    """(path, blob) of path and every local module its column-0 static imports reach, or None.

    None when a local import is missing from the tree or a module in the closure has a
    dynamic import( (an unpinned module could then run before the read). Bare-specifier
    packages (off-Git node_modules) are outside the closure; the demonstration covers them."""
    seen = {path: repo.tree[path][2]} if path in repo.tree and path in repo.texts else None
    todo = [path]
    while seen is not None and todo:
        source = todo.pop(); text = repo.texts.get(source)
        if not isinstance(text, str) or not _plain_lines(text) or re.search(r'(?<![\w$.])import\s*\(', _js_mask(text, True)[0]): return None
        for n, line in enumerate(text.split('\n'), 1):
            if not line.startswith('import'): continue
            found = _node_import(source, text, n)
            if found is None or not found.endswith(NODE_SUFFIXES) or found in seen: continue
            if found not in repo.tree or found not in repo.texts: return None
            seen[found] = repo.tree[found][2]; todo.append(found)
    return None if seen is None else sorted(seen.items())


def node_closure_demonstrated(classifier, repo, rows, producers):
    """Rows whose producer's whole local import closure is the same objects now and at its
    demonstration revision; any other well-formed row is stale (dropped, no credit, no error).
    Malformed rows pass through, so the handler still rejects them."""
    kept = []
    for row in rows:
        runner = row.get('runner') if isinstance(row, dict) else None
        if not isinstance(runner, str) or not runner.startswith(NONPY_ENTRY_PREFIX): kept.append(row); continue
        p = runner[len(NONPY_ENTRY_PREFIX):]
        revisions = [d[2] for d in producers if d[0] == p and _current(repo, p, d[1])]
        if len(revisions) != 1: kept.append(row); continue
        closure = node_local_import_closure(repo, p)
        if closure is not None and _historical_objects(classifier, repo, revisions[0], closure): kept.append(row)
    return kept


register_consumer_section(MJS_CHECKER_SECTION, ('runner', 'form', 'target', 'frames'), True,
                          lambda c, g, _, rows: node_producer_reads(c, g, node_closure_demonstrated(c, g.repo, rows, REVIEWED_MJS_CHECKERS),
                                                                    REVIEWED_MJS_CHECKERS, REVIEWED_MJS_CHECKER_READS))


def mjs_checker_controls(env):
    """H1234 (2) controls: the reviewed tables and H997 part, a synthetic
    scripts/ checker credited only through this section with both reviews and
    an unchanged import closure, and each section refusing the other's table."""
    global REVIEWED_MJS_CHECKERS, REVIEWED_MJS_CHECKER_READS, REVIEWED_NONPY_ENTRIES, REVIEWED_NODE_PRODUCERS, REVIEWED_NODE_PRODUCER_READS
    commit, run, rejected, blob, frame, reviewed_nonpy = (env[k] for k in ('commit', 'run', 'rejected', 'blob', 'frame', 'reviewed_nonpy'))
    assert len(REVIEWED_MJS_CHECKERS) == len(REVIEWED_MJS_CHECKER_READS) == 6
    part = [p for p in REVIEW_TABLE_PARTS['nonpy'] if p[0] == 'H1234']
    assert len(part) == 1 and part[0][1] <= reviewed_nonpy and {r[:2] for r in part[0][1]} == {c[:2] for c in REVIEWED_MJS_CHECKERS}
    assert all(r[1][0][:2] in {c[:2] for c in REVIEWED_MJS_CHECKERS} and r[0].startswith('scripts/') and r[2].startswith('tests/') for r in REVIEWED_MJS_CHECKER_READS)
    assert not {r[2] for r in REVIEWED_MJS_CHECKER_READS} & {r[2] for r in REVIEWED_NODE_PRODUCER_READS}
    C, H = 'scripts/mjsck/check.mjs', 'scripts/mjsck/help.mjs'
    checker = ("#!/usr/bin/env node\nimport {readFileSync} from 'node:fs';\nimport {help} from './help.mjs';\nconst [compiler]=process.argv.slice(2);\n"
               "if(!compiler)throw Error('usage');\nconst source=readFileSync(new URL('../../tests/mjsck/Top.sol',import.meta.url),'utf8');\n"
               "for(const x of [1]){\nreadFileSync(new URL('../../tests/mjsck/Loop.sol',import.meta.url));\n}\nconsole.log(source.length,help);\n")
    helper = "import {deep} from './deep.mjs';\nexport const help=deep;\n"
    nc = commit({C: checker, H: helper, 'scripts/mjsck/deep.mjs': 'export const deep=1;\n', 'tests/mjsck/Top.sol': 'top\n', 'tests/mjsck/Loop.sol': 'loop\n'},
                'mjs checker'); N = nc.ref
    nl = commit({'tests/unrelated.txt': 'mjs later\n'}, 'mjs checker later')
    assert [p for p, _ in node_local_import_closure(nl, C)] == [C, 'scripts/mjsck/deep.mjs', H]
    iface = nonpython_entry_interface(C, checker); assert iface is not None
    role = {'path': C, 'input_revision': N, 'source_blob': blob(nc, C), 'kind': NONPY_ENTRY_KIND, 'command': ['node', C], 'interface': iface,
            'provenance': {'commit': N, 'path': C, 'blob': blob(nc, C)}, 'purpose': 'Synthetic checker.'}
    T = 'tests/mjsck/Top.sol'
    row = lambda line=6, target=T, **k: dict({'runner': NONPY_ENTRY_PREFIX + C, 'frames': [frame(nc, C, line)], 'form': 'node-readFileSync',
                                              'target': target, 'target_blob': blob(nc, target), 'purpose': 'Synthetic checker read.'}, **k)
    key = lambda r: (C, tuple((f['path'], f['blob'], f['line']) for f in r['frames']), r['target'], r['target_blob'])
    reads = lambda *rows: {MJS_CHECKER_SECTION: list(rows)}
    demonstrated = frozenset({(C, blob(nc, C), N, ('node', C, 'PINNED_COMPILER'))})
    saved = REVIEWED_MJS_CHECKERS, REVIEWED_MJS_CHECKER_READS, REVIEWED_NONPY_ENTRIES, REVIEWED_NODE_PRODUCERS, REVIEWED_NODE_PRODUCER_READS
    try:
        rejected(nl, 'unreviewed non-Python entry role', standalone=[role])  # no H997 row for the checker yet
        REVIEWED_NONPY_ENTRIES = reviewed_nonpy | {(C, blob(nc, C), N)}
        base = run(nl, standalone=[role])[1]; assert base[T]['class'] != 'keep'
        rejected(nl, 'unreviewed Node producer read', reads(row()), standalone=[role])
        REVIEWED_MJS_CHECKER_READS = frozenset({key(row()), key(row(8, 'tests/mjsck/Loop.sol'))})
        rejected(nl, 'lacks a demonstrated producer', reads(row()), standalone=[role])
        REVIEWED_MJS_CHECKERS = demonstrated
        rows = run(nl, reads(row()), standalone=[role])[1]
        assert rows[T]['class'] == 'keep' and rows[T]['runner_chain']['entry']['derived_from'] == NONPY_ENTRY_PREFIX + C
        assert rows[T]['runner_chain']['entry']['consumer_route']['demonstrated_command'] == ['node', C, 'PINNED_COMPILER']
        assert sorted(p for p, r in rows.items() if canonical(r) != canonical(base[p])) == [T]
        rejected(nl, 'top-level literal readFileSync', reads(row(8, 'tests/mjsck/Loop.sol')), standalone=[role])
        rejected(nl, 'invalid Node producer read route', reads(dict(row(), extra=1)), standalone=[role])  # malformed rows still reach the handler
        # A module two imports away changed, or gained a dynamic import: stale, no credit, no error.
        deep = commit({'scripts/mjsck/deep.mjs': 'process.exitCode=0;\nexport const deep=1;\n'}, 'mjs deep changed')
        assert run(deep, reads(row()), standalone=[role])[1][T]['class'] != 'keep'
        dynamic = commit({'scripts/mjsck/deep.mjs': 'export const deep=1;\n', H: helper + "await import('./deep.mjs');\n"}, 'mjs dynamic import')
        assert node_local_import_closure(dynamic, C) is None and run(dynamic, reads(row()), standalone=[role])[1][T]['class'] != 'keep'
        back = commit({H: helper}, 'mjs restored')
        assert run(back, reads(row()), standalone=[role])[1][T]['class'] == 'keep'
        # Each section refuses the other's table, even when that table holds the row.
        REVIEWED_NODE_PRODUCERS, REVIEWED_NODE_PRODUCER_READS = demonstrated, REVIEWED_MJS_CHECKER_READS
        REVIEWED_MJS_CHECKERS, REVIEWED_MJS_CHECKER_READS = saved[:2]
        assert run(nl, {NODE_PRODUCER_SECTION: [row()]}, standalone=[role])[1][T]['class'] == 'keep'  # form (a) with the seeded table
        rejected(nl, 'unreviewed Node producer read', reads(row()), standalone=[role])
        REVIEWED_NODE_PRODUCERS, REVIEWED_NODE_PRODUCER_READS = saved[3:]
        REVIEWED_MJS_CHECKERS, REVIEWED_MJS_CHECKER_READS = demonstrated, frozenset({key(row())})
        rejected(nl, 'unreviewed Node producer read', {NODE_PRODUCER_SECTION: [row()]}, standalone=[role])
        assert not REVIEWED_NODE_PRODUCER_READS & saved[1] and not REVIEWED_NODE_PRODUCERS & saved[0]
    finally: REVIEWED_MJS_CHECKERS, REVIEWED_MJS_CHECKER_READS, REVIEWED_NONPY_ENTRIES, REVIEWED_NODE_PRODUCERS, REVIEWED_NODE_PRODUCER_READS = saved


FORM_CONTROLS.append(mjs_checker_controls)
