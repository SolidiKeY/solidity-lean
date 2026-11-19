# H1212 (gh#1526, Q-X1ERR-3, Option A), form (b): further H1009 nonpassing read
# persistence runners, reviewed case by case, without changing x1r's pinned
# 11-row REVIEWED_NONPASS_PERSISTENCE (roles.py). consumer_routes section
# reviewed_nonpass_reads takes rows of the persistent_reads nonpassing shape
#   {runner: 'nonpassing:P', input_revision, frames: [{path, blob, line,
#    code_qualname, code_firstlineno}], target, target_blob, operation}
# with operation NONPASS_READ_OPERATION, and checks each with the unchanged
# H1009 rule (persisted_nonpassing_read) against REVIEWED_NONPASS_ROWS_H1212
# instead of the H1009 table: P's nonpassing-unittest definition at the
# recorded revision, its blob, every frame and the target the same blobs now
# and then, the introducing commit, an entered test or setup context and the
# definition's reviewed scope. A row at its own revision is the ordinary
# failed-run read and is skipped here. The tables stay disjoint: an H1009
# runner here, or one of these in persistent_reads, is unreviewed. Source-only
# failed-run root; the named in-scope target alone is credited (consumption):
# no pass, helper, child, output, proof or runtime credit.
# Reviewed on master 57c3b2f7 from x1e-classify-rest-rest's B4p list (the
# failing unittests): each is a declared unittest runner (class and explicit
# unittest.main), failed when run there with python3 -B, and its blob was
# introduced once, by the commit recorded. The other B4p consumers need
# arguments, deleted evidence or absolute /workspace paths: they are not
# failing unittests and stay unresolved.
NONPASS_ROWS_SECTION = 'reviewed_nonpass_reads'
# (runner path, runner blob, commit that introduced that blob at that path)
REVIEWED_NONPASS_ROWS_H1212 = frozenset({
    ('tests/roadmap-v17/test_creation_try.py', 'd7853dbbe9750a1e3628c823cf2c221a947918b3', 'bd6573f3cd7107308989e921ffb4b9c4c9ed44dc'),
    ('tests/roadmap-v17/test_process_identity.py', '142a76b8a49268aff84bf791fdcb7c71b29e486f', 'c1cd7210d5f6423fc49a082b9c2d815ca4f7a4a8'),
    ('scripts/test-sol-numeric-literals-integrated-v2.py', 'e1e82d90f77d1d0eb92f9a5619cdd386f89c83c0', 'e8f27ea28e891296f35955234cb30383b15ede60'),
    ('Bridge/tests/precompile-agreement/test_inventory.py', '545c6d0b04d1ba570de5bd6274fdc85b1faee234', '4af981a849741ee8accac29cda9056b90658957f'),
})


def reviewed_nonpass_reads(classifier, graph, catalog, rows, reviewed=None):
    """H1212 (b): H1009 persisted nonpassing reads of the runners reviewed here."""
    reviewed = REVIEWED_NONPASS_ROWS_H1212 if reviewed is None else reviewed
    for row in rows:
        if not isinstance(row, dict) or set(row) != {'runner', 'input_revision', 'frames', 'target', 'target_blob', 'operation'}:
            raise ValueError('invalid reviewed nonpassing read route')
        if row['operation'] != NONPASS_READ_OPERATION: raise ValueError('reviewed nonpassing read needs the nonpassing operation')
        if row['input_revision'] == graph.repo.ref: continue
        persisted_nonpassing_read(classifier, graph, catalog, row, reviewed)


register_consumer_section(NONPASS_ROWS_SECTION, ('runner', 'input_revision', 'target', 'frames'), True,
                          lambda c, g, k, rows: reviewed_nonpass_reads(c, g, k, rows))


def reviewed_nonpass_rows_controls(env):
    """H1212 (b) controls: the reviewed rows, credit through this section only,
    the H1009 table and section unchanged, and the refused shapes."""
    global REVIEWED_NONPASS_ROWS_H1212
    commit, run, rejected, blob = (env[k] for k in ('commit', 'run', 'rejected', 'blob'))
    paths = {p for p, _, _ in REVIEWED_NONPASS_ROWS_H1212}
    assert len(REVIEWED_NONPASS_ROWS_H1212) == len(paths) == 4 and not paths & {p for p, _, _ in REVIEWED_NONPASS_PERSISTENCE}
    assert len(REVIEWED_NONPASS_PERSISTENCE) == 11 and NONPASS_ROWS_SECTION in CONSUMER_SECTIONS
    P, D, O = 'tests/npr/test_np.py', 'tests/npr/data.txt', 'tests/npr/other.txt'
    text = ("import unittest\nclass T(unittest.TestCase):\n def test_it(self):\n  open('tests/npr/data.txt').read()\n"
            "  open('tests/npr/other.txt').read()\n  self.fail('nonpassing')\nif __name__ == '__main__': unittest.main()\n")
    nc = commit({P: text, D: 'npr data\n', O: 'npr other\n'}, 'reviewed nonpassing'); N = nc.ref
    nl = commit({'tests/unrelated.txt': 'npr later\n'}, 'reviewed nonpassing later')
    defn = {'path': P, 'input_revision': N, 'source_blob': blob(nc, P), 'command': ['python3', '-B', P], 'kind': 'nonpassing-unittest',
            'purpose': 'Synthetic failing test.', 'input_scope': [D]}
    fr = lambda line=4, qual='T.test_it', first=3: {'path': P, 'blob': blob(nc, P), 'line': line, 'code_qualname': qual, 'code_firstlineno': first}
    row = lambda target=D, frames=None, **k: dict({'runner': 'nonpassing:' + P, 'input_revision': N, 'frames': frames or [fr(7, '<module>', 1), fr()],
        'target': target, 'target_blob': blob(nc, target), 'operation': NONPASS_READ_OPERATION}, **k)
    reads = lambda *rows: {NONPASS_ROWS_SECTION: list(rows)}
    base_model, base = run(nl, standalone=[defn])
    assert base[D]['class'] != 'keep' and NONPASS_PERSIST_PREFIX + P not in base_model['entry_points']
    saved = REVIEWED_NONPASS_ROWS_H1212
    try:
        rejected(nl, 'unreviewed nonpassing read persistence', reads(row()), standalone=[defn])
        REVIEWED_NONPASS_ROWS_H1212 = frozenset({(P, blob(nc, P), N)})
        model, rows = run(nl, reads(row()), standalone=[defn]); entry = model['entry_points'][NONPASS_PERSIST_PREFIX + P]
        assert rows[D]['class'] == 'keep' and rows[D]['runner_chain']['entry']['consumer_route']['kind'] == 'persisted-nonpassing-read'
        assert rows[D]['runner_chain']['edges'][-1]['operation'] == PERSISTED_NONPASS_OPERATION
        assert entry['source_only'] and entry['validation_at_measured_revision']['status'] == 'unavailable'
        assert sorted(p for p, r in rows.items() if canonical(r) != canonical(base[p])) == [D]  # one read, no other credit
        # The H1009 section keeps its own table: this review admits nothing there.
        rejected(nl, 'unreviewed nonpassing read persistence', {'persistent_reads': [row()]}, standalone=[defn])
        # At its own revision the row is skipped here (the ordinary failed-run read is a catalog read).
        assert canonical(run(nc, reads(row()), standalone=[defn])[1][D]) == canonical(run(nc, standalone=[defn])[1][D])
        # Out of the reviewed scope: an unreviewed read, never keep.
        _, rows = run(nl, reads(row(O, [fr(7, '<module>', 1), fr(5)])), standalone=[defn])
        assert rows[O]['class'] is None and 'unreviewed_readers' in rows[O]['secondary']
        for bad, message in ((row(operation='validated Python read of measured bytes'), 'needs the nonpassing operation'),
                             (dict(row(), extra=1), 'invalid reviewed nonpassing read route'),
                             (row(runner='validated:' + P), 'needs a nonpassing runner'),
                             (row(frames=[fr(7, '<module>', 1)]), 'entered test or setup context'),
                             (row(input_revision='0' * 40), 'lacks its nonpassing runner definition')):
            rejected(nl, message, reads(bad), standalone=[defn])
        REVIEWED_NONPASS_ROWS_H1212 = frozenset({(P, blob(nc, P), nl.ref)})
        rejected(nl, 'introducing provenance', reads(row()), standalone=[defn])
        REVIEWED_NONPASS_ROWS_H1212 = frozenset({(P, blob(nc, P), N)})
        edited = commit({D: 'npr changed\n'}, 'reviewed nonpassing edited')  # stale: no credit, no error
        assert run(edited, reads(row()), standalone=[defn])[1][D]['class'] != 'keep'
        commit({D: 'npr data\n'}, 'reviewed nonpassing restored')
    finally: REVIEWED_NONPASS_ROWS_H1212 = saved


FORM_CONTROLS.append(reviewed_nonpass_rows_controls)
