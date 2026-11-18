# H1108 (gh#1459, Q-X1R-FRAMECREDIT, Option A), x1ad: executes credit goes to
# the observed target only, never to a helper or data frame of the call stack,
# for (1) a same-revision nonpassing read (validated_routes in
# check-tests-used.py) and (2) an H938 persisted read (_observe and
# persisted_reads in fragments.py). The recorded frames stay in the chain as
# provenance. x1r (ce4999b50) already did this for persisted nonpassing reads
# (persisted_nonpassing_read, roles.py); its controls stay there. A passing
# read at its own revision still credits its frames: that run executed them.
# Controls only: this form registers no role, section or table.

_executes_credit_namespace = globals()
(FORM_CONTROLS, NONPASS_READ_OPERATION, canonical) = (
    _executes_credit_namespace[name] for name in ('FORM_CONTROLS', 'NONPASS_READ_OPERATION', 'canonical'))

EXECUTES_CREDIT_PASSING_OPERATION = 'validated Python read of measured bytes'


def executes_credit_controls(env):
    """x1ad H1108 controls: a helper frame and a data frame of a nonpassing or a
    persisted read get no executes credit; the target keeps its credit."""
    commit, run, blob = (env[k] for k in ('commit', 'run', 'blob'))
    P = 'tests/ec_np_test.py'; V = 'tests/ec_pass_test.py'; H = 'tests/ec_helper.py'
    D = 'tests/ec-data.txt'; F = 'tests/ec-frame.txt'
    nonpassing = ("import unittest\nclass T(unittest.TestCase):\n def test_it(self):\n  __import__('ec_helper').load('tests/ec-data.txt')\n"
                  "  self.fail('nonpassing')\nif __name__ == '__main__': unittest.main()\n")
    passing = ("import unittest\nclass T(unittest.TestCase):\n def test_it(self):\n  __import__('ec_helper').load('tests/ec-data.txt')\n"
               "if __name__ == '__main__': unittest.main()\n")
    ec = commit({P: nonpassing, V: passing, H: 'def load(p):\n    return open(p).read()\n', D: 'ec data\n', F: 'ec frame\n'}, 'executes credit')
    E = ec.ref; later = commit({'tests/unrelated.txt': 'EC\n'}, 'executes credit later')
    defs = [{'path': P, 'input_revision': E, 'source_blob': blob(ec, P), 'command': ['python3', '-B', P], 'kind': 'nonpassing-unittest',
             'purpose': 'Synthetic failing test.', 'input_scope': [D]},
            {'path': V, 'input_revision': E, 'source_blob': blob(ec, V), 'command': ['python3', '-B', V], 'kind': 'unittest',
             'purpose': 'Synthetic passing test.', 'input_scope': [D], 'other_reads': 'unresolved'}]
    frame = lambda path, line, qual=None, first=None: dict(
        {'path': path, 'blob': blob(ec, path), 'line': line}, **({} if qual is None else {'code_qualname': qual, 'code_firstlineno': first}))
    helper = {'nonpassing': frame(H, 2, 'load', 1), 'passing': frame(H, 2)}
    data = {'nonpassing': frame(F, 1, '<module>', 1), 'passing': frame(F, 1)}
    def read(kind, extra):
        if kind == 'nonpassing':
            runner, operation, stack = 'nonpassing:' + P, NONPASS_READ_OPERATION, [frame(P, 6, '<module>', 1), frame(P, 4, 'T.test_it', 3)]
        else: runner, operation, stack = 'validated:' + V, EXECUTES_CREDIT_PASSING_OPERATION, [frame(V, 5), frame(V, 4)]
        return {'persistent_reads': [{'runner': runner, 'input_revision': E, 'frames': stack + [extra], 'target': D,
                                      'target_blob': blob(ec, D), 'operation': operation}]}
    base = {repo.ref: run(repo, standalone=defs)[1] for repo in (ec, later)}
    for repo in (ec, later):
        for path in (D, H, F): assert base[repo.ref][path]['class'] != 'keep', path
    # (1) Same revision, nonpassing: the target only; helper and data frames
    # stay in the chain (executes provenance) but gain no record change.
    for extra in (helper['nonpassing'], data['nonpassing']):
        _, rows = run(ec, read('nonpassing', extra), standalone=defs)
        chain = rows[D]['runner_chain']; edges = chain['edges']
        assert rows[D]['class'] == 'keep' and chain['entry']['validation_at_measured_revision']['status'] == 'failed'
        assert edges[-1]['kind'] == 'consumes' and edges[-2]['target'] == extra['path'] and edges[-2]['kind'] == 'executes'
        assert canonical(rows[extra['path']]) == canonical(base[E][extra['path']]), extra['path']
        assert all(canonical(rows[p]) == canonical(base[E][p]) for p in (P, H, F)), extra['path']
    # (2) H938 persisted passing read at a later revision: the target only.
    for extra in (helper['passing'], data['passing']):
        _, rows = run(later, read('passing', extra), standalone=defs)
        chain = rows[D]['runner_chain']; edges = chain['edges']
        assert rows[D]['class'] == 'keep' and chain['entry']['consumer_route']['kind'] == 'persisted-read'
        assert edges[-2]['target'] == extra['path'] and edges[-2]['kind'] == 'executes' and edges[-1]['kind'] == 'consumes'
        assert all(canonical(rows[p]) == canonical(base[later.ref][p]) for p in (V, H, F)), extra['path']
    # Scope guard: the passing run at its own revision executed its frames, so
    # the helper keeps that credit (H1108 restricts only the two forms above).
    _, rows = run(ec, read('passing', helper['passing']), standalone=defs)
    assert rows[D]['class'] == 'keep' and rows[H]['class'] == 'keep' and rows[H]['runner_chain']['edges'][-1]['kind'] == 'executes'


FORM_CONTROLS.append(executes_credit_controls)
