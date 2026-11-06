"""Negative controls for the external acceptance preflight; no parser mocks."""
import copy
from check_fixture_coverage import validate,validate_case_membership
manifest,data=validate()
def refuses(label,mutate):
    bad=copy.deepcopy(data);mutate(bad)
    try:validate_case_membership(manifest,bad)
    except AssertionError:print('PASS refused '+label);return
    raise AssertionError('accepted '+label)
refuses('empty',lambda d:d.update(cases=[]))
refuses('truncated',lambda d:d['cases'].pop())
refuses('duplicate replacing missing',lambda d:d['cases'].__setitem__(-1,copy.deepcopy(d['cases'][0])))
refuses('inverted polarity',lambda d:d['cases'][0].update(expect_accept=False))
refuses('wrong fixture provenance',lambda d:d['cases'][0].update(fixtures=[]))
