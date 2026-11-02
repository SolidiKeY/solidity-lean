#!/usr/bin/env python3
"""Exact actual builtin axiom sets/order for the owned argument-failure client."""
import json,re,sys
from pathlib import Path
PINS = {'Solidity.Backend.InternalFlow.SharedCallPrefix.Checks.emitted_argument_failure': ['Classical.choice',
                                                                                    'Quot.sound',
                                                                                    'propext'],
 'Solidity.Backend.InternalFlow.SharedCallPrefix.Checks.emitted_revert': ['Classical.choice',
                                                                          'Quot.sound',
                                                                          'propext'],
 'Solidity.Backend.InternalFlow.SharedCallPrefix.Checks.emitted_success_vector': ['Classical.choice',
                                                                                  'Quot.sound',
                                                                                  'propext'],
 'Solidity.Backend.InternalFlow.SharedCallPrefix.Checks.emitted_success_repr': ['Classical.choice',
                                                                                'Quot.sound',
                                                                                'propext'],
 'Solidity.Backend.InternalFlow.SharedCallPrefix.Checks.emitted_not_fault': ['Classical.choice',
                                                                             'Quot.sound',
                                                                             'propext'],
 'Solidity.Backend.InternalFlow.SharedCallPrefix.Checks.emitted_not_success': ['Classical.choice',
                                                                               'Quot.sound',
                                                                               'propext'],
 'Solidity.Backend.InternalFlow.SharedCallPrefix.Checks.wrong_emitted_cursor': ['Classical.choice',
                                                                                'Quot.sound',
                                                                                'propext'],
 'Solidity.Backend.InternalFlow.SharedCallPrefix.Checks.distinct_emitted_programs': ['Classical.choice',
                                                                                     'Quot.sound',
                                                                                     'propext'],
 'Solidity.Backend.InternalFlow.SharedCallPrefix.Checks.public_metadata': ['Classical.choice',
                                                                           'Quot.sound',
                                                                           'propext'],
 'Solidity.Backend.InternalFlow.SharedPrefixCapacity.fork': ['Classical.choice',
                                                             'Quot.sound',
                                                             'propext'],
 'Solidity.Backend.InternalFlow.SharedCallPrefix.Checks.shared_capacity': ['Classical.choice',
                                                                           'Quot.sound',
                                                                           'propext'],
 'Solidity.Backend.InternalFlow.SharedCallPrefix.Checks.constructed_argument_vector': ['Classical.choice',
                                                                                       'Quot.sound',
                                                                                       'propext'],
 'Solidity.Backend.InternalFlow.SharedCallPrefix.Checks.constructed_wrong_alias': ['Classical.choice',
                                                                                   'Quot.sound',
                                                                                   'propext']}
ORDER = ['Solidity.Backend.InternalFlow.SharedCallPrefix.Checks.emitted_argument_failure',
 'Solidity.Backend.InternalFlow.SharedCallPrefix.Checks.emitted_revert',
 'Solidity.Backend.InternalFlow.SharedCallPrefix.Checks.emitted_success_vector',
 'Solidity.Backend.InternalFlow.SharedCallPrefix.Checks.emitted_success_repr',
 'Solidity.Backend.InternalFlow.SharedCallPrefix.Checks.emitted_not_fault',
 'Solidity.Backend.InternalFlow.SharedCallPrefix.Checks.emitted_not_success',
 'Solidity.Backend.InternalFlow.SharedCallPrefix.Checks.wrong_emitted_cursor',
 'Solidity.Backend.InternalFlow.SharedCallPrefix.Checks.distinct_emitted_programs',
 'Solidity.Backend.InternalFlow.SharedCallPrefix.Checks.public_metadata',
 'Solidity.Backend.InternalFlow.SharedPrefixCapacity.fork',
 'Solidity.Backend.InternalFlow.SharedCallPrefix.Checks.shared_capacity',
 'Solidity.Backend.InternalFlow.SharedCallPrefix.Checks.constructed_argument_vector',
 'Solidity.Backend.InternalFlow.SharedCallPrefix.Checks.constructed_wrong_alias']
log = Path(sys.argv[1]).read_text()
reports = re.findall(r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",log)
assert [n for n,_ in reports] == ORDER, "missing, extra, duplicate or reordered actual report"
actual = {n:sorted(x.strip() for x in a.split(',') if x.strip()) for n,a in reports}
assert actual == PINS, "changed actual axiom set"
assert not re.search(r"\berror(?:\(|:)",log), "Lean diagnostic error"
print(json.dumps({"status":"pass","actual_reports":len(reports),"actual_axioms":actual},indent=2))
