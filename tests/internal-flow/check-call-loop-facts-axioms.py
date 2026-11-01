#!/usr/bin/env python3
"""Exact actual kernel axiom sets for the original call/loop target consumer."""
import json
from pathlib import Path
import re
import sys
PINS = {'Solidity.Backend.InternalFlow.PublishedLoopChecks.callPrefix_cost': ['Classical.choice',
                                                                       'Quot.sound',
                                                                       'propext'],
 'Solidity.Backend.InternalFlow.PublishedLoopChecks.callPrefix_frame': ['Classical.choice',
                                                                        'Quot.sound',
                                                                        'propext'],
 'Solidity.Backend.InternalFlow.PublishedLoopChecks.callScope_frame': ['Classical.choice',
                                                                       'Quot.sound',
                                                                       'propext'],
 'Solidity.Backend.InternalFlow.PublishedLoopChecks.callScope_nonalloc': ['Classical.choice',
                                                                          'Quot.sound',
                                                                          'propext'],
 'Solidity.Backend.InternalFlow.PublishedLoopChecks.call_alias_first': ['Classical.choice',
                                                                        'Quot.sound',
                                                                        'propext'],
 'Solidity.Backend.InternalFlow.PublishedLoopChecks.call_alias_second': ['Classical.choice',
                                                                         'Quot.sound',
                                                                         'propext'],
 'Solidity.Backend.InternalFlow.PublishedLoopChecks.call_capacity': ['Classical.choice',
                                                                     'Quot.sound',
                                                                     'propext'],
 'Solidity.Backend.InternalFlow.PublishedLoopChecks.call_count_value': ['Classical.choice',
                                                                        'Quot.sound',
                                                                        'propext'],
 'Solidity.Backend.InternalFlow.PublishedLoopChecks.call_element_first': ['Classical.choice',
                                                                          'Quot.sound',
                                                                          'propext'],
 'Solidity.Backend.InternalFlow.PublishedLoopChecks.call_element_second': ['Classical.choice',
                                                                           'Quot.sound',
                                                                           'propext'],
 'Solidity.Backend.InternalFlow.PublishedLoopChecks.call_marker_value': ['Classical.choice',
                                                                         'Quot.sound',
                                                                         'propext'],
 'Solidity.Backend.InternalFlow.PublishedLoopChecks.call_private_length': ['Classical.choice',
                                                                           'Quot.sound',
                                                                           'propext'],
 'Solidity.Backend.InternalFlow.PublishedLoopChecks.call_rejected_frame': ['Classical.choice',
                                                                           'Quot.sound',
                                                                           'propext'],
 'Solidity.Backend.InternalFlow.PublishedLoopChecks.call_rejected_nonalloc': ['Classical.choice',
                                                                              'Quot.sound',
                                                                              'propext'],
 'Solidity.Backend.InternalFlow.PublishedLoopChecks.call_rejected_source': ['Classical.choice',
                                                                            'Quot.sound',
                                                                            'propext'],
 'Solidity.Backend.InternalFlow.PublishedLoopChecks.call_returned_length': ['Classical.choice',
                                                                            'Quot.sound',
                                                                            'propext'],
 'Solidity.Backend.InternalFlow.PublishedLoopChecks.call_target_reached': ['Classical.choice',
                                                                           'Quot.sound',
                                                                           'propext']}
log = Path(sys.argv[1]).read_text()
reports = re.findall(r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)", log)
actual = {n: sorted(a.strip() for a in names.split(',') if a.strip()) for n, names in reports}
assert len(actual) == len(reports), "duplicate axiom report"
assert actual == PINS, "missing, extra or changed axiom report"
assert 'error:' not in log and 'error(' not in log, "Lean diagnostics contain an error"
print(json.dumps({"status": "pass", "reports": len(reports)}, sort_keys=True))
