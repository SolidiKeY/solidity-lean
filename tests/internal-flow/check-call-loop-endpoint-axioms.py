#!/usr/bin/env python3
"""Exact actual kernel axiom sets for the original call/loop target consumer."""
import json
from pathlib import Path
import re
import sys
PINS = {'Solidity.Backend.InternalFlow.PublishedLoopChecks.call_complete_endpoint': ['Classical.choice',
                                                                              'Quot.sound',
                                                                              'propext'],
 'Solidity.Backend.InternalFlow.PublishedLoopChecks.call_exact_growth': ['Classical.choice',
                                                                         'Quot.sound',
                                                                         'propext'],
 'Solidity.Backend.InternalFlow.PublishedLoopChecks.call_loop_endpoint': ['Classical.choice',
                                                                          'Quot.sound',
                                                                          'propext'],
 'Solidity.Backend.InternalFlow.PublishedLoopChecks.call_negative_controls': ['Classical.choice',
                                                                              'Quot.sound',
                                                                              'propext'],
 'Solidity.Backend.InternalFlow.PublishedLoopChecks.call_rejected_not_fault': ['Classical.choice',
                                                                               'Quot.sound',
                                                                               'propext'],
 'Solidity.Backend.InternalFlow.PublishedLoopChecks.call_rejected_target': ['Classical.choice',
                                                                            'Quot.sound',
                                                                            'propext'],
 'Solidity.Backend.InternalFlow.PublishedLoopChecks.call_represented_contents': ['Classical.choice',
                                                                                 'Quot.sound',
                                                                                 'propext']}
log = Path(sys.argv[1]).read_text()
reports = re.findall(r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)", log)
actual = {n: sorted(a.strip() for a in names.split(',') if a.strip()) for n, names in reports}
assert len(actual) == len(reports), "duplicate axiom report"
assert actual == PINS, "missing, extra or changed axiom report"
assert 'error:' not in log and 'error(' not in log, "Lean diagnostics contain an error"
print(json.dumps({"status": "pass", "reports": len(reports)}, sort_keys=True))
