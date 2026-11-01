#!/usr/bin/env python3
"""Exact actual kernel axiom sets for allocating-loop prefix consumers."""
import json
from pathlib import Path
import re
import sys
PINS = {'Solidity.Backend.InternalFlow.AllocatingLoopHalts.allocation_negatives': ['Classical.choice',
                                                                            'Quot.sound',
                                                                            'propext'],
 'Solidity.Backend.InternalFlow.AllocatingLoopHalts.before_failure_observed': ['Classical.choice',
                                                                               'Quot.sound',
                                                                               'propext'],
 'Solidity.Backend.InternalFlow.AllocatingLoopHalts.target_allocation': ['Classical.choice',
                                                                         'Quot.sound',
                                                                         'propext'],
 'Solidity.Backend.InternalFlow.AllocatingLoopHalts.target_fault': ['Classical.choice',
                                                                    'Quot.sound',
                                                                    'propext'],
 'Solidity.Backend.InternalFlow.AllocatingLoopHalts.wrong_divergence_class': ['Classical.choice',
                                                                              'Quot.sound',
                                                                              'propext']}
log = Path(sys.argv[1]).read_text()
reports = re.findall(r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)", log)
actual = {n: sorted(a.strip() for a in names.split(',') if a.strip()) for n, names in reports}
assert len(actual) == len(reports), "duplicate axiom report"
assert actual == PINS, "missing, extra or changed axiom report"
assert 'error:' not in log and 'error(' not in log, "Lean diagnostics contain an error"
print(json.dumps({"status": "pass", "reports": len(reports)}, sort_keys=True))
