#!/usr/bin/env python3
"""Exact actual kernel axiom sets for the finite dispatch consumer."""
import json
from pathlib import Path
import re
import sys
PINS = {'Solidity.Backend.InternalFlow.DispatchChecks.capacity': ['Classical.choice',
                                                           'Quot.sound',
                                                           'propext'],
 'Solidity.Backend.InternalFlow.DispatchChecks.complete_endpoint': ['Classical.choice',
                                                                    'Quot.sound',
                                                                    'propext'],
 'Solidity.Backend.InternalFlow.DispatchChecks.endpoint': ['Classical.choice',
                                                           'Quot.sound',
                                                           'propext'],
 'Solidity.Backend.InternalFlow.DispatchChecks.exact_fallback': ['Classical.choice',
                                                                 'Quot.sound',
                                                                 'propext'],
 'Solidity.Backend.InternalFlow.DispatchChecks.fallback_not_fault': ['Classical.choice',
                                                                     'Quot.sound',
                                                                     'propext'],
 'Solidity.Backend.InternalFlow.DispatchChecks.negative_controls': ['Classical.choice',
                                                                    'Quot.sound',
                                                                    'propext'],
 'Solidity.Backend.InternalFlow.DispatchChecks.observe_after': ['Classical.choice',
                                                                'Quot.sound',
                                                                'propext'],
 'Solidity.Backend.InternalFlow.MemoryDispatchChecks.capacity': ['Classical.choice',
                                                                 'Quot.sound',
                                                                 'propext'],
 'Solidity.Backend.InternalFlow.MemoryDispatchChecks.complete_endpoint': ['Classical.choice',
                                                                          'Quot.sound',
                                                                          'propext'],
 'Solidity.Backend.InternalFlow.MemoryDispatchChecks.endpoint': ['Classical.choice',
                                                                 'Quot.sound',
                                                                 'propext'],
 'Solidity.Backend.InternalFlow.MemoryDispatchChecks.negative_escape': ['Classical.choice',
                                                                        'Quot.sound',
                                                                        'propext'],
 'Solidity.Backend.InternalFlow.MemoryDispatchChecks.observe_after': ['Classical.choice',
                                                                      'Quot.sound',
                                                                      'propext']}
log = Path(sys.argv[1]).read_text()
reports = re.findall(r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)", log)
actual = {n: sorted(a.strip() for a in names.split(',') if a.strip()) for n, names in reports}
assert len(actual) == len(reports), "duplicate axiom report"
assert actual == PINS, "missing, extra or changed axiom report"
assert 'error:' not in log and 'error(' not in log, "Lean diagnostics contain an error"
print(json.dumps({"status": "pass", "reports": len(reports)}, sort_keys=True))
