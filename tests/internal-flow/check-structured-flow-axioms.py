#!/usr/bin/env python3
"""Exact actual kernel axiom sets for the structural successful-flow consumer."""
import json
from pathlib import Path
import re
import sys
PINS = {'Solidity.Backend.InternalFlow.FrameProg.sound': ['Classical.choice',
                                                   'Quot.sound',
                                                   'propext'],
 'Solidity.Backend.InternalFlow.FrameStmt.sound': ['Classical.choice',
                                                   'Quot.sound',
                                                   'propext'],
 'Solidity.Backend.InternalFlow.StructuredChecks.actual_run': ['Classical.choice',
                                                               'Quot.sound',
                                                               'propext'],
 'Solidity.Backend.InternalFlow.StructuredChecks.actual_writer_excluded': ['Classical.choice',
                                                                           'Quot.sound',
                                                                           'propext'],
 'Solidity.Backend.InternalFlow.StructuredChecks.changed_marker_not_protected': ['Classical.choice',
                                                                                 'Quot.sound',
                                                                                 'propext'],
 'Solidity.Backend.InternalFlow.StructuredChecks.complete_values': ['Classical.choice',
                                                                    'Quot.sound',
                                                                    'propext'],
 'Solidity.Backend.InternalFlow.StructuredChecks.existing_guard_unchanged': ['propext'],
 'Solidity.Backend.InternalFlow.StructuredChecks.false_branch': ['Classical.choice',
                                                                 'Quot.sound',
                                                                 'propext'],
 'Solidity.Backend.InternalFlow.StructuredChecks.framed': ['Classical.choice',
                                                           'Quot.sound',
                                                           'propext'],
 'Solidity.Backend.InternalFlow.StructuredChecks.old_contents': ['Classical.choice',
                                                                 'Quot.sound',
                                                                 'propext'],
 'Solidity.Backend.InternalFlow.StructuredChecks.wrong_observations': ['Classical.choice',
                                                                       'Quot.sound',
                                                                       'propext']}
# Additive C22 consumers; every earlier exact set remains unchanged.
PINS.update({'Solidity.Backend.InternalFlow.StructuredChecks.call_arguments': ['Classical.choice',
                                                                   'Quot.sound',
                                                                   'propext'],
 'Solidity.Backend.InternalFlow.structured_call_frame': ['Classical.choice',
                                                         'Quot.sound',
                                                         'propext'],
 'Solidity.Backend.InternalFlow.StructuredChecks.actual_call': ['Classical.choice',
                                                                'Quot.sound',
                                                                'propext'],
 'Solidity.Backend.InternalFlow.StructuredChecks.call_framed': ['Classical.choice',
                                                                'Quot.sound',
                                                                'propext'],
 'Solidity.Backend.InternalFlow.StructuredChecks.call_observations': ['Classical.choice',
                                                                      'Quot.sound',
                                                                      'propext'],
 'Solidity.Backend.InternalFlow.StructuredChecks.wrong_call_unwind': ['Classical.choice',
                                                                      'Quot.sound',
                                                                      'propext']})

log = Path(sys.argv[1]).read_text()
reports = re.findall(r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)", log)
actual = {n: sorted(a.strip() for a in names.split(',') if a.strip()) for n, names in reports}
assert len(actual) == len(reports), "duplicate axiom report"
assert actual == PINS, "missing, extra or changed axiom report"
assert 'error:' not in log and 'error(' not in log, "Lean diagnostics contain an error"
print(json.dumps({"status": "pass", "reports": len(reports)}, sort_keys=True))
