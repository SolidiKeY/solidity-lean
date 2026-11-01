#!/usr/bin/env python3
"""Guard actual unmodified builtin reports for the captured caller-frame consumer.
Run on the separately checked import query; it does not replace kernel checking
or the unchanged original542-report fixture inventory.
"""
import json
from pathlib import Path
import re
import sys
NAMES = ['Solidity.Backend.InternalFlow.CallerFrame.read_thin', 'Solidity.Backend.InternalFlow.CallerFrame.export_environment', 'Solidity.Backend.InternalFlow.CallerFrame.call_environment', 'Solidity.Backend.InternalFlow.CallerFrame.single_call_environment', 'Solidity.Backend.InternalFlow.CallerFrame.single_call_alias', 'Solidity.Backend.InternalFlow.CallerFrame.selected_target', 'Solidity.Backend.InternalFlow.CallerFrame.overlapping_destination', 'Solidity.Backend.InternalFlow.DispatchChecks.ProtectedCaller.separated', 'Solidity.Backend.InternalFlow.DispatchChecks.ProtectedCaller.complete_caller_frame', 'Solidity.Backend.InternalFlow.DispatchChecks.ProtectedCaller.wrong_destination', 'Solidity.Backend.InternalFlow.DispatchChecks.ProtectedCaller.full_frame_changes', 'Solidity.Backend.InternalFlow.DispatchChecks.ProtectedCaller.no_heap_frame', 'Solidity.Backend.InternalFlow.DispatchChecks.ProtectedCaller.fallback_no_success', 'Solidity.Backend.InternalFlow.DispatchChecks.ProtectedCaller.protected_alias_id', 'Solidity.Backend.InternalFlow.DispatchChecks.ProtectedCaller.wrong_private_escape', 'Solidity.Backend.InternalFlow.DispatchChecks.ProtectedCaller.protected_target']
PINS = {'Solidity.Backend.InternalFlow.CallerFrame.read_thin': ['propext'], 'Solidity.Backend.InternalFlow.CallerFrame.export_environment': ['propext'], 'Solidity.Backend.InternalFlow.CallerFrame.call_environment': ['Classical.choice', 'Quot.sound', 'propext'], 'Solidity.Backend.InternalFlow.CallerFrame.single_call_environment': ['Classical.choice', 'Quot.sound', 'propext'], 'Solidity.Backend.InternalFlow.CallerFrame.single_call_alias': ['Classical.choice', 'Quot.sound', 'propext'], 'Solidity.Backend.InternalFlow.CallerFrame.selected_target': ['Classical.choice', 'Quot.sound', 'propext'], 'Solidity.Backend.InternalFlow.CallerFrame.overlapping_destination': ['propext'], 'Solidity.Backend.InternalFlow.DispatchChecks.ProtectedCaller.separated': ['Quot.sound', 'propext'], 'Solidity.Backend.InternalFlow.DispatchChecks.ProtectedCaller.complete_caller_frame': ['Classical.choice', 'Quot.sound', 'propext'], 'Solidity.Backend.InternalFlow.DispatchChecks.ProtectedCaller.wrong_destination': ['propext'], 'Solidity.Backend.InternalFlow.DispatchChecks.ProtectedCaller.full_frame_changes': ['Classical.choice', 'Quot.sound', 'propext'], 'Solidity.Backend.InternalFlow.DispatchChecks.ProtectedCaller.no_heap_frame': ['Classical.choice', 'Quot.sound', 'propext'], 'Solidity.Backend.InternalFlow.DispatchChecks.ProtectedCaller.fallback_no_success': ['Classical.choice', 'Quot.sound', 'propext'], 'Solidity.Backend.InternalFlow.DispatchChecks.ProtectedCaller.protected_alias_id': ['Classical.choice', 'Quot.sound', 'propext'], 'Solidity.Backend.InternalFlow.DispatchChecks.ProtectedCaller.wrong_private_escape': ['Classical.choice', 'Quot.sound', 'propext'], 'Solidity.Backend.InternalFlow.DispatchChecks.ProtectedCaller.protected_target': ['Classical.choice', 'Quot.sound', 'propext']}
PATTERN = r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)"
def check(text):
    if re.search(r"(?:^|\n).*?(?:error:|error\(|sorryAx)", text):
        raise ValueError("diagnostic or untrusted axiom in builtin audit")
    reports = [(n, sorted(x.strip() for x in a.split(',') if x.strip()))
               for n, a in re.findall(PATTERN, text)]
    expected = [(n, PINS[n]) for n in NAMES]
    if reports != expected:
        raise ValueError("missing, reordered, duplicate or changed caller-frame axiom report")
    return len(reports)
if __name__ == '__main__':
    try:
        count = check(Path(sys.argv[1]).read_text())
    except (ValueError, OSError, IndexError) as error:
        print(str(error), file=sys.stderr)
        sys.exit(1)
    print(json.dumps({'status': 'pass', 'actual_builtin_reports': count}))
