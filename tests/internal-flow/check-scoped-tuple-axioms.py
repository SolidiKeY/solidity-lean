#!/usr/bin/env python3
"""Guard actual unmodified builtin reports for the scoped tuple consumer.
Run on the separately checked import query; it does not replace kernel checking
or the unchanged original542-report fixture inventory.
"""
import json
from pathlib import Path
import re
import sys
NAMES = ['Solidity.Backend.InternalFlow.TupleCalls.Scoped.scoped_tuple_expansion', 'Solidity.Backend.InternalFlow.TupleCalls.Scoped.statement', 'Solidity.Backend.InternalFlow.TupleCalls.Scoped.program_statement_endpoint', 'Solidity.Backend.InternalFlow.TupleCallChecks.Composed.ScopedDiscard.source', 'Solidity.Backend.InternalFlow.TupleCallChecks.Composed.ScopedDiscard.full_source', 'Solidity.Backend.InternalFlow.TupleCallChecks.Composed.ScopedDiscard.expanded_source', 'Solidity.Backend.InternalFlow.TupleCallChecks.Composed.ScopedDiscard.fields', 'Solidity.Backend.InternalFlow.TupleCallChecks.Composed.ScopedDiscard.target', 'Solidity.Backend.InternalFlow.TupleCallChecks.Composed.ScopedDiscard.full_target', 'Solidity.Backend.InternalFlow.TupleCallChecks.Composed.ScopedDiscard.actual_extension', 'Solidity.Backend.InternalFlow.TupleCallChecks.Composed.ScopedDiscard.wrong_caller', 'Solidity.Backend.InternalFlow.TupleCallChecks.Composed.ScopedDiscard.private_does_not_escape', 'Solidity.Backend.InternalFlow.TupleCallChecks.Composed.ScopedDiscard.wrong_contents', 'Solidity.Backend.InternalFlow.TupleCallChecks.Composed.ScopedDiscard.wrong_cost', 'Solidity.Backend.InternalFlow.TupleCallChecks.Composed.ScopedDiscard.bare_failure']
PATTERN = r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)"
def check(text):
    if re.search(r"(?:^|\n).*?(?:error:|error\(|sorryAx)", text):
        raise ValueError("diagnostic or untrusted axiom in builtin audit")
    reports = [(n, sorted(x.strip() for x in a.split(',') if x.strip()))
               for n, a in re.findall(PATTERN, text)]
    expected = [(n, ['Classical.choice', 'Quot.sound', 'propext']) for n in NAMES]
    if reports != expected:
        raise ValueError("missing, reordered, duplicate or changed scoped axiom report")
    return len(reports)
if __name__ == '__main__':
    try:
        count = check(Path(sys.argv[1]).read_text())
    except (ValueError, OSError, IndexError) as error:
        print(str(error), file=sys.stderr)
        sys.exit(1)
    print(json.dumps({'status': 'pass', 'actual_builtin_reports': count}))
