#!/usr/bin/env python3
"""Summarize completed immutable baseline attempts; never applies owner patches.

Per-module rounded observations and full-attempt durations are not substituted
for a successful whole-build comparison. All bulk output remains off Git.
"""
import argparse
from decimal import Decimal
import json
from pathlib import Path
import re

MODULES = ['Solidity.KeySort', 'Solidity.Yul.Builtins',
           'Solidity.SolcValidation.Dialect', 'Solidity.SolcValidation.DataLayout',
           'Solidity.SolcValidation.DataResolution',
           'Solidity.Frontend.SolcJson.IrImport',
           'Solidity.Frontend.SolcJson.IrImportControls']


def seal(evidence):
    comparison = json.loads((evidence / 'matched-full-comparison.json').read_text())
    if not comparison['comparison_is_valid_successful_full_builds']:
        if comparison['full_wall_delta_percent'] is not None:
            raise RuntimeError('failed full gates must not produce an accepted ratio')
    errors = {}
    observations = {}
    for lane in ['old', 'new']:
        rows = {}
        failures = {}
        for line in (evidence / f'matched-rss-{lane}-result.log').read_text().splitlines():
            match = re.match(r'error: ([^:]+\.lean):(\d+):(\d+): (.*)', line)
            if match:
                failures.setdefault(match[1], []).append({
                    'line': int(match[2]), 'column': int(match[3]), 'message': match[4]})
            match = re.search(r'Built ([A-Za-z0-9_.]+) \(([0-9.]+)(ms|s)\)', line)
            if match and match[1] in MODULES:
                if match[1] in rows:
                    raise RuntimeError(f'duplicate observed module {match[1]}')
                duration = Decimal(match[2]) / (1000 if match[3] == 'ms' else 1)
                rows[match[1]] = {'rounded_lake_seconds': str(duration), 'line': line}
        if set(rows) != set(MODULES):
            raise RuntimeError(f'incomplete scoped-module observations for {lane}')
        observations[lane] = rows
        errors[lane] = failures
    summary = {'attempts': comparison['attempts'],
               'accepted_full_wall_delta_percent': comparison['full_wall_delta_percent'],
               'comparison_status': comparison['status'],
               'failed_source_files': errors,
               'rounded_scoped_module_observations': observations,
               'boundary': 'Both logs are immutable pinned-BASE attempts without the H70 '
                           'partial overlays. They do not validate or reject those patches. '
                           'Per-module log durations are rounded observations, not successful '
                           'full-build timing or RSS comparisons. No source or budget is changed.'}
    (evidence / 'completed-full-evidence.json').write_text(json.dumps(summary, indent=2) + '\n')
    print(json.dumps({'status': comparison['status'],
                      'accepted_full_wall_delta_percent': comparison['full_wall_delta_percent'],
                      'failed_source_file_counts': {lane: len(rows) for lane, rows in errors.items()}}))


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--evidence', type=Path, required=True)
    seal(parser.parse_args().evidence)
