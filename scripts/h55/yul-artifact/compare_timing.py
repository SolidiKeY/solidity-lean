#!/usr/bin/env python3
"""Fail closed on changed runtime conditions or any paired slowdown >10%.
Input arrays contain bounded.py run records with toolchain and executor IDs
added by the benchmark driver. This checks receipts, not proof validity.
"""
import argparse, json
from decimal import Decimal
CONDITIONS=('command','address_space_limit_bytes','reserve_bytes','lean_num_threads',
            'swap_configured','toolchain','executor','cache_state')

def compare(before,after):
    if not before or len(before) != len(after):
        raise ValueError('nonempty equally sized paired runs required')
    ratios=[]
    for left,right in zip(before,after):
        for key in CONDITIONS:
            if key not in left or key not in right or left[key] != right[key]:
                raise ValueError('missing or changed condition: '+key)
        for run in (left,right):
            if any(key not in run for key in ('exit_code','stop_reason','wall_seconds')):
                raise ValueError('missing outcome fields')
            if not isinstance(run['command'],list) or not run['command'] or any(not isinstance(arg,str) or not arg for arg in run['command']):
                raise ValueError('nonempty command arguments required')
            for key in ('toolchain','executor','cache_state'):
                if not isinstance(run[key],str) or not run[key].strip():
                    raise ValueError('nonempty identity/cache condition required: '+key)
            limit=run['address_space_limit_bytes']
            reserve=run['reserve_bytes']
            if type(limit) is not int or not 0 < limit <= 12*1024**3:
                raise ValueError('address space bound must be positive and at most 12 GiB')
            if type(reserve) is not int or reserve < 4*1024**3:
                raise ValueError('at least 4 GiB reserve required')
            if run['exit_code'] != 0 or run['stop_reason'] is not None:
                raise ValueError('unsuccessful/resource-stopped run cannot be benchmarked')
            if run['lean_num_threads'] != 1 or run['swap_configured'] is not False:
                raise ValueError('serial no-swap conditions required')
            seconds=Decimal(str(run['wall_seconds']))
            if not seconds.is_finite() or seconds <= 0: raise ValueError('invalid duration')
        ratios.append(Decimal(str(right['wall_seconds']))/Decimal(str(left['wall_seconds'])))
    stopped=any(ratio > Decimal('1.1') for ratio in ratios)
    return dict(stop=stopped,paired_ratios=[str(ratio) for ratio in ratios])

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('before'); parser.add_argument('after')
    args=parser.parse_args()
    with open(args.before) as stream: before=json.load(stream)
    with open(args.after) as stream: after=json.load(stream)
    report=compare(before,after)
    print(json.dumps(report,indent=2))
    return int(report['stop'])
if __name__ == '__main__': raise SystemExit(main())
