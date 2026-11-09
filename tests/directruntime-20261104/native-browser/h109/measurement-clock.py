"""Guard H127 rounded-time and zero-exit deadline-overrun regressions.

Linux clock observation/arithmetic only. This does not execute a worker, grant
an execution budget, authenticate CI, or issue a measurement/cleanup verdict.
The future controller must enforce the returned deadline independently of exit.
"""
import re
import time
from pathlib import Path


class ClockError(RuntimeError):
    pass


def boot_id():
    value = Path('/proc/sys/kernel/random/boot_id').read_text().strip()
    if not re.fullmatch(r'[0-9a-f]{8}(?:-[0-9a-f]{4}){3}-[0-9a-f]{12}', value):
        raise ClockError('unavailable boot identity')
    return value


def validate(sample):
    if not isinstance(sample, dict) or set(sample) != {'bootId', 'monotonicBeforeNs', 'boottimeNs', 'monotonicAfterNs'}:
        raise ClockError('unknown clock sample schema')
    if not isinstance(sample['bootId'], str) or not re.fullmatch(r'[0-9a-f]{8}(?:-[0-9a-f]{4}){3}-[0-9a-f]{12}', sample['bootId']):
        raise ClockError('invalid boot identity')
    for field in ['monotonicBeforeNs', 'boottimeNs', 'monotonicAfterNs']:
        if type(sample[field]) is not int or sample[field] < 0:
            raise ClockError('clock values must be nonnegative integer nanoseconds')
    if sample['monotonicAfterNs'] < sample['monotonicBeforeNs']:
        raise ClockError('monotonic clock reversed during capture')


def capture():
    """Bracket BOOTTIME with MONOTONIC reads; do not guess an error tolerance."""
    origin = boot_id()
    try:
        before = time.monotonic_ns()
        boot = time.clock_gettime_ns(time.CLOCK_BOOTTIME)
        after = time.monotonic_ns()
    except (AttributeError, OSError) as error:
        raise ClockError('CLOCK_BOOTTIME is required; no fallback value') from error
    if boot_id() != origin:
        raise ClockError('boot identity changed during capture')
    sample = {'bootId': origin, 'monotonicBeforeNs': before,
              'boottimeNs': boot, 'monotonicAfterNs': after}
    validate(sample)
    return sample


def compare(start, end, approved_budget_ns):
    """Conservative elapsed bounds; this function does not approve the budget.

    The start sample belongs immediately before worker launch; the end belongs
    after exit. Count the capture brackets toward the budget. BOOTTIME elapsed
    must fall within the MONOTONIC elapsed interval; observable disagreement outside the capture bounds is
    ineligible, not an invented adjustment. Consistency cannot attest absence of
    every short suspension. Equality at the deadline expires it.
    """
    validate(start)
    validate(end)
    if type(approved_budget_ns) is not int or approved_budget_ns <= 0:
        raise ClockError('requires an externally approved positive ns budget')
    if start['bootId'] != end['bootId']:
        raise ClockError('samples cross a boot boundary')
    if end['monotonicBeforeNs'] < start['monotonicAfterNs'] or end['boottimeNs'] < start['boottimeNs']:
        raise ClockError('samples reversed or overlapping')
    lower = end['monotonicBeforeNs'] - start['monotonicAfterNs']
    upper = end['monotonicAfterNs'] - start['monotonicBeforeNs']
    boot_elapsed = end['boottimeNs'] - start['boottimeNs']
    consistent = lower <= boot_elapsed <= upper
    expired = upper >= approved_budget_ns
    return {'elapsedLowerNs': lower, 'elapsedUpperNs': upper,
            'boottimeElapsedNs': boot_elapsed, 'clockConsistent': consistent,
            'approvedBudgetNs': approved_budget_ns,
            'deadlineMonotonicNs': start['monotonicBeforeNs'] + approved_budget_ns,
            'expired': expired, 'stopRequired': expired or not consistent,
            'remainingNs': max(0, approved_budget_ns-upper) if consistent else 0,
            'timingEligible': consistent and not expired,
            'boundary': 'Timing arithmetic only; not worker success, CI authorization or verified cleanup.'}
