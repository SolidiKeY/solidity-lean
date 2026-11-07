"""Guard nanosecond deadlines and clock disagreement; no proof workload runs."""
import importlib.util
import pathlib
import unittest
from unittest import mock

spec = importlib.util.spec_from_file_location('clock', pathlib.Path(__file__).with_name('measurement-clock.py'))
m = importlib.util.module_from_spec(spec)
spec.loader.exec_module(m)
BOOT = '00000000-0000-4000-8000-000000000001'


def sample(a, b, c):
    return {'bootId': BOOT, 'monotonicBeforeNs': a, 'boottimeNs': b, 'monotonicAfterNs': c}


class ClockControls(unittest.TestCase):
    def test_subsecond_precision_and_capture_bounds(self):
        result = m.compare(sample(100, 104, 107), sample(180, 185, 190), 100)
        self.assertEqual((result['elapsedLowerNs'], result['elapsedUpperNs']), (73, 90))
        self.assertEqual(result['boottimeElapsedNs'], 81)
        self.assertEqual(result['remainingNs'], 10)
        self.assertTrue(result['timingEligible'])

    def test_deadline_equality_and_one_ns_overrun_fail(self):
        start = sample(100, 105, 110)
        for end in [sample(190, 200, 200), sample(191, 201, 201)]:
            result = m.compare(start, end, 100)
            self.assertTrue(result['expired'])
            self.assertFalse(result['timingEligible'])
            self.assertEqual(result['remainingNs'], 0)
        # No process-exit field can turn this arithmetic into a passing run.
        self.assertNotIn('passed', result)

    def test_suspend_or_other_clock_disagreement_fails(self):
        start = sample(100, 105, 110)
        for boot in [180, 300]:
            result = m.compare(start, sample(190, boot, 200), 1000)
            self.assertFalse(result['clockConsistent'])
            self.assertFalse(result['timingEligible'])
            self.assertTrue(result['stopRequired'])
            self.assertEqual(result['remainingNs'], 0)

    def test_missing_bool_negative_reversed_and_boot_drift_refused(self):
        start = sample(100, 105, 110)
        for bad in [{}, sample(True, 200, 210), sample(-1, 200, 210), sample(220, 200, 210)]:
            with self.assertRaises(m.ClockError):m.compare(start, bad, 1000)
        with self.assertRaises(m.ClockError):m.compare(start, sample(109, 200, 210), 1000)
        drift = sample(190, 200, 210);drift['bootId'] = '00000000-0000-4000-8000-000000000002'
        with self.assertRaises(m.ClockError):m.compare(start, drift, 1000)
        for budget in [0, -1, True, 3.14]:
            with self.assertRaises(m.ClockError):m.compare(start, sample(190, 200, 210), budget)

    def test_capture_brackets_both_clocks_and_refuses_missing_clock(self):
        with mock.patch.object(m, 'boot_id', return_value=BOOT), mock.patch.object(m.time, 'monotonic_ns', side_effect=[100, 110]), mock.patch.object(m.time, 'clock_gettime_ns', return_value=105):
            self.assertEqual(m.capture(), sample(100, 105, 110))
        with mock.patch.object(m, 'boot_id', return_value=BOOT), mock.patch.object(m.time, 'clock_gettime_ns', side_effect=OSError('clock unavailable')):
            with self.assertRaises(m.ClockError):m.capture()
        with mock.patch.object(m, 'boot_id', side_effect=[BOOT, '00000000-0000-4000-8000-000000000002']):
            with self.assertRaises(m.ClockError):m.capture()


if __name__ == '__main__':
    unittest.main()
