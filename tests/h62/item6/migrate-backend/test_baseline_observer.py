import importlib.util
from pathlib import Path
import unittest

ROOT=Path(__file__).resolve().parents[4]
spec=importlib.util.spec_from_file_location('observer',ROOT/'scripts/h62/item6/migrate-backend/watch_existing_baseline.py')
observer=importlib.util.module_from_spec(spec);spec.loader.exec_module(observer)

class ObserverScopeControls(unittest.TestCase):
    def test_reused_or_zombie_root_is_not_a_valid_lineage_epoch(self):
        self.assertTrue(observer.root_epoch_ok({10:{'start_ticks':42,'state':'S'}},10,42))
        for records in ({},{10:{'start_ticks':43,'state':'S'}},{10:{'start_ticks':42,'state':'Z'}},{10:{'start_ticks':42,'state':'X'}}):
            with self.subTest(records=records): self.assertFalse(observer.root_epoch_ok(records,10,42))

    def test_unrelated_same_executable_and_cyclic_lineages_are_excluded(self):
        records={10:{'ppid':1},11:{'ppid':10},12:{'ppid':11},20:{'ppid':1},21:{'ppid':20},30:{'ppid':31},31:{'ppid':30}}
        self.assertTrue(observer.descendant(12,10,records))
        for pid in (1,20,21,30,31,999):
            with self.subTest(pid=pid): self.assertFalse(observer.descendant(pid,10,records))

if __name__=='__main__': unittest.main()
