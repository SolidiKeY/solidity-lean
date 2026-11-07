#!/usr/bin/env python3
import unittest
from resource_accounting import account
G=1024**3


def stat(inactive,active):return {'inactive_file':inactive,'active_file':active}


class ResourceTests(unittest.TestCase):
    def test_reclaimable_cache_does_not_consume_other_reserve(self):
        r=account(5*G,G,stat(3*G,G),stat(0,0))
        self.assertEqual(r['parent_other_raw'],4*G)
        self.assertEqual(r['parent_other'],0)
        self.assertGreater(r['parent_other_raw']+12*G+G,16*G)
        self.assertLessEqual(r['parent_other']+12*G+G,16*G)

    def test_runtime_cache_not_subtracted_from_others_twice(self):
        r=account(8*G,4*G,stat(2*G,G),stat(G,G))
        self.assertEqual(r['parent_non_reclaimable'],5*G)
        self.assertEqual(r['runtime_non_reclaimable'],2*G)
        self.assertEqual(r['parent_other'],3*G)

    def test_actual_noncache_pressure_still_refuses(self):
        r=account(7*G,G,stat(G,0),stat(0,0))
        self.assertEqual(r['parent_other'],5*G)
        self.assertGreater(r['parent_other']+12*G+G,16*G)

    def test_invalid_and_nonatomic_samples(self):
        for stats in [{},stat(-1,0),stat(True,0)]:
            with self.assertRaises((KeyError,ValueError)):
                account(G,0,stats,stat(0,0))
        r=account(10,0,stat(8,8),stat(0,0))
        self.assertEqual(r['parent_other'],0)
        self.assertEqual(r['parent_reclaimable_file'],16)


if __name__=='__main__':unittest.main()
