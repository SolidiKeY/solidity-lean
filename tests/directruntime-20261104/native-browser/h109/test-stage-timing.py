"""Guard cumulative slow-library deadlines with synthetic clock observations only."""
import importlib.util
from pathlib import Path
import unittest

spec=importlib.util.spec_from_file_location("stage",Path(__file__).with_name("stage-timing.py"))
m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
BOOT="11111111-1111-1111-1111-111111111111"


def sample(t):return {"bootId":BOOT,"monotonicBeforeNs":t,"boottimeNs":t,"monotonicAfterNs":t}


def fixture(step=1_000_000_000,context="lane-end"):
    return {"context":context,"checks":[{"target":target,"start":sample(i*step),"end":sample(i*step+1),"exitCode":0,"cachedVerdict":False} for i,target in enumerate(m.TARGETS)]}


class TimingControls(unittest.TestCase):
    def test_complete_positive_is_not_authenticated_execution(self):
        result=m.assess(fixture())
        self.assertEqual(result["targetCount"],16)
        self.assertIn("Solidity.Examples.Tactics.OpenLoops.RowsNine",m.TARGETS)
        self.assertTrue(result["timingEligibleByDeclaredPolicy"])
        for field in ("contextAuthenticated","executionAuthenticated","resourcesAuthenticated","cleanupAuthenticated","workerExecutionAccepted"):
            self.assertIs(result[field],False)

    def test_zero_exit_small_file_times_cannot_hide_cumulative_gap_overrun(self):
        record=fixture(step=40_000_000_000)
        result=m.assess(record)
        self.assertFalse(result["timingEligibleByDeclaredPolicy"])
        self.assertIn("whole-library clock mismatch or deadline",result["failures"])
        self.assertTrue(all(row["elapsedUpperNs"]==1 for row in result["intervals"]))

    def test_ci600_is_whole_library_not_per_target_or_local(self):
        local=fixture(step=30_000_000_000)
        self.assertFalse(m.assess(local)["timingEligibleByDeclaredPolicy"])
        local["context"]="ci-slow-library"
        result=m.assess(local);self.assertTrue(result["timingEligibleByDeclaredPolicy"])
        self.assertEqual(result["declaredBudgetNs"],600_000_000_000)
        self.assertFalse(result["contextAuthenticated"])
        self.assertFalse(m.assess(fixture(step=40_000_000_000,context="ci-slow-library"))["timingEligibleByDeclaredPolicy"])

    def test_exact_deadline_and_capture_uncertainty_expire(self):
        record=fixture();record["checks"][-1]["end"]=sample(300_000_000_000)
        self.assertFalse(m.assess(record)["timingEligibleByDeclaredPolicy"])
        record=fixture()
        record["checks"][0]["start"]={"bootId":BOOT,"monotonicBeforeNs":0,"boottimeNs":1,"monotonicAfterNs":2}
        record["checks"][0]["end"]=sample(10)
        record["checks"][-1]["end"]={"bootId":BOOT,"monotonicBeforeNs":299_999_999_999,"boottimeNs":300_000_000_000,"monotonicAfterNs":300_000_000_001}
        self.assertFalse(m.assess(record)["timingEligibleByDeclaredPolicy"])

    def test_wrong_denominator_reorder_cached_and_bool_exit_refused(self):
        for variant in ("missing","order","cached","exit"):
            record=fixture()
            if variant=="missing":record["checks"].pop()
            elif variant=="order":record["checks"].reverse()
            elif variant=="cached":record["checks"][0]["cachedVerdict"]=True
            else:record["checks"][0]["exitCode"]=True
            with self.subTest(variant=variant),self.assertRaises(ValueError):m.assess(record)

    def test_nonzero_and_clock_mismatch_never_pass(self):
        record=fixture();record["checks"][0]["exitCode"]=1
        self.assertFalse(m.assess(record)["timingEligibleByDeclaredPolicy"])
        record=fixture();record["checks"][3]["end"]["boottimeNs"]+=1
        self.assertFalse(m.assess(record)["timingEligibleByDeclaredPolicy"])
        record=fixture();record["checks"][2]["start"]["bootId"]="22222222-2222-2222-2222-222222222222"
        with self.assertRaises(m.clock.ClockError):m.assess(record)

    def test_no_budget_override_or_unknown_context(self):
        for context in ("ci","local600","unknown"):
            record=fixture();record["context"]=context
            with self.assertRaises(ValueError):m.assess(record)
        record=fixture();record["budgetNs"]=10**30
        with self.assertRaises(ValueError):m.assess(record)


if __name__=="__main__":unittest.main()
