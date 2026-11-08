import unittest
from copy import deepcopy
from indexed_roles import annotate_occurrences
class IndexedRoleTests(unittest.TestCase):
    def fixture(self):
        names=["P","fs","L","x","y","anon","anon"]
        bs=[dict(name=n,type=("x.All P" if i==5 else "y.All P" if i==6 else "data"),is_prop=i>=5) for i,n in enumerate(names)]
        return bs,dict(binders=names,configuration=[0,1],premises={5:"source-fields",6:"replacement-fields"})
    def test_same_names_have_distinct_occurrences(self):
        bs,spec=self.fixture();rows=annotate_occurrences("fixture",bs,spec)
        self.assertEqual([r["role"] for r in rows[5:]],["source-fields","replacement-fields"])
        self.assertNotEqual(rows[5]["binder_id"],rows[6]["binder_id"])
    def test_second_same_named_premise_cannot_be_omitted(self):
        bs,spec=self.fixture();del spec["premises"][6]
        with self.assertRaisesRegex(AssertionError,"Indexed logical premise"):annotate_occurrences("fixture",bs,spec)
    def test_second_same_named_premise_cannot_be_data(self):
        bs,spec=self.fixture();bs[6]["is_prop"]=False
        with self.assertRaisesRegex(AssertionError,"Indexed logical premise"):annotate_occurrences("fixture",bs,spec)
    def test_data_removal_cannot_shift_duplicate_roles(self):
        bs,spec=self.fixture();bs.pop(2)
        with self.assertRaisesRegex(AssertionError,"ordered binder census"):annotate_occurrences("fixture",bs,spec)
if __name__=="__main__":unittest.main()
