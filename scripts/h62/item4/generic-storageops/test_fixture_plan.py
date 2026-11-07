import copy
import io
import subprocess
import tarfile
import tempfile
from unittest import mock
import importlib.util
from pathlib import Path
import unittest
s=importlib.util.spec_from_file_location("plan",Path(__file__).with_name("fixture_plan.py"))
m=importlib.util.module_from_spec(s);s.loader.exec_module(m)

class PlanTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        # Classify the exact frozen source, not a subsequently edited worktree.
        # The normal classifier/acceptance commands still reject live drift.
        census=m.m.c
        archive=subprocess.check_output(
            ["git","archive",census.BASE,"--",census.FAMILY],cwd=census.ROOT)
        with tempfile.TemporaryDirectory(prefix="h62-frozen-plan-") as temp:
            root=Path(temp)
            with tarfile.open(fileobj=io.BytesIO(archive)) as tree:
                for member in tree.getmembers():
                    if not member.isfile(): continue
                    path=Path(member.name)
                    if path.is_absolute() or ".." in path.parts:
                        raise ValueError("unsafe frozen source path")
                    target=root/path
                    target.parent.mkdir(parents=True,exist_ok=True)
                    target.write_bytes(tree.extractfile(member).read())
            cls.inventory=census.census(root)
            with mock.patch.object(census,"ROOT",root), \
                 mock.patch.object(census,"census",return_value=cls.inventory):
                cls.classification=m.m.classify()
        cls.plan=m.build(cls.classification)
    def test_all_claims_and_support(self):
        m.validate(self.plan,self.classification)
        self.assertEqual(self.plan["totals"],dict(claims=1623,packets=84,private=616,public=1007))
    def test_inventory_drift_still_refused(self):
        changed=copy.deepcopy(self.inventory)
        changed["files"][0]["sha256"]="0"*64
        with mock.patch.object(m.m.c,"census",return_value=changed):
            with self.assertRaisesRegex(ValueError,"frozen inventory drift"):
                m.m.classify()
    def test_corruption_refused(self):
        for name in ("drop","duplicate","contract","fixture","equivalence"):
            with self.subTest(name=name):
                y=copy.deepcopy(self.plan)
                if name=="drop":y["cases"].pop()
                elif name=="duplicate":y["cases"].append(y["cases"][0])
                elif name=="contract":y["cases"][0]["exact_result_type"]="True"
                elif name=="fixture":next(p for p in y["packets"] if p["fixture_ids"])["fixture_ids"].pop()
                else:y["cases"][0]["equivalence"]["proved"]=True
                with self.assertRaises(ValueError):m.validate(y,self.classification)

if __name__=="__main__":unittest.main()
