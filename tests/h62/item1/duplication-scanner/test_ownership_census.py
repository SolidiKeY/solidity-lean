"""Guard stale scope labels, dirty blobs and overlapping ownership claims."""
import importlib.util
from pathlib import Path
import tempfile
import subprocess
import unittest
ROOT=Path(__file__).resolve().parents[4]
spec=importlib.util.spec_from_file_location("ownership",ROOT/"scripts/h62/item1/duplication-scanner/ownership_census.py")
owner=importlib.util.module_from_spec(spec);spec.loader.exec_module(owner)


class OwnershipControls(unittest.TestCase):
    scope={"exclusive_files":["tools/exclusive.py"],"new_file_scope":["tools/**"]}

    def test_pattern_without_provenance_is_not_ownership(self):
        r=owner.classify("tools/foreign.py",True,self.scope,[])
        self.assertEqual(r["owner"],"unknown")
        self.assertIn("existing-owner-review",r["allocation_status"])

    def test_git_provenance_outside_allocation_is_not_authority(self):
        r=owner.classify("Solidity/Source/Producer.lean",True,self.scope,["member"])
        self.assertEqual(r["owner"],"unknown")
        self.assertEqual(r["allocation_status"],"outside-cleanup-allocation-read-only")

    def test_exclusive_and_allocated_member_paths_are_distinct(self):
        self.assertEqual(owner.classify("tools/exclusive.py",True,self.scope,[])["allocation_status"],"authenticated-cleanup-exclusive")
        self.assertEqual(owner.classify("tools/member.py",True,self.scope,["member"])["allocation_status"],"cleanup-allocation-and-member-git-provenance")

    def test_dirty_blob_or_conflicting_claims_remain_review(self):
        for clean,claims in [(False,["member"]),(True,["one","two"])]:
            r=owner.classify("tools/member.py",clean,self.scope,claims)
            self.assertEqual(r["owner"],"unknown")

    def test_path_escape_rejected(self):
        for path in ("/tools/exclusive.py","tools/../exclusive.py"):
            with self.assertRaises(ValueError):owner.classify(path,True,self.scope,[])

    def test_fabricated_authority_is_rejected(self):
        with tempfile.TemporaryDirectory() as d:
            p=Path(d);(p/"manifest.json").write_text('{"members":{}}')
            with self.assertRaisesRegex(ValueError,"unauthenticated"):
                owner.load_authority(p)

    def test_clean_committed_post_member_mutation_needs_new_authority(self):
        with tempfile.TemporaryDirectory() as directory:
            root=Path(directory)
            def git(*args):return subprocess.check_output(["git",*args],cwd=root,stderr=subprocess.DEVNULL).decode().strip()
            git("init","-q");git("config","user.name","fixture");git("config","user.email","fixture@example.invalid")
            (root/"tools").mkdir();source=root/"tools/member.py";source.write_text("first\n")
            git("add",".");git("commit","-qm","member source")
            member=git("rev-parse","HEAD");old=owner.tree_blobs(root,member)
            source.write_text("changed by later commit\n");git("add",".");git("commit","-qm","later clean mutation")
            current=owner.tree_blobs(root,"HEAD");self.assertEqual(git("status","--porcelain"),"")
            path="tools/member.py";claims=["member"]
            bound=owner.blob_provenance(path,current[path],claims,{"member":old},{})
            self.assertFalse(bound)
            result=owner.classify(path,True,self.scope,claims,bound)
            self.assertEqual(result["allocation_status"],"post-member-blob-owner-review")
            self.assertEqual(result["owner"],"unknown")
            self.assertTrue(owner.blob_provenance(path,current[path],claims,{"member":old},current))

    def test_authenticated_later_blob_cannot_expand_allocation(self):
        path="Solidity/Source/Producer.lean";claims=["member"]
        bound=owner.blob_provenance(path,"new",claims,{"member":{path:"old"}},{path:"new"})
        self.assertTrue(bound)
        self.assertEqual(owner.classify(path,True,self.scope,claims,bound)["allocation_status"],"outside-cleanup-allocation-read-only")

    def test_untracked_matching_pattern_is_not_owned(self):
        result=owner.classify("tools/member.py",True,self.scope,["member"],True,False)
        self.assertEqual(result["owner"],"unknown")
        self.assertEqual(result["allocation_status"],"untracked-or-ignored-owner-review")

    def test_nested_git_sources_are_not_silently_omitted(self):
        with tempfile.TemporaryDirectory() as directory:
            root=Path(directory)
            subprocess.run(["git","init","-q",str(root)],check=True)
            nested=root/"tests/nested";nested.mkdir(parents=True)
            subprocess.run(["git","init","-q",str(nested)],check=True)
            (nested/"Fixture.lean").write_text("theorem fixture : True := by trivial\n")
            git_other=subprocess.check_output(["git","ls-files","--others","--exclude-standard"],cwd=root).decode()
            self.assertNotIn("Fixture.lean",git_other)
            selected,errors=owner.scanner_inputs(root)
            self.assertIn("tests/nested/Fixture.lean",selected)
            self.assertEqual(errors,[])

    def test_foreign_allocation_hints_never_transfer_ownership(self):
        outside=owner.classify("Solidity/Source/Producer.lean",True,self.scope,["member"],True,True,True)
        self.assertEqual(outside["allocation_status"],"foreign-chain-allocation-read-only")
        self.assertEqual(outside["owner"],"unknown")
        conflicting=owner.classify("tools/exclusive.py",True,self.scope,[],True,True,True)
        self.assertEqual(conflicting["allocation_status"],"conflicting-authenticated-allocations-owner-review")
        self.assertEqual(conflicting["owner"],"unknown")


if __name__=="__main__":unittest.main()
