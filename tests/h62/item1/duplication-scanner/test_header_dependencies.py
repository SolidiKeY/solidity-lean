"""Guard dropped headers, guessed dependency paths, shadows and false clearance."""
import copy
import importlib.util
from pathlib import Path
import sys
import subprocess
from unittest import mock
import tempfile
import unittest

ROOT=Path(__file__).resolve().parents[4];SCRIPTS=ROOT/"scripts/h62/item1/duplication-scanner"
sys.path.insert(0,str(SCRIPTS))
try:
    spec=importlib.util.spec_from_file_location("header_deps",SCRIPTS/"header_dependencies.py")
    graph=importlib.util.module_from_spec(spec);spec.loader.exec_module(graph)
finally:sys.path.pop(0)


def node(path,dependencies=(),status="parsed-header"):
    return {"path":path,"module":graph.encoded(Path(path).with_suffix("").parts),"status":status,
            "imports":[{"module":graph.encoded(Path(dep).with_suffix("").parts),"resolution":{"status":"project-source","path":dep}} for dep in dependencies]}


def header(path="A.lean"):
    return {"path":path,"status":"parsed-header","header_prefix":"import Lean\n","is_module":False,
            "imports":[{"module":graph.encoded(["Lean"]),"importAll":False,"isExported":True,"isMeta":False,"implicit":False}],
            "diagnostics":[],"body_parsed":False,"dynamic_references_known":False}


class HeaderDependencyControls(unittest.TestCase):
    def test_frozen_original_surface_keeps_all_129_files(self):
        paths,digest=graph.frozen_targets();self.assertEqual(len(paths),129);self.assertEqual(len(set(paths)),129);self.assertEqual(len(digest),64)

    def test_declared_held_path_and_cycles_terminate(self):
        nodes=[node("A.lean",["B.lean"]),node("B.lean",["A.lean",graph.HELD]),node(graph.HELD)]
        result=graph.held_path(nodes,"A.lean")
        self.assertEqual(result["status"],"declared-path-to-held-module")
        self.assertEqual(result["path"],["A.lean","B.lean",graph.HELD])
        self.assertEqual(graph.held_path([node("A.lean",["A.lean"])],"A.lean")["status"],"no-declared-path-to-held-module")
        # Absence of a declared path is not a compilation permission or timing clearance.
        self.assertNotIn("safe_to_compile",result)

    def test_bad_or_missing_headers_remain_unknown(self):
        for nodes in ([],[node("A.lean",status="header-error")],[node("A.lean",["Missing.lean"])]):
            self.assertEqual(graph.held_path(nodes,"A.lean")["status"],"header-dependency-unknown")

    def test_missing_unsafe_and_shadowed_module_resolution(self):
        with tempfile.TemporaryDirectory() as directory:
            root=Path(directory);sdk=root/"lib/lean";sdk.mkdir(parents=True)
            (sdk/"X.olean").write_bytes(b"sdk")
            source=node("X.lean");caller=node("A.lean");caller["imports"]=[{"module":graph.encoded(["X"])},{"module":graph.encoded(["Missing"])},{"module":graph.encoded([".."]) }]
            graph.resolve([source,caller],root)
            self.assertEqual([x["resolution"]["status"] for x in caller["imports"]],["ambiguous-source-or-sdk","unresolved-module","unsafe-or-unsupported-module-name"])

    def test_quoted_dot_component_preserved_in_sdk_path(self):
        with tempfile.TemporaryDirectory() as directory:
            root=Path(directory);folder=root/"lib/lean/Foo";folder.mkdir(parents=True);(folder/"A.B.olean").write_bytes(b"sdk")
            caller=node("Caller.lean");caller["imports"]=[{"module":graph.encoded(["Foo","A.B"])}]
            graph.resolve([caller],root)
            result=caller["imports"][0]["resolution"]
            self.assertEqual(result["status"],"sdk-artifact-observed-not-loaded")
            self.assertTrue(result["path"].endswith("Foo/A.B.olean"))

    def test_source_duplicates_never_choose_a_winner(self):
        with tempfile.TemporaryDirectory() as directory:
            a=node("A.lean");b=node("B.lean");b["module"]=a["module"]
            caller=node("Caller.lean");caller["imports"]=[{"module":a["module"]}]
            graph.resolve([a,b,caller],Path(directory))
            self.assertEqual(caller["imports"][0]["resolution"]["status"],"ambiguous-source-or-sdk")

    def test_record_coverage_and_exact_header_prefix_required(self):
        inputs=[{"path":"A.lean","source":"import Lean\ndef x := 1\n"}]
        for records in ([],[header(),header()],[dict(header(),header_prefix="import Fake\n")]):
            with self.assertRaises(ValueError):graph.validate_headers([node("A.lean")],inputs,records)
        nodes=[node("A.lean")];graph.validate_headers(nodes,inputs,[header()]);self.assertEqual(nodes[0]["status"],"parsed-header")

    def test_body_or_dynamic_claims_and_hidden_failure_refused(self):
        inputs=[{"path":"A.lean","source":"import Lean\n"}]
        for mutate in (lambda r:r.update(body_parsed=True),lambda r:r.update(dynamic_references_known=True),
                       lambda r:r.update(is_module=1),lambda r:r.update(status="header-error"),
                       lambda r:r["imports"][0].update(isMeta=1)):
            record=header();mutate(record)
            with self.assertRaises(ValueError):graph.validate_headers([node("A.lean")],inputs,[record])

    def test_overlapping_source_roots_refused_independent_of_order(self):
        for roots in (("vendor/A","vendor/A/Nested"),("vendor/A/Nested","vendor/A"),("Solidity/Parts",)):
            with self.assertRaisesRegex(ValueError,"overlapping"):
                graph.source_roots({"lean_lib":[{"srcDir":r} for r in roots]})
        self.assertEqual(len(graph.source_roots({"lean_lib":[{"srcDir":"vendor/A"},{"srcDir":"vendor/A"}]})),1)

    def test_primary_root_spellings_do_not_expand_scope(self):
        for spelling in (".","./",""):
            self.assertEqual(graph.source_roots({"lean_lib":[{"srcDir":spelling}]}),[])
            roots=graph.source_roots({"lean_lib":[{"srcDir":spelling},{"srcDir":"vendor/A"}]})
            self.assertEqual(roots,[graph.PurePosixPath("vendor/A")])

    def test_nondefault_package_root_is_explicitly_unsupported(self):
        for folder in ("src","../other","/outside"):
            with self.assertRaisesRegex(ValueError,"unsupported non-default"):
                graph.source_roots({"srcDir":folder})
        for folder in (".","./",""):
            self.assertEqual(graph.source_roots({"srcDir":folder}),[])

    def git_fixture(self,root,*args):
        return subprocess.check_output(["git","-C",str(root),*args],stderr=subprocess.DEVNULL)

    def init_fixture(self,root):
        self.git_fixture(root,"init","-q")
        (root/"lakefile.toml").write_text('name = "fixture"\n')
        (root/"A.lean").write_text("def a := 0\n")
        self.git_fixture(root,"add",".")
        self.git_fixture(root,"-c","user.name=Fixture","-c","user.email=fixture@localhost","commit","-qm","base")
        return self.git_fixture(root,"rev-parse","HEAD").decode().strip()

    def test_collection_uses_captured_tree_after_ambient_head_changes(self):
        with tempfile.TemporaryDirectory() as directory:
            root=Path(directory);head=self.init_fixture(root)
            (root/"B.lean").write_text("def b := 1\n");self.git_fixture(root,"add",".")
            self.git_fixture(root,"-c","user.name=Fixture","-c","user.email=fixture@localhost","commit","-qm","later")
            with mock.patch.object(graph,"ROOT",root):nodes,_,scope=graph.collect_sources(head)
            self.assertEqual([n["path"] for n in nodes],["A.lean"])
            self.assertEqual(scope["source_head"],head)

    def test_dirty_core_configuration_is_not_promoted_to_captured_tree(self):
        with tempfile.TemporaryDirectory() as directory:
            root=Path(directory);head=self.init_fixture(root)
            (root/"lakefile.toml").write_text('name = "changed"\n')
            with mock.patch.object(graph,"ROOT",root),self.assertRaisesRegex(ValueError,"configuration differs"):
                graph.collect_sources(head)

    def test_target_identity_survives_missing_dependency_path(self):
        nodes=[{"path":"A.lean","status":"parsed-header","imports":[]}]
        rows=graph.target_records(nodes,["A.lean",graph.HELD,"Missing.lean"])
        self.assertEqual([r["target"] for r in rows],["A.lean",graph.HELD,"Missing.lean"])
        self.assertIsNone(rows[0]["path"])
        self.assertEqual(rows[1]["path"],[graph.HELD])
        self.assertEqual(rows[2]["status"],"header-dependency-unknown")
        with self.assertRaisesRegex(ValueError,"duplicate target"):
            graph.target_records(nodes,["A.lean","A.lean"])

    def test_inert_body_marker_is_a_real_refusal(self):
        with tempfile.TemporaryDirectory() as directory:
            output=Path(directory);(output/"CONTROL-MUST-NOT-EXECUTE").write_text("EXECUTED")
            with self.assertRaisesRegex(ValueError,"body was executed"):graph.verify_controls([],[],output)


if __name__=="__main__":unittest.main()
