#!/usr/bin/env python3
import contextlib
import importlib.util
import io
import os
import json
import subprocess
import hashlib
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

SCRIPT = Path(__file__).resolve().parents[4] / "scripts/h62/item1/pin-fragments/census.py"
spec = importlib.util.spec_from_file_location("census", SCRIPT)
census = importlib.util.module_from_spec(spec)
spec.loader.exec_module(census)

class CensusTests(unittest.TestCase):
    def run_fixture(self, fragment, inventory, untracked=b""):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            file = root / "scripts/g07-axiom-pins.d/Solidity/F.json"
            file.parent.mkdir(parents=True)
            file.write_text("{}")
            def git(*args):
                return subprocess.run(["git", *args], cwd=root, check=True, capture_output=True).stdout.decode().strip()
            git("init", "-q"); git("config", "user.email", "fixture@example.invalid"); git("config", "user.name", "fixture")
            git("add", "."); git("commit", "-qm", "seed")
            (root / "scripts/hygiene").mkdir()
            (root / "scripts/hygiene/allow.json").write_text(json.dumps({"seed": git("rev-parse", "HEAD")}))
            file.write_text(fragment)
            (root / census.INVENTORY).write_text(inventory)
            tracked = b"scripts/g07-axiom-pins.d/Solidity/F.json\0"
            output = io.StringIO()
            with patch.object(census, "ROOT", root), patch.object(census.subprocess, "check_output", side_effect=[tracked, untracked]), contextlib.redirect_stdout(output):
                code = census.main()
            return code, json.loads(output.getvalue())

    def test_matching_and_duplicate_key(self):
        key = "Solidity/F.lean:x"
        good = json.dumps({key: []})
        code, result = self.run_fixture(good, good)
        self.assertEqual(code, 0)
        self.assertEqual(result["fragment_pins"], 1)
        duplicate = "{" + json.dumps(key) + ":[]," + json.dumps(key) + ":[\"propext\"]}"
        code, result = self.run_fixture(duplicate, json.dumps({key: ["propext"]}))
        self.assertEqual(code, 1)
        self.assertTrue(any("duplicate key" in e for e in result["errors"]))

    def test_mismatch_empty_name_and_untracked(self):
        code, result = self.run_fixture(json.dumps({"Solidity/F.lean:": []}), json.dumps({"Solidity/F.lean:x": []}), b"scripts/g07-axiom-pins.d/extra.json\0")
        self.assertEqual(code, 1)
        self.assertEqual(result["inventory_only_keys"], ["Solidity/F.lean:x"])
        self.assertEqual(result["fragments_only_keys"], ["Solidity/F.lean:"])
        self.assertEqual(len(result["untracked_fragments"]), 1)
        self.assertTrue(any("wrong fragment" in e for e in result["errors"]))

    def test_different_values_and_invalid_inventory(self):
        key = "Solidity/F.lean:x"
        code, result = self.run_fixture(json.dumps({key: []}), json.dumps({key: ["propext"]}))
        self.assertEqual(code, 1)
        self.assertEqual(result["different_value_keys"], [key])
        code, result = self.run_fixture(json.dumps({key: []}), "{")
        self.assertEqual(code, 1)
        self.assertIn("fatal", result)
        duplicate = "{" + json.dumps(key) + ":[]," + json.dumps(key) + ":[]}" 
        code, result = self.run_fixture(json.dumps({key: []}), duplicate)
        self.assertEqual(code, 1)
        self.assertTrue(any("duplicate inventory key" in e for e in result["errors"]))



FRAGMENTS_SCRIPT = SCRIPT.parents[3] / "coord-tools/fragments.py"
fspec = importlib.util.spec_from_file_location("fragments", FRAGMENTS_SCRIPT)
fragments = importlib.util.module_from_spec(fspec)
fspec.loader.exec_module(fragments)
LEGACY = "scripts/g07-axiom-pins.d/Solidity/F.json"
KEY = "Solidity/F.lean:x"
NEW_KEY = "Solidity/Δ.lean:new"
NEW_PATH = "scripts/axiom-pins/" + hashlib.sha256("Solidity/Δ.lean".encode()).hexdigest() + ".json"

class StorageIntegration(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.root = Path(self.tmp.name)
        self.old = Path.cwd()
        os.chdir(self.root)
        self.git("init", "-q")
        self.git("config", "user.name", "fixture")
        self.git("config", "user.email", "fixture@example.invalid")
        self.raw = ' { "Solidity/F.lean:x" : [] }\n'
        self.put(LEGACY, self.raw)
        self.git("add", "."); self.git("commit", "-qm", "immutable seed")
        self.put("scripts/hygiene/allow.json", json.dumps({"seed": self.git("rev-parse", "HEAD")}))
        self.put(census.INVENTORY, json.dumps({KEY: []}) + "\n")
        self.git("add", "."); self.git("commit", "-qm", "base")
    def tearDown(self):
        os.chdir(self.old); self.tmp.cleanup()
    def git(self, *args):
        return subprocess.run(["git", *args], capture_output=True, text=True, check=True).stdout.strip()
    def put(self, path, text):
        p = self.root / path; p.parent.mkdir(parents=True, exist_ok=True); p.write_text(text)
    def census(self):
        output = io.StringIO()
        with patch.object(census, "ROOT", self.root), contextlib.redirect_stdout(output): code = census.main()
        return code, json.loads(output.getvalue())
    def adopt(self, before, after, own=False):
        notes = []
        ok = fragments.apply_json(fragments.Tree(), census.INVENTORY, fragments.PIN_FRAGMENT_ROOTS[0],
                                  json.dumps(before), json.dumps(after), "fixture", notes, own)
        return ok, notes
    def test_mixed_union_census_generation_and_raw_stability(self):
        self.assertTrue(self.adopt({KEY:[]},{KEY:[],NEW_KEY:["propext"]})[0])
        self.assertTrue((self.root / NEW_PATH).is_file())
        with contextlib.redirect_stdout(io.StringIO()): self.assertEqual(fragments.write_mode(False, False),0)
        combined = (self.root / census.INVENTORY).read_bytes()
        expected = {KEY:[], NEW_KEY:["propext"]}
        self.assertEqual(json.loads(combined),expected)
        self.assertEqual(combined, fragments.canon({"x":expected},compact=True)["x"].encode())
        self.assertEqual((self.root / LEGACY).read_text(), self.raw)
        self.git("add", ".")
        code, report = self.census()
        self.assertEqual(code,0,report)
        self.assertEqual(report["tracked_fragments"],2)
        with contextlib.redirect_stdout(io.StringIO()): self.assertEqual(fragments.write_mode(True,False),0)
        self.assertEqual((self.root / census.INVENTORY).read_bytes(),combined)
    def test_missing_and_duplicate_across_roots(self):
        self.put(census.INVENTORY,json.dumps({KEY:[],NEW_KEY:[]}))
        code, report = self.census()
        self.assertEqual(code,1); self.assertEqual(report["inventory_only_keys"],[NEW_KEY])
        self.put(NEW_PATH,json.dumps({KEY:[]})); self.git("add", ".")
        code, report = self.census()
        self.assertEqual(code,1)
        self.assertTrue(any("duplicate across fragments" in e for e in report["errors"]))
    def test_invalid_and_wrong_placement_census(self):
        for value in (["sorryAx"],None,{},[3]):
            self.put(LEGACY,json.dumps({KEY:value}))
            code, report = self.census()
            self.assertEqual(code,1,report)
        self.put(LEGACY,json.dumps({"Solidity/Other.lean:x":[]}))
        code, report = self.census()
        self.assertEqual(code,1)
        self.assertTrue(any("wrong fragment" in e for e in report["errors"]))
    def test_direct_combined_only_change_is_refused(self):
        direct = json.dumps({KEY:[],NEW_KEY:[]}) + "\n"
        self.put(census.INVENTORY,direct)
        with contextlib.redirect_stdout(io.StringIO()): self.assertEqual(fragments.write_mode(False,False),1)
        self.assertEqual((self.root / census.INVENTORY).read_text(),direct)
        self.assertFalse((self.root / NEW_PATH).exists())
    def test_adoption_rejects_invalid_lists_and_duplicate_before_mutation(self):
        for bad in ({KEY:[],NEW_KEY:["sorryAx"]}, {KEY:[],NEW_KEY:None}, []):
            ok, _ = self.adopt({KEY:[]},bad)
            self.assertFalse(ok)
            self.assertEqual((self.root / LEGACY).read_text(),self.raw)
            self.assertFalse((self.root / NEW_PATH).exists())
        notes=[]
        self.assertFalse(fragments.apply_json(fragments.Tree(),census.INVENTORY,fragments.PIN_FRAGMENT_ROOTS[0],
                         '{}','{"Solidity/F.lean:x":[],"Solidity/F.lean:x":[]}',"fixture",notes,False))
    def test_conflict_prevents_pending_writes_and_own_fragment_wins(self):
        self.put(LEGACY,json.dumps({KEY:["Quot.sound"]}) + "\n")
        before = (self.root / LEGACY).read_bytes()
        ok, notes = self.adopt({KEY:[]},{NEW_KEY:[]})
        self.assertFalse(ok)
        self.assertTrue(any("removed" in n and "changed on the other side" in n for n in notes))
        self.assertEqual((self.root / LEGACY).read_bytes(),before)
        self.assertFalse((self.root / NEW_PATH).exists())
        self.assertTrue(self.adopt({KEY:[]},{KEY:["propext"]},own=True)[0])
        self.assertEqual((self.root / LEGACY).read_bytes(),before)
    def test_verified_removal_and_malformed_file_preflight(self):
        self.put("scripts/axiom-pins/unrecognized.json","{")
        ok, _ = self.adopt({KEY:[]},{})
        self.assertFalse(ok)
        self.assertEqual((self.root / LEGACY).read_text(),self.raw)
        (self.root / "scripts/axiom-pins/unrecognized.json").unlink()
        self.assertTrue(self.adopt({KEY:[]},{})[0])
        self.assertFalse((self.root / LEGACY).exists())
    def test_resolve_places_adopted_direct_edit_under_hash_and_stages_it(self):
        self.git("checkout","-qb","side")
        self.put(census.INVENTORY,json.dumps({KEY:[],NEW_KEY:[]}))
        self.git("add", "."); self.git("commit","-qm","direct side edit")
        self.git("checkout","-qb","ours","HEAD~1")
        self.put("unrelated.txt","other\n"); self.git("add", "."); self.git("commit","-qm","other side")
        self.git("merge","--no-ff","side","-m","Merge side")
        with contextlib.redirect_stdout(io.StringIO()): self.assertEqual(fragments.resolve("side","ours"),0)
        self.assertEqual(json.loads((self.root / NEW_PATH).read_text()),{NEW_KEY:[]})
        self.assertIn(NEW_PATH,self.git("diff","--cached","--name-only"))
        self.assertEqual((self.root / LEGACY).read_text(),self.raw)



    def test_historical_symlink_fragment_rejected_before_adoption(self):
        (self.root / LEGACY).unlink()
        (self.root / LEGACY).symlink_to(json.dumps({KEY:[]}))
        self.git("add","."); self.git("commit","-qm","symbolic fragment")
        with self.assertRaisesRegex(fragments.Error,"nonregular fragment"):
            fragments.fragment_op(fragments.Tree("HEAD"))

    def test_resolve_leaves_conflicted_fragment_untouched(self):
        self.git("checkout","-qb","side")
        self.put(LEGACY,json.dumps({KEY:["propext"]}) + "\n")
        self.git("add","."); self.git("commit","-qm","side fragment")
        self.git("checkout","-qb","ours","HEAD~1")
        self.put(LEGACY,json.dumps({KEY:["Quot.sound"]}) + "\n")
        self.git("add","."); self.git("commit","-qm","ours fragment")
        result=subprocess.run(["git","merge","side"],capture_output=True)
        self.assertEqual(result.returncode,1)
        before=(self.root / LEGACY).read_bytes()
        with contextlib.redirect_stdout(io.StringIO()) as output:
            self.assertEqual(fragments.resolve("side","ours"),1)
        self.assertIn("fragment under",output.getvalue())
        self.assertEqual((self.root / LEGACY).read_bytes(),before)
        self.assertIn(LEGACY,self.git("diff","--name-only","--diff-filter=U"))

    def test_census_rejects_symbolic_or_file_fragment_root(self):
        path=self.root / "scripts/axiom-pins"
        path.symlink_to("g07-axiom-pins.d",target_is_directory=True)
        self.git("add",".")
        code, report=self.census()
        self.assertEqual(code,1)
        self.assertTrue(any("symbolic fragment root" in e for e in report["errors"]))
        path.unlink(); path.write_text("not a directory")
        self.git("add",".")
        code, report=self.census()
        self.assertEqual(code,1)
        self.assertTrue(any("non-directory" in e for e in report["errors"]))

    def test_resolve_fragmented_merge_base_predates_seed_policy(self):
        seed=self.git("rev-parse","HEAD~1")
        self.git("checkout","-qb","side",seed)
        self.put(census.INVENTORY,json.dumps({KEY:[],NEW_KEY:[]}))
        self.git("add","."); self.git("commit","-qm","side before policy")
        # The original branch contains the introduction of the immutable policy.
        original=self.git("for-each-ref","--format=%(refname:short)","refs/heads").splitlines()
        original=next(b for b in original if b != "side")
        self.git("checkout",original)
        result=subprocess.run(["git","merge","--no-ff","side","-m","Merge side"],capture_output=True)
        self.assertIn(result.returncode,(0,1))
        with contextlib.redirect_stdout(io.StringIO()): self.assertEqual(fragments.resolve("side","ours"),0)
        self.assertEqual(json.loads((self.root / NEW_PATH).read_text()),{NEW_KEY:[]})
        self.assertEqual((self.root / LEGACY).read_text(),self.raw)

class PolicyBoundaries(unittest.TestCase):
    def test_unchanged_hygiene_rejects_new_legacy_and_keeps_exact_size_boundaries(self):
        checker = SCRIPT.parents[3] / "hygiene/check.py"
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            def git(*args):
                return subprocess.run(["git", *args], cwd=root, capture_output=True, text=True, check=True).stdout.strip()
            def put(path, raw):
                p = root / path; p.parent.mkdir(parents=True, exist_ok=True); p.write_bytes(raw)
            def run(*args):
                return subprocess.run(["python3", "-B", str(checker), *args], cwd=root, capture_output=True, text=True)
            git("init","-q"); git("config","user.name","fixture"); git("config","user.email","fixture@example.invalid")
            put("scripts/g07-axiom-pins.json", b" " * 2938337)
            put(LEGACY,b"{}\n")
            git("add","."); git("commit","-qm","seed")
            seed = git("rev-parse","HEAD")
            git("update-ref","refs/remotes/origin/master",seed)
            seeded = run("seed","--rev",seed)
            self.assertEqual(seeded.returncode,0,seeded.stderr)
            put("scripts/hygiene/allow.json",seeded.stdout.encode())
            git("add","."); git("commit","-qm","seed policy")
            git("update-ref","refs/remotes/origin/master",git("rev-parse","HEAD"))
            def check(expected, needle=None):
                git("add","."); git("commit","-qm","boundary","--allow-empty")
                result=run(); self.assertEqual(result.returncode,expected,result.stdout+result.stderr)
                if needle: self.assertIn(needle,result.stdout+result.stderr)
            put("data/at.bin",b"x"*204800); check(0)
            put("data/at.bin",b"x"*204801); check(1,"204801 bytes over the 204800-byte")
            put("data/at.bin",b"x"*204800)
            put("scripts/g07-axiom-pins.json",b" "*2938338); check(1,"legacy exception stops at 2938337 bytes")
            put("scripts/g07-axiom-pins.json",b" "*2938337); check(0)
            put("scripts/g07-axiom-pins.d/Solidity/New.json",b"{}\n")
            check(1,"new path under legacy prefix 'scripts/g07-axiom-pins.d'")

if __name__ == "__main__": unittest.main()
