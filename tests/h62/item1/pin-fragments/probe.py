#!/usr/bin/env python3
"""Read-only acceptance probes for the existing G07 fragment implementation."""
import importlib.util
import json
import os
import pathlib
import subprocess
import tempfile
import unittest

ROOT = pathlib.Path(os.environ.get("PIN_FRAGMENTS_ROOT", pathlib.Path(__file__).resolve().parents[4]))
FRAGMENTS = "scripts/g07-axiom-pins.d"
spec = importlib.util.spec_from_file_location("coord_fragments", ROOT / "scripts/coord-tools/fragments.py")
fragments = importlib.util.module_from_spec(spec)
spec.loader.exec_module(fragments)

class FixtureTree:
    def __init__(self, root):
        self.root = pathlib.Path(root)
        self.files = {p.relative_to(self.root).as_posix() for p in self.root.rglob("*") if p.is_file()}
    def under(self, path): return [f for f in self.files if f.startswith(path + "/")]
    def prefetch(self, paths): pass
    def read(self, path): return (self.root / path).read_text()

def write_fragments(root, obj):
    js = "import {writeFragments} from " + json.dumps((ROOT / "scripts/check-axiom-pins.mjs").as_uri()) + ";let s=String();for await (const c of process.stdin) s+=c;writeFragments(process.argv[1],JSON.parse(s));"
    subprocess.run(["node", "--input-type=module", "-e", js, str(root)], input=json.dumps(obj), text=True, check=True)

def generated(root):
    errors = []
    text = fragments.generate(FixtureTree(root), "inventory.json", FRAGMENTS, "json", errors)
    return text, errors

class FragmentProbes(unittest.TestCase):
    def test_actual_inventory_roundtrip(self):
        original = json.loads((ROOT / "scripts/g07-axiom-pins.json").read_text())
        with tempfile.TemporaryDirectory() as root:
            write_fragments(root, original)
            text, errors = generated(root)
            self.assertEqual(errors, [])
            self.assertEqual(json.loads(text), original)
            self.assertEqual(text, (ROOT / "scripts/g07-axiom-pins.json").read_text())

    def test_fragment_bytes_do_not_depend_on_input_order(self):
        pins = {"Solidity/F.lean:z": ["propext"], "Solidity/F.lean:a": []}
        with tempfile.TemporaryDirectory() as first, tempfile.TemporaryDirectory() as second:
            write_fragments(first, pins)
            write_fragments(second, dict(reversed(list(pins.items()))))
            rel = pathlib.Path(FRAGMENTS) / "Solidity/F.json"
            self.assertEqual((pathlib.Path(first) / rel).read_bytes(), (pathlib.Path(second) / rel).read_bytes())

    def test_divergent_merge_is_refused_without_mutation(self):
        key = "Solidity/F.lean:x"
        with tempfile.TemporaryDirectory() as root:
            file = pathlib.Path(root) / FRAGMENTS / "Solidity/F.json"
            file.parent.mkdir(parents=True)
            file.write_text(json.dumps({key: ["Quot.sound"]}) + "\n")
            before = file.read_bytes()
            notes = []
            old = os.getcwd()
            try:
                os.chdir(root)
                accepted = fragments.apply_json(FixtureTree(root), "inventory.json", FRAGMENTS,
                    json.dumps({key: []}), json.dumps({key: ["propext"]}), "lane", notes, False)
            finally:
                os.chdir(old)
            self.assertFalse(accepted)
            self.assertTrue(any("changed on both sides" in note for note in notes))
            self.assertEqual(file.read_bytes(), before)

    def test_merge_removal_conflicts_preserve_current_value(self):
        key = "Solidity/F.lean:x"
        with tempfile.TemporaryDirectory() as root:
            file = pathlib.Path(root) / FRAGMENTS / "Solidity/F.json"
            file.parent.mkdir(parents=True)
            file.write_text(json.dumps({key: ["Quot.sound"]}) + "\n")
            before = file.read_bytes(); notes = []; old = os.getcwd()
            try:
                os.chdir(root)
                accepted = fragments.apply_json(FixtureTree(root), "inventory.json", FRAGMENTS,
                    json.dumps({key: []}), "{}", "lane", notes, False)
            finally:
                os.chdir(old)
            self.assertFalse(accepted)
            self.assertTrue(any("removed" in note and "changed on the other side" in note for note in notes))
            self.assertEqual(file.read_bytes(), before)

    def test_own_fragment_is_authoritative_over_stale_combined_value(self):
        key = "Solidity/F.lean:x"
        with tempfile.TemporaryDirectory() as root:
            file = pathlib.Path(root) / FRAGMENTS / "Solidity/F.json"
            file.parent.mkdir(parents=True)
            file.write_text(json.dumps({key: ["Quot.sound"]}) + "\n")
            before = file.read_bytes(); notes = []; old = os.getcwd()
            try:
                os.chdir(root)
                accepted = fragments.apply_json(FixtureTree(root), "inventory.json", FRAGMENTS,
                    json.dumps({key: []}), json.dumps({key: ["propext"]}), "lane", notes, True)
            finally:
                os.chdir(old)
            self.assertTrue(accepted)
            self.assertEqual(file.read_bytes(), before)

    def test_merge_conflict_prevents_other_pending_writes(self):
        key, other = "Solidity/F.lean:x", "Solidity/G.lean:y"
        with tempfile.TemporaryDirectory() as root:
            file = pathlib.Path(root) / FRAGMENTS / "Solidity/F.json"
            file.parent.mkdir(parents=True)
            file.write_text(json.dumps({key: ["Quot.sound"]}) + "\n")
            before = file.read_bytes(); notes = []; old = os.getcwd()
            try:
                os.chdir(root)
                accepted = fragments.apply_json(FixtureTree(root), "inventory.json", FRAGMENTS,
                    json.dumps({key: []}), json.dumps({other: ["propext"]}), "lane", notes, False)
            finally:
                os.chdir(old)
            self.assertFalse(accepted)
            self.assertTrue(any("removed" in note and "changed on the other side" in note for note in notes))
            self.assertEqual(file.read_bytes(), before)
            self.assertFalse((pathlib.Path(root) / FRAGMENTS / "Solidity/G.json").exists())

    def test_uncontested_removal_deletes_empty_fragment(self):
        key = "Solidity/F.lean:x"
        with tempfile.TemporaryDirectory() as root:
            file = pathlib.Path(root) / FRAGMENTS / "Solidity/F.json"
            file.parent.mkdir(parents=True)
            file.write_text(json.dumps({key: []}) + "\n")
            notes = []; old = os.getcwd()
            try:
                os.chdir(root)
                accepted = fragments.apply_json(FixtureTree(root), "inventory.json", FRAGMENTS,
                    json.dumps({key: []}), "{}", "lane", notes, False)
            finally:
                os.chdir(old)
            self.assertTrue(accepted)
            self.assertFalse(file.exists())

    def test_cleanup_removes_stale_fragments_and_keeps_live_pins(self):
        with tempfile.TemporaryDirectory() as root:
            write_fragments(root, {"Solidity/Old/Nested.lean:x": [], "Solidity/Keep.lean:a": []})
            write_fragments(root, {"Solidity/Keep.lean:a": ["propext"]})
            self.assertFalse((pathlib.Path(root) / FRAGMENTS / "Solidity/Old").exists())
            text, errors = generated(root)
            self.assertEqual(errors, [])
            self.assertEqual(json.loads(text), {"Solidity/Keep.lean:a": ["propext"]})

    def test_bad_writer_keys_refused_before_cleanup(self):
        for key in ("missing-delimiter", "../escape.lean:x", "Solidity/../escape.lean:x", "Solidity/F.lean:"):
            with self.subTest(key=key), tempfile.TemporaryDirectory() as root:
                write_fragments(root, {"Solidity/Keep.lean:x": []})
                live = pathlib.Path(root) / FRAGMENTS / "Solidity/Keep.json"
                before = live.read_bytes()
                with self.assertRaises(subprocess.CalledProcessError):
                    write_fragments(root, {key: []})
                self.assertEqual(live.read_bytes(), before)

    def test_cleanup_rejects_symlink_without_touching_target(self):
        with tempfile.TemporaryDirectory() as root, tempfile.TemporaryDirectory() as outside:
            directory = pathlib.Path(root) / FRAGMENTS
            directory.mkdir(parents=True)
            victim = pathlib.Path(outside) / "victim.json"
            victim.write_text("preserve")
            (directory / "link").symlink_to(outside, target_is_directory=True)
            with self.assertRaises(subprocess.CalledProcessError):
                write_fragments(root, {})
            self.assertEqual(victim.read_text(), "preserve")

    def test_invalid_combined_inputs_are_refused_without_mutation(self):
        bad = ('{"Solidity/F.lean:x": [], "Solidity/F.lean:x": ["propext"]}',
               '{"../escape.lean:x": []}', '{"missing": []}', '{"Solidity/F.lean:x": null}')
        for combined in bad:
            with self.subTest(combined=combined), tempfile.TemporaryDirectory() as root:
                file = pathlib.Path(root) / FRAGMENTS / "Solidity/F.json"
                file.parent.mkdir(parents=True)
                file.write_text('{"Solidity/F.lean:x": []}\n')
                before = file.read_bytes(); notes = []; old = os.getcwd()
                try:
                    os.chdir(root)
                    accepted = fragments.apply_json(FixtureTree(root), "inventory.json", FRAGMENTS,
                        '{"Solidity/F.lean:x": []}', combined, "lane", notes, False)
                finally:
                    os.chdir(old)
                self.assertFalse(accepted)
                self.assertTrue(notes)
                self.assertEqual(file.read_bytes(), before)

    def test_duplicate_json_key_is_rejected(self):
        with tempfile.TemporaryDirectory() as root:
            file = pathlib.Path(root) / FRAGMENTS / "Solidity/F.json"
            file.parent.mkdir(parents=True)
            file.write_text('{"Solidity/F.lean:x": ["propext"], "Solidity/F.lean:x": []}\n')
            _, errors = generated(root)
            self.assertTrue(errors, "duplicate keys silently discard a pin value")

if __name__ == "__main__": unittest.main()
