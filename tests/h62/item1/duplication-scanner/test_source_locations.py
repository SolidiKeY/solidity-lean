"""Guard guessed namespaces, generated aliases, ambiguous ranges and replay."""
import copy
import hashlib
import importlib.util
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest import mock

ROOT = Path(__file__).resolve().parents[4]
SCRIPTS = ROOT / "scripts/h62/item1/duplication-scanner"
sys.path.insert(0, str(SCRIPTS))
try:
    spec = importlib.util.spec_from_file_location("source_locations", SCRIPTS / "bind_source_locations.py")
    locations = importlib.util.module_from_spec(spec); spec.loader.exec_module(locations)
finally:
    sys.path.pop(0)


def name(*parts):
    value = ["anonymous"]
    for part in parts: value = ["str",value,part]
    return value


def position(line, column): return {"line":line,"column":column}


def selection(line, first, last, end):
    return {"start":position(line,first),"end":position(line,last),
            "range_start":position(line,0),"range_end":position(line,end)}


def fixtures():
    source = "theorem same : True := True.intro\ntheorem same : True := True.intro\n"
    lexical = [{"path":"A.lean","line":line,"name":"same","kind":"theorem","reject_reason":None} for line in (1,2)]
    kernel = {"format":1,"module":locations.kernel.MODULE,"total":2,"rows":[
        {"declaration":name(namespace,"same"),"kind":"theorem","status":"serialized","signature":[namespace]} for namespace in ("First","Second")]}
    metadata = {"format":1,"module":locations.kernel.MODULE,"rows":[
        {"declaration":row["declaration"],"selection":selection(line,8,12,32)} for line,row in enumerate(kernel["rows"],1)]}
    return source,lexical,kernel,metadata


class SourceLocationControls(unittest.TestCase):
    def test_namespaces_come_from_kernel_identity_not_spelling(self):
        result = locations.join_locations(*fixtures())
        self.assertEqual(result["linked"],2)
        self.assertEqual([r["declaration"] for r in result["rows"]],[name("First","same"),name("Second","same")])
        self.assertFalse(result["ownership_verified"])
        self.assertFalse(result["unloaded_private_artifacts_covered"])

    def test_same_location_for_two_constants_is_ambiguous(self):
        source,lexical,kernel,metadata = fixtures()
        metadata["rows"][1]["selection"] = copy.deepcopy(metadata["rows"][0]["selection"])
        result = locations.join_locations(source,lexical,kernel,metadata)
        self.assertEqual(result["linked"],0)
        self.assertEqual(result["rows"][0]["status"],"ambiguous-direct-location-match")

    def test_generated_alias_to_parent_does_not_get_a_source_link(self):
        source,lexical,kernel,metadata = fixtures()
        generated = {"declaration":name("First","same","rec"),"kind":"recursor","status":"serialized","signature":[]}
        kernel["rows"].append(generated);kernel["total"]+=1
        metadata["rows"].append({"declaration":generated["declaration"],"selection":copy.deepcopy(metadata["rows"][0]["selection"])})
        result = locations.join_locations(source,lexical,kernel,metadata)
        self.assertEqual(result["linked"],2)
        self.assertIn(generated["declaration"],result["kernel_without_lexical_link"])

    def test_missing_locations_and_unsupported_types_stay_unresolved(self):
        source,lexical,kernel,metadata = fixtures()
        metadata["rows"][0]["selection"] = None
        kernel["rows"][1].pop("signature");kernel["rows"][1].update(status="unsupported",reason="expression metadata")
        result = locations.join_locations(source,lexical,kernel,metadata)
        self.assertEqual(result["linked"],0)
        self.assertEqual([r["status"] for r in result["rows"]],["no-direct-location-match","unsupported-signature"])

    def test_kind_mismatch_and_lexical_refusal_are_not_hidden(self):
        source,lexical,kernel,metadata = fixtures()
        lexical[0]["kind"]="def";lexical[1]["reject_reason"]="unsupported-declaration-form"
        result = locations.join_locations(source,lexical,kernel,metadata)
        self.assertEqual(result["rows"][0]["status"],"declaration-kind-mismatch")
        self.assertEqual(result["rows"][1]["reject_reason"],"unsupported-declaration-form")

    def test_omitted_duplicate_or_foreign_constant_metadata_is_rejected(self):
        for mutation in (lambda rows:rows.pop(),lambda rows:rows.append(copy.deepcopy(rows[0])),
                         lambda rows:rows[0].update(declaration=name("foreign"))):
            source,lexical,kernel,metadata = fixtures(); mutation(metadata["rows"])
            with self.assertRaises(ValueError): locations.join_locations(source,lexical,kernel,metadata)

    def test_multiple_lexical_claims_for_one_constant_are_rejected(self):
        source,lexical,kernel,metadata = fixtures();lexical.append(copy.deepcopy(lexical[0]))
        with self.assertRaisesRegex(ValueError,"multiple lexical rows"):
            locations.join_locations(source,lexical,kernel,metadata)

    def test_unicode_codepoints_and_lf_only_line_map(self):
        source = "def α𐐀 : Nat := 0\n"
        self.assertEqual(locations.source_slice(source,selection(1,4,6,17)),"α𐐀")
        # U+2028 is not a FileMap newline; Python splitlines would miscount it.
        source = "x\u2028y\n"
        self.assertEqual(locations.source_slice(source,selection(1,2,3,3)),"y")
        location = {"start":position(1,0),"end":position(2,0),"range_start":position(1,0),"range_end":position(2,0)}
        self.assertEqual(locations.source_slice(source,location),source)

    def test_out_of_range_or_non_nested_positions_rejected(self):
        for location in (selection(99,8,12,32),selection(1,99,100,101),selection(1,12,8,32),selection(1,8,12,10)):
            with self.assertRaises(ValueError): locations.source_slice(fixtures()[0],location)

    def test_bound_live_receipts_allow_finite_timings_but_reject_nonfinite(self):
        with tempfile.TemporaryDirectory() as directory:
            path=Path(directory)/"receipt.json"
            raw=b'{"seconds":1.25,"exit":0}\n';path.write_bytes(raw)
            value=locations.read_bound_json(path,hashlib.sha256(raw).hexdigest())
            self.assertEqual(value,{"seconds":1.25,"exit":0})
            for raw in (b'{"seconds":NaN}',b'{"seconds":1e999}'):
                path.write_bytes(raw)
                with self.assertRaises(ValueError):locations.read_bound_json(path,hashlib.sha256(raw).hexdigest())

    def test_post_kernel_mutation_cannot_feed_source_join(self):
        for altered in ("census.json","rebuild/receipt.json"):
            with self.subTest(artifact=altered),tempfile.TemporaryDirectory() as directory:
                output=Path(directory)/"new"
                def fake_live(child):
                    (child/"rebuild").mkdir(parents=True)
                    census_bytes=b'{}\n';rebuild_bytes=b'{"compiled_artifacts": []}\n'
                    (child/"census.json").write_bytes(census_bytes)
                    (child/"rebuild/receipt.json").write_bytes(rebuild_bytes)
                    live={"status":"pass","census_sha256":hashlib.sha256(census_bytes).hexdigest(),
                          "rebuild_receipt_sha256":hashlib.sha256(rebuild_bytes).hexdigest()}
                    (child/"receipt.json").write_text(json.dumps(live,indent=2)+"\n")
                    (child/altered).write_text('{"fabricated":true}\n')
                    return live
                with mock.patch.object(locations.kernel,"run",side_effect=fake_live),mock.patch.object(locations.binder,"checked_process") as compiler:
                    with self.assertRaisesRegex(ValueError,"child artifact hash mismatch"):
                        locations.run(output)
                compiler.assert_not_called()
                self.assertEqual(json.loads((output/"receipt.json").read_text())["status"],"failed")

    def test_saved_success_output_cannot_authorize_a_new_run(self):
        with tempfile.TemporaryDirectory() as directory:
            output=Path(directory)/"old";output.mkdir();(output/"receipt.json").write_text('{"status":"pass"}')
            with mock.patch.object(locations.kernel,"run") as run:
                with self.assertRaises(FileExistsError):locations.run(output)
            run.assert_not_called()


if __name__ == "__main__":unittest.main()
