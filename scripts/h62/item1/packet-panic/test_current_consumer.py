import hashlib
import pathlib
import tomllib
import unittest

ROOT = pathlib.Path(__file__).resolve().parents[4]
PROJECT = ROOT / "tests/h62/item1/packet-panic/closure-project-current"

class CurrentConsumerTest(unittest.TestCase):
    def test_project_location_toolchain_and_generated_files(self):
        config = tomllib.loads((PROJECT / "lakefile.toml").read_text())
        libs = {item["name"]: item for item in config["lean_lib"]}
        self.assertEqual(libs["PanicBytes"]["srcDir"], ".")
        self.assertEqual((PROJECT / libs["Solidity"]["srcDir"]).resolve(), ROOT)
        self.assertTrue(all("-j1" in item["weakLeanArgs"] for item in libs.values()))
        self.assertEqual((PROJECT / "lean-toolchain").read_text().strip(), "leanprover/lean4:v4.35.0")
        self.assertEqual(set((PROJECT / ".gitignore").read_text().splitlines()), {"/.lake/", "/lake-manifest.json", "/PanicBytes.lean"})
        helper = ROOT / "Solidity/Backend/PrimitivePackets/PanicBytes.lean"
        self.assertEqual(hashlib.sha256(helper.read_bytes()).hexdigest(), "c1d3eeb8f7c23308ee1b0b33fb7be331e7792f7bf8e646812517453db7428246")

if __name__ == "__main__": unittest.main()
