import importlib.util
from pathlib import Path
import unittest

ROOT = Path(__file__).resolve().parents[4]
spec = importlib.util.spec_from_file_location("generate_linking_fixture", ROOT/"scripts/h62/item6/migrate-backend/generate_linking_fixture.py")
generator = importlib.util.module_from_spec(spec)
spec.loader.exec_module(generator)

class ProposalOutputGuards(unittest.TestCase):
    def test_original_and_output_aliases_are_refused_without_writes(self):
        target = ROOT/"tests/h62/item6/migrate-backend/NoWrite.lean"
        metadata = Path("/workspace/migrate-backend-evidence/NoWrite.json")
        with self.assertRaises(ValueError): generator.validate_outputs(generator.SOURCE,target,metadata)
        with self.assertRaises(ValueError): generator.validate_outputs(target,target,metadata)

    def test_other_original_sources_are_outside_output_scope(self):
        other = ROOT/"Solidity/Backend/Scalar/Slice.lean"
        patch = Path("/workspace/migrate-backend-evidence/NoWrite.patch")
        metadata = Path("/workspace/migrate-backend-evidence/NoWrite.json")
        with self.assertRaises(ValueError): generator.validate_outputs(other,patch,metadata)

    def test_distinct_scoped_output_paths_are_accepted_without_writes(self):
        paths = [ROOT/"tests/h62/item6/migrate-backend/NoWrite.lean",Path("/workspace/migrate-backend-evidence/NoWrite.patch"),Path("/workspace/migrate-backend-evidence/NoWrite.json")]
        self.assertEqual(generator.validate_outputs(*paths),[path.resolve() for path in paths])

if __name__ == "__main__": unittest.main()
