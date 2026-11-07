"""Guard missing/duplicated law associations and changed premise acceptance."""
import unittest
from family_coverage import check


class FamilyCoverage(unittest.TestCase):
    source = b"namespace N\ntheorem t (h : False) : True := by trivial\nend N\n"
    witness = "theorem witness_t : True := by trivial\n#verify_hypotheses witness_t for N.t\n"

    def run_check(self, source=None, witness=None):
        return check("fixture", self.source, self.source if source is None else source,
                     self.witness if witness is None else witness)

    def test_complete(self):
        self.assertEqual(self.run_check()["named_targets"], 1)

    def test_missing(self):
        with self.assertRaisesRegex(ValueError, "association"):
            self.run_check(witness="")

    def test_duplicate(self):
        with self.assertRaisesRegex(ValueError, "association"):
            self.run_check(witness=self.witness * 2)

    def test_unexpected(self):
        with self.assertRaisesRegex(ValueError, "association"):
            self.run_check(witness=self.witness.replace("N.t", "N.other"))

    def test_comment_is_not_association(self):
        with self.assertRaisesRegex(ValueError, "association"):
            self.run_check(witness="/-\n" + self.witness + "-/\n")

    def test_string_is_not_association(self):
        with self.assertRaisesRegex(ValueError, "association"):
            self.run_check(witness='def text := "\n#verify_hypotheses witness_t for N.t\n"\n')

    def test_undeclared_witness(self):
        with self.assertRaisesRegex(ValueError, "witness declaration"):
            self.run_check(witness="#verify_hypotheses invented for N.t\n")

    def test_duplicate_source_name(self):
        with self.assertRaisesRegex(ValueError, "duplicate source theorem"):
            self.run_check(source=self.source + self.source)

    def test_changed_premise(self):
        with self.assertRaisesRegex(ValueError, "header/context"):
            self.run_check(source=self.source.replace(b"(h : False)", b"(h : True)"))


if __name__ == "__main__":
    unittest.main()
