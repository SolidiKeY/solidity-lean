"""Guard missing/duplicated law associations and changed premise acceptance."""
import unittest
from family_coverage import check, check_families


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

    def test_short_and_qualified_witness_are_one_identity(self):
        source = self.source.replace(b"end N", b"theorem u (h : False) : True := by trivial\nend N")
        witness = "namespace N\ntheorem w : True := by trivial\nend N\n#verify_hypotheses w for N.t\n#verify_hypotheses N.w for N.u\n"
        with self.assertRaisesRegex(ValueError, "duplicate resolved witness"):
            check("fixture", source, source, witness)

    def test_changed_premise(self):
        with self.assertRaisesRegex(ValueError, "header/context"):
            self.run_check(source=self.source.replace(b"(h : False)", b"(h : True)"))


class CombinedFamilies(unittest.TestCase):
    def families(self, duplicate_target=False, duplicate_witness=False):
        source_a = FamilyCoverage.source
        witness_a = FamilyCoverage.witness
        source_b = source_a if duplicate_target else source_a.replace(b"theorem t", b"theorem u")
        witness_b = witness_a if duplicate_target else witness_a.replace("N.t", "N.u")
        if not duplicate_witness and not duplicate_target:
            witness_b = witness_b.replace("witness_t", "witness_u")
        return [("a", source_a, source_a, witness_a), ("b", source_b, source_b, witness_b)]

    def test_distinct(self):
        report = check_families(self.families())
        self.assertEqual(report["unique_targets"], 2)
        self.assertEqual(report["unique_witnesses"], 2)
        self.assertFalse(report["kernel_checked_by_this_command"])

    def test_duplicate_target_refused(self):
        with self.assertRaisesRegex(ValueError, "target counted"):
            check_families(self.families(duplicate_target=True))

    def test_duplicate_witness_refused(self):
        with self.assertRaisesRegex(ValueError, "witness declaration counted"):
            check_families(self.families(duplicate_witness=True))


if __name__ == "__main__":
    unittest.main()
