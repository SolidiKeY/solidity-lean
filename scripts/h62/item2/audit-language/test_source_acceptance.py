"""Guard omitted/duplicated source rows and invented owner/proof authority."""
import copy
import unittest
from source_acceptance import validate, parser_regressions


class FreshAcceptance(unittest.TestCase):
    def report(self):
        return {"historical_replay": False, "kernel_checked": False, "certified_witnesses": 0,
                "declarations": [{"id": "fixture:1:t", "source_signature": "theorem t (h : False) : True",
                                  "owner": None, "owner_status": "UNVERIFIABLE-historical-snapshot"}]}

    def test_exact(self):
        report = self.report()
        validate(report, copy.deepcopy(report))

    def test_mutations_refused(self):
        for mutation in ("omit", "duplicate", "premise", "owner", "kernel", "replay", "witness"):
            with self.subTest(mutation=mutation):
                expected = self.report()
                changed = copy.deepcopy(expected)
                if mutation == "omit": changed["declarations"].clear()
                elif mutation == "duplicate": changed["declarations"] *= 2
                elif mutation == "premise": changed["declarations"][0]["source_signature"] = "theorem t : True"
                elif mutation == "owner": changed["declarations"][0]["owner"] = "invented-owner"
                elif mutation == "kernel": changed["kernel_checked"] = True
                elif mutation == "replay": changed["historical_replay"] = True
                else: changed["certified_witnesses"] = 1
                with self.assertRaises(ValueError):
                    validate(changed, expected)

    def test_parser_regressions(self):
        parser_regressions()


if __name__ == "__main__":
    unittest.main()
