"""Adversarial census fixtures; no Lean/server invocation."""
import unittest
import tempfile
from pathlib import Path
from unittest.mock import patch
from census import scan, main

class CensusTests(unittest.TestCase):
    def test_comments_strings_and_default_binder(self):
        text='''/- theorem ghost : False := by /- nested -/ -/
namespace N
section
variable {A : Type}
def decoy := "theorem phantom : False := by"
theorem live (n : Nat := 0) : n = n := rfl
end
end N
'''
        rows=scan(text,"fixture")
        self.assertEqual([r["source_name"] for r in rows],["N.live"])
        self.assertEqual(rows[0]["source_header"],"theorem live (n : Nat := 0) : n = n")
    def test_equations_let_and_where(self):
        rows=scan("""namespace N
 theorem eqn : (n : Nat) → n = n
  | n => rfl
 theorem scoped : let n := 1; n = 1 := rfl
 theorem record : R where
   field := 1
end N
""","fixture")
        self.assertEqual([r["source_header"] for r in rows],[
            "theorem eqn : (n : Nat) → n = n",
            "theorem scoped : let n := 1; n = 1", "theorem record : R"])
    def test_unsupported_prefix_fails_closed(self):
        with self.assertRaisesRegex(ValueError,"Unsupported declaration prefix"):
            scan("@[simp] theorem hidden : True := trivial","fixture")
    def test_removed_frozen_map_row_is_rejected(self):
        with tempfile.TemporaryDirectory() as temp:
            checkout=Path(temp)/"checkout"
            mapping=checkout/"docs/module-map/theories.md"
            mapping.parent.mkdir(parents=True)
            tick=chr(96)  # Disposable fixture paths are not repository documentation links.
            mapping.write_text(f"| {tick}Theory/One.lean{tick} | one |\n")
            frozen=mapping.read_text()+f"| {tick}Theory/Two.lean{tick} | two |\n"
            with patch("census.ROOT",checkout), patch("census.subprocess.run"), \
                 patch("census.subprocess.check_output",return_value=frozen.encode()), \
                 patch("sys.argv",["census.py","--out",str(Path(temp)/"out")]):
                with self.assertRaisesRegex(SystemExit,"Frozen module map changed"):
                    main()

    def test_root_namespace_and_mutual(self):
        rows=scan("namespace N\nmutual\ntheorem _root_.R.x : True := trivial\nend\nend N\n","fixture")
        self.assertEqual(rows[0]["source_name"],"R.x")

if __name__ == "__main__": unittest.main()
