import Lean

/- Isolated witnesses for the String/Slice boundary blocking Syntax.Raw.
These cover standard-library conversions, not the complete Solidity parser. -/
namespace H62StringApiBoundary

def dropText (text : String) (count : Nat) : String :=
  toString (text.drop count)

def dropTailText (text : String) (count : Nat) : String :=
  String.mk (text.toList.take (text.toList.length - count))

def firstSuffix (text : String) (suffixes : List String) : Option String :=
  suffixes.find? (fun suffix : String => text.endsWith suffix)

example : dropText "keccak" 1 = "eccak" := by decide +kernel
example : dropText "éλabc" 2 = "abc" := by decide +kernel
example : dropText "abc" 0 = "abc" := by decide +kernel
example : dropText "abc" 9 = "" := by decide +kernel
example : dropTailText "uint256[]" 2 = "uint256" := by decide +kernel
example : dropTailText "abcéλ" 2 = "abc" := by decide +kernel
example : dropTailText "abc" 9 = "" := by decide +kernel
-- The old substring equality primitive does not kernel-reduce here.
-- These are runtime acceptance checks, separate from the seven kernel proofs above.
/-- info: some "[]" -/
#guard_msgs in #eval firstSuffix "uint256[]" ["[]", "()"]
/-- info: none -/
#guard_msgs in #eval firstSuffix "uint256" ["[]", "()"]
end H62StringApiBoundary
