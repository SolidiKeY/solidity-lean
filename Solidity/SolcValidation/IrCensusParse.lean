import Solidity.SolcValidation.IrErase
import Solidity.SolcValidation.IrCensusTree

/-!
# The parser's own result for the LinkedMath fixture

`linked_certified` (`SolcValidation/IrCensusTree.lean`) shows that `linkedRoot`
carries the parser's certificate for the fixture text. Here the parser itself is
run on the text by the kernel: `parse linkedText` succeeds and its tree is
`linkedRoot` (`linked_is_the_parse`), compared through the injective erasure of
`SolcValidation/IrErase.lean`; so theorems about `linkedRoot` are about the
parser's output, not only about a tree with the same certificate.

The same statement for the Census fixture is not proved: running `parse` on its
45 KB in the kernel takes about two minutes when only the success is decided, and
deciding the erasure of the result as well exhausted the Lean worker (the kernel
does not share the parser's intermediate results, so every projection of the
result re-runs the parse below it). Census rests on `census_certified`; printer
injectivity under `objectWf` (which would make any certified tree the parse) is
not proved.
-/
namespace Solidity.SolcValidation.IrSyntax
open Solidity.SolcValidation

/-- The parser succeeds on `text` and returns a tree whose erasure is `root`'s. -/
def parsesTo (text : String) (root : Object Code) : Bool :=
  match parse text with
  | .ok p => decide (objectErase p.parts.root = objectErase root)
  | .error _ => false

theorem parse_is (text : String) (root : Object Code) (h : parsesTo text root = true) :
    ∃ p, parse text = .ok p ∧ p.parts.root = root := by
  unfold parsesTo at h
  revert h
  cases parse text with
  | error e => intro h; exact Bool.noConfusion h
  | ok p =>
    intro h
    exact ⟨p, rfl, objectErase_inj _ _ (of_decide_eq_true h)⟩

theorem linked_parse_erased : parsesTo linkedText linkedRoot = true := by decide +kernel

/-- The parser's result for the LinkedMath fixture is `linkedRoot`. -/
theorem linked_is_the_parse : ∃ p, parse linkedText = .ok p ∧ p.parts.root = linkedRoot :=
  parse_is linkedText linkedRoot linked_parse_erased

end Solidity.SolcValidation.IrSyntax
