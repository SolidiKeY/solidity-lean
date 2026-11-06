import Solidity.Yul.WordLogic

/-! Surface notation for the intrinsic closed-word logic. These macros only
construct the indexed core objects. Printers are kept in WordPrint. -/
namespace Solidity.Yul.Logic
scoped syntax "tm{" &"yul"  term " | " term " }" : term
scoped syntax "dl{" &"yul" &"program"  term " | " term " }" : term
scoped syntax "dl{" &"yul"  term " ; " term " ; " term " ; " term " }" : term
scoped syntax "dl{" &"yul"  term " ⇝ " term " }" : term
scoped syntax "dl{" &"yul" &"subst"  term " ; " term " }" : term
scoped syntax (name := yulTermModal) "dl{" &"yul" &"eval" term " ; " term " ; " term " => " term " }" : term
scoped syntax "dl{" &"yul" &"atom"  term " }" : term

scoped syntax (name := yulLoopModal) "dl{" &"yul" &"loop" term " ; " term " ; " term " ; "
  term " ; " term " ; " term " ; " term " }" : term

macro_rules (kind := yulLoopModal)
  | `(dl{ yul loop $control ; $mode ; $model ; $condition ; $step ; $body ; $post }) =>
      `(Solidity.Yul.Logic.Fml.loopModal $control $mode $model $condition $step $body $post)

scoped syntax (name := yulFeed) "dl{" &"yul" &"feed" term " | " term " }" : term

macro_rules (kind := yulFeed)
  | `(dl{ yul feed $read | $post }) => `(Solidity.Yul.Logic.Fml.feed $read $post)

macro_rules (kind := yulTermModal)
  | `(dl{ yul eval $mode ; $model ; $term => $post }) =>
      `(Solidity.Yul.Logic.Fml.termModal $mode $model $term $post)

macro_rules
  | `(tm{ yul $code | $words }) => `(Solidity.Yul.Logic.Term.mk $code $words)
  | `(dl{ yul program $code | $words }) => `(Solidity.Yul.Logic.Program.mk $code $words)
  | `(dl{ yul $mode ; $model ; $program ; $post }) =>
      `(Solidity.Yul.Logic.Fml.modal $mode $model $program $post)
  | `(dl{ yul $first ⇝ $second }) => do
      let rule := Lean.mkIdent `Solidity.Yul.Logic.Rule
      `($rule $first $second)
  | `(dl{ yul subst $update ; $post }) => `(Solidity.Yul.Logic.Fml.subst $update $post)
  | `(dl{ yul atom $predicate }) => `(Solidity.Yul.Logic.Fml.atom $predicate)
end Solidity.Yul.Logic
