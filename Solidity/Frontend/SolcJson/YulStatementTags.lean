import Solidity.Frontend.SolcJson.Yul
import Solidity.Yul.StatementTags

/-! Actual successful statement decoding preserves its intrinsic constructor
tag. Helper facts are concrete decoder proofs, not assumed preparation laws. -/
namespace Solidity.Frontend.YulJson.StatementTags
open Lean (Json)
theorem decoded_tag (fuel : Nat) {node tree}
    (parsed : statementAux fuel node = .ok tree) :
    Solidity.Yul.StatementTags.statement tree = (string node "nodeType").toOption := by
  cases fuel with
  | zero => cases parsed
  | succ fuel =>
      rw [statementAux] at parsed
      cases kindEq : string node "nodeType" with
      | error reason =>
          simp only [kindEq,bind,Except.bind] at parsed
          cases parsed
      | ok kind =>
          change Solidity.Yul.StatementTags.statement tree = some kind
          simp only [kindEq,bind,Except.bind] at parsed
          by_cases kind0 : kind = "YulBlock"
          · rw [if_pos kind0] at parsed
            subst kind
            repeat' first | (split at parsed) |
              (simp only [pure, Except.pure] at parsed) | (cases parsed) | rfl
          · rw [if_neg kind0] at parsed
            by_cases kind1 : kind = "YulVariableDeclaration"
            · rw [if_pos kind1] at parsed
              subst kind
              repeat' first | (split at parsed) |
                (simp only [pure, Except.pure] at parsed) | (cases parsed) | rfl
            · rw [if_neg kind1] at parsed
              by_cases kind2 : kind = "YulAssignment"
              · rw [if_pos kind2] at parsed
                subst kind
                repeat' first | (split at parsed) |
                  (simp only [pure, Except.pure] at parsed) | (cases parsed) | rfl
              · rw [if_neg kind2] at parsed
                by_cases kind3 : kind = "YulExpressionStatement"
                · rw [if_pos kind3] at parsed
                  subst kind
                  repeat' first | (split at parsed) |
                    (simp only [pure, Except.pure] at parsed) | (cases parsed) | rfl
                · rw [if_neg kind3] at parsed
                  by_cases kind4 : kind = "YulIf"
                  · rw [if_pos kind4] at parsed
                    subst kind
                    repeat' first | (split at parsed) |
                      (simp only [pure, Except.pure] at parsed) | (cases parsed) | rfl
                  · rw [if_neg kind4] at parsed
                    by_cases kind5 : kind = "YulForLoop"
                    · rw [if_pos kind5] at parsed
                      subst kind
                      repeat' first | (split at parsed) |
                        (simp only [pure, Except.pure] at parsed) | (cases parsed) | rfl
                    · rw [if_neg kind5] at parsed
                      by_cases kind6 : kind = "YulSwitch"
                      · rw [if_pos kind6] at parsed
                        subst kind
                        repeat' first | (split at parsed) |
                          (simp only [pure, Except.pure] at parsed) | (cases parsed) | rfl
                      · rw [if_neg kind6] at parsed
                        by_cases kind7 : kind = "YulFunctionDefinition"
                        · rw [if_pos kind7] at parsed
                          subst kind
                          repeat' first | (split at parsed) |
                            (simp only [pure, Except.pure] at parsed) | (cases parsed) | rfl
                        · rw [if_neg kind7] at parsed
                          by_cases kind8 : kind = "YulBreak"
                          · rw [if_pos kind8] at parsed
                            subst kind
                            repeat' first | (split at parsed) |
                              (simp only [pure, Except.pure] at parsed) | (cases parsed) | rfl
                          · rw [if_neg kind8] at parsed
                            by_cases kind9 : kind = "YulContinue"
                            · rw [if_pos kind9] at parsed
                              subst kind
                              repeat' first | (split at parsed) |
                                (simp only [pure, Except.pure] at parsed) | (cases parsed) | rfl
                            · rw [if_neg kind9] at parsed
                              by_cases kind10 : kind = "YulLeave"
                              · rw [if_pos kind10] at parsed
                                subst kind
                                repeat' first | (split at parsed) |
                                  (simp only [pure, Except.pure] at parsed) | (cases parsed) | rfl
                              · rw [if_neg kind10] at parsed
                                cases parsed
/-- A concrete known intrinsic constructor fixes the actual JSON node tag. -/
theorem kind_of_tag (fuel : Nat) {node tree wanted}
    (parsed : statementAux fuel node = .ok tree)
    (tag : Solidity.Yul.StatementTags.statement tree = some wanted) :
    string node "nodeType" = .ok wanted := by
  have actual := decoded_tag fuel parsed
  cases kindEq : string node "nodeType" with
  | error reason =>
      rw [kindEq] at actual
      have impossible : (some wanted : Option String) = none := tag.symm.trans actual
      cases impossible
  | ok kind =>
      rw [kindEq] at actual
      have same : (some wanted : Option String) = some kind := tag.symm.trans actual
      exact congrArg Except.ok (Option.some.inj same).symm

end Solidity.Frontend.YulJson.StatementTags
