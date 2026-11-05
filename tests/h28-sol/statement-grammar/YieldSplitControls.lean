import Solidity.Frontend.StatementGrammarH28.YieldSplit

/-! Actual intermediate-layout decomposition, including string bytes that
look like braces but remain neutral string tokens. No expression uniqueness. -/
namespace Solidity.Frontend.StatementGrammarH28
open Solidity.Source Solidity.Frontend.Checked

def splitHead : Syn (.item .body) :=
  .stmtItem (.returnStmt (.some (.lit (.str [123, 125]))))
def splitTailItem : Syn (.item .body) :=
  .stmtItem (.returnStmt (.some (.lit (.str [66]))))
def splitTail : Syn (.list (.item .body)) := .cons splitTailItem .nil

def splitL : List Choice := [.frags [1, 1], .frags [1], .attrs [.vis]]
def splitN : List Choice := [.frags [1], .attrs [.vis]]
def splitM : List Choice := [.attrs [.vis]]
def splitHeadTokens : List Tok := [.kw .return_, .str [123], .str [125], .punct .semi]
def splitTailTokens : List Tok := [.kw .return_, .str [66], .punct .semi]

theorem split_head_actual : splitHead.yield splitL = some ([splitHeadTokens], splitN) := by decide

theorem split_tail_actual : splitTail.yield splitN = some ([splitTailTokens], splitM) := by decide

theorem split_list_actual :
    (Syn.cons splitHead splitTail).yield splitL =
      some ([splitHeadTokens, splitTailTokens], splitM) :=
  list_yield_cons_of _ _ splitL splitN splitM _ _ split_head_actual split_tail_actual

example : ∃ head tail N, splitHead.yield splitL = some (head, N) ∧
    splitTail.yield N = some (tail, splitM) ∧
    [splitHeadTokens, splitTailTokens] = head.flatten :: tail :=
  list_yield_cons_decompose _ _ _ _ _ split_list_actual

theorem split_head_balanced : BraceBalanced splitHeadTokens :=
  .append (.token _ (by decide) (by decide))
    (.append (.token _ (by decide) (by decide))
      (.append (.token _ (by decide) (by decide)) (.token _ (by decide) (by decide))))

theorem split_tail_balanced : BraceBalanced splitTailTokens :=
  .append (.token _ (by decide) (by decide))
    (.append (.token _ (by decide) (by decide)) (.token _ (by decide) (by decide)))

theorem split_block_boundary :
    BlockBoundary (Syn.block (.cons splitHead splitTail)) splitL splitM
      (splitHeadTokens ++ splitTailTokens) := by
  apply block_boundary_of_items _ splitL splitM [splitHeadTokens, splitTailTokens] split_list_actual
  intro part hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact split_head_balanced
  · exact split_tail_balanced

/-- Bad fragment lengths fail; a successful yield is never mocked. -/
example : splitHead.yield [.frags [1]] = none := by decide

example : splitHead.yield [.frags []] = none := by decide

#print axioms split_head_actual
#print axioms split_tail_actual
#print axioms split_list_actual
#print axioms split_block_boundary
end Solidity.Frontend.StatementGrammarH28
