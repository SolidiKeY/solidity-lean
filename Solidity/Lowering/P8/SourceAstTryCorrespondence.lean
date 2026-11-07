import Solidity.Lowering.P8.SourceAstBranchCorrespondence

/-! Try success and ordered-handler correspondence.
Regression purpose: retain call, success return names/body, mandatory first
catch and every later catch in order. These are unchanged-reader syntax laws,
not Source typing, admission, lifecycle or artifact provenance proofs. -/
namespace Solidity.Lowering.P8.SourceAstTryCorrespondence
open Lean Solidity.Source
open SourceAstParameters SourceAstCorrespondence SourceAstExpressionCorrespondence

theorem try_ok_iff_each (fuel : Nat) (node rawCall success firstCatch rawBody : Json)
    (clauses : Array Json) (rest : List Json) (call : Syn .expr)
    (returns : List (Syn .param)) (body : Syn (.block .body))
    (first : Syn (.catchClause .body)) (out : Syn (.stmt .body))
    (kind : node.getObjValAs? String "nodeType" = .ok "TryStatement")
    (callField : node.getObjVal? "externalCall" = .ok rawCall)
    (callValue : SourceAstExpressions.expression fuel rawCall = .ok call)
    (clauseField : node.getObjValAs? (Array Json) "clauses" = .ok clauses)
    (shape : clauses.toList = success :: firstCatch :: rest)
    (successKind : success.getObjValAs? String "nodeType" = .ok "TryCatchClause")
    (successName : success.getObjValAs? String "errorName" = .ok "")
    (returnsValue : SourceAstStatements.clauseParameters fuel success = .ok returns)
    (bodyField : success.getObjVal? "block" = .ok rawBody)
    (bodyValue : SourceAstStatements.blockWith (SourceAstStatements.statement fuel) rawBody = .ok body)
    (firstValue : SourceAstStatements.catchWith fuel
      (SourceAstStatements.blockWith (SourceAstStatements.statement fuel)) firstCatch = .ok first) :
    SourceAstStatements.statement (fuel + 1) node = .ok out ↔
      ∃ handlers, Each (fun child handler => SourceAstStatements.catchWith fuel
        (SourceAstStatements.blockWith (SourceAstStatements.statement fuel)) child = .ok handler)
        rest handlers ∧ out = .tryStmt call (syntaxList returns) body first (syntaxList handlers) := by
  rw [SourceAstStatements.statement]
  simp only [kind, callField, callValue, clauseField, shape, successKind, successName,
    returnsValue, bodyField, bodyValue, firstValue, ok_bind, beq_self_eq_true,
    pure_bind]
  exact build_ok_iff_each
    (SourceAstStatements.catchWith fuel (SourceAstStatements.blockWith (SourceAstStatements.statement fuel)))
    (fun (handlers : List (Syn (.catchClause .body))) =>
      (Syn.tryStmt call (syntaxList returns) body first (syntaxList handlers) : Syn (.stmt .body)))
    rest out

/-- A successful call conversion cannot hide a missing success/catch pair.
This is the existing conversion gap, not a new Source exclusion. -/
theorem short_clauses_rejected (fuel : Nat) (node rawCall : Json)
    (clauses : Array Json) (call : Syn .expr)
    (kind : node.getObjValAs? String "nodeType" = .ok "TryStatement")
    (callField : node.getObjVal? "externalCall" = .ok rawCall)
    (callValue : SourceAstExpressions.expression fuel rawCall = .ok call)
    (clauseField : node.getObjValAs? (Array Json) "clauses" = .ok clauses)
    (short : clauses.toList = [] ∨ ∃ success, clauses.toList = [success]) :
    SourceAstStatements.statement (fuel + 1) node =
      .error "try requires success and at least one catch" := by
  rcases short with shape | ⟨success, shape⟩
  all_goals
    rw [SourceAstStatements.statement]
    simp only [kind, callField, callValue, clauseField, shape, ok_bind]
    rfl

/-- info: 'Solidity.Lowering.P8.SourceAstTryCorrespondence.try_ok_iff_each' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms try_ok_iff_each
/-- info: 'Solidity.Lowering.P8.SourceAstTryCorrespondence.short_clauses_rejected' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms short_clauses_rejected
end Solidity.Lowering.P8.SourceAstTryCorrespondence
