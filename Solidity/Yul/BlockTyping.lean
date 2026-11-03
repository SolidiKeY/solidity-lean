import Solidity.Yul.ScopedBlockTyping

/-!
# Closed-root compatibility for the shared intrinsic Yul checker

The implementation now lives in ScopedBlockTyping. All entry points below are
the concrete closed-scope specialization; constructor field types reduce to
the original ExprD/AssignmentD. No second traversal or Source state is kept.
This remains preparation, not Solidity assembly admission.
-/
namespace Solidity.Yul.BlockTyping
open Solidity.Source (Syn Cat)

abbrev InitializerD {F n} (E : Env F n) (count : Nat) (term : Syn (.opt .yulExpr)) :=
  ScopedBlockTyping.InitializerD BlockScope.Scope.closed E count term
abbrev BlockD {F n} (E : Env F n) (c : Control) (body : Syn (.list .yulStmt)) :=
  ScopedBlockTyping.BlockD BlockScope.Scope.closed E c body
abbrev WalkD {F n} (E : Env F n) (c : Control) (body : Syn (.list .yulStmt)) {m} (final : Env F m) :=
  ScopedBlockTyping.WalkD BlockScope.Scope.closed E c body final
abbrev StatementD {F n} (E : Env F n) (c : Control) (term : Syn .yulStmt) {m} (final : Env F m) :=
  ScopedBlockTyping.StatementD BlockScope.Scope.closed E c term final
abbrev CaseD {F n} (E : Env F n) (c : Control) (term : Syn .yulCase) (w : Word) :=
  ScopedBlockTyping.CaseD BlockScope.Scope.closed E c term w
abbrev CasesD {F n} (E : Env F n) (c : Control) (term : Syn (.list .yulCase)) (words : List Word) :=
  ScopedBlockTyping.CasesD BlockScope.Scope.closed E c term words
abbrev DefaultD {F n} (E : Env F n) (c : Control) (term : Syn (.opt (.list .yulStmt))) :=
  ScopedBlockTyping.DefaultD BlockScope.Scope.closed E c term

abbrev StatementCheck (term : Syn .yulStmt) := ScopedBlockTyping.StatementCheck .closed term
abbrev WalkCheck (term : Syn (.list .yulStmt)) := ScopedBlockTyping.WalkCheck .closed term
abbrev Result (category : Cat) (term : Syn category) := ScopedBlockTyping.Result .closed category term

abbrev blockWith {body : Syn (.list .yulStmt)} (walk : WalkCheck body)
    {F n} (E : Env F n) (c : Control) :=
  ScopedBlockTyping.blockWith .closed walk E c
abbrev checkExpr {F n} (E : Env F n) (count : Nat) (expression : Syn .yulExpr) :=
  ScopedBlockTyping.checkExpr .closed E count expression
abbrev checkInitializer {F n} (E : Env F n) (count : Nat) (term : Syn (.opt .yulExpr)) :=
  ScopedBlockTyping.checkInitializer .closed E count term
abbrev checkNode {category : Cat} (term : Syn category) : Result category term :=
  ScopedBlockTyping.checkNode .closed term
abbrev checkBlock {F n} (E : Env F n) (c : Control) (body : Syn (.list .yulStmt)) :=
  ScopedBlockTyping.checkBlock .closed E c body
abbrev checkWalk {F n} (E : Env F n) (c : Control) (body : Syn (.list .yulStmt)) :=
  ScopedBlockTyping.checkWalk .closed E c body
abbrev checkStatement {F n} (E : Env F n) (c : Control) (term : Syn .yulStmt) :=
  ScopedBlockTyping.checkStatement .closed E c term

theorem checkExpr_complete {F n E expression count}
    (d : @ExprD F [] n (Env.reads E) expression count) :
    checkExpr E count expression = some d :=
  ScopedBlockTyping.checkExpr_complete (scope := .closed) (E := E) d

theorem InitializerD.complete {F n E count term} (d : @InitializerD F n E count term) :
    checkNode term E count = some d := ScopedBlockTyping.InitializerD.complete d
theorem checkInitializer_agrees {F n} (E : Env F n) (count : Nat) (term : Syn (.opt .yulExpr)) :
    checkInitializer E count term = checkNode term E count :=
  ScopedBlockTyping.checkInitializer_agrees .closed E count term
theorem InitializerD.fixed_complete {F n E count term} (d : @InitializerD F n E count term) :
    checkInitializer E count term = some d := ScopedBlockTyping.InitializerD.fixed_complete d

theorem blockWith_complete {F n E c body headers m final}
    (headersD : HeadersD body headers) (walk : WalkCheck body)
    (d : @WalkD (headers.map Prod.snd ++ F) n (Env.hoist E headers) c body m final)
    (hw : walk (E.hoist headers) c = some ⟨m, final, d⟩) :
    blockWith walk E c = some (.intro headersD d) :=
  ScopedBlockTyping.blockWith_complete headersD walk d hw

theorem BlockD.complete {F n E c body} (d : @BlockD F n E c body) :
    checkBlock E c body = some d := ScopedBlockTyping.BlockD.complete d
theorem WalkD.complete {F n E c body m final} (d : @WalkD F n E c body m final) :
    checkWalk E c body = some ⟨m, final, d⟩ := ScopedBlockTyping.WalkD.complete d
theorem StatementD.complete {F n E c term m final} (d : @StatementD F n E c term m final) :
    checkStatement E c term = some ⟨m, final, d⟩ := ScopedBlockTyping.StatementD.complete d
theorem CaseD.complete {F n E c term w} (d : @CaseD F n E c term w) :
    checkNode term E c = some ⟨w, d⟩ := ScopedBlockTyping.CaseD.complete d
theorem CasesD.complete {F n E c term words} (d : @CasesD F n E c term words) :
    checkNode term E c = some ⟨words, d⟩ := ScopedBlockTyping.CasesD.complete d
theorem DefaultD.complete {F n E c term} (d : @DefaultD F n E c term) :
    checkNode term E c = some d := ScopedBlockTyping.DefaultD.complete d

theorem checkBlock_iff {F n} (E : Env F n) (c : Control) (body : Syn (.list .yulStmt)) :
    (checkBlock E c body).isSome = true ↔ Nonempty (BlockD E c body) :=
  ScopedBlockTyping.checkBlock_iff .closed E c body

end Solidity.Yul.BlockTyping
