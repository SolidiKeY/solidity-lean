import Solidity.Frontend.StatementGrammarH28.ContextPr
import Solidity.Frontend.Checked.Prec

/-! Full statement-root discrimination under the existing precedence/path
contract. Expression uniqueness and parser completeness are not premises. -/
namespace Solidity.Frontend.StatementGrammarH28
open Solidity.Source Solidity.Frontend.Checked

def PathParts (parts : List (List Tok)) : Prop := PathTokens parts.flatten

def DeclShape (loc : Option DataLoc) (name : String) (parts : List (List Tok)) : Prop :=
  ∃ ty, AtomPairSafe ty ∧ ty ≠ [] ∧ parts = [ty ++ optToks DataLoc.toks loc ++ idt name]

def SemiFrameParts (parts : List (List Tok)) : Prop :=
  ∀ tail, badStmtTriple (parts.flatten ++ pu .semi ++ tail) = false

def SimpleFrameParts (parts : List (List Tok)) : Prop := SimpleFrameSafe parts.flatten

def RevertFrameParts (parts : List (List Tok)) : Prop :=
  ∀ tail, badStmtTriple (parts.flatten ++ tail) = true

theorem syntax_path_yield {c : Cat} (s : Syn c) :
    s.isPathExpr = true → PrEnsures s.yield PathParts := by
  induction s with
  | ident name =>
    intro _h
    exact ensures_pure _ PathParts ⟨name, [], rfl, Or.inl rfl⟩
  | member e name ihe =>
    intro h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ PathParts PathParts (ihe h)
    intro a ha
    apply ensures_pure _ PathParts
    simpa only [PathParts, List.flatten_cons, List.flatten_nil, List.append_nil] using
      path_append_member ha (if name == "address" then [.elem .address] else idt name)
  | _ => intro h; cases h

theorem var_decl_yield_shape (t : Syn .typeName) (loc : Option DataLoc) (name : String) :
    PrEnsures (Syn.varDecl t loc name).yield (DeclShape loc name) := by
  rw [Syn.yield]
  apply ensures_bind_checked _ _ (fun p => PairParts p ∧ SafeParts p) (DeclShape loc name)
    (ensures_both _ PairParts SafeParts (type_pair_safe t) (type_yield_safe_start t))
  intro a ha
  exact ensures_pure _ (DeclShape loc name) ⟨a.flatten, ha.1, safe_start_nonempty ha.2, rfl⟩

theorem simple_semicolon_frame (s : Syn .simple) : PrEnsures s.yield SemiFrameParts := by
  cases s with
  | exprStmt e =>
    intro L parts M he tail
    exact atom_pair_no_bad_triple (atom_pair_safe_frame parts.flatten (pu .semi) tail
      (expression_pair_safe e L parts M he)
      (safe_start_nonempty (expression_yield_safe_start e L parts M he))
      ⟨_, _, rfl, rfl⟩)
  | declTuple holes decl decls e =>
    rw [Syn.yield]
    apply ensures_bind (P := SemiFrameParts)
    intro a
    apply ensures_bind (P := SemiFrameParts)
    intro b
    apply ensures_bind (P := SemiFrameParts)
    intro c
    exact ensures_pure _ SemiFrameParts (by intro tail; rfl)
  | declVar decl init =>
    cases decl with
    | varDecl t loc name =>
      rw [Syn.yield]
      apply ensures_bind_checked _ _ (DeclShape loc name) SemiFrameParts
        (var_decl_yield_shape t loc name)
      intro a ha
      apply ensures_bind (P := SemiFrameParts)
      intro b
      apply ensures_pure _ SemiFrameParts
      intro tail
      obtain ⟨ty, ht, hn, he⟩ := ha
      subst a
      simpa only [List.flatten_cons, List.flatten_nil, List.append_nil, List.append_assoc] using
        decl_head_no_bad_triple ty loc name b tail ht hn

theorem simple_statement_frame (s : Syn .simple) {k : SCtx} :
    PrEnsures (Syn.simpleStmt (k := k) s).yield SimpleFrameParts := by
  rw [Syn.yield]
  apply ensures_bind_checked _ _ SemiFrameParts SimpleFrameParts (simple_semicolon_frame s)
  intro a ha
  apply ensures_pure _ SimpleFrameParts
  intro tail
  simpa only [List.flatten_cons, List.flatten_nil, List.append_nil] using ha tail

theorem revert_statement_bad_frame {k : SCtx} (e : Syn .expr) (args : Syn .callArgs)
    (hp : e.isPathExpr = true) :
    PrEnsures (Syn.revert (k := k) e args).yield RevertFrameParts := by
  rw [Syn.yield]
  apply ensures_bind_checked _ _ PathParts RevertFrameParts (syntax_path_yield e hp)
  intro a ha
  apply ensures_bind_checked _ _ ParenParts RevertFrameParts (call_args_paren_start args)
  intro b hb
  apply ensures_pure _ RevertFrameParts
  intro tail
  simpa only [List.flatten_cons, List.flatten_nil, List.append_nil, List.append_assoc] using
    revert_bad_triple a.flatten b.flatten tail ha hb

theorem simple_revert_prefix_distinct {k j : SCtx}
    (s : Syn .simple) (e : Syn .expr) (args : Syn .callArgs) (hp : e.isPathExpr = true)
    (L M N P : List Choice) (xs ys : List (List Tok)) (rest tail : List Tok)
    (hs : (Syn.simpleStmt (k := k) s).yield L = some (xs, M))
    (hr : (Syn.revert (k := j) e args).yield N = some (ys, P)) :
    xs.flatten ++ rest ≠ ys.flatten ++ tail := by
  intro he
  have simpleFrame := simple_statement_frame s L xs M hs rest
  have revertFrame := revert_statement_bad_frame e args hp N ys P hr tail
  rw [he, revertFrame] at simpleFrame
  cases simpleFrame

theorem simple_revert_root_prefix_distinct {k j : SCtx}
    (s : Syn (.stmt k)) (t : Syn (.stmt j))
    (hs : root s = .simple) (hr : root t = .revertError) (hp : t.precNode = true)
    (L M N P : List Choice) (xs ys : List (List Tok)) (rest tail : List Tok)
    (hyS : s.yield L = some (xs, M)) (hyT : t.yield N = some (ys, P)) :
    xs.flatten ++ rest ≠ ys.flatten ++ tail := by
  cases s with
  | simpleStmt simple =>
    cases t with
    | revert e args =>
      change e.isPathExpr = true at hp
      exact simple_revert_prefix_distinct simple e args hp L M N P xs ys rest tail hyS hyT
    | _ => cases hr
  | _ => cases hs

/-- Every statement root is distinguished under the existing node contract,
for arbitrary expression/type/argument atoms and layouts. -/
theorem statement_root_unique_node_contract {k j : SCtx}
    (s : Syn (.stmt k)) (t : Syn (.stmt j)) (ps : s.precNode = true) (pt : t.precNode = true)
    (L M N P : List Choice) (xs ys : List (List Tok)) (rest tail : List Tok)
    (hyS : s.yield L = some (xs, M)) (hyT : t.yield N = some (ys, P))
    (he : xs.flatten ++ rest = ys.flatten ++ tail) : root s = root t := by
  rcases statement_root_collision_cases s t L M N P xs ys rest tail hyS hyT he with
    equal | ⟨hs, ht⟩ | ⟨hs, ht⟩
  · exact equal
  · exact False.elim (simple_revert_root_prefix_distinct s t hs ht pt L M N P xs ys rest tail hyS hyT he)
  · exact False.elim (simple_revert_root_prefix_distinct t s ht hs ps N P L M ys xs tail rest hyT hyS he.symm)

/-- Full original precedence/layout contract version; no expression
uniqueness or successful parser premise is required for root discrimination. -/
theorem statement_root_unique {k j : SCtx}
    (s : Syn (.stmt k)) (t : Syn (.stmt j)) (ps : s.prec = true) (pt : t.prec = true)
    (L M N P : List Choice) (xs ys : List (List Tok)) (rest tail : List Tok)
    (hyS : s.yield L = some (xs, M)) (hyT : t.yield N = some (ys, P))
    (he : xs.flatten ++ rest = ys.flatten ++ tail) : root s = root t :=
  statement_root_unique_node_contract s t (Syn.prec_root ps) (Syn.prec_root pt)
    L M N P xs ys rest tail hyS hyT he

#print axioms syntax_path_yield
#print axioms var_decl_yield_shape
#print axioms simple_semicolon_frame
#print axioms simple_statement_frame
#print axioms revert_statement_bad_frame
#print axioms simple_revert_prefix_distinct
#print axioms simple_revert_root_prefix_distinct
#print axioms statement_root_unique_node_contract
#print axioms statement_root_unique
end Solidity.Frontend.StatementGrammarH28
