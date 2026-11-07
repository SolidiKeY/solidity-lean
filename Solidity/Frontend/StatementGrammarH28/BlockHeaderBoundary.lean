import Solidity.Frontend.StatementGrammarH28.RootContract
import Solidity.Frontend.StatementGrammarH28.FramedItemList
import Solidity.Frontend.StatementGrammarH28.BlockLeafCoverage

/-! Intrinsic block/call-options boundary under the existing precedence contract.
Expression/type/argument yields remain read-only atoms; no uniqueness is assumed. -/
namespace Solidity.Frontend.StatementGrammarH28
open Solidity.Source Solidity.Frontend.Checked

def namedArgStart : List Tok → Bool
  | .ident _ :: .punct .colon :: _ => true
  | _ => false

def NoNamedFrame (ts : List Tok) : Prop := ∀ tail, namedArgStart (ts ++ tail) = false

def NoNamedParts (parts : List (List Tok)) : Prop := NoNamedFrame parts.flatten

def BlockBodyParts (parts : List (List Tok)) : Prop := NoNamedFrame (parts.flatten ++ pu .rbrace)

def SimpleNamedParts (parts : List (List Tok)) : Prop :=
  ∀ tail, namedArgStart (parts.flatten ++ pu .semi ++ tail) = false

theorem atom_pair_no_named {ts : List Tok} (h : AtomPairSafe ts) : namedArgStart ts = false := by
  cases ts with
  | nil => rfl
  | cons first rest =>
    cases first with
    | ident name =>
      cases rest with
      | nil => rfl
      | cons second after =>
        cases second with
        | punct p => cases p <;> first | rfl | cases h
        | _ => rfl
    | _ => rfl

theorem nonIdent_no_named_frame {ts : List Tok} (h : NonIdentStart ts) : NoNamedFrame ts :=
  fun tail => atom_pair_no_named (nonIdent_atom_pair_safe (nonIdent_append h tail))

theorem decl_head_no_named (ty : List Tok) (loc : Option DataLoc) (name : String)
    (after : List Tok) (ht : AtomPairSafe ty) (hn : ty ≠ []) :
    namedArgStart ((ty ++ optToks DataLoc.toks loc ++ idt name) ++ after) = false := by
  cases ty with
  | nil => exact False.elim (hn rfl)
  | cons first rest =>
    cases first with
    | ident typeName =>
      cases rest with
      | nil =>
        cases loc with
        | none => rfl
        | some loc => cases loc <;> rfl
      | cons second more => exact atom_pair_no_named ht
    | _ => rfl

theorem simple_statement_no_named (s : Syn .simple) {k : SCtx} :
    PrEnsures (Syn.simpleStmt (k := k) s).yield NoNamedParts := by
  rw [Syn.yield]
  apply ensures_bind_checked _ _ SimpleNamedParts NoNamedParts
  · cases s with
    | exprStmt e =>
      intro L parts M hy tail
      exact atom_pair_no_named (atom_pair_safe_frame parts.flatten (pu .semi) tail
        (expression_pair_safe e L parts M hy)
        (safe_start_nonempty (expression_yield_safe_start e L parts M hy)) ⟨_, _, rfl, rfl⟩)
    | declTuple holes decl decls e =>
      rw [Syn.yield]
      apply ensures_bind (P := SimpleNamedParts)
      intro a
      apply ensures_bind (P := SimpleNamedParts)
      intro b
      apply ensures_bind (P := SimpleNamedParts)
      intro c
      exact ensures_pure _ _ (by intro tail; rfl)
    | declVar decl init =>
      cases decl with
      | varDecl t loc name =>
        rw [Syn.yield]
        apply ensures_bind_checked _ _ (DeclShape loc name) SimpleNamedParts (var_decl_yield_shape t loc name)
        intro a ha
        apply ensures_bind (P := SimpleNamedParts)
        intro b
        apply ensures_pure _ SimpleNamedParts
        intro tail
        obtain ⟨ty, ht, hn, he⟩ := ha
        subst a
        simpa only [List.flatten_cons, List.flatten_nil, List.append_nil, List.append_assoc] using
          decl_head_no_named ty loc name
            ((match b with | [e] => pu .assign ++ e | _ => []) ++ pu .semi ++ tail) ht hn
  · intro a ha
    apply ensures_pure _ NoNamedParts
    intro tail
    simpa only [NoNamedParts, NoNamedFrame, List.flatten_cons, List.flatten_nil,
      List.append_nil] using ha tail

theorem revert_statement_no_named {k : SCtx} (e : Syn .expr) (args : Syn .callArgs)
    (hp : e.isPathExpr = true) :
    PrEnsures (Syn.revert (k := k) e args).yield NoNamedParts := by
  rw [Syn.yield]
  apply ensures_bind_checked _ _ PathParts NoNamedParts (syntax_path_yield e hp)
  intro a ha
  apply ensures_bind
  intro b
  apply ensures_pure
  intro tail
  obtain ⟨name, after, he, shape⟩ := ha
  simp only [NoNamedParts, NoNamedFrame, List.flatten_cons, List.flatten_nil, List.append_nil]
  rw [he]
  rfl

theorem statement_no_named {k : SCtx} (s : Syn (.stmt k)) (hp : s.precNode = true) :
    PrEnsures s.yield NoNamedParts := by
  by_cases simple : root s = .simple
  · cases s with
    | simpleStmt a => exact simple_statement_no_named a
    | _ => cases simple
  · by_cases revert : root s = .revertError
    · cases s with
      | revert e args => exact revert_statement_no_named e args hp
      | _ => cases revert
    · obtain ⟨tok, ht, hh⟩ := root_hard_token (root s) simple revert
      have nonIdent : identToken tok = false := by
        cases tok <;> first | rfl | cases hh
      intro L parts M hy tail
      have head := statement_fixed_head s tok ht L parts M hy
      change parts.flatten.head? = some tok at head
      have start : NonIdentStart parts.flatten := by
        cases he : parts.flatten with
        | nil => rw [he] at head; cases head
        | cons t rest =>
          rw [he] at head
          have eq : t = tok := Option.some.inj head
          subst t
          exact ⟨tok, rest, rfl, nonIdent⟩
      exact nonIdent_no_named_frame start tail

theorem statement_all_root {k : SCtx} (s : Syn (.stmt k))
    (h : s.all Syn.precNode = true) : s.precNode = true := by
  cases s with
  | ifStmt c t e =>
    change ((((Syn.ifStmt c t e).precNode && c.all Syn.precNode) && t.all Syn.precNode) &&
      e.all Syn.precNode) = true at h
    simp only [Bool.and_eq_true] at h
    exact h.1.1.1
  | emit e args =>
    change (((Syn.emit e args).precNode && e.all Syn.precNode) && args.all Syn.precNode) = true at h
    simp only [Bool.and_eq_true] at h
    exact h.1.1
  | revert e args =>
    change (((Syn.revert e args).precNode && e.all Syn.precNode) && args.all Syn.precNode) = true at h
    simp only [Bool.and_eq_true] at h
    exact h.1.1
  | _ => rfl

theorem item_no_named {k : SCtx} (x : Syn (.item k)) (h : x.all Syn.precNode = true) :
    PrEnsures x.yield NoNamedParts := by
  cases x with
  | stmtItem s =>
    have hs : s.all Syn.precNode = true := by
      change ((Syn.stmtItem s).precNode && s.all Syn.precNode) = true at h
      simp only [Bool.and_eq_true] at h
      exact h.2
    exact statement_no_named s (statement_all_root s hs)
  | uncheckedItem b =>
    rw [Syn.yield]
    apply ensures_bind
    intro parts
    exact ensures_pure _ NoNamedParts (by intro tail; rfl)

theorem item_list_no_named_body {k : SCtx} (xs : Syn (.list (.item k)))
    (h : xs.all Syn.precNode = true) :
    PrEnsures xs.yield BlockBodyParts := by
  cases xs with
  | nil => exact ensures_pure _ _ (by intro tail; rfl)
  | cons x xs =>
    have hx : x.all Syn.precNode = true := by
      change (((Syn.cons x xs).precNode && x.all Syn.precNode) && xs.all Syn.precNode) = true at h
      simp only [Bool.and_eq_true] at h
      exact h.1.2
    rw [Syn.yield]
    apply ensures_bind_checked _ _ NoNamedParts BlockBodyParts (item_no_named x hx)
    intro a ha
    apply ensures_bind (P := BlockBodyParts)
    intro b
    apply ensures_pure _ BlockBodyParts
    intro tail
    simpa only [BlockBodyParts, NoNamedParts, NoNamedFrame, List.flatten_cons, List.append_assoc] using
      ha (b.flatten ++ pu .rbrace ++ tail)

theorem block_items_no_named_body {k : SCtx} (xs : Syn (.list (.item k)))
    (hp : (Syn.block xs).prec = true) :
    PrEnsures xs.yield BlockBodyParts := by
  have hb : (Syn.block xs).all Syn.precNode = true := by
    change ((Syn.block xs).precNode && (Syn.block xs).all Syn.precNode) = true at hp
    simp only [Bool.and_eq_true] at hp
    exact hp.2
  have hi : xs.all Syn.precNode = true := by
    change ((Syn.block xs).precNode && xs.all Syn.precNode) = true at hb
    simp only [Bool.and_eq_true] at hb
    exact hb.2
  exact item_list_no_named_body xs hi

/-- After removing a yielded block's opening brace, no arbitrary continuation
can turn the first two tokens into a named call-option field. -/
theorem block_yield_no_named_header {k : SCtx} (b : Syn (.block k)) (hp : b.prec = true)
    (L M : List Choice) (parts : List (List Tok))
    (hy : b.yield L = some (parts, M)) : NoNamedFrame (parts.flatten.drop 1) := by
  cases b with
  | block xs =>
    obtain ⟨body, hb, he⟩ := block_yield_decompose xs L M parts hy
    rw [he]
    have boundary := block_items_no_named_body xs hp L body M hb
    simpa only [BlockBodyParts, List.flatten_cons, List.flatten_nil, List.append_nil,
      braces, pu, List.cons_append, List.nil_append, List.drop_succ_cons, List.drop_zero] using boundary

/-- The actual postfix parser stops at an opening brace unless its next two
located tokens form an identifier/colon pair. -/
theorem postLoop_no_named_lookahead (n : Nat) (e : Syn .expr) (s : St)
    (hbrace : s.ts.head?.map (fun t : Located => t.tok) = some (.punct .lbrace))
    (hpair : namedArgStart ((s.ts.drop 1).map (fun t : Located => t.tok)) = false) :
    postLoop (n + 1) e s = .ok (e, s) := by
  cases s with
  | mk tokens ch eof =>
    cases tokens with
    | nil => cases hbrace
    | cons first rest =>
      cases first with
      | mk tok a b =>
        have ht : tok = .punct .lbrace := Option.some.inj hbrace
        subst tok
        cases rest with
        | nil => rfl
        | cons second rest =>
          cases rest with
          | nil => rfl
          | cons third rest =>
            cases second with
            | mk tok1 c d =>
              cases third with
              | mk tok2 f g =>
                by_cases colon : tok2 = .punct .colon
                · subst tok2
                  cases tok1 <;> first | rfl | cases hpair
                · have hb : ((some tok2 : Option Tok) == some (.punct .colon)) = false :=
                    beq_eq_false_iff_ne.mpr (by intro bad; exact colon (Option.some.inj bad))
                  rw [postLoop]
                  change ((if ((some tok2 : Option Tok) == some (.punct .colon)) then _
                    else pure e) : P (Syn .expr)) _ = _
                  rw [hb]
                  rfl

/-- For every actual precedence-selected block yield, the existing postfix
parser preserves the entire block and arbitrary suffix, at every positive fuel. -/
theorem postLoop_yielded_block {k : SCtx} (b : Syn (.block k)) (hp : b.prec = true)
    (L M : List Choice) (parts : List (List Tok))
    (hy : b.yield L = some (parts, M)) (n : Nat) (e : Syn .expr) (s : St) :
    postLoop (n + 1) e (locatedInput parts.flatten s) =
      .ok (e, locatedInput parts.flatten s) := by
  cases b with
  | block xs =>
    obtain ⟨body, hb, he⟩ := block_yield_decompose xs L M parts hy
    subst parts
    apply postLoop_no_named_lookahead
    · rfl
    · have boundary := block_items_no_named_body xs hp L body M hb
      simpa only [BlockBodyParts, NoNamedFrame, locatedInput, atToken, braces, pu,
        List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append,
        List.nil_append, List.drop_succ_cons, List.drop_zero, List.map_append,
        List.map_cons, List.map_nil, List.map_map, Function.comp_def, List.map_id, List.map_id',
        List.append_assoc] using boundary (s.ts.map (fun t : Located => t.tok))

#print axioms atom_pair_no_named
#print axioms nonIdent_no_named_frame
#print axioms decl_head_no_named
#print axioms simple_statement_no_named
#print axioms revert_statement_no_named
#print axioms statement_no_named
#print axioms statement_all_root
#print axioms item_no_named
#print axioms item_list_no_named_body
#print axioms block_items_no_named_body
#print axioms block_yield_no_named_header
#print axioms postLoop_no_named_lookahead
#print axioms postLoop_yielded_block
end Solidity.Frontend.StatementGrammarH28
