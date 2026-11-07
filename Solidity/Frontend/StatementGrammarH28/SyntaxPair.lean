import Solidity.Frontend.StatementGrammarH28.PairPr

/-! H31 two-token invariants of existing expression/type/argument yields.
No expression uniqueness or producer interface change is used. -/
namespace Solidity.Frontend.StatementGrammarH28
open Solidity.Source Solidity.Frontend.Checked

def PairParts (parts : List (List Tok)) : Prop := AtomPairSafe parts.flatten
def ParenParts (parts : List (List Tok)) : Prop := ParenStart parts.flatten

def PairInvariant : Cat → List (List Tok) → Prop
  | .expr | .typeName => PairParts
  | .callArgs => ParenParts
  | _ => fun _ => True

theorem syntax_pair_invariant {c : Cat} (s : Syn c) : PrEnsures s.yield (PairInvariant c) := by
  induction s with
  | positional es ihes =>
    rw [Syn.yield]
    apply ensures_bind (P := ParenParts)
    intro a
    exact ensures_pure _ ParenParts (by exact ⟨_, rfl⟩)
  | named args ihargs =>
    rw [Syn.yield]
    apply ensures_bind (P := ParenParts)
    intro a
    exact ensures_pure _ ParenParts (by exact ⟨_, rfl⟩)
  | elem e =>
    rw [Syn.yield]
    apply ensures_pure _ PairParts
    simpa only [PairParts, List.flatten_cons, List.flatten_nil, List.append_nil] using
      nonIdent_atom_pair_safe (elem_nonIdent e)
  | fnType ps vis mu rets ihps ihrets =>
    rw [Syn.yield]
    apply ensures_bind (P := PairParts)
    intro order
    apply ensures_bind (P := PairParts)
    intro p
    apply ensures_bind (P := PairParts)
    intro attrs
    apply ensures_bind (P := PairParts)
    intro r
    exact ensures_pure _ PairParts (by rfl)
  | mapping key kn v vn ihv =>
    cases key with
    | elem e _he =>
      rw [Syn.yield]
      apply ensures_bind (P := PairParts)
      intro a
      exact ensures_pure _ PairParts (by rfl)
    | path p =>
      rw [Syn.yield]
      apply ensures_bind (P := PairParts)
      intro a
      exact ensures_pure _ PairParts (by rfl)
  | userType p =>
    rw [Syn.yield]
    apply ensures_pure _ PairParts
    simpa only [PairParts, List.flatten_cons, List.flatten_nil, List.append_nil] using path_atom_pair_safe p
  | array t len iht ihlen =>
    rw [Syn.yield]
    apply ensures_bind_checked _ _ (fun p => PairParts p ∧ SafeParts p) PairParts
      (ensures_both _ PairParts SafeParts iht (type_yield_safe_start t))
    intro a ha
    apply ensures_bind (P := PairParts)
    intro b
    apply ensures_pure _ PairParts
    simpa only [PairParts, List.flatten_cons, List.flatten_nil, List.append_nil, List.append_assoc] using
      atom_pair_safe_frame a.flatten (pu .lbrack) (b.flatten ++ pu .rbrack) ha.1 (safe_start_nonempty ha.2) (⟨_, _, rfl, rfl⟩)
  | index e i ihe ihi =>
    rw [Syn.yield]
    apply ensures_bind_checked _ _ (fun p => PairParts p ∧ SafeParts p) PairParts
      (ensures_both _ PairParts SafeParts ihe (expression_yield_safe_start e))
    intro a ha
    apply ensures_bind (P := PairParts)
    intro b
    apply ensures_pure _ PairParts
    simpa only [PairParts, List.flatten_cons, List.flatten_nil, List.append_nil, List.append_assoc] using
      atom_pair_safe_frame a.flatten (pu .lbrack) (b.flatten ++ pu .rbrack) ha.1 (safe_start_nonempty ha.2) (⟨_, _, rfl, rfl⟩)
  | slice e i j ihe ihi ihj =>
    rw [Syn.yield]
    apply ensures_bind_checked _ _ (fun p => PairParts p ∧ SafeParts p) PairParts
      (ensures_both _ PairParts SafeParts ihe (expression_yield_safe_start e))
    intro a ha
    apply ensures_bind (P := PairParts)
    intro b
    apply ensures_bind (P := PairParts)
    intro c
    apply ensures_pure _ PairParts
    simpa only [PairParts, List.flatten_cons, List.flatten_nil, List.append_nil, List.append_assoc] using
      atom_pair_safe_frame a.flatten (pu .lbrack) (b.flatten ++ pu .colon ++ c.flatten ++ pu .rbrack) ha.1 (safe_start_nonempty ha.2) (⟨_, _, rfl, rfl⟩)
  | member e name ihe =>
    rw [Syn.yield]
    apply ensures_bind_checked _ _ (fun p => PairParts p ∧ SafeParts p) PairParts
      (ensures_both _ PairParts SafeParts ihe (expression_yield_safe_start e))
    intro a ha
    apply ensures_pure _ PairParts
    simpa only [PairParts, List.flatten_cons, List.flatten_nil, List.append_nil, List.append_assoc] using
      atom_pair_safe_frame a.flatten (pu .period) (if name == "address" then [.elem .address] else idt name) ha.1 (safe_start_nonempty ha.2) (⟨_, _, rfl, rfl⟩)
  | callOptions e arg args ihe iharg ihargs =>
    rw [Syn.yield]
    apply ensures_bind_checked _ _ (fun p => PairParts p ∧ SafeParts p) PairParts
      (ensures_both _ PairParts SafeParts ihe (expression_yield_safe_start e))
    intro a ha
    apply ensures_bind (P := PairParts)
    intro b
    apply ensures_bind (P := PairParts)
    intro c
    apply ensures_pure _ PairParts
    simpa only [PairParts, List.flatten_cons, List.flatten_nil, List.append_nil, List.append_assoc] using
      atom_pair_safe_frame a.flatten (braces (commaSep (b.flatten :: c))) ([]) ha.1 (safe_start_nonempty ha.2) (⟨_, _, rfl, rfl⟩)
  | call e args ihe ihargs =>
    rw [Syn.yield]
    apply ensures_bind_checked _ _ (fun p => PairParts p ∧ SafeParts p) PairParts
      (ensures_both _ PairParts SafeParts ihe (expression_yield_safe_start e))
    intro a ha
    apply ensures_bind_checked _ _ ParenParts PairParts ihargs
    intro b hb
    apply ensures_pure _ PairParts
    simpa only [PairParts, List.flatten_cons, List.flatten_nil, List.append_nil, List.append_assoc] using
      atom_pair_safe_frame a.flatten (b.flatten) ([]) ha.1 (safe_start_nonempty ha.2) (paren_separator hb)
  | payableConv args ihargs =>
    rw [Syn.yield]
    apply ensures_bind (P := PairParts)
    intro a
    exact ensures_pure _ PairParts (by rfl)
  | metaType t iht =>
    rw [Syn.yield]
    apply ensures_bind (P := PairParts)
    intro a
    exact ensures_pure _ PairParts (by rfl)
  | unaryPrefix op e ihe =>
    rw [Syn.yield]
    apply ensures_bind (P := PairParts)
    intro a
    apply ensures_pure _ PairParts
    simpa only [PairParts, List.flatten_cons, List.flatten_nil, List.append_nil] using
      nonIdent_atom_pair_safe (nonIdent_append (prefix_nonIdent op) a.flatten)
  | unarySuffix op e ihe =>
    rw [Syn.yield]
    apply ensures_bind_checked _ _ (fun p => PairParts p ∧ SafeParts p) PairParts
      (ensures_both _ PairParts SafeParts ihe (expression_yield_safe_start e))
    intro a ha
    apply ensures_pure _ PairParts
    simpa only [PairParts, List.flatten_cons, List.flatten_nil, List.append_nil, List.append_assoc] using
      atom_pair_safe_frame a.flatten (pu op.punct) ([]) ha.1 (safe_start_nonempty ha.2) (suffix_separator op)
  | exp left right ihleft ihright =>
    rw [Syn.yield]
    apply ensures_bind_checked _ _ (fun p => PairParts p ∧ SafeParts p) PairParts
      (ensures_both _ PairParts SafeParts ihleft (expression_yield_safe_start left))
    intro a ha
    apply ensures_bind (P := PairParts)
    intro b
    apply ensures_pure _ PairParts
    simpa only [PairParts, List.flatten_cons, List.flatten_nil, List.append_nil, List.append_assoc] using
      atom_pair_safe_frame a.flatten (pu .exp) (b.flatten) ha.1 (safe_start_nonempty ha.2) (⟨_, _, rfl, rfl⟩)
  | mulDivMod op left right ihleft ihright =>
    rw [Syn.yield]
    apply ensures_bind_checked _ _ (fun p => PairParts p ∧ SafeParts p) PairParts
      (ensures_both _ PairParts SafeParts ihleft (expression_yield_safe_start left))
    intro a ha
    apply ensures_bind (P := PairParts)
    intro b
    apply ensures_pure _ PairParts
    simpa only [PairParts, List.flatten_cons, List.flatten_nil, List.append_nil, List.append_assoc] using
      atom_pair_safe_frame a.flatten (pu op.punct) (b.flatten) ha.1 (safe_start_nonempty ha.2) (mul_separator op)
  | addSub op left right ihleft ihright =>
    rw [Syn.yield]
    apply ensures_bind_checked _ _ (fun p => PairParts p ∧ SafeParts p) PairParts
      (ensures_both _ PairParts SafeParts ihleft (expression_yield_safe_start left))
    intro a ha
    apply ensures_bind (P := PairParts)
    intro b
    apply ensures_pure _ PairParts
    simpa only [PairParts, List.flatten_cons, List.flatten_nil, List.append_nil, List.append_assoc] using
      atom_pair_safe_frame a.flatten (pu op.punct) (b.flatten) ha.1 (safe_start_nonempty ha.2) (add_separator op)
  | shift op left right ihleft ihright =>
    rw [Syn.yield]
    apply ensures_bind_checked _ _ (fun p => PairParts p ∧ SafeParts p) PairParts
      (ensures_both _ PairParts SafeParts ihleft (expression_yield_safe_start left))
    intro a ha
    apply ensures_bind (P := PairParts)
    intro b
    apply ensures_pure _ PairParts
    simpa only [PairParts, List.flatten_cons, List.flatten_nil, List.append_nil, List.append_assoc] using
      atom_pair_safe_frame a.flatten (pu op.punct) (b.flatten) ha.1 (safe_start_nonempty ha.2) (shift_separator op)
  | bitAnd left right ihleft ihright =>
    rw [Syn.yield]
    apply ensures_bind_checked _ _ (fun p => PairParts p ∧ SafeParts p) PairParts
      (ensures_both _ PairParts SafeParts ihleft (expression_yield_safe_start left))
    intro a ha
    apply ensures_bind (P := PairParts)
    intro b
    apply ensures_pure _ PairParts
    simpa only [PairParts, List.flatten_cons, List.flatten_nil, List.append_nil, List.append_assoc] using
      atom_pair_safe_frame a.flatten (pu .bitAnd) (b.flatten) ha.1 (safe_start_nonempty ha.2) (⟨_, _, rfl, rfl⟩)
  | bitXor left right ihleft ihright =>
    rw [Syn.yield]
    apply ensures_bind_checked _ _ (fun p => PairParts p ∧ SafeParts p) PairParts
      (ensures_both _ PairParts SafeParts ihleft (expression_yield_safe_start left))
    intro a ha
    apply ensures_bind (P := PairParts)
    intro b
    apply ensures_pure _ PairParts
    simpa only [PairParts, List.flatten_cons, List.flatten_nil, List.append_nil, List.append_assoc] using
      atom_pair_safe_frame a.flatten (pu .bitXor) (b.flatten) ha.1 (safe_start_nonempty ha.2) (⟨_, _, rfl, rfl⟩)
  | bitOr left right ihleft ihright =>
    rw [Syn.yield]
    apply ensures_bind_checked _ _ (fun p => PairParts p ∧ SafeParts p) PairParts
      (ensures_both _ PairParts SafeParts ihleft (expression_yield_safe_start left))
    intro a ha
    apply ensures_bind (P := PairParts)
    intro b
    apply ensures_pure _ PairParts
    simpa only [PairParts, List.flatten_cons, List.flatten_nil, List.append_nil, List.append_assoc] using
      atom_pair_safe_frame a.flatten (pu .bitOr) (b.flatten) ha.1 (safe_start_nonempty ha.2) (⟨_, _, rfl, rfl⟩)
  | order op left right ihleft ihright =>
    rw [Syn.yield]
    apply ensures_bind_checked _ _ (fun p => PairParts p ∧ SafeParts p) PairParts
      (ensures_both _ PairParts SafeParts ihleft (expression_yield_safe_start left))
    intro a ha
    apply ensures_bind (P := PairParts)
    intro b
    apply ensures_pure _ PairParts
    simpa only [PairParts, List.flatten_cons, List.flatten_nil, List.append_nil, List.append_assoc] using
      atom_pair_safe_frame a.flatten (pu op.punct) (b.flatten) ha.1 (safe_start_nonempty ha.2) (order_separator op)
  | equality op left right ihleft ihright =>
    rw [Syn.yield]
    apply ensures_bind_checked _ _ (fun p => PairParts p ∧ SafeParts p) PairParts
      (ensures_both _ PairParts SafeParts ihleft (expression_yield_safe_start left))
    intro a ha
    apply ensures_bind (P := PairParts)
    intro b
    apply ensures_pure _ PairParts
    simpa only [PairParts, List.flatten_cons, List.flatten_nil, List.append_nil, List.append_assoc] using
      atom_pair_safe_frame a.flatten (pu op.punct) (b.flatten) ha.1 (safe_start_nonempty ha.2) (equality_separator op)
  | and left right ihleft ihright =>
    rw [Syn.yield]
    apply ensures_bind_checked _ _ (fun p => PairParts p ∧ SafeParts p) PairParts
      (ensures_both _ PairParts SafeParts ihleft (expression_yield_safe_start left))
    intro a ha
    apply ensures_bind (P := PairParts)
    intro b
    apply ensures_pure _ PairParts
    simpa only [PairParts, List.flatten_cons, List.flatten_nil, List.append_nil, List.append_assoc] using
      atom_pair_safe_frame a.flatten (pu .and) (b.flatten) ha.1 (safe_start_nonempty ha.2) (⟨_, _, rfl, rfl⟩)
  | or left right ihleft ihright =>
    rw [Syn.yield]
    apply ensures_bind_checked _ _ (fun p => PairParts p ∧ SafeParts p) PairParts
      (ensures_both _ PairParts SafeParts ihleft (expression_yield_safe_start left))
    intro a ha
    apply ensures_bind (P := PairParts)
    intro b
    apply ensures_pure _ PairParts
    simpa only [PairParts, List.flatten_cons, List.flatten_nil, List.append_nil, List.append_assoc] using
      atom_pair_safe_frame a.flatten (pu .or) (b.flatten) ha.1 (safe_start_nonempty ha.2) (⟨_, _, rfl, rfl⟩)
  | assign op left right ihleft ihright =>
    rw [Syn.yield]
    apply ensures_bind_checked _ _ (fun p => PairParts p ∧ SafeParts p) PairParts
      (ensures_both _ PairParts SafeParts ihleft (expression_yield_safe_start left))
    intro a ha
    apply ensures_bind (P := PairParts)
    intro b
    apply ensures_pure _ PairParts
    simpa only [PairParts, List.flatten_cons, List.flatten_nil, List.append_nil, List.append_assoc] using
      atom_pair_safe_frame a.flatten (pu op.punct) (b.flatten) ha.1 (safe_start_nonempty ha.2) (assign_separator op)
  | cond c yes no ihc ihyes ihno =>
    rw [Syn.yield]
    apply ensures_bind_checked _ _ (fun p => PairParts p ∧ SafeParts p) PairParts
      (ensures_both _ PairParts SafeParts ihc (expression_yield_safe_start c))
    intro a ha
    apply ensures_bind (P := PairParts)
    intro b
    apply ensures_bind (P := PairParts)
    intro c
    apply ensures_pure _ PairParts
    simpa only [PairParts, List.flatten_cons, List.flatten_nil, List.append_nil, List.append_assoc] using
      atom_pair_safe_frame a.flatten (pu .question) (b.flatten ++ pu .colon ++ c.flatten) ha.1 (safe_start_nonempty ha.2) (⟨_, _, rfl, rfl⟩)
  | new t iht =>
    rw [Syn.yield]
    apply ensures_bind (P := PairParts)
    intro a
    exact ensures_pure _ PairParts (by rfl)
  | tuple first rest ihfirst ihrest =>
    rw [Syn.yield]
    apply ensures_bind (P := PairParts)
    intro a
    apply ensures_bind (P := PairParts)
    intro b
    exact ensures_pure _ PairParts (by rfl)
  | inlineArray first rest ihfirst ihrest =>
    rw [Syn.yield]
    apply ensures_bind (P := PairParts)
    intro a
    apply ensures_bind (P := PairParts)
    intro b
    exact ensures_pure _ PairParts (by rfl)
  | ident name =>
    rw [Syn.yield]
    exact ensures_pure _ PairParts (by rfl)
  | lit lit =>
    rw [Syn.yield]
    apply ensures_bind_checked _ _ NonIdentStart PairParts (litP_nonIdent lit)
    intro ts ht
    apply ensures_pure _ PairParts
    simpa only [PairParts, List.flatten_cons, List.flatten_nil, List.append_nil] using
      nonIdent_atom_pair_safe ht
  | litUnit n u =>
    rw [Syn.yield]
    exact ensures_pure _ PairParts (by rfl)
  | elemType e he =>
    rw [Syn.yield]
    exact ensures_pure _ PairParts (by rfl)
  | _ => intro L parts M _h; trivial

theorem expression_pair_safe (e : Syn .expr) : PrEnsures e.yield PairParts := syntax_pair_invariant e

theorem type_pair_safe (t : Syn .typeName) : PrEnsures t.yield PairParts := syntax_pair_invariant t

theorem call_args_paren_start (args : Syn .callArgs) : PrEnsures args.yield ParenParts :=
  syntax_pair_invariant args

#print axioms syntax_pair_invariant
#print axioms expression_pair_safe
#print axioms type_pair_safe
#print axioms call_args_paren_start
end Solidity.Frontend.StatementGrammarH28
