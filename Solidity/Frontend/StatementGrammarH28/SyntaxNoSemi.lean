import Solidity.Frontend.StatementGrammarH28.NoSemiAtoms

/-! All successful yields in the full expression/type/argument/simple-statement
closure are semicolon-free. No expression uniqueness or parse success premise. -/
namespace Solidity.Frontend.StatementGrammarH28
open Solidity.Source Solidity.Frontend.Checked

def SemiFreeCat : Cat → Bool
  | .callArgs | .namedArg | .param | .typeName | .varDecl | .expr | .simple
    => true
  | .list c | .opt c => SemiFreeCat c
  | _ => false

theorem syntax_yield_semiFree {c : Cat} (s : Syn c) :
    SemiFreeCat c = true → PrEnsures s.yield SemiFreeParts := by
  induction s with
  | nil => intro _h; exact ensures_pure _ SemiFreeParts semiFreeParts_nil
  | cons x xs ihx ihxs =>
    intro h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ SemiFreeParts SemiFreeParts (ihx h)
    intro a ha
    apply ensures_bind_checked _ _ SemiFreeParts SemiFreeParts (ihxs h)
    intro b hb
    exact ensures_pure _ SemiFreeParts (semiFreeParts_cons (semiFreeParts_flat ha) hb)
  | none => intro _h; exact ensures_pure _ SemiFreeParts semiFreeParts_nil
  | some x ihx =>
    intro h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ SemiFreeParts SemiFreeParts (ihx h)
    intro a ha
    exact ensures_pure _ SemiFreeParts (semiFreeParts_singleton (semiFreeParts_flat ha))
  | positional es ihes =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ SemiFreeParts SemiFreeParts (ihes rfl)
    intro a ha
    exact ensures_pure _ SemiFreeParts (semiFreeParts_singleton (semiFree_parens (semiFree_commaSep a ha)))
  | named args ihargs =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ SemiFreeParts SemiFreeParts (ihargs rfl)
    intro a ha
    exact ensures_pure _ SemiFreeParts (semiFreeParts_singleton (semiFree_parens (.wrap (semiFree_commaSep a ha))))
  | namedArg name e ihe =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ SemiFreeParts SemiFreeParts (ihe rfl)
    intro a ha
    exact ensures_pure _ SemiFreeParts (semiFreeParts_singleton (.append (.append (semiFree_id name) (semiFree_punct .colon (by intro h; cases h))) (semiFreeParts_flat ha)))
  | param t loc name iht =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ SemiFreeParts SemiFreeParts (iht rfl)
    intro a ha
    exact ensures_pure _ SemiFreeParts (semiFreeParts_singleton (.append (.append (semiFreeParts_flat ha) (semiFree_optToks DataLoc.toks semiFree_dataLoc loc)) (semiFree_optToks idt semiFree_id name)))
  | elem e =>
    intro _h
    rw [Syn.yield]
    exact ensures_pure _ SemiFreeParts (semiFreeParts_singleton (semiFree_elem e))
  | fnType ps vis mu rets ihps ihrets =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind (P := SemiFreeParts)
    intro order
    apply ensures_bind_checked _ _ SemiFreeParts SemiFreeParts (ihps rfl)
    intro a ha
    have hv := semiFree_optToks Visibility.toks semiFree_visibility vis
    have hm := semiFree_optToks Mutability.toks semiFree_mutability mu
    have singles : ∀ pair ∈ (single .vis (optToks Visibility.toks vis) ++
        single .mutab (optToks Mutability.toks mu)), SemiFree pair.2 := by
      intro pair hp
      cases List.mem_append.mp hp with
      | inl h => exact semiFree_single _ _ hv pair h
      | inr h => exact semiFree_single _ _ hm pair h
    apply ensures_bind_checked _ _ SemiFree SemiFreeParts
      (attrsP_empty_mods_semiFree _ singles order)
    intro attrs hattrs
    apply ensures_bind_checked _ _ SemiFreeParts SemiFreeParts (ihrets rfl)
    intro r hr
    exact ensures_pure _ SemiFreeParts (semiFreeParts_singleton
      (.append (.append (.append (semiFree_kw .function)
        (semiFree_parens (semiFree_commaSep a ha))) hattrs)
        (semiFree_choice r.isEmpty .empty
          (.append (semiFree_kw .returns) (semiFree_parens (semiFree_commaSep r hr))))))
  | mapping key kn v vn ihv =>
    intro _h
    cases key with
    | elem elemType _he =>
      rw [Syn.yield]
      apply ensures_bind_checked _ _ SemiFreeParts SemiFreeParts (ihv rfl)
      intro a ha
      exact ensures_pure _ SemiFreeParts (semiFreeParts_singleton
        (.append (semiFree_kw .mapping) (semiFree_parens
          (.append (.append (.append (.append (semiFree_elem elemType)
            (semiFree_optToks idt semiFree_id kn))
            (semiFree_punct .doubleArrow (by intro h; cases h)))
            (semiFreeParts_flat ha)) (semiFree_optToks idt semiFree_id vn)))))
    | path path =>
      rw [Syn.yield]
      apply ensures_bind_checked _ _ SemiFreeParts SemiFreeParts (ihv rfl)
      intro a ha
      exact ensures_pure _ SemiFreeParts (semiFreeParts_singleton
        (.append (semiFree_kw .mapping) (semiFree_parens
          (.append (.append (.append (.append (semiFree_path path)
            (semiFree_optToks idt semiFree_id kn))
            (semiFree_punct .doubleArrow (by intro h; cases h)))
            (semiFreeParts_flat ha)) (semiFree_optToks idt semiFree_id vn)))))
  | userType p =>
    intro _h
    rw [Syn.yield]
    exact ensures_pure _ SemiFreeParts (semiFreeParts_singleton (semiFree_path p))
  | array t len iht ihlen =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ SemiFreeParts SemiFreeParts (iht rfl)
    intro a ha
    apply ensures_bind_checked _ _ SemiFreeParts SemiFreeParts (ihlen rfl)
    intro b hb
    exact ensures_pure _ SemiFreeParts (semiFreeParts_singleton (.append (.append (.append (semiFreeParts_flat ha) (semiFree_punct .lbrack (by intro h; cases h))) (semiFreeParts_flat hb)) (semiFree_punct .rbrack (by intro h; cases h))))
  | varDecl t loc name iht =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ SemiFreeParts SemiFreeParts (iht rfl)
    intro a ha
    exact ensures_pure _ SemiFreeParts (semiFreeParts_singleton (.append (.append (semiFreeParts_flat ha) (semiFree_optToks DataLoc.toks semiFree_dataLoc loc)) (semiFree_id name)))
  | index e i ihe ihi =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ SemiFreeParts SemiFreeParts (ihe rfl)
    intro a ha
    apply ensures_bind_checked _ _ SemiFreeParts SemiFreeParts (ihi rfl)
    intro b hb
    exact ensures_pure _ SemiFreeParts (semiFreeParts_singleton (.append (.append (.append (semiFreeParts_flat ha) (semiFree_punct .lbrack (by intro h; cases h))) (semiFreeParts_flat hb)) (semiFree_punct .rbrack (by intro h; cases h))))
  | slice e i j ihe ihi ihj =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ SemiFreeParts SemiFreeParts (ihe rfl)
    intro a ha
    apply ensures_bind_checked _ _ SemiFreeParts SemiFreeParts (ihi rfl)
    intro b hb
    apply ensures_bind_checked _ _ SemiFreeParts SemiFreeParts (ihj rfl)
    intro c hc
    exact ensures_pure _ SemiFreeParts (semiFreeParts_singleton (.append (.append (.append (.append (.append (semiFreeParts_flat ha) (semiFree_punct .lbrack (by intro h; cases h))) (semiFreeParts_flat hb)) (semiFree_punct .colon (by intro h; cases h))) (semiFreeParts_flat hc)) (semiFree_punct .rbrack (by intro h; cases h))))
  | member e name ihe =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ SemiFreeParts SemiFreeParts (ihe rfl)
    intro a ha
    exact ensures_pure _ SemiFreeParts (semiFreeParts_singleton (.append (.append (semiFreeParts_flat ha) (semiFree_punct .period (by intro h; cases h))) (semiFree_choice (name == "address") (.token _ (by intro h; cases h)) (semiFree_id name))))
  | callOptions e arg args ihe iharg ihargs =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ SemiFreeParts SemiFreeParts (ihe rfl)
    intro a ha
    apply ensures_bind_checked _ _ SemiFreeParts SemiFreeParts (iharg rfl)
    intro b hb
    apply ensures_bind_checked _ _ SemiFreeParts SemiFreeParts (ihargs rfl)
    intro c hc
    exact ensures_pure _ SemiFreeParts (semiFreeParts_singleton (.append (semiFreeParts_flat ha) (.wrap (semiFree_commaSep (b.flatten :: c) (semiFreeParts_cons (semiFreeParts_flat hb) hc)))))
  | call e args ihe ihargs =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ SemiFreeParts SemiFreeParts (ihe rfl)
    intro a ha
    apply ensures_bind_checked _ _ SemiFreeParts SemiFreeParts (ihargs rfl)
    intro b hb
    exact ensures_pure _ SemiFreeParts (semiFreeParts_singleton (.append (semiFreeParts_flat ha) (semiFreeParts_flat hb)))
  | payableConv args ihargs =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ SemiFreeParts SemiFreeParts (ihargs rfl)
    intro a ha
    exact ensures_pure _ SemiFreeParts (semiFreeParts_singleton (.append (semiFree_kw .payable) (semiFreeParts_flat ha)))
  | metaType t iht =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ SemiFreeParts SemiFreeParts (iht rfl)
    intro a ha
    exact ensures_pure _ SemiFreeParts (semiFreeParts_singleton (.append (semiFree_kw .type_) (semiFree_parens (semiFreeParts_flat ha))))
  | unaryPrefix op e ihe =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ SemiFreeParts SemiFreeParts (ihe rfl)
    intro a ha
    exact ensures_pure _ SemiFreeParts (semiFreeParts_singleton (.append (semiFree_prefix op) (semiFreeParts_flat ha)))
  | unarySuffix op e ihe =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ SemiFreeParts SemiFreeParts (ihe rfl)
    intro a ha
    exact ensures_pure _ SemiFreeParts (semiFreeParts_singleton (.append (semiFreeParts_flat ha) (semiFree_suffix op)))
  | exp left right ihleft ihright =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ SemiFreeParts SemiFreeParts (ihleft rfl)
    intro a ha
    apply ensures_bind_checked _ _ SemiFreeParts SemiFreeParts (ihright rfl)
    intro b hb
    exact ensures_pure _ SemiFreeParts (semiFreeParts_singleton (.append (.append (semiFreeParts_flat ha) (semiFree_punct .exp (by intro h; cases h))) (semiFreeParts_flat hb)))
  | mulDivMod op left right ihleft ihright =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ SemiFreeParts SemiFreeParts (ihleft rfl)
    intro a ha
    apply ensures_bind_checked _ _ SemiFreeParts SemiFreeParts (ihright rfl)
    intro b hb
    exact ensures_pure _ SemiFreeParts (semiFreeParts_singleton (.append (.append (semiFreeParts_flat ha) (semiFree_mul op)) (semiFreeParts_flat hb)))
  | addSub op left right ihleft ihright =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ SemiFreeParts SemiFreeParts (ihleft rfl)
    intro a ha
    apply ensures_bind_checked _ _ SemiFreeParts SemiFreeParts (ihright rfl)
    intro b hb
    exact ensures_pure _ SemiFreeParts (semiFreeParts_singleton (.append (.append (semiFreeParts_flat ha) (semiFree_add op)) (semiFreeParts_flat hb)))
  | shift op left right ihleft ihright =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ SemiFreeParts SemiFreeParts (ihleft rfl)
    intro a ha
    apply ensures_bind_checked _ _ SemiFreeParts SemiFreeParts (ihright rfl)
    intro b hb
    exact ensures_pure _ SemiFreeParts (semiFreeParts_singleton (.append (.append (semiFreeParts_flat ha) (semiFree_shift op)) (semiFreeParts_flat hb)))
  | bitAnd left right ihleft ihright =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ SemiFreeParts SemiFreeParts (ihleft rfl)
    intro a ha
    apply ensures_bind_checked _ _ SemiFreeParts SemiFreeParts (ihright rfl)
    intro b hb
    exact ensures_pure _ SemiFreeParts (semiFreeParts_singleton (.append (.append (semiFreeParts_flat ha) (semiFree_punct .bitAnd (by intro h; cases h))) (semiFreeParts_flat hb)))
  | bitXor left right ihleft ihright =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ SemiFreeParts SemiFreeParts (ihleft rfl)
    intro a ha
    apply ensures_bind_checked _ _ SemiFreeParts SemiFreeParts (ihright rfl)
    intro b hb
    exact ensures_pure _ SemiFreeParts (semiFreeParts_singleton (.append (.append (semiFreeParts_flat ha) (semiFree_punct .bitXor (by intro h; cases h))) (semiFreeParts_flat hb)))
  | bitOr left right ihleft ihright =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ SemiFreeParts SemiFreeParts (ihleft rfl)
    intro a ha
    apply ensures_bind_checked _ _ SemiFreeParts SemiFreeParts (ihright rfl)
    intro b hb
    exact ensures_pure _ SemiFreeParts (semiFreeParts_singleton (.append (.append (semiFreeParts_flat ha) (semiFree_punct .bitOr (by intro h; cases h))) (semiFreeParts_flat hb)))
  | order op left right ihleft ihright =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ SemiFreeParts SemiFreeParts (ihleft rfl)
    intro a ha
    apply ensures_bind_checked _ _ SemiFreeParts SemiFreeParts (ihright rfl)
    intro b hb
    exact ensures_pure _ SemiFreeParts (semiFreeParts_singleton (.append (.append (semiFreeParts_flat ha) (semiFree_order op)) (semiFreeParts_flat hb)))
  | equality op left right ihleft ihright =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ SemiFreeParts SemiFreeParts (ihleft rfl)
    intro a ha
    apply ensures_bind_checked _ _ SemiFreeParts SemiFreeParts (ihright rfl)
    intro b hb
    exact ensures_pure _ SemiFreeParts (semiFreeParts_singleton (.append (.append (semiFreeParts_flat ha) (semiFree_equality op)) (semiFreeParts_flat hb)))
  | and left right ihleft ihright =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ SemiFreeParts SemiFreeParts (ihleft rfl)
    intro a ha
    apply ensures_bind_checked _ _ SemiFreeParts SemiFreeParts (ihright rfl)
    intro b hb
    exact ensures_pure _ SemiFreeParts (semiFreeParts_singleton (.append (.append (semiFreeParts_flat ha) (semiFree_punct .and (by intro h; cases h))) (semiFreeParts_flat hb)))
  | or left right ihleft ihright =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ SemiFreeParts SemiFreeParts (ihleft rfl)
    intro a ha
    apply ensures_bind_checked _ _ SemiFreeParts SemiFreeParts (ihright rfl)
    intro b hb
    exact ensures_pure _ SemiFreeParts (semiFreeParts_singleton (.append (.append (semiFreeParts_flat ha) (semiFree_punct .or (by intro h; cases h))) (semiFreeParts_flat hb)))
  | assign op left right ihleft ihright =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ SemiFreeParts SemiFreeParts (ihleft rfl)
    intro a ha
    apply ensures_bind_checked _ _ SemiFreeParts SemiFreeParts (ihright rfl)
    intro b hb
    exact ensures_pure _ SemiFreeParts (semiFreeParts_singleton (.append (.append (semiFreeParts_flat ha) (semiFree_assign op)) (semiFreeParts_flat hb)))
  | cond cond yes no ihcond ihyes ihno =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ SemiFreeParts SemiFreeParts (ihcond rfl)
    intro a ha
    apply ensures_bind_checked _ _ SemiFreeParts SemiFreeParts (ihyes rfl)
    intro b hb
    apply ensures_bind_checked _ _ SemiFreeParts SemiFreeParts (ihno rfl)
    intro c hc
    exact ensures_pure _ SemiFreeParts (semiFreeParts_singleton (.append (.append (.append (.append (semiFreeParts_flat ha) (semiFree_punct .question (by intro h; cases h))) (semiFreeParts_flat hb)) (semiFree_punct .colon (by intro h; cases h))) (semiFreeParts_flat hc)))
  | new t iht =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ SemiFreeParts SemiFreeParts (iht rfl)
    intro a ha
    exact ensures_pure _ SemiFreeParts (semiFreeParts_singleton (.append (semiFree_kw .new) (semiFreeParts_flat ha)))
  | tuple first rest ihfirst ihrest =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ SemiFreeParts SemiFreeParts (ihfirst rfl)
    intro a ha
    apply ensures_bind_checked _ _ SemiFreeParts SemiFreeParts (ihrest rfl)
    intro b hb
    exact ensures_pure _ SemiFreeParts (semiFreeParts_singleton (semiFree_parens (.append (semiFreeParts_flat ha) (semiFree_flatMap_prefix b (pu .comma) hb (semiFree_punct .comma (by intro h; cases h))))))
  | inlineArray first rest ihfirst ihrest =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ SemiFreeParts SemiFreeParts (ihfirst rfl)
    intro a ha
    apply ensures_bind_checked _ _ SemiFreeParts SemiFreeParts (ihrest rfl)
    intro b hb
    exact ensures_pure _ SemiFreeParts (semiFreeParts_singleton (.append (.append (semiFree_punct .lbrack (by intro h; cases h)) (semiFree_commaSep (a.flatten :: b) (semiFreeParts_cons (semiFreeParts_flat ha) hb))) (semiFree_punct .rbrack (by intro h; cases h))))
  | ident name =>
    intro _h
    rw [Syn.yield]
    exact ensures_pure _ SemiFreeParts (semiFreeParts_singleton (semiFree_id name))
  | lit lit =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ SemiFree SemiFreeParts (litP_semiFree lit)
    intro ts ht
    exact ensures_pure _ SemiFreeParts (semiFreeParts_singleton ht)
  | litUnit n u =>
    intro _h
    rw [Syn.yield]
    exact ensures_pure _ SemiFreeParts (semiFreeParts_singleton (.append (.token _ (by intro h; cases h)) (.token _ (by intro h; cases h))))
  | elemType e he =>
    intro _h
    rw [Syn.yield]
    exact ensures_pure _ SemiFreeParts (semiFreeParts_singleton (semiFree_elem_atom e))
  | declVar decl init ihdecl ihinit =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ SemiFreeParts SemiFreeParts (ihdecl rfl)
    intro a ha
    apply ensures_bind_checked _ _ SemiFreeParts SemiFreeParts (ihinit rfl)
    intro b hb
    exact ensures_pure _ SemiFreeParts (semiFreeParts_singleton (.append (semiFreeParts_flat ha) (semiFree_optional b hb (fun ts => pu .assign ++ ts) (fun ts ht => .append (semiFree_punct .assign (by intro h; cases h)) ht))))
  | declTuple holes decl decls e ihdecl ihdecls ihe =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ SemiFreeParts SemiFreeParts (ihdecl rfl)
    intro a ha
    apply ensures_bind_checked _ _ SemiFreeParts SemiFreeParts (ihdecls rfl)
    intro b hb
    apply ensures_bind_checked _ _ SemiFreeParts SemiFreeParts (ihe rfl)
    intro c hc
    exact ensures_pure _ SemiFreeParts (semiFreeParts_singleton (.append (.append (.append (.append (.append (.append (semiFree_punct .lparen (by intro h; cases h)) (semiFreeParts_flat (semiFreeParts_replicate holes (pu .comma) (semiFree_punct .comma (by intro h; cases h))))) (semiFreeParts_flat ha)) (semiFree_flatMap_prefix b (pu .comma) hb (semiFree_punct .comma (by intro h; cases h)))) (semiFree_punct .rparen (by intro h; cases h))) (semiFree_punct .assign (by intro h; cases h))) (semiFreeParts_flat hc)))
  | exprStmt e ih => intro _h; exact ih rfl
  | _ => intro h; cases h

theorem expression_yield_semiFree (e : Syn .expr) : PrEnsures e.yield SemiFreeParts :=
  syntax_yield_semiFree e rfl

theorem simple_yield_semiFree (s : Syn .simple) : PrEnsures s.yield SemiFreeParts :=
  syntax_yield_semiFree s rfl

end Solidity.Frontend.StatementGrammarH28
