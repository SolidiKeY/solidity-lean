import Solidity.Frontend.StatementGrammarH28.ControlFreeAtoms

/-! H31 proof-only all-atom continuation keyword absence. Existing syntax,
precedence contracts, expression-uniqueness exclusion and budgets unchanged. -/
namespace Solidity.Frontend.StatementGrammarH28
open Solidity.Source Solidity.Frontend.Checked

theorem syntax_yield_controlFree {c : Cat} (s : Syn c) :
    SemiFreeCat c = true → PrEnsures s.yield ControlFreeParts := by
  induction s with
  | nil => intro _h; exact ensures_pure _ ControlFreeParts controlFreeParts_nil
  | cons x xs ihx ihxs =>
    intro h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ ControlFreeParts ControlFreeParts (ihx h)
    intro a ha
    apply ensures_bind_checked _ _ ControlFreeParts ControlFreeParts (ihxs h)
    intro b hb
    exact ensures_pure _ ControlFreeParts (controlFreeParts_cons (controlFreeParts_flat ha) hb)
  | none => intro _h; exact ensures_pure _ ControlFreeParts controlFreeParts_nil
  | some x ihx =>
    intro h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ ControlFreeParts ControlFreeParts (ihx h)
    intro a ha
    exact ensures_pure _ ControlFreeParts (controlFreeParts_singleton (controlFreeParts_flat ha))
  | positional es ihes =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ ControlFreeParts ControlFreeParts (ihes rfl)
    intro a ha
    exact ensures_pure _ ControlFreeParts (controlFreeParts_singleton (controlFree_parens (controlFree_commaSep a ha)))
  | named args ihargs =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ ControlFreeParts ControlFreeParts (ihargs rfl)
    intro a ha
    exact ensures_pure _ ControlFreeParts (controlFreeParts_singleton (controlFree_parens (.wrap (controlFree_commaSep a ha))))
  | namedArg name e ihe =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ ControlFreeParts ControlFreeParts (ihe rfl)
    intro a ha
    exact ensures_pure _ ControlFreeParts (controlFreeParts_singleton (.append (.append (controlFree_id name) (controlFree_punct .colon)) (controlFreeParts_flat ha)))
  | param t loc name iht =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ ControlFreeParts ControlFreeParts (iht rfl)
    intro a ha
    exact ensures_pure _ ControlFreeParts (controlFreeParts_singleton (.append (.append (controlFreeParts_flat ha) (controlFree_optToks DataLoc.toks controlFree_dataLoc loc)) (controlFree_optToks idt controlFree_id name)))
  | elem e =>
    intro _h
    rw [Syn.yield]
    exact ensures_pure _ ControlFreeParts (controlFreeParts_singleton (controlFree_elem e))
  | fnType ps vis mu rets ihps ihrets =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind (P := ControlFreeParts)
    intro order
    apply ensures_bind_checked _ _ ControlFreeParts ControlFreeParts (ihps rfl)
    intro a ha
    have hv := controlFree_optToks Visibility.toks controlFree_visibility vis
    have hm := controlFree_optToks Mutability.toks controlFree_mutability mu
    have singles : ∀ pair ∈ (single .vis (optToks Visibility.toks vis) ++
        single .mutab (optToks Mutability.toks mu)), ControlFree pair.2 := by
      intro pair hp
      cases List.mem_append.mp hp with
      | inl h => exact controlFree_single _ _ hv pair h
      | inr h => exact controlFree_single _ _ hm pair h
    apply ensures_bind_checked _ _ ControlFree ControlFreeParts
      (attrsP_empty_mods_controlFree _ singles order)
    intro attrs hattrs
    apply ensures_bind_checked _ _ ControlFreeParts ControlFreeParts (ihrets rfl)
    intro r hr
    exact ensures_pure _ ControlFreeParts (controlFreeParts_singleton
      (.append (.append (.append (controlFree_kw .function (by decide))
        (controlFree_parens (controlFree_commaSep a ha))) hattrs)
        (controlFree_choice r.isEmpty .empty
          (.append (controlFree_kw .returns (by decide)) (controlFree_parens (controlFree_commaSep r hr))))))
  | mapping key kn v vn ihv =>
    intro _h
    cases key with
    | elem elemType _he =>
      rw [Syn.yield]
      apply ensures_bind_checked _ _ ControlFreeParts ControlFreeParts (ihv rfl)
      intro a ha
      exact ensures_pure _ ControlFreeParts (controlFreeParts_singleton
        (.append (controlFree_kw .mapping (by decide)) (controlFree_parens
          (.append (.append (.append (.append (controlFree_elem elemType)
            (controlFree_optToks idt controlFree_id kn))
            (controlFree_punct .doubleArrow))
            (controlFreeParts_flat ha)) (controlFree_optToks idt controlFree_id vn)))))
    | path path =>
      rw [Syn.yield]
      apply ensures_bind_checked _ _ ControlFreeParts ControlFreeParts (ihv rfl)
      intro a ha
      exact ensures_pure _ ControlFreeParts (controlFreeParts_singleton
        (.append (controlFree_kw .mapping (by decide)) (controlFree_parens
          (.append (.append (.append (.append (controlFree_path path)
            (controlFree_optToks idt controlFree_id kn))
            (controlFree_punct .doubleArrow))
            (controlFreeParts_flat ha)) (controlFree_optToks idt controlFree_id vn)))))
  | userType p =>
    intro _h
    rw [Syn.yield]
    exact ensures_pure _ ControlFreeParts (controlFreeParts_singleton (controlFree_path p))
  | array t len iht ihlen =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ ControlFreeParts ControlFreeParts (iht rfl)
    intro a ha
    apply ensures_bind_checked _ _ ControlFreeParts ControlFreeParts (ihlen rfl)
    intro b hb
    exact ensures_pure _ ControlFreeParts (controlFreeParts_singleton (.append (.append (.append (controlFreeParts_flat ha) (controlFree_punct .lbrack)) (controlFreeParts_flat hb)) (controlFree_punct .rbrack)))
  | varDecl t loc name iht =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ ControlFreeParts ControlFreeParts (iht rfl)
    intro a ha
    exact ensures_pure _ ControlFreeParts (controlFreeParts_singleton (.append (.append (controlFreeParts_flat ha) (controlFree_optToks DataLoc.toks controlFree_dataLoc loc)) (controlFree_id name)))
  | index e i ihe ihi =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ ControlFreeParts ControlFreeParts (ihe rfl)
    intro a ha
    apply ensures_bind_checked _ _ ControlFreeParts ControlFreeParts (ihi rfl)
    intro b hb
    exact ensures_pure _ ControlFreeParts (controlFreeParts_singleton (.append (.append (.append (controlFreeParts_flat ha) (controlFree_punct .lbrack)) (controlFreeParts_flat hb)) (controlFree_punct .rbrack)))
  | slice e i j ihe ihi ihj =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ ControlFreeParts ControlFreeParts (ihe rfl)
    intro a ha
    apply ensures_bind_checked _ _ ControlFreeParts ControlFreeParts (ihi rfl)
    intro b hb
    apply ensures_bind_checked _ _ ControlFreeParts ControlFreeParts (ihj rfl)
    intro c hc
    exact ensures_pure _ ControlFreeParts (controlFreeParts_singleton (.append (.append (.append (.append (.append (controlFreeParts_flat ha) (controlFree_punct .lbrack)) (controlFreeParts_flat hb)) (controlFree_punct .colon)) (controlFreeParts_flat hc)) (controlFree_punct .rbrack)))
  | member e name ihe =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ ControlFreeParts ControlFreeParts (ihe rfl)
    intro a ha
    exact ensures_pure _ ControlFreeParts (controlFreeParts_singleton (.append (.append (controlFreeParts_flat ha) (controlFree_punct .period)) (controlFree_choice (name == "address") (.token _ rfl) (controlFree_id name))))
  | callOptions e arg args ihe iharg ihargs =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ ControlFreeParts ControlFreeParts (ihe rfl)
    intro a ha
    apply ensures_bind_checked _ _ ControlFreeParts ControlFreeParts (iharg rfl)
    intro b hb
    apply ensures_bind_checked _ _ ControlFreeParts ControlFreeParts (ihargs rfl)
    intro c hc
    exact ensures_pure _ ControlFreeParts (controlFreeParts_singleton (.append (controlFreeParts_flat ha) (.wrap (controlFree_commaSep (b.flatten :: c) (controlFreeParts_cons (controlFreeParts_flat hb) hc)))))
  | call e args ihe ihargs =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ ControlFreeParts ControlFreeParts (ihe rfl)
    intro a ha
    apply ensures_bind_checked _ _ ControlFreeParts ControlFreeParts (ihargs rfl)
    intro b hb
    exact ensures_pure _ ControlFreeParts (controlFreeParts_singleton (.append (controlFreeParts_flat ha) (controlFreeParts_flat hb)))
  | payableConv args ihargs =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ ControlFreeParts ControlFreeParts (ihargs rfl)
    intro a ha
    exact ensures_pure _ ControlFreeParts (controlFreeParts_singleton (.append (controlFree_kw .payable (by decide)) (controlFreeParts_flat ha)))
  | metaType t iht =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ ControlFreeParts ControlFreeParts (iht rfl)
    intro a ha
    exact ensures_pure _ ControlFreeParts (controlFreeParts_singleton (.append (controlFree_kw .type_ (by decide)) (controlFree_parens (controlFreeParts_flat ha))))
  | unaryPrefix op e ihe =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ ControlFreeParts ControlFreeParts (ihe rfl)
    intro a ha
    exact ensures_pure _ ControlFreeParts (controlFreeParts_singleton (.append (controlFree_prefix op) (controlFreeParts_flat ha)))
  | unarySuffix op e ihe =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ ControlFreeParts ControlFreeParts (ihe rfl)
    intro a ha
    exact ensures_pure _ ControlFreeParts (controlFreeParts_singleton (.append (controlFreeParts_flat ha) (controlFree_suffix op)))
  | exp left right ihleft ihright =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ ControlFreeParts ControlFreeParts (ihleft rfl)
    intro a ha
    apply ensures_bind_checked _ _ ControlFreeParts ControlFreeParts (ihright rfl)
    intro b hb
    exact ensures_pure _ ControlFreeParts (controlFreeParts_singleton (.append (.append (controlFreeParts_flat ha) (controlFree_punct .exp)) (controlFreeParts_flat hb)))
  | mulDivMod op left right ihleft ihright =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ ControlFreeParts ControlFreeParts (ihleft rfl)
    intro a ha
    apply ensures_bind_checked _ _ ControlFreeParts ControlFreeParts (ihright rfl)
    intro b hb
    exact ensures_pure _ ControlFreeParts (controlFreeParts_singleton (.append (.append (controlFreeParts_flat ha) (controlFree_mul op)) (controlFreeParts_flat hb)))
  | addSub op left right ihleft ihright =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ ControlFreeParts ControlFreeParts (ihleft rfl)
    intro a ha
    apply ensures_bind_checked _ _ ControlFreeParts ControlFreeParts (ihright rfl)
    intro b hb
    exact ensures_pure _ ControlFreeParts (controlFreeParts_singleton (.append (.append (controlFreeParts_flat ha) (controlFree_add op)) (controlFreeParts_flat hb)))
  | shift op left right ihleft ihright =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ ControlFreeParts ControlFreeParts (ihleft rfl)
    intro a ha
    apply ensures_bind_checked _ _ ControlFreeParts ControlFreeParts (ihright rfl)
    intro b hb
    exact ensures_pure _ ControlFreeParts (controlFreeParts_singleton (.append (.append (controlFreeParts_flat ha) (controlFree_shift op)) (controlFreeParts_flat hb)))
  | bitAnd left right ihleft ihright =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ ControlFreeParts ControlFreeParts (ihleft rfl)
    intro a ha
    apply ensures_bind_checked _ _ ControlFreeParts ControlFreeParts (ihright rfl)
    intro b hb
    exact ensures_pure _ ControlFreeParts (controlFreeParts_singleton (.append (.append (controlFreeParts_flat ha) (controlFree_punct .bitAnd)) (controlFreeParts_flat hb)))
  | bitXor left right ihleft ihright =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ ControlFreeParts ControlFreeParts (ihleft rfl)
    intro a ha
    apply ensures_bind_checked _ _ ControlFreeParts ControlFreeParts (ihright rfl)
    intro b hb
    exact ensures_pure _ ControlFreeParts (controlFreeParts_singleton (.append (.append (controlFreeParts_flat ha) (controlFree_punct .bitXor)) (controlFreeParts_flat hb)))
  | bitOr left right ihleft ihright =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ ControlFreeParts ControlFreeParts (ihleft rfl)
    intro a ha
    apply ensures_bind_checked _ _ ControlFreeParts ControlFreeParts (ihright rfl)
    intro b hb
    exact ensures_pure _ ControlFreeParts (controlFreeParts_singleton (.append (.append (controlFreeParts_flat ha) (controlFree_punct .bitOr)) (controlFreeParts_flat hb)))
  | order op left right ihleft ihright =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ ControlFreeParts ControlFreeParts (ihleft rfl)
    intro a ha
    apply ensures_bind_checked _ _ ControlFreeParts ControlFreeParts (ihright rfl)
    intro b hb
    exact ensures_pure _ ControlFreeParts (controlFreeParts_singleton (.append (.append (controlFreeParts_flat ha) (controlFree_order op)) (controlFreeParts_flat hb)))
  | equality op left right ihleft ihright =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ ControlFreeParts ControlFreeParts (ihleft rfl)
    intro a ha
    apply ensures_bind_checked _ _ ControlFreeParts ControlFreeParts (ihright rfl)
    intro b hb
    exact ensures_pure _ ControlFreeParts (controlFreeParts_singleton (.append (.append (controlFreeParts_flat ha) (controlFree_equality op)) (controlFreeParts_flat hb)))
  | and left right ihleft ihright =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ ControlFreeParts ControlFreeParts (ihleft rfl)
    intro a ha
    apply ensures_bind_checked _ _ ControlFreeParts ControlFreeParts (ihright rfl)
    intro b hb
    exact ensures_pure _ ControlFreeParts (controlFreeParts_singleton (.append (.append (controlFreeParts_flat ha) (controlFree_punct .and)) (controlFreeParts_flat hb)))
  | or left right ihleft ihright =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ ControlFreeParts ControlFreeParts (ihleft rfl)
    intro a ha
    apply ensures_bind_checked _ _ ControlFreeParts ControlFreeParts (ihright rfl)
    intro b hb
    exact ensures_pure _ ControlFreeParts (controlFreeParts_singleton (.append (.append (controlFreeParts_flat ha) (controlFree_punct .or)) (controlFreeParts_flat hb)))
  | assign op left right ihleft ihright =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ ControlFreeParts ControlFreeParts (ihleft rfl)
    intro a ha
    apply ensures_bind_checked _ _ ControlFreeParts ControlFreeParts (ihright rfl)
    intro b hb
    exact ensures_pure _ ControlFreeParts (controlFreeParts_singleton (.append (.append (controlFreeParts_flat ha) (controlFree_assign op)) (controlFreeParts_flat hb)))
  | cond cond yes no ihcond ihyes ihno =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ ControlFreeParts ControlFreeParts (ihcond rfl)
    intro a ha
    apply ensures_bind_checked _ _ ControlFreeParts ControlFreeParts (ihyes rfl)
    intro b hb
    apply ensures_bind_checked _ _ ControlFreeParts ControlFreeParts (ihno rfl)
    intro c hc
    exact ensures_pure _ ControlFreeParts (controlFreeParts_singleton (.append (.append (.append (.append (controlFreeParts_flat ha) (controlFree_punct .question)) (controlFreeParts_flat hb)) (controlFree_punct .colon)) (controlFreeParts_flat hc)))
  | new t iht =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ ControlFreeParts ControlFreeParts (iht rfl)
    intro a ha
    exact ensures_pure _ ControlFreeParts (controlFreeParts_singleton (.append (controlFree_kw .new (by decide)) (controlFreeParts_flat ha)))
  | tuple first rest ihfirst ihrest =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ ControlFreeParts ControlFreeParts (ihfirst rfl)
    intro a ha
    apply ensures_bind_checked _ _ ControlFreeParts ControlFreeParts (ihrest rfl)
    intro b hb
    exact ensures_pure _ ControlFreeParts (controlFreeParts_singleton (controlFree_parens (.append (controlFreeParts_flat ha) (controlFree_flatMap_prefix b (pu .comma) hb (controlFree_punct .comma)))))
  | inlineArray first rest ihfirst ihrest =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ ControlFreeParts ControlFreeParts (ihfirst rfl)
    intro a ha
    apply ensures_bind_checked _ _ ControlFreeParts ControlFreeParts (ihrest rfl)
    intro b hb
    exact ensures_pure _ ControlFreeParts (controlFreeParts_singleton (.append (.append (controlFree_punct .lbrack) (controlFree_commaSep (a.flatten :: b) (controlFreeParts_cons (controlFreeParts_flat ha) hb))) (controlFree_punct .rbrack)))
  | ident name =>
    intro _h
    rw [Syn.yield]
    exact ensures_pure _ ControlFreeParts (controlFreeParts_singleton (controlFree_id name))
  | lit lit =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ ControlFree ControlFreeParts (litP_controlFree lit)
    intro ts ht
    exact ensures_pure _ ControlFreeParts (controlFreeParts_singleton ht)
  | litUnit n u =>
    intro _h
    rw [Syn.yield]
    exact ensures_pure _ ControlFreeParts (controlFreeParts_singleton (.append (.token _ rfl) (.token _ rfl)))
  | elemType e he =>
    intro _h
    rw [Syn.yield]
    exact ensures_pure _ ControlFreeParts (controlFreeParts_singleton (controlFree_elem_atom e))
  | declVar decl init ihdecl ihinit =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ ControlFreeParts ControlFreeParts (ihdecl rfl)
    intro a ha
    apply ensures_bind_checked _ _ ControlFreeParts ControlFreeParts (ihinit rfl)
    intro b hb
    exact ensures_pure _ ControlFreeParts (controlFreeParts_singleton (.append (controlFreeParts_flat ha) (controlFree_optional b hb (fun ts => pu .assign ++ ts) (fun ts ht => .append (controlFree_punct .assign) ht))))
  | declTuple holes decl decls e ihdecl ihdecls ihe =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ ControlFreeParts ControlFreeParts (ihdecl rfl)
    intro a ha
    apply ensures_bind_checked _ _ ControlFreeParts ControlFreeParts (ihdecls rfl)
    intro b hb
    apply ensures_bind_checked _ _ ControlFreeParts ControlFreeParts (ihe rfl)
    intro c hc
    exact ensures_pure _ ControlFreeParts (controlFreeParts_singleton (.append (.append (.append (.append (.append (.append (controlFree_punct .lparen) (controlFreeParts_flat (controlFreeParts_replicate holes (pu .comma) (controlFree_punct .comma)))) (controlFreeParts_flat ha)) (controlFree_flatMap_prefix b (pu .comma) hb (controlFree_punct .comma))) (controlFree_punct .rparen)) (controlFree_punct .assign)) (controlFreeParts_flat hc)))
  | exprStmt e ih => intro _h; exact ih rfl
  | _ => intro h; cases h

theorem expression_yield_controlFree (e : Syn .expr) : PrEnsures e.yield ControlFreeParts :=
  syntax_yield_controlFree e rfl

theorem simple_yield_controlFree (s : Syn .simple) : PrEnsures s.yield ControlFreeParts :=
  syntax_yield_controlFree s rfl

theorem syntax_yield_no_continuations {c : Cat} (s : Syn c) (hc : SemiFreeCat c = true)
    (L M : List Choice) (parts : List (List Tok)) (hy : s.yield L = some (parts, M))
    (t : Tok) (hb : boundaryToken t = true) : t ∉ parts.flatten :=
  controlFree_no_boundary (controlFreeParts_flat (syntax_yield_controlFree s hc L parts M hy)) t hb

#print axioms syntax_yield_controlFree
#print axioms expression_yield_controlFree
#print axioms simple_yield_controlFree
#print axioms syntax_yield_no_continuations
end Solidity.Frontend.StatementGrammarH28
