import Solidity.Frontend.StatementGrammarH28.ParenAtoms

/-! Universal parenthesis balance over all79 statement dependency constructors
and matching actual expression-header splitting. H31 proof-only atom inspection;
no expression uniqueness, assumed parser success or producer change. -/
namespace Solidity.Frontend.StatementGrammarH28
open Solidity.Source Solidity.Frontend.Checked

def ParenBalanceCat : Cat → Bool
  | .callArgs | .namedArg | .param | .typeName | .varDecl | .expr | .simple
  | .stmt _ | .item _ | .block _ | .catchClause _ | .yulStmt | .yulExpr | .yulCase => true
  | .list c | .opt c => ParenBalanceCat c
  | _ => false

theorem syntax_yield_parenBalanced {c : Cat} (s : Syn c) :
    ParenBalanceCat c = true → PrEnsures s.yield ParenBalancedParts := by
  induction s with
  | nil => intro _h; exact ensures_pure _ ParenBalancedParts parenBalancedParts_nil
  | cons x xs ihx ihxs =>
    intro h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ ParenBalancedParts ParenBalancedParts (ihx h)
    intro a ha
    apply ensures_bind_checked _ _ ParenBalancedParts ParenBalancedParts (ihxs h)
    intro b hb
    exact ensures_pure _ ParenBalancedParts (parenBalancedParts_cons (parenBalancedParts_flat ha) hb)
  | none => intro _h; exact ensures_pure _ ParenBalancedParts parenBalancedParts_nil
  | some x ihx =>
    intro h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ ParenBalancedParts ParenBalancedParts (ihx h)
    intro a ha
    exact ensures_pure _ ParenBalancedParts (parenBalancedParts_singleton (parenBalancedParts_flat ha))
  | positional es ihes =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ ParenBalancedParts ParenBalancedParts (ihes rfl)
    intro a ha
    exact ensures_pure _ ParenBalancedParts (parenBalancedParts_singleton (parenBalanced_parens (parenBalanced_commaSep a ha)))
  | named args ihargs =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ ParenBalancedParts ParenBalancedParts (ihargs rfl)
    intro a ha
    exact ensures_pure _ ParenBalancedParts (parenBalancedParts_singleton (parenBalanced_parens (.brace (parenBalanced_commaSep a ha))))
  | namedArg name e ihe =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ ParenBalancedParts ParenBalancedParts (ihe rfl)
    intro a ha
    exact ensures_pure _ ParenBalancedParts (parenBalancedParts_singleton (.append (.append (parenBalanced_id name) (parenBalanced_punct .colon (by intro h; cases h) (by intro h; cases h))) (parenBalancedParts_flat ha)))
  | param t loc name iht =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ ParenBalancedParts ParenBalancedParts (iht rfl)
    intro a ha
    exact ensures_pure _ ParenBalancedParts (parenBalancedParts_singleton (.append (.append (parenBalancedParts_flat ha) (parenBalanced_optToks DataLoc.toks parenBalanced_dataLoc loc)) (parenBalanced_optToks idt parenBalanced_id name)))
  | elem e =>
    intro _h
    rw [Syn.yield]
    exact ensures_pure _ ParenBalancedParts (parenBalancedParts_singleton (parenBalanced_elem e))
  | fnType ps vis mu rets ihps ihrets =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind (P := ParenBalancedParts)
    intro order
    apply ensures_bind_checked _ _ ParenBalancedParts ParenBalancedParts (ihps rfl)
    intro a ha
    have hv := parenBalanced_optToks Visibility.toks parenBalanced_visibility vis
    have hm := parenBalanced_optToks Mutability.toks parenBalanced_mutability mu
    have singles : ∀ pair ∈ (single .vis (optToks Visibility.toks vis) ++
        single .mutab (optToks Mutability.toks mu)), ParenBalanced pair.2 := by
      intro pair hp
      cases List.mem_append.mp hp with
      | inl h => exact parenBalanced_single _ _ hv pair h
      | inr h => exact parenBalanced_single _ _ hm pair h
    apply ensures_bind_checked _ _ ParenBalanced ParenBalancedParts
      (attrsP_empty_mods_parenBalanced _ singles order)
    intro attrs hattrs
    apply ensures_bind_checked _ _ ParenBalancedParts ParenBalancedParts (ihrets rfl)
    intro r hr
    exact ensures_pure _ ParenBalancedParts (parenBalancedParts_singleton
      (.append (.append (.append (parenBalanced_kw .function)
        (parenBalanced_parens (parenBalanced_commaSep a ha))) hattrs)
        (parenBalanced_choice r.isEmpty .empty
          (.append (parenBalanced_kw .returns) (parenBalanced_parens (parenBalanced_commaSep r hr))))))
  | mapping key kn v vn ihv =>
    intro _h
    cases key with
    | elem elemType _he =>
      rw [Syn.yield]
      apply ensures_bind_checked _ _ ParenBalancedParts ParenBalancedParts (ihv rfl)
      intro a ha
      exact ensures_pure _ ParenBalancedParts (parenBalancedParts_singleton
        (.append (parenBalanced_kw .mapping) (parenBalanced_parens
          (.append (.append (.append (.append (parenBalanced_elem elemType)
            (parenBalanced_optToks idt parenBalanced_id kn))
            (parenBalanced_punct .doubleArrow (by intro h; cases h) (by intro h; cases h)))
            (parenBalancedParts_flat ha)) (parenBalanced_optToks idt parenBalanced_id vn)))))
    | path path =>
      rw [Syn.yield]
      apply ensures_bind_checked _ _ ParenBalancedParts ParenBalancedParts (ihv rfl)
      intro a ha
      exact ensures_pure _ ParenBalancedParts (parenBalancedParts_singleton
        (.append (parenBalanced_kw .mapping) (parenBalanced_parens
          (.append (.append (.append (.append (parenBalanced_path path)
            (parenBalanced_optToks idt parenBalanced_id kn))
            (parenBalanced_punct .doubleArrow (by intro h; cases h) (by intro h; cases h)))
            (parenBalancedParts_flat ha)) (parenBalanced_optToks idt parenBalanced_id vn)))))
  | userType p =>
    intro _h
    rw [Syn.yield]
    exact ensures_pure _ ParenBalancedParts (parenBalancedParts_singleton (parenBalanced_path p))
  | array t len iht ihlen =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ ParenBalancedParts ParenBalancedParts (iht rfl)
    intro a ha
    apply ensures_bind_checked _ _ ParenBalancedParts ParenBalancedParts (ihlen rfl)
    intro b hb
    exact ensures_pure _ ParenBalancedParts (parenBalancedParts_singleton (.append (.append (.append (parenBalancedParts_flat ha) (parenBalanced_punct .lbrack (by intro h; cases h) (by intro h; cases h))) (parenBalancedParts_flat hb)) (parenBalanced_punct .rbrack (by intro h; cases h) (by intro h; cases h))))
  | varDecl t loc name iht =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ ParenBalancedParts ParenBalancedParts (iht rfl)
    intro a ha
    exact ensures_pure _ ParenBalancedParts (parenBalancedParts_singleton (.append (.append (parenBalancedParts_flat ha) (parenBalanced_optToks DataLoc.toks parenBalanced_dataLoc loc)) (parenBalanced_id name)))
  | index e i ihe ihi =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ ParenBalancedParts ParenBalancedParts (ihe rfl)
    intro a ha
    apply ensures_bind_checked _ _ ParenBalancedParts ParenBalancedParts (ihi rfl)
    intro b hb
    exact ensures_pure _ ParenBalancedParts (parenBalancedParts_singleton (.append (.append (.append (parenBalancedParts_flat ha) (parenBalanced_punct .lbrack (by intro h; cases h) (by intro h; cases h))) (parenBalancedParts_flat hb)) (parenBalanced_punct .rbrack (by intro h; cases h) (by intro h; cases h))))
  | slice e i j ihe ihi ihj =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ ParenBalancedParts ParenBalancedParts (ihe rfl)
    intro a ha
    apply ensures_bind_checked _ _ ParenBalancedParts ParenBalancedParts (ihi rfl)
    intro b hb
    apply ensures_bind_checked _ _ ParenBalancedParts ParenBalancedParts (ihj rfl)
    intro c hc
    exact ensures_pure _ ParenBalancedParts (parenBalancedParts_singleton (.append (.append (.append (.append (.append (parenBalancedParts_flat ha) (parenBalanced_punct .lbrack (by intro h; cases h) (by intro h; cases h))) (parenBalancedParts_flat hb)) (parenBalanced_punct .colon (by intro h; cases h) (by intro h; cases h))) (parenBalancedParts_flat hc)) (parenBalanced_punct .rbrack (by intro h; cases h) (by intro h; cases h))))
  | member e name ihe =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ ParenBalancedParts ParenBalancedParts (ihe rfl)
    intro a ha
    exact ensures_pure _ ParenBalancedParts (parenBalancedParts_singleton (.append (.append (parenBalancedParts_flat ha) (parenBalanced_punct .period (by intro h; cases h) (by intro h; cases h))) (parenBalanced_choice (name == "address") (.token _ (by intro h; cases h) (by intro h; cases h)) (parenBalanced_id name))))
  | callOptions e arg args ihe iharg ihargs =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ ParenBalancedParts ParenBalancedParts (ihe rfl)
    intro a ha
    apply ensures_bind_checked _ _ ParenBalancedParts ParenBalancedParts (iharg rfl)
    intro b hb
    apply ensures_bind_checked _ _ ParenBalancedParts ParenBalancedParts (ihargs rfl)
    intro c hc
    exact ensures_pure _ ParenBalancedParts (parenBalancedParts_singleton (.append (parenBalancedParts_flat ha) (.brace (parenBalanced_commaSep (b.flatten :: c) (parenBalancedParts_cons (parenBalancedParts_flat hb) hc)))))
  | call e args ihe ihargs =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ ParenBalancedParts ParenBalancedParts (ihe rfl)
    intro a ha
    apply ensures_bind_checked _ _ ParenBalancedParts ParenBalancedParts (ihargs rfl)
    intro b hb
    exact ensures_pure _ ParenBalancedParts (parenBalancedParts_singleton (.append (parenBalancedParts_flat ha) (parenBalancedParts_flat hb)))
  | payableConv args ihargs =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ ParenBalancedParts ParenBalancedParts (ihargs rfl)
    intro a ha
    exact ensures_pure _ ParenBalancedParts (parenBalancedParts_singleton (.append (parenBalanced_kw .payable) (parenBalancedParts_flat ha)))
  | metaType t iht =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ ParenBalancedParts ParenBalancedParts (iht rfl)
    intro a ha
    exact ensures_pure _ ParenBalancedParts (parenBalancedParts_singleton (.append (parenBalanced_kw .type_) (parenBalanced_parens (parenBalancedParts_flat ha))))
  | unaryPrefix op e ihe =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ ParenBalancedParts ParenBalancedParts (ihe rfl)
    intro a ha
    exact ensures_pure _ ParenBalancedParts (parenBalancedParts_singleton (.append (parenBalanced_prefix op) (parenBalancedParts_flat ha)))
  | unarySuffix op e ihe =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ ParenBalancedParts ParenBalancedParts (ihe rfl)
    intro a ha
    exact ensures_pure _ ParenBalancedParts (parenBalancedParts_singleton (.append (parenBalancedParts_flat ha) (parenBalanced_suffix op)))
  | exp left right ihleft ihright =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ ParenBalancedParts ParenBalancedParts (ihleft rfl)
    intro a ha
    apply ensures_bind_checked _ _ ParenBalancedParts ParenBalancedParts (ihright rfl)
    intro b hb
    exact ensures_pure _ ParenBalancedParts (parenBalancedParts_singleton (.append (.append (parenBalancedParts_flat ha) (parenBalanced_punct .exp (by intro h; cases h) (by intro h; cases h))) (parenBalancedParts_flat hb)))
  | mulDivMod op left right ihleft ihright =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ ParenBalancedParts ParenBalancedParts (ihleft rfl)
    intro a ha
    apply ensures_bind_checked _ _ ParenBalancedParts ParenBalancedParts (ihright rfl)
    intro b hb
    exact ensures_pure _ ParenBalancedParts (parenBalancedParts_singleton (.append (.append (parenBalancedParts_flat ha) (parenBalanced_mul op)) (parenBalancedParts_flat hb)))
  | addSub op left right ihleft ihright =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ ParenBalancedParts ParenBalancedParts (ihleft rfl)
    intro a ha
    apply ensures_bind_checked _ _ ParenBalancedParts ParenBalancedParts (ihright rfl)
    intro b hb
    exact ensures_pure _ ParenBalancedParts (parenBalancedParts_singleton (.append (.append (parenBalancedParts_flat ha) (parenBalanced_add op)) (parenBalancedParts_flat hb)))
  | shift op left right ihleft ihright =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ ParenBalancedParts ParenBalancedParts (ihleft rfl)
    intro a ha
    apply ensures_bind_checked _ _ ParenBalancedParts ParenBalancedParts (ihright rfl)
    intro b hb
    exact ensures_pure _ ParenBalancedParts (parenBalancedParts_singleton (.append (.append (parenBalancedParts_flat ha) (parenBalanced_shift op)) (parenBalancedParts_flat hb)))
  | bitAnd left right ihleft ihright =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ ParenBalancedParts ParenBalancedParts (ihleft rfl)
    intro a ha
    apply ensures_bind_checked _ _ ParenBalancedParts ParenBalancedParts (ihright rfl)
    intro b hb
    exact ensures_pure _ ParenBalancedParts (parenBalancedParts_singleton (.append (.append (parenBalancedParts_flat ha) (parenBalanced_punct .bitAnd (by intro h; cases h) (by intro h; cases h))) (parenBalancedParts_flat hb)))
  | bitXor left right ihleft ihright =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ ParenBalancedParts ParenBalancedParts (ihleft rfl)
    intro a ha
    apply ensures_bind_checked _ _ ParenBalancedParts ParenBalancedParts (ihright rfl)
    intro b hb
    exact ensures_pure _ ParenBalancedParts (parenBalancedParts_singleton (.append (.append (parenBalancedParts_flat ha) (parenBalanced_punct .bitXor (by intro h; cases h) (by intro h; cases h))) (parenBalancedParts_flat hb)))
  | bitOr left right ihleft ihright =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ ParenBalancedParts ParenBalancedParts (ihleft rfl)
    intro a ha
    apply ensures_bind_checked _ _ ParenBalancedParts ParenBalancedParts (ihright rfl)
    intro b hb
    exact ensures_pure _ ParenBalancedParts (parenBalancedParts_singleton (.append (.append (parenBalancedParts_flat ha) (parenBalanced_punct .bitOr (by intro h; cases h) (by intro h; cases h))) (parenBalancedParts_flat hb)))
  | order op left right ihleft ihright =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ ParenBalancedParts ParenBalancedParts (ihleft rfl)
    intro a ha
    apply ensures_bind_checked _ _ ParenBalancedParts ParenBalancedParts (ihright rfl)
    intro b hb
    exact ensures_pure _ ParenBalancedParts (parenBalancedParts_singleton (.append (.append (parenBalancedParts_flat ha) (parenBalanced_order op)) (parenBalancedParts_flat hb)))
  | equality op left right ihleft ihright =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ ParenBalancedParts ParenBalancedParts (ihleft rfl)
    intro a ha
    apply ensures_bind_checked _ _ ParenBalancedParts ParenBalancedParts (ihright rfl)
    intro b hb
    exact ensures_pure _ ParenBalancedParts (parenBalancedParts_singleton (.append (.append (parenBalancedParts_flat ha) (parenBalanced_equality op)) (parenBalancedParts_flat hb)))
  | and left right ihleft ihright =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ ParenBalancedParts ParenBalancedParts (ihleft rfl)
    intro a ha
    apply ensures_bind_checked _ _ ParenBalancedParts ParenBalancedParts (ihright rfl)
    intro b hb
    exact ensures_pure _ ParenBalancedParts (parenBalancedParts_singleton (.append (.append (parenBalancedParts_flat ha) (parenBalanced_punct .and (by intro h; cases h) (by intro h; cases h))) (parenBalancedParts_flat hb)))
  | or left right ihleft ihright =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ ParenBalancedParts ParenBalancedParts (ihleft rfl)
    intro a ha
    apply ensures_bind_checked _ _ ParenBalancedParts ParenBalancedParts (ihright rfl)
    intro b hb
    exact ensures_pure _ ParenBalancedParts (parenBalancedParts_singleton (.append (.append (parenBalancedParts_flat ha) (parenBalanced_punct .or (by intro h; cases h) (by intro h; cases h))) (parenBalancedParts_flat hb)))
  | assign op left right ihleft ihright =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ ParenBalancedParts ParenBalancedParts (ihleft rfl)
    intro a ha
    apply ensures_bind_checked _ _ ParenBalancedParts ParenBalancedParts (ihright rfl)
    intro b hb
    exact ensures_pure _ ParenBalancedParts (parenBalancedParts_singleton (.append (.append (parenBalancedParts_flat ha) (parenBalanced_assign op)) (parenBalancedParts_flat hb)))
  | cond cond yes no ihcond ihyes ihno =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ ParenBalancedParts ParenBalancedParts (ihcond rfl)
    intro a ha
    apply ensures_bind_checked _ _ ParenBalancedParts ParenBalancedParts (ihyes rfl)
    intro b hb
    apply ensures_bind_checked _ _ ParenBalancedParts ParenBalancedParts (ihno rfl)
    intro c hc
    exact ensures_pure _ ParenBalancedParts (parenBalancedParts_singleton (.append (.append (.append (.append (parenBalancedParts_flat ha) (parenBalanced_punct .question (by intro h; cases h) (by intro h; cases h))) (parenBalancedParts_flat hb)) (parenBalanced_punct .colon (by intro h; cases h) (by intro h; cases h))) (parenBalancedParts_flat hc)))
  | new t iht =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ ParenBalancedParts ParenBalancedParts (iht rfl)
    intro a ha
    exact ensures_pure _ ParenBalancedParts (parenBalancedParts_singleton (.append (parenBalanced_kw .new) (parenBalancedParts_flat ha)))
  | tuple first rest ihfirst ihrest =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ ParenBalancedParts ParenBalancedParts (ihfirst rfl)
    intro a ha
    apply ensures_bind_checked _ _ ParenBalancedParts ParenBalancedParts (ihrest rfl)
    intro b hb
    exact ensures_pure _ ParenBalancedParts (parenBalancedParts_singleton (parenBalanced_parens (.append (parenBalancedParts_flat ha) (parenBalanced_flatMap_prefix b (pu .comma) hb (parenBalanced_punct .comma (by intro h; cases h) (by intro h; cases h))))))
  | inlineArray first rest ihfirst ihrest =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ ParenBalancedParts ParenBalancedParts (ihfirst rfl)
    intro a ha
    apply ensures_bind_checked _ _ ParenBalancedParts ParenBalancedParts (ihrest rfl)
    intro b hb
    exact ensures_pure _ ParenBalancedParts (parenBalancedParts_singleton (.append (.append (parenBalanced_punct .lbrack (by intro h; cases h) (by intro h; cases h)) (parenBalanced_commaSep (a.flatten :: b) (parenBalancedParts_cons (parenBalancedParts_flat ha) hb))) (parenBalanced_punct .rbrack (by intro h; cases h) (by intro h; cases h))))
  | ident name =>
    intro _h
    rw [Syn.yield]
    exact ensures_pure _ ParenBalancedParts (parenBalancedParts_singleton (parenBalanced_id name))
  | lit lit =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ ParenBalanced ParenBalancedParts (litP_parenBalanced lit)
    intro ts ht
    exact ensures_pure _ ParenBalancedParts (parenBalancedParts_singleton ht)
  | litUnit n u =>
    intro _h
    rw [Syn.yield]
    exact ensures_pure _ ParenBalancedParts (parenBalancedParts_singleton (.append (.token _ (by intro h; cases h) (by intro h; cases h)) (.token _ (by intro h; cases h) (by intro h; cases h))))
  | elemType e he =>
    intro _h
    rw [Syn.yield]
    exact ensures_pure _ ParenBalancedParts (parenBalancedParts_singleton (parenBalanced_elem_atom e))
  | declVar decl init ihdecl ihinit =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ ParenBalancedParts ParenBalancedParts (ihdecl rfl)
    intro a ha
    apply ensures_bind_checked _ _ ParenBalancedParts ParenBalancedParts (ihinit rfl)
    intro b hb
    exact ensures_pure _ ParenBalancedParts (parenBalancedParts_singleton (.append (parenBalancedParts_flat ha) (parenBalanced_optional b hb (fun ts => pu .assign ++ ts) (fun ts ht => .append (parenBalanced_punct .assign (by intro h; cases h) (by intro h; cases h)) ht))))
  | declTuple holes decl decls e ihdecl ihdecls ihe =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ ParenBalancedParts ParenBalancedParts (ihdecl rfl)
    intro a ha
    apply ensures_bind_checked _ _ ParenBalancedParts ParenBalancedParts (ihdecls rfl)
    intro b hb
    apply ensures_bind_checked _ _ ParenBalancedParts ParenBalancedParts (ihe rfl)
    intro c hc
    apply ensures_pure _ ParenBalancedParts
    apply parenBalancedParts_singleton
    have framed : ParenBalanced
        ((parens (((List.replicate holes (pu .comma)).flatten ++ a.flatten) ++
          b.flatMap (pu .comma ++ ·)) ++ pu .assign) ++ c.flatten) :=
      .append (.append (parenBalanced_parens
        (.append (.append (parenBalancedParts_flat
          (parenBalancedParts_replicate holes (pu .comma)
            (parenBalanced_punct .comma (by intro h; cases h) (by intro h; cases h))))
          (parenBalancedParts_flat ha))
          (parenBalanced_flatMap_prefix b (pu .comma) hb
            (parenBalanced_punct .comma (by intro h; cases h) (by intro h; cases h)))))
        (parenBalanced_punct .assign (by intro h; cases h) (by intro h; cases h)))
        (parenBalancedParts_flat hc)
    simpa only [parens, List.append_assoc] using framed
  | exprStmt e ih => intro _h; exact ih rfl
  | blockStmt b ih => intro _h; exact ih rfl
  | stmtItem s ih => intro _h; exact ih rfl
  | yulExprStmt e ih => intro _h; exact ih rfl
  | simpleStmt simple ihsimple =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ ParenBalancedParts ParenBalancedParts (ihsimple rfl)
    intro a ha
    exact ensures_pure _ ParenBalancedParts (parenBalancedParts_singleton (.append (parenBalancedParts_flat ha) (parenBalanced_punct .semi (by intro h; cases h) (by intro h; cases h))))
  | ifStmt c t e ihc iht ihe =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ ParenBalancedParts ParenBalancedParts (ihc rfl)
    intro a ha
    apply ensures_bind_checked _ _ ParenBalancedParts ParenBalancedParts (iht rfl)
    intro b hb
    apply ensures_bind_checked _ _ ParenBalancedParts ParenBalancedParts (ihe rfl)
    intro c hc
    exact ensures_pure _ ParenBalancedParts (parenBalancedParts_singleton (.append (.append (.append (parenBalanced_kw .if_) (parenBalanced_parens (parenBalancedParts_flat ha))) (parenBalancedParts_flat hb)) (parenBalanced_optional c hc (fun ts => tk .else_ ++ ts) (fun ts ht => .append (parenBalanced_kw .else_) ht))))
  | forStmt i c v b ihi ihc ihv ihb =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ ParenBalancedParts ParenBalancedParts (ihi rfl)
    intro a ha
    apply ensures_bind_checked _ _ ParenBalancedParts ParenBalancedParts (ihc rfl)
    intro b hb
    apply ensures_bind_checked _ _ ParenBalancedParts ParenBalancedParts (ihv rfl)
    intro c hc
    apply ensures_bind_checked _ _ ParenBalancedParts ParenBalancedParts (ihb rfl)
    intro d hd
    exact ensures_pure _ ParenBalancedParts (parenBalancedParts_singleton (.append (.append (parenBalanced_kw .for_) (parenBalanced_parens (.append (.append (.append (.append (parenBalancedParts_flat ha) (parenBalanced_punct .semi (by intro h; cases h) (by intro h; cases h))) (parenBalancedParts_flat hb)) (parenBalanced_punct .semi (by intro h; cases h) (by intro h; cases h))) (parenBalancedParts_flat hc)))) (parenBalancedParts_flat hd)))
  | whileStmt c b ihc ihb =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ ParenBalancedParts ParenBalancedParts (ihc rfl)
    intro a ha
    apply ensures_bind_checked _ _ ParenBalancedParts ParenBalancedParts (ihb rfl)
    intro b hb
    exact ensures_pure _ ParenBalancedParts (parenBalancedParts_singleton (.append (.append (parenBalanced_kw .while_) (parenBalanced_parens (parenBalancedParts_flat ha))) (parenBalancedParts_flat hb)))
  | doWhile b c ihb ihc =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ ParenBalancedParts ParenBalancedParts (ihb rfl)
    intro a ha
    apply ensures_bind_checked _ _ ParenBalancedParts ParenBalancedParts (ihc rfl)
    intro b hb
    exact ensures_pure _ ParenBalancedParts (parenBalancedParts_singleton (.append (.append (.append (.append (parenBalanced_kw .do_) (parenBalancedParts_flat ha)) (parenBalanced_kw .while_)) (parenBalanced_parens (parenBalancedParts_flat hb))) (parenBalanced_punct .semi (by intro h; cases h) (by intro h; cases h))))
  | continueStmt  =>
    intro _h
    rw [Syn.yield]
    exact ensures_pure _ ParenBalancedParts (parenBalancedParts_singleton (.append (parenBalanced_kw .continue_) (parenBalanced_punct .semi (by intro h; cases h) (by intro h; cases h))))
  | breakStmt  =>
    intro _h
    rw [Syn.yield]
    exact ensures_pure _ ParenBalancedParts (parenBalancedParts_singleton (.append (parenBalanced_kw .break_) (parenBalanced_punct .semi (by intro h; cases h) (by intro h; cases h))))
  | tryStmt e rets body handler catches ihe ihrets ihbody ihhandler ihhandleres =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ ParenBalancedParts ParenBalancedParts (ihe rfl)
    intro a ha
    apply ensures_bind_checked _ _ ParenBalancedParts ParenBalancedParts (ihrets rfl)
    intro b hb
    apply ensures_bind_checked _ _ ParenBalancedParts ParenBalancedParts (ihbody rfl)
    intro c hc
    apply ensures_bind_checked _ _ ParenBalancedParts ParenBalancedParts (ihhandler rfl)
    intro d hd
    apply ensures_bind_checked _ _ ParenBalancedParts ParenBalancedParts (ihhandleres rfl)
    intro e he
    exact ensures_pure _ ParenBalancedParts (parenBalancedParts_singleton (.append (.append (.append (.append (.append (parenBalanced_kw .try_) (parenBalancedParts_flat ha)) (parenBalanced_choice b.isEmpty .empty (.append (parenBalanced_kw .returns) (parenBalanced_parens (parenBalanced_commaSep b hb))))) (parenBalancedParts_flat hc)) (parenBalancedParts_flat hd)) (parenBalancedParts_flat he)))
  | catchPlain b ihb =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ ParenBalancedParts ParenBalancedParts (ihb rfl)
    intro a ha
    exact ensures_pure _ ParenBalancedParts (parenBalancedParts_singleton (.append (parenBalanced_kw .catch_) (parenBalancedParts_flat ha)))
  | catchSig name p ps b ihp ihps ihb =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ ParenBalancedParts ParenBalancedParts (ihp rfl)
    intro a ha
    apply ensures_bind_checked _ _ ParenBalancedParts ParenBalancedParts (ihps rfl)
    intro b hb
    apply ensures_bind_checked _ _ ParenBalancedParts ParenBalancedParts (ihb rfl)
    intro c hc
    exact ensures_pure _ ParenBalancedParts (parenBalancedParts_singleton (.append (.append (.append (parenBalanced_kw .catch_) (parenBalanced_optToks idt parenBalanced_id name)) (parenBalanced_parens (parenBalanced_commaSep (a.flatten :: b) (parenBalancedParts_cons (parenBalancedParts_flat ha) hb)))) (parenBalancedParts_flat hc)))
  | returnStmt e ihe =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ ParenBalancedParts ParenBalancedParts (ihe rfl)
    intro a ha
    exact ensures_pure _ ParenBalancedParts (parenBalancedParts_singleton (.append (.append (parenBalanced_kw .return_) (parenBalancedParts_flat ha)) (parenBalanced_punct .semi (by intro h; cases h) (by intro h; cases h))))
  | emit e args ihe ihargs =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ ParenBalancedParts ParenBalancedParts (ihe rfl)
    intro a ha
    apply ensures_bind_checked _ _ ParenBalancedParts ParenBalancedParts (ihargs rfl)
    intro b hb
    exact ensures_pure _ ParenBalancedParts (parenBalancedParts_singleton (.append (.append (.append (parenBalanced_kw .emit) (parenBalancedParts_flat ha)) (parenBalancedParts_flat hb)) (parenBalanced_punct .semi (by intro h; cases h) (by intro h; cases h))))
  | revert e args ihe ihargs =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ ParenBalancedParts ParenBalancedParts (ihe rfl)
    intro a ha
    apply ensures_bind_checked _ _ ParenBalancedParts ParenBalancedParts (ihargs rfl)
    intro b hb
    exact ensures_pure _ ParenBalancedParts (parenBalancedParts_singleton (.append (.append (.append (parenBalanced_id "revert") (parenBalancedParts_flat ha)) (parenBalancedParts_flat hb)) (parenBalanced_punct .semi (by intro h; cases h) (by intro h; cases h))))
  | assembly evm flags body ihbody =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ ParenBalancedParts ParenBalancedParts (ihbody rfl)
    intro a ha
    exact ensures_pure _ ParenBalancedParts (parenBalancedParts_singleton (.append (.append (.append (parenBalanced_kw .assembly) (parenBalanced_choice evm (.token _ (by intro h; cases h) (by intro h; cases h)) .empty)) (parenBalanced_choice flags.isEmpty .empty (parenBalanced_parens (parenBalanced_commaSep _ (parenBalancedParts_map _ flags (fun _ => (.token _ (by intro h; cases h) (by intro h; cases h)))))))) (.brace (parenBalancedParts_flat ha))))
  | block items ihitems =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ ParenBalancedParts ParenBalancedParts (ihitems rfl)
    intro a ha
    exact ensures_pure _ ParenBalancedParts (parenBalancedParts_singleton (.brace (parenBalancedParts_flat ha)))
  | uncheckedItem b ihb =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ ParenBalancedParts ParenBalancedParts (ihb rfl)
    intro a ha
    exact ensures_pure _ ParenBalancedParts (parenBalancedParts_singleton (.append (parenBalanced_kw .unchecked) (parenBalancedParts_flat ha)))
  | yulBlock ss ihss =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ ParenBalancedParts ParenBalancedParts (ihss rfl)
    intro a ha
    exact ensures_pure _ ParenBalancedParts (parenBalancedParts_singleton (.brace (parenBalancedParts_flat ha)))
  | yulLet first rest e ihe =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ ParenBalancedParts ParenBalancedParts (ihe rfl)
    intro a ha
    exact ensures_pure _ ParenBalancedParts (parenBalancedParts_singleton (.append (.append (.token _ (by intro h; cases h) (by intro h; cases h)) (parenBalanced_commaSep _ (parenBalancedParts_map idt (first :: rest) parenBalanced_id))) (parenBalanced_optional a ha (fun ts => pu .yulAssign ++ ts) (fun ts ht => .append (parenBalanced_punct .yulAssign (by intro h; cases h) (by intro h; cases h)) ht))))
  | yulAssign first rest e ihe =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ ParenBalancedParts ParenBalancedParts (ihe rfl)
    intro a ha
    exact ensures_pure _ ParenBalancedParts (parenBalancedParts_singleton (.append (.append (parenBalanced_commaSep _ (parenBalancedParts_map _ (first :: rest) (fun p => (parenBalancedParts_flat (parenBalanced_intersperse (p.map idt) (pu .period) (parenBalancedParts_map idt p parenBalanced_id) (parenBalanced_punct .period (by intro h; cases h) (by intro h; cases h))))))) (parenBalanced_punct .yulAssign (by intro h; cases h) (by intro h; cases h))) (parenBalancedParts_flat ha)))
  | yulIf c b ihc ihb =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ ParenBalancedParts ParenBalancedParts (ihc rfl)
    intro a ha
    apply ensures_bind_checked _ _ ParenBalancedParts ParenBalancedParts (ihb rfl)
    intro b hb
    exact ensures_pure _ ParenBalancedParts (parenBalancedParts_singleton (.append (.append (.token _ (by intro h; cases h) (by intro h; cases h)) (parenBalancedParts_flat ha)) (.brace (parenBalancedParts_flat hb))))
  | yulFor i c p b ihi ihc ihp ihb =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ ParenBalancedParts ParenBalancedParts (ihi rfl)
    intro a ha
    apply ensures_bind_checked _ _ ParenBalancedParts ParenBalancedParts (ihc rfl)
    intro b hb
    apply ensures_bind_checked _ _ ParenBalancedParts ParenBalancedParts (ihp rfl)
    intro c hc
    apply ensures_bind_checked _ _ ParenBalancedParts ParenBalancedParts (ihb rfl)
    intro d hd
    exact ensures_pure _ ParenBalancedParts (parenBalancedParts_singleton (.append (.append (.append (.append (.token _ (by intro h; cases h) (by intro h; cases h)) (.brace (parenBalancedParts_flat ha))) (parenBalancedParts_flat hb)) (.brace (parenBalancedParts_flat hc))) (.brace (parenBalancedParts_flat hd))))
  | yulSwitch e cs d ihe ihcs ihd =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ ParenBalancedParts ParenBalancedParts (ihe rfl)
    intro a ha
    apply ensures_bind_checked _ _ ParenBalancedParts ParenBalancedParts (ihcs rfl)
    intro b hb
    apply ensures_bind_checked _ _ ParenBalancedParts ParenBalancedParts (ihd rfl)
    intro c hc
    exact ensures_pure _ ParenBalancedParts (parenBalancedParts_singleton (.append (.append (.append (.token _ (by intro h; cases h) (by intro h; cases h)) (parenBalancedParts_flat ha)) (parenBalancedParts_flat hb)) (parenBalanced_optional c hc (fun ts => [Tok.yulKw .default] ++ braces ts) (fun ts ht => .append (.token _ (by intro h; cases h) (by intro h; cases h)) (.brace ht)))))
  | yulCase lit b ihb =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ ParenBalancedParts ParenBalancedParts (ihb rfl)
    intro a ha
    exact ensures_pure _ ParenBalancedParts (parenBalancedParts_singleton (.append (.append (.token _ (by intro h; cases h) (by intro h; cases h)) (parenBalanced_yulLit lit)) (.brace (parenBalancedParts_flat ha))))
  | yulLeave  =>
    intro _h
    rw [Syn.yield]
    exact ensures_pure _ ParenBalancedParts (parenBalancedParts_singleton (.token _ (by intro h; cases h) (by intro h; cases h)))
  | yulBreak  =>
    intro _h
    rw [Syn.yield]
    exact ensures_pure _ ParenBalancedParts (parenBalancedParts_singleton (.token _ (by intro h; cases h) (by intro h; cases h)))
  | yulContinue  =>
    intro _h
    rw [Syn.yield]
    exact ensures_pure _ ParenBalancedParts (parenBalancedParts_singleton (.token _ (by intro h; cases h) (by intro h; cases h)))
  | yulFun name args rets b ihb =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ ParenBalancedParts ParenBalancedParts (ihb rfl)
    intro a ha
    exact ensures_pure _ ParenBalancedParts (parenBalancedParts_singleton (.append (.append (.append (.append (.token _ (by intro h; cases h) (by intro h; cases h)) (parenBalanced_id name)) (parenBalanced_parens (parenBalanced_commaSep _ (parenBalancedParts_map idt args parenBalanced_id)))) (parenBalanced_choice rets.isEmpty .empty (.append (parenBalanced_punct .rightArrow (by intro h; cases h) (by intro h; cases h)) (parenBalanced_commaSep _ (parenBalancedParts_map idt rets parenBalanced_id))))) (.brace (parenBalancedParts_flat ha))))
  | yulPath head tail =>
    intro _h
    rw [Syn.yield]
    exact ensures_pure _ ParenBalancedParts (parenBalancedParts_singleton (parenBalancedParts_flat (parenBalanced_intersperse ((head :: tail).map idt) (pu .period) (parenBalancedParts_map idt (head :: tail) parenBalanced_id) (parenBalanced_punct .period (by intro h; cases h) (by intro h; cases h)))))
  | yulCall fn args ihargs =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ ParenBalancedParts ParenBalancedParts (ihargs rfl)
    intro a ha
    exact ensures_pure _ ParenBalancedParts (parenBalancedParts_singleton (.append (parenBalanced_id fn) (parenBalanced_parens (parenBalanced_commaSep a ha))))
  | yulLit lit =>
    intro _h
    rw [Syn.yield]
    exact ensures_pure _ ParenBalancedParts (parenBalancedParts_singleton (parenBalanced_yulLit lit))
  | _ => intro h; cases h

theorem expression_yield_parentheses (e : Syn .expr) :
    PrEnsures e.yield ParenBalancedParts := syntax_yield_parenBalanced e rfl

theorem statement_yield_parentheses {k : SCtx} (s : Syn (.stmt k)) :
    PrEnsures s.yield ParenBalancedParts := syntax_yield_parenBalanced s rfl

theorem expression_parenthesis_header_split (e f : Syn .expr)
    (L M N P : List Choice) (xs ys : List (List Tok)) (rest tail : List Tok)
    (he : e.yield L = some (xs, M)) (hf : f.yield N = some (ys, P))
    (tokens : parens xs.flatten ++ rest = parens ys.flatten ++ tail) :
    xs.flatten = ys.flatten ∧ rest = tail :=
  parenBalanced_parenthesized_split
    (parenBalancedParts_flat (expression_yield_parentheses e L xs M he))
    (parenBalancedParts_flat (expression_yield_parentheses f N ys P hf)) tokens

theorem syntax_parenthesis_header_suffix {c : Cat} (s : Syn c)
    (hc : ParenBalanceCat c = true) (L M : List Choice)
    (parts : List (List Tok)) (tail : List Tok)
    (hy : s.yield L = some (parts, M)) :
    parenHeaderSuffix (parens parts.flatten ++ tail) = some tail :=
  paren_header_after_balanced
    (parenBalancedParts_flat (syntax_yield_parenBalanced s hc L parts M hy)) tail

end Solidity.Frontend.StatementGrammarH28
