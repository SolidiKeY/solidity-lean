import Solidity.Frontend.StatementGrammarH28.BalanceAtoms
import Solidity.Frontend.StatementGrammarH28.YieldSplit

/-! H31 universal delimiter balance over the immutable syntax closure needed
by statements. This is a token-boundary invariant, not expression uniqueness.
No producer implementation or original theorem statement is changed. -/
namespace Solidity.Frontend.StatementGrammarH28
open Solidity.Source Solidity.Frontend.Checked

def BalanceCat : Cat → Bool
  | .callArgs | .namedArg | .param | .typeName | .varDecl | .expr | .simple
  | .stmt _ | .item _ | .block _ | .catchClause _ | .yulStmt | .yulExpr | .yulCase => true
  | .list c | .opt c => BalanceCat c
  | _ => false

theorem syntax_yield_balanced {c : Cat} (s : Syn c) :
    BalanceCat c = true → PrEnsures s.yield BalancedParts := by
  induction s with
  | nil => intro _h; exact ensures_pure _ BalancedParts balancedParts_nil
  | cons x xs ihx ihxs =>
    intro h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ BalancedParts BalancedParts (ihx h)
    intro a ha
    apply ensures_bind_checked _ _ BalancedParts BalancedParts (ihxs h)
    intro b hb
    exact ensures_pure _ BalancedParts (balancedParts_cons (balancedParts_flat ha) hb)
  | none => intro _h; exact ensures_pure _ BalancedParts balancedParts_nil
  | some x ihx =>
    intro h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ BalancedParts BalancedParts (ihx h)
    intro a ha
    exact ensures_pure _ BalancedParts (balancedParts_singleton (balancedParts_flat ha))
  | positional es ihes =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ BalancedParts BalancedParts (ihes rfl)
    intro a ha
    exact ensures_pure _ BalancedParts (balancedParts_singleton (balanced_parens (balanced_commaSep a ha)))
  | named args ihargs =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ BalancedParts BalancedParts (ihargs rfl)
    intro a ha
    exact ensures_pure _ BalancedParts (balancedParts_singleton (balanced_parens (.wrap (balanced_commaSep a ha))))
  | namedArg name e ihe =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ BalancedParts BalancedParts (ihe rfl)
    intro a ha
    exact ensures_pure _ BalancedParts (balancedParts_singleton (.append (.append (balanced_id name) (balanced_punct .colon (by intro h; cases h) (by intro h; cases h))) (balancedParts_flat ha)))
  | param t loc name iht =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ BalancedParts BalancedParts (iht rfl)
    intro a ha
    exact ensures_pure _ BalancedParts (balancedParts_singleton (.append (.append (balancedParts_flat ha) (balanced_optToks DataLoc.toks balanced_dataLoc loc)) (balanced_optToks idt balanced_id name)))
  | elem e =>
    intro _h
    rw [Syn.yield]
    exact ensures_pure _ BalancedParts (balancedParts_singleton (balanced_elem e))
  | fnType ps vis mu rets ihps ihrets =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind (P := BalancedParts)
    intro order
    apply ensures_bind_checked _ _ BalancedParts BalancedParts (ihps rfl)
    intro a ha
    have hv := balanced_optToks Visibility.toks balanced_visibility vis
    have hm := balanced_optToks Mutability.toks balanced_mutability mu
    have singles : ∀ pair ∈ (single .vis (optToks Visibility.toks vis) ++
        single .mutab (optToks Mutability.toks mu)), BraceBalanced pair.2 := by
      intro pair hp
      cases List.mem_append.mp hp with
      | inl h => exact balanced_single _ _ hv pair h
      | inr h => exact balanced_single _ _ hm pair h
    apply ensures_bind_checked _ _ BraceBalanced BalancedParts
      (attrsP_empty_mods_balanced _ singles order)
    intro attrs hattrs
    apply ensures_bind_checked _ _ BalancedParts BalancedParts (ihrets rfl)
    intro r hr
    exact ensures_pure _ BalancedParts (balancedParts_singleton
      (.append (.append (.append (balanced_kw .function)
        (balanced_parens (balanced_commaSep a ha))) hattrs)
        (balanced_choice r.isEmpty .empty
          (.append (balanced_kw .returns) (balanced_parens (balanced_commaSep r hr))))))
  | mapping key kn v vn ihv =>
    intro _h
    cases key with
    | elem elemType _he =>
      rw [Syn.yield]
      apply ensures_bind_checked _ _ BalancedParts BalancedParts (ihv rfl)
      intro a ha
      exact ensures_pure _ BalancedParts (balancedParts_singleton
        (.append (balanced_kw .mapping) (balanced_parens
          (.append (.append (.append (.append (balanced_elem elemType)
            (balanced_optToks idt balanced_id kn))
            (balanced_punct .doubleArrow (by intro h; cases h) (by intro h; cases h)))
            (balancedParts_flat ha)) (balanced_optToks idt balanced_id vn)))))
    | path path =>
      rw [Syn.yield]
      apply ensures_bind_checked _ _ BalancedParts BalancedParts (ihv rfl)
      intro a ha
      exact ensures_pure _ BalancedParts (balancedParts_singleton
        (.append (balanced_kw .mapping) (balanced_parens
          (.append (.append (.append (.append (balanced_path path)
            (balanced_optToks idt balanced_id kn))
            (balanced_punct .doubleArrow (by intro h; cases h) (by intro h; cases h)))
            (balancedParts_flat ha)) (balanced_optToks idt balanced_id vn)))))
  | userType p =>
    intro _h
    rw [Syn.yield]
    exact ensures_pure _ BalancedParts (balancedParts_singleton (balanced_path p))
  | array t len iht ihlen =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ BalancedParts BalancedParts (iht rfl)
    intro a ha
    apply ensures_bind_checked _ _ BalancedParts BalancedParts (ihlen rfl)
    intro b hb
    exact ensures_pure _ BalancedParts (balancedParts_singleton (.append (.append (.append (balancedParts_flat ha) (balanced_punct .lbrack (by intro h; cases h) (by intro h; cases h))) (balancedParts_flat hb)) (balanced_punct .rbrack (by intro h; cases h) (by intro h; cases h))))
  | varDecl t loc name iht =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ BalancedParts BalancedParts (iht rfl)
    intro a ha
    exact ensures_pure _ BalancedParts (balancedParts_singleton (.append (.append (balancedParts_flat ha) (balanced_optToks DataLoc.toks balanced_dataLoc loc)) (balanced_id name)))
  | index e i ihe ihi =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ BalancedParts BalancedParts (ihe rfl)
    intro a ha
    apply ensures_bind_checked _ _ BalancedParts BalancedParts (ihi rfl)
    intro b hb
    exact ensures_pure _ BalancedParts (balancedParts_singleton (.append (.append (.append (balancedParts_flat ha) (balanced_punct .lbrack (by intro h; cases h) (by intro h; cases h))) (balancedParts_flat hb)) (balanced_punct .rbrack (by intro h; cases h) (by intro h; cases h))))
  | slice e i j ihe ihi ihj =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ BalancedParts BalancedParts (ihe rfl)
    intro a ha
    apply ensures_bind_checked _ _ BalancedParts BalancedParts (ihi rfl)
    intro b hb
    apply ensures_bind_checked _ _ BalancedParts BalancedParts (ihj rfl)
    intro c hc
    exact ensures_pure _ BalancedParts (balancedParts_singleton (.append (.append (.append (.append (.append (balancedParts_flat ha) (balanced_punct .lbrack (by intro h; cases h) (by intro h; cases h))) (balancedParts_flat hb)) (balanced_punct .colon (by intro h; cases h) (by intro h; cases h))) (balancedParts_flat hc)) (balanced_punct .rbrack (by intro h; cases h) (by intro h; cases h))))
  | member e name ihe =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ BalancedParts BalancedParts (ihe rfl)
    intro a ha
    exact ensures_pure _ BalancedParts (balancedParts_singleton (.append (.append (balancedParts_flat ha) (balanced_punct .period (by intro h; cases h) (by intro h; cases h))) (balanced_choice (name == "address") (.token _ (by intro h; cases h) (by intro h; cases h)) (balanced_id name))))
  | callOptions e arg args ihe iharg ihargs =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ BalancedParts BalancedParts (ihe rfl)
    intro a ha
    apply ensures_bind_checked _ _ BalancedParts BalancedParts (iharg rfl)
    intro b hb
    apply ensures_bind_checked _ _ BalancedParts BalancedParts (ihargs rfl)
    intro c hc
    exact ensures_pure _ BalancedParts (balancedParts_singleton (.append (balancedParts_flat ha) (.wrap (balanced_commaSep (b.flatten :: c) (balancedParts_cons (balancedParts_flat hb) hc)))))
  | call e args ihe ihargs =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ BalancedParts BalancedParts (ihe rfl)
    intro a ha
    apply ensures_bind_checked _ _ BalancedParts BalancedParts (ihargs rfl)
    intro b hb
    exact ensures_pure _ BalancedParts (balancedParts_singleton (.append (balancedParts_flat ha) (balancedParts_flat hb)))
  | payableConv args ihargs =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ BalancedParts BalancedParts (ihargs rfl)
    intro a ha
    exact ensures_pure _ BalancedParts (balancedParts_singleton (.append (balanced_kw .payable) (balancedParts_flat ha)))
  | metaType t iht =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ BalancedParts BalancedParts (iht rfl)
    intro a ha
    exact ensures_pure _ BalancedParts (balancedParts_singleton (.append (balanced_kw .type_) (balanced_parens (balancedParts_flat ha))))
  | unaryPrefix op e ihe =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ BalancedParts BalancedParts (ihe rfl)
    intro a ha
    exact ensures_pure _ BalancedParts (balancedParts_singleton (.append (balanced_prefix op) (balancedParts_flat ha)))
  | unarySuffix op e ihe =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ BalancedParts BalancedParts (ihe rfl)
    intro a ha
    exact ensures_pure _ BalancedParts (balancedParts_singleton (.append (balancedParts_flat ha) (balanced_suffix op)))
  | exp left right ihleft ihright =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ BalancedParts BalancedParts (ihleft rfl)
    intro a ha
    apply ensures_bind_checked _ _ BalancedParts BalancedParts (ihright rfl)
    intro b hb
    exact ensures_pure _ BalancedParts (balancedParts_singleton (.append (.append (balancedParts_flat ha) (balanced_punct .exp (by intro h; cases h) (by intro h; cases h))) (balancedParts_flat hb)))
  | mulDivMod op left right ihleft ihright =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ BalancedParts BalancedParts (ihleft rfl)
    intro a ha
    apply ensures_bind_checked _ _ BalancedParts BalancedParts (ihright rfl)
    intro b hb
    exact ensures_pure _ BalancedParts (balancedParts_singleton (.append (.append (balancedParts_flat ha) (balanced_mul op)) (balancedParts_flat hb)))
  | addSub op left right ihleft ihright =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ BalancedParts BalancedParts (ihleft rfl)
    intro a ha
    apply ensures_bind_checked _ _ BalancedParts BalancedParts (ihright rfl)
    intro b hb
    exact ensures_pure _ BalancedParts (balancedParts_singleton (.append (.append (balancedParts_flat ha) (balanced_add op)) (balancedParts_flat hb)))
  | shift op left right ihleft ihright =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ BalancedParts BalancedParts (ihleft rfl)
    intro a ha
    apply ensures_bind_checked _ _ BalancedParts BalancedParts (ihright rfl)
    intro b hb
    exact ensures_pure _ BalancedParts (balancedParts_singleton (.append (.append (balancedParts_flat ha) (balanced_shift op)) (balancedParts_flat hb)))
  | bitAnd left right ihleft ihright =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ BalancedParts BalancedParts (ihleft rfl)
    intro a ha
    apply ensures_bind_checked _ _ BalancedParts BalancedParts (ihright rfl)
    intro b hb
    exact ensures_pure _ BalancedParts (balancedParts_singleton (.append (.append (balancedParts_flat ha) (balanced_punct .bitAnd (by intro h; cases h) (by intro h; cases h))) (balancedParts_flat hb)))
  | bitXor left right ihleft ihright =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ BalancedParts BalancedParts (ihleft rfl)
    intro a ha
    apply ensures_bind_checked _ _ BalancedParts BalancedParts (ihright rfl)
    intro b hb
    exact ensures_pure _ BalancedParts (balancedParts_singleton (.append (.append (balancedParts_flat ha) (balanced_punct .bitXor (by intro h; cases h) (by intro h; cases h))) (balancedParts_flat hb)))
  | bitOr left right ihleft ihright =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ BalancedParts BalancedParts (ihleft rfl)
    intro a ha
    apply ensures_bind_checked _ _ BalancedParts BalancedParts (ihright rfl)
    intro b hb
    exact ensures_pure _ BalancedParts (balancedParts_singleton (.append (.append (balancedParts_flat ha) (balanced_punct .bitOr (by intro h; cases h) (by intro h; cases h))) (balancedParts_flat hb)))
  | order op left right ihleft ihright =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ BalancedParts BalancedParts (ihleft rfl)
    intro a ha
    apply ensures_bind_checked _ _ BalancedParts BalancedParts (ihright rfl)
    intro b hb
    exact ensures_pure _ BalancedParts (balancedParts_singleton (.append (.append (balancedParts_flat ha) (balanced_order op)) (balancedParts_flat hb)))
  | equality op left right ihleft ihright =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ BalancedParts BalancedParts (ihleft rfl)
    intro a ha
    apply ensures_bind_checked _ _ BalancedParts BalancedParts (ihright rfl)
    intro b hb
    exact ensures_pure _ BalancedParts (balancedParts_singleton (.append (.append (balancedParts_flat ha) (balanced_equality op)) (balancedParts_flat hb)))
  | and left right ihleft ihright =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ BalancedParts BalancedParts (ihleft rfl)
    intro a ha
    apply ensures_bind_checked _ _ BalancedParts BalancedParts (ihright rfl)
    intro b hb
    exact ensures_pure _ BalancedParts (balancedParts_singleton (.append (.append (balancedParts_flat ha) (balanced_punct .and (by intro h; cases h) (by intro h; cases h))) (balancedParts_flat hb)))
  | or left right ihleft ihright =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ BalancedParts BalancedParts (ihleft rfl)
    intro a ha
    apply ensures_bind_checked _ _ BalancedParts BalancedParts (ihright rfl)
    intro b hb
    exact ensures_pure _ BalancedParts (balancedParts_singleton (.append (.append (balancedParts_flat ha) (balanced_punct .or (by intro h; cases h) (by intro h; cases h))) (balancedParts_flat hb)))
  | assign op left right ihleft ihright =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ BalancedParts BalancedParts (ihleft rfl)
    intro a ha
    apply ensures_bind_checked _ _ BalancedParts BalancedParts (ihright rfl)
    intro b hb
    exact ensures_pure _ BalancedParts (balancedParts_singleton (.append (.append (balancedParts_flat ha) (balanced_assign op)) (balancedParts_flat hb)))
  | cond cond yes no ihcond ihyes ihno =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ BalancedParts BalancedParts (ihcond rfl)
    intro a ha
    apply ensures_bind_checked _ _ BalancedParts BalancedParts (ihyes rfl)
    intro b hb
    apply ensures_bind_checked _ _ BalancedParts BalancedParts (ihno rfl)
    intro c hc
    exact ensures_pure _ BalancedParts (balancedParts_singleton (.append (.append (.append (.append (balancedParts_flat ha) (balanced_punct .question (by intro h; cases h) (by intro h; cases h))) (balancedParts_flat hb)) (balanced_punct .colon (by intro h; cases h) (by intro h; cases h))) (balancedParts_flat hc)))
  | new t iht =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ BalancedParts BalancedParts (iht rfl)
    intro a ha
    exact ensures_pure _ BalancedParts (balancedParts_singleton (.append (balanced_kw .new) (balancedParts_flat ha)))
  | tuple first rest ihfirst ihrest =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ BalancedParts BalancedParts (ihfirst rfl)
    intro a ha
    apply ensures_bind_checked _ _ BalancedParts BalancedParts (ihrest rfl)
    intro b hb
    exact ensures_pure _ BalancedParts (balancedParts_singleton (balanced_parens (.append (balancedParts_flat ha) (balanced_flatMap_prefix b (pu .comma) hb (balanced_punct .comma (by intro h; cases h) (by intro h; cases h))))))
  | inlineArray first rest ihfirst ihrest =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ BalancedParts BalancedParts (ihfirst rfl)
    intro a ha
    apply ensures_bind_checked _ _ BalancedParts BalancedParts (ihrest rfl)
    intro b hb
    exact ensures_pure _ BalancedParts (balancedParts_singleton (.append (.append (balanced_punct .lbrack (by intro h; cases h) (by intro h; cases h)) (balanced_commaSep (a.flatten :: b) (balancedParts_cons (balancedParts_flat ha) hb))) (balanced_punct .rbrack (by intro h; cases h) (by intro h; cases h))))
  | ident name =>
    intro _h
    rw [Syn.yield]
    exact ensures_pure _ BalancedParts (balancedParts_singleton (balanced_id name))
  | lit lit =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ BraceBalanced BalancedParts (litP_balanced lit)
    intro ts ht
    exact ensures_pure _ BalancedParts (balancedParts_singleton ht)
  | litUnit n u =>
    intro _h
    rw [Syn.yield]
    exact ensures_pure _ BalancedParts (balancedParts_singleton (.append (.token _ (by intro h; cases h) (by intro h; cases h)) (.token _ (by intro h; cases h) (by intro h; cases h))))
  | elemType e he =>
    intro _h
    rw [Syn.yield]
    exact ensures_pure _ BalancedParts (balancedParts_singleton (balanced_elem_atom e))
  | declVar decl init ihdecl ihinit =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ BalancedParts BalancedParts (ihdecl rfl)
    intro a ha
    apply ensures_bind_checked _ _ BalancedParts BalancedParts (ihinit rfl)
    intro b hb
    exact ensures_pure _ BalancedParts (balancedParts_singleton (.append (balancedParts_flat ha) (balanced_optional b hb (fun ts => pu .assign ++ ts) (fun ts ht => .append (balanced_punct .assign (by intro h; cases h) (by intro h; cases h)) ht))))
  | declTuple holes decl decls e ihdecl ihdecls ihe =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ BalancedParts BalancedParts (ihdecl rfl)
    intro a ha
    apply ensures_bind_checked _ _ BalancedParts BalancedParts (ihdecls rfl)
    intro b hb
    apply ensures_bind_checked _ _ BalancedParts BalancedParts (ihe rfl)
    intro c hc
    exact ensures_pure _ BalancedParts (balancedParts_singleton (.append (.append (.append (.append (.append (.append (balanced_punct .lparen (by intro h; cases h) (by intro h; cases h)) (balancedParts_flat (balancedParts_replicate holes (pu .comma) (balanced_punct .comma (by intro h; cases h) (by intro h; cases h))))) (balancedParts_flat ha)) (balanced_flatMap_prefix b (pu .comma) hb (balanced_punct .comma (by intro h; cases h) (by intro h; cases h)))) (balanced_punct .rparen (by intro h; cases h) (by intro h; cases h))) (balanced_punct .assign (by intro h; cases h) (by intro h; cases h))) (balancedParts_flat hc)))
  | exprStmt e ih => intro _h; exact ih rfl
  | blockStmt b ih => intro _h; exact ih rfl
  | stmtItem s ih => intro _h; exact ih rfl
  | yulExprStmt e ih => intro _h; exact ih rfl
  | simpleStmt simple ihsimple =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ BalancedParts BalancedParts (ihsimple rfl)
    intro a ha
    exact ensures_pure _ BalancedParts (balancedParts_singleton (.append (balancedParts_flat ha) (balanced_punct .semi (by intro h; cases h) (by intro h; cases h))))
  | ifStmt c t e ihc iht ihe =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ BalancedParts BalancedParts (ihc rfl)
    intro a ha
    apply ensures_bind_checked _ _ BalancedParts BalancedParts (iht rfl)
    intro b hb
    apply ensures_bind_checked _ _ BalancedParts BalancedParts (ihe rfl)
    intro c hc
    exact ensures_pure _ BalancedParts (balancedParts_singleton (.append (.append (.append (balanced_kw .if_) (balanced_parens (balancedParts_flat ha))) (balancedParts_flat hb)) (balanced_optional c hc (fun ts => tk .else_ ++ ts) (fun ts ht => .append (balanced_kw .else_) ht))))
  | forStmt i c v b ihi ihc ihv ihb =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ BalancedParts BalancedParts (ihi rfl)
    intro a ha
    apply ensures_bind_checked _ _ BalancedParts BalancedParts (ihc rfl)
    intro b hb
    apply ensures_bind_checked _ _ BalancedParts BalancedParts (ihv rfl)
    intro c hc
    apply ensures_bind_checked _ _ BalancedParts BalancedParts (ihb rfl)
    intro d hd
    exact ensures_pure _ BalancedParts (balancedParts_singleton (.append (.append (balanced_kw .for_) (balanced_parens (.append (.append (.append (.append (balancedParts_flat ha) (balanced_punct .semi (by intro h; cases h) (by intro h; cases h))) (balancedParts_flat hb)) (balanced_punct .semi (by intro h; cases h) (by intro h; cases h))) (balancedParts_flat hc)))) (balancedParts_flat hd)))
  | whileStmt c b ihc ihb =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ BalancedParts BalancedParts (ihc rfl)
    intro a ha
    apply ensures_bind_checked _ _ BalancedParts BalancedParts (ihb rfl)
    intro b hb
    exact ensures_pure _ BalancedParts (balancedParts_singleton (.append (.append (balanced_kw .while_) (balanced_parens (balancedParts_flat ha))) (balancedParts_flat hb)))
  | doWhile b c ihb ihc =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ BalancedParts BalancedParts (ihb rfl)
    intro a ha
    apply ensures_bind_checked _ _ BalancedParts BalancedParts (ihc rfl)
    intro b hb
    exact ensures_pure _ BalancedParts (balancedParts_singleton (.append (.append (.append (.append (balanced_kw .do_) (balancedParts_flat ha)) (balanced_kw .while_)) (balanced_parens (balancedParts_flat hb))) (balanced_punct .semi (by intro h; cases h) (by intro h; cases h))))
  | continueStmt  =>
    intro _h
    rw [Syn.yield]
    exact ensures_pure _ BalancedParts (balancedParts_singleton (.append (balanced_kw .continue_) (balanced_punct .semi (by intro h; cases h) (by intro h; cases h))))
  | breakStmt  =>
    intro _h
    rw [Syn.yield]
    exact ensures_pure _ BalancedParts (balancedParts_singleton (.append (balanced_kw .break_) (balanced_punct .semi (by intro h; cases h) (by intro h; cases h))))
  | tryStmt e rets body handler catches ihe ihrets ihbody ihhandler ihhandleres =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ BalancedParts BalancedParts (ihe rfl)
    intro a ha
    apply ensures_bind_checked _ _ BalancedParts BalancedParts (ihrets rfl)
    intro b hb
    apply ensures_bind_checked _ _ BalancedParts BalancedParts (ihbody rfl)
    intro c hc
    apply ensures_bind_checked _ _ BalancedParts BalancedParts (ihhandler rfl)
    intro d hd
    apply ensures_bind_checked _ _ BalancedParts BalancedParts (ihhandleres rfl)
    intro e he
    exact ensures_pure _ BalancedParts (balancedParts_singleton (.append (.append (.append (.append (.append (balanced_kw .try_) (balancedParts_flat ha)) (balanced_choice b.isEmpty .empty (.append (balanced_kw .returns) (balanced_parens (balanced_commaSep b hb))))) (balancedParts_flat hc)) (balancedParts_flat hd)) (balancedParts_flat he)))
  | catchPlain b ihb =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ BalancedParts BalancedParts (ihb rfl)
    intro a ha
    exact ensures_pure _ BalancedParts (balancedParts_singleton (.append (balanced_kw .catch_) (balancedParts_flat ha)))
  | catchSig name p ps b ihp ihps ihb =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ BalancedParts BalancedParts (ihp rfl)
    intro a ha
    apply ensures_bind_checked _ _ BalancedParts BalancedParts (ihps rfl)
    intro b hb
    apply ensures_bind_checked _ _ BalancedParts BalancedParts (ihb rfl)
    intro c hc
    exact ensures_pure _ BalancedParts (balancedParts_singleton (.append (.append (.append (balanced_kw .catch_) (balanced_optToks idt balanced_id name)) (balanced_parens (balanced_commaSep (a.flatten :: b) (balancedParts_cons (balancedParts_flat ha) hb)))) (balancedParts_flat hc)))
  | returnStmt e ihe =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ BalancedParts BalancedParts (ihe rfl)
    intro a ha
    exact ensures_pure _ BalancedParts (balancedParts_singleton (.append (.append (balanced_kw .return_) (balancedParts_flat ha)) (balanced_punct .semi (by intro h; cases h) (by intro h; cases h))))
  | emit e args ihe ihargs =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ BalancedParts BalancedParts (ihe rfl)
    intro a ha
    apply ensures_bind_checked _ _ BalancedParts BalancedParts (ihargs rfl)
    intro b hb
    exact ensures_pure _ BalancedParts (balancedParts_singleton (.append (.append (.append (balanced_kw .emit) (balancedParts_flat ha)) (balancedParts_flat hb)) (balanced_punct .semi (by intro h; cases h) (by intro h; cases h))))
  | revert e args ihe ihargs =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ BalancedParts BalancedParts (ihe rfl)
    intro a ha
    apply ensures_bind_checked _ _ BalancedParts BalancedParts (ihargs rfl)
    intro b hb
    exact ensures_pure _ BalancedParts (balancedParts_singleton (.append (.append (.append (balanced_id "revert") (balancedParts_flat ha)) (balancedParts_flat hb)) (balanced_punct .semi (by intro h; cases h) (by intro h; cases h))))
  | assembly evm flags body ihbody =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ BalancedParts BalancedParts (ihbody rfl)
    intro a ha
    exact ensures_pure _ BalancedParts (balancedParts_singleton (.append (.append (.append (balanced_kw .assembly) (balanced_choice evm (.token _ (by intro h; cases h) (by intro h; cases h)) .empty)) (balanced_choice flags.isEmpty .empty (balanced_parens (balanced_commaSep _ (balancedParts_map _ flags (fun _ => (.token _ (by intro h; cases h) (by intro h; cases h)))))))) (.wrap (balancedParts_flat ha))))
  | block items ihitems =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ BalancedParts BalancedParts (ihitems rfl)
    intro a ha
    exact ensures_pure _ BalancedParts (balancedParts_singleton (.wrap (balancedParts_flat ha)))
  | uncheckedItem b ihb =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ BalancedParts BalancedParts (ihb rfl)
    intro a ha
    exact ensures_pure _ BalancedParts (balancedParts_singleton (.append (balanced_kw .unchecked) (balancedParts_flat ha)))
  | yulBlock ss ihss =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ BalancedParts BalancedParts (ihss rfl)
    intro a ha
    exact ensures_pure _ BalancedParts (balancedParts_singleton (.wrap (balancedParts_flat ha)))
  | yulLet first rest e ihe =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ BalancedParts BalancedParts (ihe rfl)
    intro a ha
    exact ensures_pure _ BalancedParts (balancedParts_singleton (.append (.append (.token _ (by intro h; cases h) (by intro h; cases h)) (balanced_commaSep _ (balancedParts_map idt (first :: rest) balanced_id))) (balanced_optional a ha (fun ts => pu .yulAssign ++ ts) (fun ts ht => .append (balanced_punct .yulAssign (by intro h; cases h) (by intro h; cases h)) ht))))
  | yulAssign first rest e ihe =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ BalancedParts BalancedParts (ihe rfl)
    intro a ha
    exact ensures_pure _ BalancedParts (balancedParts_singleton (.append (.append (balanced_commaSep _ (balancedParts_map _ (first :: rest) (fun p => (balancedParts_flat (balanced_intersperse (p.map idt) (pu .period) (balancedParts_map idt p balanced_id) (balanced_punct .period (by intro h; cases h) (by intro h; cases h))))))) (balanced_punct .yulAssign (by intro h; cases h) (by intro h; cases h))) (balancedParts_flat ha)))
  | yulIf c b ihc ihb =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ BalancedParts BalancedParts (ihc rfl)
    intro a ha
    apply ensures_bind_checked _ _ BalancedParts BalancedParts (ihb rfl)
    intro b hb
    exact ensures_pure _ BalancedParts (balancedParts_singleton (.append (.append (.token _ (by intro h; cases h) (by intro h; cases h)) (balancedParts_flat ha)) (.wrap (balancedParts_flat hb))))
  | yulFor i c p b ihi ihc ihp ihb =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ BalancedParts BalancedParts (ihi rfl)
    intro a ha
    apply ensures_bind_checked _ _ BalancedParts BalancedParts (ihc rfl)
    intro b hb
    apply ensures_bind_checked _ _ BalancedParts BalancedParts (ihp rfl)
    intro c hc
    apply ensures_bind_checked _ _ BalancedParts BalancedParts (ihb rfl)
    intro d hd
    exact ensures_pure _ BalancedParts (balancedParts_singleton (.append (.append (.append (.append (.token _ (by intro h; cases h) (by intro h; cases h)) (.wrap (balancedParts_flat ha))) (balancedParts_flat hb)) (.wrap (balancedParts_flat hc))) (.wrap (balancedParts_flat hd))))
  | yulSwitch e cs d ihe ihcs ihd =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ BalancedParts BalancedParts (ihe rfl)
    intro a ha
    apply ensures_bind_checked _ _ BalancedParts BalancedParts (ihcs rfl)
    intro b hb
    apply ensures_bind_checked _ _ BalancedParts BalancedParts (ihd rfl)
    intro c hc
    exact ensures_pure _ BalancedParts (balancedParts_singleton (.append (.append (.append (.token _ (by intro h; cases h) (by intro h; cases h)) (balancedParts_flat ha)) (balancedParts_flat hb)) (balanced_optional c hc (fun ts => [Tok.yulKw .default] ++ braces ts) (fun ts ht => .append (.token _ (by intro h; cases h) (by intro h; cases h)) (.wrap ht)))))
  | yulCase lit b ihb =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ BalancedParts BalancedParts (ihb rfl)
    intro a ha
    exact ensures_pure _ BalancedParts (balancedParts_singleton (.append (.append (.token _ (by intro h; cases h) (by intro h; cases h)) (balanced_yulLit lit)) (.wrap (balancedParts_flat ha))))
  | yulLeave  =>
    intro _h
    rw [Syn.yield]
    exact ensures_pure _ BalancedParts (balancedParts_singleton (.token _ (by intro h; cases h) (by intro h; cases h)))
  | yulBreak  =>
    intro _h
    rw [Syn.yield]
    exact ensures_pure _ BalancedParts (balancedParts_singleton (.token _ (by intro h; cases h) (by intro h; cases h)))
  | yulContinue  =>
    intro _h
    rw [Syn.yield]
    exact ensures_pure _ BalancedParts (balancedParts_singleton (.token _ (by intro h; cases h) (by intro h; cases h)))
  | yulFun name args rets b ihb =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ BalancedParts BalancedParts (ihb rfl)
    intro a ha
    exact ensures_pure _ BalancedParts (balancedParts_singleton (.append (.append (.append (.append (.token _ (by intro h; cases h) (by intro h; cases h)) (balanced_id name)) (balanced_parens (balanced_commaSep _ (balancedParts_map idt args balanced_id)))) (balanced_choice rets.isEmpty .empty (.append (balanced_punct .rightArrow (by intro h; cases h) (by intro h; cases h)) (balanced_commaSep _ (balancedParts_map idt rets balanced_id))))) (.wrap (balancedParts_flat ha))))
  | yulPath head tail =>
    intro _h
    rw [Syn.yield]
    exact ensures_pure _ BalancedParts (balancedParts_singleton (balancedParts_flat (balanced_intersperse ((head :: tail).map idt) (pu .period) (balancedParts_map idt (head :: tail) balanced_id) (balanced_punct .period (by intro h; cases h) (by intro h; cases h)))))
  | yulCall fn args ihargs =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ BalancedParts BalancedParts (ihargs rfl)
    intro a ha
    exact ensures_pure _ BalancedParts (balancedParts_singleton (.append (balanced_id fn) (balanced_parens (balanced_commaSep a ha))))
  | yulLit lit =>
    intro _h
    rw [Syn.yield]
    exact ensures_pure _ BalancedParts (balancedParts_singleton (balanced_yulLit lit))
  | _ => intro h; cases h

/-- All successful expression yields are brace balanced, without any
expression uniqueness or parser-success assumption. -/
theorem expression_yield_balanced (e : Syn .expr) : PrEnsures e.yield BalancedParts :=
  syntax_yield_balanced e rfl

theorem statement_yield_balanced {k : SCtx} (s : Syn (.stmt k)) :
    PrEnsures s.yield BalancedParts := syntax_yield_balanced s rfl

theorem arbitrary_block_boundary {k : SCtx} (items : Syn (.list (.item k)))
    (L M : List Choice) (parts : List (List Tok))
    (h : items.yield L = some (parts, M)) : BlockBoundary (.block items) L M parts.flatten := by
  constructor
  · exact block_yield_of_items items L M parts h
  · exact balancedParts_flat (syntax_yield_balanced items rfl L parts M h)

theorem successful_block_boundary {k : SCtx} (b : Syn (.block k))
    (L M : List Choice) (segments : List (List Tok))
    (h : b.yield L = some (segments, M)) :
    ∃ body, segments = [braces body] ∧ BlockBoundary b L M body := by
  cases b with
  | block items =>
    obtain ⟨parts, hi, hs⟩ := block_yield_decompose items L M segments h
    exact ⟨parts.flatten, hs, arbitrary_block_boundary items L M parts hi⟩

/-- All arbitrary successful block yields have a unique braced content/suffix
split. Contents are tokens; tree equality would require further uniqueness. -/
theorem arbitrary_block_prefix_split {k j : SCtx} (b : Syn (.block k)) (c : Syn (.block j))
    (L M N P : List Choice) (xs ys : List (List Tok)) (rest tail : List Tok)
    (hb : b.yield L = some (xs, M)) (hc : c.yield N = some (ys, P))
    (he : xs.flatten ++ rest = ys.flatten ++ tail) :
    ∃ body, xs = [braces body] ∧ ys = [braces body] ∧ rest = tail := by
  obtain ⟨x, hx, bx⟩ := successful_block_boundary b L M xs hb
  obtain ⟨y, hy, by_⟩ := successful_block_boundary c N P ys hc
  subst xs
  subst ys
  have heads : braces x ++ rest = braces y ++ tail := by
    simpa only [List.flatten_cons, List.flatten_nil, List.append_nil] using he
  obtain ⟨content, suffix⟩ := balanced_braced_split bx.balanced by_.balanced heads
  subst y
  exact ⟨x, rfl, rfl, suffix⟩

#print axioms successful_block_boundary
#print axioms arbitrary_block_prefix_split
#print axioms syntax_yield_balanced
#print axioms expression_yield_balanced
#print axioms statement_yield_balanced
#print axioms arbitrary_block_boundary
end Solidity.Frontend.StatementGrammarH28
