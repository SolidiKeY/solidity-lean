import Solidity.Frontend.StatementGrammarH28.ControlFreeAtoms

/-! Continuation-token absence for every existing inline-Yul constructor.
This is a printer boundary invariant; no Yul execution, expression uniqueness,
parser success, syntax representation or producer interface is introduced. -/
namespace Solidity.Frontend.StatementGrammarH28
open Solidity.Source Solidity.Frontend.Checked

def YulControlCat : Cat → Bool
  | .yulStmt | .yulExpr | .yulCase => true
  | .list c | .opt c => YulControlCat c
  | _ => false

theorem controlFree_yulLit (l : YulLit) : ControlFree l.toks := by
  cases l <;> exact .token _ rfl

theorem yul_yield_controlFree {c : Cat} (s : Syn c) :
    YulControlCat c = true → PrEnsures s.yield ControlFreeParts := by
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
  | yulExprStmt e ih => intro _h; exact ih rfl
  | yulBlock ss ihss =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ ControlFreeParts ControlFreeParts (ihss rfl)
    intro a ha
    exact ensures_pure _ ControlFreeParts (controlFreeParts_singleton (.wrap (controlFreeParts_flat ha)))
  | yulLet first rest e ihe =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ ControlFreeParts ControlFreeParts (ihe rfl)
    intro a ha
    exact ensures_pure _ ControlFreeParts (controlFreeParts_singleton (.append (.append (.token _ rfl) (controlFree_commaSep _ (controlFreeParts_map idt (first :: rest) controlFree_id))) (controlFree_optional a ha (fun ts => pu .yulAssign ++ ts) (fun ts ht => .append (controlFree_punct .yulAssign) ht))))
  | yulAssign first rest e ihe =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ ControlFreeParts ControlFreeParts (ihe rfl)
    intro a ha
    exact ensures_pure _ ControlFreeParts (controlFreeParts_singleton (.append (.append (controlFree_commaSep _ (controlFreeParts_map _ (first :: rest) (fun p => (controlFreeParts_flat (controlFree_intersperse (p.map idt) (pu .period) (controlFreeParts_map idt p controlFree_id) (controlFree_punct .period)))))) (controlFree_punct .yulAssign)) (controlFreeParts_flat ha)))
  | yulIf c b ihc ihb =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ ControlFreeParts ControlFreeParts (ihc rfl)
    intro a ha
    apply ensures_bind_checked _ _ ControlFreeParts ControlFreeParts (ihb rfl)
    intro b hb
    exact ensures_pure _ ControlFreeParts (controlFreeParts_singleton (.append (.append (.token _ rfl) (controlFreeParts_flat ha)) (.wrap (controlFreeParts_flat hb))))
  | yulFor i c p b ihi ihc ihp ihb =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ ControlFreeParts ControlFreeParts (ihi rfl)
    intro a ha
    apply ensures_bind_checked _ _ ControlFreeParts ControlFreeParts (ihc rfl)
    intro b hb
    apply ensures_bind_checked _ _ ControlFreeParts ControlFreeParts (ihp rfl)
    intro c hc
    apply ensures_bind_checked _ _ ControlFreeParts ControlFreeParts (ihb rfl)
    intro d hd
    exact ensures_pure _ ControlFreeParts (controlFreeParts_singleton (.append (.append (.append (.append (.token _ rfl) (.wrap (controlFreeParts_flat ha))) (controlFreeParts_flat hb)) (.wrap (controlFreeParts_flat hc))) (.wrap (controlFreeParts_flat hd))))
  | yulSwitch e cs d ihe ihcs ihd =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ ControlFreeParts ControlFreeParts (ihe rfl)
    intro a ha
    apply ensures_bind_checked _ _ ControlFreeParts ControlFreeParts (ihcs rfl)
    intro b hb
    apply ensures_bind_checked _ _ ControlFreeParts ControlFreeParts (ihd rfl)
    intro c hc
    exact ensures_pure _ ControlFreeParts (controlFreeParts_singleton (.append (.append (.append (.token _ rfl) (controlFreeParts_flat ha)) (controlFreeParts_flat hb)) (controlFree_optional c hc (fun ts => [Tok.yulKw .default] ++ braces ts) (fun ts ht => .append (.token _ rfl) (.wrap ht)))))
  | yulCase lit b ihb =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ ControlFreeParts ControlFreeParts (ihb rfl)
    intro a ha
    exact ensures_pure _ ControlFreeParts (controlFreeParts_singleton (.append (.append (.token _ rfl) (controlFree_yulLit lit)) (.wrap (controlFreeParts_flat ha))))
  | yulLeave  =>
    intro _h
    rw [Syn.yield]
    exact ensures_pure _ ControlFreeParts (controlFreeParts_singleton (.token _ rfl))
  | yulBreak  =>
    intro _h
    rw [Syn.yield]
    exact ensures_pure _ ControlFreeParts (controlFreeParts_singleton (.token _ rfl))
  | yulContinue  =>
    intro _h
    rw [Syn.yield]
    exact ensures_pure _ ControlFreeParts (controlFreeParts_singleton (.token _ rfl))
  | yulFun name args rets b ihb =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ ControlFreeParts ControlFreeParts (ihb rfl)
    intro a ha
    exact ensures_pure _ ControlFreeParts (controlFreeParts_singleton (.append (.append (.append (.append (.token _ rfl) (controlFree_id name)) (controlFree_parens (controlFree_commaSep _ (controlFreeParts_map idt args controlFree_id)))) (controlFree_choice rets.isEmpty .empty (.append (controlFree_punct .rightArrow) (controlFree_commaSep _ (controlFreeParts_map idt rets controlFree_id))))) (.wrap (controlFreeParts_flat ha))))
  | yulPath head tail =>
    intro _h
    rw [Syn.yield]
    exact ensures_pure _ ControlFreeParts (controlFreeParts_singleton (controlFreeParts_flat (controlFree_intersperse ((head :: tail).map idt) (pu .period) (controlFreeParts_map idt (head :: tail) controlFree_id) (controlFree_punct .period))))
  | yulCall fn args ihargs =>
    intro _h
    rw [Syn.yield]
    apply ensures_bind_checked _ _ ControlFreeParts ControlFreeParts (ihargs rfl)
    intro a ha
    exact ensures_pure _ ControlFreeParts (controlFreeParts_singleton (.append (controlFree_id fn) (controlFree_parens (controlFree_commaSep a ha))))
  | yulLit lit =>
    intro _h
    rw [Syn.yield]
    exact ensures_pure _ ControlFreeParts (controlFreeParts_singleton (controlFree_yulLit lit))
  | _ => intro h; cases h

theorem yul_yield_no_continuations {c : Cat} (s : Syn c)
    (hc : YulControlCat c = true) (L M : List Choice)
    (parts : List (List Tok)) (hy : s.yield L = some (parts, M))
    (t : Tok) (hb : boundaryToken t = true) : t ∉ parts.flatten :=
  controlFree_no_boundary
    (controlFreeParts_flat (yul_yield_controlFree s hc L parts M hy)) t hb

theorem assembly_yield_controlFree {k : SCtx} (evm : Bool) (flags : List String)
    (body : Syn (.list .yulStmt)) :
    PrEnsures (Syn.assembly (k := k) evm flags body).yield ControlFreeParts := by
  rw [Syn.yield]
  apply ensures_bind_checked _ _ ControlFreeParts ControlFreeParts
    (yul_yield_controlFree body rfl)
  intro b hb
  exact ensures_pure _ ControlFreeParts (controlFreeParts_singleton
    (.append (.append (.append (controlFree_kw .assembly (by decide))
      (controlFree_choice evm (.token _ rfl) .empty))
      (controlFree_choice flags.isEmpty .empty
        (controlFree_parens (controlFree_commaSep _
          (controlFreeParts_map (fun f => [.str (ascii f)]) flags
            (fun _ => .token _ rfl))))))
      (.wrap (controlFreeParts_flat hb))))

#print axioms controlFree_yulLit
#print axioms yul_yield_controlFree
#print axioms yul_yield_no_continuations
#print axioms assembly_yield_controlFree
end Solidity.Frontend.StatementGrammarH28
