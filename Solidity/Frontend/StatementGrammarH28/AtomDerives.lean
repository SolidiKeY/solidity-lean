import Solidity.Frontend.StatementGrammarH28.AtomNested
import Solidity.Frontend.StatementGrammarH28.AtomYield

/-! Yield and `Derives` uniqueness for the mutual `AtomStmt`/`AtomItems`
fragment.

The printer side of each atom is a stated premise: `Prints t parts` (the
existing printer yields exactly `parts` for `t` and consumes no layout
choice) or `PrintsTo t ts` (its yield flattens to `ts`). `AtomStmtP`,
`AtomItemsP`, `AtomCatchP` and `AtomCatchesP` mirror the four parse relations
with the same token indices and these printer premises on expressions,
simple statements, call arguments, parameters, Yul bodies and assembly flags,
never on statements, items, blocks or catch clauses. With both witnesses a
statement's `Derives` set is exactly its token list
(`atom_stmt_derives_iff`), and two trees deriving the same words are equal
(`atom_stmt_yield_unique`). No expression uniqueness (SOL-EU) is assumed. -/
namespace Solidity.Frontend.StatementGrammarH28
open Solidity.Source Solidity.Frontend.Checked

/-- Layout-free printing: the existing printer yields exactly `parts` for `t`
and consumes no layout choice. -/
def Prints {c : Cat} (t : Syn c) (parts : List (List Tok)) : Prop :=
  ∀ L : List Choice, t.yield L = some (parts, L)

/-- Layout-free printing up to the flattening every parent applies. -/
def PrintsTo {c : Cat} (t : Syn c) (ts : List Tok) : Prop :=
  ∃ parts, Prints t parts ∧ parts.flatten = ts

theorem prints_to_of_atom {c : Syn .expr} {cs : List Tok} (h : AtomYield c cs) :
    PrintsTo c cs :=
  ⟨[cs], h, by simp only [List.flatten_cons, List.flatten_nil, List.append_nil]⟩

theorem ident_prints_to (x : String) : PrintsTo (.ident x) [.ident x] :=
  prints_to_of_atom (ident_atom_yield x)

theorem simple_ident_prints_to (x : String) :
    PrintsTo (Syn.exprStmt (.ident x)) [.ident x] :=
  ⟨[[.ident x]], fun _ => rfl, rfl⟩

theorem empty_args_prints_to :
    PrintsTo (Syn.positional .nil) [.punct .lparen, .punct .rparen] :=
  ⟨[[.punct .lparen, .punct .rparen]], fun _ => rfl, rfl⟩

theorem none_prints_to {c : Cat} : PrintsTo (Syn.none (c := c)) [] := ⟨[], fun _ => rfl, rfl⟩

theorem nil_prints {c : Cat} : Prints (Syn.nil (c := c)) [] := fun _ => rfl

theorem bool_param_prints_to (x : Option String) :
    PrintsTo (Syn.param (.elem .bool) .none x) ([.elem .bool] ++ optToks idt x) := by
  refine ⟨[[.elem .bool] ++ optToks idt x], ?_, by
    simp only [List.flatten_cons, List.flatten_nil, List.append_nil]⟩
  intro L
  cases x <;> rfl

local macro "prints_simp" "[" hs:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic|
  simp only [Syn.yield, bind, StateT.bind, pure, StateT.pure, Option.bind, tk, pu, idt, parens,
    braces, evmToks, List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append,
    List.nil_append, List.append_assoc, $hs,*])

mutual
inductive AtomStmtP : {k : SCtx} → Syn (.stmt k) → List Tok → Prop where
  | block {k : SCtx} {xs : Syn (.list (.item k))} {parts : List (List Tok)} :
      AtomItemsP xs parts → AtomStmtP (.blockStmt (.block xs)) (braces parts.flatten)
  | returnNone {k : SCtx} : AtomStmtP (k := k) (.returnStmt .none) [.kw .return_, .punct .semi]
  | returnSome {k : SCtx} {e : Syn .expr} {es : List Tok} :
      PrintsTo e es →
      AtomStmtP (k := k) (.returnStmt (.some e)) ([.kw .return_] ++ es ++ [.punct .semi])
  | breakStmt {u : Bool} : AtomStmtP (k := ⟨true, u⟩) .breakStmt [.kw .break_, .punct .semi]
  | continueStmt {u : Bool} :
      AtomStmtP (k := ⟨true, u⟩) .continueStmt [.kw .continue_, .punct .semi]
  | ifNone {k : SCtx} {c : Syn .expr} {cs : List Tok} {x : Syn (.stmt k)} {ts : List Tok} :
      PrintsTo c cs → AtomStmtP x ts →
      AtomStmtP (.ifStmt c x .none) ([.kw .if_, .punct .lparen] ++ cs ++ [.punct .rparen] ++ ts)
  | ifSome {k : SCtx} {c : Syn .expr} {cs : List Tok} {t e : Syn (.stmt k)} {ts es : List Tok} :
      PrintsTo c cs → AtomStmtP t ts → AtomStmtP e es →
      AtomStmtP (.ifStmt c t (.some e))
        ([.kw .if_, .punct .lparen] ++ cs ++ [.punct .rparen] ++ ts ++ [.kw .else_] ++ es)
  | whileLoop {l u : Bool} {c : Syn .expr} {cs : List Tok} {x : Syn (.stmt ⟨true, u⟩)}
      {ts : List Tok} :
      PrintsTo c cs → AtomStmtP x ts →
      AtomStmtP (Syn.whileStmt (l := l) c x)
        ([.kw .while_, .punct .lparen] ++ cs ++ [.punct .rparen] ++ ts)
  | forLoop {l u : Bool} {x : Syn (.stmt ⟨true, u⟩)} {ts : List Tok} :
      AtomStmtP x ts → AtomStmtP (Syn.forStmt (l := l) .none .none .none x)
        ([.kw .for_, .punct .lparen, .punct .semi, .punct .semi, .punct .rparen] ++ ts)
  | doLoop {l u : Bool} {c : Syn .expr} {cs : List Tok} {x : Syn (.stmt ⟨true, u⟩)}
      {ts : List Tok} :
      PrintsTo c cs → AtomStmtP x ts →
      AtomStmtP (Syn.doWhile (l := l) x c)
        ([.kw .do_] ++ ts ++ [.kw .while_, .punct .lparen] ++ cs ++ [.punct .rparen, .punct .semi])
  | forAtom {l u : Bool} {c v : Syn (.opt .expr)} {cs vs : List Tok}
      {x : Syn (.stmt ⟨true, u⟩)} {ts : List Tok} :
      PrintsTo c cs → PrintsTo v vs → AtomStmtP x ts →
      AtomStmtP (Syn.forStmt (l := l) .none c v x)
        ([.kw .for_, .punct .lparen, .punct .semi] ++ cs ++ [.punct .semi] ++ vs ++
          [.punct .rparen] ++ ts)
  | simpleS {k : SCtx} {x : Syn .simple} {ss : List Tok} :
      PrintsTo x ss → AtomStmtP (k := k) (.simpleStmt x) (ss ++ [.punct .semi])
  | forInit {l u : Bool} {x : Syn .simple} {ss : List Tok}
      {c v : Syn (.opt .expr)} {cs vs : List Tok} {b : Syn (.stmt ⟨true, u⟩)} {ts : List Tok} :
      PrintsTo x ss → PrintsTo c cs → PrintsTo v vs → AtomStmtP b ts →
      AtomStmtP (Syn.forStmt (l := l) (.some x) c v b)
        ([.kw .for_, .punct .lparen] ++ ss ++ [.punct .semi] ++ cs ++ [.punct .semi] ++ vs ++
          [.punct .rparen] ++ ts)
  | emitS {k : SCtx} {e : Syn .expr} {ps : List Tok} {args : Syn .callArgs} {as : List Tok} :
      PrintsTo e ps → PrintsTo args as →
      AtomStmtP (k := k) (.emit e args) ([.kw .emit] ++ ps ++ as ++ [.punct .semi])
  | revertS {k : SCtx} {e : Syn .expr} {y : String} {ps : List Tok} {args : Syn .callArgs}
      {as : List Tok} :
      PrintsTo e (.ident y :: ps) → PrintsTo args as →
      AtomStmtP (k := k) (.revert e args)
        ([.ident "revert"] ++ (.ident y :: ps) ++ as ++ [.punct .semi])
  | revertExpr {k : SCtx} {x : Syn .simple} {ss : List Tok} :
      PrintsTo x (.ident "revert" :: ss) →
      AtomStmtP (k := k) (.simpleStmt x) (.ident "revert" :: ss ++ [.punct .semi])
  | asm {k : SCtx} {evm : Bool} {flags : List String} {fts : List Tok}
      {body : Syn (.list .yulStmt)} {bs : List Tok} :
      fts = (if flags.isEmpty then [] else parens (commaSep (flags.map fun f => [.str (ascii f)]))) →
      PrintsTo body bs →
      AtomStmtP (k := k) (.assembly evm flags body)
        ([.kw .assembly] ++ evmToks evm ++ fts ++ braces bs)
  | tryS {k : SCtx} {e : Syn .expr} {es : List Tok}
      {xs : Syn (.list (.item k))} {parts : List (List Tok)}
      {c : Syn (.catchClause k)} {cts : List Tok}
      {cs : Syn (.list (.catchClause k))} {cparts : List (List Tok)} :
      PrintsTo e es → AtomItemsP xs parts → AtomCatchP c cts → AtomCatchesP cs cparts →
      AtomStmtP (.tryStmt e .nil (.block xs) c cs)
        ([.kw .try_] ++ es ++ braces parts.flatten ++ cts ++ cparts.flatten)
  | tryRets {k : SCtx} {e : Syn .expr} {es : List Tok}
      {rets : Syn (.list .param)} {rps : List (List Tok)} {rs : List Tok}
      {xs : Syn (.list (.item k))} {parts : List (List Tok)}
      {c : Syn (.catchClause k)} {cts : List Tok}
      {cs : Syn (.list (.catchClause k))} {cparts : List (List Tok)} :
      PrintsTo e es → Prints rets rps → rps ≠ [] →
      .kw .returns :: rs = tk .returns ++ parens (commaSep rps) →
      AtomItemsP xs parts → AtomCatchP c cts → AtomCatchesP cs cparts →
      AtomStmtP (.tryStmt e rets (.block xs) c cs)
        ([.kw .try_] ++ es ++ (.kw .returns :: rs) ++ braces parts.flatten ++ cts ++
          cparts.flatten)

inductive AtomItemsP : {k : SCtx} → Syn (.list (.item k)) → List (List Tok) → Prop where
  | nil {k : SCtx} : AtomItemsP (Syn.nil (c := .item k)) []
  | stmtCons {k : SCtx} {x : Syn (.stmt k)} {xs : Syn (.list (.item k))}
      {ts : List Tok} {parts : List (List Tok)} :
      AtomStmtP x ts → AtomItemsP xs parts → AtomItemsP (.cons (.stmtItem x) xs) (ts :: parts)
  | uncheckedCons {l : Bool} {ys : Syn (.list (.item ⟨l, true⟩))}
      {xs : Syn (.list (.item ⟨l, false⟩))} {qs parts : List (List Tok)} :
      AtomItemsP ys qs → AtomItemsP xs parts →
      AtomItemsP (.cons (.uncheckedItem (.block ys)) xs)
        ((.kw .unchecked :: braces qs.flatten) :: parts)

inductive AtomCatchP : {k : SCtx} → Syn (.catchClause k) → List Tok → Prop where
  | plain {k : SCtx} {xs : Syn (.list (.item k))} {parts : List (List Tok)} :
      AtomItemsP xs parts →
      AtomCatchP (.catchPlain (.block xs)) ([.kw .catch_] ++ braces parts.flatten)
  | sig {k : SCtx} {name : Option String} {p : Syn .param} {pt : List Tok}
      {ps : Syn (.list .param)} {pss : List (List Tok)} {pts : List Tok}
      {xs : Syn (.list (.item k))} {parts : List (List Tok)} :
      PrintsTo p pt → Prints ps pss → pts = parens (commaSep (pt :: pss)) → AtomItemsP xs parts →
      AtomCatchP (.catchSig name p ps (.block xs))
        ([.kw .catch_] ++ optToks idt name ++ pts ++ braces parts.flatten)

inductive AtomCatchesP : {k : SCtx} → Syn (.list (.catchClause k)) → List (List Tok) → Prop where
  | nil {k : SCtx} : AtomCatchesP (Syn.nil (c := .catchClause k)) []
  | cons {k : SCtx} {c : Syn (.catchClause k)} {cs : Syn (.list (.catchClause k))}
      {ts : List Tok} {parts : List (List Tok)} :
      AtomCatchP c ts → AtomCatchesP cs parts → AtomCatchesP (.cons c cs) (ts :: parts)
end

mutual
theorem atom_stmt_prints : {k : SCtx} → {x : Syn (.stmt k)} → {ts : List Tok} →
    AtomStmtP x ts → Prints x [ts]
  | _, _, _, .block h => by
    have hi := atom_items_prints h
    intro L
    prints_simp [hi L]
  | _, _, _, .returnNone => fun _ => rfl
  | _, _, _, .returnSome ⟨ps, hp, he⟩ => by
    subst he
    intro L
    prints_simp [hp L]
  | _, _, _, .breakStmt => fun _ => rfl
  | _, _, _, .continueStmt => fun _ => rfl
  | _, _, _, .ifNone ⟨ps, hp, hc⟩ h => by
    subst hc
    have hx := atom_stmt_prints h
    intro L
    prints_simp [hp L, hx L]
  | _, _, _, .ifSome ⟨ps, hp, hc⟩ ht he => by
    subst hc
    have hx := atom_stmt_prints ht
    have hy := atom_stmt_prints he
    intro L
    prints_simp [hp L, hx L, hy L]
  | _, _, _, .whileLoop ⟨ps, hp, hc⟩ h => by
    subst hc
    have hx := atom_stmt_prints h
    intro L
    prints_simp [hp L, hx L]
  | _, _, _, .forLoop h => by
    have hx := atom_stmt_prints h
    intro L
    prints_simp [hx L]
  | _, _, _, .doLoop ⟨ps, hp, hc⟩ h => by
    subst hc
    have hx := atom_stmt_prints h
    intro L
    prints_simp [hp L, hx L]
  | _, _, _, .forAtom ⟨ps, hp, hc⟩ ⟨qs, hq, hv⟩ h => by
    subst hc hv
    have hx := atom_stmt_prints h
    intro L
    prints_simp [hp L, hq L, hx L]
  | _, _, _, .simpleS ⟨ps, hp, hs⟩ => by
    subst hs
    intro L
    prints_simp [hp L]
  | _, _, _, .forInit ⟨ps, hp, hs⟩ ⟨qs, hq, hc⟩ ⟨rs, hr, hv⟩ h => by
    subst hs hc hv
    have hx := atom_stmt_prints h
    intro L
    prints_simp [hp L, hq L, hr L, hx L]
  | _, _, _, .emitS ⟨ps, hp, he⟩ ⟨qs, hq, ha⟩ => by
    intro L
    prints_simp [hp L, hq L, he, ha]
  | _, _, _, .revertS ⟨ps, hp, he⟩ ⟨qs, hq, ha⟩ => by
    intro L
    prints_simp [hp L, hq L, he, ha]
  | _, _, _, .revertExpr ⟨ps, hp, hs⟩ => by
    intro L
    prints_simp [hp L, hs]
  | _, _, _, .asm (evm := evm) hf ⟨ps, hp, hb⟩ => by
    subst hf hb
    intro L
    cases evm <;> prints_simp [hp L] <;> rfl
  | _, _, _, .tryS ⟨ps, hp, he⟩ hi hc hcs => by
    subst he
    have h1 := atom_items_prints hi
    have h2 := atom_catch_prints hc
    have h3 := atom_catches_prints hcs
    intro L
    prints_simp [hp L, h1 L, h2 L, h3 L]
    rfl
  | _, _, _, .tryRets (rps := rps) ⟨ps, hp, he⟩ hr hne hrs hi hc hcs => by
    subst he
    have h1 := atom_items_prints hi
    have h2 := atom_catch_prints hc
    have h3 := atom_catches_prints hcs
    intro L
    have hemp : rps.isEmpty = false := by
      cases rps with
      | nil => exact absurd rfl hne
      | cons _ _ => rfl
    simp only [tk, parens, pu, List.cons_append, List.nil_append, List.cons.injEq,
      true_and] at hrs
    prints_simp [hp L, hr L, h1 L, h2 L, h3 L, hemp, hrs, Bool.false_eq_true, ite_false]

theorem atom_items_prints : {k : SCtx} → {xs : Syn (.list (.item k))} →
    {parts : List (List Tok)} → AtomItemsP xs parts → Prints xs parts
  | _, _, _, .nil => fun _ => rfl
  | _, _, _, .stmtCons hx ht => by
    have h1 := atom_stmt_prints hx
    have h2 := atom_items_prints ht
    intro L
    prints_simp [h1 L, h2 L]
  | _, _, _, .uncheckedCons hy ht => by
    have h1 := atom_items_prints hy
    have h2 := atom_items_prints ht
    intro L
    prints_simp [h1 L, h2 L]

theorem atom_catch_prints : {k : SCtx} → {c : Syn (.catchClause k)} → {ts : List Tok} →
    AtomCatchP c ts → Prints c [ts]
  | _, _, _, .plain h => by
    have h1 := atom_items_prints h
    intro L
    prints_simp [h1 L]
  | _, _, _, .sig ⟨ps, hp, hpt⟩ hps hpts h => by
    subst hpt hpts
    have h1 := atom_items_prints h
    intro L
    prints_simp [hp L, hps L, h1 L]

theorem atom_catches_prints : {k : SCtx} → {cs : Syn (.list (.catchClause k))} →
    {parts : List (List Tok)} → AtomCatchesP cs parts → Prints cs parts
  | _, _, _, .nil => fun _ => rfl
  | _, _, _, .cons hc ht => by
    have h1 := atom_catch_prints hc
    have h2 := atom_catches_prints ht
    intro L
    prints_simp [h1 L, h2 L]
end

/-- A statement's derivations are exactly its printed tokens. -/
theorem atom_stmt_derives_iff {k : SCtx} {x : Syn (.stmt k)} {ts : List Tok}
    (h : AtomStmtP x ts) (words : List Tok) : x.Derives words ↔ words = ts := by
  have hp := atom_stmt_prints h
  constructor
  · intro ⟨L, hy⟩
    unfold Syn.toks at hy
    rw [hp L] at hy
    cases L with
    | nil =>
      simp only [List.flatten_cons, List.flatten_nil, List.append_nil, Option.some.injEq] at hy
      exact hy.symm
    | cons choice rest => cases hy
  · intro he
    subst words
    refine ⟨[], ?_⟩
    unfold Syn.toks
    rw [hp []]
    simp only [List.flatten_cons, List.flatten_nil, List.append_nil]

/-- Yield uniqueness for the mutual fragment: two trees with parse and print
witnesses deriving the same words are equal. -/
theorem atom_stmt_yield_unique {k : SCtx} {x y : Syn (.stmt k)}
    {ts us words : List Tok} {d e : Nat}
    (hx : AtomStmt x ts d) (px : AtomStmtP x ts)
    (hy : AtomStmt y us e) (py : AtomStmtP y us)
    (dx : x.Derives words) (dy : y.Derives words) : x = y :=
  atom_stmt_token_unique hx hy
    (((atom_stmt_derives_iff px words).mp dx).symm.trans
      ((atom_stmt_derives_iff py words).mp dy))

#print axioms prints_to_of_atom
#print axioms ident_prints_to
#print axioms simple_ident_prints_to
#print axioms empty_args_prints_to
#print axioms none_prints_to
#print axioms nil_prints
#print axioms bool_param_prints_to
#print axioms atom_stmt_prints
#print axioms atom_items_prints
#print axioms atom_catch_prints
#print axioms atom_catches_prints
#print axioms atom_stmt_derives_iff
#print axioms atom_stmt_yield_unique
end Solidity.Frontend.StatementGrammarH28
