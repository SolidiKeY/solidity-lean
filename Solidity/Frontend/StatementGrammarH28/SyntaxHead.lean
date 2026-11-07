import Solidity.Frontend.StatementGrammarH28.HeadPr

/-! H31 arbitrary expression/type/simple first-token facts. These do not
establish expression uniqueness or contextual-revert discrimination. -/
namespace Solidity.Frontend.StatementGrammarH28
open Solidity.Source Solidity.Frontend.Checked

def SafeParts (parts : List (List Tok)) : Prop := SafeStart parts.flatten

def HeadInvariant : Cat → List (List Tok) → Prop
  | .expr | .typeName | .param | .varDecl | .simple | .callArgs | .namedArg => SafeParts
  | _ => fun _ => True

theorem syntax_head_invariant {c : Cat} (s : Syn c) : PrEnsures s.yield (HeadInvariant c) := by
  induction s with
  | positional es ihes =>
    rw [Syn.yield]
    apply ensures_bind (P := SafeParts)
    intro a
    apply ensures_pure _ SafeParts
    simp only [SafeParts, List.flatten_cons, List.flatten_nil, List.append_nil]
    exact ⟨_, _, rfl, rfl⟩
  | named args ihargs =>
    rw [Syn.yield]
    apply ensures_bind (P := SafeParts)
    intro a
    apply ensures_pure _ SafeParts
    simp only [SafeParts, List.flatten_cons, List.flatten_nil, List.append_nil]
    exact ⟨_, _, rfl, rfl⟩
  | namedArg name e ihe =>
    rw [Syn.yield]
    apply ensures_bind (P := SafeParts)
    intro a
    apply ensures_pure _ SafeParts
    simp only [SafeParts, List.flatten_cons, List.flatten_nil, List.append_nil]
    exact ⟨_, _, rfl, rfl⟩
  | param t loc name iht =>
    rw [Syn.yield]
    apply ensures_bind_checked _ _ SafeParts SafeParts iht
    intro a ha
    apply ensures_pure _ SafeParts
    simp only [SafeParts, List.flatten_cons, List.flatten_nil, List.append_nil]
    repeat first | exact ha | apply safe_start_append
  | elem e =>
    rw [Syn.yield]
    apply ensures_pure _ SafeParts
    simp only [SafeParts, List.flatten_cons, List.flatten_nil, List.append_nil]
    exact elem_safe_start e
  | fnType ps vis mu rets ihps ihrets =>
    rw [Syn.yield]
    apply ensures_bind (P := SafeParts)
    intro order
    apply ensures_bind (P := SafeParts)
    intro p
    apply ensures_bind (P := SafeParts)
    intro attrs
    apply ensures_bind (P := SafeParts)
    intro r
    apply ensures_pure _ SafeParts
    simp only [SafeParts, List.flatten_cons, List.flatten_nil, List.append_nil]
    exact ⟨_, _, rfl, rfl⟩
  | mapping key kn v vn ihv =>
    cases key with
    | elem e _he =>
      rw [Syn.yield]
      apply ensures_bind (P := SafeParts)
      intro a
      apply ensures_pure _ SafeParts
      simp only [SafeParts, List.flatten_cons, List.flatten_nil, List.append_nil]
      exact ⟨_, _, rfl, rfl⟩
    | path p =>
      rw [Syn.yield]
      apply ensures_bind (P := SafeParts)
      intro a
      apply ensures_pure _ SafeParts
      simp only [SafeParts, List.flatten_cons, List.flatten_nil, List.append_nil]
      exact ⟨_, _, rfl, rfl⟩
  | userType p =>
    rw [Syn.yield]
    apply ensures_pure _ SafeParts
    simp only [SafeParts, List.flatten_cons, List.flatten_nil, List.append_nil]
    exact path_safe_start p
  | array t len iht ihlen =>
    rw [Syn.yield]
    apply ensures_bind_checked _ _ SafeParts SafeParts iht
    intro a ha
    apply ensures_bind (P := SafeParts)
    intro b
    apply ensures_pure _ SafeParts
    simp only [SafeParts, List.flatten_cons, List.flatten_nil, List.append_nil]
    repeat first | exact ha | apply safe_start_append
  | varDecl t loc name iht =>
    rw [Syn.yield]
    apply ensures_bind_checked _ _ SafeParts SafeParts iht
    intro a ha
    apply ensures_pure _ SafeParts
    simp only [SafeParts, List.flatten_cons, List.flatten_nil, List.append_nil]
    repeat first | exact ha | apply safe_start_append
  | index e i ihe ihi =>
    rw [Syn.yield]
    apply ensures_bind_checked _ _ SafeParts SafeParts ihe
    intro a ha
    apply ensures_bind (P := SafeParts)
    intro b
    apply ensures_pure _ SafeParts
    simp only [SafeParts, List.flatten_cons, List.flatten_nil, List.append_nil]
    repeat first | exact ha | apply safe_start_append
  | slice e i j ihe ihi ihj =>
    rw [Syn.yield]
    apply ensures_bind_checked _ _ SafeParts SafeParts ihe
    intro a ha
    apply ensures_bind (P := SafeParts)
    intro b
    apply ensures_bind (P := SafeParts)
    intro c
    apply ensures_pure _ SafeParts
    simp only [SafeParts, List.flatten_cons, List.flatten_nil, List.append_nil]
    repeat first | exact ha | apply safe_start_append
  | member e name ihe =>
    rw [Syn.yield]
    apply ensures_bind_checked _ _ SafeParts SafeParts ihe
    intro a ha
    apply ensures_pure _ SafeParts
    simp only [SafeParts, List.flatten_cons, List.flatten_nil, List.append_nil]
    repeat first | exact ha | apply safe_start_append
  | callOptions e arg args ihe iharg ihargs =>
    rw [Syn.yield]
    apply ensures_bind_checked _ _ SafeParts SafeParts ihe
    intro a ha
    apply ensures_bind (P := SafeParts)
    intro b
    apply ensures_bind (P := SafeParts)
    intro c
    apply ensures_pure _ SafeParts
    simp only [SafeParts, List.flatten_cons, List.flatten_nil, List.append_nil]
    repeat first | exact ha | apply safe_start_append
  | call e args ihe ihargs =>
    rw [Syn.yield]
    apply ensures_bind_checked _ _ SafeParts SafeParts ihe
    intro a ha
    apply ensures_bind (P := SafeParts)
    intro b
    apply ensures_pure _ SafeParts
    simp only [SafeParts, List.flatten_cons, List.flatten_nil, List.append_nil]
    repeat first | exact ha | apply safe_start_append
  | payableConv args ihargs =>
    rw [Syn.yield]
    apply ensures_bind (P := SafeParts)
    intro a
    apply ensures_pure _ SafeParts
    simp only [SafeParts, List.flatten_cons, List.flatten_nil, List.append_nil]
    exact ⟨_, _, rfl, rfl⟩
  | metaType t iht =>
    rw [Syn.yield]
    apply ensures_bind (P := SafeParts)
    intro a
    apply ensures_pure _ SafeParts
    simp only [SafeParts, List.flatten_cons, List.flatten_nil, List.append_nil]
    exact ⟨_, _, rfl, rfl⟩
  | unaryPrefix op e ihe =>
    rw [Syn.yield]
    apply ensures_bind (P := SafeParts)
    intro a
    apply ensures_pure _ SafeParts
    simp only [SafeParts, List.flatten_cons, List.flatten_nil, List.append_nil]
    apply safe_start_append
    exact prefix_safe_start op
  | unarySuffix op e ihe =>
    rw [Syn.yield]
    apply ensures_bind_checked _ _ SafeParts SafeParts ihe
    intro a ha
    apply ensures_pure _ SafeParts
    simp only [SafeParts, List.flatten_cons, List.flatten_nil, List.append_nil]
    repeat first | exact ha | apply safe_start_append
  | exp left right ihleft ihright =>
    rw [Syn.yield]
    apply ensures_bind_checked _ _ SafeParts SafeParts ihleft
    intro a ha
    apply ensures_bind (P := SafeParts)
    intro b
    apply ensures_pure _ SafeParts
    simp only [SafeParts, List.flatten_cons, List.flatten_nil, List.append_nil]
    repeat first | exact ha | apply safe_start_append
  | mulDivMod op left right ihleft ihright =>
    rw [Syn.yield]
    apply ensures_bind_checked _ _ SafeParts SafeParts ihleft
    intro a ha
    apply ensures_bind (P := SafeParts)
    intro b
    apply ensures_pure _ SafeParts
    simp only [SafeParts, List.flatten_cons, List.flatten_nil, List.append_nil]
    repeat first | exact ha | apply safe_start_append
  | addSub op left right ihleft ihright =>
    rw [Syn.yield]
    apply ensures_bind_checked _ _ SafeParts SafeParts ihleft
    intro a ha
    apply ensures_bind (P := SafeParts)
    intro b
    apply ensures_pure _ SafeParts
    simp only [SafeParts, List.flatten_cons, List.flatten_nil, List.append_nil]
    repeat first | exact ha | apply safe_start_append
  | shift op left right ihleft ihright =>
    rw [Syn.yield]
    apply ensures_bind_checked _ _ SafeParts SafeParts ihleft
    intro a ha
    apply ensures_bind (P := SafeParts)
    intro b
    apply ensures_pure _ SafeParts
    simp only [SafeParts, List.flatten_cons, List.flatten_nil, List.append_nil]
    repeat first | exact ha | apply safe_start_append
  | bitAnd left right ihleft ihright =>
    rw [Syn.yield]
    apply ensures_bind_checked _ _ SafeParts SafeParts ihleft
    intro a ha
    apply ensures_bind (P := SafeParts)
    intro b
    apply ensures_pure _ SafeParts
    simp only [SafeParts, List.flatten_cons, List.flatten_nil, List.append_nil]
    repeat first | exact ha | apply safe_start_append
  | bitXor left right ihleft ihright =>
    rw [Syn.yield]
    apply ensures_bind_checked _ _ SafeParts SafeParts ihleft
    intro a ha
    apply ensures_bind (P := SafeParts)
    intro b
    apply ensures_pure _ SafeParts
    simp only [SafeParts, List.flatten_cons, List.flatten_nil, List.append_nil]
    repeat first | exact ha | apply safe_start_append
  | bitOr left right ihleft ihright =>
    rw [Syn.yield]
    apply ensures_bind_checked _ _ SafeParts SafeParts ihleft
    intro a ha
    apply ensures_bind (P := SafeParts)
    intro b
    apply ensures_pure _ SafeParts
    simp only [SafeParts, List.flatten_cons, List.flatten_nil, List.append_nil]
    repeat first | exact ha | apply safe_start_append
  | order op left right ihleft ihright =>
    rw [Syn.yield]
    apply ensures_bind_checked _ _ SafeParts SafeParts ihleft
    intro a ha
    apply ensures_bind (P := SafeParts)
    intro b
    apply ensures_pure _ SafeParts
    simp only [SafeParts, List.flatten_cons, List.flatten_nil, List.append_nil]
    repeat first | exact ha | apply safe_start_append
  | equality op left right ihleft ihright =>
    rw [Syn.yield]
    apply ensures_bind_checked _ _ SafeParts SafeParts ihleft
    intro a ha
    apply ensures_bind (P := SafeParts)
    intro b
    apply ensures_pure _ SafeParts
    simp only [SafeParts, List.flatten_cons, List.flatten_nil, List.append_nil]
    repeat first | exact ha | apply safe_start_append
  | and left right ihleft ihright =>
    rw [Syn.yield]
    apply ensures_bind_checked _ _ SafeParts SafeParts ihleft
    intro a ha
    apply ensures_bind (P := SafeParts)
    intro b
    apply ensures_pure _ SafeParts
    simp only [SafeParts, List.flatten_cons, List.flatten_nil, List.append_nil]
    repeat first | exact ha | apply safe_start_append
  | or left right ihleft ihright =>
    rw [Syn.yield]
    apply ensures_bind_checked _ _ SafeParts SafeParts ihleft
    intro a ha
    apply ensures_bind (P := SafeParts)
    intro b
    apply ensures_pure _ SafeParts
    simp only [SafeParts, List.flatten_cons, List.flatten_nil, List.append_nil]
    repeat first | exact ha | apply safe_start_append
  | assign op left right ihleft ihright =>
    rw [Syn.yield]
    apply ensures_bind_checked _ _ SafeParts SafeParts ihleft
    intro a ha
    apply ensures_bind (P := SafeParts)
    intro b
    apply ensures_pure _ SafeParts
    simp only [SafeParts, List.flatten_cons, List.flatten_nil, List.append_nil]
    repeat first | exact ha | apply safe_start_append
  | cond c yes no ihc ihyes ihno =>
    rw [Syn.yield]
    apply ensures_bind_checked _ _ SafeParts SafeParts ihc
    intro a ha
    apply ensures_bind (P := SafeParts)
    intro b
    apply ensures_bind (P := SafeParts)
    intro c
    apply ensures_pure _ SafeParts
    simp only [SafeParts, List.flatten_cons, List.flatten_nil, List.append_nil]
    repeat first | exact ha | apply safe_start_append
  | new t iht =>
    rw [Syn.yield]
    apply ensures_bind (P := SafeParts)
    intro a
    apply ensures_pure _ SafeParts
    simp only [SafeParts, List.flatten_cons, List.flatten_nil, List.append_nil]
    exact ⟨_, _, rfl, rfl⟩
  | tuple first rest ihfirst ihrest =>
    rw [Syn.yield]
    apply ensures_bind (P := SafeParts)
    intro a
    apply ensures_bind (P := SafeParts)
    intro b
    apply ensures_pure _ SafeParts
    simp only [SafeParts, List.flatten_cons, List.flatten_nil, List.append_nil]
    exact ⟨_, _, rfl, rfl⟩
  | inlineArray first rest ihfirst ihrest =>
    rw [Syn.yield]
    apply ensures_bind (P := SafeParts)
    intro a
    apply ensures_bind (P := SafeParts)
    intro b
    apply ensures_pure _ SafeParts
    simp only [SafeParts, List.flatten_cons, List.flatten_nil, List.append_nil]
    exact ⟨_, _, rfl, rfl⟩
  | ident name =>
    rw [Syn.yield]
    apply ensures_pure _ SafeParts
    simp only [SafeParts, List.flatten_cons, List.flatten_nil, List.append_nil]
    exact ⟨_, _, rfl, rfl⟩
  | lit lit =>
    rw [Syn.yield]
    apply ensures_bind_checked _ _ SafeStart SafeParts (litP_safe_start lit)
    intro ts ht
    apply ensures_pure _ SafeParts
    simpa only [SafeParts, List.flatten_cons, List.flatten_nil, List.append_nil] using ht
  | litUnit n u =>
    rw [Syn.yield]
    apply ensures_pure _ SafeParts
    simp only [SafeParts, List.flatten_cons, List.flatten_nil, List.append_nil]
    exact ⟨_, _, rfl, rfl⟩
  | elemType e he =>
    rw [Syn.yield]
    apply ensures_pure _ SafeParts
    simp only [SafeParts, List.flatten_cons, List.flatten_nil, List.append_nil]
    exact ⟨_, _, rfl, rfl⟩
  | declVar decl init ihdecl ihinit =>
    rw [Syn.yield]
    apply ensures_bind_checked _ _ SafeParts SafeParts ihdecl
    intro a ha
    apply ensures_bind (P := SafeParts)
    intro b
    apply ensures_pure _ SafeParts
    simp only [SafeParts, List.flatten_cons, List.flatten_nil, List.append_nil]
    repeat first | exact ha | apply safe_start_append
  | declTuple holes decl decls e ihdecl ihdecls ihe =>
    rw [Syn.yield]
    apply ensures_bind (P := SafeParts)
    intro a
    apply ensures_bind (P := SafeParts)
    intro b
    apply ensures_bind (P := SafeParts)
    intro c
    apply ensures_pure _ SafeParts
    simp only [SafeParts, List.flatten_cons, List.flatten_nil, List.append_nil]
    exact ⟨_, _, rfl, rfl⟩
  | exprStmt e ihe => exact ihe
  | _ => intro L parts M _h; trivial

theorem expression_yield_safe_start (e : Syn .expr) : PrEnsures e.yield SafeParts :=
  syntax_head_invariant e

theorem type_yield_safe_start (t : Syn .typeName) : PrEnsures t.yield SafeParts :=
  syntax_head_invariant t

theorem simple_yield_safe_start (s : Syn .simple) : PrEnsures s.yield SafeParts :=
  syntax_head_invariant s

#print axioms syntax_head_invariant
#print axioms expression_yield_safe_start
#print axioms type_yield_safe_start
#print axioms simple_yield_safe_start
end Solidity.Frontend.StatementGrammarH28
