import Solidity.Frontend.StatementGrammarH28.BoundaryHeadPr

/-! All seven immutable atom categories have an inhabited non-continuation
token head. Other categories receive no head claim. -/
namespace Solidity.Frontend.StatementGrammarH28
open Solidity.Source Solidity.Frontend.Checked

def BoundaryParts (parts : List (List Tok)) : Prop := BoundaryStart parts.flatten

def BoundaryHeadInvariant : Cat → List (List Tok) → Prop
  | .expr | .typeName | .param | .varDecl | .simple | .callArgs | .namedArg => BoundaryParts
  | _ => fun _ => True

theorem syntax_boundary_head_invariant {c : Cat} (s : Syn c) : PrEnsures s.yield (BoundaryHeadInvariant c) := by
  induction s with
  | positional es ihes =>
    rw [Syn.yield]
    apply ensures_bind (P := BoundaryParts)
    intro a
    apply ensures_pure _ BoundaryParts
    simp only [BoundaryParts, List.flatten_cons, List.flatten_nil, List.append_nil]
    exact ⟨_, _, rfl, rfl⟩
  | named args ihargs =>
    rw [Syn.yield]
    apply ensures_bind (P := BoundaryParts)
    intro a
    apply ensures_pure _ BoundaryParts
    simp only [BoundaryParts, List.flatten_cons, List.flatten_nil, List.append_nil]
    exact ⟨_, _, rfl, rfl⟩
  | namedArg name e ihe =>
    rw [Syn.yield]
    apply ensures_bind (P := BoundaryParts)
    intro a
    apply ensures_pure _ BoundaryParts
    simp only [BoundaryParts, List.flatten_cons, List.flatten_nil, List.append_nil]
    exact ⟨_, _, rfl, rfl⟩
  | param t loc name iht =>
    rw [Syn.yield]
    apply ensures_bind_checked _ _ BoundaryParts BoundaryParts iht
    intro a ha
    apply ensures_pure _ BoundaryParts
    simp only [BoundaryParts, List.flatten_cons, List.flatten_nil, List.append_nil]
    repeat first | exact ha | apply boundary_start_append
  | elem e =>
    rw [Syn.yield]
    apply ensures_pure _ BoundaryParts
    simp only [BoundaryParts, List.flatten_cons, List.flatten_nil, List.append_nil]
    exact elem_boundary_start e
  | fnType ps vis mu rets ihps ihrets =>
    rw [Syn.yield]
    apply ensures_bind (P := BoundaryParts)
    intro order
    apply ensures_bind (P := BoundaryParts)
    intro p
    apply ensures_bind (P := BoundaryParts)
    intro attrs
    apply ensures_bind (P := BoundaryParts)
    intro r
    apply ensures_pure _ BoundaryParts
    simp only [BoundaryParts, List.flatten_cons, List.flatten_nil, List.append_nil]
    exact ⟨_, _, rfl, rfl⟩
  | mapping key kn v vn ihv =>
    cases key with
    | elem e _he =>
      rw [Syn.yield]
      apply ensures_bind (P := BoundaryParts)
      intro a
      apply ensures_pure _ BoundaryParts
      simp only [BoundaryParts, List.flatten_cons, List.flatten_nil, List.append_nil]
      exact ⟨_, _, rfl, rfl⟩
    | path p =>
      rw [Syn.yield]
      apply ensures_bind (P := BoundaryParts)
      intro a
      apply ensures_pure _ BoundaryParts
      simp only [BoundaryParts, List.flatten_cons, List.flatten_nil, List.append_nil]
      exact ⟨_, _, rfl, rfl⟩
  | userType p =>
    rw [Syn.yield]
    apply ensures_pure _ BoundaryParts
    simp only [BoundaryParts, List.flatten_cons, List.flatten_nil, List.append_nil]
    exact path_boundary_start p
  | array t len iht ihlen =>
    rw [Syn.yield]
    apply ensures_bind_checked _ _ BoundaryParts BoundaryParts iht
    intro a ha
    apply ensures_bind (P := BoundaryParts)
    intro b
    apply ensures_pure _ BoundaryParts
    simp only [BoundaryParts, List.flatten_cons, List.flatten_nil, List.append_nil]
    repeat first | exact ha | apply boundary_start_append
  | varDecl t loc name iht =>
    rw [Syn.yield]
    apply ensures_bind_checked _ _ BoundaryParts BoundaryParts iht
    intro a ha
    apply ensures_pure _ BoundaryParts
    simp only [BoundaryParts, List.flatten_cons, List.flatten_nil, List.append_nil]
    repeat first | exact ha | apply boundary_start_append
  | index e i ihe ihi =>
    rw [Syn.yield]
    apply ensures_bind_checked _ _ BoundaryParts BoundaryParts ihe
    intro a ha
    apply ensures_bind (P := BoundaryParts)
    intro b
    apply ensures_pure _ BoundaryParts
    simp only [BoundaryParts, List.flatten_cons, List.flatten_nil, List.append_nil]
    repeat first | exact ha | apply boundary_start_append
  | slice e i j ihe ihi ihj =>
    rw [Syn.yield]
    apply ensures_bind_checked _ _ BoundaryParts BoundaryParts ihe
    intro a ha
    apply ensures_bind (P := BoundaryParts)
    intro b
    apply ensures_bind (P := BoundaryParts)
    intro c
    apply ensures_pure _ BoundaryParts
    simp only [BoundaryParts, List.flatten_cons, List.flatten_nil, List.append_nil]
    repeat first | exact ha | apply boundary_start_append
  | member e name ihe =>
    rw [Syn.yield]
    apply ensures_bind_checked _ _ BoundaryParts BoundaryParts ihe
    intro a ha
    apply ensures_pure _ BoundaryParts
    simp only [BoundaryParts, List.flatten_cons, List.flatten_nil, List.append_nil]
    repeat first | exact ha | apply boundary_start_append
  | callOptions e arg args ihe iharg ihargs =>
    rw [Syn.yield]
    apply ensures_bind_checked _ _ BoundaryParts BoundaryParts ihe
    intro a ha
    apply ensures_bind (P := BoundaryParts)
    intro b
    apply ensures_bind (P := BoundaryParts)
    intro c
    apply ensures_pure _ BoundaryParts
    simp only [BoundaryParts, List.flatten_cons, List.flatten_nil, List.append_nil]
    repeat first | exact ha | apply boundary_start_append
  | call e args ihe ihargs =>
    rw [Syn.yield]
    apply ensures_bind_checked _ _ BoundaryParts BoundaryParts ihe
    intro a ha
    apply ensures_bind (P := BoundaryParts)
    intro b
    apply ensures_pure _ BoundaryParts
    simp only [BoundaryParts, List.flatten_cons, List.flatten_nil, List.append_nil]
    repeat first | exact ha | apply boundary_start_append
  | payableConv args ihargs =>
    rw [Syn.yield]
    apply ensures_bind (P := BoundaryParts)
    intro a
    apply ensures_pure _ BoundaryParts
    simp only [BoundaryParts, List.flatten_cons, List.flatten_nil, List.append_nil]
    exact ⟨_, _, rfl, rfl⟩
  | metaType t iht =>
    rw [Syn.yield]
    apply ensures_bind (P := BoundaryParts)
    intro a
    apply ensures_pure _ BoundaryParts
    simp only [BoundaryParts, List.flatten_cons, List.flatten_nil, List.append_nil]
    exact ⟨_, _, rfl, rfl⟩
  | unaryPrefix op e ihe =>
    rw [Syn.yield]
    apply ensures_bind (P := BoundaryParts)
    intro a
    apply ensures_pure _ BoundaryParts
    simp only [BoundaryParts, List.flatten_cons, List.flatten_nil, List.append_nil]
    apply boundary_start_append
    exact prefix_boundary_start op
  | unarySuffix op e ihe =>
    rw [Syn.yield]
    apply ensures_bind_checked _ _ BoundaryParts BoundaryParts ihe
    intro a ha
    apply ensures_pure _ BoundaryParts
    simp only [BoundaryParts, List.flatten_cons, List.flatten_nil, List.append_nil]
    repeat first | exact ha | apply boundary_start_append
  | exp left right ihleft ihright =>
    rw [Syn.yield]
    apply ensures_bind_checked _ _ BoundaryParts BoundaryParts ihleft
    intro a ha
    apply ensures_bind (P := BoundaryParts)
    intro b
    apply ensures_pure _ BoundaryParts
    simp only [BoundaryParts, List.flatten_cons, List.flatten_nil, List.append_nil]
    repeat first | exact ha | apply boundary_start_append
  | mulDivMod op left right ihleft ihright =>
    rw [Syn.yield]
    apply ensures_bind_checked _ _ BoundaryParts BoundaryParts ihleft
    intro a ha
    apply ensures_bind (P := BoundaryParts)
    intro b
    apply ensures_pure _ BoundaryParts
    simp only [BoundaryParts, List.flatten_cons, List.flatten_nil, List.append_nil]
    repeat first | exact ha | apply boundary_start_append
  | addSub op left right ihleft ihright =>
    rw [Syn.yield]
    apply ensures_bind_checked _ _ BoundaryParts BoundaryParts ihleft
    intro a ha
    apply ensures_bind (P := BoundaryParts)
    intro b
    apply ensures_pure _ BoundaryParts
    simp only [BoundaryParts, List.flatten_cons, List.flatten_nil, List.append_nil]
    repeat first | exact ha | apply boundary_start_append
  | shift op left right ihleft ihright =>
    rw [Syn.yield]
    apply ensures_bind_checked _ _ BoundaryParts BoundaryParts ihleft
    intro a ha
    apply ensures_bind (P := BoundaryParts)
    intro b
    apply ensures_pure _ BoundaryParts
    simp only [BoundaryParts, List.flatten_cons, List.flatten_nil, List.append_nil]
    repeat first | exact ha | apply boundary_start_append
  | bitAnd left right ihleft ihright =>
    rw [Syn.yield]
    apply ensures_bind_checked _ _ BoundaryParts BoundaryParts ihleft
    intro a ha
    apply ensures_bind (P := BoundaryParts)
    intro b
    apply ensures_pure _ BoundaryParts
    simp only [BoundaryParts, List.flatten_cons, List.flatten_nil, List.append_nil]
    repeat first | exact ha | apply boundary_start_append
  | bitXor left right ihleft ihright =>
    rw [Syn.yield]
    apply ensures_bind_checked _ _ BoundaryParts BoundaryParts ihleft
    intro a ha
    apply ensures_bind (P := BoundaryParts)
    intro b
    apply ensures_pure _ BoundaryParts
    simp only [BoundaryParts, List.flatten_cons, List.flatten_nil, List.append_nil]
    repeat first | exact ha | apply boundary_start_append
  | bitOr left right ihleft ihright =>
    rw [Syn.yield]
    apply ensures_bind_checked _ _ BoundaryParts BoundaryParts ihleft
    intro a ha
    apply ensures_bind (P := BoundaryParts)
    intro b
    apply ensures_pure _ BoundaryParts
    simp only [BoundaryParts, List.flatten_cons, List.flatten_nil, List.append_nil]
    repeat first | exact ha | apply boundary_start_append
  | order op left right ihleft ihright =>
    rw [Syn.yield]
    apply ensures_bind_checked _ _ BoundaryParts BoundaryParts ihleft
    intro a ha
    apply ensures_bind (P := BoundaryParts)
    intro b
    apply ensures_pure _ BoundaryParts
    simp only [BoundaryParts, List.flatten_cons, List.flatten_nil, List.append_nil]
    repeat first | exact ha | apply boundary_start_append
  | equality op left right ihleft ihright =>
    rw [Syn.yield]
    apply ensures_bind_checked _ _ BoundaryParts BoundaryParts ihleft
    intro a ha
    apply ensures_bind (P := BoundaryParts)
    intro b
    apply ensures_pure _ BoundaryParts
    simp only [BoundaryParts, List.flatten_cons, List.flatten_nil, List.append_nil]
    repeat first | exact ha | apply boundary_start_append
  | and left right ihleft ihright =>
    rw [Syn.yield]
    apply ensures_bind_checked _ _ BoundaryParts BoundaryParts ihleft
    intro a ha
    apply ensures_bind (P := BoundaryParts)
    intro b
    apply ensures_pure _ BoundaryParts
    simp only [BoundaryParts, List.flatten_cons, List.flatten_nil, List.append_nil]
    repeat first | exact ha | apply boundary_start_append
  | or left right ihleft ihright =>
    rw [Syn.yield]
    apply ensures_bind_checked _ _ BoundaryParts BoundaryParts ihleft
    intro a ha
    apply ensures_bind (P := BoundaryParts)
    intro b
    apply ensures_pure _ BoundaryParts
    simp only [BoundaryParts, List.flatten_cons, List.flatten_nil, List.append_nil]
    repeat first | exact ha | apply boundary_start_append
  | assign op left right ihleft ihright =>
    rw [Syn.yield]
    apply ensures_bind_checked _ _ BoundaryParts BoundaryParts ihleft
    intro a ha
    apply ensures_bind (P := BoundaryParts)
    intro b
    apply ensures_pure _ BoundaryParts
    simp only [BoundaryParts, List.flatten_cons, List.flatten_nil, List.append_nil]
    repeat first | exact ha | apply boundary_start_append
  | cond c yes no ihc ihyes ihno =>
    rw [Syn.yield]
    apply ensures_bind_checked _ _ BoundaryParts BoundaryParts ihc
    intro a ha
    apply ensures_bind (P := BoundaryParts)
    intro b
    apply ensures_bind (P := BoundaryParts)
    intro c
    apply ensures_pure _ BoundaryParts
    simp only [BoundaryParts, List.flatten_cons, List.flatten_nil, List.append_nil]
    repeat first | exact ha | apply boundary_start_append
  | new t iht =>
    rw [Syn.yield]
    apply ensures_bind (P := BoundaryParts)
    intro a
    apply ensures_pure _ BoundaryParts
    simp only [BoundaryParts, List.flatten_cons, List.flatten_nil, List.append_nil]
    exact ⟨_, _, rfl, rfl⟩
  | tuple first rest ihfirst ihrest =>
    rw [Syn.yield]
    apply ensures_bind (P := BoundaryParts)
    intro a
    apply ensures_bind (P := BoundaryParts)
    intro b
    apply ensures_pure _ BoundaryParts
    simp only [BoundaryParts, List.flatten_cons, List.flatten_nil, List.append_nil]
    exact ⟨_, _, rfl, rfl⟩
  | inlineArray first rest ihfirst ihrest =>
    rw [Syn.yield]
    apply ensures_bind (P := BoundaryParts)
    intro a
    apply ensures_bind (P := BoundaryParts)
    intro b
    apply ensures_pure _ BoundaryParts
    simp only [BoundaryParts, List.flatten_cons, List.flatten_nil, List.append_nil]
    exact ⟨_, _, rfl, rfl⟩
  | ident name =>
    rw [Syn.yield]
    apply ensures_pure _ BoundaryParts
    simp only [BoundaryParts, List.flatten_cons, List.flatten_nil, List.append_nil]
    exact ⟨_, _, rfl, rfl⟩
  | lit lit =>
    rw [Syn.yield]
    apply ensures_bind_checked _ _ BoundaryStart BoundaryParts (litP_boundary_start lit)
    intro ts ht
    apply ensures_pure _ BoundaryParts
    simpa only [BoundaryParts, List.flatten_cons, List.flatten_nil, List.append_nil] using ht
  | litUnit n u =>
    rw [Syn.yield]
    apply ensures_pure _ BoundaryParts
    simp only [BoundaryParts, List.flatten_cons, List.flatten_nil, List.append_nil]
    exact ⟨_, _, rfl, rfl⟩
  | elemType e he =>
    rw [Syn.yield]
    apply ensures_pure _ BoundaryParts
    simp only [BoundaryParts, List.flatten_cons, List.flatten_nil, List.append_nil]
    exact ⟨_, _, rfl, rfl⟩
  | declVar decl init ihdecl ihinit =>
    rw [Syn.yield]
    apply ensures_bind_checked _ _ BoundaryParts BoundaryParts ihdecl
    intro a ha
    apply ensures_bind (P := BoundaryParts)
    intro b
    apply ensures_pure _ BoundaryParts
    simp only [BoundaryParts, List.flatten_cons, List.flatten_nil, List.append_nil]
    repeat first | exact ha | apply boundary_start_append
  | declTuple holes decl decls e ihdecl ihdecls ihe =>
    rw [Syn.yield]
    apply ensures_bind (P := BoundaryParts)
    intro a
    apply ensures_bind (P := BoundaryParts)
    intro b
    apply ensures_bind (P := BoundaryParts)
    intro c
    apply ensures_pure _ BoundaryParts
    simp only [BoundaryParts, List.flatten_cons, List.flatten_nil, List.append_nil]
    exact ⟨_, _, rfl, rfl⟩
  | exprStmt e ihe => exact ihe
  | _ => intro L parts M _h; trivial

theorem expression_yield_boundary_start (e : Syn .expr) : PrEnsures e.yield BoundaryParts :=
  syntax_boundary_head_invariant e

theorem type_yield_boundary_start (t : Syn .typeName) : PrEnsures t.yield BoundaryParts :=
  syntax_boundary_head_invariant t

theorem simple_yield_boundary_start (s : Syn .simple) : PrEnsures s.yield BoundaryParts :=
  syntax_boundary_head_invariant s

end Solidity.Frontend.StatementGrammarH28
