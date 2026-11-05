import Solidity.Frontend.QualifiedUnits.Relation

/-!
# Original owner-body layout

A container in a source declaration graph is followed by exactly its own
collected body. This theorem links the member interval to actual intrinsic
syntax, including malformed units with repeated container spellings.
-/
namespace Solidity.Frontend.QualifiedUnits
open Solidity.Source

/-- Declarations in the identified container's actual intrinsic body. -/
def bodyDeclsSyntax (kind : DeclKind) {c : Cat} (s : Syn c) : List Decl :=
  Syn.casesOn (motive := fun c (_ : Syn c) => List Decl) s
    («nil» := fun {_} => [])
    («cons» := fun {_} _ _ => [])
    («none» := fun {_} => [])
    («some» := fun {_} _ => [])
    («unit» := fun _ => [])
    («pragma» := fun _ => [])
    («importPath» := fun _ _ => [])
    («importSymbols» := fun _ _ _ => [])
    («importStar» := fun _ _ => [])
    («importAlias» := fun _ _ => [])
    («contract» := fun _ a1 _ _ a4 => if kind == .contract then a4.collect (some a1) else [])
    («interface» := fun a0 _ a2 => if kind == .interface then a2.collect (some a0) else [])
    («library» := fun a0 a1 => if kind == .library then a1.collect (some a0) else [])
    («topPart» := fun _ => [])
    («inherit» := fun _ _ => [])
    («constructor» := fun _ _ _ _ _ => [])
    («function» := fun {_} _ _ _ _ _ _ _ _ _ => [])
    («modifier» := fun _ _ _ _ _ => [])
    («fallback» := fun _ _ _ _ _ _ _ => [])
    («fbNoParams» := [])
    («fbParams» := fun _ _ _ => [])
    («receive» := fun _ _ _ _ _ _ => [])
    («struct» := fun {_} _ _ _ => [])
    («structMember» := fun _ _ => [])
    («enum» := fun {_} _ _ _ => [])
    («udvt» := fun {_} _ _ => [])
    («stateVar» := fun _ _ _ _ _ _ _ => [])
    («constant» := fun _ _ _ => [])
    («event» := fun {_} _ _ _ => [])
    («eventParam» := fun _ _ _ => [])
    («error» := fun {_} _ _ => [])
    («errorParam» := fun _ _ => [])
    («usingPart» := fun {_} _ => [])
    («usingPath» := fun _ _ _ => [])
    («usingAliases» := fun _ _ _ _ => [])
    («usingAlias» := fun _ _ => [])
    («positional» := fun _ => [])
    («named» := fun _ => [])
    («namedArg» := fun _ _ => [])
    («modInv» := fun _ _ => [])
    («param» := fun _ _ _ => [])
    («elem» := fun _ => [])
    («fnType» := fun _ _ _ _ => [])
    («mapping» := fun _ _ _ _ => [])
    («userType» := fun _ => [])
    («array» := fun _ _ => [])
    («varDecl» := fun _ _ _ => [])
    («index» := fun _ _ => [])
    («slice» := fun _ _ _ => [])
    («member» := fun _ _ => [])
    («callOptions» := fun _ _ _ => [])
    («call» := fun _ _ => [])
    («payableConv» := fun _ => [])
    («metaType» := fun _ => [])
    («unaryPrefix» := fun _ _ => [])
    («unarySuffix» := fun _ _ => [])
    («exp» := fun _ _ => [])
    («mulDivMod» := fun _ _ _ => [])
    («addSub» := fun _ _ _ => [])
    («shift» := fun _ _ _ => [])
    («bitAnd» := fun _ _ => [])
    («bitXor» := fun _ _ => [])
    («bitOr» := fun _ _ => [])
    («order» := fun _ _ _ => [])
    («equality» := fun _ _ _ => [])
    («and» := fun _ _ => [])
    («or» := fun _ _ => [])
    («cond» := fun _ _ _ => [])
    («assign» := fun _ _ _ => [])
    («new» := fun _ => [])
    («tuple» := fun _ _ => [])
    («inlineArray» := fun _ _ => [])
    («ident» := fun _ => [])
    («lit» := fun _ => [])
    («litUnit» := fun _ _ => [])
    («elemType» := fun _ _ => [])
    («declVar» := fun _ _ => [])
    («declTuple» := fun _ _ _ _ => [])
    («exprStmt» := fun _ => [])
    («blockStmt» := fun {_} _ => [])
    («simpleStmt» := fun {_} _ => [])
    («ifStmt» := fun {_} _ _ _ => [])
    («forStmt» := fun {_ _} _ _ _ _ => [])
    («whileStmt» := fun {_ _} _ _ => [])
    («doWhile» := fun {_ _} _ _ => [])
    («continueStmt» := fun {_} => [])
    («breakStmt» := fun {_} => [])
    («tryStmt» := fun {_} _ _ _ _ _ => [])
    («catchPlain» := fun {_} _ => [])
    («catchSig» := fun {_} _ _ _ _ => [])
    («returnStmt» := fun {_} _ => [])
    («emit» := fun {_} _ _ => [])
    («revert» := fun {_} _ _ => [])
    («assembly» := fun {_} _ _ _ => [])
    («block» := fun {_} _ => [])
    («stmtItem» := fun {_} _ => [])
    («uncheckedItem» := fun {_} _ => [])
    («yulBlock» := fun _ => [])
    («yulLet» := fun _ _ _ => [])
    («yulAssign» := fun _ _ _ => [])
    («yulExprStmt» := fun _ => [])
    («yulIf» := fun _ _ => [])
    («yulFor» := fun _ _ _ _ => [])
    («yulSwitch» := fun _ _ _ => [])
    («yulCase» := fun _ _ => [])
    («yulLeave» := [])
    («yulBreak» := [])
    («yulContinue» := [])
    («yulFun» := fun _ _ _ _ => [])
    («yulPath» := fun _ _ => [])
    («yulCall» := fun _ _ => [])
    («yulLit» := fun _ => [])

def bodyDecls (d : Decl) : List Decl := bodyDeclsSyntax d.kind d.node

theorem bodyDecls_length (d : Decl) : (bodyDecls d).length = memberCount d := by
  rcases d with ⟨kind, name, scope, top, node⟩
  cases kind <;> cases node <;> rfl

/-- Every container's indexed occurrence has its actual body immediately after it. -/
def OwnerLayout (L : List Decl) : Prop :=
  ∀ i d, L[i]? = some d → Container d.kind →
    ∃ pre post, L = pre ++ d :: (bodyDecls d ++ post) ∧ pre.length = i

theorem no_container_layout {L : List Decl}
    (h : ∀ d, d ∈ L → ¬ Container d.kind) : OwnerLayout L := by
  intro i d hd hc
  exact False.elim (h d (List.mem_of_getElem? hd) hc)

theorem empty_layout : OwnerLayout [] := by
  apply no_container_layout
  intro d hd
  cases hd

theorem OwnerLayout.append {L M : List Decl} (hL : OwnerLayout L) (hM : OwnerLayout M) :
    OwnerLayout (L ++ M) := by
  intro i d hi hc
  by_cases hl : i < L.length
  · rw [List.getElem?_append_left hl] at hi
    obtain ⟨pre, post, he, hp⟩ := hL i d hi hc
    refine ⟨pre, post ++ M, ?_, hp⟩
    rw [he]
    simp only [List.append_assoc, List.cons_append]
  · have hle : L.length ≤ i := Nat.le_of_not_lt hl
    rw [List.getElem?_append_right hle] at hi
    obtain ⟨pre, post, he, hp⟩ := hM (i - L.length) d hi hc
    refine ⟨L ++ pre, post, ?_, ?_⟩
    · rw [he]
      simp only [List.append_assoc]
    · simp only [List.length_append, hp]
      omega

theorem part_no_container {t : Bool} (scope : Option String) (p : Syn (.part t))
    (d : Decl) (hd : d ∈ p.collect scope) : ¬ Container d.kind := by
  cases p <;> simp only [Syn.collect, List.mem_singleton, List.not_mem_nil] at hd
  all_goals cases hd <;> simp only [Container, reduceCtorEq, or_self, not_false_eq_true]

theorem parts_no_container {t : Bool} (scope : Option String) :
    ∀ (xs : Syn (.list (.part t))) (d : Decl), d ∈ xs.collect scope → ¬ Container d.kind
  | .nil, _, h => by cases h
  | .cons p ps, d, h => by
    rcases List.mem_append.mp h with h | h
    · exact part_no_container scope p d h
    · exact parts_no_container scope ps d h

theorem container_layout {d : Decl} {members : List Decl}
    (he : members = bodyDecls d) (hn : ∀ e, e ∈ members → ¬ Container e.kind) :
    OwnerLayout (d :: members) := by
  intro i e hi hc
  cases i with
  | zero =>
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
    subst hi
    refine ⟨[], [], ?_, rfl⟩
    simp only [List.nil_append, List.append_nil, he]
  | succ i =>
    simp only [List.getElem?_cons_succ] at hi
    exact False.elim (hn e (List.mem_of_getElem? hi) hc)

theorem top_layout (s : Syn .top) : OwnerLayout (s.collect none) := by
  cases s with
  | contract abstract name layout bases body =>
    exact container_layout rfl (parts_no_container (some name) body)
  | interface name bases body =>
    exact container_layout rfl (parts_no_container (some name) body)
  | library name body =>
    exact container_layout rfl (parts_no_container (some name) body)
  | topPart p => exact no_container_layout (part_no_container none p)
  | pragma => exact empty_layout
  | importPath => exact empty_layout
  | importStar => exact empty_layout
  | importSymbols => exact empty_layout

theorem tops_layout : ∀ xs : Syn (.list .top), OwnerLayout (xs.collect none)
  | .nil => empty_layout
  | .cons s ss => (top_layout s).append (tops_layout ss)

theorem source_layout (s : Syn .unit) : OwnerLayout s.decls := by
  cases s with
  | unit xs => exact tops_layout xs

/-- Every member identity is a position in the identified owner's actual
body; this does not require unique container spellings or source admission. -/
theorem Member.in_owner_body {P : UnitSet} {i j : DeclId} {x : String}
    (h : Member P i x j) :
    ∃ d e k, P.decl? i = some d ∧ P.decl? j = some e ∧ j.unit = i.unit ∧
      k < (bodyDecls d).length ∧ (bodyDecls d)[k]? = some e ∧ j.idx = i.idx + 1 + k := by
  cases h with
  | @intro child d e x hd hc he hu hs hn hx hlo hhi =>
    cases hui : P.unit? i.unit with
    | none =>
      have hi : P.decl? i = none := by simp only [UnitSet.decl?, hui, Option.bind_none]
      rw [hi] at hd
      cases hd
    | some s =>
      have hi : s.decls[i.idx]? = some d := by
        simpa only [UnitSet.decl?, hui, Option.bind_some] using hd
      have hj : s.decls[j.idx]? = some e := by
        simpa only [UnitSet.decl?, hu, hui, Option.bind_some] using he
      obtain ⟨pre, post, layout, hp⟩ := source_layout s i.idx d hi hc
      let k : Nat := j.idx - i.idx - 1
      have hk : k < (bodyDecls d).length := by
        rw [bodyDecls_length]
        dsimp only [k]
        omega
      rw [layout, List.getElem?_append_right (show pre.length ≤ j.idx by omega)] at hj
      have hoff : j.idx - pre.length = k + 1 := by dsimp only [k]; omega
      rw [hoff, List.getElem?_cons_succ, List.getElem?_append_left hk] at hj
      refine ⟨d, e, k, hd, he, hu, hk, hj, ?_⟩
      dsimp only [k]
      omega

end Solidity.Frontend.QualifiedUnits
