import Solidity.Frontend.QualifiedUnits.UnitPaths

/-!
# Inherited declaration namespaces on original identities

Base references retain their complete existing `IdPath`. Resolving a base
contract/interface needs unit namespaces: the intrinsic syntax cannot nest
contract declarations inside contracts. This module does not check C3,
overrides, inheritance validity or types (G14/G13); it computes declaration
visibility along the existing syntactic base graph. A nearer declaration of
the queried name stops that route. Cycles terminate by finite saturation.
-/
namespace Solidity.Frontend.QualifiedUnits
open Solidity.Source Solidity.Frontend.Static

/-- Syntactic base paths, without dropping qualifiers. -/
def basePathsSyntax (kind : DeclKind) {c : Cat} (s : Syn c) : List IdPath :=
  Syn.casesOn (motive := fun c (_ : Syn c) => List IdPath) s
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
    («contract» := fun _ _ _ a3 _ => if kind == .contract then inheritPaths a3 else [])
    («interface» := fun _ a1 _ => if kind == .interface then inheritPaths a1 else [])
    («library» := fun _ _ => [])
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

def basePaths (d : Decl) : List IdPath := basePathsSyntax d.kind d.node

/-- Independent base-reference edge over existing declaration identities. -/
inductive Base (P : UnitSet) (R : List Remapping) : DeclId → DeclId → Prop where
  | intro {i j : DeclId} {d : Decl} {p : IdPath} :
      P.decl? i = some d → p ∈ basePaths d → UnitRoute P R (Sees P R i.unit p.head) p.tail j → Base P R i j

/-- A base's private declarations are invisible before shadowing decisions.
Own-scope private declarations remain visible. -/
def VisibleMember (P : UnitSet) (root owner : DeclId) (x : String) (j : DeclId) : Prop :=
  Member P owner x j ∧ (owner = root ∨ ∃ d, P.decl? j = some d ∧ d.isPrivate = false)

inductive InheritedFrom (P : UnitSet) (R : List Remapping) (root : DeclId) : DeclId → String → DeclId → Prop where
  | here {i j : DeclId} {x : String} : VisibleMember P root i x j → InheritedFrom P R root i x j
  | base {i b j : DeclId} {x : String} : (¬ ∃ k, VisibleMember P root i x k) → Base P R i b →
      InheritedFrom P R root b x j → InheritedFrom P R root i x j

def InheritedMember (P : UnitSet) (R : List Remapping) (i : DeclId) (x : String) (j : DeclId) : Prop :=
  InheritedFrom P R i i x j

def visible (P : UnitSet) (root owner j : DeclId) : Bool :=
  if owner = root then true else
    match P.decl? j with
    | none => false
    | some d => !d.isPrivate

theorem visible_iff {P : UnitSet} {root owner j : DeclId} : visible P root owner j = true ↔
    owner = root ∨ ∃ d, P.decl? j = some d ∧ d.isPrivate = false := by
  by_cases he : owner = root
  · simp only [visible, he, if_true, true_or]
  · cases hd : P.decl? j <;>
      simp only [visible, he, if_false, hd, Bool.false_eq_true, false_or,
        Bool.not_eq_true', Option.some.injEq, reduceCtorEq, false_and, exists_false,
        exists_eq_left']

def visibleMembers (P : UnitSet) (root owner : DeclId) (x : String) : List DeclId :=
  (members P owner x).filter (visible P root owner)

theorem mem_visibleMembers {P : UnitSet} {root owner j : DeclId} {x : String} :
    j ∈ visibleMembers P root owner x ↔ VisibleMember P root owner x j := by
  simp only [visibleMembers, List.mem_filter, mem_members, visible_iff, VisibleMember]

/-- Keep declaration identities, never spelling-based copies. -/
def declIds (symbols : List Sym) : List DeclId := symbols.filterMap fun s =>
  match s with
  | .decl i => some i
  | .unit _ => none

theorem mem_declIds {ss : List Sym} {i : DeclId} : i ∈ declIds ss ↔ Sym.decl i ∈ ss := by
  constructor
  · intro h
    obtain ⟨s, hs, hi⟩ := List.mem_filterMap.mp h
    cases s with
    | unit => cases hi
    | decl j => cases Option.some.inj hi; exact hs
  · intro h
    exact List.mem_filterMap.mpr ⟨.decl i, h, rfl⟩

/-- Executable base edges require unique namespace prefixes and a base kind. -/
def baseTargets (P : UnitSet) (R : List Remapping) (i : DeclId) : List DeclId :=
  match P.decl? i with
  | none => []
  | some d => (basePaths d).filterMap fun p => unitBase P R i.unit p

theorem mem_baseTargets {P : UnitSet} {R : List Remapping} {i j : DeclId} :
    j ∈ baseTargets P R i ↔ Base P R i j := by
  unfold baseTargets
  cases hd : P.decl? i with
  | none =>
    constructor
    · intro h; cases h
    · intro h; cases h with
      | intro he _ _ => rw [hd] at he; cases he
  | some d =>
    constructor
    · intro h
      obtain ⟨p, hp, hj⟩ := List.mem_filterMap.mp h
      exact .intro hd hp (unitBase_iff.mp hj)
    · intro h
      cases h with
      | intro he hp hj =>
        cases Option.some.inj (hd.symm.trans he)
        exact List.mem_filterMap.mpr ⟨_, hp, unitBase_iff.mpr hj⟩

theorem Through.decl_exists {P : UnitSet} {R : List Remapping} {a : Sym} {xs : List String}
    {i : DeclId} (h : Through P R a xs (.decl i))
    (ha : ∀ j, a = .decl j → ∃ d, P.decl? j = some d) : ∃ d, P.decl? i = some d := by
  induction xs generalizing a with
  | nil => cases h; exact ha i rfl
  | cons x xs ih =>
    cases h with
    | next hs ht =>
      apply ih ht
      intro j hj
      rw [hj] at hs
      exact hs.decl_exists

theorem Qualified.decl_exists {P : UnitSet} {R : List Remapping} {u : String} {p : IdPath}
    {i : DeclId} (h : Qualified P R u p (.decl i)) : ∃ d, P.decl? i = some d := by
  obtain ⟨a, ha, ht⟩ := h
  apply ht.decl_exists
  intro j hj
  rw [hj] at ha
  obtain ⟨d, hd, _⟩ := ha.decl_exists
  exact ⟨d, hd⟩

/-- All original declaration positions, with the query root included. -/
def idUniverse (P : UnitSet) (root : DeclId) : List DeclId :=
  root :: P.units.flatMap fun (u, s) => (List.range s.decls.length).map fun k => ⟨u, k⟩

theorem decl_mem_universe {P : UnitSet} {root i : DeclId} {d : Decl}
    (h : P.decl? i = some d) : i ∈ idUniverse P root := by
  unfold UnitSet.decl? at h
  cases hu : P.unit? i.unit with
  | none => rw [hu] at h; cases h
  | some s =>
    simp only [hu, Option.bind_some] at h
    have hi : i.idx < s.decls.length := (List.getElem?_eq_some_iff.mp h).1
    apply List.mem_cons_of_mem
    apply List.mem_flatMap.mpr
    refine ⟨(i.unit, s), UnitSet.unit?_mem hu, ?_⟩
    exact List.mem_map.mpr ⟨i.idx, List.mem_range.mpr hi, by cases i; rfl⟩

/-- Base traversal stops when this scope declares the queried name. -/
def baseSucc (P : UnitSet) (R : List Remapping) (root : DeclId) (x : String) (i : DeclId) : List DeclId :=
  if visibleMembers P root i x = [] then baseTargets P R i else []

theorem mem_baseSucc {P : UnitSet} {R : List Remapping} {x : String} {root i j : DeclId} :
    j ∈ baseSucc P R root x i ↔ (¬ ∃ k, VisibleMember P root i x k) ∧ Base P R i j := by
  unfold baseSucc
  by_cases he : visibleMembers P root i x = []
  · simp only [he, if_true, mem_baseTargets]
    have hn : ¬ ∃ k, VisibleMember P root i x k := by
      intro ⟨k, hk⟩
      have hm := mem_visibleMembers.mpr hk
      rw [he] at hm
      cases hm
    exact ⟨fun h => ⟨hn, h⟩, And.right⟩
  · simp only [he, if_false, List.not_mem_nil, false_iff]
    intro ⟨hn, _⟩
    apply he
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro k hk
    exact hn ⟨k, mem_visibleMembers.mp hk⟩

theorem baseSucc_closed (P : UnitSet) (R : List Remapping) (root : DeclId) (x : String) :
    ∀ a, a ∈ idUniverse P root → ∀ b, b ∈ baseSucc P R root x a → b ∈ idUniverse P root := by
  intro a _ b hb
  obtain ⟨_, he⟩ := mem_baseSucc.mp hb
  cases he with
  | intro _ _ hq =>
    obtain ⟨d, hd, _⟩ := hq.decl_exists
    exact decl_mem_universe hd

/-- Executable inherited lookup, bounded by the existing finite identity graph. -/
def inheritedMembers (P : UnitSet) (R : List Remapping) (i : DeclId) (x : String) : List DeclId :=
  (reachable (baseSucc P R i x) (idUniverse P i) i).flatMap fun b => visibleMembers P i b x

theorem InheritedFrom.reach {P : UnitSet} {R : List Remapping} {root i j : DeclId} {x : String}
    (h : InheritedFrom P R root i x j) :
    ∃ b, Reach (baseSucc P R root x) i b ∧ VisibleMember P root b x j := by
  induction h with
  | here hm => exact ⟨_, .refl _, hm⟩
  | base hn hb _ ih =>
    obtain ⟨b, hr, hm⟩ := ih
    exact ⟨b, .step (mem_baseSucc.mpr ⟨hn, hb⟩) hr, hm⟩

theorem inherited_of_reach {P : UnitSet} {R : List Remapping} {root i b j : DeclId} {x : String}
    (h : Reach (baseSucc P R root x) i b) (hm : VisibleMember P root b x j) : InheritedFrom P R root i x j := by
  induction h with
  | refl => exact .here hm
  | step hb _ ih =>
    obtain ⟨hn, he⟩ := mem_baseSucc.mp hb
    exact .base hn he (ih hm)

theorem mem_inheritedMembers {P : UnitSet} {R : List Remapping} {i j : DeclId} {x : String} :
    j ∈ inheritedMembers P R i x ↔ InheritedMember P R i x j := by
  have reach : ∀ b, b ∈ reachable (baseSucc P R i x) (idUniverse P i) i ↔ Reach (baseSucc P R i x) i b :=
    fun _ => mem_reachable (baseSucc_closed P R i x) (List.mem_cons_self : i ∈ idUniverse P i)
  constructor
  · intro h
    obtain ⟨b, hb, hj⟩ := List.mem_flatMap.mp h
    exact inherited_of_reach ((reach _).mp hb) (mem_visibleMembers.mp hj)
  · intro h
    obtain ⟨b, hb, hj⟩ := InheritedFrom.reach h
    exact List.mem_flatMap.mpr ⟨b, (reach _).mpr hb, mem_visibleMembers.mpr hj⟩

end Solidity.Frontend.QualifiedUnits
