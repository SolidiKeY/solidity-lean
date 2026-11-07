import Solidity.Source.Typing

/-! H57/H125 additive environment-aware statement typing.
Regression: a nameable mapping-bearing struct must be refused as a memory or
calldata local, while an initialized storage reference remains admissible.
V1 StmtD/ItemsD and its intentionally negative refusal statements are frozen.
A generic fold over the original derivation checks only declaration locations;
all other premises and resolved typing evidence are reused without a rule copy.
No Lowering import, global admission change or v1 retirement is introduced. -/
namespace Solidity.Source

/-- V2 local declaration location policy; equivalent to the published H24
environment-aware formula, without importing the Lowering consumer. -/
def envLocOK (E : Env) (ty : STy) (loc : Option DataLoc) (initialized : Bool) : Bool :=
  locOK ty loc initialized &&
    (loc.isNone || loc == some .storage || !E.hasMapping (E.structCount + 1) ty)

theorem envLocOK_implies_locOK {E : Env} {ty : STy} {loc : Option DataLoc}
    {initialized : Bool} (ok : envLocOK E ty loc initialized = true) :
    locOK ty loc initialized = true := by
  simp only [envLocOK, Bool.and_eq_true] at ok
  exact ok.1

/-- An explicit v2 location is storage or contains no mapping. -/
theorem envLocOK_sound :
 ∀ (E : Solidity.Source.Env) (ty : Solidity.Source.STy) (loc : Solidity.Source.DataLoc)
(initialized : Bool), Solidity.Source.envLocOK E ty (some loc) initialized = true →
loc = .storage ∨ E.hasMapping (E.structCount + 1) ty = false := by
  intro E ty loc initialized ok
  have allowed := (Bool.and_eq_true_iff.mp ok).2
  cases loc <;> cases mapping : E.hasMapping (E.structCount + 1) ty <;>
    rw [mapping] at allowed <;> first
    | exact Or.inl rfl
    | exact Or.inr mapping
    | exact Or.inr rfl
    | cases allowed

namespace V2

mutual
/-- The reusable declaration-policy fold, with generalized indexed elimination. -/
def checkStmt (rule : STy → Option DataLoc → Bool → Bool)
    {C : Ctx} {k : SCtx} {L L' : List (String × STy)} {s : Syn (.stmt k)}
    (d : Source.StmtD C L s L') : Bool := by
  apply Source.StmtD.casesOn (motive_1 := fun {_} _ _ _ _ => Bool) d
  case declVar =>
    intro k L t loc name ty typed location
    exact rule ty loc false
  case declInit =>
    intro k L t loc name e ty sourceTy typed location expression conversion
    exact rule ty loc true
  case block =>
    intro k L L' b body
    exact checkItems rule body
  case ifThen =>
    intro k L L' c s typed notDecl body
    exact checkStmt rule body
  case ifElse =>
    intro k L L1 L2 c s t typed notFirst notSecond first second
    exact checkStmt rule first && checkStmt rule second
  case whileLoop =>
    intro l u L L' c s typed notDecl body
    exact checkStmt rule body
  case doWhile =>
    intro l u L L' c s notDecl body typed
    exact checkStmt rule body
  case forLoop =>
    intro l u L L' cond post s typedCond typedPost notDecl body
    exact checkStmt rule body
  case forInit =>
    intro l u L L1 L2 i cond post s initial typedCond typedPost notDecl body
    exact checkStmt rule initial && checkStmt rule body
  case tryCall =>
    intro k L L1 L2 c f args rets okb cl dn d ps rs sigmas tys name cb target argv overload signature fit named same success catchClause failure
    exact checkItems rule success && checkItems rule failure
  all_goals (intros; exact true)
termination_by structural d

/-- Unchecked and catch traversal uses the same generalized policy elimination. -/
def checkItems (rule : STy → Option DataLoc → Bool → Bool)
    {C : Ctx} {k : SCtx} {L L' : List (String × STy)}
    {s : Syn (.list (.item k))} (d : Source.ItemsD C L s L') : Bool := by
  apply Source.ItemsD.casesOn (motive_2 := fun {_} _ _ _ _ => Bool) d
  case nil => intros; exact true
  case stmt =>
    intro k L L1 L2 s rest first tail
    exact checkStmt rule first && checkItems rule tail
  case unchecked =>
    intro l L L1 L2 b rest body tail
    exact checkItems rule body && checkItems rule tail
termination_by structural d
end

/-- Additive v2 judgment: the original derivation, with the stronger policy
checked at exactly its declVar/declInit nodes, recursively. -/
structure StmtD (C : Ctx) {k : SCtx} (L : List (String × STy))
    (s : Syn (.stmt k)) (L' : List (String × STy)) where
  toV1 : Source.StmtD C L s L'
  locations : checkStmt (envLocOK C.env) toV1 = true

structure ItemsD (C : Ctx) {k : SCtx} (L : List (String × STy))
    (s : Syn (.list (.item k))) (L' : List (String × STy)) where
  toV1 : Source.ItemsD C L s L'
  locations : checkItems (envLocOK C.env) toV1 = true

/-- V2 declaration formation has exactly v1's premises except envLocOK. -/
def StmtD.declVar {C : Ctx} {k : SCtx} {L : List (String × STy)}
    {t : Syn .typeName} {loc : Option DataLoc} {name : String} {ty : STy}
    (typed : t.ty C.env C.scope (loc.getD .memory) = some ty)
    (location : envLocOK C.env ty loc false = true) :
    StmtD C (k := k) L (.simpleStmt (.declVar (.varDecl t loc name) .none)) ((name, ty) :: L) :=
  ⟨.declVar typed (envLocOK_implies_locOK location), location⟩

/-- V2 initialized declarations retain expression typing and conversion exactly. -/
def StmtD.declInit {C : Ctx} {k : SCtx} {L : List (String × STy)}
    {t : Syn .typeName} {loc : Option DataLoc} {name : String}
    {e : Syn .expr} {ty sourceTy : STy}
    (typed : t.ty C.env C.scope (loc.getD .memory) = some ty)
    (location : envLocOK C.env ty loc true = true)
    (expression : Typed (C.at L) e sourceTy)
    (conversion : sourceTy.implicit C.isBase C.mapFree ty = true) :
    StmtD C (k := k) L (.simpleStmt (.declVar (.varDecl t loc name) (.some e))) ((name, ty) :: L) :=
  ⟨.declInit typed (envLocOK_implies_locOK location) expression conversion, location⟩


/-- The environment condition is restricted to types actually named in a scope,
rather than arbitrary unrelated type values. It states the precise premise
needed by the v1-to-v2 bridge; v2 admission itself requires no such assumption. -/
def CompatibleAt (C : Ctx) : Prop :=
  ∀ (t : Syn .typeName) ty loc initialized,
    t.ty C.env C.scope (loc.getD .memory) = some ty →
    locOK ty loc initialized = true → envLocOK C.env ty loc initialized = true

mutual
def checkStmt_valid (rule : STy → Option DataLoc → Bool → Bool)
    {C : Ctx}
    (respects : ∀ (t : Syn .typeName) ty loc initialized,
      t.ty C.env C.scope (loc.getD .memory) = some ty →
      locOK ty loc initialized = true → rule ty loc initialized = true)
    {k : SCtx} {L L' : List (String × STy)} {s : Syn (.stmt k)}
    (d : Source.StmtD C L s L') : checkStmt rule d = true :=
  match d with
  | .declVar (τ := ty) (l := loc) typed location => respects _ ty loc false typed location
  | .declInit (τ := ty) (l := loc) typed location _ _ => respects _ ty loc true typed location
  | .block body => checkItems_valid rule respects body
  | .ifThen _ _ body => checkStmt_valid rule respects body
  | .ifElse _ _ _ first second =>
      Bool.and_eq_true_iff.mpr ⟨checkStmt_valid rule respects first, checkStmt_valid rule respects second⟩
  | .whileLoop _ _ body => checkStmt_valid rule respects body
  | .doWhile _ body _ => checkStmt_valid rule respects body
  | .forLoop _ _ _ body => checkStmt_valid rule respects body
  | .forInit initial _ _ _ body =>
      Bool.and_eq_true_iff.mpr ⟨checkStmt_valid rule respects initial, checkStmt_valid rule respects body⟩
  | .tryCall _ _ _ _ _ _ _ success _ failure =>
      Bool.and_eq_true_iff.mpr ⟨checkItems_valid rule respects success, checkItems_valid rule respects failure⟩
  | .expr _ _ | .placeholder _ | .declTuple _ _ _ | .brk | .cont |
    .ret _ | .retVal _ _ _ | .retTuple _ _ _ _ | .emit _ _ |
    .revertError _ _ | .rethrow _ _ _ _ => rfl

def checkItems_valid (rule : STy → Option DataLoc → Bool → Bool)
    {C : Ctx}
    (respects : ∀ (t : Syn .typeName) ty loc initialized,
      t.ty C.env C.scope (loc.getD .memory) = some ty →
      locOK ty loc initialized = true → rule ty loc initialized = true)
    {k : SCtx} {L L' : List (String × STy)} {s : Syn (.list (.item k))}
    (d : Source.ItemsD C L s L') : checkItems rule d = true :=
  match d with
  | .nil => rfl
  | .stmt first rest =>
      Bool.and_eq_true_iff.mpr ⟨checkStmt_valid rule respects first, checkItems_valid rule respects rest⟩
  | .unchecked body rest =>
      Bool.and_eq_true_iff.mpr ⟨checkItems_valid rule respects body, checkItems_valid rule respects rest⟩
end

/-- V1 derivations lift exactly under the named-type compatibility premise. -/
def StmtD.ofV1 {C : Ctx} {k : SCtx} {L L' : List (String × STy)} {s : Syn (.stmt k)}
    (d : Source.StmtD C L s L') (compatible : CompatibleAt C) : StmtD C L s L' :=
  ⟨d, checkStmt_valid (envLocOK C.env) compatible d⟩

def ItemsD.ofV1 {C : Ctx} {k : SCtx} {L L' : List (String × STy)}
    {s : Syn (.list (.item k))} (d : Source.ItemsD C L s L')
    (compatible : CompatibleAt C) : ItemsD C L s L' :=
  ⟨d, checkItems_valid (envLocOK C.env) compatible d⟩

/-- Inversion retains the actual initialized/uninitialized declaration check. -/
theorem declaration_location :
 ∀ (C : Solidity.Source.Ctx) (k : Solidity.Source.SCtx)
(L L' : List (String × Solidity.Source.STy)) (t : Solidity.Source.Syn .typeName)
(loc : Solidity.Source.DataLoc) (name : String) (init : Solidity.Source.Syn (.opt .expr))
(ty : Solidity.Source.STy),
t.ty C.env C.scope loc = some ty →
Solidity.Source.V2.StmtD C (k := k) L
(.simpleStmt (.declVar (.varDecl t (some loc) name) init)) L' →
∃ initialized, Solidity.Source.envLocOK C.env ty (some loc) initialized = true := by
  intro C k L L' t loc name init ty typed derivation
  rcases derivation with ⟨derivation, checked⟩
  cases derivation with
  | declVar typed' location =>
    rw [Option.getD_some, typed] at typed'
    cases typed'
    exact ⟨false, checked⟩
  | declInit typed' location expression conversion =>
    rw [Option.getD_some, typed] at typed'
    cases typed'
    exact ⟨true, checked⟩

/-- Positive H24 local declaration admission for v2, in every environment.
No compatibility assumption is needed for this direction. -/
theorem declaration_admissible :
 ∀ (C : Solidity.Source.Ctx) (k : Solidity.Source.SCtx)
(L L' : List (String × Solidity.Source.STy)) (t : Solidity.Source.Syn .typeName)
(loc : Solidity.Source.DataLoc) (name : String) (init : Solidity.Source.Syn (.opt .expr))
(ty : Solidity.Source.STy),
t.ty C.env C.scope loc = some ty →
Solidity.Source.V2.StmtD C (k := k) L
(.simpleStmt (.declVar (.varDecl t (some loc) name) init)) L' →
loc = .storage ∨ C.env.hasMapping (C.env.structCount + 1) ty = false := by
  intro C k L L' t loc name init ty typed derivation
  obtain ⟨initialized, admitted⟩ :=
    Solidity.Source.V2.declaration_location C k L L' t loc name init ty typed derivation
  exact Solidity.Source.envLocOK_sound C.env ty loc initialized admitted

end V2
end Solidity.Source
