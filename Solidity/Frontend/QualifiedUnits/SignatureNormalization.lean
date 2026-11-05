import Solidity.Frontend.QualifiedUnits.TypePaths
import Solidity.Source.Typing

/-! H27: reusable signature comparison metadata over existing Source syntax.
Every nominal reference is indexed by the actual UnitSet and carries an
original DeclId whose original declaration has the required kind. These are
type comparison keys, not an operational AST, and no Source API is changed. -/
namespace Solidity.Frontend.QualifiedUnits.SignatureNormalization
open Solidity.Source

abbrev Declared (P : UnitSet) := {i : DeclId // ∃ d, P.decl? i = some d}
abbrev Nominal (P : UnitSet) (kind : DeclKind) :=
  {i : DeclId // ∃ d, P.decl? i = some d ∧ d.kind = kind}
abbrev ContractRef (P : UnitSet) :=
  {i : DeclId // ∃ d, P.decl? i = some d ∧ (d.kind = .contract ∨ d.kind = .interface)}

/-- Existing primitive type carriers; nominal identity is never a spelling. -/
inductive TypeKey (P : UnitSet) where
  | integer (ty : IntTy)
  | boolean
  | address (payable : Bool)
  | fixedBytes (n : Nat) (valid : 1 ≤ n ∧ n ≤ 32)
  | fixedPoint (ty : FixTy)
  | bytes (loc : DataLoc)
  | string (loc : DataLoc)
  | enumeration (ref : Nominal P .enum)
  | valueType (ref : Nominal P .udvt)
  | contract (ref : ContractRef P)
  | record (loc : DataLoc) (ref : Nominal P .struct)
  | array (loc : DataLoc) (element : TypeKey P) (length : Option Nat)
  | mapping (key value : TypeKey P)
  | callable (external : Bool) (params returns : List (TypeKey P)) (mutability : Option Mutability)
  deriving Repr

mutual

def TypeKey.same {P : UnitSet} : TypeKey P → TypeKey P → Bool
  | .integer a,.integer b => decide (a = b)
  | .boolean,.boolean => true
  | .address a,.address b => decide (a = b)
  | .fixedBytes a _,.fixedBytes b _ => decide (a = b)
  | .fixedPoint a,.fixedPoint b => decide (a = b)
  | .bytes a,.bytes b | .string a,.string b => decide (a = b)
  | .enumeration a,.enumeration b => decide (a = b)
  | .valueType a,.valueType b => decide (a = b)
  | .contract a,.contract b => decide (a = b)
  | .record l a,.record m b => decide (l = m) && decide (a = b)
  | .array l a n,.array m b k => decide (l = m) && a.same b && decide (n = k)
  | .mapping a b,.mapping c d => a.same c && b.same d
  | .callable e ps rs m,.callable f qs ts n =>
      decide (e = f) && TypeKey.sameList ps qs && TypeKey.sameList rs ts && decide (m = n)
  | _,_ => false

def TypeKey.sameList {P : UnitSet} : List (TypeKey P) → List (TypeKey P) → Bool
  | [],[] => true
  | a :: as_,b :: bs => a.same b && TypeKey.sameList as_ bs
  | _,_ => false

end

mutual

theorem TypeKey.eq_of_same {P : UnitSet} : (a b : TypeKey P) → a.same b = true → a = b
  | a,b,h => by
    cases a <;> cases b <;>
      simp_all only [TypeKey.same,Bool.false_eq_true,decide_eq_true_eq,Bool.and_eq_true,
        TypeKey.array.injEq,TypeKey.mapping.injEq,TypeKey.callable.injEq,and_true,true_and] <;>
      first
      | exact TypeKey.eq_of_same _ _ h.1.2
      | exact ⟨TypeKey.eq_of_same _ _ h.1,TypeKey.eq_of_same _ _ h.2⟩
      | exact ⟨TypeKey.eq_of_sameList _ _ h.1.1.2,TypeKey.eq_of_sameList _ _ h.1.2⟩

theorem TypeKey.eq_of_sameList {P : UnitSet} : (a b : List (TypeKey P)) → TypeKey.sameList a b = true → a = b
  | [],[],_ => rfl
  | a :: as_,b :: bs,h => by
    simp only [TypeKey.sameList,Bool.and_eq_true] at h
    rw [TypeKey.eq_of_same a b h.1,TypeKey.eq_of_sameList as_ bs h.2]
  | [],_ :: _,h => by cases h
  | _ :: _,[],h => by cases h

end

mutual

theorem TypeKey.same_refl {P : UnitSet} : (a : TypeKey P) → a.same a = true
  | .array l a n => by simp only [TypeKey.same,decide_true,TypeKey.same_refl a,Bool.and_self]
  | .mapping a b => by simp only [TypeKey.same,TypeKey.same_refl a,TypeKey.same_refl b,Bool.and_self]
  | .callable e ps rs m => by
    simp only [TypeKey.same,decide_true,TypeKey.sameList_refl ps,TypeKey.sameList_refl rs,Bool.and_self]
  | .integer _ | .boolean | .address _ | .fixedBytes _ _ | .fixedPoint _ | .bytes _ | .string _
  | .enumeration _ | .valueType _ | .contract _ | .record _ _ => by
    simp only [TypeKey.same,decide_true,Bool.and_self]

theorem TypeKey.sameList_refl {P : UnitSet} : (a : List (TypeKey P)) → TypeKey.sameList a a = true
  | [] => rfl
  | a :: as_ => by simp only [TypeKey.sameList,TypeKey.same_refl a,TypeKey.sameList_refl as_,Bool.and_self]

end

instance instDecidableEqTypeKey {P : UnitSet} : DecidableEq (TypeKey P) := fun a b =>
  if h : a.same b = true then isTrue (TypeKey.eq_of_same a b h)
  else isFalse (fun equal => h (equal ▸ TypeKey.same_refl a))

def elementary (P : UnitSet) (loc : DataLoc) : Elem → TypeKey P
  | .address => .address false
  | .addressPayable => .address true
  | .bool => .boolean
  | .bytes => .bytes loc
  | .string => .string loc
  | .int sign bits valid => .integer ⟨sign,bits,valid⟩
  | .fixedBytes n valid => .fixedBytes n valid
  | .fixed sign none => .fixedPoint ⟨sign,128,18,by decide⟩
  | .fixed sign (some dims) => .fixedPoint ⟨sign,dims.bits,dims.digits,dims.valid⟩

/-- Type paths resolve to original declaration positions, including aliases. -/
def nominal (P : UnitSet) (R : List Remapping) (u : String) (scope : Option DeclId)
    (loc : DataLoc) (path : IdPath) : Option (TypeKey P) :=
  match TypePaths.lookup P R u scope path with
  | none => none
  | some i =>
    match hd : P.decl? i with
    | none => none
    | some d =>
      match hk : d.kind with
      | .enum => some (.enumeration ⟨i,d,hd,hk⟩)
      | .udvt => some (.valueType ⟨i,d,hd,hk⟩)
      | .struct => some (.record loc ⟨i,d,hd,hk⟩)
      | .contract => some (.contract ⟨i,d,hd,Or.inl hk⟩)
      | .interface => some (.contract ⟨i,d,hd,Or.inr hk⟩)
      | _ => none

def TypeKey.nominalId? {P : UnitSet} : TypeKey P → Option DeclId
  | .enumeration ref | .valueType ref => some ref.val
  | .contract ref => some ref.val
  | .record _ ref => some ref.val
  | _ => none

/-- A normalized nominal leaf denotes precisely the original qualified path,
not merely some existing declaration of the same spelling or kind. -/
theorem nominal_origin {P : UnitSet} {R : List Remapping} {u : String} {scope : Option DeclId}
    {loc : DataLoc} {path : IdPath} {key : TypeKey P}
    (h : nominal P R u scope loc path = some key) :
    ∃ i, TypePaths.Route P R (TypePaths.head P R u scope path.head) path.tail (.decl i) ∧
      key.nominalId? = some i := by
  unfold nominal at h
  split at h
  · cases h
  · rename_i i hi
    split at h
    · cases h
    · rename_i decl hd
      split at h
      all_goals first
      | (solve | cases h)
      | cases Option.some.inj h; exact ⟨i,TypePaths.lookup_iff.mp hi,rfl⟩

def keyType (P : UnitSet) (R : List Remapping) (u : String) (scope : Option DeclId) :
    MapKey → Option (TypeKey P)
  | .elem e _ => some (elementary P .memory e)
  | .path path =>
    match nominal P R u scope .memory path with
    | some (.record _ _) => none
    | result => result

/-- Structural recursion over original type/parameter syntax. Array length
folding is the existing Source.arrayLen, not a new expression interpreter. -/
def types (P : UnitSet) (R : List Remapping) (u : String) (scope : Option DeclId)
    (loc : DataLoc) {c : Cat} (s : Syn c) : Option (List (TypeKey P)) :=
  Syn.casesOn (motive := fun c (_ : Syn c) => Option (List (TypeKey P))) s
    («nil» := fun {_} => some [])
    («cons» := fun {_} a0 a1 => match types P R u scope loc a0, types P R u scope loc a1 with
      | some first,some rest => some (first ++ rest)
      | _,_ => none)
    («none» := fun {_} => none)
    («some» := fun {_} _ => none)
    («unit» := fun _ => none)
    («pragma» := fun _ => none)
    («importPath» := fun _ _ => none)
    («importSymbols» := fun _ _ _ => none)
    («importStar» := fun _ _ => none)
    («importAlias» := fun _ _ => none)
    («contract» := fun _ _ _ _ _ => none)
    («interface» := fun _ _ _ => none)
    («library» := fun _ _ => none)
    («topPart» := fun _ => none)
    («inherit» := fun _ _ => none)
    («constructor» := fun _ _ _ _ _ => none)
    («function» := fun {_} _ _ _ _ _ _ _ _ _ => none)
    («modifier» := fun _ _ _ _ _ => none)
    («fallback» := fun _ _ _ _ _ _ _ => none)
    («fbNoParams» := none)
    («fbParams» := fun _ _ _ => none)
    («receive» := fun _ _ _ _ _ _ => none)
    («struct» := fun {_} _ _ _ => none)
    («structMember» := fun _ _ => none)
    («enum» := fun {_} _ _ _ => none)
    («udvt» := fun {_} _ _ => none)
    («stateVar» := fun _ _ _ _ _ _ _ => none)
    («constant» := fun _ _ _ => none)
    («event» := fun {_} _ _ _ => none)
    («eventParam» := fun a0 _ _ => types P R u scope .memory a0)
    («error» := fun {_} _ _ => none)
    («errorParam» := fun a0 _ => types P R u scope .memory a0)
    («usingPart» := fun {_} _ => none)
    («usingPath» := fun _ _ _ => none)
    («usingAliases» := fun _ _ _ _ => none)
    («usingAlias» := fun _ _ => none)
    («positional» := fun _ => none)
    («named» := fun _ => none)
    («namedArg» := fun _ _ => none)
    («modInv» := fun _ _ => none)
    («param» := fun a0 a1 _ => types P R u scope (a1.getD loc) a0)
    («elem» := fun a0 => some [elementary P loc a0])
    («fnType» := fun a0 a1 a2 a3 => match types P R u scope .memory a0, types P R u scope .memory a3 with
      | some ps,some rs => some [.callable (a1 == some .external) ps rs a2]
      | _,_ => none)
    («mapping» := fun a0 _ a2 _ => if loc = .storage then
      match keyType P R u scope a0, types P R u scope .storage a2 with
      | some k,some [v] => some [.mapping k v]
      | _,_ => none
      else none)
    («userType» := fun a0 => (nominal P R u scope loc a0).map ([·]))
    («array» := fun a0 a1 => match types P R u scope loc a0, arrayLen a1 with
      | some [element], some length => some [.array loc element length]
      | _,_ => none)
    («varDecl» := fun _ _ _ => none)
    («index» := fun _ _ => none)
    («slice» := fun _ _ _ => none)
    («member» := fun _ _ => none)
    («callOptions» := fun _ _ _ => none)
    («call» := fun _ _ => none)
    («payableConv» := fun _ => none)
    («metaType» := fun _ => none)
    («unaryPrefix» := fun _ _ => none)
    («unarySuffix» := fun _ _ => none)
    («exp» := fun _ _ => none)
    («mulDivMod» := fun _ _ _ => none)
    («addSub» := fun _ _ _ => none)
    («shift» := fun _ _ _ => none)
    («bitAnd» := fun _ _ => none)
    («bitXor» := fun _ _ => none)
    («bitOr» := fun _ _ => none)
    («order» := fun _ _ _ => none)
    («equality» := fun _ _ _ => none)
    («and» := fun _ _ => none)
    («or» := fun _ _ => none)
    («cond» := fun _ _ _ => none)
    («assign» := fun _ _ _ => none)
    («new» := fun _ => none)
    («tuple» := fun _ _ => none)
    («inlineArray» := fun _ _ => none)
    («ident» := fun _ => none)
    («lit» := fun _ => none)
    («litUnit» := fun _ _ => none)
    («elemType» := fun _ _ => none)
    («declVar» := fun _ _ => none)
    («declTuple» := fun _ _ _ _ => none)
    («exprStmt» := fun _ => none)
    («blockStmt» := fun {_} _ => none)
    («simpleStmt» := fun {_} _ => none)
    («ifStmt» := fun {_} _ _ _ => none)
    («forStmt» := fun {_ _} _ _ _ _ => none)
    («whileStmt» := fun {_ _} _ _ => none)
    («doWhile» := fun {_ _} _ _ => none)
    («continueStmt» := fun {_} => none)
    («breakStmt» := fun {_} => none)
    («tryStmt» := fun {_} _ _ _ _ _ => none)
    («catchPlain» := fun {_} _ => none)
    («catchSig» := fun {_} _ _ _ _ => none)
    («returnStmt» := fun {_} _ => none)
    («emit» := fun {_} _ _ => none)
    («revert» := fun {_} _ _ => none)
    («assembly» := fun {_} _ _ _ => none)
    («block» := fun {_} _ => none)
    («stmtItem» := fun {_} _ => none)
    («uncheckedItem» := fun {_} _ => none)
    («yulBlock» := fun _ => none)
    («yulLet» := fun _ _ _ => none)
    («yulAssign» := fun _ _ _ => none)
    («yulExprStmt» := fun _ => none)
    («yulIf» := fun _ _ => none)
    («yulFor» := fun _ _ _ _ => none)
    («yulSwitch» := fun _ _ _ => none)
    («yulCase» := fun _ _ => none)
    («yulLeave» := none)
    («yulBreak» := none)
    («yulContinue» := none)
    («yulFun» := fun _ _ _ _ => none)
    («yulPath» := fun _ _ => none)
    («yulCall» := fun _ _ => none)
    («yulLit» := fun _ => none)
termination_by structural s

/-- Original owner occurrence, not a name-based join between equal spellings. -/
def owns (P : UnitSet) (owner child : DeclId) (decl : Decl) : Bool :=
  match P.decl? owner with
  | none => false
  | some container => decide (Container container.kind) &&
    owner.unit == child.unit && decl.scope == some container.name &&
    decide (owner.idx < child.idx ∧ child.idx ≤ owner.idx + memberCount container)

def ownerScope (P : UnitSet) (i : DeclId) (decl : Decl) : Option (Option DeclId) :=
  match decl.scope with
  | none => some none
  | some _ =>
    match uniqueSymbol (((idUniverse P i).filter (fun owner => owns P owner i decl)).map Sym.decl) with
    | some (.decl owner) => some (some owner)
    | _ => none

def partsSyntax (P : UnitSet) (R : List Remapping) (u : String) (scope : Option DeclId)
    (kind : DeclKind) {c : Cat} (s : Syn c) : Option (List (TypeKey P) × List (TypeKey P)) :=
  Syn.casesOn (motive := fun c (_ : Syn c) => Option (List (TypeKey P) × List (TypeKey P))) s
    («nil» := fun {_} => none)
    («cons» := fun {_} _ _ => none)
    («none» := fun {_} => none)
    («some» := fun {_} _ => none)
    («unit» := fun _ => none)
    («pragma» := fun _ => none)
    («importPath» := fun _ _ => none)
    («importSymbols» := fun _ _ _ => none)
    («importStar» := fun _ _ => none)
    («importAlias» := fun _ _ => none)
    («contract» := fun _ _ _ _ _ => none)
    («interface» := fun _ _ _ => none)
    («library» := fun _ _ => none)
    («topPart» := fun _ => none)
    («inherit» := fun _ _ => none)
    («constructor» := fun _ _ _ _ _ => none)
    («function» := fun {_} _ a1 _ _ _ _ _ a7 _ => if kind == .function then
      match types P R u scope .memory a1, types P R u scope .memory a7 with
      | some ps,some rs => some (ps,rs)
      | _,_ => none
      else none)
    («modifier» := fun _ _ _ _ _ => none)
    («fallback» := fun _ _ _ _ _ _ _ => none)
    («fbNoParams» := none)
    («fbParams» := fun _ _ _ => none)
    («receive» := fun _ _ _ _ _ _ => none)
    («struct» := fun {_} _ _ _ => none)
    («structMember» := fun _ _ => none)
    («enum» := fun {_} _ _ _ => none)
    («udvt» := fun {_} _ _ => none)
    («stateVar» := fun _ _ _ _ _ _ _ => none)
    («constant» := fun _ _ _ => none)
    («event» := fun {_} _ a1 _ => if kind == .event then (types P R u scope .memory a1).map (fun ps => (ps,[])) else none)
    («eventParam» := fun _ _ _ => none)
    («error» := fun {_} _ _ => none)
    («errorParam» := fun _ _ => none)
    («usingPart» := fun {_} _ => none)
    («usingPath» := fun _ _ _ => none)
    («usingAliases» := fun _ _ _ _ => none)
    («usingAlias» := fun _ _ => none)
    («positional» := fun _ => none)
    («named» := fun _ => none)
    («namedArg» := fun _ _ => none)
    («modInv» := fun _ _ => none)
    («param» := fun _ _ _ => none)
    («elem» := fun _ => none)
    («fnType» := fun _ _ _ _ => none)
    («mapping» := fun _ _ _ _ => none)
    («userType» := fun _ => none)
    («array» := fun _ _ => none)
    («varDecl» := fun _ _ _ => none)
    («index» := fun _ _ => none)
    («slice» := fun _ _ _ => none)
    («member» := fun _ _ => none)
    («callOptions» := fun _ _ _ => none)
    («call» := fun _ _ => none)
    («payableConv» := fun _ => none)
    («metaType» := fun _ => none)
    («unaryPrefix» := fun _ _ => none)
    («unarySuffix» := fun _ _ => none)
    («exp» := fun _ _ => none)
    («mulDivMod» := fun _ _ _ => none)
    («addSub» := fun _ _ _ => none)
    («shift» := fun _ _ _ => none)
    («bitAnd» := fun _ _ => none)
    («bitXor» := fun _ _ => none)
    («bitOr» := fun _ _ => none)
    («order» := fun _ _ _ => none)
    («equality» := fun _ _ _ => none)
    («and» := fun _ _ => none)
    («or» := fun _ _ => none)
    («cond» := fun _ _ _ => none)
    («assign» := fun _ _ _ => none)
    («new» := fun _ => none)
    («tuple» := fun _ _ => none)
    («inlineArray» := fun _ _ => none)
    («ident» := fun _ => none)
    («lit» := fun _ => none)
    («litUnit» := fun _ _ => none)
    («elemType» := fun _ _ => none)
    («declVar» := fun _ _ => none)
    («declTuple» := fun _ _ _ _ => none)
    («exprStmt» := fun _ => none)
    («blockStmt» := fun {_} _ => none)
    («simpleStmt» := fun {_} _ => none)
    («ifStmt» := fun {_} _ _ _ => none)
    («forStmt» := fun {_ _} _ _ _ _ => none)
    («whileStmt» := fun {_ _} _ _ => none)
    («doWhile» := fun {_ _} _ _ => none)
    («continueStmt» := fun {_} => none)
    («breakStmt» := fun {_} => none)
    («tryStmt» := fun {_} _ _ _ _ _ => none)
    («catchPlain» := fun {_} _ => none)
    («catchSig» := fun {_} _ _ _ _ => none)
    («returnStmt» := fun {_} _ => none)
    («emit» := fun {_} _ _ => none)
    («revert» := fun {_} _ _ => none)
    («assembly» := fun {_} _ _ _ => none)
    («block» := fun {_} _ => none)
    («stmtItem» := fun {_} _ => none)
    («uncheckedItem» := fun {_} _ => none)
    («yulBlock» := fun _ => none)
    («yulLet» := fun _ _ _ => none)
    («yulAssign» := fun _ _ _ => none)
    («yulExprStmt» := fun _ => none)
    («yulIf» := fun _ _ => none)
    («yulFor» := fun _ _ _ _ => none)
    («yulSwitch» := fun _ _ _ => none)
    («yulCase» := fun _ _ => none)
    («yulLeave» := none)
    («yulBreak» := none)
    («yulContinue» := none)
    («yulFun» := fun _ _ _ _ => none)
    («yulPath» := fun _ _ => none)
    («yulCall» := fun _ _ => none)
    («yulLit» := fun _ => none)

def parts (P : UnitSet) (R : List Remapping) (u : String) (scope : Option DeclId)
    (decl : Decl) : Option (List (TypeKey P) × List (TypeKey P)) :=
  partsSyntax P R u scope decl.kind decl.node

structure Signature (P : UnitSet) where
  owner : Declared P
  kind : DeclKind
  parameters : List (TypeKey P)
  returns : List (TypeKey P)
  deriving DecidableEq, Repr

def normalize (P : UnitSet) (R : List Remapping) (i : DeclId) : Option (Signature P) :=
  match hd : P.decl? i with
  | none => none
  | some decl => do
    let scope ← ownerScope P i decl
    let (ps,rs) ← parts P R i.unit scope decl
    pure ⟨⟨i,decl,hd⟩,decl.kind,ps,rs⟩

/-- Normalization never renumbers or replaces the declaration being compared. -/
theorem preserves_identity {P : UnitSet} {R : List Remapping} {i : DeclId} {s : Signature P}
    (h : normalize P R i = some s) : s.owner.val = i := by
  unfold normalize at h
  split at h
  · cases h
  · rename_i decl hd
    obtain ⟨scope,_,h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨pair,_,h⟩ := Option.bind_eq_some_iff.mp h
    rcases pair with ⟨ps,rs⟩
    cases Option.some.inj h
    rfl

/-- Even equal parameter signatures cannot collapse two declaration identities. -/
theorem normalize_injective {P : UnitSet} {R : List Remapping} {i j : DeclId} {s : Signature P}
    (left : normalize P R i = some s) (right : normalize P R j = some s) : i = j :=
  (preserves_identity left).symm.trans (preserves_identity right)

theorem original_declaration {P : UnitSet} (s : Signature P) : ∃ d, P.decl? s.owner.val = some d :=
  s.owner.property

theorem nominal_identity {P : UnitSet} {kind : DeclKind} (ref : Nominal P kind) :
    ∃ d, P.decl? ref.val = some d ∧ d.kind = kind := ref.property

theorem enumeration_identity {P : UnitSet} {left right : Nominal P .enum}
    (h : TypeKey.enumeration left = TypeKey.enumeration right) : left.val = right.val := by
  cases h
  rfl

/-- Three-way comparison: unresolved declarations are never reported as
successfully distinct signatures. Consumers must propagate `none`. This is
comparison of normalized Source keys; override validity remains G14. -/
def sameParams (P : UnitSet) (R : List Remapping) (a b : DeclId) : Option Bool :=
  match normalize P R a, normalize P R b with
  | some left, some right => some (decide (left.kind = right.kind ∧ left.parameters = right.parameters))
  | _, _ => none

theorem sameParams_true_iff {P : UnitSet} {R : List Remapping} {a b : DeclId} :
    sameParams P R a b = some true ↔
    ∃ left right, normalize P R a = some left ∧ normalize P R b = some right ∧
      left.kind = right.kind ∧ left.parameters = right.parameters := by
  cases hl : normalize P R a <;> cases hr : normalize P R b <;>
    simp only [sameParams,hl,hr,Option.some.injEq,reduceCtorEq,exists_false,
      false_and,and_false,decide_eq_true_eq]
  constructor
  · intro h; exact ⟨_,_,rfl,rfl,h⟩
  · rintro ⟨_,_,rfl,rfl,h⟩; exact h

theorem sameParams_false_iff {P : UnitSet} {R : List Remapping} {a b : DeclId} :
    sameParams P R a b = some false ↔
    ∃ left right, normalize P R a = some left ∧ normalize P R b = some right ∧
      ¬ (left.kind = right.kind ∧ left.parameters = right.parameters) := by
  cases hl : normalize P R a <;> cases hr : normalize P R b <;>
    simp only [sameParams,hl,hr,Option.some.injEq,reduceCtorEq,exists_false,
      false_and,and_false,decide_eq_false_iff_not]
  constructor
  · intro h; exact ⟨_,_,rfl,rfl,h⟩
  · rintro ⟨_,_,rfl,rfl,h⟩; exact h

theorem sameParams_none_iff {P : UnitSet} {R : List Remapping} {a b : DeclId} :
    sameParams P R a b = none ↔ normalize P R a = none ∨ normalize P R b = none := by
  cases ha : normalize P R a <;> cases hb : normalize P R b <;>
    simp only [sameParams,ha,hb,reduceCtorEq,
      or_true,or_false]

end Solidity.Frontend.QualifiedUnits.SignatureNormalization
