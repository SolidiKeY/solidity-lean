import Solidity.Frontend.QualifiedUnits.SignatureNormalization

/-! Directional signature hiding over identity-bearing normalization keys.
This is candidate collection metadata, not override validity (G14). In
particular, the allowed external-calldata/public-memory override does not
create an additional base candidate. Storage remains distinct. -/
namespace Solidity.Frontend.QualifiedUnits.SignatureHiding
open Solidity.Source SignatureNormalization

/-- External parameter passing identifies memory and calldata, while keeping
storage and function-pointer parameter types distinct. Nominal IDs survive. -/
def externalKey {P : UnitSet} : TypeKey P → TypeKey P
  | .bytes loc => .bytes (if loc = .calldata then .memory else loc)
  | .string loc => .string (if loc = .calldata then .memory else loc)
  | .record loc ref => .record (if loc = .calldata then .memory else loc) ref
  | .array loc elem len => .array (if loc = .calldata then .memory else loc) (externalKey elem) len
  | other => other

theorem externalKey_nominal_identity {P : UnitSet} (key : TypeKey P) :
    (externalKey key).nominalId? = key.nominalId? := by
  cases key <;> rfl

mutual

def nominalIds {P : UnitSet} : TypeKey P → List DeclId
  | .enumeration ref | .valueType ref => [ref.val]
  | .contract ref => [ref.val]
  | .record _ ref => [ref.val]
  | .array _ elem _ => nominalIds elem
  | .mapping key value => nominalIds key ++ nominalIds value
  | .callable _ ps rs _ => nominalIdsList ps ++ nominalIdsList rs
  | _ => []

def nominalIdsList {P : UnitSet} : List (TypeKey P) → List DeclId
  | [] => []
  | key :: rest => nominalIds key ++ nominalIdsList rest

end

/-- All nominal leaves survive, including array elements, mapping values and
nested function-pointer signatures. Multiplicity and order also survive. -/
theorem externalKey_all_nominal_identity {P : UnitSet} : (key : TypeKey P) →
    nominalIds (externalKey key) = nominalIds key
  | .array _ elem _ => externalKey_all_nominal_identity elem
  | .integer _ | .boolean | .address _ | .fixedBytes _ _ | .fixedPoint _ | .bytes _ | .string _
  | .enumeration _ | .valueType _ | .contract _ | .record _ _ | .mapping _ _ | .callable _ _ _ _ => rfl

def externalSyntax (kind : DeclKind) {c : Cat} (s : Syn c) : Bool :=
  Syn.casesOn (motive := fun c (_ : Syn c) => Bool) s
    («nil» := fun {_} => false)
    («cons» := fun {_} _ _ => false)
    («none» := fun {_} => false)
    («some» := fun {_} _ => false)
    («unit» := fun _ => false)
    («pragma» := fun _ => false)
    («importPath» := fun _ _ => false)
    («importSymbols» := fun _ _ _ => false)
    («importStar» := fun _ _ => false)
    («importAlias» := fun _ _ => false)
    («contract» := fun _ _ _ _ _ => false)
    («interface» := fun _ _ _ => false)
    («library» := fun _ _ => false)
    («topPart» := fun _ => false)
    («inherit» := fun _ _ => false)
    («constructor» := fun _ _ _ _ _ => false)
    («function» := fun {_} _ _ a2 _ _ _ _ _ _ => kind == .function && a2 == some .external)
    («modifier» := fun _ _ _ _ _ => false)
    («fallback» := fun _ _ _ _ _ _ _ => false)
    («fbNoParams» := false)
    («fbParams» := fun _ _ _ => false)
    («receive» := fun _ _ _ _ _ _ => false)
    («struct» := fun {_} _ _ _ => false)
    («structMember» := fun _ _ => false)
    («enum» := fun {_} _ _ _ => false)
    («udvt» := fun {_} _ _ => false)
    («stateVar» := fun _ _ _ _ _ _ _ => false)
    («constant» := fun _ _ _ => false)
    («event» := fun {_} _ _ _ => false)
    («eventParam» := fun _ _ _ => false)
    («error» := fun {_} _ _ => false)
    («errorParam» := fun _ _ => false)
    («usingPart» := fun {_} _ => false)
    («usingPath» := fun _ _ _ => false)
    («usingAliases» := fun _ _ _ _ => false)
    («usingAlias» := fun _ _ => false)
    («positional» := fun _ => false)
    («named» := fun _ => false)
    («namedArg» := fun _ _ => false)
    («modInv» := fun _ _ => false)
    («param» := fun _ _ _ => false)
    («elem» := fun _ => false)
    («fnType» := fun _ _ _ _ => false)
    («mapping» := fun _ _ _ _ => false)
    («userType» := fun _ => false)
    («array» := fun _ _ => false)
    («varDecl» := fun _ _ _ => false)
    («index» := fun _ _ => false)
    («slice» := fun _ _ _ => false)
    («member» := fun _ _ => false)
    («callOptions» := fun _ _ _ => false)
    («call» := fun _ _ => false)
    («payableConv» := fun _ => false)
    («metaType» := fun _ => false)
    («unaryPrefix» := fun _ _ => false)
    («unarySuffix» := fun _ _ => false)
    («exp» := fun _ _ => false)
    («mulDivMod» := fun _ _ _ => false)
    («addSub» := fun _ _ _ => false)
    («shift» := fun _ _ _ => false)
    («bitAnd» := fun _ _ => false)
    («bitXor» := fun _ _ => false)
    («bitOr» := fun _ _ => false)
    («order» := fun _ _ _ => false)
    («equality» := fun _ _ _ => false)
    («and» := fun _ _ => false)
    («or» := fun _ _ => false)
    («cond» := fun _ _ _ => false)
    («assign» := fun _ _ _ => false)
    («new» := fun _ => false)
    («tuple» := fun _ _ => false)
    («inlineArray» := fun _ _ => false)
    («ident» := fun _ => false)
    («lit» := fun _ => false)
    («litUnit» := fun _ _ => false)
    («elemType» := fun _ _ => false)
    («declVar» := fun _ _ => false)
    («declTuple» := fun _ _ _ _ => false)
    («exprStmt» := fun _ => false)
    («blockStmt» := fun {_} _ => false)
    («simpleStmt» := fun {_} _ => false)
    («ifStmt» := fun {_} _ _ _ => false)
    («forStmt» := fun {_ _} _ _ _ _ => false)
    («whileStmt» := fun {_ _} _ _ => false)
    («doWhile» := fun {_ _} _ _ => false)
    («continueStmt» := fun {_} => false)
    («breakStmt» := fun {_} => false)
    («tryStmt» := fun {_} _ _ _ _ _ => false)
    («catchPlain» := fun {_} _ => false)
    («catchSig» := fun {_} _ _ _ _ => false)
    («returnStmt» := fun {_} _ => false)
    («emit» := fun {_} _ _ => false)
    («revert» := fun {_} _ _ => false)
    («assembly» := fun {_} _ _ _ => false)
    («block» := fun {_} _ => false)
    («stmtItem» := fun {_} _ => false)
    («uncheckedItem» := fun {_} _ => false)
    («yulBlock» := fun _ => false)
    («yulLet» := fun _ _ _ => false)
    («yulAssign» := fun _ _ _ => false)
    («yulExprStmt» := fun _ => false)
    («yulIf» := fun _ _ => false)
    («yulFor» := fun _ _ _ _ => false)
    («yulSwitch» := fun _ _ _ => false)
    («yulCase» := fun _ _ => false)
    («yulLeave» := false)
    («yulBreak» := false)
    («yulContinue» := false)
    («yulFun» := fun _ _ _ _ => false)
    («yulPath» := fun _ _ => false)
    («yulCall» := fun _ _ => false)
    («yulLit» := fun _ => false)

def isExternal (P : UnitSet) (i : DeclId) : Bool :=
  match P.decl? i with
  | none => false
  | some d => externalSyntax d.kind d.node

/-- `newer` precedes `older` in an independently chosen owner order. The
normalization failure case is explicit and must be propagated by consumers.
Returns are normalized, but do not participate in hiding. -/
def hides (P : UnitSet) (R : List Remapping) (newer older : DeclId) : Option Bool :=
  match normalize P R newer, normalize P R older with
  | some n,some o => some (decide (n.kind = o.kind) &&
      if isExternal P older then decide (n.parameters.map externalKey = o.parameters.map externalKey)
      else decide (n.parameters = o.parameters))
  | _,_ => none

theorem hides_none_iff {P : UnitSet} {R : List Remapping} {newer older : DeclId} :
    hides P R newer older = none ↔ normalize P R newer = none ∨ normalize P R older = none := by
  cases hn : normalize P R newer <;> cases ho : normalize P R older <;>
    simp only [hides,hn,ho,reduceCtorEq,or_true,or_false]

/-- A comparison result has two original declarations, without creating or
replacing either identity. -/
theorem hides_originals {P : UnitSet} {R : List Remapping} {newer older : DeclId} {answer : Bool}
    (h : hides P R newer older = some answer) :
    (∃ d, P.decl? newer = some d) ∧ (∃ d, P.decl? older = some d) := by
  unfold hides at h
  split at h
  · rename_i n o hn ho
    constructor
    · have hi := preserves_identity hn
      rw [← hi]
      exact original_declaration n
    · have hi := preserves_identity ho
      rw [← hi]
      exact original_declaration o
  · cases h

end Solidity.Frontend.QualifiedUnits.SignatureHiding
