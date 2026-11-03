import Solidity.Yul.SourceBindings
import Solidity.Yul.Syntax

/-! Static shape of actual S01 local types, before execution or solc-ID mapping.
This component supplies elementary value encodings and physical-reference
categories. Named enum/UDVT encodings require declaration evidence separately.
Widths describe raw words and NEVER truncate a value on assembly assignment. -/
namespace Solidity.Yul

def sourceWidth (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256) : Fin 32 :=
  ⟨bits / 8 - 1, by omega⟩

theorem sourceWidth_bits (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256) :
    bits = 8 * ((sourceWidth bits valid).val + 1) := by
  dsimp only [sourceWidth]
  omega

theorem sourceWidth_unique (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256)
    (width : Fin 32) (same : bits = 8 * (width.val + 1)) :
    sourceWidth bits valid = width := by
  apply Fin.ext
  dsimp only [sourceWidth]
  omega

def sourceBytesWidth (count : Nat) (valid : 1 ≤ count ∧ count ≤ 32) : Fin 32 :=
  ⟨count - 1, by omega⟩

def integerEncoding (signed : Bool) (width : Fin 32) : Encoding :=
  if signed then .signed width else .unsigned width

/-- Independent exact-width elementary local value classification. -/
inductive SourceScalarD : Solidity.Source.STy → Encoding → Type where
  | int (ty : Solidity.Source.IntTy) (width : Fin 32)
      (bits : ty.bits = 8 * (width.val + 1)) :
      SourceScalarD (.int ty) (integerEncoding ty.signed width)
  | fixed (ty : Solidity.Source.FixTy) (width : Fin 32)
      (bits : ty.bits = 8 * (width.val + 1)) :
      SourceScalarD (.fixed ty) (integerEncoding ty.signed width)
  | bytes (count : Nat) (valid : 1 ≤ count ∧ count ≤ 32) (width : Fin 32)
      (bytes : count = width.val + 1) :
      SourceScalarD (.fixedBytes count valid) (.fixedBytes width)
  | bool : SourceScalarD .bool .boolean
  | address (payable : Bool) : SourceScalarD (.address payable) .address
  | contract (name : Solidity.Source.DeclName) : SourceScalarD (.contract name) .address

def checkSourceScalar (ty : Solidity.Source.STy) :
    Option ((encoding : Encoding) × SourceScalarD ty encoding) :=
  match ty with
  | .int ty => some ⟨integerEncoding ty.signed (sourceWidth ty.bits ty.valid),
      .int ty _ (sourceWidth_bits ty.bits ty.valid)⟩
  | .fixed ty =>
    let valid := ⟨ty.valid.1, ty.valid.2.1, ty.valid.2.2.1⟩
    some ⟨integerEncoding ty.signed (sourceWidth ty.bits valid),
      .fixed ty _ (sourceWidth_bits ty.bits valid)⟩
  | .fixedBytes count valid =>
    let width := sourceBytesWidth count valid
    some ⟨.fixedBytes width, .bytes count valid width (by dsimp only [width, sourceBytesWidth]; omega)⟩
  | .bool => some ⟨.boolean, .bool⟩
  | .address payable => some ⟨.address, .address payable⟩
  | .contract name => some ⟨.address, .contract name⟩
  | _ => none

theorem SourceScalarD.complete {ty encoding} (d : SourceScalarD ty encoding) :
    checkSourceScalar ty = some ⟨encoding, d⟩ := by
  cases d with
  | int ty width bits =>
    have same := sourceWidth_unique ty.bits ty.valid width bits
    cases same
    rfl
  | fixed ty width bits =>
    have same := sourceWidth_unique ty.bits
      ⟨ty.valid.1, ty.valid.2.1, ty.valid.2.2.1⟩ width bits
    cases same
    rfl
  | bytes count valid width bytes =>
    have same : sourceBytesWidth count valid = width := by
      apply Fin.ext
      change count - 1 = width.val
      omega
    cases same
    rfl
  | bool | address _ | contract _ => rfl

theorem checkSourceScalar_iff (ty : Solidity.Source.STy) :
    (checkSourceScalar ty).isSome = true ↔
      ∃ encoding, Nonempty (SourceScalarD ty encoding) := by
  constructor
  · intro h
    cases found : checkSourceScalar ty with
    | none => rw [found] at h; cases h
    | some pair => exact ⟨pair.1, ⟨pair.2⟩⟩
  · rintro ⟨encoding, ⟨d⟩⟩
    rw [d.complete]
    rfl


/-- Reference categories retain physical information for later VY2 semantics;
this relation does not supply any slot/address/layout agreement. -/
inductive SourceReferenceD : Solidity.Source.STy → ExternalType → Type where
  | bytesMemory : SourceReferenceD (.bytes .memory) .memory
  | stringMemory : SourceReferenceD (.string .memory) .memory
  | arrayMemory (elem len) : SourceReferenceD (.array .memory elem len) .memory
  | structMemory (name) : SourceReferenceD (.struct .memory name) .memory
  | bytesCalldata : SourceReferenceD (.bytes .calldata) .calldataDynamic
  | stringCalldata : SourceReferenceD (.string .calldata) .calldataDynamic
  | arrayCalldataDynamic (elem) : SourceReferenceD (.array .calldata elem none) .calldataDynamic
  | arrayCalldataStatic (elem len) : SourceReferenceD (.array .calldata elem (some len)) .calldataStatic
  | structCalldata (name) : SourceReferenceD (.struct .calldata name) .calldataStatic
  | bytesStorage : SourceReferenceD (.bytes .storage) (.storage true false)
  | stringStorage : SourceReferenceD (.string .storage) (.storage true false)
  | arrayStorage (elem len) : SourceReferenceD (.array .storage elem len) (.storage true false)
  | structStorage (name) : SourceReferenceD (.struct .storage name) (.storage true false)
  | mapping (key value) : SourceReferenceD (.mapping key value) (.storage true false)
  | externalFunction (params rets mutability) :
      SourceReferenceD (.fn true params rets mutability) .externalFunction
  | internalFunction (params rets mutability) :
      SourceReferenceD (.fn false params rets mutability) .internalFunction

def checkSourceReference (ty : Solidity.Source.STy) :
    Option ((kind : ExternalType) × SourceReferenceD ty kind) :=
  match ty with
  | .bytes .memory => some ⟨.memory, .bytesMemory⟩
  | .string .memory => some ⟨.memory, .stringMemory⟩
  | .array .memory elem len => some ⟨.memory, .arrayMemory elem len⟩
  | .struct .memory name => some ⟨.memory, .structMemory name⟩
  | .bytes .calldata => some ⟨.calldataDynamic, .bytesCalldata⟩
  | .string .calldata => some ⟨.calldataDynamic, .stringCalldata⟩
  | .array .calldata elem none => some ⟨.calldataDynamic, .arrayCalldataDynamic elem⟩
  | .array .calldata elem (some len) => some ⟨.calldataStatic, .arrayCalldataStatic elem len⟩
  | .struct .calldata name => some ⟨.calldataStatic, .structCalldata name⟩
  | .bytes .storage => some ⟨.storage true false, .bytesStorage⟩
  | .string .storage => some ⟨.storage true false, .stringStorage⟩
  | .array .storage elem len => some ⟨.storage true false, .arrayStorage elem len⟩
  | .struct .storage name => some ⟨.storage true false, .structStorage name⟩
  | .mapping key value => some ⟨.storage true false, .mapping key value⟩
  | .fn true params rets mutability => some ⟨.externalFunction, .externalFunction params rets mutability⟩
  | .fn false params rets mutability => some ⟨.internalFunction, .internalFunction params rets mutability⟩
  | _ => none

theorem SourceReferenceD.complete {ty kind} (d : SourceReferenceD ty kind) :
    checkSourceReference ty = some ⟨kind, d⟩ := by
  cases d <;> rfl

inductive SourceLocalTypeD : Solidity.Source.STy → ExternalType → Type where
  | scalar {ty encoding} : SourceScalarD ty encoding → SourceLocalTypeD ty (.value encoding)
  | reference {ty kind} : SourceReferenceD ty kind → SourceLocalTypeD ty kind

def checkSourceLocalType (ty : Solidity.Source.STy) :
    Option ((kind : ExternalType) × SourceLocalTypeD ty kind) :=
  match checkSourceScalar ty with
  | some ⟨encoding, d⟩ => some ⟨.value encoding, .scalar d⟩
  | none => (checkSourceReference ty).map fun ⟨kind, d⟩ => ⟨kind, .reference d⟩

theorem SourceLocalTypeD.complete {ty kind} (d : SourceLocalTypeD ty kind) :
    checkSourceLocalType ty = some ⟨kind, d⟩ := by
  cases d with
  | scalar scalar =>
    unfold checkSourceLocalType
    rw [scalar.complete]
  | reference reference =>
    cases reference <;> rfl

theorem checkSourceLocalType_iff (ty : Solidity.Source.STy) :
    (checkSourceLocalType ty).isSome = true ↔
      ∃ kind, Nonempty (SourceLocalTypeD ty kind) := by
  constructor
  · intro h
    cases found : checkSourceLocalType ty with
    | none => rw [found] at h; cases h
    | some pair => exact ⟨pair.1, ⟨pair.2⟩⟩
  · rintro ⟨kind, ⟨d⟩⟩
    rw [d.complete]
    rfl

/-- Actual named-type node payloads, observed with a category-generalized
recursor. No Source.Env.layout fallback is used for missing declarations. -/
inductive EnumNodeD : {c : Solidity.Source.Cat} → Solidity.Source.Syn c → Nat → Prop where
  | intro {top name first rest} :
      EnumNodeD (Solidity.Source.Syn.enum (t := top) name first rest) (rest.length + 1)

inductive UdvtNodeD : {c : Solidity.Source.Cat} →
    Solidity.Source.Syn c → Solidity.Source.Elem → Prop where
  | intro {top name elem} :
      UdvtNodeD (Solidity.Source.Syn.udvt (t := top) name elem) elem

def sourceEnumSize {c} (node : Solidity.Source.Syn c) : Option Nat := by
  apply Solidity.Source.Syn.casesOn (motive := fun _ _ => Option Nat) node
  case enum => intro top name first rest; exact some (rest.length + 1)
  all_goals intros; exact none

def sourceUdvtElem {c} (node : Solidity.Source.Syn c) : Option Solidity.Source.Elem := by
  apply Solidity.Source.Syn.casesOn (motive := fun _ _ => Option Solidity.Source.Elem) node
  case udvt => intro top name elem; exact some elem
  all_goals intros; exact none

theorem EnumNodeD.complete {c node size} (d : @EnumNodeD c node size) :
    sourceEnumSize node = some size := by cases d; rfl

theorem UdvtNodeD.complete {c node elem} (d : @UdvtNodeD c node elem) :
    sourceUdvtElem node = some elem := by cases d; rfl

theorem sourceEnumSize_sound {c} (node : Solidity.Source.Syn c) {size}
    (found : sourceEnumSize node = some size) : EnumNodeD node size := by
  cases node <;> first | (cases found; exact .intro) | cases found

theorem sourceUdvtElem_sound {c} (node : Solidity.Source.Syn c) {elem}
    (found : sourceUdvtElem node = some elem) : UdvtNodeD node elem := by
  cases node <;> first | (cases found; exact .intro) | cases found

/-- All local categories, with actual declaration premises for enum/UDVT
representations. This classifies types; Source declaration well-formedness,
solc-ID/source occurrence provenance and execution are separate obligations. -/
inductive DeclaredSourceTypeD (env : Solidity.Source.Env) :
    Solidity.Source.STy → ExternalType → Type where
  | basic {ty kind} : SourceLocalTypeD ty kind → DeclaredSourceTypeD env ty kind
  | enum {name decl size} :
      env.declOf .enum name = some decl → EnumNodeD decl.node size →
      size ≤ 256 → DeclaredSourceTypeD env (.enum name) (.value (.unsigned 0))
  | udvt {name decl elem encoding} :
      env.declOf .udvt name = some decl → UdvtNodeD decl.node elem →
      SourceScalarD (elem.ty .memory) encoding →
      DeclaredSourceTypeD env (.udvt name) (.value encoding)

def checkDeclaredSourceType (env : Solidity.Source.Env) (ty : Solidity.Source.STy) :
    Option ((kind : ExternalType) × DeclaredSourceTypeD env ty kind) :=
  match ty with
  | .enum name =>
    match lookup : env.declOf .enum name with
    | none => none
    | some decl =>
      match node : sourceEnumSize decl.node with
      | none => none
      | some size =>
        if range : size ≤ 256 then
          some ⟨.value (.unsigned 0), .enum lookup (sourceEnumSize_sound decl.node node) range⟩
        else none
  | .udvt name =>
    match lookup : env.declOf .udvt name with
    | none => none
    | some decl =>
      match node : sourceUdvtElem decl.node with
      | none => none
      | some elem =>
        (checkSourceScalar (elem.ty .memory)).map fun ⟨encoding, d⟩ =>
          ⟨.value encoding, .udvt lookup (sourceUdvtElem_sound decl.node node) d⟩
  | other => (checkSourceLocalType other).map fun ⟨kind, d⟩ => ⟨kind, .basic d⟩

theorem DeclaredSourceTypeD.complete {env ty kind} (d : DeclaredSourceTypeD env ty kind) :
    checkDeclaredSourceType env ty = some ⟨kind, d⟩ := by
  cases d with
  | basic basic =>
    have base : checkDeclaredSourceType env ty =
        (checkSourceLocalType ty).map (fun ⟨kind, d⟩ =>
          (⟨kind, DeclaredSourceTypeD.basic d⟩ :
            (kind : ExternalType) × DeclaredSourceTypeD env ty kind)) := by
      cases basic with
      | scalar scalar => cases scalar <;> rfl
      | reference reference => cases reference <;> rfl
    rw [base, basic.complete]
    rfl
  | @enum name decl size lookup node range =>
    dsimp only [checkDeclaredSourceType]
    split
    · next absent => rw [lookup] at absent; cases absent
    · next actual found =>
      have same := Option.some.inj (found.symm.trans lookup)
      cases same
      split
      · next absent => rw [node.complete] at absent; cases absent
      · next actualSize foundSize =>
        have same := Option.some.inj (foundSize.symm.trans node.complete)
        cases same
        rw [dif_pos range]
  | @udvt name decl elem encoding lookup node scalar =>
    dsimp only [checkDeclaredSourceType]
    split
    · next absent => rw [lookup] at absent; cases absent
    · next actual found =>
      have same := Option.some.inj (found.symm.trans lookup)
      cases same
      split
      · next absent => rw [node.complete] at absent; cases absent
      · next actualElem foundElem =>
        have same := Option.some.inj (foundElem.symm.trans node.complete)
        cases same
        rw [scalar.complete]
        rfl

theorem checkDeclaredSourceType_iff (env : Solidity.Source.Env) (ty : Solidity.Source.STy) :
    (checkDeclaredSourceType env ty).isSome = true ↔
      ∃ kind, Nonempty (DeclaredSourceTypeD env ty kind) := by
  constructor
  · intro h
    cases found : checkDeclaredSourceType env ty with
    | none => rw [found] at h; cases h
    | some pair => exact ⟨pair.1, ⟨pair.2⟩⟩
  · rintro ⟨kind, ⟨d⟩⟩
    rw [d.complete]
    rfl

/-- Concrete identity plus classification; it retains both original Source type
and original typed local handle. No solc-ID is inferred from the name. -/
structure ClassifiedSourceLocal (ctx : Solidity.Source.Ctx) (name : String) where
  ref : SourceLocalRef ctx
  identity : SourceLocalD ctx name ref
  kind : ExternalType
  shape : DeclaredSourceTypeD ctx.env ref.ty kind

def checkClassifiedSourceLocal (ctx : Solidity.Source.Ctx) (name : String) :
    Option (ClassifiedSourceLocal ctx name) := do
  let ⟨ref, identity⟩ ← checkSourceLocal ctx name
  let ⟨kind, shape⟩ ← checkDeclaredSourceType ctx.env ref.ty
  pure ⟨ref, identity, kind, shape⟩

theorem ClassifiedSourceLocal.complete {ctx name} (d : ClassifiedSourceLocal ctx name) :
    checkClassifiedSourceLocal ctx name = some d := by
  rcases d with ⟨ref, identity, kind, shape⟩
  unfold checkClassifiedSourceLocal
  rw [identity.complete]
  change (checkDeclaredSourceType ctx.env ref.ty).bind _ = _
  rw [shape.complete]
  rfl



/-- Refuse the selected oversized declaration without retrying a later one.
These are actual declaration/node premises, not a check-success assumption. -/
theorem checkDeclaredSourceType_enum_large (env : Solidity.Source.Env)
    (name : Solidity.Source.DeclName) (decl : Solidity.Source.Decl) (size : Nat)
    (lookup : env.declOf .enum name = some decl) (node : EnumNodeD decl.node size)
    (large : 256 < size) :
    checkDeclaredSourceType env (.enum name) = none := by
  dsimp only [checkDeclaredSourceType]
  split
  · rfl
  · next actual found =>
    have same := Option.some.inj (found.symm.trans lookup)
    cases same
    split
    · rfl
    · next actualSize foundSize =>
      have same := Option.some.inj (foundSize.symm.trans node.complete)
      cases same
      rw [dif_neg (by omega)]


theorem checkClassifiedSourceLocal_iff (ctx : Solidity.Source.Ctx) (name : String) :
    (checkClassifiedSourceLocal ctx name).isSome = true ↔
      Nonempty (ClassifiedSourceLocal ctx name) := by
  constructor
  · intro h
    cases found : checkClassifiedSourceLocal ctx name with
    | none => rw [found] at h; cases h
    | some d => exact ⟨d⟩
  · rintro ⟨d⟩
    rw [d.complete]
    rfl

theorem DeclaredSourceTypeD.unique {env ty first second}
    (one : DeclaredSourceTypeD env ty first) (two : DeclaredSourceTypeD env ty second) :
    first = second :=
  congrArg (fun pair => pair.1) (Option.some.inj (one.complete.symm.trans two.complete))

end Solidity.Yul
