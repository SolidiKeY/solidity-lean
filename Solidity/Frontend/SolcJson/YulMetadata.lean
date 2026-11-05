
import Solidity.Frontend.SolcJson.Yul
import Solidity.Yul.ExternalCheck

/-! Intrinsic declaration-identity and source-span metadata ingress. The provider
must still connect these identities/types/names to the Solidity declaration
checker. Parsing metadata does not certify source occurrences, safety or admission. -/
namespace Solidity.Frontend.YulJson
open Lean (Json)
open Solidity.Yul

structure Declaration (X : List ExternalType) where
  id : Nat
  name : String
  ty : ExternalType
  index : Member X ty

/-- Independent identity lookup, with no fallback after a matching declaration. -/
inductive IdentityD {X} : List (Declaration X) → Nat → Declaration X → Prop where
  | head {d rest id} : id = d.id → IdentityD (d :: rest) id d
  | tail {d rest id result} : id ≠ d.id → IdentityD rest id result →
      IdentityD (d :: rest) id result

def identify {X} : (entries : List (Declaration X)) → (id : Nat) →
    Option {d : Declaration X // IdentityD entries id d}
  | [], _ => none
  | d :: rest, id =>
    if h : id = d.id then some ⟨d, .head h⟩
    else match identify rest id with
      | none => none
      | some ⟨result, proof⟩ => some ⟨result, .tail h proof⟩

theorem IdentityD.complete {X entries id result}
    (d : @IdentityD X entries id result) : identify entries id = some ⟨result, d⟩ := by
  induction d with
  | head h => simp only [identify, dif_pos h]
  | tail h _ ih => simp only [identify, dif_neg h, ih]

theorem IdentityD.id_eq {X entries id result} (d : @IdentityD X entries id result) :
    id = result.id := by
  induction d with
  | head h => exact h
  | tail _ _ ih => exact ih

/-- Uniqueness is checked; actual source provenance is an input obligation. -/
structure DeclarationTable (X : List ExternalType) where
  entries : List (Declaration X)
  unique : (entries.map Declaration.id).Nodup

def checkDeclarationTable {X} (entries : List (Declaration X)) : Option (DeclarationTable X) :=
  if h : (entries.map Declaration.id).Nodup then some ⟨entries, h⟩ else none

structure SourceSpan where
  start : Nat
  length : Nat
  file : Int
  deriving Repr, DecidableEq

def decimal (s : String) : Option Nat :=
  if !s.isEmpty && s.toUTF8.data.all (fun b => 48 ≤ b && b ≤ 57) then s.toNat? else none

def sourceSpan (s : String) : Except Error SourceSpan := do
  let [start, length, file] := s.splitOn ":" | throw (.field "src")
  let some start := decimal start | throw (.field "src")
  let some length := decimal length | throw (.field "src")
  let file ← if file = "-1" then pure (-1 : Int) else
    match decimal file with
    | some n => pure (Int.ofNat n)
    | none => throw (.field "src")
  pure ⟨start, length, file⟩

def natural (j : Json) (key : String) : Except Error Nat :=
  (j.getObjValAs? Nat key).mapError (fun _ => .field key)

def boolean (j : Json) (key : String) : Except Error Bool :=
  (j.getObjValAs? Bool key).mapError (fun _ => .field key)

/-- Read capability is retained. Assignment occurrence checking must separately
construct the write capability and match the occurrence's exact source span. -/
structure Reference {X} (table : DeclarationTable X) where
  declarationId : Nat
  declaration : Declaration X
  identified : IdentityD table.entries declarationId declaration
  source : SourceSpan
  suffix : List String
  attr : Attribute
  spelled : SuffixD suffix attr
  access : Access declaration.ty attr false

def Reference.term {X table} (r : @Reference X table) : ExternalRef X false :=
  ⟨r.declaration.index, r.attr, r.access⟩

def reference {X} (table : DeclarationTable X) (j : Json) : Except Error (Reference table) := do
  let id ← natural j "declaration"
  let some ⟨decl, identified⟩ := identify table.entries id | throw (.field "declaration identity")
  let src ← sourceSpan (← string j "src")
  let suffix ← match j.getObjVal? "suffix" with
    | .error _ => pure []
    | .ok value => match value.getStr? with
      | .ok s => pure [s]
      | .error _ => throw (.field "suffix")
  let checked : Except Error {a : Attribute // SuffixD suffix a} :=
    match hs : checkSuffix suffix with
    | none => .error (.field "suffix")
    | some attr => .ok ⟨attr, checkSuffix_sound hs⟩
  let ⟨attr, spelled⟩ ← checked
  let slot ← boolean j "isSlot"
  let offset ← boolean j "isOffset"
  if slot != decide (attr = .slot) then throw (.field "isSlot/suffix mismatch")
  if offset != decide (attr = .offset) then throw (.field "isOffset/suffix mismatch")
  if (← natural j "valueSize") != 1 then throw (.field "valueSize")
  let some cap := checkAccess decl.ty attr false | throw (.field "external capability")
  pure ⟨id, decl, identified, src, suffix, attr, spelled, cap⟩

structure References {X} (table : DeclarationTable X) where
  entries : List (Reference table)
  unique : (entries.map Reference.source).Nodup

def references {X} (table : DeclarationTable X) (j : Json) : Except Error (References table) := do
  let entries ← ((← array j "externalReferences").toList).mapM (reference table)
  if h : (entries.map Reference.source).Nodup then pure ⟨entries, h⟩
  else throw (.field "duplicate external source span")

/-- Exact field import only. Unknown flags are retained (solc warns); duplicate
memory-safe flags are an error. Documentation is retained without interpreting
NatSpec, so this record does not establish the memory-safe admission premise. -/
structure Metadata {X} (table : DeclarationTable X) where
  references : References table
  flags : List String
  documentation : Option String

def metadata {X} (table : DeclarationTable X) (j : Json) : Except Error (Metadata table) := do
  requireNode j "InlineAssembly"
  if (← string j "evmVersion") != "osaka" then throw (.field "evmVersion")
  let refs ← references table j
  let flags ← match j.getObjVal? "flags" with
    | .error _ => pure []
    | .ok value => do
      let values ← value.getArr?.mapError (fun _ => .field "flags")
      values.toList.mapM (fun value => value.getStr?.mapError (fun _ => .field "flags"))
  if (flags.filter (· == "memory-safe")).length > 1 then
    throw (.field "duplicate memory-safe flag")
  let documentation ← match j.getObjVal? "documentation" with
    | .error _ => pure none
    | .ok value => do
      let s ← value.getStr?.mapError (fun _ => .field "documentation")
      pure (some s)
  pure ⟨refs, flags, documentation⟩

end Solidity.Frontend.YulJson
