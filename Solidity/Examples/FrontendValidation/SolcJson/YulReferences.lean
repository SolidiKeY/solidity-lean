import Solidity.Frontend.SolcJson.YulBuiltinUse
import Solidity.Frontend.SolcJson.YulAttachedUse

/-! Literal identity, capability and actual-occurrence controls. These certify
structural attachment relative to supplied bindings, not source provenance. -/
namespace Solidity.Examples.FrontendValidation.SolcJson.YulReferences
open Lean Solidity.Frontend.YulJson

private def declaration : Declaration [.value .boolean] :=
  ⟨1, "v", .value .boolean, .here⟩
private def table : DeclarationTable [.value .boolean] := ⟨[declaration], by decide⟩
private def original : Names.Original := [("v", some 1)]
private def refNode : Json := Json.mkObj [
  ("declaration", toJson (1 : Nat)), ("src", .str "0:1:0"),
  ("isSlot", .bool false), ("isOffset", .bool false), ("valueSize", toJson (1 : Nat))]
private def identifierNode : Json := Json.mkObj [
  ("nodeType", .str "YulIdentifier"), ("name", .str "v"), ("src", .str "0:1:0")]
private def wrongSpan : Json := identifierNode.setObjVal! "src" (.str "1:1:0")
private def emptyBlock : Json := Json.mkObj [
  ("nodeType", .str "YulBlock"), ("statements", .arr #[])]
private def importedRef : Option (Reference table) := (reference table refNode).toOption

#guard (identify [declaration] 1).isSome
#guard (identify [declaration] 2).isNone
#guard (checkDeclarationTable [declaration]).isSome
#guard (checkDeclarationTable [declaration, declaration]).isNone
#guard (reference table refNode).isOk
#guard (reference table (refNode.setObjVal! "declaration" (toJson (2 : Nat)))).toOption.isNone
#guard (Names.select table original "v").isSome
#guard (Names.select table [("v", none)] "v").isNone
#guard (Names.entry? table original "v").isSome
#guard (Names.entry? table [("v", some 2)] "v").isNone
#guard (importedRef.map fun ref =>
  (Names.checkReference table original "v" ref).isSome) == some true
#guard (importedRef.map fun ref =>
  (Names.checkReference table [("v", none)] "v" ref).isSome) == some false
#guard (MetadataWords.input? table original).isSome
#guard (MetadataWords.input? table [("v.x", some 1)]).isNone

#guard Occurrences.isIdentifier identifierNode
#guard !Occurrences.isIdentifier emptyBlock
#guard Occurrences.includeField emptyBlock "statements"
#guard !Occurrences.includeField emptyBlock "name"
#guard (Occurrences.collect 8 identifierNode false).isOk
#guard (Occurrences.collect 0 identifierNode false).toOption.isNone
private def children : List (Occurrences.Child (.arr #[identifierNode]) false) :=
  (Occurrences.arrayChildren #[identifierNode] false).entries
#guard (Occurrences.checkChildren (fun child =>
  Occurrences.collect 8 child.node child.role) children).isOk
#guard (Occurrences.checkChildren (fun child =>
  Occurrences.collect 0 child.node child.role) children).toOption.isNone

#guard (importedRef.map fun ref =>
  (ReferenceAttachment.check table original false identifierNode ref).isOk) == some true
#guard (importedRef.map fun ref =>
  (ReferenceAttachment.check table original false wrongSpan ref).isOk) == some false

private def attachedUse (locals : List (String × Fin 1)) : Option Bool := do
  let ref ← importedRef
  let attached ← (ReferenceAttachment.check table original false identifierNode ref).toOption
  pure (ReferenceAttachment.checkUse attached .root locals).isSome
#guard attachedUse [] == some true
#guard attachedUse [("v", 0)] == some false

private def candidateAt (node : Json) : Option Bool := do
  let ref ← importedRef
  let collected ← (Occurrences.collect 8 node false).toOption
  let occurrence ← collected.occurrences.head?
  pure (ReferenceCover.candidate (original := original) ref occurrence).isSome
#guard candidateAt identifierNode == some true
#guard candidateAt wrongSpan == some false

private def covered (node : Json) : Option Bool := do
  let ref ← importedRef
  let collected ← (Occurrences.collect 8 node false).toOption
  pure (ReferenceCover.check (original := original) collected ref).isOk
#guard covered identifierNode == some true
#guard covered emptyBlock == some false

private def coveredAll (node : Json) : Option Bool := do
  let ref ← importedRef
  let collected ← (Occurrences.collect 8 node false).toOption
  pure (ReferenceCover.checkAll (original := original) collected [ref]).isOk
#guard coveredAll identifierNode == some true
#guard coveredAll emptyBlock == some false

end Solidity.Examples.FrontendValidation.SolcJson.YulReferences
