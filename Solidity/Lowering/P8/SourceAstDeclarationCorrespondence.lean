import Solidity.Lowering.P8.SourceAstTryCorrespondence

/-! Struct and using-directive structural correspondence.
Regression purpose: retain member names/types/order and using-library/type/global
syntax. These laws are not Source validity, name resolution or artifact binding. -/
namespace Solidity.Lowering.P8.SourceAstDeclarationCorrespondence
open Lean Solidity.Source
open SourceAstParameters SourceAstCorrespondence SourceAstExpressionCorrespondence

theorem member_exact (fuel : Nat) (node rawType : Json) (ty : Syn .typeName) (name : String)
    (kind : node.getObjValAs? String "nodeType" = .ok "VariableDeclaration")
    (typeField : node.getObjVal? "typeName" = .ok rawType)
    (typeValue : SourceAstCompoundTypes.typeName fuel rawType = .ok ty)
    (nameField : node.getObjValAs? String "name" = .ok name) :
    SourceAstUnit.structMember fuel node = .ok (.structMember ty name) := by
  unfold SourceAstUnit.structMember
  simp only [kind, typeField, typeValue, nameField, ok_bind, beq_self_eq_true, ite_true, pure_bind]
  rfl

theorem struct_ok_iff_each (fuel : Nat) (node : Json) (children : Array Json)
    (name : String) (out : Syn (.part false))
    (kind : node.getObjValAs? String "nodeType" = .ok "StructDefinition")
    (fields : node.getObjValAs? (Array Json) "members" = .ok children)
    (nameField : node.getObjValAs? String "name" = .ok name) :
    SourceAstUnit.part fuel node = .ok out ↔
      ∃ head tail, Each (fun child member => SourceAstUnit.structMember fuel child = .ok member)
        children.toList (head :: tail) ∧ out = .struct name head (syntaxList tail) := by
  rw [SourceAstUnit.part]
  simp only [kind, fields, nameField, ok_bind]
  have law := nonempty_build_ok_iff_each (SourceAstUnit.structMember fuel)
    (fun (head : Syn .structMember) (tail : List (Syn .structMember)) =>
      (Syn.struct name head (syntaxList tail) : Syn (.part false)))
    "nonempty struct required" children.toList out
  cases converted : children.toList.mapM (SourceAstUnit.structMember fuel) with
  | error message => simpa only [converted] using law
  | ok values => cases values <;> simpa only [converted] using law

theorem using_path_exact (fuel : Nat) (node library rawType : Json) (lib : IdPath)
    (name : String) (ty : Syn (.opt .typeName)) (global : Bool)
    (kind : node.getObjValAs? String "nodeType" = .ok "UsingForDirective")
    (functions : SourceAstUnit.absentOrEmpty node "functionList" = .ok ())
    (libraryField : node.getObjVal? "libraryName" = .ok library)
    (libraryKind : library.getObjValAs? String "nodeType" = .ok "IdentifierPath")
    (nameField : library.getObjValAs? String "name" = .ok name)
    (pathValue : SourceAstTypes.path name = .ok lib)
    (typeField : node.getObjVal? "typeName" = .ok rawType)
    (typeValue : (match rawType with
      | .null => (Except.ok Syn.none : Except String (Syn (.opt .typeName)))
      | _ => (SourceAstCompoundTypes.typeName fuel rawType).map Syn.some) = .ok ty)
    (globalField : node.getObjValAs? Bool "global" = .ok global) :
    SourceAstUnit.part fuel node = .ok (.usingPart (.usingPath lib ty global)) := by
  cases rawType
  case null =>
    change Except.ok Syn.none = Except.ok ty at typeValue
    cases typeValue
    rw [SourceAstUnit.part]
    simp only [kind, functions, libraryField, libraryKind, nameField, pathValue,
      typeField, globalField, ok_bind, beq_self_eq_true, ite_true, pure_bind]
    rfl
  all_goals
    simp only [] at typeValue
    rw [SourceAstUnit.part]
    simp only [kind, functions, libraryField, libraryKind, nameField, pathValue,
      typeField, typeValue, globalField, ok_bind, beq_self_eq_true, ite_true, pure_bind]
    rfl

/-- info: 'Solidity.Lowering.P8.SourceAstDeclarationCorrespondence.member_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms member_exact
/-- info: 'Solidity.Lowering.P8.SourceAstDeclarationCorrespondence.struct_ok_iff_each' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms struct_ok_iff_each
/-- info: 'Solidity.Lowering.P8.SourceAstDeclarationCorrespondence.using_path_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms using_path_exact
end Solidity.Lowering.P8.SourceAstDeclarationCorrespondence
