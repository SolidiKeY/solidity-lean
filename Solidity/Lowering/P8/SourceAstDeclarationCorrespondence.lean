import Solidity.Lowering.P8.SourceAstTryCorrespondence

/-! Declaration structural correspondence.
Regression purpose: retain member names/types/order and using-library/type/global
syntax, state initializers and function signatures/bodies. These laws are not Source validity, name resolution or artifact binding. -/
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

/-- Preserve the supported mutable state declaration without discarding its initializer. -/
theorem state_exact (fuel : Nat) (node rawType : Json) (ty : Syn .typeName)
    (visibility : String) (vis : Option StateVis) (name : String) (transient : Bool)
    (value : Syn (.opt .expr))
    (kind : node.getObjValAs? String "nodeType" = .ok "VariableDeclaration")
    (state : node.getObjValAs? Bool "stateVariable" = .ok true)
    (constant : node.getObjValAs? Bool "constant" = .ok false)
    (mutable : node.getObjValAs? String "mutability" = .ok "mutable")
    (location : node.getObjValAs? String "storageLocation" = .ok "default")
    (overrides : SourceAstUnit.absentOrEmpty node "overrides" = .ok ())
    (typeField : node.getObjVal? "typeName" = .ok rawType)
    (typeValue : SourceAstCompoundTypes.typeName fuel rawType = .ok ty)
    (visField : node.getObjValAs? String "visibility" = .ok visibility)
    (visValue : SourceAstUnit.stateVisibility visibility = .ok vis)
    (transientField : SourceAstUnit.optionalBool node "transient" = .ok transient)
    (nameField : node.getObjValAs? String "name" = .ok name)
    (initializer : SourceAstUnit.optionalExprField fuel node "value" = .ok value) :
    SourceAstUnit.part fuel node = .ok (.stateVar ty vis none none transient name value) := by
  rw [SourceAstUnit.part]
  simp only [kind, state, constant, mutable, location, overrides, typeField, typeValue,
    visField, visValue, transientField, nameField, initializer, ok_bind,
    beq_self_eq_true, Bool.not_false, Bool.and_true, ite_true, pure_bind]
  rfl

/-- Preserve function signatures and the optional original body under exact child conversions. -/
theorem function_exact (fuel : Nat) (node rawArgs rawResults rawBody : Json)
    (args results : Syn (.list .param)) (body : Syn (.opt (.block .body)))
    (name visibility mutability : String) (vis : Option Visibility)
    (mutabilityValue : Option Mutability) (virtual : Bool)
    (kind : node.getObjValAs? String "nodeType" = .ok "FunctionDefinition")
    (functionKind : node.getObjValAs? String "kind" = .ok "function")
    (modifiers : SourceAstUnit.absentOrEmpty node "modifiers" = .ok ())
    (overrides : SourceAstUnit.absentOrEmpty node "overrides" = .ok ())
    (argsField : node.getObjVal? "parameters" = .ok rawArgs)
    (argsValue : SourceAstCompoundTypes.parametersWith (SourceAstCompoundTypes.typeName fuel)
      rawArgs = .ok args)
    (resultsField : node.getObjVal? "returnParameters" = .ok rawResults)
    (resultsValue : SourceAstCompoundTypes.parametersWith (SourceAstCompoundTypes.typeName fuel)
      rawResults = .ok results)
    (bodyField : node.getObjVal? "body" = .ok rawBody)
    (bodyValue : (match rawBody with
      | .null => (Except.ok Syn.none : Except String (Syn (.opt (.block .body))))
      | _ => (SourceAstStatements.block fuel rawBody).map Syn.some) = .ok body)
    (nameField : node.getObjValAs? String "name" = .ok name)
    (visField : node.getObjValAs? String "visibility" = .ok visibility)
    (visValue : SourceAstUnit.functionVisibility visibility = .ok vis)
    (mutField : node.getObjValAs? String "stateMutability" = .ok mutability)
    (mutValue : SourceAstCompoundTypes.mutability mutability = .ok mutabilityValue)
    (virtualField : SourceAstUnit.optionalBool node "virtual" = .ok virtual) :
    SourceAstUnit.part fuel node =
      .ok (.function (.ident name) args vis mutabilityValue .nil virtual none results body) := by
  cases rawBody
  case null =>
    change Except.ok Syn.none = Except.ok body at bodyValue
    cases bodyValue
    rw [SourceAstUnit.part]
    simp only [kind, functionKind, modifiers, overrides, argsField, argsValue,
      resultsField, resultsValue, bodyField, nameField, visField, visValue, mutField,
      mutValue, virtualField, ok_bind, beq_self_eq_true, ite_true, pure_bind]
    rfl
  all_goals
    simp only [] at bodyValue
    rw [SourceAstUnit.part]
    simp only [kind, functionKind, modifiers, overrides, argsField, argsValue,
      resultsField, resultsValue, bodyField, bodyValue, nameField, visField, visValue,
      mutField, mutValue, virtualField, ok_bind, beq_self_eq_true, ite_true, pure_bind]
    rfl

/-- A failed top-level traversal is not turned into a successful shortened unit. -/
theorem unit_children_failure (fuel : Nat) (node : Json) (children : Array Json)
    (message : String)
    (kind : node.getObjValAs? String "nodeType" = .ok "SourceUnit")
    (fields : node.getObjValAs? (Array Json) "nodes" = .ok children)
    (failed : children.toList.mapM (SourceAstUnit.top fuel) = .error message) :
    SourceAstUnit.unit fuel node = .error message := by
  rw [SourceAstUnit.unit]
  simp only [kind, fields, failed, ok_bind, beq_self_eq_true, ite_true, pure_bind]
  rfl

/-- First-child failure retains its diagnostic without any tail conversion premise. -/
theorem unit_head_failure (fuel : Nat) (node head : Json) (tail : List Json)
    (children : Array Json) (message : String)
    (kind : node.getObjValAs? String "nodeType" = .ok "SourceUnit")
    (fields : node.getObjValAs? (Array Json) "nodes" = .ok children)
    (order : children.toList = head :: tail)
    (failed : SourceAstUnit.top fuel head = .error message) :
    SourceAstUnit.unit fuel node = .error message := by
  apply unit_children_failure fuel node children message kind fields
  rw [order]
  exact mapM_head_failure (SourceAstUnit.top fuel) head tail message failed

/-- Whole-unit traversal failure identifies the first failing top-level child. -/
theorem unit_first_failure (fuel : Nat) (node : Json) (children : Array Json)
    (message : String)
    (kind : node.getObjValAs? String "nodeType" = .ok "SourceUnit")
    (fields : node.getObjValAs? (Array Json) "nodes" = .ok children)
    (failed : SourceAstUnit.unit fuel node = .error message) :
    ∃ before values child tail, children.toList = before ++ child :: tail ∧
      Each (fun x y => SourceAstUnit.top fuel x = .ok y) before values ∧
      SourceAstUnit.top fuel child = .error message := by
  rw [SourceAstUnit.unit] at failed
  simp only [kind, fields, ok_bind, beq_self_eq_true, ite_true, pure_bind] at failed
  cases traversal : children.toList.mapM (SourceAstUnit.top fuel) with
  | error actual =>
    rw [traversal] at failed
    change Except.error actual = Except.error message at failed
    cases failed
    exact (mapM_error_iff_first (SourceAstUnit.top fuel) children.toList message).mp traversal
  | ok values =>
    rw [traversal] at failed
    cases failed

/-- info: 'Solidity.Lowering.P8.SourceAstDeclarationCorrespondence.state_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms state_exact
/-- info: 'Solidity.Lowering.P8.SourceAstDeclarationCorrespondence.function_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms function_exact

/-- Preserve literal pragma tokens without interpreting compiler acceptance. -/
theorem pragma_exact (fuel : Nat) (node : Json) (tokens : List String)
    (kind : node.getObjValAs? String "nodeType" = .ok "PragmaDirective")
    (literals : node.getObjValAs? (List String) "literals" = .ok tokens) :
    SourceAstUnit.top fuel node = .ok (.pragma tokens) := by
  rw [SourceAstUnit.top]
  simp only [kind, literals, ok_bind]
  rfl

/-- Successful containers retain every child, with the original kind/abstract checks. -/
theorem top_ok_iff_each (fuel : Nat) (node : Json) (children : Array Json)
    (name category : String) (abstract : Bool) (out : Syn .top)
    (kind : node.getObjValAs? String "nodeType" = .ok "ContractDefinition")
    (bases : SourceAstUnit.absentOrEmpty node "baseContracts" = .ok ())
    (layout : SourceAstUnit.absentOrEmpty node "storageLayout" = .ok ())
    (nameField : node.getObjValAs? String "name" = .ok name)
    (fields : node.getObjValAs? (Array Json) "nodes" = .ok children)
    (abstractField : SourceAstUnit.optionalBool node "abstract" = .ok abstract)
    (categoryField : node.getObjValAs? String "contractKind" = .ok category) :
    SourceAstUnit.top fuel node = .ok out ↔
      ∃ parts, Each (fun child part => SourceAstUnit.part fuel child = .ok part)
        children.toList parts ∧
        (match (generalizing := false) category with
          | "library" => do
              unless !abstract do throw "abstract library is not syntax"
              pure (Syn.library name (syntaxList parts))
          | "contract" => pure (Syn.contract abstract name .none .nil (syntaxList parts))
          | "interface" => pure (Syn.interface name .nil (syntaxList parts))
          | _ => throw "contract kind required") = (Except.ok out : Except String (Syn .top)) := by
  rw [SourceAstUnit.top]
  simp only [kind, bases, layout, nameField, fields, abstractField, categoryField, ok_bind]
  simpa only using bind_ok_iff_each (SourceAstUnit.part fuel)
    (fun parts => match (generalizing := false) category with
      | "library" => do
          unless !abstract do throw "abstract library is not syntax"
          pure (Syn.library name (syntaxList parts))
      | "contract" => pure (Syn.contract abstract name .none .nil (syntaxList parts))
      | "interface" => pure (Syn.interface name .nil (syntaxList parts))
      | _ => throw "contract kind required") children.toList out

/-- info: 'Solidity.Lowering.P8.SourceAstDeclarationCorrespondence.pragma_exact' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms pragma_exact
/-- info: 'Solidity.Lowering.P8.SourceAstDeclarationCorrespondence.top_ok_iff_each' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms top_ok_iff_each

/-- info: 'Solidity.Lowering.P8.SourceAstDeclarationCorrespondence.member_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms member_exact
/-- info: 'Solidity.Lowering.P8.SourceAstDeclarationCorrespondence.struct_ok_iff_each' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms struct_ok_iff_each
/-- info: 'Solidity.Lowering.P8.SourceAstDeclarationCorrespondence.using_path_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms using_path_exact
/-- info: 'Solidity.Lowering.P8.SourceAstDeclarationCorrespondence.unit_children_failure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms unit_children_failure
/-- info: 'Solidity.Lowering.P8.SourceAstDeclarationCorrespondence.unit_head_failure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms unit_head_failure
/-- info: 'Solidity.Lowering.P8.SourceAstDeclarationCorrespondence.unit_first_failure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms unit_first_failure
end Solidity.Lowering.P8.SourceAstDeclarationCorrespondence
