import Solidity.Yul.Views.InheritedDeclarationControls

namespace Solidity.Yul.Views.Controls

theorem diamond_private_base_included :
    diamondName "a" ∈ inheritedRootNames diamondEnv diamondHierarchy.order false ∧
    diamondEnv.lookup (some "D") "a" = [] := ⟨by decide,rfl⟩

theorem diamond_qualified_roots :
    (diamondDeclTypes.map Prod.fst).map Source.DeclName.scope =
      [some "A",some "B",some "C",some "C",some "D",some "D",some "D"] := rfl

theorem diamond_actual_bank (c : ScalarPath diamondEnv.layout (diamondEnv.lay account))
    (member : c ∈ diamondRegistry account) : diamondEnv.transientRoot c.path = false :=
  diamondChecked.bank_agreement c member

theorem diamond_actual_transient_bank (c : ScalarPath diamondEnv.layout (diamondEnv.lay account))
    (member : c ∈ diamondTempRegistry account) : diamondEnv.transientRoot c.path = true :=
  diamondTempChecked.bank_agreement c member

def diamondWrongOrder : RootDeclarations diamondEnv
    [(diamondName "b",.int diamondU248),(diamondName "a",.int diamondU8),(diamondName "c",.bool),
     (diamondName "items",diamondItemsTy),(diamondName "e",.int diamondU248),
     (diamondName "f",.int unsigned16),(diamondName "marker",.int .u256)] :=
  .cons (.scalar (.int diamondU248) (by decide)) (.cons (.scalar (.int diamondU8) (by decide))
    (.cons (.scalar .bool (by decide)) (.cons diamondItems (.cons (.scalar (.int diamondU248) (by decide))
      (.cons (.scalar (.int unsigned16) (by decide)) (.cons (.scalar (.int .u256) (by decide)) .nil))))))

theorem diamond_wrong_order : (prepareInheritedDeclarations diamondWrongOrder "D" false account 0).toOption.isNone := by decide

theorem diamond_wrong_bank : (prepareInheritedDeclarations diamondDeclarations "D" true account 0).toOption.isNone := by decide

def diamondMissingAncestor : Source.Env := ⟨diamondEnv.decls.filter (fun d => d.name != "A")⟩
theorem diamond_missing_ancestor : prepareStorageHierarchy diamondMissingAncestor "D" = .error .invalidBases := rfl

theorem diamond_unknown_active : prepareStorageHierarchy diamondEnv "Missing" = .error .malformedLineage := rfl

def diamondDuplicateContract : Source.Env := ⟨diamondEnv.decls ++ [⟨.contract,"A",none,true,.contract false "A" .none .nil .nil⟩]⟩
theorem diamond_duplicate_contract : prepareStorageHierarchy diamondDuplicateContract "D" = .error .duplicateContracts := rfl

def diamondMalformedAncestor : Source.Env := ⟨diamondEnv.decls.map (fun d => if d.name = "A" then
  ⟨.contract,"A",none,true,.library "A" .nil⟩ else d)⟩
theorem diamond_malformed_ancestor : prepareStorageHierarchy diamondMalformedAncestor "D" = .error .malformedLineage := rfl

/-- Same spelling in a DIFFERENT base scope is a different source identity.
It cannot silently replace an existing qualified field in the complete inventory. -/
def diamondAliasExtra : Source.Env := ⟨diamondEnv.decls ++
  [⟨.stateVar,"a",some "B",false,.stateVar (.elem .bool) none none none false "a" .none⟩]⟩
theorem diamond_same_name_distinct_scope :
    inheritedRootNames diamondAliasExtra ["A","B","C","D"] false =
      [⟨some "A","a"⟩,⟨some "B","b"⟩,⟨some "B","a"⟩,⟨some "C","c"⟩,⟨some "C","items"⟩,
       ⟨some "D","e"⟩,⟨some "D","f"⟩,⟨some "D","marker"⟩] := rfl

end Solidity.Yul.Views.Controls
