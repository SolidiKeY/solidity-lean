import Solidity.Yul.Views.InheritedDeclarationLaws

namespace Solidity.Yul.Views.Controls

def diamondName (name : String) : Source.DeclName :=
  ⟨if name = "a" then some "A" else if name = "b" then some "B" else if name = "c" ∨ name = "items" then some "C" else some "D",name⟩
def diamondPath (name : String) : Source.SPath := ⟨diamondName name,[]⟩
def diamondU8 : Source.IntTy := ⟨false,8,by decide⟩
def diamondU248 : Source.IntTy := ⟨false,248,by decide⟩

def diamondEnv : Source.Env := ⟨[
  ⟨.struct,"DiamondInner",none,true,.struct "DiamondInner" (.structMember (.elem .bool) "flag")
    (.cons (.structMember (.elem (.int false 16 (by decide))) "small") .nil)⟩,
  ⟨.contract,"A",none,true,.contract false "A" .none .nil .nil⟩,
  ⟨.stateVar,"a",some "A",false,.stateVar (.elem (.int false 8 (by decide))) (some .priv) none none false "a" .none⟩,
  ⟨.contract,"B",none,true,.contract false "B" .none (.cons (.inherit ⟨"A",[]⟩ .none) .nil) .nil⟩,
  ⟨.stateVar,"b",some "B",false,.stateVar (.elem (.int false 248 (by decide))) none none none false "b" .none⟩,
  ⟨.contract,"C",none,true,.contract false "C" .none (.cons (.inherit ⟨"A",[]⟩ .none) .nil) .nil⟩,
  ⟨.stateVar,"c",some "C",false,.stateVar (.elem .bool) none none none false "c" .none⟩,
  ⟨.stateVar,"items",some "C",false,.stateVar (.array (.userType ⟨"DiamondInner",[]⟩) (.some (.lit (.num (.dec 2 0 0))))) none none none false "items" .none⟩,
  ⟨.contract,"D",none,true,.contract false "D" .none (.cons (.inherit ⟨"B",[]⟩ .none) (.cons (.inherit ⟨"C",[]⟩ .none) .nil)) .nil⟩,
  ⟨.stateVar,"e",some "D",false,.stateVar (.elem (.int false 248 (by decide))) none none none false "e" .none⟩,
  ⟨.stateVar,"f",some "D",false,.stateVar (.elem (.int false 16 (by decide))) none none none false "f" .none⟩,
  ⟨.stateVar,"marker",some "D",false,.stateVar (.elem (.int false 256 (by decide))) none none none false "marker" .none⟩,
  ⟨.stateVar,"temp",some "D",false,.stateVar (.elem (.int false 16 (by decide))) none none none true "temp" .none⟩]⟩

def diamondInnerTy : Source.STy := .struct .storage (⟨none,"DiamondInner"⟩)
def diamondItemsTy : Source.STy := .array .storage diamondInnerTy (some 2)
def diamondInner : FixedDeclaration diamondEnv diamondInnerTy :=
  .strct (⟨none,"DiamondInner"⟩) [("flag",.bool),("small",.int unsigned16)] rfl
    (.cons (.scalar .bool (by decide)) (.cons (.scalar (.int unsigned16) (by decide)) .nil))
def diamondItems : FixedDeclaration diamondEnv diamondItemsTy := .array 2 (by decide) diamondInner

def diamondDeclTypes : List (Source.DeclName × Source.STy) :=
  [(diamondName "a",.int diamondU8),(diamondName "b",.int diamondU248),(diamondName "c",.bool),
   (diamondName "items",diamondItemsTy),(diamondName "e",.int diamondU248),(diamondName "f",.int unsigned16),(diamondName "marker",.int .u256)]
def diamondDeclarations : RootDeclarations diamondEnv diamondDeclTypes :=
  .cons (.scalar (.int diamondU8) (by decide)) (.cons (.scalar (.int diamondU248) (by decide))
    (.cons (.scalar .bool (by decide)) (.cons diamondItems (.cons (.scalar (.int diamondU248) (by decide))
      (.cons (.scalar (.int unsigned16) (by decide)) (.cons (.scalar (.int .u256) (by decide)) .nil))))))

theorem diamond_metadata_order : inheritedRootNames diamondEnv ["A","B","C","D"] false = (diamondDeclTypes.map Prod.fst) := rfl

def diamondA := ((FixedDeclaration.scalar (E := diamondEnv) (.int diamondU8) (by decide)).pack (diamondPath "a") account 0).toOption.get (by decide)
def diamondB := ((FixedDeclaration.scalar (E := diamondEnv) (.int diamondU248) (by decide)).pack (diamondPath "b") account 1).toOption.get (by decide)
def diamondC := ((FixedDeclaration.scalar (E := diamondEnv) .bool (by decide)).pack (diamondPath "c") account 32).toOption.get (by decide)
def diamondI := (diamondItems.pack (diamondPath "items") account 33).toOption.get (by decide)
def diamondE := ((FixedDeclaration.scalar (E := diamondEnv) (.int diamondU248) (by decide)).pack (diamondPath "e") account 128).toOption.get (by decide)
def diamondF := ((FixedDeclaration.scalar (E := diamondEnv) (.int unsigned16) (by decide)).pack (diamondPath "f") account 159).toOption.get (by decide)
def diamondM := ((FixedDeclaration.scalar (E := diamondEnv) (.int .u256) (by decide)).pack (diamondPath "marker") account 162).toOption.get (by decide)
def diamondComputed := diamondA.1++(diamondB.1++(diamondC.1++(diamondI.1++(diamondE.1++(diamondF.1++diamondM.1)))))

theorem diamond_declarations_ok : diamondDeclarations.pack account 0 = .ok (diamondComputed,224) := by
  apply RootDeclarations.cons_ok (middle := 1) (typed := rfl)
  · exact fixedExcept_get _ (by decide)
  · apply RootDeclarations.cons_ok (middle := 32) (typed := rfl)
    · exact fixedExcept_get _ (by decide)
    · apply RootDeclarations.cons_ok (middle := 33) (typed := rfl)
      · exact fixedExcept_get _ (by decide)
      · apply RootDeclarations.cons_ok (middle := 128) (typed := rfl)
        · exact fixedExcept_get _ (by decide)
        · apply RootDeclarations.cons_ok (middle := 159) (typed := rfl)
          · exact fixedExcept_get _ (by decide)
          · apply RootDeclarations.cons_ok (middle := 162) (typed := rfl)
            · exact fixedExcept_get _ (by decide)
            · have last := RootDeclarations.cons_ok (root := diamondName "marker")
                (FixedDeclaration.scalar (E := diamondEnv) (.int .u256) (by decide)) .nil account 162 diamondM.1 224 [] 224 rfl
                (fixedExcept_get _ (by decide)) rfl
              simpa only [List.append_nil] using last

def diamondHierarchy : StorageHierarchy diamondEnv "D" :=
  (prepareStorageHierarchy diamondEnv "D").toOption.get (by decide)

theorem diamond_owner_C3 : diamondEnv.linearize "D" = some ["D","C","B","A"] := rfl
theorem diamond_base_first : diamondHierarchy.order = ["A","B","C","D"] := rfl

def diamondChecked : CheckedInheritedDeclarations diamondDeclarations "D" false account 0 :=
  ⟨diamondHierarchy,rfl,by decide,by decide,diamondComputed,224,diamond_declarations_ok⟩

def diamondRegistry (a : Roadmap.Address) : List (ScalarPath diamondEnv.layout (diamondEnv.lay a)) := diamondChecked.registrations

theorem diamond_computed_coordinates : (diamondRegistry account).map (fun c => (c.slot.val,c.field.offset,c.field.width)) =
    [(0,0,1),(0,1,31),(1,0,1),(2,0,1),(2,1,2),(3,0,1),(3,1,2),(4,0,31),(5,0,2),(6,0,32)] := rfl

theorem diamond_exact_end : diamondDeclarations.endByte 0 = 224 := diamondChecked.extent.symm
theorem diamond_separation : finiteSeparated (diamondRegistry account) := diamondChecked.separated

def diamondTempDeclarations : RootDeclarations diamondEnv [(diamondName "temp",.int unsigned16)] := .cons (.scalar (.int unsigned16) (by decide)) .nil
def diamondTempChecked := (prepareInheritedDeclarations diamondTempDeclarations "D" true account 0).toOption.get (by decide)
def diamondTempRegistry (a : Roadmap.Address) : List (ScalarPath diamondEnv.layout (diamondEnv.lay a)) := diamondTempChecked.registrations

theorem diamond_actual_transient_inventory : inheritedRootNames diamondEnv diamondHierarchy.order true = [diamondName "temp"] := rfl

def diamondDuplicate : RootDeclarations diamondEnv [(diamondName "a",.int diamondU8),(diamondName "a",.int diamondU8)] :=
  .cons (.scalar (.int diamondU8) (by decide)) (.cons (.scalar (.int diamondU8) (by decide)) .nil)
theorem diamond_duplicate_checked : (prepareInheritedDeclarations diamondDuplicate "D" false account 0).toOption.isNone := by decide

def diamondMissing : RootDeclarations diamondEnv [(diamondName "absent",.bool)] := .cons (.scalar .bool (by decide)) .nil
theorem diamond_missing_checked : diamondMissing.pack account 0 = .error .missingRoot := rfl

def diamondMistyped : RootDeclarations diamondEnv [(diamondName "a",.bool)] := .cons (.scalar .bool (by decide)) .nil
theorem diamond_mistyped_checked : diamondMistyped.pack account 0 = .error .missingRoot := rfl

theorem diamond_incomplete_order_checked : (prepareInheritedDeclarations diamondTempDeclarations "D" false account 0).toOption.isNone := by decide

theorem diamond_nonwrapping_failure : (diamondDeclarations.pack account ((2^256-1)*32)).toOption.isNone := by decide

end Solidity.Yul.Views.Controls
