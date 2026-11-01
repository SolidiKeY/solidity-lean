import Solidity.Yul.Views.ComputedLayoutPreparation

namespace Solidity.Yul.Views.Controls

def originName (name : String) : Source.DeclName :=
  ⟨if name = "a" then some "A" else if name = "b" then some "B" else if name = "c" ∨ name = "items" then some "C" else some "D",name⟩
def originPath (name : String) : Source.SPath := ⟨originName name,[]⟩
def originU8 : Source.IntTy := ⟨false,8,by decide⟩
def originU248 : Source.IntTy := ⟨false,248,by decide⟩

def originEnv : Source.Env := ⟨[
  ⟨.struct,"DiamondInner",none,true,.struct "DiamondInner" (.structMember (.elem .bool) "flag")
    (.cons (.structMember (.elem (.int false 16 (by decide))) "small") .nil)⟩,
  ⟨.contract,"A",none,true,.contract false "A" .none .nil .nil⟩,
  ⟨.stateVar,"a",some "A",false,.stateVar (.elem (.int false 8 (by decide))) (some .priv) none none false "a" .none⟩,
  ⟨.contract,"B",none,true,.contract false "B" .none (.cons (.inherit ⟨"A",[]⟩ .none) .nil) .nil⟩,
  ⟨.stateVar,"b",some "B",false,.stateVar (.elem (.int false 248 (by decide))) none none none false "b" .none⟩,
  ⟨.contract,"C",none,true,.contract false "C" .none (.cons (.inherit ⟨"A",[]⟩ .none) .nil) .nil⟩,
  ⟨.stateVar,"c",some "C",false,.stateVar (.elem .bool) none none none false "c" .none⟩,
  ⟨.stateVar,"items",some "C",false,.stateVar (.array (.userType ⟨"DiamondInner",[]⟩) (.some (.lit (.num (.dec 2 0 0))))) none none none false "items" .none⟩,
  ⟨.contract,"D",none,true,.contract false "D" (.some (.lit (.num (.dec 42 0 0)))) (.cons (.inherit ⟨"B",[]⟩ .none) (.cons (.inherit ⟨"C",[]⟩ .none) .nil)) .nil⟩,
  ⟨.stateVar,"e",some "D",false,.stateVar (.elem (.int false 248 (by decide))) none none none false "e" .none⟩,
  ⟨.stateVar,"f",some "D",false,.stateVar (.elem (.int false 16 (by decide))) none none none false "f" .none⟩,
  ⟨.stateVar,"marker",some "D",false,.stateVar (.elem (.int false 256 (by decide))) none none none false "marker" .none⟩,
  ⟨.stateVar,"temp",some "D",false,.stateVar (.elem (.int false 16 (by decide))) none none none true "temp" .none⟩]⟩

def originInnerTy : Source.STy := .struct .storage (⟨none,"DiamondInner"⟩)
def originItemsTy : Source.STy := .array .storage originInnerTy (some 2)
def originInner : FixedDeclaration originEnv originInnerTy :=
  .strct (⟨none,"DiamondInner"⟩) [("flag",.bool),("small",.int unsigned16)] rfl
    (.cons (.scalar .bool (by decide)) (.cons (.scalar (.int unsigned16) (by decide)) .nil))
def originItems : FixedDeclaration originEnv originItemsTy := .array 2 (by decide) originInner

def originDeclTypes : List (Source.DeclName × Source.STy) :=
  [(originName "a",.int originU8),(originName "b",.int originU248),(originName "c",.bool),
   (originName "items",originItemsTy),(originName "e",.int originU248),(originName "f",.int unsigned16),(originName "marker",.int .u256)]
def originDeclarations : RootDeclarations originEnv originDeclTypes :=
  .cons (.scalar (.int originU8) (by decide)) (.cons (.scalar (.int originU248) (by decide))
    (.cons (.scalar .bool (by decide)) (.cons originItems (.cons (.scalar (.int originU248) (by decide))
      (.cons (.scalar (.int unsigned16) (by decide)) (.cons (.scalar (.int .u256) (by decide)) .nil))))))

theorem origin_metadata_order : inheritedRootNames originEnv ["A","B","C","D"] false = (originDeclTypes.map Prod.fst) := rfl

def originA := ((FixedDeclaration.scalar (E := originEnv) (.int originU8) (by decide)).pack (originPath "a") account 1344).toOption.get (by decide)
def originB := ((FixedDeclaration.scalar (E := originEnv) (.int originU248) (by decide)).pack (originPath "b") account 1345).toOption.get (by decide)
def originC := ((FixedDeclaration.scalar (E := originEnv) .bool (by decide)).pack (originPath "c") account 1376).toOption.get (by decide)
def originI := (originItems.pack (originPath "items") account 1377).toOption.get (by decide)
def originE := ((FixedDeclaration.scalar (E := originEnv) (.int originU248) (by decide)).pack (originPath "e") account 1472).toOption.get (by decide)
def originF := ((FixedDeclaration.scalar (E := originEnv) (.int unsigned16) (by decide)).pack (originPath "f") account 1503).toOption.get (by decide)
def originM := ((FixedDeclaration.scalar (E := originEnv) (.int .u256) (by decide)).pack (originPath "marker") account 1506).toOption.get (by decide)
def originComputed := originA.1++(originB.1++(originC.1++(originI.1++(originE.1++(originF.1++originM.1)))))

theorem origin_declarations_ok : originDeclarations.pack account 1344 = .ok (originComputed,1568) := by
  apply RootDeclarations.cons_ok (middle := 1345) (typed := rfl)
  · exact fixedExcept_get _ (by decide)
  · apply RootDeclarations.cons_ok (middle := 1376) (typed := rfl)
    · exact fixedExcept_get _ (by decide)
    · apply RootDeclarations.cons_ok (middle := 1377) (typed := rfl)
      · exact fixedExcept_get _ (by decide)
      · apply RootDeclarations.cons_ok (middle := 1472) (typed := rfl)
        · exact fixedExcept_get _ (by decide)
        · apply RootDeclarations.cons_ok (middle := 1503) (typed := rfl)
          · exact fixedExcept_get _ (by decide)
          · apply RootDeclarations.cons_ok (middle := 1506) (typed := rfl)
            · exact fixedExcept_get _ (by decide)
            · have last := RootDeclarations.cons_ok (root := originName "marker")
                (FixedDeclaration.scalar (E := originEnv) (.int .u256) (by decide)) .nil account 1506 originM.1 1568 [] 1568 rfl
                (fixedExcept_get _ (by decide)) rfl
              simpa only [List.append_nil] using last

def originHierarchy : StorageHierarchy originEnv "D" :=
  (prepareStorageHierarchy originEnv "D").toOption.get (by decide)

theorem origin_owner_C3 : originEnv.linearize "D" = some ["D","C","B","A"] := rfl
theorem origin_base_first : originHierarchy.order = ["A","B","C","D"] := rfl

def originDecision := (prepareActiveOrigin originEnv "D").toOption.get (by decide)
theorem origin_computed_word : originDecision.persistent = 42 := rfl
theorem origin_transient_word : originDecision.forBank true = 0 := rfl

def originChecked : CheckedInheritedDeclarations originDeclarations "D" false account (originDecision.forBank false) :=
  ⟨originHierarchy,rfl,by decide,by decide,originComputed,1568,origin_declarations_ok⟩
def originLayout : ComputedSourceLayout originDeclarations "D" false account := ⟨originDecision,originChecked⟩

def originRegistry (a : Roadmap.Address) : List (ScalarPath originEnv.layout (originEnv.lay a)) := originChecked.registrations

theorem origin_computed_coordinates : (originRegistry account).map (fun c => (c.slot.val,c.field.offset,c.field.width)) =
    [(42,0,1),(42,1,31),(43,0,1),(44,0,1),(44,1,2),(45,0,1),(45,1,2),(46,0,31),(47,0,2),(48,0,32)] := rfl

theorem origin_exact_end : originDeclarations.endByte 1344 = 1568 := originChecked.extent.symm
theorem origin_separation : finiteSeparated (originRegistry account) := originChecked.separated

def originTempDeclarations : RootDeclarations originEnv [(originName "temp",.int unsigned16)] := .cons (.scalar (.int unsigned16) (by decide)) .nil
def originTempLayout := (prepareComputedLayout originTempDeclarations "D" true account).toOption.get (by decide)
def originTempChecked := originTempLayout.layout

def originTempRegistry (a : Roadmap.Address) : List (ScalarPath originEnv.layout (originEnv.lay a)) := originTempChecked.registrations

theorem origin_actual_transient_inventory : inheritedRootNames originEnv originHierarchy.order true = [originName "temp"] := rfl

def originDuplicate : RootDeclarations originEnv [(originName "a",.int originU8),(originName "a",.int originU8)] :=
  .cons (.scalar (.int originU8) (by decide)) (.cons (.scalar (.int originU8) (by decide)) .nil)
theorem origin_duplicate_checked : (prepareInheritedDeclarations originDuplicate "D" false account 1344).toOption.isNone := by decide

def originMissing : RootDeclarations originEnv [(originName "absent",.bool)] := .cons (.scalar .bool (by decide)) .nil
theorem origin_missing_checked : originMissing.pack account 0 = .error .missingRoot := rfl

def originMistyped : RootDeclarations originEnv [(originName "a",.bool)] := .cons (.scalar .bool (by decide)) .nil
theorem origin_mistyped_checked : originMistyped.pack account 0 = .error .missingRoot := rfl

theorem origin_incomplete_order_checked : (prepareInheritedDeclarations originTempDeclarations "D" false account 1344).toOption.isNone := by decide

theorem origin_nonwrapping_failure : (originDeclarations.pack account ((2^256-1)*32)).toOption.isNone := by decide

end Solidity.Yul.Views.Controls

namespace Solidity.Yul.Views.Controls

theorem origin_prepared_registry :
    prepareInheritedDeclarations originDeclarations "D" false account (originDecision.forBank false) = .ok originChecked :=
  prepareInherited_exact originDeclarations "D" false account (originDecision.forBank false) originHierarchy
    (fixedExcept_get _ (by decide)) originChecked.sourceDistinct originChecked.distinct originChecked.ordered
    originComputed 1568 origin_declarations_ok

theorem origin_entry_exact : prepareComputedLayout originDeclarations "D" false account = .ok originLayout :=
  prepareComputed_exact originDeclarations "D" false account originDecision (fixedExcept_get _ (by decide))
    originChecked origin_prepared_registry

theorem origin_default_actual : (prepareActiveOrigin diamondEnv "D").toOption.map ActiveLayoutOrigin.persistent = some 0 := rfl

end Solidity.Yul.Views.Controls
