import Solidity.Yul.Views.RootDeclarationSource
import Solidity.Yul.Views.RootDeclarationTyping

namespace Solidity.Yul.Views

theorem RootDeclarations.cons_ok {E root τ rest} (head : FixedDeclaration E τ) (tail : RootDeclarations E rest)
    (a cursor cs middle ds stop) (typed : E.rootTy root = some τ)
    (first : head.pack ⟨root,[]⟩ a cursor = .ok (cs,middle))
    (second : tail.pack a middle = .ok (ds,stop)) :
    (RootDeclarations.cons (root := root) head tail).pack a cursor = .ok (cs++ds,stop) := by
  simp only [RootDeclarations.pack_cons,if_pos typed,first,Except.bind,second,Except.map]

end Solidity.Yul.Views

namespace Solidity.Yul.Views.Controls

def rootName (name : String) : Source.DeclName := ⟨none,name⟩
def rootPath (name : String) : Source.SPath := ⟨rootName name,[]⟩
def rootU8 : Source.IntTy := ⟨false,8,by decide⟩
def rootU248 : Source.IntTy := ⟨false,248,by decide⟩

def rootEnv : Source.Env := ⟨[
  ⟨.struct,"RootInner",none,true,.struct "RootInner" (.structMember (.elem .bool) "flag")
    (.cons (.structMember (.elem (.int false 16 (by decide))) "small") .nil)⟩,
  ⟨.stateVar,"a",none,true,.stateVar (.elem (.int false 8 (by decide))) none none none false "a" .none⟩,
  ⟨.stateVar,"b",none,true,.stateVar (.elem (.int false 248 (by decide))) none none none false "b" .none⟩,
  ⟨.stateVar,"c",none,true,.stateVar (.elem .bool) none none none false "c" .none⟩,
  ⟨.stateVar,"items",none,true,.stateVar (.array (.userType ⟨"RootInner",[]⟩) (.some (.lit (.num (.dec 2 0 0))))) none none none false "items" .none⟩,
  ⟨.stateVar,"e",none,true,.stateVar (.elem (.int false 248 (by decide))) none none none false "e" .none⟩,
  ⟨.stateVar,"f",none,true,.stateVar (.elem (.int false 16 (by decide))) none none none false "f" .none⟩,
  ⟨.stateVar,"marker",none,true,.stateVar (.elem (.int false 256 (by decide))) none none none false "marker" .none⟩,
  ⟨.stateVar,"temp",none,true,.stateVar (.elem (.int false 16 (by decide))) none none none true "temp" .none⟩]⟩

def rootInnerTy : Source.STy := .struct .storage (rootName "RootInner")
def rootItemsTy : Source.STy := .array .storage rootInnerTy (some 2)
def rootInner : FixedDeclaration rootEnv rootInnerTy :=
  .strct (rootName "RootInner") [("flag",.bool),("small",.int unsigned16)] rfl
    (.cons (.scalar .bool (by decide)) (.cons (.scalar (.int unsigned16) (by decide)) .nil))
def rootItems : FixedDeclaration rootEnv rootItemsTy := .array 2 (by decide) rootInner

def rootDeclTypes : List (Source.DeclName × Source.STy) :=
  [(rootName "a",.int rootU8),(rootName "b",.int rootU248),(rootName "c",.bool),
   (rootName "items",rootItemsTy),(rootName "e",.int rootU248),(rootName "f",.int unsigned16),(rootName "marker",.int .u256)]
def rootDeclarations : RootDeclarations rootEnv rootDeclTypes :=
  .cons (.scalar (.int rootU8) (by decide)) (.cons (.scalar (.int rootU248) (by decide))
    (.cons (.scalar .bool (by decide)) (.cons rootItems (.cons (.scalar (.int rootU248) (by decide))
      (.cons (.scalar (.int unsigned16) (by decide)) (.cons (.scalar (.int .u256) (by decide)) .nil))))))

theorem root_metadata_order : ordinaryRootNames rootEnv none false = (rootDeclTypes.map Prod.fst) := rfl

def rootA := ((FixedDeclaration.scalar (E := rootEnv) (.int rootU8) (by decide)).pack (rootPath "a") account 0).toOption.get (by decide)
def rootB := ((FixedDeclaration.scalar (E := rootEnv) (.int rootU248) (by decide)).pack (rootPath "b") account 1).toOption.get (by decide)
def rootC := ((FixedDeclaration.scalar (E := rootEnv) .bool (by decide)).pack (rootPath "c") account 32).toOption.get (by decide)
def rootI := (rootItems.pack (rootPath "items") account 33).toOption.get (by decide)
def rootE := ((FixedDeclaration.scalar (E := rootEnv) (.int rootU248) (by decide)).pack (rootPath "e") account 128).toOption.get (by decide)
def rootF := ((FixedDeclaration.scalar (E := rootEnv) (.int unsigned16) (by decide)).pack (rootPath "f") account 159).toOption.get (by decide)
def rootM := ((FixedDeclaration.scalar (E := rootEnv) (.int .u256) (by decide)).pack (rootPath "marker") account 162).toOption.get (by decide)
def rootComputed := rootA.1++(rootB.1++(rootC.1++(rootI.1++(rootE.1++(rootF.1++rootM.1)))))

theorem root_declarations_ok : rootDeclarations.pack account 0 = .ok (rootComputed,224) := by
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
            · have last := RootDeclarations.cons_ok (root := rootName "marker")
                (FixedDeclaration.scalar (E := rootEnv) (.int .u256) (by decide)) .nil account 162 rootM.1 224 [] 224 rfl
                (fixedExcept_get _ (by decide)) rfl
              simpa only [List.append_nil] using last

def rootChecked : CheckedRootDeclarations rootDeclarations none false account 0 :=
  ⟨rfl,by decide,by decide,rootComputed,224,root_declarations_ok⟩
def rootRegistry (a : Roadmap.Address) : List (ScalarPath rootEnv.layout (rootEnv.lay a)) := rootChecked.registrations

theorem root_computed_coordinates : (rootRegistry account).map (fun c => (c.slot.val,c.field.offset,c.field.width)) =
    [(0,0,1),(0,1,31),(1,0,1),(2,0,1),(2,1,2),(3,0,1),(3,1,2),(4,0,31),(5,0,2),(6,0,32)] := rfl

theorem root_exact_end : rootDeclarations.endByte 0 = 224 := rootChecked.extent.symm
theorem root_separation : finiteSeparated (rootRegistry account) := rootChecked.separated

def rootTempDeclarations : RootDeclarations rootEnv [(rootName "temp",.int unsigned16)] := .cons (.scalar (.int unsigned16) (by decide)) .nil
def rootTempChecked := (prepareRootDeclarations rootTempDeclarations none true account 0).toOption.get (by decide)
def rootTempRegistry (a : Roadmap.Address) : List (ScalarPath rootEnv.layout (rootEnv.lay a)) := rootTempChecked.registrations

theorem root_actual_transient_inventory : ordinaryRootNames rootEnv none true = [rootName "temp"] := rfl

def rootDuplicate : RootDeclarations rootEnv [(rootName "a",.int rootU8),(rootName "a",.int rootU8)] :=
  .cons (.scalar (.int rootU8) (by decide)) (.cons (.scalar (.int rootU8) (by decide)) .nil)
theorem root_duplicate_checked : (prepareRootDeclarations rootDuplicate none false account 0).toOption.isNone := by decide

def rootMissing : RootDeclarations rootEnv [(rootName "absent",.bool)] := .cons (.scalar .bool (by decide)) .nil
theorem root_missing_checked : rootMissing.pack account 0 = .error .missingRoot := rfl

def rootMistyped : RootDeclarations rootEnv [(rootName "a",.bool)] := .cons (.scalar .bool (by decide)) .nil
theorem root_mistyped_checked : rootMistyped.pack account 0 = .error .missingRoot := rfl

theorem root_incomplete_order_checked : (prepareRootDeclarations rootTempDeclarations none false account 0).toOption.isNone := by decide

theorem root_nonwrapping_failure : (rootDeclarations.pack account ((2^256-1)*32)).toOption.isNone := by decide

end Solidity.Yul.Views.Controls
