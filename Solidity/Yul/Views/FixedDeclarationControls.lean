import Solidity.Yul.Views.FixedDeclarationSource

namespace Solidity.Yul.Views.Controls

/-- Actual declarations: Inner[2][2] followed by uint128[3]. -/
def recursiveDeclEnv : Source.Env := ⟨[
  ⟨.struct,"Inner",none,true,.struct "Inner" (.structMember (.elem .bool) "flag")
    (.cons (.structMember (.elem (.int false 16 (by decide))) "small") .nil)⟩,
  ⟨.struct,"Recursive",none,true,.struct "Recursive"
    (.structMember (.array (.array (.userType ⟨"Inner",[]⟩) (.some (.lit (.num (.dec 2 0 0)))))
      (.some (.lit (.num (.dec 2 0 0))))) "grid")
    (.cons (.structMember (.array (.elem (.int false 128 (by decide))) (.some (.lit (.num (.dec 3 0 0))))) "values") .nil)⟩,
  ⟨.stateVar,"recursive",none,true,.stateVar (.userType ⟨"Recursive",[]⟩) none none none false "recursive" .none⟩]⟩

def recursiveRoot : Source.DeclName := ⟨none,"recursive"⟩
def recursiveUnsigned128 : Source.IntTy := ⟨false,128,by decide⟩

def recursiveInnerTy : Source.STy := .struct .storage ⟨none,"Inner"⟩
def recursiveInnerFields : List (String × Source.STy) :=
  [("flag",.bool),("small",.int unsigned16)]

def recursiveInner : FixedDeclaration recursiveDeclEnv recursiveInnerTy :=
  .strct ⟨none,"Inner"⟩ recursiveInnerFields rfl
    (.cons (.scalar .bool (by decide)) (.cons (.scalar (.int unsigned16) (by decide)) .nil))

def recursiveRootTy : Source.STy := .struct .storage ⟨none,"Recursive"⟩
def recursiveRootFields : List (String × Source.STy) :=
  [("grid",.array .storage (.array .storage recursiveInnerTy (some 2)) (some 2)),
   ("values",.array .storage (.int recursiveUnsigned128) (some 3))]

def recursiveLayout : FixedDeclaration recursiveDeclEnv recursiveRootTy :=
  .strct ⟨none,"Recursive"⟩ recursiveRootFields rfl
    (.cons (.array 2 (by decide) (.array 2 (by decide) recursiveInner))
      (.cons (.array 3 (by decide) (.scalar (.int recursiveUnsigned128) (by decide))) .nil))

theorem fixedRow_ok {E} (step : Nat → Source.Step) (head : FixedPackFn E) (tail : Nat → FixedPackFn E)
    (index path a cursor cs middle ds stop)
    (first : head (path.go (step index)) a cursor = .ok (cs,middle))
    (second : tail (index+1) path a middle = .ok (ds,stop)) :
    packFixedRow step head tail index path a cursor = .ok (cs++ds,stop) := by
  unfold packFixedRow
  rw [first]
  simp only [Except.bind]
  rw [second]
  rfl

theorem fixedAlign_ok {E} (body : FixedPackFn E) (path a cursor cs stop)
    (success : body path a (roundSlot cursor) = .ok (cs,stop)) :
    alignFixedPack body path a cursor = .ok (cs,roundSlot stop) := by
  unfold alignFixedPack
  rw [success]
  rfl

theorem fixedExcept_get {α ε} (x : Except ε α) (ready : x.toOption.isSome) :
    x = .ok (x.toOption.get ready) := by
  cases x with
  | error reason => cases ready
  | ok value => rfl

def recursiveGridPath (i j k : Nat) : Source.SPath := ⟨recursiveRoot,[.field 0,.index i,.index j,.field k]⟩
def recursiveValuePath (i : Nat) : Source.SPath := ⟨recursiveRoot,[.field 1,.index i]⟩


def recursiveChunk00 := (recursiveInner.pack ⟨recursiveRoot,[.field 0,.index 0,.index 0]⟩ account (8*32)).toOption.get (by decide)
theorem recursiveChunk00_ok : recursiveInner.pack ⟨recursiveRoot,[.field 0,.index 0,.index 0]⟩ account (8*32) = .ok (recursiveChunk00.1,9*32) := by
  have computed := fixedExcept_get (recursiveInner.pack ⟨recursiveRoot,[.field 0,.index 0,.index 0]⟩ account (8*32)) (by decide)
  exact computed

def recursiveChunk01 := (recursiveInner.pack ⟨recursiveRoot,[.field 0,.index 0,.index 1]⟩ account (9*32)).toOption.get (by decide)
theorem recursiveChunk01_ok : recursiveInner.pack ⟨recursiveRoot,[.field 0,.index 0,.index 1]⟩ account (9*32) = .ok (recursiveChunk01.1,10*32) := by
  have computed := fixedExcept_get (recursiveInner.pack ⟨recursiveRoot,[.field 0,.index 0,.index 1]⟩ account (9*32)) (by decide)
  exact computed

def recursiveChunk10 := (recursiveInner.pack ⟨recursiveRoot,[.field 0,.index 1,.index 0]⟩ account (10*32)).toOption.get (by decide)
theorem recursiveChunk10_ok : recursiveInner.pack ⟨recursiveRoot,[.field 0,.index 1,.index 0]⟩ account (10*32) = .ok (recursiveChunk10.1,11*32) := by
  have computed := fixedExcept_get (recursiveInner.pack ⟨recursiveRoot,[.field 0,.index 1,.index 0]⟩ account (10*32)) (by decide)
  exact computed

def recursiveChunk11 := (recursiveInner.pack ⟨recursiveRoot,[.field 0,.index 1,.index 1]⟩ account (11*32)).toOption.get (by decide)
theorem recursiveChunk11_ok : recursiveInner.pack ⟨recursiveRoot,[.field 0,.index 1,.index 1]⟩ account (11*32) = .ok (recursiveChunk11.1,12*32) := by
  have computed := fixedExcept_get (recursiveInner.pack ⟨recursiveRoot,[.field 0,.index 1,.index 1]⟩ account (11*32)) (by decide)
  exact computed

def recursiveRow := FixedDeclaration.array 2 (by decide) recursiveInner
theorem recursiveRow0_ok : recursiveRow.pack ⟨recursiveRoot,[.field 0,.index 0]⟩ account (8*32) =
    .ok (recursiveChunk00.1++recursiveChunk01.1,10*32) := by
  change alignFixedPack (fun p a c => packFixedElements recursiveInner.pack p a 0 2 c) _ _ _ = _
  apply fixedAlign_ok (stop := 10*32)
  apply fixedRow_ok (middle := 9*32)
  · exact recursiveChunk00_ok
  · have one := fixedRow_ok Source.Step.index recursiveInner.pack
      (fun i p a c => packFixedElements recursiveInner.pack p a i 0 c) 1 ⟨recursiveRoot,[.field 0,.index 0]⟩ account (9*32) recursiveChunk01.1 (10*32) [] (10*32) recursiveChunk01_ok rfl
    simpa only [List.append_nil] using one

theorem recursiveRow1_ok : recursiveRow.pack ⟨recursiveRoot,[.field 0,.index 1]⟩ account (10*32) =
    .ok (recursiveChunk10.1++recursiveChunk11.1,12*32) := by
  change alignFixedPack (fun p a c => packFixedElements recursiveInner.pack p a 0 2 c) _ _ _ = _
  apply fixedAlign_ok (stop := 12*32)
  apply fixedRow_ok (middle := 11*32)
  · exact recursiveChunk10_ok
  · have one := fixedRow_ok Source.Step.index recursiveInner.pack
      (fun i p a c => packFixedElements recursiveInner.pack p a i 0 c) 1 ⟨recursiveRoot,[.field 0,.index 1]⟩ account (11*32) recursiveChunk11.1 (12*32) [] (12*32) recursiveChunk11_ok rfl
    simpa only [List.append_nil] using one

def recursiveGrid := FixedDeclaration.array 2 (by decide) recursiveRow

theorem recursiveGrid_ok : recursiveGrid.pack ⟨recursiveRoot,[.field 0]⟩ account (8*32) =
    .ok ((recursiveChunk00.1++recursiveChunk01.1)++(recursiveChunk10.1++recursiveChunk11.1),12*32) := by
  change alignFixedPack (fun p a c => packFixedElements recursiveRow.pack p a 0 2 c) _ _ _ = _
  apply fixedAlign_ok (stop := 12*32)
  apply fixedRow_ok (middle := 10*32)
  · exact recursiveRow0_ok
  · have one := fixedRow_ok Source.Step.index recursiveRow.pack
      (fun i p a c => packFixedElements recursiveRow.pack p a i 0 c) 1 ⟨recursiveRoot,[.field 0]⟩ account (10*32)
      (recursiveChunk10.1++recursiveChunk11.1) (12*32) [] (12*32) recursiveRow1_ok rfl
    simpa only [List.append_nil] using one

def recursiveValues := FixedDeclaration.array 3 (by decide) (FixedDeclaration.scalar (E := recursiveDeclEnv) (.int recursiveUnsigned128) (by decide))
def recursiveValueChunk := (recursiveValues.pack ⟨recursiveRoot,[.field 1]⟩ account (12*32)).toOption.get (by decide)
theorem recursiveValues_ok : recursiveValues.pack ⟨recursiveRoot,[.field 1]⟩ account (12*32) = .ok (recursiveValueChunk.1,14*32) :=
  fixedExcept_get _ (by decide)

def recursiveComputed := ((recursiveChunk00.1++recursiveChunk01.1)++(recursiveChunk10.1++recursiveChunk11.1))++recursiveValueChunk.1

theorem recursiveLayout_ok : recursiveLayout.pack ⟨recursiveRoot,[]⟩ account (8*32) = .ok (recursiveComputed,14*32) := by
  change alignFixedPack (packFixedField recursiveGrid.pack (packFixedField recursiveValues.pack (fun _ _ _ c => .ok ([],c))) 0) _ _ _ = _
  apply fixedAlign_ok (stop := 14*32)
  apply fixedRow_ok (middle := 12*32)
  · exact recursiveGrid_ok
  · have one := fixedRow_ok Source.Step.field recursiveValues.pack (fun _ _ _ c => .ok ([],c))
      1 ⟨recursiveRoot,[]⟩ account (12*32) recursiveValueChunk.1 (14*32) [] (14*32) recursiveValues_ok rfl
    simpa only [List.append_nil] using one

def recursiveChecked : CheckedFixedDeclaration recursiveLayout recursiveRoot account 8 :=
  ⟨rfl,recursiveComputed,14*32,recursiveLayout_ok⟩
def recursiveRegistry (a : Roadmap.Address) : List (ScalarPath recursiveDeclEnv.layout (recursiveDeclEnv.lay a)) := recursiveChecked.registrations

theorem recursive_computed_coordinates :
    (recursiveRegistry account).map (fun c => (c.slot.val,c.field.offset,c.field.width)) =
      [(8,0,1),(8,1,2),(9,0,1),(9,1,2),(10,0,1),(10,1,2),(11,0,1),(11,1,2),
       (12,0,16),(12,16,16),(13,0,16)] := rfl

theorem recursive_exact_end : recursiveChecked.endByte = 14*32 ∧ recursiveLayout.endByte (8*32) = 14*32 := ⟨rfl,recursiveChecked.extent.symm⟩
theorem recursive_separated : finiteSeparated (recursiveRegistry account) := recursiveChecked.separated

theorem recursive_complete_paths :
    (recursiveRegistry account).map ScalarPath.path =
      [recursiveGridPath 0 0 0,recursiveGridPath 0 0 1,
       recursiveGridPath 0 1 0,recursiveGridPath 0 1 1,
       recursiveGridPath 1 0 0,recursiveGridPath 1 0 1,
       recursiveGridPath 1 1 0,recursiveGridPath 1 1 1] ++
       (List.range' 0 3).map recursiveValuePath := rfl

theorem recursive_paths_unique : ((recursiveRegistry account).map ScalarPath.path).Nodup := recursiveChecked.unique

theorem recursive_missing_root : (checkFixedDeclaration recursiveLayout ⟨none,"missing"⟩ account 8).toOption = none := rfl

/-- Owner pathTy is structural and does not check fixed-array index bounds.
The derived inventory, in contrast, enumerates precisely the declared count. -/
theorem recursive_out_of_range_not_registered :
    recursiveGridPath 2 0 0 ∉ (recursiveRegistry account).map ScalarPath.path := by decide

theorem recursive_wrong_cell : recursiveLayout.pack ⟨recursiveRoot,[.field 8]⟩ account 256 = .error .cellMismatch := rfl

theorem recursive_slot_overflow :
    (recursiveInner.pack ⟨recursiveRoot,[.field 0,.index 0,.index 0]⟩ account ((2^256)*32)).toOption.isNone := by decide

end Solidity.Yul.Views.Controls
