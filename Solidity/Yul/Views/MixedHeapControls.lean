import Solidity.Yul.Views.MixedMemoryMemOK

namespace Solidity.Yul.Views.Controls

def mixedName : Source.DeclName := ⟨none, "Box"⟩
def mixedArrayTy : Source.STy := .array .memory (.bytes .memory) none
def mixedTypes : List Source.STy := [.bool, .int Source.IntTy.u256, .bytes .memory, .bytes .memory, mixedArrayTy]
def mixedEnv : Source.Env := ⟨[⟨.struct, "Box", none, true,
  .struct "Box" (.structMember (.elem .bool) "flag")
    (.cons (.structMember (.elem (.int false 256 (by decide))) "number")
    (.cons (.structMember (.elem .bytes) "left")
    (.cons (.structMember (.elem .bytes) "right")
    (.cons (.structMember (.array (.elem .bytes) .none) "children") .nil))))⟩]⟩
def mixedLayout : Source.Layout := mixedEnv.layout
def mixedSeven : Source.Val mixedLayout (.int Source.IntTy.u256) := .int 7 (by decide)
def mixedNine : Source.Val mixedLayout (.int Source.IntTy.u256) := .int 9 (by decide)
def mixedStaticVals (i : Fin 2) : Source.Val mixedLayout (.int Source.IntTy.u256) := if i.val = 0 then mixedSeven else mixedNine
def mixedStatic : Source.Data mixedLayout (.array .memory (.int Source.IntTy.u256) (some 2)) :=
  .array 2 (fun _ e => (Option.some.inj e).symm) (fun i => .val (mixedStaticVals i))
def mixedDynamic : Source.Data mixedLayout mixedArrayTy :=
  .array 2 (fun _ e => nomatch e) (fun _ => .val (.memRef rfl 0))
def mixedFields : Source.DataList mixedLayout (mixedLayout.fields mixedName) :=
  .cons (.val (.bool true)) (.cons (.val mixedSeven) (.cons (.val (.memRef rfl 0))
    (.cons (.val (.memRef rfl 0)) (.cons (.val (.memRef rfl 4)) .nil))))
def mixedStruct : Source.Data mixedLayout (.struct .memory mixedName) := .struct mixedFields
def mixedChild : List UInt8 := [0x11, 0x22, 0x33]
def mixedString : List UInt8 := [0xff, 0x61]
def mixedOther : List UInt8 := [0xee, 0xdd, 0xcc]
def mixedHeap : Source.Heap mixedLayout :=
  ((((((Source.Heap.empty.alloc ⟨.bytes .memory, .bytes mixedChild⟩).1.alloc
    ⟨.string .memory, .string mixedString⟩).1.alloc
    ⟨.array .memory (.int Source.IntTy.u256) (some 2), mixedStatic⟩).1.alloc
    ⟨.struct .memory mixedName, mixedStruct⟩).1.alloc ⟨mixedArrayTy, mixedDynamic⟩).1.alloc
    ⟨.bytes .memory, .bytes mixedOther⟩).1

theorem mixed_present_lt (a : Nat) (present : (mixedHeap.cells a).isSome) : a < 6 := by
  apply Nat.lt_of_not_le
  intro no
  have absent := mixedHeap.bounded a no
  rw [absent] at present
  cases present

def mixedShape (a : Nat) : MemoryShape :=
  if a = 1 then .bytes 2 else if a = 2 then .array false 2 else
  if a = 3 then .strct 5 else if a = 4 then .array true 2 else .bytes 3

def mixedPlacement : Placement mixedHeap where
  address a := 128 + a * 256
  shape := mixedShape
  free := 1664
  free_start := by decide
  distinct a b _ _ same := by omega
  typed a τ d found := by
    cases a with
    | zero =>
      cases found
      exact .bytes _
    | succ a =>
      cases a with
      | zero =>
        cases found
        exact .string _
      | succ a =>
        cases a with
        | zero =>
          cases found
          exact .array 2 _ _
        | succ a =>
          cases a with
          | zero =>
            cases found
            exact .strct _
          | succ a =>
            cases a with
            | zero =>
              cases found
              exact .array 2 _ _
            | succ a =>
              cases a with
              | zero =>
                cases found
                exact .bytes _
              | succ a =>
                have absent := mixedHeap.bounded (a + 6) (by change 6 ≤ a + 6; omega)
                change mixedHeap.cells (a + 6) = some ⟨τ, d⟩ at found
                rw [absent] at found
                cases found
  starts a _ := by omega
  ends a present := by
    have bound := mixed_present_lt a present
    have size : (mixedShape a).size ≤ 160 := by
      unfold mixedShape
      split <;> try decide
      split <;> try decide
      split <;> try decide
      split <;> decide
    change 128 + a * 256 + (mixedShape a).size ≤ 1664
    omega
  separate a b _ _ different := by
    have size (i : Nat) : (mixedShape i).size ≤ 160 := by
      unfold mixedShape
      split <;> try decide
      split <;> try decide
      split <;> try decide
      split <;> decide
    have sa := size a
    have sb := size b
    change 128 + a * 256 + (mixedShape a).size ≤ 128 + b * 256 ∨
      128 + b * 256 + (mixedShape b).size ≤ 128 + a * 256
    omega

def mixedPointer : Roadmap.Word := ownedPointerWord mixedPlacement 0 (.bytes .memory) rfl
def mixedArrayPointer : Roadmap.Word := ownedPointerWord mixedPlacement 4 mixedArrayTy rfl

theorem mixed_static_element (i : Fin 2) : MemoryElement mixedPlacement (mixedStaticVals i) (if i.val = 0 then 7 else 9) := by
  unfold mixedStaticVals
  split
  · exact .scalar mixedSeven 7 (by decide)
  · exact .scalar mixedNine 9 (by decide)

def mixedStaticImage : MemoryImage mixedPlacement mixedStatic := .words _ _
  (.array 2 (fun _ e => (Option.some.inj e).symm) (by decide) mixedStaticVals
    (fun i => if i.val = 0 then 7 else 9) mixed_static_element)
def mixedDynamicImage : MemoryImage mixedPlacement mixedDynamic := .words _ _
  (.array (n := none) (τ := .bytes .memory) 2 (fun _ e => nomatch e) (by decide) (fun _ => .memRef rfl 0) (fun _ => mixedPointer)
    (fun _ => .pointer rfl 0 (.bytes .memory) rfl rfl))
def mixedStructWords : List Roadmap.Word := [1, 7, mixedPointer, mixedPointer, mixedArrayPointer]
def mixedStructImage : MemoryImage mixedPlacement mixedStruct := .words _ mixedStructWords
  (.strct mixedFields mixedStructWords
    (.cons (.bool true) 1 (.scalar _ _ (by decide)) _ _
    (.cons mixedSeven 7 (.scalar _ _ (by decide)) _ _
    (.cons (.memRef rfl 0) mixedPointer (.pointer rfl 0 (.bytes .memory) rfl rfl) _ _
    (.cons (.memRef rfl 0) mixedPointer (.pointer rfl 0 (.bytes .memory) rfl rfl) _ _
    (.cons (.memRef rfl 4) mixedArrayPointer (.pointer rfl 4 mixedArrayTy rfl rfl) _ _ .nil))))))

def mixedEntry0 : MixedHeapEntry mixedPlacement := ⟨0, _, .bytes mixedChild, rfl, .bytes _ (by decide)⟩
def mixedEntry1 : MixedHeapEntry mixedPlacement := ⟨1, _, .string mixedString, rfl, .string _ (by decide)⟩
def mixedEntry2 : MixedHeapEntry mixedPlacement := ⟨2, _, mixedStatic, rfl, mixedStaticImage⟩
def mixedEntry3 : MixedHeapEntry mixedPlacement := ⟨3, _, mixedStruct, rfl, mixedStructImage⟩
def mixedEntry4 : MixedHeapEntry mixedPlacement := ⟨4, _, mixedDynamic, rfl, mixedDynamicImage⟩
def mixedEntry5 : MixedHeapEntry mixedPlacement := ⟨5, _, .bytes mixedOther, rfl, .bytes _ (by decide)⟩
def mixedEntries := [mixedEntry0, mixedEntry1, mixedEntry2, mixedEntry3, mixedEntry4, mixedEntry5]
def mixedResidual : ByteView := mstore (mstore (fun _ => 0xa5) 64 1664) 96 0
def mixedPhysical := encodeMixedHeap mixedPlacement mixedEntries mixedResidual

theorem mixed_distinct : (mixedEntries.map MixedHeapEntry.id).Nodup := by decide

theorem mixed_coverage : CoversMixedHeap mixedEntries := by
  intro a present
  have bound := mixed_present_lt a present
  have choices : a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4 ∨ a = 5 := by omega
  rcases choices with eq | eq | eq | eq | eq | eq
  · subst a; exact ⟨mixedEntry0, List.mem_cons_self, rfl⟩
  · subst a; exact ⟨mixedEntry1, (List.mem_cons_of_mem _ List.mem_cons_self), rfl⟩
  · subst a; exact ⟨mixedEntry2, (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)), rfl⟩
  · subst a; exact ⟨mixedEntry3, (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))), rfl⟩
  · subst a; exact ⟨mixedEntry4, (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))), rfl⟩
  · subst a; exact ⟨mixedEntry5, (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))))), rfl⟩

theorem mixed_all_reads : ∀ e ∈ mixedEntries, e.image.Reads mixedPhysical (mixedPlacement.address e.id) :=
  encodeMixedHeap_reads _ _ mixed_distinct _

theorem mixed_unchanged : encodeMixedHeap mixedPlacement mixedEntries mixedPhysical = mixedPhysical :=
  encodeMixedHeap_unchanged _ _ _ mixed_all_reads

theorem mixed_reserved_initial : ReservedOK mixedResidual 1664 := by
  constructor
  · change readBE (mstore (mstore (fun _ => 0xa5) 64 1664) 96 0) 64 32 = 1664
    have eq := mload_congr (mstore (mstore (fun _ => 0xa5) 64 1664) 96 0) (mstore (fun _ => 0xa5) 64 1664) 64
      (fun i => mstore_outside _ _ _ _ (by have hi := i.isLt; omega))
    exact (congrArg Fin.val eq).trans (congrArg Fin.val (mload_mstore _ 64 1664))
  · intro i
    have hz : wordByte (0 : Roadmap.Word) i = 0 := by
      change UInt8.ofNat ((0 : Roadmap.Word).val / 256 ^ (31 - i.val)) = 0
      rw [show (0 : Roadmap.Word).val = 0 by decide, Nat.zero_div]
      rfl
    exact (find_mstore _ 96 0 i).trans hz

theorem mixed_reserved : ReservedOK mixedPhysical 1664 :=
  encodeMixedHeap_reserved _ _ _ mixed_reserved_initial

theorem mixed_exact_words : mload mixedPhysical 128 = 3 ∧ mload mixedPhysical 384 = 2 ∧
    mload mixedPhysical 640 = 7 ∧ mload mixedPhysical 672 = 9 ∧
    mload mixedPhysical 896 = 1 ∧ mload mixedPhysical 928 = 7 ∧
    mload mixedPhysical 960 = 128 ∧ mload mixedPhysical 992 = 128 ∧ mload mixedPhysical 1024 = 1152 ∧
    mload mixedPhysical 1152 = 2 ∧ mload mixedPhysical 1184 = 128 ∧ mload mixedPhysical 1216 = 128 := by decide

theorem mixed_nested_alias_words :
    mload mixedPhysical (mload mixedPhysical 960).val = 3 ∧
    mload mixedPhysical (mload mixedPhysical 992).val = 3 ∧
    mload mixedPhysical ((mload mixedPhysical 1024).val + 32) = 128 ∧
    mixedPhysical ((mload mixedPhysical ((mload mixedPhysical 1024).val + 32)).val + 32) = 0x11 := by
  obtain ⟨child, str, sa, sb, flag, uint, ptr1, ptr2, arr, len, elem1, elem2⟩ := mixed_exact_words
  rw [ptr1, ptr2, arr]
  change mload mixedPhysical 128 = 3 ∧ mload mixedPhysical 128 = 3 ∧ mload mixedPhysical 1184 = 128 ∧
    mixedPhysical ((mload mixedPhysical 1184).val + 32) = 0x11
  rw [elem1]
  refine ⟨child, child, rfl, ?_⟩
  exact bytesObject_payload mixedChild (by decide) (encodeMixedHeap mixedPlacement mixedEntries.tail mixedResidual) 128 0 (by decide)

theorem mixed_residual_padding : mixedPhysical 163 = 0xa5 ∧ mixedPhysical 420 = 0xa5 ∧
    mixedPhysical 704 = 0xa5 ∧ mixedPhysical 1056 = 0xa5 ∧ mixedPhysical 1248 = 0xa5 ∧
    mixedPhysical 1443 = 0xa5 := by decide

def mixedState : Source.EMState mixedEnv [.bytes .memory, .string .memory, mixedArrayTy, .struct .memory mixedName] :=
  ⟨.cons (.memRef rfl 0) (.cons (.memRef rfl 0) (.cons (.memRef rfl 4) (.cons (.memRef rfl 3) .nil))),
    ⟨⟨⟨fun _ => Source.Account.empty _⟩, .empty, []⟩, mixedHeap, [], [], ⟨[], .nil⟩, Source.FailureExecution.Cursor.empty⟩⟩
def mixedReadFrame : Source.Fr :=
  {this:=0,sender:=0,value:=0,static:=false,contract:="MixedHeap",checked:=true,depth:=0,cd:=[]}

theorem mixed_actual_MemOK : Source.MemOK mixedEnv mixedHeap.ty mixedState := by
  obtain ⟨heap, top, inner⟩ := mixedHeap_owner_invariants mixedPlacement mixedEntries mixed_coverage
  refine ⟨⟨⟨heap, Source.HeapTy.Le.refl _⟩, ?_⟩, top, inner⟩
  exact ⟨⟨.bytes .memory, rfl, rfl⟩, ⟨⟨.bytes .memory, rfl, rfl⟩,
    ⟨⟨mixedArrayTy, rfl, rfl⟩, ⟨⟨.struct .memory mixedName, rfl, rfl⟩, trivial⟩⟩⟩⟩

theorem mixed_source_alias_reads (horizon : Nat) :
    (Source.bytesOfRV (E := mixedEnv) mixedReadFrame horizon (.val (mixedState.1.get (.here)))).run mixedState = (.ok mixedChild, mixedState) ∧
    (Source.bytesOfRV (E := mixedEnv) mixedReadFrame horizon (.val (mixedState.1.get (.there .here)))).run mixedState = (.ok mixedChild, mixedState) := ⟨rfl, rfl⟩

theorem mixed_missing_ownership : ¬ ∃ w, MemoryElement mixedPlacement (Source.Val.memRef (τ := .bytes .memory) rfl 6) w := by
  rintro ⟨w, e⟩
  cases e with
  | scalar v w read => cases read
  | pointer loc a σ owned shape =>
    change none = some σ at owned
    cases owned

theorem mixed_wrong_shape_ownership : ¬ ∃ w, MemoryElement mixedPlacement (Source.Val.memRef (τ := .bytes .memory) rfl 2) w := by
  rintro ⟨w, e⟩
  cases e with
  | scalar v w read => cases read
  | pointer loc a σ owned shape =>
    have eq : .array .memory (.int Source.IntTy.u256) (some 2) = σ := Option.some.inj owned
    subst σ
    cases shape

theorem mixed_string_bytes_alias : MemoryElement mixedPlacement (Source.Val.memRef (τ := .bytes .memory) rfl 1)
    (ownedPointerWord mixedPlacement 1 (.string .memory) rfl) := .pointer rfl 1 (.string .memory) rfl rfl

theorem mixed_wrong_pointer_word : ¬ MemoryElement mixedPlacement (Source.Val.memRef (τ := .bytes .memory) rfl 0) 129 := by
  intro e
  have eq := elementWord_unique e.read (MemoryElement.read (MemoryElement.pointer (p := mixedPlacement) (τ := .bytes .memory) rfl 0 (.bytes .memory) rfl rfl))
  have values := congrArg Fin.val eq
  change 129 = 128 at values
  omega

theorem mixed_wrong_member_type : mixedFields.nth 0 (.int Source.IntTy.u256) = .error (.stuck "field type") := rfl

/-- The compiler fixture reserves the same pool first; its temporary named
return defaults add224 bytes. Both free choices are valid placements. -/
def mixedObservedPlacement : Placement mixedHeap :=
  { mixedPlacement with
    free := 1888
    free_start := by decide
    ends := by
      intro a present
      have old := mixedPlacement.ends a present
      change mixedPlacement.address a + (mixedPlacement.shape a).size ≤ 1888
      have value : mixedPlacement.free.val = 1664 := rfl
      rw [value] at old
      omega }
def mixedObservedPhysical := mstore mixedPhysical 64 1888

theorem mixed_observed_reserved : ReservedOK mixedObservedPhysical 1888 := by
  refine ⟨congrArg Fin.val (mload_mstore mixedPhysical 64 1888), ?_⟩
  intro i
  exact (mstore_outside mixedPhysical 64 (96 + i.val) 1888 (by have hi := i.isLt; omega)).trans (mixed_reserved.2 i)

theorem mixed_observed_source_word (a : Nat) (τ : Source.STy) (d : Source.Data mixedLayout τ)
    (found : mixedHeap.get a = some ⟨τ, d⟩) (off : Nat) (w : Roadmap.Word)
    (read : ObjectWord mixedObservedPlacement.address d off w) :
    mload mixedObservedPhysical (mixedObservedPlacement.address a + off) = w := by
  have present : (mixedHeap.cells a).isSome := by change (mixedHeap.get a).isSome = true; rw [found]; rfl
  have start := mixedObservedPlacement.starts a present
  rw [mload_congr mixedObservedPhysical mixedPhysical _ (fun i => mstore_outside _ _ _ _ (by omega))]
  exact encodeMixedHeap_source_word _ _ mixed_distinct mixed_coverage _ a τ d found off w read

#print axioms mixed_observed_source_word
#print axioms mixed_actual_MemOK
#print axioms mixed_source_alias_reads
#print axioms mixed_missing_ownership
#print axioms mixed_exact_words
#print axioms mixed_unchanged
#print axioms mixed_nested_alias_words
end Solidity.Yul.Views.Controls
