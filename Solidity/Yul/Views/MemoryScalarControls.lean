import Solidity.Yul.Views.CanonicalRetained
import Solidity.Yul.Views.RetainedMemberControls
import Solidity.Yul.Views.ScalarControls

namespace Solidity.Yul.Views.Controls

def canonName : Source.DeclName := ⟨none, "ScalarBox"⟩
def canonEnv : Source.Env := ⟨[⟨.struct, "ScalarBox", none, true,
  .struct "ScalarBox" (.structMember (.elem (.int true 8 (by decide))) "signed")
    (.cons (.structMember (.elem .address) "addr")
    (.cons (.structMember (.elem (.fixedBytes 3 (by decide))) "data") .nil))⟩]⟩
def canonLayout := canonEnv.layout
def canonS8 : Source.IntTy := ⟨true, 8, by decide⟩
def canonMin : Source.Val canonLayout (.int canonS8) := .int (-128) (by decide)
def canonNeg : Source.Val canonLayout (.int canonS8) := .int (-1) (by decide)
def canonZero : Source.Val canonLayout (.int canonS8) := .int 0 (by decide)
def canonMax : Source.Val canonLayout (.int canonS8) := .int 127 (by decide)
def canonAddr : Source.Val canonLayout (.address false) := .address ⟨0x1234, by decide⟩
def canonAddrMax : Source.Val canonLayout (.address false) := .address ⟨2 ^ 160 - 1, by decide⟩
def canonB3Ty : Source.STy := .fixedBytes 3 (by decide)
def canonB3 : Source.Val canonLayout canonB3Ty := .fixedBytes [0x11, 0x22, 0x33] rfl
def canonB3New : Source.Val canonLayout canonB3Ty := .fixedBytes [0xff, 0, 0xaa] rfl
def canonB3Word : Roadmap.Word := Source.toWord (0x112233 * 2 ^ 232)
def canonB3NewWord : Roadmap.Word := Source.toWord (0xff00aa * 2 ^ 232)
def canonFields : Source.DataList canonLayout (canonLayout.fields canonName) := .cons (.val canonMin) (.cons (.val canonAddr) (.cons (.val canonB3) .nil))
def canonNewFields : Source.DataList canonLayout (canonLayout.fields canonName) := .cons (.val canonNeg) (.cons (.val canonAddrMax) (.cons (.val canonB3New) .nil))
def canonSValues (i : Fin 4) : Source.Val canonLayout (.int canonS8) := if i.val = 0 then canonMin else if i.val = 1 then canonNeg else if i.val = 2 then canonZero else canonMax
def canonSNew (i : Fin 4) : Source.Val canonLayout (.int canonS8) := if i.val = 0 then canonNeg else if i.val = 1 then canonMax else if i.val = 2 then canonMin else canonZero
def canonSWords (i : Fin 4) : Roadmap.Word := if i.val = 0 then Source.intWord (-128) else if i.val = 1 then Source.intWord (-1) else if i.val = 2 then 0 else 127
def canonSNewWords (i : Fin 4) : Roadmap.Word := if i.val = 0 then Source.intWord (-1) else if i.val = 1 then 127 else if i.val = 2 then Source.intWord (-128) else 0
def canonHL : ∀ x, some 4 = some x → x = 4 := fun _ e => (Option.some.inj e).symm
def canonBValues (_ : Fin 2) : Source.Val canonLayout canonB3Ty := canonB3
def canonBWords (_ : Fin 2) : Roadmap.Word := canonB3Word

def canonHeap : Source.Heap canonLayout :=
  ((((Source.Heap.empty.alloc ⟨.struct .memory canonName, .struct canonFields⟩).1.alloc
    ⟨.array .memory (.int canonS8) (some 4), memberArrayData canonLayout (.int canonS8) (some 4) 4 canonHL canonSValues⟩).1.alloc
    ⟨.array .memory canonB3Ty none, dynamicMemberData canonLayout canonB3Ty 2 canonBValues⟩).1.alloc
    ⟨.bytes .memory, .bytes [0xee, 0xdd, 0xcc]⟩).1

def canonShape (a : Nat) : MemoryShape := if a = 0 then .strct 3 else if a = 1 then .array false 4 else if a = 2 then .array true 2 else .bytes 3

def canonPlacement : Placement canonHeap where
  address a := 128 + a * 256
  shape := canonShape
  free := 1152
  free_start := by decide
  distinct a b _ _ eq := by omega
  typed a τ d found := by
    cases a with
    | zero => cases found; exact .strct _
    | succ a => cases a with
      | zero => cases found; exact .array _ _ _
      | succ a => cases a with
        | zero => cases found; exact .array _ _ _
        | succ a => cases a with
          | zero => cases found; exact .bytes _
          | succ a =>
            have absent := canonHeap.bounded (a + 4) (by change 4 ≤ a + 4; omega)
            change canonHeap.cells (a + 4) = some ⟨τ, d⟩ at found
            rw [absent] at found
            cases found
  starts a _ := by omega
  ends a present := by
    have bound : a < 4 := by
      apply Nat.lt_of_not_le
      intro no
      have absent := canonHeap.bounded a no
      rw [absent] at present
      cases present
    have size : (canonShape a).size ≤ 128 := by
      unfold canonShape
      split <;> try decide
      split <;> try decide
      split <;> decide
    change 128 + a * 256 + (canonShape a).size ≤ 1152
    omega
  separate a b _ _ distinct := by
    have size (i : Nat) : (canonShape i).size ≤ 128 := by
      unfold canonShape
      split <;> try decide
      split <;> try decide
      split <;> decide
    have sa := size a
    have sb := size b
    change 128 + a * 256 + (canonShape a).size ≤ 128 + b * 256 ∨ 128 + b * 256 + (canonShape b).size ≤ 128 + a * 256
    omega

theorem canon_signed_encoding (i : Fin 4) : MemoryElement canonPlacement (canonSValues i) (canonSWords i) := by
  unfold canonSValues canonSWords
  split <;> try exact .scalar _ _ rfl
  split <;> try exact .scalar _ _ rfl
  split <;> exact .scalar _ _ (by decide)

theorem canon_new_signed_encoding (i : Fin 4) : MemoryElement canonPlacement (canonSNew i) (canonSNewWords i) := by
  unfold canonSNew canonSNewWords
  split <;> try exact .scalar _ _ (by decide)
  split <;> try exact .scalar _ _ (by decide)
  split <;> exact .scalar _ _ (by decide)

theorem canon_fields_encoding : MemoryFields canonPlacement canonFields [Source.intWord (-128), 0x1234, canonB3Word] :=
  .cons canonMin _ (.scalar _ _ rfl) _ _ (.cons canonAddr 0x1234 (.scalar _ _ (by decide)) _ _ (.cons canonB3 canonB3Word (.scalar _ _ (by decide)) _ _ .nil))
theorem canon_new_fields_encoding : MemoryFields canonPlacement canonNewFields [Source.intWord (-1), Source.toWord (2 ^ 160 - 1), canonB3NewWord] :=
  .cons canonNeg _ (.scalar _ _ rfl) _ _ (.cons canonAddrMax (Source.toWord (2 ^ 160 - 1)) (.scalar _ _ (by decide)) _ _ (.cons canonB3New canonB3NewWord (.scalar _ _ (by decide)) _ _ .nil))

def canonEntry0 : MixedHeapEntry canonPlacement := ⟨0, _, .struct canonFields, rfl, .words _ _ (.strct _ _ canon_fields_encoding)⟩
def canonEntry1 : MixedHeapEntry canonPlacement := ⟨1, _, memberArrayData canonLayout (.int canonS8) (some 4) 4 canonHL canonSValues, rfl,
  .words _ _ (.array 4 canonHL (by decide) canonSValues canonSWords canon_signed_encoding)⟩
def canonEntry2 : MixedHeapEntry canonPlacement := ⟨2, _, dynamicMemberData canonLayout canonB3Ty 2 canonBValues, rfl,
  .words _ _ (.array (n := none) 2 (fun _ e => nomatch e) (by decide) canonBValues canonBWords (fun _ => .scalar _ _ (by change canonB3.word = some canonB3Word; decide)))⟩
def canonEntry3 : MixedHeapEntry canonPlacement := ⟨3, _, .bytes [0xee, 0xdd, 0xcc], rfl, .bytes _ (by decide)⟩
def canonEntries := [canonEntry0, canonEntry1, canonEntry2, canonEntry3]

theorem canon_coverage : CoversMixedHeap canonEntries := by
  intro a present
  have bound : a < 4 := by
    apply Nat.lt_of_not_le
    intro no
    have absent := canonHeap.bounded a no
    rw [absent] at present
    cases present
  have choices : a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 := by omega
  rcases choices with eq | eq | eq | eq
  · subst a; exact ⟨canonEntry0, List.mem_cons_self, rfl⟩
  · subst a; exact ⟨canonEntry1, List.mem_cons_of_mem _ List.mem_cons_self, rfl⟩
  · subst a; exact ⟨canonEntry2, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), rfl⟩
  · subst a; exact ⟨canonEntry3, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)), rfl⟩

def canonResidual : ByteView := mstore (mstore (fun _ => 0xa5) 64 1152) 96 0
def canonPhysical := encodeMixedHeap canonPlacement canonEntries canonResidual
def canonState : Source.EMState canonEnv [.array .memory (.int canonS8) (some 4), .array .memory (.int canonS8) (some 4)] :=
  ⟨.cons (.memRef rfl 1) (.cons (.memRef rfl 1) .nil), ⟨⟨⟨fun _ => Source.Account.empty _⟩, .empty, []⟩, canonHeap, [], [], ⟨[], .nil⟩⟩⟩

theorem canon_actual_MemOK : Source.MemOK canonEnv canonHeap.ty canonState := by
  obtain ⟨heap, top, inner⟩ := mixedHeap_owner_invariants canonPlacement canonEntries canon_coverage
  exact ⟨⟨⟨heap, Source.HeapTy.Le.refl _⟩, ⟨⟨.array .memory (.int canonS8) (some 4), rfl, rfl⟩,
    ⟨⟨.array .memory (.int canonS8) (some 4), rfl, rfl⟩, trivial⟩⟩⟩, top, inner⟩

theorem canon_field_support (τ : Source.STy) (member : τ ∈ canonLayout.fields canonName) : ExtendedMemberType canonLayout τ := by
  change τ ∈ [.int canonS8, .address false, canonB3Ty] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with eq | eq | eq
  all_goals subst τ; exact Or.inr trivial

def canonStructPhysical := wordListView [Source.intWord (-1), Source.toWord (2 ^ 160 - 1), canonB3NewWord] canonPhysical 128
def canonStructHeap := canonHeap.write 0 (.struct canonNewFields) (by rfl)
def canonStructState := withSourceHeap canonState canonStructHeap

theorem canon_struct_decode : decodeCanonicalFields canonPlacement canonEntries (canonLayout.fields canonName) canonStructPhysical 128 = some canonNewFields :=
  decodeCanonicalFields_reads canonPlacement canonEntries canon_coverage canon_new_fields_encoding canon_field_support _ _ (fun i w found => wordList_read _ _ _ i w found)

theorem canon_struct_step : canonicalStructState canonState canonPlacement canonEntries 0 canonName canonStructPhysical = some (.ok (), canonStructState) := by
  unfold canonicalStructState
  change (decodeCanonicalFields canonPlacement canonEntries (canonLayout.fields canonName) canonStructPhysical 128).map _ = _
  rw [canon_struct_decode]
  rfl

theorem canon_struct_MemOK (H : Source.HeapTy) (ok : Source.MemOK canonEnv H canonState) : Source.MemOK canonEnv H canonStructState :=
  canonicalStructState_MemOK canonEnv H canonState canonPlacement canonEntries 0 canonName canonStructPhysical _ canon_struct_step ok

def canonArrayPhysical := memberArrayView (some 4) 4 (by decide) canonSNewWords canonPhysical 384
def canonArrayHeap := canonHeap.write 1 (memberArrayData canonLayout (.int canonS8) (some 4) 4 canonHL canonSNew) (by rfl)
def canonArrayState := withSourceHeap canonState canonArrayHeap

theorem canon_array_decode : decodeCanonicalArray canonPlacement canonEntries (.int canonS8) 4 canonArrayPhysical 384 = some canonSNew :=
  decodeCanonicalArray_reads canonPlacement canonEntries canon_coverage (.int canonS8) (Or.inr trivial) _ canonSNew canonSNewWords canon_new_signed_encoding _ _ (memberArrayView_element _ _ _ _ _ _)

theorem canon_array_step : canonicalArrayState canonState canonPlacement canonEntries 1 (.int canonS8) (some 4) 4 canonHL canonArrayPhysical = some (.ok (), canonArrayState) := by
  unfold canonicalArrayState
  simp only [arrayLengthChoice, Option.getD_some, if_true]
  change (decodeCanonicalArray canonPlacement canonEntries (.int canonS8) 4 canonArrayPhysical 384).map _ = _
  rw [canon_array_decode]
  rfl

theorem canon_array_MemOK (H : Source.HeapTy) (ok : Source.MemOK canonEnv H canonState) : Source.MemOK canonEnv H canonArrayState :=
  canonicalArrayState_MemOK canonEnv H canonState canonPlacement canonEntries 1 (.int canonS8) (some 4) 4 canonHL canonArrayPhysical _ canon_array_step ok

theorem canon_array_aliases : canonArrayState.1.get .here = .memRef rfl 1 ∧ canonArrayState.1.get (.there .here) = .memRef rfl 1 ∧
    (Source.readLoc (E := canonEnv) mixedReadFrame (τ := .int canonS8) (.mem 1 2)).run canonArrayState = (.ok canonMin, canonArrayState) := ⟨rfl, rfl, rfl⟩

theorem canon_disjoint_source : canonStructHeap.write 1 (memberArrayData canonLayout (.int canonS8) (some 4) 4 canonHL canonSNew) (by rfl) =
    canonArrayHeap.write 0 (.struct canonNewFields) (by rfl) := heap_writes_commute canonHeap 0 1 _ _ rfl rfl (by decide)

theorem canon_disjoint_physical : wordListView [Source.intWord (-1), Source.toWord (2 ^ 160 - 1), canonB3NewWord]
    (wordListView (List.ofFn canonSNewWords) canonPhysical 384) 128 =
    wordListView (List.ofFn canonSNewWords) (wordListView [Source.intWord (-1), Source.toWord (2 ^ 160 - 1), canonB3NewWord] canonPhysical 128) 384 :=
  (wordList_disjoint_commute _ _ canonPhysical 128 384 (Or.inl (by decide))).symm

theorem canon_negative_controls : decodeCanonicalScalar canonLayout (.int canonS8) 255 = none ∧
    decodeCanonicalScalar canonLayout (.int Source.IntTy.u8) 0x1234 = none ∧
    decodeCanonicalScalar canonLayout (.address false) (Source.toWord (2 ^ 160)) = none ∧
    decodeCanonicalScalar canonLayout canonB3Ty 0x112233 = none := ⟨rfl, rfl, rfl, rfl⟩

theorem canon_signed_boundaries : decodeCanonicalScalar canonLayout (.int canonS8) (Source.intWord (-128)) = some canonMin ∧
    decodeCanonicalScalar canonLayout (.int canonS8) (Source.intWord (-1)) = some canonNeg ∧
    decodeCanonicalScalar canonLayout (.int canonS8) 0 = some canonZero ∧ decodeCanonicalScalar canonLayout (.int canonS8) 127 = some canonMax := by
  exact ⟨decodeCanonicalScalar_encode canonLayout (.int canonS8) trivial canonMin _ rfl,
    decodeCanonicalScalar_encode canonLayout (.int canonS8) trivial canonNeg _ rfl,
    decodeCanonicalScalar_encode canonLayout (.int canonS8) trivial canonZero _ (by decide),
    decodeCanonicalScalar_encode canonLayout (.int canonS8) trivial canonMax _ (by decide)⟩

theorem canon_all_reads : ∀ e ∈ canonEntries, e.image.Reads canonPhysical (canonPlacement.address e.id) :=
  encodeMixedHeap_reads _ _ (by decide) _

theorem canon_struct_unchanged : canonicalStructState canonState canonPlacement canonEntries 0 canonName canonPhysical = some (.ok (), canonState) := by
  apply canonicalStruct_unchanged canonState canonPlacement canonEntries canon_coverage 0 canonName canonFields rfl
    [Source.intWord (-128), 0x1234, canonB3Word] canon_fields_encoding canon_field_support
  exact canon_all_reads canonEntry0 List.mem_cons_self

def canonZeroPhysical := mstore canonPhysical 640 0
def canonZeroHeap := canonHeap.write 2 (dynamicMemberData canonLayout canonB3Ty 0 Fin.elim0) (by rfl)
def canonZeroPlacement := retainedMemberArrayPlacement canonPlacement canonPlacement (retainInitial _ _) 2 canonB3Ty 2 canonBValues rfl 0 Fin.elim0 (by decide)
def canonZeroHistory := retainedMemberArray_history canonPlacement canonPlacement (retainInitial _ _) 2 canonB3Ty 2 canonBValues rfl 0 Fin.elim0 (by decide)
def canonRegrowPhysical := mstore canonZeroPhysical 640 2

theorem canon_regrow_decode : decodeCanonicalArray canonZeroPlacement [] canonB3Ty 2 canonRegrowPhysical 672 = some canonBValues := by
  apply decodeArrayWith_of_decodes
  intro i
  have read : mload canonRegrowPhysical (672 + i.val * 32) = canonB3Word := by
    have eq : mload canonRegrowPhysical (672 + i.val * 32) = mload canonPhysical (672 + i.val * 32) := by
      apply mload_congr
      intro j
      change mstore (mstore canonPhysical 640 0) 640 2 (672 + i.val * 32 + j.val) = _
      rw [mstore_outside _ _ _ _ (by omega), mstore_outside _ _ _ _ (by omega)]
    rw [eq]
    have reads := canon_all_reads canonEntry2 (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
    have choices : i = 0 ∨ i = 1 := by have hi := i.isLt; apply Or.imp (fun h => Fin.ext h) (fun h => Fin.ext h); omega
    rcases choices with eq | eq
    · subst i; exact reads 1 canonB3Word rfl
    · subst i; exact reads 2 canonB3Word rfl
  rw [read]
  exact decodeExtendedScalar_encode canonZeroPlacement [] canonB3Ty trivial canonB3 canonB3Word (.scalar _ _ (by decide))

def canonAliasState : Source.EMState canonEnv [.array .memory canonB3Ty none, .array .memory canonB3Ty none] :=
  ⟨.cons (.memRef rfl 2) (.cons (.memRef rfl 2) .nil), canonState.2⟩
def canonZeroState := withSourceHeap canonAliasState canonZeroHeap
def canonRegrowHeap := canonZeroHeap.write 2 (dynamicMemberData canonLayout canonB3Ty 2 canonBValues) (by rfl)
def canonRegrowState := withSourceHeap canonZeroState canonRegrowHeap

theorem canon_zero_step : canonicalRetainedState canonAliasState canonPlacement canonPlacement (retainInitial _ _) canonEntries 2 canonB3Ty canonZeroPhysical = some (.ok (), canonZeroState) := by
  unfold canonicalRetainedState
  rw [show canonPlacement.address 2 = 640 from rfl, show mload canonZeroPhysical 640 = 0 from mload_mstore _ _ _]
  rfl

theorem canon_regrow_step : canonicalRetainedState canonZeroState canonPlacement canonZeroPlacement canonZeroHistory [] 2 canonB3Ty canonRegrowPhysical = some (.ok (), canonRegrowState) := by
  unfold canonicalRetainedState
  rw [show canonZeroPlacement.address 2 = 640 from rfl, show mload canonRegrowPhysical 640 = 2 from mload_mstore _ _ _]
  rw [if_pos (by decide)]
  change (decodeCanonicalArray canonZeroPlacement [] canonB3Ty 2 canonRegrowPhysical 672).map _ = _
  rw [canon_regrow_decode]
  rfl

theorem canon_alias_initial_MemOK : Source.MemOK canonEnv canonHeap.ty canonAliasState :=
  ⟨⟨canon_actual_MemOK.1.1, ⟨⟨.array .memory canonB3Ty none, rfl, rfl⟩, ⟨⟨.array .memory canonB3Ty none, rfl, rfl⟩, trivial⟩⟩⟩, canon_actual_MemOK.2⟩

theorem canon_regrow_MemOK (H : Source.HeapTy) (ok : Source.MemOK canonEnv H canonAliasState) : Source.MemOK canonEnv H canonRegrowState :=
  canonicalRetainedState_MemOK canonEnv H canonZeroState canonPlacement canonZeroPlacement canonZeroHistory [] 2 canonB3Ty canonRegrowPhysical _ canon_regrow_step
    (canonicalRetainedState_MemOK canonEnv H canonAliasState canonPlacement canonPlacement (retainInitial _ _) canonEntries 2 canonB3Ty canonZeroPhysical _ canon_zero_step ok)

theorem canon_regrow_alias_lengths :
    (Source.lengthOf mixedReadFrame (canonZeroState.1.get .here)).run canonZeroState = (.ok 0, canonZeroState) ∧
    (Source.lengthOf mixedReadFrame (canonRegrowState.1.get .here)).run canonRegrowState = (.ok 2, canonRegrowState) ∧
    (Source.lengthOf mixedReadFrame (canonRegrowState.1.get (.there .here))).run canonRegrowState = (.ok 2, canonRegrowState) ∧
    (Source.readLoc (E := canonEnv) mixedReadFrame (τ := canonB3Ty) (.mem 2 1)).run canonRegrowState = (.ok canonB3, canonRegrowState) := ⟨rfl, rfl, rfl, rfl⟩

theorem canon_source_error : canonicalArrayState canonState canonPlacement canonEntries 0 (.int canonS8) (some 4) 4 canonHL
    (wordListView (List.ofFn canonSNewWords) canonPhysical 128) = some (.error (.stuck "memory write type"), canonState) := by
  have decoded : decodeCanonicalArray canonPlacement canonEntries (.int canonS8) 4 (wordListView (List.ofFn canonSNewWords) canonPhysical 128) 128 = some canonSNew := by
    apply decodeCanonicalArray_reads canonPlacement canonEntries canon_coverage (.int canonS8) (Or.inr trivial) 4 canonSNew canonSNewWords canon_new_signed_encoding
    intro i
    apply wordList_read
    rw [List.getElem?_eq_getElem (by simp only [List.length_ofFn]; exact i.isLt)]
    simp only [List.getElem_ofFn]
  unfold canonicalArrayState
  simp only [arrayLengthChoice, Option.getD_some, if_true]
  change (decodeCanonicalArray canonPlacement canonEntries (.int canonS8) 4 (wordListView (List.ofFn canonSNewWords) canonPhysical 128) 128).map _ = _
  rw [decoded]
  simp only [Option.map_some]
  rw [memberArrayHeapPut_error canonState 0 (.int canonS8) (some 4) 4 canonHL canonSNew (by decide)]

theorem canon_old_decoder_unchanged : decodeMemoryMember canonPlacement canonEntries (.int canonS8) (Source.intWord (-1)) = none ∧
    decodeMemoryMember canonPlacement canonEntries .bool 2 = none := ⟨rfl, rfl⟩

theorem canon_legacy_reference : decodeExtendedMemoryMember mixedPlacement mixedEntries (.bytes .memory) 128 = some (.memRef rfl 0) :=
  decodeExtendedMemoryMember_encode mixedPlacement mixedEntries mixed_coverage (.bytes .memory) (Or.inl (Or.inr (Or.inr rfl))) _ _ (.pointer rfl 0 (.bytes .memory) rfl rfl)

theorem canon_enum_and_contract : decodeCanonicalScalar scalarLayout (.enum scalarName) 2 = some (.enum ⟨2, by decide⟩) ∧
    decodeCanonicalScalar scalarLayout (.enum scalarName) 3 = none ∧
    decodeCanonicalScalar scalarLayout (.contract scalarName) 0x1234 = some (.contract ⟨0x1234, by decide⟩) := by
  refine ⟨decodeCanonicalScalar_encode scalarLayout (.enum scalarName) (by change 3 ≤ 2 ^ 256; decide) _ _ (by decide), rfl, ?_⟩
  exact decodeCanonicalScalar_encode scalarLayout (.contract scalarName) trivial _ _ (by decide)

theorem canon_unsigned24_boundary : decodeCanonicalScalar canonLayout (.int ⟨false, 24, by decide⟩) 16777215 =
    some (.int 16777215 (by decide)) := decodeCanonicalScalar_encode canonLayout (.int ⟨false, 24, by decide⟩) trivial _ _ (by decide)

theorem canon_reserved_and_tails : canonStructPhysical 64 = canonPhysical 64 ∧ canonArrayPhysical 96 = canonPhysical 96 ∧
    canonStructPhysical 224 = canonPhysical 224 ∧ canonRegrowPhysical 736 = canonPhysical 736 := by
  exact ⟨wordList_residual _ _ _ _ (Or.inl (by decide)), memberArrayView_residual _ _ _ _ _ _ _ (Or.inl (by decide)),
    wordList_residual _ _ _ _ (Or.inr (by decide)), (mstore_outside _ _ _ _ (by decide)).trans (mstore_outside _ _ _ _ (by decide))⟩

end Solidity.Yul.Views.Controls
