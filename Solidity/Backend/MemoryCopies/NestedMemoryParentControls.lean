import Solidity.Backend.MemoryCopies.NestedMemoryParent

/-! A real dynamic parent contains two aliases of the same variable-length
child. A separate reservation receives the new deep-copy pointer. -/
namespace Solidity.Backend.MemoryCopies.NestedMemoryParentControls
open Evm Evm.Memory
private abbrev R : RefTy := .array (.prim .uint)
private abbrev P : RefTy := .array (.ref R)
private abbrev H : HTy := [R, P]
private def child : HRef H R := ⟨0, rfl⟩
private def source : HRef H P := ⟨1, rfl⟩
private def values (payloads : List (Fin W)) : List PrimTy.uint.Denote := payloads.map indexValue
private theorem wide : 128 < W := by decide
private def heap (payloads : List (Fin W)) (bounded : payloads.length < 128) : Heap H :=
  (⟨values payloads, by rw [values, List.length_map]; have large : 128 < W := wide; omega⟩, (⟨[child,child], by decide⟩, ()))
private def base (identity : Nat) : Fin W := if identity = 0 then wmod 16 else wmod 160
private def machine (payloads : List (Fin W)) : Machine :=
  {Machine.init with stack := [w[77]], mem := fun address =>
    if address = 0 then w[192] else if address = 7 then w[99]
    else if address = 16 then .val (wmod payloads.length) else if address = 160 then w[2]
    else if address = 161 ∨ address = 162 then w[16]
    else if 17 ≤ address ∧ address < 17 + payloads.length then .val (payloads[address - 17]?.getD (wmod 0)) else w[0]}
private theorem refs {Q : RefTy} (reference : HRef H Q) : (Q = R ∧ HEq reference child) ∨ (Q = P ∧ HEq reference source) := by
  rcases reference with ⟨index, selected⟩
  cases index with
  | zero => cases selected; exact .inl ⟨rfl, HEq.rfl⟩
  | succ index => cases index with
    | zero => cases selected; exact .inr ⟨rfl, HEq.rfl⟩
    | succ index => cases selected
private theorem cells_child (payloads : List (Fin W)) (bounded : payloads.length < 128) :
    Objects.cells (heap payloads bounded) child = 1 + payloads.length := by
  with_unfolding_all change 1 + (values payloads).length = 1 + payloads.length
  rw [values, List.length_map]
private theorem cells_source (payloads : List (Fin W)) (bounded : payloads.length < 128) :
    Objects.cells (heap payloads bounded) source = 3 := by
  with_unfolding_all rfl
private theorem heap_repr (payloads : List (Fin W)) (bounded : payloads.length < 128) :
    Objects.HeapRepr (heap payloads bounded) base 8 (machine payloads) := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · intro Q reference
    rcases refs reference with ⟨rfl, eq⟩ | ⟨rfl, eq⟩ <;> cases eq <;> decide
  · intro Q reference
    rcases refs reference with ⟨rfl, eq⟩ | ⟨rfl, eq⟩ <;> cases eq
    · rw [cells_child]
      change 16 + (1 + payloads.length) ≤ W
      have large : 512 < W := by decide
      omega
    · rw [cells_source]
      decide
  · intro Q S left right different
    rcases refs left with ⟨rfl, eq⟩ | ⟨rfl, eq⟩ <;> cases eq
      <;> rcases refs right with ⟨rfl, eq⟩ | ⟨rfl, eq⟩ <;> cases eq
    · exact (different rfl).elim
    · left
      rw [cells_child]
      change 16 + (1 + payloads.length) ≤ 160
      omega
    · right
      rw [cells_child]
      change 16 + (1 + payloads.length) ≤ 160
      omega
    · exact (different rfl).elim
  · intro A E shape reference
    rcases refs reference with ⟨rfl, eq⟩ | ⟨rfl, eq⟩ <;> cases eq <;> cases shape
    · refine ⟨?_, ?_, ?_⟩
      · rw [cells_child]
        change 16 + (1 + payloads.length) ≤ W
        have large : 512 < W := by decide
        omega
      · intro _
        with_unfolding_all change Word.val (wmod payloads.length) = Word.val (wmod (values payloads).length)
        rw [values, List.length_map]
      · intro index item selected
        with_unfolding_all change (values payloads)[index]? = some item at selected
        simp only [values, List.getElem?_map] at selected
        cases found : payloads[index]? with
        | none => simp only [found, Option.map_none] at selected; cases selected
        | some payload =>
          simp only [found, Option.map_some] at selected
          cases selected
          have lower : index < payloads.length := lt_of_getElem? found
          change ReprV .uint (indexValue payload) ((machine payloads).mem (17 + index))
          simp only [machine, if_neg (show 17 + index ≠ 0 by omega), if_neg (show 17 + index ≠ 7 by omega),
            if_neg (show 17 + index ≠ 16 by omega), if_neg (show 17 + index ≠ 160 by omega),
            if_neg (show ¬(17 + index = 161 ∨ 17 + index = 162) by omega),
            if_pos (show 17 ≤ 17 + index ∧ 17 + index < 17 + payloads.length by omega), Nat.add_sub_cancel_left, found, Option.getD_some]
          exact ReprV.uint_of rfl
    · refine ⟨by rw [cells_source]; decide, ?_, ?_⟩
      · intro _
        with_unfolding_all rfl
      · intro index item selected
        with_unfolding_all change [child,child][index]? = some item at selected
        cases index with
        | zero => cases selected; rfl
        | succ index => cases index with
          | zero => cases selected; rfl
          | succ index => cases selected
  · intro name reference
    rcases refs reference with ⟨different, _⟩ | ⟨different, _⟩ <;> cases different
  · intro name field Q reference fieldType
    rcases refs reference with ⟨different, _⟩ | ⟨different, _⟩ <;> cases different
private theorem allocator (payloads : List (Fin W)) (bounded : payloads.length < 128) :
    Objects.AllocatorRepr (heap payloads bounded) base 8 (wmod 192) (machine payloads) := by
  refine ⟨heap_repr payloads bounded, ⟨by decide, by decide, rfl, ?_⟩, ?_⟩
  · intro address above
    change 192 ≤ address at above
    simp only [machine, if_neg (show address ≠ 0 by omega), if_neg (show address ≠ 7 by omega),
      if_neg (show address ≠ 16 by omega), if_neg (show address ≠ 160 by omega),
      if_neg (show ¬(address = 161 ∨ address = 162) by omega), if_neg (show ¬(17 ≤ address ∧ address < 17 + payloads.length) by omega)]
  · intro Q reference
    rcases refs reference with ⟨rfl, eq⟩ | ⟨rfl, eq⟩ <;> cases eq
    · rw [cells_child]
      change 16 + (1 + payloads.length) ≤ 192
      omega
    · rw [cells_source]
      decide
private def row (payloads : List (Fin W)) (bounded : payloads.length < 128) : PrimitiveStorageRow .uint :=
  ⟨values payloads, by rw [values, List.length_map]; exact Nat.lt_trans bounded wide⟩
private theorem source_rows (payloads : List (Fin W)) (bounded : payloads.length < 128) :
    memoryChildRows (heap payloads bounded) .uint source = [row payloads bounded,row payloads bounded] := by
  with_unfolding_all rfl
private theorem source_snapshot (payloads : List (Fin W)) (bounded : payloads.length < 128) :
    MVal.copyMToSt (heap payloads bounded) (T := .ref P) source =
      nestedStorageParentValue .uint [row payloads bounded,row payloads bounded] (by change 2 < W; decide) := by
  simpa only [memoryParentRowsValue, source_rows] using memory_parent_snapshot (heap payloads bounded) .uint source
private theorem demand (payloads : List (Fin W)) (bounded : payloads.length < 128) :
    memoryParentDemand (heap payloads bounded) .uint source = 3 + 2 * (payloads.length + 1) := by
  unfold memoryParentDemand
  rw [source_rows]
  simp only [nestedStorageParentDemand, nestedStorageDemand, List.length_cons, List.length_nil, row, values, List.length_map]
  omega

theorem certificate_inhabited : NestedMemoryParentCertificate := nestedMemoryParent

theorem actual_typed (payloads : List (Fin W)) (bounded : payloads.length < 128) : ∃ fits,
    NestedMemoryParentResult (heap payloads bounded) .uint source base 8 (wmod 192) (machine payloads) fits := by
  have fits : (wmod 192).val + memoryParentDemand (heap payloads bounded) .uint source < W := by
    rw [demand]
    change 192 + (3 + 2 * (payloads.length + 1)) < W
    have large : 512 < W := by decide
    omega
  exact ⟨fits, nested_memory_parent_success (heap payloads bounded) .uint source base 8 (wmod 192) (machine payloads)
    (allocator payloads bounded) fits⟩

theorem actual_runtime (payloads : List (Fin W)) (bounded : payloads.length < 128) : ∃ target : Machine,
    run (nestedMemoryParentCode .uint) ((machine payloads).push w[160]) = .ok (target.push w[192]) 0 ∧
    target.mem 0 = .val (wmod (195 + 2 * (payloads.length + 1))) ∧ target.mem 192 = w[2] ∧
    target.mem 161 = w[16] ∧ target.mem 162 = w[16] ∧ target.stack = [w[77]] ∧
    (∀ index payload, payloads[index]? = some payload → target.mem (17 + index) = .val payload) := by
  obtain ⟨fits, base', target, ran, allocated, root, extension, shape, below, gaps, keeps, fresh, length, contents, retained⟩ := actual_typed payloads bounded
  let snapshot := MVal.copyMToSt (heap payloads bounded) (T := .ref P) source
  let grown := snapshot.copyStToM (heap payloads bounded) rfl
  have sourceLength : (heap payloads bounded).len source .dyn = 2 := by with_unfolding_all rfl
  have copiedHeader : target.mem 192 = w[2] := by
    have header : target.mem (base' grown.val.id).val = .val (wmod (grown.heap.len grown.val .dyn)) :=
      (allocated.heap.arrays .dyn grown.val).length rfl
    rw [root, length, sourceLength] at header
    exact header
  refine ⟨target, ran, ?_, copiedHeader, (below 161 (by decide) (by decide)).trans rfl,
    (below 162 (by decide) (by decide)).trans rfl, congrArg Machine.stack shape, ?_⟩
  · refine allocated.free.cell.trans ?_
    apply congrArg Word.val
    apply Fin.ext
    change 192 + memoryParentDemand (heap payloads bounded) .uint source = (195 + 2 * (payloads.length + 1)) % W
    rw [demand, Nat.mod_eq_of_lt (show 195 + 2 * (payloads.length + 1) < W by
      have large : 512 < W := by decide
      omega)]
    omega
  · intro index payload chosen
    have lower : index < payloads.length := lt_of_getElem? chosen
    rw [below (17 + index) (by omega) (by change 17 + index < 192; omega)]
    simp only [machine, if_neg (show 17 + index ≠ 0 by omega), if_neg (show 17 + index ≠ 7 by omega),
      if_neg (show 17 + index ≠ 16 by omega), if_neg (show 17 + index ≠ 160 by omega),
      if_neg (show ¬(17 + index = 161 ∨ 17 + index = 162) by omega),
      if_pos (show 17 ≤ 17 + index ∧ 17 + index < 17 + payloads.length by omega), Nat.add_sub_cancel_left, chosen, Option.getD_some]

private theorem primitive_mirror_values {H' : HTy} (hp : Heap H') (frontier : Nat) (primitive : PrimTy)
    (items : List primitive.Denote) (stored : List (MVal H' (.prim primitive)))
    (mirrored : (SVec.ofList (items.map SVal.prim)).Mirrors hp frontier stored) : stored = items := by
  induction items generalizing stored with
  | nil => simpa only [List.map_nil, SVec.ofList, SVec.Mirrors] using mirrored
  | cons item items ih =>
    simp only [List.map_cons, SVec.ofList, SVec.Mirrors, SVal.Mirrors] at mirrored
    obtain ⟨actual, tail, rfl, same, rest⟩ := mirrored
    rw [same, ih tail rest]

theorem copied_payloads (payloads : List (Fin W)) (bounded : payloads.length < 128) : ∃ target : Machine, ∃ pointer : Fin W,
    run (nestedMemoryParentCode .uint) ((machine payloads).push w[160]) = .ok (target.push w[192]) 0 ∧
    target.mem 193 = .val pointer ∧ target.mem pointer.val = .val (wmod payloads.length) ∧
    (∀ index payload, payloads[index]? = some payload → target.mem (pointer.val + 1 + index) = .val payload) := by
  obtain ⟨fits, base', target, ran, allocated, root, extension, shape, below, gaps, keeps, fresh, length, contents, retained⟩ := actual_typed payloads bounded
  let snapshot := MVal.copyMToSt (heap payloads bounded) (T := .ref P) source
  let grown := snapshot.copyStToM (heap payloads bounded) rfl
  have mirrored : (nestedStorageParentValue .uint [row payloads bounded,row payloads bounded] (by change 2 < W; decide)).Mirrors grown.heap H.length grown.val :=
    (congrArg (fun value : SVal (.ref P) => value.Mirrors grown.heap H.length grown.val) (source_snapshot payloads bounded)).mp
      (SVal.mirrors_copyStToM (heap payloads bounded) snapshot rfl)
  obtain ⟨first, tail, parentElements, firstMirror, tailMirror⟩ := mirrored.2
  have elements : MObj.elems .dyn (grown.heap.get first) = values payloads :=
    primitive_mirror_values grown.heap H.length .uint (values payloads) _ firstMirror.2
  have firstPointer : target.mem 193 = .val (base' first.id) := by
    have observed : target.mem ((base' grown.val.id).val + 1 + 0) = .val (base' first.id) :=
      (allocated.heap.arrays .dyn grown.val).elements 0 first (by rw [parentElements]; rfl)
    rw [root] at observed
    exact observed
  have firstLength : grown.heap.len first .dyn = payloads.length := by
    simpa only [Heap.len, MObj.elems_dyn, values, List.length_map] using congrArg List.length elements
  refine ⟨target, base' first.id, ran, firstPointer, ?_, ?_⟩
  · rw [← firstLength]
    exact (allocated.heap.arrays .dyn first).length rfl
  · intro index payload chosen
    have selected : (MObj.elems .dyn (grown.heap.get first))[index]? = some (indexValue payload) := by
      rw [elements]
      simp only [values, List.getElem?_map, chosen, Option.map_some]
    have represented : ReprV .uint (indexValue payload) (target.mem ((base' first.id).val + 1 + index)) :=
      (allocated.heap.arrays .dyn first).elements index (indexValue payload) selected
    obtain ⟨word, stored, equal⟩ := represented
    have same : word = payload := Fin.ext (Int.ofNat_inj.mp equal.symm)
    subst word
    exact stored

theorem pair_copied_words : ∃ target : Machine, ∃ pointer : Fin W,
    run (nestedMemoryParentCode .uint) ((machine [wmod 11,wmod 23]).push w[160]) = .ok (target.push w[192]) 0 ∧
    target.mem 193 = .val pointer ∧ target.mem pointer.val = w[2] ∧
    target.mem (pointer.val + 1) = w[11] ∧ target.mem (pointer.val + 2) = w[23] := by
  obtain ⟨target, pointer, ran, stored, header, words⟩ := copied_payloads [wmod 11,wmod 23] (by decide)
  exact ⟨target, pointer, ran, stored, header, words 0 (wmod 11) rfl, words 1 (wmod 23) rfl⟩

theorem empty_children_runtime : ∃ target : Machine,
    run (nestedMemoryParentCode .uint) ((machine []).push w[160]) = .ok (target.push w[192]) 0 ∧
    target.mem 0 = w[197] ∧ target.mem 192 = w[2] := by
  obtain ⟨target, ran, cursor, header, _⟩ := actual_runtime [] (by decide)
  exact ⟨target, ran, cursor, header⟩

private def long : List (Fin W) := List.ofFn (fun i : Fin 64 => wmod (i.val + 1))
theorem long_copied_words : ∃ target : Machine, ∃ pointer : Fin W,
    run (nestedMemoryParentCode .uint) ((machine long).push w[160]) = .ok (target.push w[192]) 0 ∧
    target.mem 193 = .val pointer ∧ target.mem pointer.val = w[64] ∧
    target.mem (pointer.val + 1) = w[1] ∧ target.mem (pointer.val + 64) = w[64] := by
  obtain ⟨target, pointer, ran, stored, header, words⟩ := copied_payloads long (by rw [long, List.length_ofFn]; decide)
  exact ⟨target, pointer, ran, stored, by simpa only [long, List.length_ofFn] using header,
    words 0 (wmod 1) (by decide +kernel), words 63 (wmod 64) (by decide +kernel)⟩

theorem ignored_children_rejected (target : Machine)
    (ran : run (nestedMemoryParentCode .uint) ((machine []).push w[160]) = .ok (target.push w[192]) 0) : target.mem 0 ≠ w[195] := by
  obtain ⟨actual, execution, cursor, _⟩ := empty_children_runtime
  rw [ran] at execution
  have same : target.mem 0 = actual.mem 0 := congrArg (fun m => m.mem 0) (Out.ok.inj execution).1
  rw [same, cursor]
  decide

private def moved (payloads : List (Fin W)) (cursor : Fin W) : Machine := writeMachine (machine payloads) 0 (.val cursor)
private theorem moved_allocator (payloads : List (Fin W)) (bounded : payloads.length < 128)
    (cursor : Fin W) (above : 192 ≤ cursor.val) : Objects.AllocatorRepr (heap payloads bounded) base 8 cursor (moved payloads cursor) := by
  have old : Objects.AllocatorRepr (heap payloads bounded) base 8 (wmod 192) (machine payloads) := allocator payloads bounded
  refine ⟨old.heap.localWrite 0 (by decide) (.val cursor), ⟨by decide, by omega, rfl, ?_⟩, ?_⟩
  · intro address lower
    exact (upd_other _ _ (by omega : address ≠ 0)).trans (old.free.zero address (by change 192 ≤ address; omega))
  · intro Q reference
    have live : (base reference.id).val + Objects.cells (heap payloads bounded) reference ≤ 192 := old.live reference
    omega

theorem saturated_parent_refusal : run (nestedMemoryParentCode .uint) ((moved [] wMax).push w[160]) = .revert := by
  exact nested_memory_parent_refusal (heap [] (by decide)) .uint source base 8 wMax (moved [] wMax)
    (moved_allocator [] (by decide) wMax (by decide)) (by
      rw [demand]
      change ¬ W - 1 + (3 + 2 * (0 + 1)) < W
      have positive : 0 < W := W_pos
      omega)

private def late : Fin W := ⟨W - 7, by
  have large : 1024 < W := by decide
  omega⟩
theorem child_refusal_after_successful_prefix : ∃ middle : Machine,
    run ([.dup 1, .mloadAt] ++ (referenceCapacityGuard 0 ++ (Objects.nestedPrefix ++ nestedMemoryTurnCode .uint)))
      ((moved [wmod 11,wmod 23] late).push w[160]) =
      .ok (nestedMemoryControl middle (wmod 160) late (wmod 2) (wmod 1)) 0 ∧
    run (nestedMemoryParentCode .uint) ((moved [wmod 11,wmod 23] late).push w[160]) = .revert := by
  have large : 1024 < W := by decide
  have input : Objects.AllocatorRepr (heap [wmod 11,wmod 23] (by decide)) base 8 late (moved [wmod 11,wmod 23] late) :=
    moved_allocator _ (by decide) late (by change 192 ≤ W - 7; omega)
  have parentFits : late.val + (wmod 2).val + 1 < W := by change W - 7 + 2 + 1 < W; omega
  let next : Fin W := ⟨late.val + (wmod 2).val + 1, parentFits⟩
  let start := allocateMachine (moved [wmod 11,wmod 23] late) late (wmod 2)
  have reserved : Objects.AllocatorRepr (heap [wmod 11,wmod 23] (by decide)) base 8 next start ∧
      Objects.Gap (heap [wmod 11,wmod 23] (by decide)) base late.val (late.val + (wmod 2).val + 1) := input.reserveArray _ parentFits
  have gap : Objects.Gap (heap [wmod 11,wmod 23] (by decide)) base late.val (late.val + 1 + (wmod 2).val) := by
    intro Q reference
    simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using reserved.2 reference
  have firstFits : next.val + ((heap [wmod 11,wmod 23] (by decide)).len child .dyn + 1) < W := by
    with_unfolding_all change W - 7 + 2 + 1 + (2 + 1) < W
    omega
  obtain ⟨_, middle, body, _⟩ := nested_memory_turn_success (heap [wmod 11,wmod 23] (by decide)) .uint source child base 8 next start
    late (wmod 2) (wmod 0) reserved.1 gap (by change 8 ≤ W - 7; omega)
    (by change W - 7 + 1 + 2 ≤ W - 7 + 2 + 1; omega) (by decide) (by with_unfolding_all rfl) firstFits
  have countTwo : memoryChildCount (heap [wmod 11,wmod 23] (by decide)) .uint source = wmod 2 := by
    apply Fin.ext
    with_unfolding_all change 2 = 2 % W
    exact (Nat.mod_eq_of_lt (by decide : 2 < W)).symm
  have sourceWord : base source.id = (⟨160, by decide⟩ : Fin W) := by decide +kernel
  have modSource : wmod 160 = (⟨160, by decide⟩ : Fin W) := Fin.ext (Nat.mod_eq_of_lt (by decide))
  have headerRun : run [.dup 1, .mloadAt] ((moved [wmod 11,wmod 23] late).push (.val (base source.id))) =
      .ok (((moved [wmod 11,wmod 23] late).push (.val (base source.id))).push (.val (wmod 2))) 0 := by
    simpa only [countTwo] using nested_memory_parent_enter _ .uint source base 8 late _ input
  have guard : run (referenceCapacityGuard 0) (((moved [wmod 11,wmod 23] late).push (.val (base source.id))).push (.val (wmod 2))) =
      .ok (((moved [wmod 11,wmod 23] late).push (.val (base source.id))).push (.val (wmod 2))) 0 := by
    rw [nested_memory_parent_guard _ (base source.id) late (wmod 2) input.free.cell, if_pos parentFits]
  have prefixRun : run ([.dup 1, .mloadAt] ++ (referenceCapacityGuard 0 ++ (Objects.nestedPrefix ++ nestedMemoryTurnCode .uint)))
      ((moved [wmod 11,wmod 23] late).push (.val (base source.id))) =
      .ok (nestedMemoryControl middle (base source.id) late (wmod 2) (wmod 1)) 0 := by
    rw [run_append_ok headerRun, run_append_ok guard,
      run_append_ok (nested_memory_parent_prefix _ (base source.id) late (wmod 2) input.free.cell)]
    exact body
  refine ⟨middle, ?_, ?_⟩
  · simpa only [sourceWord, modSource] using prefixRun
  · have refused : run (nestedMemoryParentCode .uint) ((moved [wmod 11,wmod 23] late).push (.val (base source.id))) = .revert :=
      nested_memory_parent_refusal _ .uint source base 8 late _ input (by
        rw [demand]
        change ¬ W - 7 + (3 + 2 * (2 + 1)) < W
        omega)
    simpa only [sourceWord] using refused

private def emptyReference : HRef [P] P := ⟨0,rfl⟩
private def emptyHeap : Heap [P] := (⟨[],by decide⟩,())
private def emptyBase (_ : Nat) : Fin W := wmod 16
private def emptyMachine : Machine := {Machine.init with stack := [w[77]], mem := fun address =>
  if address = 0 then w[32] else if address = 7 then w[99] else w[0]}
private theorem empty_refs {Q : RefTy} (reference : HRef [P] Q) : Q = P ∧ HEq reference emptyReference := by
  rcases reference with ⟨index, selected⟩
  cases index with
  | zero => cases selected; exact ⟨rfl, HEq.rfl⟩
  | succ index => cases selected
private theorem empty_allocator : Objects.AllocatorRepr emptyHeap emptyBase 8 (wmod 32) emptyMachine := by
  refine ⟨⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩, ⟨by decide, by decide, rfl, ?_⟩, ?_⟩
  · intro Q reference
    obtain ⟨rfl, equal⟩ := empty_refs reference
    cases equal
    decide
  · intro Q reference
    obtain ⟨rfl, equal⟩ := empty_refs reference
    cases equal
    with_unfolding_all decide
  · intro Q S left right different
    obtain ⟨rfl, leftEq⟩ := empty_refs left
    obtain ⟨rfl, rightEq⟩ := empty_refs right
    cases leftEq
    cases rightEq
    exact (different rfl).elim
  · intro A E shape reference
    obtain ⟨rfl, equal⟩ := empty_refs reference
    cases equal
    cases shape
    refine ⟨by with_unfolding_all decide, ?_, ?_⟩
    · intro _
      with_unfolding_all rfl
    · intro index item selected
      with_unfolding_all change ([] : List (HRef [P] R))[index]? = some item at selected
      simp only [List.getElem?_nil] at selected
      cases selected
  · intro name reference
    obtain ⟨different, _⟩ := empty_refs reference
    cases different
  · intro name field Q reference fieldType
    obtain ⟨different, _⟩ := empty_refs reference
    cases different
  · intro address lower
    change 32 ≤ address at lower
    simp only [emptyMachine, if_neg (show address ≠ 0 by omega), if_neg (show address ≠ 7 by omega)]
  · intro Q reference
    obtain ⟨rfl, equal⟩ := empty_refs reference
    cases equal
    with_unfolding_all decide

theorem empty_parent_typed : ∃ fits, NestedMemoryParentResult emptyHeap .uint emptyReference emptyBase 8 (wmod 32) emptyMachine fits := by
  exact ⟨by with_unfolding_all decide, nested_memory_parent_success _ .uint emptyReference emptyBase 8 _ _ empty_allocator _⟩

theorem empty_parent_runtime : ∃ target : Machine,
    run (nestedMemoryParentCode .uint) (emptyMachine.push w[16]) = .ok (target.push w[32]) 0 ∧ target.mem 0 = w[33] ∧ target.mem 32 = w[0] := by
  obtain ⟨fits, base', target, ran, allocated, root, _, _, _, _, _, _, length, _, _⟩ := empty_parent_typed
  let grown := (MVal.copyMToSt emptyHeap (T := .ref P) emptyReference).copyStToM emptyHeap rfl
  have emptyDemand : memoryParentDemand emptyHeap .uint emptyReference = 1 := by with_unfolding_all rfl
  have emptyLength : emptyHeap.len emptyReference .dyn = 0 := by with_unfolding_all rfl
  refine ⟨target, ran, ?_, ?_⟩
  · refine allocated.free.cell.trans ?_
    apply congrArg Word.val
    apply Fin.ext
    change (wmod 32).val + memoryParentDemand emptyHeap .uint emptyReference = 33
    simp only [wmod_def, Nat.mod_eq_of_lt (by decide : 32 < W), emptyDemand]
  ·
    have header : target.mem (base' grown.val.id).val = .val (wmod (grown.heap.len grown.val .dyn)) :=
      (allocated.heap.arrays .dyn grown.val).length rfl
    rw [root, length] at header
    simpa only [wmod_def, Nat.mod_eq_of_lt (by decide : 32 < W), emptyLength, Nat.zero_mod] using header

private def emptyMoved (cursor : Fin W) : Machine := writeMachine emptyMachine 0 (.val cursor)
private theorem empty_moved_allocator (cursor : Fin W) (above : 32 ≤ cursor.val) :
    Objects.AllocatorRepr emptyHeap emptyBase 8 cursor (emptyMoved cursor) := by
  refine ⟨empty_allocator.heap.localWrite 0 (by decide) (.val cursor), ⟨by decide, by omega, rfl, ?_⟩, ?_⟩
  · intro address lower
    exact (upd_other _ _ (by omega : address ≠ 0)).trans (empty_allocator.free.zero address (by change 32 ≤ address; omega))
  · intro Q reference
    have live : (emptyBase reference.id).val + Objects.cells emptyHeap reference ≤ 32 := empty_allocator.live reference
    omega

theorem empty_parent_header_refusal : run (nestedMemoryParentCode .uint) ((emptyMoved wMax).push w[16]) = .revert := by
  exact nested_memory_parent_refusal emptyHeap .uint emptyReference emptyBase 8 wMax (emptyMoved wMax)
    (empty_moved_allocator wMax (by decide)) (by
      have cost : memoryParentDemand emptyHeap .uint emptyReference = 1 := by with_unfolding_all rfl
      rw [cost]
      change ¬ W - 1 + 1 < W
      have positive : 0 < W := W_pos
      omega)

theorem erased_copied_word_rejected (target : Machine) (pointer : Fin W)
    (ran : run (nestedMemoryParentCode .uint) ((machine [wmod 11,wmod 23]).push w[160]) = .ok (target.push w[192]) 0)
    (firstPointer : target.mem 193 = .val pointer) : target.mem (pointer.val + 1) ≠ w[0] := by
  obtain ⟨actual, actualPointer, execution, stored, header, word, _⟩ := pair_copied_words
  rw [ran] at execution
  have sameMemory : target.mem = actual.mem := by
    have pushed : (target.push w[192]).mem = (actual.push w[192]).mem := congrArg Machine.mem (Out.ok.inj execution).1
    exact pushed
  rw [sameMemory] at firstPointer
  have samePointer : pointer = actualPointer := Word.val.inj (firstPointer.symm.trans stored)
  rw [sameMemory, samePointer, word]
  decide

#print axioms certificate_inhabited
#print axioms actual_typed
#print axioms actual_runtime
#print axioms copied_payloads
#print axioms pair_copied_words
#print axioms empty_children_runtime
#print axioms long_copied_words
#print axioms ignored_children_rejected
#print axioms saturated_parent_refusal
#print axioms child_refusal_after_successful_prefix
#print axioms empty_parent_typed
#print axioms empty_parent_runtime
#print axioms empty_parent_header_refusal
#print axioms erased_copied_word_rejected
end Solidity.Backend.MemoryCopies.NestedMemoryParentControls
