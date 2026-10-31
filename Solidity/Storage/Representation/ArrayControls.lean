import Solidity.Storage.Representation.Arrays

/-! Heterogeneous array observations, writes and header/element controls. -/
namespace Solidity.Storage.Representation.ArrayControls
private def zero : PrimTy.uint.Denote := ⟨0, by decide⟩
private def one : PrimTy.uint.Denote := ⟨1, by decide⟩
private def two : PrimTy.uint.Denote := ⟨2, by decide⟩
private def seven : PrimTy.uint.Denote := ⟨7, by decide⟩
private def nine : PrimTy.uint.Denote := ⟨9, by decide⟩
private def live : SVec Ty.uint 1 := .cons (.prim seven) .nil
private def shadow : SList Ty.uint := .cons (.prim nine) .nil
private def value : SVal (.ref (.array Ty.uint)) := .array live shadow (by decide)
private def words : Store := fun l => if l = .root 0 then one
  else if l = .data (.root 0) 0 then seven else nine

theorem heterogeneous_represented : ValueRep value (.darr .word) (.root 0) words := by
  apply ValueRep.array
  · exact .scalar .uint
  · decide
  · simp only [live, shadow, SVec.toList_cons, SVec.toList_nil, SList.toList_cons,
      SList.toList_nil, List.cons_append, List.nil_append, List.length_cons, List.length_nil]
    decide
  · rfl
  · simp only [live, shadow, SVec.toList_cons, SVec.toList_nil, SList.toList_cons,
      SList.toList_nil, List.cons_append, List.nil_append]
    exact .cons _ _ _ _ _ (.scalar seven _ _ rfl)
      (.cons _ _ _ _ _ (.scalar nine _ _ rfl) (.nil _ _ _))

/-- Word representation, source live read and source stale-slot read agree. -/
theorem distinct_source_reads :
    value.find (.at zero .nil) = some (.prim seven) ∧
    value.find (.at one .nil) = some (.prim nine) ∧
    value.findLive (.at one .nil) = none := by
  constructor
  · simp only [value, SVal.find_at, live, shadow, SVec.toList_cons, SVec.toList_nil,
      SList.toList_cons, SList.toList_nil, List.cons_append, List.nil_append]
    rfl
  · constructor
    · simp only [value, SVal.find_at, live, shadow, SVec.toList_cons, SVec.toList_nil,
        SList.toList_cons, SList.toList_nil, List.cons_append, List.nil_append]
      rfl
    · exact array_live_missing live shadow _ one .nil (by decide)

/-- Updating the live slot preserves a distinct shadow slot and the header. -/
theorem update_preserves_shadow :
    ∃ (changed : SVal (.ref (.array Ty.uint))) (w : Store),
      value.save (.at zero .nil) (.prim zero) = some changed ∧
      changed.find (.at zero .nil) = some (.prim zero) ∧
      changed.find (.at one .nil) = some (.prim nine) ∧
      (w (.root 0)).val = 1 ∧ ValueRep changed (.darr .word) (.root 0) w := by
  have found : (live.toList ++ shadow.toList)[zero.val.toNat]? = some (.prim seven) := by
    simp only [live, shadow, SVec.toList_cons, SVec.toList_nil, SList.toList_cons,
      SList.toList_nil, List.cons_append, List.nil_append]
    rfl
  have fresh : ValueRep (.prim zero) .word (.data (.root 0) (zero.val.toNat * STy.word.size))
      (fun _ => zero) := .scalar zero _ _ rfl
  obtain ⟨saved, represented⟩ := array_path_save heterogeneous_represented zero .nil (.prim zero)
    (.prim seven) (.prim zero) found (by rfl) fresh
  refine ⟨_, _, saved, SVal.find_save_same value _ _ saved, ?_, ?_, represented⟩
  · exact (source_frame (q := .at one .nil) saved
      (.at .nil .nil (by decide : zero ≠ one))).trans distinct_source_reads.2.1
  · rw [array_header_patch_frame]
    rfl

/-- Empty array defaults have a zero length and no occupied elements. -/
theorem empty_default_represented :
    ValueRep (.array (SVec.nil (E := Ty.uint)) SList.nil (by decide))
      (.darr .word) (.root 0) (fun _ => zero) := by
  apply ValueRep.array
  · exact .scalar .uint
  · decide
  · simp only [SVec.toList_nil, SList.toList_nil, List.nil_append, List.length_nil]
    exact Nat.zero_le _
  · rfl
  · simp only [SVec.toList_nil, SList.toList_nil, List.nil_append]
    exact .nil _ _ _

/-- Failure past the retained extent is independent of word contents. -/
theorem beyond_extent : value.find (.at two .nil) = none ∧
    value.save (.at two .nil) (.prim zero) = none := by
  constructor
  · apply array_missing live shadow _ two
    simp only [live, shadow, SVec.toList_cons, SVec.toList_nil, SList.toList_cons,
      SList.toList_nil, List.cons_append, List.nil_append, List.length_cons, List.length_nil]
    decide
  · apply array_save_missing live shadow _ two .nil (.prim zero)
    simp only [live, shadow, SVec.toList_cons, SVec.toList_nil, SList.toList_cons,
      SList.toList_nil, List.cons_append, List.nil_append, List.length_cons, List.length_nil]
    decide

/-- Positive live-read success is linked to representation, not just retention. -/
theorem live_success_and_representation :
    value.findLive (.at zero .nil) = some (.prim seven) ∧
      ValueRep (.prim seven) .word (.data (.root 0) 0) words := by
  apply array_live_read heterogeneous_represented
  simp only [live, SVec.toList_cons, SVec.toList_nil]
  rfl

/-- A stale alias may write its retained slot while live reads still reject it. -/
theorem shadow_write_combination :
    ∃ (changed : SVal (.ref (.array Ty.uint))) (w : Store),
      value.save (.at one .nil) (.prim zero) = some changed ∧
      changed.find (.at one .nil) = some (.prim zero) ∧
      changed.find (.at zero .nil) = some (.prim seven) ∧
      changed.findLive (.at one .nil) = none ∧
      (w (.root 0)).val = 1 ∧ ValueRep changed (.darr .word) (.root 0) w := by
  have found : (live.toList ++ shadow.toList)[one.val.toNat]? = some (.prim nine) := by
    simp only [live, shadow, SVec.toList_cons, SVec.toList_nil, SList.toList_cons,
      SList.toList_nil, List.cons_append, List.nil_append]
    rfl
  have fresh : ValueRep (.prim zero) .word (.data (.root 0) (one.val.toNat * STy.word.size))
      (fun _ => zero) := .scalar zero _ _ rfl
  obtain ⟨saved, represented⟩ := array_path_save heterogeneous_represented one .nil (.prim zero)
    (.prim nine) (.prim zero) found (by rfl) fresh
  refine ⟨_, _, saved, SVal.find_save_same value _ _ saved, ?_, ?_, ?_, represented⟩
  · exact (source_frame (q := .at zero .nil) saved
      (.at .nil .nil (by decide : one ≠ zero))).trans distinct_source_reads.1
  · rw [SVal.findLive_eq_findLiveM, SVal.findLiveM, SVec.toList_ofList]
    simp only [live, shadow, SVec.toList_cons, SVec.toList_nil, SList.toList_cons,
      SList.toList_nil, List.cons_append, List.nil_append]
    rfl
  · rw [array_header_patch_frame]
    rfl

private def fixedSlots : SVec Ty.uint 2 := .cons (.prim seven) (.cons (.prim nine) .nil)
private def fixedWords : Store := fun l => if l = .root 0 then seven else nine

theorem fixed_heterogeneous_represented :
    ValueRep (.fixed fixedSlots) (.sarr .word 2) (.root 0) fixedWords := by
  apply ValueRep.fixed
  · exact .scalar .uint
  · simp only [fixedSlots, SVec.toList_cons, SVec.toList_nil]
    exact .cons _ _ _ _ _ (.scalar seven _ _ rfl)
      (.cons _ _ _ _ _ (.scalar nine _ _ rfl) (.nil _ _ _))

theorem fixed_update_combination :
    ∃ (changed : SVal (.ref (.fixed Ty.uint 2))) (w : Store),
      (SVal.fixed fixedSlots).save (.atF one .nil) (.prim zero) = some changed ∧
      changed.find (.atF one .nil) = some (.prim zero) ∧
      changed.find (.atF zero .nil) = some (.prim seven) ∧
      ValueRep changed (.sarr .word 2) (.root 0) w := by
  have found : fixedSlots.toList[one.val.toNat]? = some (.prim nine) := by
    simp only [fixedSlots, SVec.toList_cons, SVec.toList_nil]
    rfl
  have fresh : ValueRep (.prim zero) .word ((Loc.root 0).add (one.val.toNat * STy.word.size))
      (fun _ => zero) := .scalar zero _ _ rfl
  obtain ⟨saved, represented⟩ := fixed_path_save fixed_heterogeneous_represented one .nil
    (.prim zero) (.prim nine) (.prim zero) found (by rfl) fresh
  refine ⟨_, _, saved, SVal.find_save_same _ _ _ saved, ?_, represented⟩
  exact (source_frame (q := .atF zero .nil) saved
    (.atF .nil .nil (by decide : one ≠ zero))).trans (by
      simp only [SVal.find_atF, fixedSlots, SVec.toList_cons, SVec.toList_nil]
      rfl)

/-- The committed source fixed-array default has represented zero words. -/
theorem fixed_default_represented :
    ValueRep (SVal.dflt (.ref (.fixed Ty.uint 2))) (.sarr .word 2) (.root 0) (fun _ => zero) := by
  change ValueRep (.fixed (SVec.replicate (.prim zero) 2)) (.sarr .word 2) (.root 0) (fun _ => zero)
  apply ValueRep.fixed
  · exact .scalar .uint
  · simp only [SVec.toList_replicate, List.replicate_succ, List.replicate_zero]
    exact .cons _ _ _ _ _ (.scalar zero _ _ rfl)
      (.cons _ _ _ _ _ (.scalar zero _ _ rfl) (.nil _ _ _))

theorem fixed_out_of_range :
    (SVal.fixed fixedSlots).find (.atF two .nil) = none ∧
    (SVal.fixed fixedSlots).save (.atF two .nil) (.prim zero) = none :=
  ⟨fixed_missing fixedSlots two (by decide),
   fixed_save_missing fixedSlots two .nil (.prim zero) (by decide)⟩

/-- Header zeroing preserves the retained nonzero slots, instead of clearing them. -/
theorem repartition_combination :
    ValueRep (.array (SVec.nil (E := Ty.uint))
      (.cons (.prim seven) (.cons (.prim nine) .nil)) (by decide)) (.darr .word)
      (.root 0) (write words (.root 0) (lengthWord 0 (by decide))) := by
  apply array_repartition heterogeneous_represented
  simp only [live, shadow, SVec.toList_nil, SVec.toList_cons, SList.toList_cons,
    SList.toList_nil, List.nil_append, List.cons_append]

private def nestedLive : SVec (.ref (.fixed Ty.uint 2)) 1 := .cons (.fixed fixedSlots) .nil
private def nestedValue : SVal (.ref (.array (.ref (.fixed Ty.uint 2)))) :=
  .array nestedLive .nil (by decide)

/-- Nested fixed-element layout under the dynamic data origin is inhabited. -/
theorem nested_array_represented :
    ValueRep nestedValue (.darr (.sarr .word 2)) (.root 0) words := by
  apply ValueRep.array
  · exact .fixed 2 (.scalar .uint)
  · decide
  · simp only [nestedLive, SVec.toList_cons, SVec.toList_nil, SList.toList_nil,
      List.cons_append, List.nil_append, List.length_cons, List.length_nil]
    decide
  · rfl
  · simp only [nestedLive, SVec.toList_cons, SVec.toList_nil, SList.toList_nil,
      List.cons_append, List.nil_append]
    apply ElementsRep.cons
    · apply ValueRep.fixed
      · exact .scalar .uint
      · simp only [fixedSlots, SVec.toList_cons, SVec.toList_nil]
        exact .cons _ _ _ _ _ (.scalar seven _ _ rfl)
          (.cons _ _ _ _ _ (.scalar nine _ _ rfl) (.nil _ _ _))
    · exact .nil _ _ _

/-- Actual composition of two array source saves and two represented updates. -/
theorem nested_array_save_combination :
    ∃ (changed : SVal (.ref (.array (.ref (.fixed Ty.uint 2))))) (w : Store),
      nestedValue.save (.at zero (.atF one .nil)) (.prim zero) = some changed ∧
      changed.find (.at zero (.atF one .nil)) = some (.prim zero) ∧
      ValueRep changed (.darr (.sarr .word 2)) (.root 0) w := by
  have foundOuter : (nestedLive.toList ++ (SList.nil (E := .ref (.fixed Ty.uint 2))).toList)[zero.val.toNat]? = some (.fixed fixedSlots) := by
    simp only [nestedLive, SVec.toList_cons, SVec.toList_nil, SList.toList_nil,
      List.cons_append, List.nil_append]
    rfl
  have child : ValueRep (.fixed fixedSlots) (.sarr .word 2) (.data (.root 0) 0) words := by
    apply ValueRep.fixed
    · exact .scalar .uint
    · simp only [fixedSlots, SVec.toList_cons, SVec.toList_nil]
      exact .cons _ _ _ _ _ (.scalar seven _ _ rfl)
        (.cons _ _ _ _ _ (.scalar nine _ _ rfl) (.nil _ _ _))
  have foundInner : fixedSlots.toList[one.val.toNat]? = some (.prim nine) := by
    simp only [fixedSlots, SVec.toList_cons, SVec.toList_nil]
    rfl
  have fresh : ValueRep (.prim zero) .word
      ((Loc.data (.root 0) 0).add (one.val.toNat * STy.word.size)) (fun _ => zero) :=
    .scalar zero _ _ rfl
  obtain ⟨innerSaved, innerRepresented⟩ := fixed_path_save child one .nil (.prim zero)
    (.prim nine) (.prim zero) foundInner (by rfl) fresh
  obtain ⟨saved, represented⟩ := array_path_save nested_array_represented zero (.atF one .nil)
    (.prim zero) (.fixed fixedSlots) (.fixed (fixedSlots.set one.val.toNat (.prim zero)))
    foundOuter innerSaved innerRepresented
  exact ⟨_, _, saved, SVal.find_save_same nestedValue _ _ saved, represented⟩

/-- info: 'Solidity.Storage.Representation.array_path_save' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms array_path_save
/-- info: 'Solidity.Storage.Representation.fixed_path_save' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms fixed_path_save
/-- info: 'Solidity.Storage.Representation.array_repartition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms array_repartition
/-- info: 'Solidity.Storage.Representation.ArrayControls.update_preserves_shadow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms update_preserves_shadow
/-- info: 'Solidity.Storage.Representation.ArrayControls.fixed_update_combination' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms fixed_update_combination
/-- info: 'Solidity.Storage.Representation.ArrayControls.nested_array_save_combination' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms nested_array_save_combination
/-- info: 'Solidity.Storage.Representation.ArrayControls.empty_default_represented' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms empty_default_represented
/-- info: 'Solidity.Storage.Representation.ArrayControls.beyond_extent' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms beyond_extent
/-- info: 'Solidity.Storage.Representation.ArrayControls.shadow_write_combination' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms shadow_write_combination
/-- info: 'Solidity.Storage.Representation.array_live_read' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms array_live_read
end Solidity.Storage.Representation.ArrayControls
