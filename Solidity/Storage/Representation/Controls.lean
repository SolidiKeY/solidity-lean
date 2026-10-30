import Solidity.Storage.Representation.Model

/-! Inhabited controls for the intrinsic representation relation. -/
namespace Solidity.Storage.Representation.Controls

private def seven : PrimTy.uint.Denote := ⟨7, by decide⟩
private def nine : PrimTy.uint.Denote := ⟨9, by decide⟩
private def two : Semantics.Word := ⟨2, by decide⟩

/-- A real source struct with a mapping member, using the committed schema. -/
def wallet : SVal (.ref (.struct "Wallet")) :=
  .struct (.cons (.prim seven) (.cons (.map .nil (.prim nine)) .nil))

private def walletWords : Store := fun l => if l = .root 0 then seven else nine

theorem wallet_represented :
    ValueRep wallet (.strct [.word, .map .word]) (.root 0) walletWords := by
  apply ValueRep.strct
  apply FieldsRep.cons
  · exact .scalar seven _ _ rfl
  · apply FieldsRep.cons
    · apply ValueRep.mapping
      · exact .scalar .uint
      · intro k
        simp only [SMap.toList_nil, Semantics.lookupBy, Option.getD_none]
        exact .scalar nine _ _ rfl
    · exact .nil _ _

/-- Fixed arrays retain their type-level length. -/
theorem fixed_represented :
    ValueRep (.fixed (.cons (.prim seven) (.cons (.prim seven) .nil)))
      (.sarr .word 2) (.root 0) (fun _ => seven) := by
  apply ValueRep.fixed
  · exact .scalar .uint
  · simp only [SVec.toList_cons, SVec.toList_nil]
    exact .cons _ _ _ _ _ (.scalar seven _ _ rfl)
      (.cons _ _ _ _ _ (.scalar seven _ _ rfl) (.nil _ _ _))

private def arrayWords : Store := fun l => if l = .root 0 then two else seven

/-- A live prefix and a stale shadow slot both have represented words. -/
theorem array_represented :
    ValueRep (.array (.cons (.prim seven) (.cons (.prim seven) .nil))
      (.cons (.prim seven) .nil) (by decide))
      (.darr .word) (.root 0) arrayWords := by
  apply ValueRep.array
  · exact .scalar .uint
  · decide
  · simp only [SVec.toList_cons, SVec.toList_nil, SList.toList_cons, SList.toList_nil,
      List.cons_append, List.nil_append, List.length_cons, List.length_nil]
    decide
  · rfl
  · simp only [SVec.toList_cons, SVec.toList_nil, SList.toList_cons, SList.toList_nil,
      List.cons_append, List.nil_append]
    exact .cons _ _ _ _ _ (.scalar seven _ _ rfl)
      (.cons _ _ _ _ _ (.scalar seven _ _ rfl)
        (.cons _ _ _ _ _ (.scalar seven _ _ rfl) (.nil _ _ _)))

private def inner : SVal (.ref (.mapping .bool Ty.uint)) :=
  .map (.cons false (.prim nine) .nil) (.prim seven)
private def nested : SVal (.ref (.mapping .bool (.ref (.mapping .bool Ty.uint)))) :=
  .map (.cons true inner .nil) (.map .nil (.prim seven))
private def nestedWords : Store := fun l =>
  if l = .hash 0 (.hash 1 (.root 0) 0) 0 then nine else seven

/-- Two levels, an explicit exceptional entry and untouched defaults. -/
theorem nested_represented :
    ValueRep nested (.map (.map .word)) (.root 0) nestedWords := by
  apply ValueRep.mapping
  · exact .mapping .bool (.scalar .uint)
  · intro outer
    cases outer <;>
      simp only [SMap.toList_cons, SMap.toList_nil] <;> apply ValueRep.mapping
    · exact .scalar .uint
    · intro innerKey
      cases innerKey <;>
        simp only [SMap.toList_nil, Semantics.lookupBy, Option.getD_none] <;>
        exact .scalar seven _ _ rfl
    · exact .scalar .uint
    · intro innerKey
      cases innerKey <;>
        simp only [SMap.toList_cons, SMap.toList_nil]
      · exact .scalar nine _ _ rfl
      · exact .scalar seven _ _ rfl

/-- These reads are the existing source semantics, independent of words. -/
theorem nested_source_read : nested.find (.key true (.key false .nil)) = some (.prim nine) := by
  simp only [nested, inner, SVal.find_key, SVal.find_nil, SMap.toList_cons, SMap.toList_nil,
    Semantics.lookupBy, if_true]

theorem nested_source_default : nested.find (.key false (.key false .nil)) = some (.prim seven) := by
  simp only [nested, SVal.find_key, SVal.find_nil, SMap.toList_cons, SMap.toList_nil,
    Semantics.lookupBy, if_neg Bool.false_ne_true]

/-- The exact existing layout boundary is explicit, not a source exclusion. -/
theorem beyond_layout_bound {E : Ty} {n : Nat} (vs : SVec E n) (sh : SList E)
    (hn : n < 2 ^ 256) (t : STy) (l : Loc) (w : Store) (large : lmax < n) :
    ¬ ValueRep (.array vs sh hn) (.darr t) l w := by
  intro h
  cases h with
  | array _ _ _ _ _ _ _ bound _ _ _ => omega

/-- Even empty arrays require the independently fixed element layout. -/
theorem empty_wrong_shape :
    ¬ ValueRep (.fixed (SVec.nil (E := Ty.uint))) (.sarr (.map .word) 0)
      (.root 0) (fun _ => seven) := by
  intro h
  cases h with
  | fixed _ _ _ _ shape _ => cases shape

/-- A representation with the wrong scalar word is rejected. -/
theorem wrong_scalar : ¬ ValueRep (.prim seven) .word (.root 0) (fun _ => nine) := by
  intro h
  have e : nine = PrimTy.toWord seven := scalar_read h
  have bad : (9 : Int) = 7 := congrArg Subtype.val e
  omega

/-- info: 'Solidity.Storage.Representation.Controls.wallet_represented' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms wallet_represented
/-- info: 'Solidity.Storage.Representation.Controls.nested_represented' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms nested_represented
/-- info: 'Solidity.Storage.Representation.Controls.array_represented' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms array_represented
/-- info: 'Solidity.Storage.Representation.Controls.wrong_scalar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms wrong_scalar
end Solidity.Storage.Representation.Controls
