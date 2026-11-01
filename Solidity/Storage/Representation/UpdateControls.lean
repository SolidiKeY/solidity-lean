import Solidity.Storage.Representation.Members
import Solidity.Storage.Representation.Controls

/-! Independent positive, negative and combined update/frame controls. -/
namespace Solidity.Storage.Representation.UpdateControls

private def seven : PrimTy.uint.Denote := ⟨7, by decide⟩
private def nine : PrimTy.uint.Denote := ⟨9, by decide⟩

private def zero : PrimTy.uint.Denote := ⟨0, by decide⟩

/-- Zero fallback support is not inferred from a nonzero custom default. -/
theorem zero_mapping_default :
    ValueRep (.map (K := .uint) SMap.nil (.prim zero)) (.map .word) (.root 0) (fun _ => zero) ∧
      (SVal.map (K := .uint) SMap.nil (.prim zero)).find (.key nine .nil) = some (.prim zero) := by
  constructor
  · apply ValueRep.mapping
    · exact .scalar .uint
    · intro k
      simp only [SMap.toList_nil, Semantics.lookupBy, Option.getD_none]
      exact .scalar zero _ _ rfl
  · rw [SVal.find_key, SMap.toList_nil]
    rfl

/-- A scalar source save and word read agree, with a distinct framed scalar. -/
theorem scalar_combination :
    ValueRep (.prim seven) .word (.root 1)
      (write (fun _ => seven) (.root 0) nine) ∧
    ValueRep (.prim nine) .word (.root 0)
      (write (fun _ => seven) (.root 0) nine) := by
  constructor
  · exact scalar_frame (.scalar seven _ _ rfl) (by decide) nine
  · exact (scalar_save seven nine (.root 0) (fun _ => seven)).2

/-- The general APIs construct a nested saved representation and its source read. -/
theorem nested_save_combination :
    ∃ (start changed : SVal (.ref (.mapping .bool (.ref (.mapping .bool Ty.uint)))) )
      (w : Store),
      start.save (.key (K := .bool) true (.key (K := .bool) false .nil)) (.prim nine) = some changed ∧
      changed.find (.key (K := .bool) true (.key (K := .bool) false .nil)) = some (.prim nine) ∧
      changed.find (.key (K := .bool) true (.key (K := .bool) true .nil)) = some (.prim seven) ∧
      changed.find (.key (K := .bool) false (.key (K := .bool) true .nil)) = some (.prim seven) ∧
      ValueRep changed (.map (.map .word)) (.root 0) w := by
  let inner : SVal (.ref (.mapping .bool Ty.uint)) := .map .nil (.prim seven)
  let start : SVal (.ref (.mapping .bool (.ref (.mapping .bool Ty.uint)))) := .map .nil inner
  have old : ValueRep start (.map (.map .word)) (.root 0) (fun _ => seven) := by
    apply ValueRep.mapping
    · exact .mapping .bool (.scalar .uint)
    · intro k
      simp only [SMap.toList_nil, Semantics.lookupBy, Option.getD_none]
      apply ValueRep.mapping
      · exact .scalar .uint
      · intro q
        simp only [SMap.toList_nil, Semantics.lookupBy, Option.getD_none]
        exact .scalar seven _ _ rfl
  have innerOld : ValueRep inner (.map .word) (.hash (keyWord (p := .bool) true) (.root 0) 0)
      (fun _ => seven) := by
    apply ValueRep.mapping
    · exact .scalar .uint
    · intro q
      simp only [SMap.toList_nil, Semantics.lookupBy, Option.getD_none]
      exact .scalar seven _ _ rfl
  have fresh : ValueRep (.prim nine) .word
      (.hash (keyWord (p := .bool) false) (.hash (keyWord (p := .bool) true) (.root 0) 0) 0) (fun _ => nine) :=
    .scalar nine _ _ rfl
  let innerChanged : SVal (.ref (.mapping .bool Ty.uint)) :=
    .map (.ofList (Semantics.setBy false (.prim nine)
      (SMap.nil (K := .bool) (V := Ty.uint)).toList)) (.prim seven)
  let innerWords : Store := patch (fun _ => seven) (fun _ => nine) .word
    (.hash (keyWord (p := .bool) false) (.hash (keyWord (p := .bool) true) (.root 0) 0) 0)
  let changed : SVal (.ref (.mapping .bool (.ref (.mapping .bool Ty.uint)))) :=
    .map (.ofList (Semantics.setBy true innerChanged
      (SMap.nil (K := .bool) (V := .ref (.mapping .bool Ty.uint))).toList)) inner
  let words : Store := patch (fun _ => seven) innerWords (.map .word)
    (.hash (keyWord (p := .bool) true) (.root 0) 0)
  have innerSaved : ValueRep innerChanged (.map .word)
      (.hash (keyWord (p := .bool) true) (.root 0) 0) innerWords :=
    mapping_save innerOld false fresh
  have sourceInner : inner.save (.key (K := .bool) false .nil) (.prim nine) = some innerChanged :=
    mapping_source_save (SMap.nil (K := .bool) (V := Ty.uint)) (.prim seven) (.prim nine) false
  have sourceSelected : ((Semantics.lookupBy true
      (SMap.nil (K := .bool) (V := .ref (.mapping .bool Ty.uint))).toList).getD inner).save
      (.key (K := .bool) false .nil) (.prim nine) = some innerChanged := by
    simpa only [SMap.toList_nil, Semantics.lookupBy, Option.getD_none] using sourceInner
  have combined : start.save (.key (K := .bool) true (.key (K := .bool) false .nil)) (.prim nine) =
      some changed ∧ ValueRep changed (.map (.map .word)) (.root 0) words :=
    mapping_path_save old true (.key (K := .bool) false .nil) (.prim nine)
    sourceSelected innerSaved
  have d1 : changed.find (.key (K := .bool) true (.key (K := .bool) true .nil)) = some (.prim seven) := (source_frame (q := .key (K := .bool) true (.key (K := .bool) true .nil)) combined.1
      (.keyIn (K := .bool) true (.key .nil .nil Bool.false_ne_true))).trans
    (show start.find (.key (K := .bool) true (.key (K := .bool) true .nil)) = some (.prim seven) by
      simp only [start, inner, SVal.find_key, SVal.find_nil, SMap.toList_nil, Semantics.lookupBy])
  have d2 : changed.find (.key (K := .bool) false (.key (K := .bool) true .nil)) = some (.prim seven) := (source_frame (q := .key (K := .bool) false (.key (K := .bool) true .nil)) combined.1
      (.key (.key (K := .bool) false .nil) (.key (K := .bool) true .nil) (Ne.symm Bool.false_ne_true))).trans
    (show start.find (.key (K := .bool) false (.key (K := .bool) true .nil)) = some (.prim seven) by
      simp only [start, inner, SVal.find_key, SVal.find_nil, SMap.toList_nil, Semantics.lookupBy])
  exact ⟨start, _, _, combined.1, SVal.find_save_same start _ _ combined.1, d1, d2, combined.2⟩

/-- A heterogeneous source struct save preserves its mapping member's default. -/
theorem wallet_save_combination :
    ∃ (changed : SVal (.ref (.struct "Wallet"))) (w : Store),
      Controls.wallet.save (.field (f := "owner") (by rfl) .nil) (.prim zero) = some changed ∧
      changed.find (.field (f := "owner") (by rfl) .nil) = some (.prim zero) ∧
      changed.find (.field (f := "stash") (by rfl) (.key seven .nil)) = some (.prim nine) ∧
      ValueRep changed (.strct [.word, .map .word]) (.root 0) w := by
  obtain ⟨t, i, _, shape, update⟩ := struct_save Controls.wallet_represented
    (f := "owner") (T := Ty.uint) (by rfl)
  cases shape
  obtain ⟨saved, represented⟩ := update (.prim zero) (fun _ => zero) (.scalar zero _ _ rfl)
  refine ⟨_, _, saved, ?_, ?_, represented⟩
  · rfl
  · change (SVal.map (K := .uint) SMap.nil (SVal.prim nine)).find (.key seven .nil) = _
    rw [SVal.find_key, SMap.toList_nil]
    rfl

/-- Same-address writes do not satisfy a disjoint frame conclusion. -/
theorem alias_rejects_frame :
    ¬ ValueRep (.prim seven) .word (.root 0)
      (write (fun _ => seven) (.root 0) nine) := by
  intro h
  have eq : write (fun _ => seven) (.root 0) nine (.root 0) = PrimTy.toWord seven := scalar_read h
  rw [write_same] at eq
  have bad : (9 : Int) = 7 := congrArg Subtype.val eq
  omega

/-- Aliasing remains a real obstruction below nested mapping/array paths. -/
theorem nested_alias_rejects_frame (l : Loc) (k : Nat) :
    ¬ ValueRep (.prim seven) .word (.hash k (.data l 0) 0)
      (write (fun _ => seven) (.hash k (.data l 0) 0) nine) := by
  intro h
  have eq : write (fun _ => seven) (.hash k (.data l 0) 0) nine
      (.hash k (.data l 0) 0) = PrimTy.toWord seven := scalar_read h
  rw [write_same] at eq
  have bad : (9 : Int) = 7 := congrArg Subtype.val eq
  omega

/-- Signed keys normalize to the full two's-complement word. -/
theorem negative_key_word :
    keyWord (p := .int) ⟨-1, by decide⟩ = 2 ^ 256 - 1 := by
  have hn : ¬ (0 : Int) ≤ -1 := by omega
  simp only [keyWord, PrimTy.toWord, hn, ↓reduceDIte]
  have hp : 0 < (2 ^ 256 : Nat) := Nat.pow_pos (by decide)
  omega

/-- info: 'Solidity.Storage.Representation.UpdateControls.scalar_combination' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms scalar_combination
/-- info: 'Solidity.Storage.Representation.UpdateControls.nested_save_combination' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms nested_save_combination
/-- info: 'Solidity.Storage.Representation.UpdateControls.wallet_save_combination' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms wallet_save_combination
/-- info: 'Solidity.Storage.Representation.UpdateControls.alias_rejects_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms alias_rejects_frame
/-- info: 'Solidity.Storage.Representation.UpdateControls.nested_alias_rejects_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms nested_alias_rejects_frame
/-- info: 'Solidity.Storage.Representation.UpdateControls.negative_key_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms negative_key_word
/-- info: 'Solidity.Storage.Representation.ValueRep.congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ValueRep.congr
/-- info: 'Solidity.Storage.Representation.mapping_save' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms mapping_save
/-- info: 'Solidity.Storage.Representation.FieldsRep.set' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FieldsRep.set
/-- info: 'Solidity.Storage.Representation.keyWord_inj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms keyWord_inj
/-- info: 'Solidity.Storage.Representation.word_normalized' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms word_normalized
end Solidity.Storage.Representation.UpdateControls
