import Solidity.Storage.Representation.Updates

/-! Member observations retain the committed source's first-name lookup. -/
namespace Solidity.Storage.Representation

theorem FieldsRep.get {fs : List (Name × Ty)} {vs : SFields fs}
    {ts : List STy} {l : Loc} {w : Store} (h : FieldsRep vs ts l w)
    {f : Name} {T : Ty} (member : Semantics.lookupBy f fs = some T) :
    ∃ t i, ts[i]? = some t ∧
      ValueRep (vs.get member) t (l.add (STy.sizes (ts.take i))) w := by
  induction fs generalizing ts l with
  | nil => simp only [Semantics.lookupBy] at member; cases member
  | cons hd rest ih =>
    obtain ⟨g, U⟩ := hd
    cases h with
    | cons v tail t ts l w head tailRep =>
      by_cases eq : f = g
      · have ht : U = T := SFields.lookupBy_cons_pos eq member
        subst U
        refine ⟨t, 0, rfl, ?_⟩
        simpa only [SFields.get_cons, dif_pos eq, List.take_zero, STy.sizes, Loc.add_zero] using head
      · obtain ⟨u, i, hi, hv⟩ := ih tailRep (SFields.lookupBy_cons_neg eq member)
        refine ⟨u, i + 1, hi, ?_⟩
        simpa only [SFields.get_cons, dif_neg eq, List.take_succ_cons, STy.sizes,
          Loc.add_add] using hv

private theorem tail_head_disjoint {t : STy} {ts : List STy} {l x : Loc}
    (tail : Occ (.strct ts) (l.add t.size) x) (head : Occ t l x) : False := by
  cases tail with
  | @field _ i u _ _ hi hx =>
    have ht : Occ u (l.add (STy.sizes ((t :: ts).take (i + 1)))) x := by
      simpa only [List.take_succ_cons, STy.sizes, Loc.add_add] using hx
    have hh : Occ t (l.add (STy.sizes ((t :: ts).take 0))) x := by
      simpa only [List.take_zero, STy.sizes, Loc.add_zero] using head
    exact occ_fields_disjoint (fs := t :: ts) (i := i + 1) (i' := 0)
      hi rfl (Nat.succ_ne_zero i) ht hh

/-- Replacing the source member and its footprint preserves the whole field store. -/
theorem FieldsRep.set {fs : List (Name × Ty)} {vs : SFields fs}
    {ts : List STy} {l : Loc} {w : Store} (h : FieldsRep vs ts l w)
    {f : Name} {T : Ty} (member : Semantics.lookupBy f fs = some T) :
    ∃ t i, ts[i]? = some t ∧ TypeRep T t ∧ ∀ (new : SVal T) (replacement : Store),
      ValueRep new t (l.add (STy.sizes (ts.take i))) replacement →
      FieldsRep (vs.set member new) ts l
        (patch w replacement t (l.add (STy.sizes (ts.take i)))) := by
  induction fs generalizing ts l with
  | nil => simp only [Semantics.lookupBy] at member; cases member
  | cons hd rest ih =>
    obtain ⟨g, U⟩ := hd
    cases h with
    | cons v tail t ts l w head tailRep =>
      by_cases eq : f = g
      · have ht : U = T := SFields.lookupBy_cons_pos eq member
        subst U
        refine ⟨t, 0, rfl, head.type, ?_⟩
        intro new replacement fresh
        simp only [SFields.set_cons, dif_pos eq, List.take_zero, STy.sizes,
          Loc.add_zero] at fresh ⊢
        apply FieldsRep.cons
        · exact fresh.replace
        · apply tailRep.congr
          intro x hx
          exact patch_outside w replacement t l x (tail_head_disjoint hx)
      · obtain ⟨u, i, hi, shape, update⟩ := ih tailRep (SFields.lookupBy_cons_neg eq member)
        refine ⟨u, i + 1, hi, shape, ?_⟩
        intro new replacement fresh
        simp only [SFields.set_cons, dif_neg eq, List.take_succ_cons, STy.sizes] at fresh ⊢
        apply FieldsRep.cons
        · apply head.patch_frame
          intro x hx hy
          have hh : Occ t (l.add (STy.sizes ((t :: ts).take 0))) x := by
            simpa only [List.take_zero, STy.sizes, Loc.add_zero] using hx
          exact occ_fields_disjoint (fs := t :: ts) (i := 0) (i' := i + 1)
            rfl hi (Nat.zero_ne_add_one i) hh hy
        · have fresh' : ValueRep new u ((l.add t.size).add (STy.sizes (ts.take i))) replacement := by
            simpa only [Loc.add_add] using fresh
          simpa only [Loc.add_add] using update new replacement fresh'

/-- Source member reads and existing layout location agree at the leaf. -/
theorem struct_member_read {s f : Name} {T : Ty} {fs : SFields (Semantics.structDef s)}
    {ts : List STy} {l : Loc} {w : Store}
    (h : ValueRep (.struct (s := s) fs) (.strct ts) l w)
    (member : Semantics.lookupBy f (Semantics.structDef s) = some T) :
    ∃ t i, ts[i]? = some t ∧
      STy.locate (.strct ts) l [.field i] =
        some (t, l.add (STy.sizes (ts.take i))) ∧
      (SVal.struct fs).find (.field member .nil) = some (fs.get member) ∧
      ValueRep (fs.get member) t (l.add (STy.sizes (ts.take i))) w := by
  cases h with
  | strct _ _ _ _ fields =>
    obtain ⟨t, i, hi, hv⟩ := fields.get member
    refine ⟨t, i, hi, ?_, ?_, hv⟩
    · simp only [STy.locate, hi]
    · rw [SVal.find_field, SVal.find_nil]

/-- Exact source member-save equation, independent of the word update. -/
theorem struct_source_save {s f : Name} {T : Ty}
    (fs : SFields (Semantics.structDef s))
    (member : Semantics.lookupBy f (Semantics.structDef s) = some T) (new : SVal T) :
    (SVal.struct (s := s) fs).save (.field member .nil) new =
      some (.struct (s := s) (fs.set member new)) := by
  rw [SVal.save_eq_saveM, SVal.saveM, saveM_nil]
  rfl

/-- A source member replacement has a whole-value representation after patching. -/
theorem struct_save {s f : Name} {T : Ty} {fs : SFields (Semantics.structDef s)}
    {ts : List STy} {l : Loc} {w : Store}
    (old : ValueRep (.struct (s := s) fs) (.strct ts) l w)
    (member : Semantics.lookupBy f (Semantics.structDef s) = some T) :
    ∃ t i, ts[i]? = some t ∧ TypeRep T t ∧ ∀ (new : SVal T) (replacement : Store),
      ValueRep new t (l.add (STy.sizes (ts.take i))) replacement →
      (SVal.struct (s := s) fs).save (.field member .nil) new =
        some (.struct (s := s) (fs.set member new)) ∧
      ValueRep (.struct (s := s) (fs.set member new)) (.strct ts) l
        (patch w replacement t (l.add (STy.sizes (ts.take i)))) := by
  cases old with
  | strct _ _ _ _ fields =>
    obtain ⟨t, i, hi, shape, update⟩ := fields.set member
    exact ⟨t, i, hi, shape, fun new replacement fresh =>
      ⟨struct_source_save fs member new, .strct _ _ _ _ (update new replacement fresh)⟩⟩

/-- Replacing a member's footprint preserves every distinct represented member. -/
theorem member_patch_frame {T : Ty} {v : SVal T} {fs : List STy}
    {i j : Nat} {t u : STy} {l : Loc} {w new : Store}
    (hi : fs[i]? = some t) (hj : fs[j]? = some u) (different : i ≠ j)
    (h : ValueRep v t (l.add (STy.sizes (fs.take i))) w) :
    ValueRep v t (l.add (STy.sizes (fs.take i)))
      (patch w new u (l.add (STy.sizes (fs.take j)))) :=
  h.patch_frame (fun _ hx hy => occ_fields_disjoint hi hj different hx hy)

end Solidity.Storage.Representation
