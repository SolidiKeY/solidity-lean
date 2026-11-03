import Solidity.Yul.Views.RootDeclarationChecked

namespace Solidity.Yul.Views

theorem ordinaryRootName_facts {scope tr d root} (selected : ordinaryRootName? scope tr d = some root) :
    root.scope = scope ∧ scopeRootName? scope d = some root ∧ plainStateVariable d = true ∧ d.isTransient = tr := by
  unfold ordinaryRootName? at selected
  split at selected
  · rename_i guard
    simp only [Bool.and_eq_true,beq_iff_eq] at guard
    have name := Option.some.inj selected
    subst root
    refine ⟨guard.1.1.2,?_,guard.1.2,guard.2⟩
    unfold scopeRootName?
    simp only [guard.1.1.1,guard.1.1.2,beq_self_eq_true,Bool.and_self,if_true]
  · cases selected

theorem scopeRootName_lookup {scope root} (sameScope : root.scope = scope) (d : Source.Decl) :
    (d.kind == .stateVar && d.scope == root.scope && d.name == root.name) = true ↔ scopeRootName? scope d = some root := by
  cases root with
  | mk rootScope name =>
    cases sameScope
    simp only [scopeRootName?,Bool.and_eq_true,beq_iff_eq]
    split
    · rename_i guard
      simp only [Option.some.injEq,Source.DeclName.mk.injEq]
      exact ⟨fun h => ⟨h.1.2,h.2⟩,fun h => ⟨guard,h.2⟩⟩
    · rename_i guard
      constructor
      · intro h
        exact False.elim (guard h.1)
      · intro h
        cases h

/-- A checked unique optional declaration key identifies the actual first
lookup target. This is a list theorem, not an assumed layout/view law. -/
theorem find_unique_key {α β} (key : α → Option β) (pred : α → Bool) (target : α) (id : β)
    (agrees : ∀ x, pred x = true ↔ key x = some id) (xs : List α)
    (distinct : (xs.filterMap key).Nodup) (member : target ∈ xs) (selected : key target = some id) :
    xs.find? pred = some target := by
  induction xs with
  | nil => cases member
  | cons head tail ih =>
    have tailDistinct : (tail.filterMap key).Nodup := by
      cases found : key head with
      | none => simpa only [List.filterMap_cons,found] using distinct
      | some value => exact (List.nodup_cons.mp (by simpa only [List.filterMap_cons,found] using distinct)).2
    rcases List.mem_cons.mp member with same | rest
    · subst head
      simp only [List.find?_cons,(agrees target).mpr selected]
    · cases test : pred head with
      | false =>
        simp only [List.find?_cons,test]
        exact ih tailDistinct rest
      | true =>
        have first := (agrees head).mp test
        have absent : id ∉ tail.filterMap key :=
          (List.nodup_cons.mp (by simpa only [List.filterMap_cons,first] using distinct)).1
        exact False.elim (absent (List.mem_filterMap.mpr ⟨target,rest,selected⟩))

/-- Selected ordinary metadata identifies the ACTUAL declaration, including
its ordinary-mutability and bank facts, rather than an arbitrary matching name. -/
theorem ordinaryRootNames_lookup {E scope tr} (distinct : (allScopeRootNames E scope).Nodup)
    (root : Source.DeclName) (member : root ∈ ordinaryRootNames E scope tr) :
    ∃ d, d ∈ E.decls ∧ E.declOf .stateVar root = some d ∧
      ordinaryRootName? scope tr d = some root ∧ plainStateVariable d = true ∧ d.isTransient = tr := by
  obtain ⟨d,inEnv,selected⟩ := List.mem_filterMap.mp member
  obtain ⟨sameScope,key,plain,bank⟩ := ordinaryRootName_facts selected
  have found : E.declOf .stateVar root = some d :=
    find_unique_key (scopeRootName? scope) _ d root
      (fun x => scopeRootName_lookup sameScope x) E.decls distinct inEnv key
  exact ⟨d,inEnv,found,selected,plain,bank⟩

/-- Actual source bank lookup follows from computed declaration uniqueness. -/
theorem ordinaryRootNames_bank {E scope tr} (distinct : (allScopeRootNames E scope).Nodup)
    (root : Source.DeclName) (member : root ∈ ordinaryRootNames E scope tr) :
    E.transientRoot ⟨root,[]⟩ = tr := by
  obtain ⟨d,_,found,_,_,bank⟩ := ordinaryRootNames_lookup distinct root member
  simp only [Source.Env.transientRoot,found,Option.map_some,Option.getD_some,bank]

theorem CheckedRootDeclarations.bank_agreement {E ds d scope tr a origin}
    (r : @CheckedRootDeclarations E ds d scope tr a origin)
    (c : ScalarPath E.layout (E.lay a)) (member : c ∈ r.registrations) : E.transientRoot c.path = tr := by
  have rootMember := ((d.pack_spec r.distinct _ _ _ _ r.packed).2.2.2 c member).2.2
  rw [r.ordered] at rootMember
  exact ordinaryRootNames_bank r.sourceDistinct c.path.root rootMember

end Solidity.Yul.Views
