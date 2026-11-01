import Solidity.Yul.Views.DynamicHeaderSelection

namespace Solidity.Yul.Views

theorem ComputedStorage.header_found {E ds d active a} (r : @ComputedStorage E ds d active a)
    (root : Source.DeclName) (cursor : Nat)
    (found : r.headerTrace.find? (fun entry => entry.1 == root) = some (root,cursor)) :
    ∃ h : DynamicHeader E root cursor, r.header? root = some ⟨cursor,h⟩ := by
  obtain ⟨h,_⟩ := r.header_present root cursor (List.mem_of_find?_eq_some found)
  refine ⟨h,?_⟩
  unfold ComputedStorage.header?
  rw [found]
  dsimp only [Bind.bind,Option.bind]
  rw [dif_pos h.declared,dif_pos h.bounded]

theorem DynamicHeader.offset {E root cursor} (h : DynamicHeader E root cursor) (a : Roadmap.Address) :
    (h.registration a).field.offset = 0 := by
  change ((dynamicHeaderSeed E).position (roundSlot cursor)).start%32 = 0
  rw [dynamic_header_start]
  exact (roundSlot_spec cursor).2.2

theorem DynamicHeader.width {E root cursor} (h : DynamicHeader E root cursor) (a : Roadmap.Address) :
    (h.registration a).field.width = 32 := rfl

theorem finiteSeparated_pair {D L} (cs : List (ScalarPath D L)) (sep : finiteSeparated cs)
    (c d : ScalarPath D L) (cm : c ∈ cs) (dm : d ∈ cs) (different : c.path ≠ d.path) : pathsApart c d := by
  induction cs with
  | nil => cases cm
  | cons head tail ih =>
    have pair := List.pairwise_cons.mp sep
    rcases List.mem_cons.mp cm with equal | cm
    · subst c
      rcases List.mem_cons.mp dm with equal | dm
      · subst d; exact False.elim (different rfl)
      · exact (pair.1 d dm).2
    · rcases List.mem_cons.mp dm with equal | dm
      · subst d; exact pathsApart_symm (pair.1 c cm).2
      · exact ih pair.2 cm dm

/-- Distinct actual declared headers cannot share a root slot: this is
DERIVED from the checked packing, not supplied as desired separation. -/
theorem ComputedStorage.header_slots_ne {E ds d active a} (r : @ComputedStorage E ds d active a)
    {root other cursor position} (h : DynamicHeader E root cursor) (g : DynamicHeader E other position)
    (hm : (root,cursor) ∈ r.headerTrace) (gm : (other,position) ∈ r.headerTrace) (different : root ≠ other) :
    (h.registration a).slot ≠ (g.registration a).slot := by
  obtain ⟨h',hc⟩ := r.header_present _ _ hm
  obtain ⟨g',gc⟩ := r.header_present _ _ gm
  rw [h'.proof_irrel h] at hc
  rw [g'.proof_irrel g] at gc
  have apart := finiteSeparated_pair _ r.separated _ _ hc gc (fun same => different (congrArg Source.SPath.root same))
  rcases apart with neq | before | after
  · exact neq
  · rw [h.offset,h.width,g.offset] at before
    omega
  · rw [g.offset,g.width,h.offset] at after
    omega

theorem DynamicHeader.elements_ne_other {E root other cursor position} (h : DynamicHeader E root cursor)
    (g : DynamicHeader E other position) (fixed : Roadmap.Evm.Fixed) (a : Roadmap.Address)
    (L i j : Nat) (roots : List Nat) (ps : List Storage.Pre)
    (regions : Hash.RegionsDisjoint (2^256) L (fixedLayoutHash fixed) roots ps)
    (lb : L ≤ 2^256) (ib : i < L) (jb : j < L)
    (hp : Storage.Pre.data (h.registration a).slot.val ∈ ps)
    (gp : Storage.Pre.data (g.registration a).slot.val ∈ ps)
    (different : (h.registration a).slot ≠ (g.registration a).slot) :
    (h.element fixed a i).slot ≠ (g.element fixed a j).slot := by
  intro same
  have eq := congrArg Fin.val same
  rw [h.element_word,g.element_word] at eq
  have distinct : Storage.Pre.data (h.registration a).slot.val ≠ Storage.Pre.data (g.registration a).slot.val := by
    intro equal
    exact different (Fin.ext (Storage.Pre.data.inj equal))
  exact regions.1 _ hp _ gp distinct
    (Hash.near_of_overlap (fixedLayoutHash_lt fixed _) (fixedLayoutHash_lt fixed _) lb ib jb eq)

end Solidity.Yul.Views
