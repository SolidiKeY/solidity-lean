import Solidity.Yul.Views.LocatedRegistration

/-! Separation for computed registrations uses precisely the owner's per-run
region premise. Word-granular root0 layouts only; this is not packed-layout
inference and distinct source paths alone do not imply distinct slot terms. -/
namespace Solidity.Yul.Views

def locatedPreimages {E fixed root tree p q} (r : LocatedWord E fixed root tree p)
    (s : LocatedWord E fixed root tree q) : List Storage.Pre :=
  r.location.pres (2^256) (fixedLayoutHash fixed) ++ s.location.pres (2^256) (fixedLayoutHash fixed)

theorem located_slots_injective {E fixed root tree p q}
    (r : LocatedWord E fixed root tree p) (s : LocatedWord E fixed root tree q)
    (L R : Nat) (fits : tree.Fits L) (rootFits : tree.size ≤ R)
    (lb : L ≤ 2^256) (rb : R ≤ 2^256)
    (regions : Hash.RegionsDisjoint (2^256) L (fixedLayoutHash fixed) (List.range R) (locatedPreimages r s))
    (a : Roadmap.Address) (same : (r.registration a).slot = (s.registration a).slot) : r.location = s.location := by
  have numeric := congrArg Fin.val same
  have separated := Storage.located_word_inj (fixedLayoutHash_lt fixed) lb rb regions fits rootFits
    r.located s.located r.positive s.positive
    (fun x hx => List.mem_append_left _ hx) (fun x hx => List.mem_append_right _ hx)
    (show (r.location.add 0).word (2^256) (fixedLayoutHash fixed) =
      (s.location.add 0).word (2^256) (fixedLayoutHash fixed) from by
      simpa only [Storage.Loc.add_zero] using numeric)
  simpa only [Storage.Loc.add_zero] using separated

theorem located_pair_separated {E fixed root tree p q}
    (r : LocatedWord E fixed root tree p) (s : LocatedWord E fixed root tree q)
    (L R : Nat) (fits : tree.Fits L) (rootFits : tree.size ≤ R)
    (lb : L ≤ 2^256) (rb : R ≤ 2^256)
    (regions : Hash.RegionsDisjoint (2^256) L (fixedLayoutHash fixed) (List.range R) (locatedPreimages r s))
    (differentPath : r.path ≠ s.path) (differentLocation : r.location ≠ s.location)
    (a : Roadmap.Address) : finiteSeparated [r.registration a,s.registration a] := by
  apply List.pairwise_cons.mpr
  constructor
  · intro x hx
    have same : x = s.registration a := List.mem_singleton.mp hx
    subst x
    exact ⟨differentPath,Or.inl (fun eq => differentLocation (located_slots_injective r s L R fits rootFits lb rb regions a eq))⟩
  · exact List.pairwise_singleton _ _

/-- A literal collision/alias check does not stand in for region separation.
It is an executable diagnostic for supplied run layouts, not admission. -/
def locatedAliasCheck {E fixed root tree p q}
    (r : LocatedWord E fixed root tree p) (s : LocatedWord E fixed root tree q) : Bool :=
  r.path == s.path || r.location == s.location

end Solidity.Yul.Views
