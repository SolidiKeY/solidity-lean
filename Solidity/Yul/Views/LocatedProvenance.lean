import Solidity.Yul.Views.LocatedRegistration

namespace Solidity.Yul.Views

def layoutKeyBounds : List Storage.Step → Prop
  | [] => True
  | .key k::rest => k < 2^256 ∧ layoutKeyBounds rest
  | _::rest => layoutKeyBounds rest

theorem translated_key_bounds (access : List Storage.Step) (out : List Source.Step)
    (success : sourceLayoutSteps access = .ok out) : layoutKeyBounds access := by
  induction access generalizing out with
  | nil => trivial
  | cons step rest ih =>
    cases step with
    | field i =>
      cases next : sourceLayoutSteps rest with
      | error reason => simp only [sourceLayoutSteps,next,Except.map] at success; cases success
      | ok steps => exact ih steps next
    | index i =>
      cases next : sourceLayoutSteps rest with
      | error reason => simp only [sourceLayoutSteps,next,Except.map] at success; cases success
      | ok steps => exact ih steps next
    | key k =>
      simp only [sourceLayoutSteps] at success
      split at success
      · rename_i bound
        cases next : sourceLayoutSteps rest with
        | error reason => simp only [next,Except.map] at success; cases success
        | ok steps => exact ⟨bound,ih steps next⟩
      · cases success

def locationKeyBounds : Storage.Loc → Prop
  | .root _ => True
  | .hash k parent _ => k < 2^256 ∧ locationKeyBounds parent
  | .data parent _ => locationKeyBounds parent

theorem locationKeyBounds_add (loc : Storage.Loc) (offset : Nat) :
    locationKeyBounds (loc.add offset) ↔ locationKeyBounds loc := by
  cases loc <;> rfl

theorem locate_key_bounds (access : List Storage.Step) (t : Storage.STy) (loc : Storage.Loc)
    (out : Storage.STy) (found : Storage.Loc) (keys : layoutKeyBounds access)
    (initial : locationKeyBounds loc) (success : t.locate loc access = some (out,found)) : locationKeyBounds found := by
  induction access generalizing t loc with
  | nil =>
    simp only [Storage.STy.locate,Option.some.injEq,Prod.mk.injEq] at success
    obtain ⟨rfl,rfl⟩ := success
    exact initial
  | cons step rest ih =>
    cases t <;> cases step <;> simp only [Storage.STy.locate] at success
    all_goals try cases success
    case strct.field fields i =>
      cases next : fields[i]? with
      | none => rw [next] at success; cases success
      | some ty =>
        rw [next] at success
        exact ih ty _ keys ((locationKeyBounds_add loc _).mpr initial) success
    case sarr.index element size i =>
      split at success
      · exact ih element _ keys ((locationKeyBounds_add loc _).mpr initial) success
      · cases success
    case darr.index element i =>
      split at success
      · exact ih element (.data loc (i * element.size)) keys initial success
      · cases success
    case map.key value k =>
      exact ih value (.hash k loc 0) keys.2 ⟨keys.1,initial⟩ success

theorem location_preimage_words (fixed : Roadmap.Evm.Fixed) (loc : Storage.Loc)
    (keys : locationKeyBounds loc) :
    ∀ p ∈ loc.pres (2^256) (fixedLayoutHash fixed), p.Words := by
  induction loc with
  | root offset => intro p member; cases member
  | hash key parent offset ih =>
    intro p member
    rcases List.mem_append.mp member with old | last
    · exact ih keys.2 p old
    · have same := List.mem_singleton.mp last
      subst p
      exact ⟨keys.1,by cases parent <;> exact Nat.mod_lt _ (by decide)⟩
  | data parent offset ih =>
    intro p member
    rcases List.mem_append.mp member with old | last
    · exact ih keys p old
    · have same := List.mem_singleton.mp last
      subst p
      cases parent <;> exact Nat.mod_lt _ (by decide)

theorem LocatedWord.preimage_words {E fixed root tree access} (r : LocatedWord E fixed root tree access) :
    ∀ p ∈ r.location.pres (2^256) (fixedLayoutHash fixed), p.Words :=
  location_preimage_words fixed r.location (locate_key_bounds access tree (.root 0) r.reached r.location
    (translated_key_bounds access r.sourceSteps r.translated) trivial r.located)

end Solidity.Yul.Views
