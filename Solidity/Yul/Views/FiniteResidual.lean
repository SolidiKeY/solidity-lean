import Solidity.Yul.Views.FiniteWorld
import Solidity.Yul.Views.ResidualJournal

/-! Derive fixed residual ownership from the actual finite registrations. This
is coverage of registered paths, not completeness for all source paths/regions.
No dynamic ownership or owned-slot padding/dirty journal integration is implied. -/
namespace Solidity.Yul.Views

def registeredOwnership {D : Source.Layout} {L T : Roadmap.Address → Source.SPath → Source.STy}
    (persistent : (a : Roadmap.Address) → List (ScalarPath D (L a)))
    (transient : (a : Roadmap.Address) → List (ScalarPath D (T a))) : ResidualOwnership :=
  fun tr a slot => if tr then ∃ c ∈ transient a, c.slot = slot else ∃ c ∈ persistent a, c.slot = slot

theorem registered_persistent_unowned {D : Source.Layout} {L T : Roadmap.Address → Source.SPath → Source.STy}
    (ps : (a : Roadmap.Address) → List (ScalarPath D (L a)))
    (ts : (a : Roadmap.Address) → List (ScalarPath D (T a)))
    (k : ResidualKey (registeredOwnership ps ts)) (ht : k.transient = false) :
    ∀ c ∈ ps k.address, c.slot ≠ k.slot := by
  intro c hc he
  apply k.unowned
  simp only [registeredOwnership, ht, Bool.false_eq_true, ↓reduceIte]
  exact ⟨c, hc, he⟩

theorem registered_transient_unowned {D : Source.Layout} {L T : Roadmap.Address → Source.SPath → Source.STy}
    (ps : (a : Roadmap.Address) → List (ScalarPath D (L a)))
    (ts : (a : Roadmap.Address) → List (ScalarPath D (T a)))
    (k : ResidualKey (registeredOwnership ps ts)) (ht : k.transient = true) :
    ∀ c ∈ ts k.address, c.slot ≠ k.slot := by
  intro c hc he
  apply k.unowned
  simp only [registeredOwnership, ht, ↓reduceIte]
  exact ⟨c, hc, he⟩

theorem finiteEncode_unowned_slot {D L} (cs : List (ScalarPath D L)) (s : Source.Storage D L)
    (m out : SlotView) (e : finiteEncode cs s m = some out) (q : Roadmap.Word)
    (unowned : ∀ c ∈ cs, c.slot ≠ q) : out q = m q := by
  induction cs generalizing m with
  | nil => exact congrArg (fun x => x q) (Option.some.inj e).symm
  | cons c cs ih =>
    obtain ⟨mid, hc, ht⟩ := Option.bind_eq_some_iff.mp e
    rw [ih mid ht (fun d hd => unowned d (List.mem_cons_of_mem c hd))]
    obtain ⟨v, _, he⟩ := Option.map_eq_some_iff.mp hc
    subst mid
    exact find_saveSlot_other m c.slot q _ (Ne.symm (unowned c List.mem_cons_self))

theorem finiteEncode_registered_residual {D : Source.Layout} {L T : Roadmap.Address → Source.SPath → Source.STy}
    (ps : (a : Roadmap.Address) → List (ScalarPath D (L a)))
    (ts : (a : Roadmap.Address) → List (ScalarPath D (T a)))
    (k : ResidualKey (registeredOwnership ps ts)) (ht : k.transient = false)
    (s : Source.Storage D (L k.address)) (m out : SlotView)
    (e : finiteEncode (ps k.address) s m = some out) : out k.slot = m k.slot :=
  finiteEncode_unowned_slot _ s m out e k.slot (registered_persistent_unowned ps ts k ht)

end Solidity.Yul.Views
