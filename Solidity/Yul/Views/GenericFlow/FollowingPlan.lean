import Solidity.Yul.Views.Generic.Plan
import Solidity.Yul.Views.GenericFlow.Following

namespace Solidity.Yul.Views.GenericFlow

/-- Adapt the shared intrinsic Plan computations to checked following. State and journal remain lazy; the effective separation checker is explicit. -/
abbrev planShape {E Γ} (F : Source.Fr) (interface : Generic.OwnershipInterface E Γ F)
    (layout : interface.Layout) (fixed : Roadmap.Evm.Fixed) (written value : Roadmap.Word)
    (state : Unit → Source.EMState E Γ)
    (journal : Unit → ResidualJournal complementCarrierOwnership)
    (check : List (ScalarPath E.layout (E.lay F.this)) → Bool) :
    PreparationShape (List (ScalarPath E.layout (E.lay F.this))) SlotView
      (Source.Op E.layout E.lay E.lay)
      (Generic.OwnershipPlan F interface layout fixed written value (state ()) (journal ()) check) :=
  ⟨fun _ => interface.inventory? layout fixed (state ()),
    fun old => finiteEncode old ((state ()).2.ex.world.accounts F.this).storage
      (fun slot => (journal ()).cells (complementKey false F.this slot)),
    check,
    fun raw => check (interface.snapshot layout fixed (saveSlot raw written value)),
    fun raw => finiteAccountWrite? F.this (interface.snapshot layout fixed (saveSlot raw written value))
      (saveSlot raw written value),
    fun old computed raw encoded checked nextChecked op prepared =>
      ⟨old,computed,raw,encoded,checked,nextChecked,op,prepared⟩⟩

end Solidity.Yul.Views.GenericFlow
