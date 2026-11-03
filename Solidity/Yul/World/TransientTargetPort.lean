import Solidity.Yul.Views.TransientSlots
import Solidity.Backend.Transient.CallbackObservation
/-! Actual VY2 transient Source/residual operations paired with local P7 target
execution. Checked preparation is adapter availability, not callee reachability.
Only the requested slot is related after a write; no whole-bank framing or
G39/Bridge execution adequacy is assumed. Static errors retain both carriers. -/
namespace Solidity.Yul.World.TransientTarget
open Views Solidity.Backend

def store {E : Source.Env} {Γ : Source.RCtx}
    {ps ts : (a : Roadmap.Address) → List (ScalarPath E.layout (E.lay a))}
    (F : Source.Fr) (slot raw : Roadmap.Word) (s : Source.EMState E Γ)
    (r : ResidualJournal complementCarrierOwnership) (target : Transient.State) :
    Option (((Except Source.Halt Unit × Source.EMState E Γ) ×
      ResidualJournal complementCarrierOwnership) × Transient.Result) :=
  match transientSlotStore? (ps:=ps) (ts:=ts) F slot raw s r with
  | none => none
  | some result => some (result, Transient.callbackInFrame F (Transient.storeCode slot raw) target)

/-- Conditional transport: pointwise view agreement is an input, not derived. -/
theorem load_assuming_view_agreement {D : Source.Layout} {L T : Roadmap.Address → Source.SPath → Source.STy}
    (ts : (a : Roadmap.Address) → List (ScalarPath D (T a)))
    (source : ResidualCompanion D L T complementCarrierOwnership)
    (target : Transient.State) (a : Roadmap.Address) (slot : Roadmap.Word) (static : Bool)
    (agrees : transientSlotLoad ts source a slot = some (target.bank a slot)) :
    (transientSlotLoad ts source a slot,
      Transient.callbackObserved a static (Transient.loadCode slot) target) =
      (some (target.bank a slot), (.ok target, some (.val (target.bank a slot)))) := by
  simp only [agrees, Transient.callbackObserved_load]

theorem store_exact {E : Source.Env} {Γ : Source.RCtx}
    {ps ts : (a : Roadmap.Address) → List (ScalarPath E.layout (E.lay a))}
    (F : Source.Fr) (slot raw : Roadmap.Word) (s : Source.EMState E Γ)
    (r : ResidualJournal complementCarrierOwnership) (target : Transient.State) (result)
    (checked : transientSlotStore? (ps:=ps) (ts:=ts) F slot raw s r = some result)
    (normal : F.static = false) :
    store (ps:=ps) (ts:=ts) F slot raw s r target =
      some (result, .ok (Transient.write target F.this slot raw)) := by
  simp only [store, checked, Transient.framed_store F normal]
theorem store_readback {E : Source.Env} {Γ : Source.RCtx}
    {ps ts : (a : Roadmap.Address) → List (ScalarPath E.layout (E.lay a))}
    (F : Source.Fr) (slot raw : Roadmap.Word) (s : Source.EMState E Γ)
    (r : ResidualJournal complementCarrierOwnership) (target : Transient.State) (result)
    (checked : transientSlotStore? (ps:=ps) (ts:=ts) F slot raw s r = some result)
    (normal : F.static = false) (separate : finiteSeparated (ts F.this)) :
    transientSlotLoad ts ⟨result.1.2.2.ex, result.2⟩ F.this slot =
      some ((Transient.write target F.this slot raw).bank F.this slot) := by
  simp only [Transient.write, Transient.put_same,
      transientSlot_load_store F slot raw s r result checked normal separate]

theorem store_static {E : Source.Env} {Γ : Source.RCtx}
    {ps ts : (a : Roadmap.Address) → List (ScalarPath E.layout (E.lay a))}
    (F : Source.Fr) (slot raw : Roadmap.Word) (s : Source.EMState E Γ)
    (r : ResidualJournal complementCarrierOwnership) (target : Transient.State)
    (static : F.static = true)
    (prepared : (preparePackedFrame (ps:=ps) (ts:=ts) F true slot raw).isSome) :
    store (ps:=ps) (ts:=ts) F slot raw s r target =
      some (((.error (.revert []),s),r), .error .staticWrite target) := by
  simp only [store, transientSlot_static F slot raw s r static prepared,
      Transient.framed_static_store F static]

/-- Both resets read zero under actual source codec defaults, for any target. -/
theorem reset_readback_zero {D : Source.Layout} {L T : Roadmap.Address → Source.SPath → Source.STy}
    (ts : (a : Roadmap.Address) → List (ScalarPath D (T a)))
    (source : ResidualCompanion D L T complementCarrierOwnership)
    (target : Transient.State)
    (defaults : ∀ a c, c∈ts a → ∃ v, Source.Val.default D (T a c.path)=some v ∧ (c.codec.encode v).val=0)
    (a : Roadmap.Address) (slot : Roadmap.Word) :
    transientSlotLoad ts (companionEndTx source) a slot =
      some ((Transient.endTx target).bank a slot) := by
  simp only [transientSlot_endTx ts source defaults, Transient.endTx, Transient.empty]
  rfl
/-- Readback derived after the actual checked write; no initial agreement premise. -/
theorem stored_load_readback {E : Source.Env} {Γ : Source.RCtx}
    {ps ts : (a : Roadmap.Address) → List (ScalarPath E.layout (E.lay a))}
    (F : Source.Fr) (slot raw : Roadmap.Word) (s : Source.EMState E Γ)
    (r : ResidualJournal complementCarrierOwnership) (target : Transient.State) (result)
    (checked : transientSlotStore? (ps:=ps) (ts:=ts) F slot raw s r = some result)
    (normal : F.static = false) (separate : finiteSeparated (ts F.this)) :
    (transientSlotLoad ts ⟨result.1.2.2.ex,result.2⟩ F.this slot,
      Transient.callbackObserved F.this F.static (Transient.loadCode slot)
        (Transient.write target F.this slot raw)) =
      (some raw,(.ok (Transient.write target F.this slot raw),some (.val raw))) := by
  simp only [transientSlot_load_store F slot raw s r result checked normal separate,
    Transient.callbackObserved_load,Transient.write,Transient.put_same]

end Solidity.Yul.World.TransientTarget
