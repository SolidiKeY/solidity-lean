import Solidity.Yul.Views.PackedResidualWritebackSound

namespace Solidity.Yul.Views

/-- Current-frame canonical preparation adapter. None is unsupported
preparation, not a Yul verdict. All actual execution goes through applyOp. -/
def packedFrameWrite? {E : Source.Env} {Γ : Source.RCtx}
    {ps ts : (a : Roadmap.Address) → List (ScalarPath E.layout (E.lay a))}
    (F : Source.Fr) (transient : Bool) (slot raw : Roadmap.Word) (s : Source.EMState E Γ)
    (r : ResidualJournal complementCarrierOwnership) :
    Option ((Except Source.Halt Unit × Source.EMState E Γ) × ResidualJournal complementCarrierOwnership) :=
  (preparePackedFrame (ps := ps) (ts := ts) F transient slot raw).map (fun p => packedSourceStep F p s r)

theorem packedFrameWrite_MemOK {E : Source.Env} {Γ : Source.RCtx} {ps ts}
    (H : Source.HeapTy) (F : Source.Fr) (transient : Bool) (slot raw : Roadmap.Word) (s : Source.EMState E Γ)
    (r : ResidualJournal complementCarrierOwnership) (result)
    (step : packedFrameWrite? (ps := ps) (ts := ts) F transient slot raw s r = some result) (ok : Source.MemOK E H s) :
    Source.MemOK E H result.1.2 := by
  obtain ⟨p,prepared,same⟩ := Option.map_eq_some_iff.mp step
  subst result
  exact packedSourceStep_MemOK H F p s r ok

theorem packedFrameWrite_static {E : Source.Env} {Γ : Source.RCtx} {ps ts}
    (F : Source.Fr) (transient : Bool) (slot raw : Roadmap.Word) (s : Source.EMState E Γ)
    (r : ResidualJournal complementCarrierOwnership) (static : F.static = true)
    (prepared : (preparePackedFrame (ps := ps) (ts := ts) F transient slot raw).isSome) :
    packedFrameWrite? (ps := ps) (ts := ts) F transient slot raw s r = some ((.error (.revert []),s),r) := by
  obtain ⟨p,yes⟩ := Option.isSome_iff_exists.mp prepared
  rw [packedFrameWrite?,yes,Option.map_some,packedSourceStep_static F p s r static]

theorem packedFrameWrite_complement {E : Source.Env} {Γ : Source.RCtx} {ps ts}
    (F : Source.Fr) (transient : Bool) (slot raw : Roadmap.Word) (s : Source.EMState E Γ)
    (r : ResidualJournal complementCarrierOwnership) (result)
    (valid : PackedComplementValid ps ts r)
    (step : packedFrameWrite? (ps := ps) (ts := ts) F transient slot raw s r = some result) : PackedComplementValid ps ts result.2 := by
  obtain ⟨p,prepared,same⟩ := Option.map_eq_some_iff.mp step
  subst result
  cases static : F.static
  · rw [packedSourceStep_nonstatic F p s r static]
    exact packedComplement_plan r valid p
  · rw [packedSourceStep_static F p s r static]
    exact valid

/-- Concrete final composition for a canonical raw SSTORE preparation at the
current source frame: real applyOp + derived mask gives the ENTIRE raw word.
No source/view/result adequacy assumption is supplied. Full assembly admission,
dirty values and HashedLayout-wide ownership remain separate obligations. -/
theorem packedFrameWrite_persistent_reencode {E : Source.Env} {Γ : Source.RCtx} {ps ts}
    (F : Source.Fr) (slot raw : Roadmap.Word) (s : Source.EMState E Γ)
    (r : ResidualJournal complementCarrierOwnership) (result)
    (step : packedFrameWrite? (ps := ps) (ts := ts) F false slot raw s r = some result)
    (static : F.static = false) (sep : finiteSeparated (ps F.this)) :
    reencodePersistentSlot ps ⟨result.1.2.2.ex,result.2⟩ F.this slot = some raw := by
  obtain ⟨p,prepared,same⟩ := Option.map_eq_some_iff.mp step
  subst result
  have request := preparePackedSlot_request _ p prepared
  have tr : p.request.transient = false := congrArg PackedSlotRequest.transient request
  have address : p.request.address = F.this := congrArg PackedSlotRequest.address request
  have slotEq : p.request.slot = slot := congrArg PackedSlotRequest.slot request
  have rawEq : p.request.raw = raw := congrArg PackedSlotRequest.raw request
  rw [packedSourceStep_nonstatic F p s r static]
  have encoded := packedPersistent_reencode (⟨s.2.ex,r⟩ : ResidualCompanion E.layout E.lay E.lay complementCarrierOwnership) p tr (address ▸ sep)
  simpa only [address,slotEq,rawEq] using encoded

theorem packedFrameWrite_transient_reencode {E : Source.Env} {Γ : Source.RCtx} {ps ts}
    (F : Source.Fr) (slot raw : Roadmap.Word) (s : Source.EMState E Γ)
    (r : ResidualJournal complementCarrierOwnership) (result)
    (step : packedFrameWrite? (ps := ps) (ts := ts) F true slot raw s r = some result)
    (static : F.static = false) (sep : finiteSeparated (ts F.this)) :
    reencodeTransientSlot ts ⟨result.1.2.2.ex,result.2⟩ F.this slot = some raw := by
  obtain ⟨p,prepared,same⟩ := Option.map_eq_some_iff.mp step
  subst result
  have request := preparePackedSlot_request _ p prepared
  have tr : p.request.transient = true := congrArg PackedSlotRequest.transient request
  have address : p.request.address = F.this := congrArg PackedSlotRequest.address request
  have slotEq : p.request.slot = slot := congrArg PackedSlotRequest.slot request
  have rawEq : p.request.raw = raw := congrArg PackedSlotRequest.raw request
  rw [packedSourceStep_nonstatic F p s r static]
  have encoded := packedTransient_reencode (⟨s.2.ex,r⟩ : ResidualCompanion E.layout E.lay E.lay complementCarrierOwnership) p tr (address ▸ sep)
  simpa only [address,slotEq,rawEq] using encoded

end Solidity.Yul.Views
