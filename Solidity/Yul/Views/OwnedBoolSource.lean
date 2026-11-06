import Solidity.Yul.Views.OwnedBoolView
import Solidity.Yul.Views.PackedResidualSource

namespace Solidity.Yul.Views

/-- Computed only from the same request's selected owned fields. -/
def requestEncoding {E : Source.Env}
    (ps ts : (a : Roadmap.Address) → List (ScalarPath E.layout (E.lay a)))
    (q : PackedSlotRequest) (before : BoolEncodingJournal) : BoolEncodingJournal :=
  let cs := selectedSlotPaths (if q.transient then ts q.address else ps q.address) q.slot
  boolEncodingRun before (encodingWrites cs q.transient q.address (fun _ => q.raw) before)

def representedBanks {E : Source.Env}
    (cs : (a : Roadmap.Address) → List (ScalarPath E.layout (E.lay a)))
    (bank : Bool) (encoding : BoolEncodingJournal) :=
  fun a => representedRegistry (cs a) bank a encoding

/-- The existing concrete validator uses representations computed from raw.
No inverse, result-view or safety theorem is a certificate field. -/
def prepareRepresentedPackedSlot {E : Source.Env}
    (ps ts : (a : Roadmap.Address) → List (ScalarPath E.layout (E.lay a)))
    (q : PackedSlotRequest) (before : BoolEncodingJournal) :=
  let encoding := requestEncoding ps ts q before
  preparePackedSlot (representedBanks ps false encoding) (representedBanks ts true encoding) q

/-- Request equality comes from the concrete preparer, not a physical law. -/
structure RepresentedSlotPlan {E : Source.Env}
    (ps ts : (a : Roadmap.Address) → List (ScalarPath E.layout (E.lay a)))
    (q : PackedSlotRequest) (before : BoolEncodingJournal) where
  packed : @PackedSlotPlan E.layout E.lay E.lay
    (representedBanks ps false (requestEncoding ps ts q before))
    (representedBanks ts true (requestEncoding ps ts q before))
  request_eq : packed.request=q

def prepareRepresentedSlot {E : Source.Env}
    (ps ts : (a : Roadmap.Address) → List (ScalarPath E.layout (E.lay a)))
    (q : PackedSlotRequest) (before : BoolEncodingJournal) : Option (RepresentedSlotPlan ps ts q before) :=
  (prepareRepresentedPackedSlot ps ts q before).pmap
    (fun packed ready => ⟨packed,preparePackedSlot_request q packed ready⟩) (fun _ eq => eq)

/-- Both physical components advance only after the SAME actual source op. -/
def representedSourceStep {E : Source.Env} {Γ : Source.RCtx}
    (ps ts : (a : Roadmap.Address) → List (ScalarPath E.layout (E.lay a)))
    (q : PackedSlotRequest) (before : BoolEncodingJournal) (F : Source.Fr)
    (p : RepresentedSlotPlan ps ts q before)
    (s : Source.EMState E Γ) (r : ResidualJournal complementCarrierOwnership) :=
  let result := packedSourceStep F p.packed s r
  (result,match result.1.1 with | .error _ => before | .ok _ => requestEncoding ps ts q before)

theorem representedSourceStep_static {E Γ ps ts q before}
    (F : Source.Fr) (p) (s : Source.EMState E Γ) (r) (static : F.static=true) :
    representedSourceStep ps ts q before F p s r=(((.error (.revert []),s),r),before) := by
  unfold representedSourceStep
  rw [packedSourceStep_static F p.packed s r static]

theorem representedSourceStep_nonstatic {E Γ ps ts q before}
    (F : Source.Fr) (p) (s : Source.EMState E Γ) (r) (static : F.static=false) :
    representedSourceStep ps ts q before F p s r=
      (((.ok (),(s.1,{s.2 with ex:=s.2.ex.apply p.packed.sourceOp})),residualWrite r p.packed.residualUpdate),requestEncoding ps ts q before) := by
  unfold representedSourceStep
  rw [packedSourceStep_nonstatic F p.packed s r static]

theorem representedSourceStep_MemOK {E Γ ps ts q before}
    (H : Source.HeapTy) (F : Source.Fr) (p) (s : Source.EMState E Γ) (r)
    (ok : Source.MemOK E H s) :
    Source.MemOK E H (representedSourceStep ps ts q before F p s r).1.1.2 :=
  packedSourceStep_MemOK H F p.packed s r ok

/-- Full slot reconstruction includes the owned bool byte AND padding. -/
theorem representedSourceStep_persistent {E Γ ps ts q before}
    (F : Source.Fr) (p) (s : Source.EMState E Γ) (r) (static : F.static=false)
    (bank : p.packed.request.transient=false) (separated : finiteSeparated (ps p.packed.request.address)) :
    let result := representedSourceStep ps ts q before F p s r
    reencodePersistentSlot (representedBanks ps false result.2)
      ⟨result.1.1.2.2.ex,result.1.2⟩ p.packed.request.address p.packed.request.slot=some p.packed.request.raw := by
  rw [representedSourceStep_nonstatic F p s r static]
  exact packedPersistent_reencode ⟨s.2.ex,r⟩ p.packed bank (representedRegistry_separated _ _ _ _ separated)

theorem representedSourceStep_transient {E Γ ps ts q before}
    (F : Source.Fr) (p) (s : Source.EMState E Γ) (r) (static : F.static=false)
    (bank : p.packed.request.transient=true) (separated : finiteSeparated (ts p.packed.request.address)) :
    let result := representedSourceStep ps ts q before F p s r
    reencodeTransientSlot (representedBanks ts true result.2)
      ⟨result.1.1.2.2.ex,result.1.2⟩ p.packed.request.address p.packed.request.slot=some p.packed.request.raw := by
  rw [representedSourceStep_nonstatic F p s r static]
  exact packedTransient_reencode ⟨s.2.ex,r⟩ p.packed bank (representedRegistry_separated _ _ _ _ separated)

end Solidity.Yul.Views
