import Solidity.Yul.Views.CellHashFinalization

/-! Initial journal cells are computed from the complete supplied raw maps and
actual packed registries. Reconstruction below reads those journal cells after
explicit endTx, rather than using an independent complement argument. This is
canonical fixed-inventory transport, not dirty-owned or changing-domain adequacy.
Preparation is a constructed initialization boundary: it preserves the supplied
undo list but does not establish its historical compatibility with changed
cells. No rollback bridge or automatic initialization is claimed. -/
namespace Solidity.Yul.Views.LinkedCellHash

def prepare {D L} (address : Roadmap.Address) (ps ts : List (ScalarPath D L))
    (maps : SlotView × SlotView) (residual : ResidualJournal complementCarrierOwnership) :
    ResidualJournal complementCarrierOwnership :=
  {residual with cells:=fun key => if key.address=address then
    if key.transient then packedMask ts maps.2 key.slot else packedMask ps maps.1 key.slot
    else residual.cells key}

theorem persistent_cells {D L} (address : Roadmap.Address) (ps ts : List (ScalarPath D L))
    (maps : SlotView × SlotView) (residual : ResidualJournal complementCarrierOwnership) :
    (fun slot => (prepare address ps ts maps residual).cells (complementKey false address slot))=
      packedMask ps maps.1 := by
  first | (simp only;done) | decide | omega | rfl | skip
  funext slot
  simp only [prepare,complementKey,ite_true,Bool.false_eq_true,if_false]

theorem other {D L} (address : Roadmap.Address) (ps ts : List (ScalarPath D L))
    (maps : SlotView × SlotView) (residual : ResidualJournal complementCarrierOwnership)
    (key : ResidualKey complementCarrierOwnership) (different : key.address≠address) :
    (prepare address ps ts maps residual).cells key=residual.cells key := by
  first | (simp only [prepare,if_neg different];done) | decide | omega | rfl | skip

theorem finalized_cells {E Γ} (s : Source.EMState E Γ) (address : Roadmap.Address)
    (ps ts : List (ScalarPath E.layout (E.lay address))) (maps : SlotView × SlotView)
    (residual : ResidualJournal complementCarrierOwnership) :
    (fun slot => (CellHashFinalization.finish s (prepare address ps ts maps residual)).residual.cells
      (complementKey false address slot))=packedMask ps maps.1 := by
  first | (simp only;done) | decide | omega | rfl | skip
  funext slot
  exact (residualEndTx_persistent (prepare address ps ts maps residual) _ rfl).trans
    (congrFun (persistent_cells address ps ts maps residual) slot)

theorem reencode {E Γ} (G : Source.Glob E) (F : Source.Fr) (n : Nat)
    (s : Source.EMState E Γ) (index : Source.Idx Γ (.bytes .calldata)) (off len : Nat)
    (requests : List (FiniteCellWrites.Request E F.this))
    (ps ts : List (ScalarPath E.layout (E.lay F.this)))
    (psep : finiteSeparated ps) (tsep : finiteSeparated ts)
    (registered : ∀ request ∈ requests, FiniteCellWrites.Registered ps ts request)
    (maps : SlotView × SlotView) (before : FiniteCellWrites.Views F ps ts s maps)
    (allowed : F.static=false) (localValue : s.1.get index=Source.Val.cdRef rfl off len)
    (residual : ResidualJournal complementCarrierOwnership) :
    let reached := (CellWritesCalldataHash.program G F (n+4) index requests).run s
    let final := CellHashFinalization.finish reached.2 (prepare F.this ps ts maps residual)
    finiteEncode ps (final.source.world.accounts F.this).storage
      (fun slot => final.residual.cells (complementKey false F.this slot))=
        some (FiniteCellWrites.raw requests maps).1 := by
  first | (simp only;done) | decide | omega | rfl | skip
  dsimp only
  rw [finalized_cells]
  exact CellHashFinalization.persistent_reencode G F n s index off len requests ps ts psep tsep
    registered maps before allowed localValue (prepare F.this ps ts maps residual)
end Solidity.Yul.Views.LinkedCellHash
