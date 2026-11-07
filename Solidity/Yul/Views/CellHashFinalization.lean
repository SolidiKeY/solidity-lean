import Solidity.Yul.Views.CellWritesCalldataHash

/-! Transaction finalization of the actual combined cell-write/hash run.
Persistent reconstruction uses the original complement. Transient reset uses
owner defaults, rather than assuming arbitrary codecs encode defaults as zero.
This explicitly finalizes carriers; it does not implement transaction error
handling. Reencoding uses the original map complement independently of the
supplied residual journal. It does not establish their initial coupling or
physical heap placement. -/
namespace Solidity.Yul.Views.CellHashFinalization

def finish {E Γ} (state : Source.EMState E Γ)
    (residual : ResidualJournal complementCarrierOwnership) :
    ResidualCompanion E.layout E.lay E.lay complementCarrierOwnership :=
  companionEndTx ⟨state.2.ex,residual⟩

theorem reset {E Γ} (state : Source.EMState E Γ)
    (residual : ResidualJournal complementCarrierOwnership)
    (address : Roadmap.Address) (path : Source.SPath) (slot : Roadmap.Word) :
    (finish state residual).source.world=state.2.ex.world ∧
    ((finish state residual).source.transient.cells address).read path=
      Source.Val.default E.layout (E.lay address path) ∧
    (finish state residual).residual.cells (complementKey false address slot)=
      residual.cells (complementKey false address slot) ∧
    (finish state residual).residual.cells (complementKey true address slot)=0 ∧
    (finish state residual).source.journal=[] ∧ (finish state residual).residual.journal=[] := by
  first | (simp only;done) | (decide) | omega | rfl | skip
  exact ⟨rfl,rfl,residualEndTx_persistent _ _ rfl,residualEndTx_transient _ _ rfl,rfl,rfl⟩

theorem persistent_reencode {E Γ} (G : Source.Glob E) (F : Source.Fr) (n : Nat)
    (s : Source.EMState E Γ) (index : Source.Idx Γ (.bytes .calldata)) (off len : Nat)
    (requests : List (FiniteCellWrites.Request E F.this))
    (ps ts : List (ScalarPath E.layout (E.lay F.this)))
    (psep : finiteSeparated ps) (tsep : finiteSeparated ts)
    (registered : ∀ request ∈ requests, FiniteCellWrites.Registered ps ts request)
    (maps : SlotView × SlotView) (before : FiniteCellWrites.Views F ps ts s maps)
    (allowed : F.static=false) (localValue : s.1.get index=Source.Val.cdRef rfl off len)
    (residual : ResidualJournal complementCarrierOwnership) :
    let reached := (CellWritesCalldataHash.program G F (n+4) index requests).run s
    finiteEncode ps ((finish reached.2 residual).source.world.accounts F.this).storage
      (packedMask ps maps.1)=some (FiniteCellWrites.raw requests maps).1 := by
  first | (simp only;done) | (decide) | omega | rfl | skip
  exact (CellWritesCalldataHash.reencode G F n s index off len requests ps ts psep tsep
    registered maps before allowed localValue).1
end Solidity.Yul.Views.CellHashFinalization
