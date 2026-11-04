import Solidity.Yul.Views.LinkedCellHash

/-! External source/residual frame transport of actual typed-write/hash runs.
The hash's heap allocation is retained in Source state; these laws deliberately
restore only the actual external execution and complementary journal carriers.
Frames are entered after computed preparation, never across its initialization. -/
namespace Solidity.Yul.Views.CellHashFrames

def operations {E} (F : Source.Fr) (requests : List (FiniteCellWrites.Request E F.this)) :=
  requests.map (fun request => @RepeatedCellWrites.operation E F request.1 request.2)

def paired {E Γ} (s : Source.EMState E Γ) (residual : ResidualJournal complementCarrierOwnership) :
    ResidualCompanion E.layout E.lay E.lay complementCarrierOwnership := ⟨s.2.ex,residual⟩

theorem external {E Γ} (G : Source.Glob E) (F : Source.Fr) (n : Nat)
    (s : Source.EMState E Γ) (index : Source.Idx Γ (.bytes .calldata)) (off len : Nat)
    (requests : List (FiniteCellWrites.Request E F.this)) (allowed : F.static=false)
    (localValue : s.1.get index=Source.Val.cdRef rfl off len)
    (residual : ResidualJournal complementCarrierOwnership) :
    paired ((CellWritesCalldataHash.program G F (n+4) index requests).run s).2 residual=
      companionRunSource (paired s residual) (operations F requests) := by
  first | (simp only;done) | decide | omega | rfl | skip
  rw [CellWritesCalldataHash.run G F n s index off len requests allowed localValue]
  unfold CellWritesCalldataHash.afterWrites
  rw [FiniteCellWrites.run F s requests allowed]
  rfl

theorem child_rollback {E Γ} (G : Source.Glob E) (F : Source.Fr) (n : Nat)
    (s : Source.EMState E Γ) (index : Source.Idx Γ (.bytes .calldata)) (off len : Nat)
    (requests : List (FiniteCellWrites.Request E F.this)) (allowed : F.static=false)
    (localValue : s.1.get index=Source.Val.cdRef rfl off len)
    (residual : ResidualJournal complementCarrierOwnership) :
    companionRollback (companionEnter (paired s residual) F.this F.sender F.value F.cd F.static)
      (paired ((CellWritesCalldataHash.program G F (n+4) index requests).run s).2 residual)=paired s residual := by
  first | (simp only;done) | decide | omega | rfl | skip
  rw [external G F n s index off len requests allowed localValue residual]
  exact companionRollback_run (paired s residual) (operations F requests) [] _ _ _ _ _

theorem locals {E Γ} (G : Source.Glob E) (F : Source.Fr) (n : Nat)
    (s : Source.EMState E Γ) (index : Source.Idx Γ (.bytes .calldata)) (off len : Nat)
    (requests : List (FiniteCellWrites.Request E F.this)) (allowed : F.static=false)
    (localValue : s.1.get index=Source.Val.cdRef rfl off len) :
    ((CellWritesCalldataHash.program G F (n+4) index requests).run s).2.1=s.1 := by
  first | (simp only;done) | decide | omega | rfl | skip
  rw [CellWritesCalldataHash.run G F n s index off len requests allowed localValue]
  exact CellWritesCalldataHash.locals F s requests allowed

theorem outer_rollback {E Γ} (G : Source.Glob E) (F : Source.Fr) (n k : Nat)
    (s : Source.EMState E Γ) (index : Source.Idx Γ (.bytes .calldata)) (off len : Nat)
    (requests childRequests : List (FiniteCellWrites.Request E F.this)) (allowed : F.static=false)
    (localValue : s.1.get index=Source.Val.cdRef rfl off len)
    (residual : ResidualJournal complementCarrierOwnership) :
    let caller := ((CellWritesCalldataHash.program G F (n+4) index requests).run s).2
    let child := ((CellWritesCalldataHash.program G F (k+4) index childRequests).run caller).2
    companionRollback (companionEnter (paired s residual) F.this F.sender F.value F.cd F.static)
      (companionCommit (companionEnter (paired caller residual) F.this F.sender F.value F.cd F.static)
        (paired child residual))=paired s residual := by
  first | (simp only;done) | decide | omega | rfl | skip
  dsimp only
  have retained : (((CellWritesCalldataHash.program G F (n+4) index requests).run s).2.1).get index=
      Source.Val.cdRef rfl off len := by
    rw [locals G F n s index off len requests allowed localValue]
    exact localValue
  rw [external G F k _ index off len childRequests allowed retained residual]
  rw [external G F n s index off len requests allowed localValue residual]
  exact companionRollback_outer_commit (paired s residual) (operations F requests) (operations F childRequests)
    [] [] _ _ _ _ _
theorem rollback_reencode {E Γ} (G : Source.Glob E) (F : Source.Fr) (n : Nat)
    (s : Source.EMState E Γ) (index : Source.Idx Γ (.bytes .calldata)) (off len : Nat)
    (requests : List (FiniteCellWrites.Request E F.this)) (allowed : F.static=false)
    (localValue : s.1.get index=Source.Val.cdRef rfl off len)
    (ps ts : List (ScalarPath E.layout (E.lay F.this))) (sep : finiteSeparated ps)
    (maps : SlotView × SlotView) (view : finiteView ps (s.2.ex.world.accounts F.this).storage maps.1)
    (residual : ResidualJournal complementCarrierOwnership) :
    let initial := paired s (LinkedCellHash.prepare F.this ps ts maps residual)
    let restored := companionRollback (companionEnter initial F.this F.sender F.value F.cd F.static)
      (paired ((CellWritesCalldataHash.program G F (n+4) index requests).run s).2 initial.residual)
    finiteEncode ps (restored.source.world.accounts F.this).storage
      (fun slot => restored.residual.cells (complementKey false F.this slot))=some maps.1 := by
  first | (simp only;done) | decide | omega | rfl | skip
  dsimp only
  have residual_projection : (paired s (LinkedCellHash.prepare F.this ps ts maps residual)).residual=
      LinkedCellHash.prepare F.this ps ts maps residual := rfl
  rw [residual_projection,child_rollback G F n s index off len requests allowed localValue]
  change finiteEncode ps (s.2.ex.world.accounts F.this).storage
    (fun slot => (LinkedCellHash.prepare F.this ps ts maps residual).cells
      (complementKey false F.this slot))=some maps.1
  rw [LinkedCellHash.persistent_cells]
  exact finiteEncode_fromComplement ps _ maps.1 sep view
end Solidity.Yul.Views.CellHashFrames
