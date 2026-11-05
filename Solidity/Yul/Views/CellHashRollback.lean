import Solidity.Yul.Views.CellHashFrames

/-! Exact execution of actual Source mark/rollbackTo around typed writes and a
calldata hash. rollbackTo restores external writes and logs but deliberately
retains heap allocation; enterInstance's separate heap restoration is not
modeled here. No source transaction or call-admission semantics are replaced. -/
namespace Solidity.Yul.Views.CellHashRollback

def program {E Γ} (G : Source.Glob E) (F : Source.Fr) (horizon : Nat)
    (index : Source.Idx Γ (.bytes .calldata)) (requests : List (FiniteCellWrites.Request E F.this)) :
    Source.EM E Γ (Source.RVal E.layout Source.STy.bytes32) := do
  let checkpoint ← Source.mark
  let value ← CellWritesCalldataHash.program G F horizon index requests
  Source.rollbackTo checkpoint
  pure value

theorem undo {D L T} (s : Source.ExecState D L T) (ops : List (Source.Op D L T)) :
    (s.run ops).undoN ((s.run ops).journal.length-s.journal.length)=s := by
  first | (simp only [Source.ExecState.journal_run,Nat.add_sub_cancel_left];done) | decide | omega | rfl | skip
  rw [Source.ExecState.journal_run]
  have count : s.journal.length+ops.length-s.journal.length=ops.length := by omega
  rw [count]
  exact Source.ExecState.undoN_run s ops

theorem run {E Γ} (G : Source.Glob E) (F : Source.Fr) (n : Nat)
    (s : Source.EMState E Γ) (index : Source.Idx Γ (.bytes .calldata)) (off len : Nat)
    (requests : List (FiniteCellWrites.Request E F.this)) (allowed : F.static=false)
    (localValue : s.1.get index=Source.Val.cdRef rfl off len) :
    let bs := (F.cd.drop off).take len
    (program G F (n+4) index requests).run s=
      (.ok (.val (Source.mkBytes (D:=E.layout) (n:=32) (h:=by decide) (Source.wordBytes (G.fixed.hash bs)))),
        objectAllocatedState s (Source.Data.bytes (l:=.memory) bs)) := by
  first | (simp only;done) | decide | omega | rfl | skip
  unfold program
  rw [Source.Hoare.run_bind]
  change ((CellWritesCalldataHash.program G F (n+4) index requests >>= fun value =>
    Source.rollbackTo (s.2.ex.journal.length,s.2.logs.length,s.2.heap) *> pure value).run s)=_
  rw [Source.Hoare.run_bind,CellWritesCalldataHash.run G F n s index off len requests allowed localValue]
  unfold CellWritesCalldataHash.afterWrites
  rw [FiniteCellWrites.run F s requests allowed]
  simp only [Source.rollbackTo,Source.EM.modSt]
  let result : Source.R (Source.RVal E.layout Source.STy.bytes32) :=
    .ok (.val (Source.mkBytes (D:=E.layout) (n:=32) (h:=by decide)
      (Source.wordBytes (G.fixed.hash ((F.cd.drop off).take len)))))
  change (result,(s.1,{s.2 with
    ex:=(s.2.ex.run (CellHashFrames.operations F requests)).undoN
      ((s.2.ex.run (CellHashFrames.operations F requests)).journal.length-s.2.ex.journal.length),
    heap:=(objectAllocatedState s (Source.Data.bytes (l:=.memory) ((F.cd.drop off).take len))).2.heap,
    logs:=s.2.logs.drop (s.2.logs.length-s.2.logs.length)}))=_
  rw [undo]
  simp only [Nat.sub_self,List.drop_zero]
  rfl
theorem low {E Γ} (G : Source.Glob E) (F : Source.Fr) (horizon : Nat)
    (s : Source.EMState E Γ) (index : Source.Idx Γ (.bytes .calldata))
    (requests : List (FiniteCellWrites.Request E F.this)) (allowed : F.static=false)
    (short : horizon<4) :
    (program G F horizon index requests).run s=
      (.error .timeout,CellWritesCalldataHash.afterWrites F s requests) := by
  first | (simp only;done) | decide | omega | rfl | skip
  unfold program
  rw [Source.Hoare.run_bind]
  change ((CellWritesCalldataHash.program G F horizon index requests >>= fun value =>
    Source.rollbackTo (s.2.ex.journal.length,s.2.logs.length,s.2.heap) *> pure value).run s)=_
  rw [Source.Hoare.run_bind,CellWritesCalldataHash.low_horizon G F horizon s index requests allowed short]

theorem reconstructed {E Γ} (G : Source.Glob E) (F : Source.Fr) (n : Nat)
    (s : Source.EMState E Γ) (index : Source.Idx Γ (.bytes .calldata)) (off len : Nat)
    (requests : List (FiniteCellWrites.Request E F.this)) (allowed : F.static=false)
    (localValue : s.1.get index=Source.Val.cdRef rfl off len)
    (ps ts : List (ScalarPath E.layout (E.lay F.this))) (sep : finiteSeparated ps)
    (maps : SlotView × SlotView) (view : finiteView ps (s.2.ex.world.accounts F.this).storage maps.1)
    (residual : ResidualJournal complementCarrierOwnership) :
    let reached := (program G F (n+4) index requests).run s
    finiteEncode ps (reached.2.2.ex.world.accounts F.this).storage
      (fun slot => (LinkedCellHash.prepare F.this ps ts maps residual).cells
        (complementKey false F.this slot))=some maps.1 := by
  first | (simp only;done) | decide | omega | rfl | skip
  dsimp only
  rw [run G F n s index off len requests allowed localValue,LinkedCellHash.persistent_cells]
  exact finiteEncode_fromComplement ps _ maps.1 sep view
end Solidity.Yul.Views.CellHashRollback
