import Solidity.Yul.Views.ActualScalarSafety
import Solidity.Yul.Views.FiniteCellWrites

/-! Actual typed writes advance only the metadata-selected existing bank map.
Requests and patches reuse FiniteCellWrites; no source state or AST is copied.
The pair keeps one account/frame and stops on actual Source failure; static
flags are explicit operation inputs, not a runtime mode-transition theorem. -/
namespace Solidity.Yul.Views

def actualBankedScalarWrite {E Γ} (F : Source.Fr) (request : FiniteCellWrites.Request E F.this)
    (maps : SlotView × SlotView) (s : Source.EMState E Γ) :=
  let source := (Source.writeAt F request.1.path request.2).run s
  (source,match source.1 with | .error _ => maps | .ok _ => FiniteCellWrites.patch request maps)

theorem actualBankedScalarWrite_source {E Γ} (F : Source.Fr) (request : FiniteCellWrites.Request E F.this)
    (maps : SlotView × SlotView) (s : Source.EMState E Γ) :
    (actualBankedScalarWrite F request maps s).1=(Source.writeAt F request.1.path request.2).run s := rfl

theorem actualBankedScalarWrite_nonstatic {E Γ} (F : Source.Fr) (request : FiniteCellWrites.Request E F.this)
    (maps : SlotView × SlotView) (s : Source.EMState E Γ) (allowed : F.static=false) :
    actualBankedScalarWrite F request maps s=
      ((Source.setCell F request.1.path (some request.2)).run s,FiniteCellWrites.patch request maps) := by
  first | (simp only;done) | decide | omega | rfl | skip
  unfold actualBankedScalarWrite
  simp only [Source.writeAt,dite_true]
  rw [RepeatedCellWrites.one F s request.1 request.2 allowed]

theorem actualBankedScalarWrite_view {E Γ} (F : Source.Fr) (request : FiniteCellWrites.Request E F.this)
    (maps : SlotView × SlotView) (s : Source.EMState E Γ)
    (ps ts : List (ScalarPath E.layout (E.lay F.this))) (psep : finiteSeparated ps) (tsep : finiteSeparated ts)
    (registered : FiniteCellWrites.Registered ps ts request) (before : FiniteCellWrites.Views F ps ts s maps)
    (allowed : F.static=false) :
    FiniteCellWrites.Views F ps ts (actualBankedScalarWrite F request maps s).1.2
      (actualBankedScalarWrite F request maps s).2 := by
  first | (simp only;done) | decide | omega | rfl | skip
  rw [actualBankedScalarWrite_nonstatic F request maps s allowed]
  exact FiniteCellWrites.step F s ps ts psep tsep request registered maps before allowed

def actualBankedScalarPair {E Γ} (F : Source.Fr) (secondStatic : Bool)
    (first second : FiniteCellWrites.Request E F.this) (maps : SlotView × SlotView) (s : Source.EMState E Γ) :=
  let one := actualBankedScalarWrite F first maps s
  match one.1.1 with
  | .error _ => one
  | .ok _ => actualBankedScalarWrite {F with static:=secondStatic} second one.2 one.1.2

theorem actualBankedScalarPair_source {E Γ} (F : Source.Fr) (secondStatic : Bool)
    (first second : FiniteCellWrites.Request E F.this) (maps : SlotView × SlotView) (s : Source.EMState E Γ) :
    (actualBankedScalarPair F secondStatic first second maps s).1=
      (do Source.writeAt F first.1.path first.2
          Source.writeAt {F with static:=secondStatic} second.1.path second.2).run s := by
  first | (simp only;done) | decide | omega | rfl | skip
  rw [Source.Hoare.run_bind]
  unfold actualBankedScalarPair actualBankedScalarWrite
  cases actual : (Source.writeAt F first.1.path first.2).run s with
  | mk result after => cases result <;> rfl

theorem actualBankedScalarPair_MemOK {E Γ} (F : Source.Fr) (secondStatic : Bool)
    (first second : FiniteCellWrites.Request E F.this) (maps : SlotView × SlotView) (s : Source.EMState E Γ)
    (H : Source.HeapTy) (ok : Source.MemOK E H s) :
    Source.MemOK E H (actualBankedScalarPair F secondStatic first second maps s).1.2 := by
  first | (simp only;done) | decide | omega | rfl | skip
  have safe := Source.Hoare.bind (Source.writeAt_mem (H:=H) F first.1.path first.2)
    (fun _=>Source.writeAt_mem (H:=H) {F with static:=secondStatic} second.1.path second.2) s ok
  rw [actualBankedScalarPair_source]
  cases actual : (do Source.writeAt F first.1.path first.2
                     Source.writeAt {F with static:=secondStatic} second.1.path second.2).run s with
  | mk result after =>
    rw [actual] at safe
    cases result <;> exact safe
theorem actualBankedScalarPair_view {E Γ} (F : Source.Fr)
    (first second : FiniteCellWrites.Request E F.this) (maps : SlotView × SlotView) (s : Source.EMState E Γ)
    (ps ts : List (ScalarPath E.layout (E.lay F.this))) (psep : finiteSeparated ps) (tsep : finiteSeparated ts)
    (firstRegistered : FiniteCellWrites.Registered ps ts first)
    (secondRegistered : FiniteCellWrites.Registered ps ts second)
    (before : FiniteCellWrites.Views F ps ts s maps) (allowed : F.static=false) :
    FiniteCellWrites.Views F ps ts (actualBankedScalarPair F false first second maps s).1.2
      (actualBankedScalarPair F false first second maps s).2 := by
  first | (simp only;done) | decide | omega | rfl | skip
  have firstView := actualBankedScalarWrite_view F first maps s ps ts psep tsep firstRegistered before allowed
  rw [actualBankedScalarWrite_nonstatic F first maps s allowed,RepeatedCellWrites.one F s first.1 first.2 allowed] at firstView
  unfold actualBankedScalarPair
  rw [actualBankedScalarWrite_nonstatic F first maps s allowed,RepeatedCellWrites.one F s first.1 first.2 allowed]
  dsimp only
  exact actualBankedScalarWrite_view {F with static:=false} second _ _ ps ts psep tsep secondRegistered firstView rfl
end Solidity.Yul.Views
