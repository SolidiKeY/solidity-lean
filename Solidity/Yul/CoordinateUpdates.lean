import Solidity.Yul.LocalCoordinates
import Solidity.Yul.DirectUpdates

/-! Raw update transport through actual typed logical coordinates. Both inverse
laws belong to Coordinates; canonical/prepend producers construct them. These
are local-word facts, not stack allocation or physical/compiler correctness. -/
namespace Solidity.Yul.Coordinates
open Closed

def encodeOutcome {X c n m} (coordinates : Coordinates X n m)
    (result : WordAdapter.Outcome X c n) : Closed.Outcome c m :=
  ⟨coordinates.pack result.state,result.flow⟩

theorem pack_write {X n m} (coordinates : Coordinates X n m)
    (target : Target X n) (policy : Policy.TargetP .A target) (value : Word) (state : WordState X n) :
    coordinates.pack (DirectUpdates.write target policy value state) =
      writeTarget (WordAdapter.target target policy coordinates.locals coordinates.cells)
        value (coordinates.pack state) := by
  cases target with
  | «local» index =>
    funext position
    change coordinates.pack (DirectUpdates.write (.local index) policy value state) position =
      writeTarget (.local (coordinates.locals index)) value (coordinates.pack state) position
    by_cases same : position = coordinates.locals index
    · subst position
      rw [writeTarget_same,pack_local]
      exact if_pos rfl
    · rw [writeTarget_other _ _ _ _ same]
      simp only [pack]
      cases source : coordinates.origin position with
      | inl i =>
        change (if i = index then value else state.locals i) = state.locals i
        apply if_neg
        intro equal
        apply same
        apply coordinates.origin_injective
        rw [source,coordinates.origin_local,equal]
      | inr cell => rfl
  | external ref =>
    let cell := ref.wordWrite policy
    funext position
    change coordinates.pack (DirectUpdates.write (.external ref) policy value state) position =
      writeTarget (.local (coordinates.cells cell)) value (coordinates.pack state) position
    by_cases same : position = coordinates.cells cell
    · subst position
      rw [writeTarget_same,pack_cell]
      exact WordCells.write_same state.cells cell value
    · rw [writeTarget_other _ _ _ _ same]
      simp only [pack]
      cases source : coordinates.origin position with
      | inl i => rfl
      | inr other =>
        apply WordCells.write_other
        intro equal
        apply same
        apply coordinates.origin_injective
        rw [source,coordinates.origin_cell,equal]

theorem pack_writeValues {X n m} (coordinates : Coordinates X n m)
    (r : Nat) (targets : Fin r → Target X n) (policy : ∀ i, Policy.TargetP .A (targets i))
    (values : Values r) (state : WordState X n) :
    coordinates.pack (DirectUpdates.writeValues r targets policy values state) =
      Closed.writeValues r
        (fun i => WordAdapter.target (targets i) (policy i) coordinates.locals coordinates.cells)
        values (coordinates.pack state) := by
  induction r generalizing state with
  | zero => rfl
  | succ r ih =>
    change coordinates.pack (DirectUpdates.writeValues r _ _ _ (DirectUpdates.write _ _ _ state)) = _
    rw [ih,pack_write]
    rfl

theorem assign_agrees (fuel : Nat) {X n m r} {c : Control} (coordinates : Coordinates X n m)
    (targets : Fin r → Target X n) (rhs : Expr [] X n r)
    (policy : Policy.StmtP .A (Stmt.assign (c := c) targets rhs)) (state : WordState X n) :
    (DirectUpdates.assign fuel targets rhs policy state).map
      (fun final => (⟨coordinates.pack final,.normal⟩ : Outcome c m)) =
      evalStmt fuel .nil True.intro
        (WordAdapter.statement (Stmt.assign (c := c) targets rhs)
          policy coordinates.locals coordinates.cells).code
        (WordAdapter.statement (Stmt.assign (c := c) targets rhs)
          policy coordinates.locals coordinates.cells).words (coordinates.pack state) := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
    rw [DirectUpdates.assign,WordAdapter.statement]
    simp only [WordAdapter.tabulate_eq]
    rw [evalStmt_assign,←expression_agrees fuel coordinates]
    cases done : DirectWords.eval fuel rhs policy.2 state with
    | none => rfl
    | some values =>
      change some (⟨coordinates.pack (DirectUpdates.writeValues r targets policy.1 values state),.normal⟩ : Outcome c m) = _
      rw [pack_writeValues]
      rfl


theorem canonical_encode {X c n} (result : WordAdapter.Outcome X c n) :
    encodeOutcome (canonical X n) result = result.encode := by
  change (⟨(canonical X n).pack result.state,result.flow⟩ : Closed.Outcome c (n+wordCellCount X)) =
    ⟨result.state.pack,result.flow⟩
  rw [canonical_pack]

end Solidity.Yul.Coordinates
