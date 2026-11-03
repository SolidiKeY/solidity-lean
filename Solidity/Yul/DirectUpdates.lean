import Solidity.Yul.DirectWords
import Solidity.Yul.WordUpdates

/-! Direct raw target updates, separate from the closed packed-local updater.
Actual open targets write actual locals or typed raw external cells. This
component does not clean words, mutate physical state, or define function calls. -/
namespace Solidity.Yul.DirectUpdates
open Closed

def write {X n} (target : Target X n) :
    Policy.TargetP .A target → Word → WordState X n → WordState X n :=
  match target with
  | .local index => fun _ value state =>
      ⟨fun i => if i = index then value else state.locals i,state.cells⟩
  | .external ref => fun policy value state =>
      ⟨state.locals,state.cells.write (ref.wordWrite policy) value⟩

theorem pack_right {X n} (state : WordState X n) (i : Fin (wordCellCount X)) :
    state.pack (Fin.natAdd n i) = state.cells.pack X i := Fin.addCases_right i

theorem pack_write {X n} (target : Target X n) (policy : Policy.TargetP .A target)
    (value : Word) (state : WordState X n) :
    (write target policy value state).pack =
      writeTarget
        (WordAdapter.target target policy (Fin.castAdd (wordCellCount X))
          (fun cell => Fin.natAdd n cell.slot)) value state.pack := by
  cases target with
  | «local» index =>
    funext position
    refine Fin.addCases (motive := fun position =>
      (write (Target.local index) policy value state).pack position =
        writeTarget (.local (Fin.castAdd (wordCellCount X) index)) value state.pack position)
      ?_ ?_ position
    · intro i
      rw [WordState.pack_local]
      change (if i = index then value else state.locals i) =
        (if Fin.castAdd (wordCellCount X) i = Fin.castAdd (wordCellCount X) index
         then value else state.pack (Fin.castAdd (wordCellCount X) i))
      rw [state.pack_local]
      simp only [Fin.ext_iff]
      rfl
    · intro i
      rw [WordState.pack,Fin.addCases_right]
      change state.cells.pack X i =
        (if Fin.natAdd n i = Fin.castAdd (wordCellCount X) index
         then value else state.pack (Fin.natAdd n i))
      rw [pack_right]
      apply (if_neg _).symm
      intro same
      have bad := congrArg Fin.val same
      change n + i.val = index.val at bad
      have bound := index.isLt
      omega
  | external ref =>
    let cell := ref.wordWrite policy
    funext position
    refine Fin.addCases (motive := fun position =>
      (write (Target.external ref) policy value state).pack position =
        writeTarget (.local (Fin.natAdd n cell.slot)) value state.pack position)
      ?_ ?_ position
    · intro i
      rw [WordState.pack_local]
      change state.locals i =
        (if Fin.castAdd (wordCellCount X) i = Fin.natAdd n cell.slot
         then value else state.pack (Fin.castAdd (wordCellCount X) i))
      rw [state.pack_local,if_neg]
      intro same
      have bad := congrArg Fin.val same
      change i.val = n + cell.slot.val at bad
      have bound := i.isLt
      omega
    · intro i
      rw [WordState.pack,Fin.addCases_right]
      change (state.cells.write cell value).pack X i =
        (if Fin.natAdd n i = Fin.natAdd n cell.slot
         then value else state.pack (Fin.natAdd n i))
      rw [WordCells.pack_write,pack_right]
      change (if i = cell.slot then value else state.cells.pack X i) =
        (if Fin.natAdd n i = Fin.natAdd n cell.slot
         then value else state.cells.pack X i)
      have same : (Fin.natAdd n i = Fin.natAdd n cell.slot) ↔ i = cell.slot := by
        constructor
        · intro equal
          apply Fin.ext
          exact Nat.add_left_cancel (congrArg Fin.val equal)
        · exact congrArg (Fin.natAdd n)
      simp only [same]

def writeValues {X n} : (r : Nat) → (targets : Fin r → Target X n) →
    (∀ i, Policy.TargetP .A (targets i)) → Values r → WordState X n → WordState X n
  | 0, _, _, _, state => state
  | r+1, targets, policy, values, state =>
      writeValues r (fun i => targets i.castSucc) (fun i => policy i.castSucc)
        (fun i => values i.castSucc)
        (write (targets (Fin.last r)) (policy (Fin.last r)) (values (Fin.last r)) state)

theorem pack_writeValues {X n} (r : Nat) (targets : Fin r → Target X n)
    (policy : ∀ i, Policy.TargetP .A (targets i)) (values : Values r)
    (state : WordState X n) :
    (writeValues r targets policy values state).pack =
      Closed.writeValues r
        (fun i => WordAdapter.target (targets i) (policy i)
          (Fin.castAdd (wordCellCount X)) (fun cell => Fin.natAdd n cell.slot))
        values state.pack := by
  induction r generalizing state with
  | zero => rfl
  | succ r ih =>
    change (writeValues r _ _ _ (write _ _ _ state)).pack = _
    rw [ih,pack_write]
    rfl

/-- One actual assignment constructor, evaluating all RHS results before writes.
Zero is timeout, and a successor uses exactly its predecessor for the RHS. -/
def assign (fuel : Nat) {X n r} {c : Control} (targets : Fin r → Target X n)
    (rhs : Expr [] X n r) (policy : Policy.StmtP .A
      (Stmt.assign (c := c) targets rhs))
    (state : WordState X n) : Option (WordState X n) :=
  match fuel with
  | 0 => none
  | k+1 => do
      let values ← DirectWords.eval k rhs policy.2 state
      pure (writeValues r targets policy.1 values state)

theorem assign_agrees (fuel : Nat) {X n r} {c : Control} (targets : Fin r → Target X n)
    (rhs : Expr [] X n r) (policy : Policy.StmtP .A
      (Stmt.assign (c := c) targets rhs))
    (state : WordState X n) :
    (assign fuel targets rhs policy state).map
      (fun final => (⟨final.pack,.normal⟩ : Outcome c (n+wordCellCount X))) =
      (evalStmt fuel .nil True.intro
        (WordAdapter.statement (Stmt.assign (c := c) targets rhs)
          policy (Fin.castAdd (wordCellCount X))
          (fun cell => Fin.natAdd n cell.slot)).code
        (WordAdapter.statement (Stmt.assign (c := c) targets rhs)
          policy (Fin.castAdd (wordCellCount X))
          (fun cell => Fin.natAdd n cell.slot)).words state.pack) := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
    rw [assign,WordAdapter.statement]
    simp only [WordAdapter.tabulate_eq]
    rw [evalStmt_assign,←DirectWords.packed_agrees]
    cases done : DirectWords.eval fuel rhs policy.2 state with
    | none => rfl
    | some values =>
      change some (⟨(writeValues r targets policy.1 values state).pack,.normal⟩ : Outcome c (n+wordCellCount X)) = _
      rw [pack_writeValues]
      rfl

end Solidity.Yul.DirectUpdates
