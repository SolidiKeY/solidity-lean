import Solidity.Goals.ElabTotal

/-! Exact execution receipts for list, branch and scope composition.
Child executions are premises; no coverage or whole-branch execution is assumed.
The reader, locals, fresh counter and call memo are all retained explicitly. -/
namespace Solidity.Correctness.Lowering.Sim.CoverageBranch

open Solidity

variable {C : Contract}

/-- A successful execution including both state layers. -/
def Runs {α : Type} (x : ElabM α) (sc : ElabScope) (st : ECtx × Nat)
    (memo : CallMemo) (a : α) (out : ECtx × Nat) (memo' : CallMemo) : Prop :=
  ((x.run sc).run st).run memo = .ok ((a, out), memo')

/-- Individual receipts in execution order, with exact intermediate states.
The empty list performs no effects. -/
inductive Children (stmt : RawStmt → ElabM (SProg C)) (sc : ElabScope) :
    List RawStmt → (ECtx × Nat) → CallMemo → SProg C →
      (ECtx × Nat) → CallMemo → Prop where
  | nil (st memo) : Children stmt sc [] st memo [] st memo
  | cons {s ss st memo P mid memo₁ Q out memo₂}
      (head : Runs (stmt s) sc st memo P mid memo₁)
      (tail : Children stmt sc ss mid memo₁ Q out memo₂) :
      Children stmt sc (s :: ss) st memo (P ++ Q) out memo₂

/-- Nil executes successfully without changing either state layer. -/
theorem list_nil (stmt : RawStmt → ElabM (SProg C)) (sc st memo) :
    Runs (elabStmtsPWith C stmt []) sc st memo [] st memo := rfl

/-- Cons threads both state layers from the child into the remaining list. -/
theorem list_cons {stmt : RawStmt → ElabM (SProg C)} {sc st memo s ss P mid memo₁ Q out memo₂}
    (head : Runs (stmt s) sc st memo P mid memo₁)
    (tail : Runs (elabStmtsPWith C stmt ss) sc mid memo₁ Q out memo₂) :
    Runs (elabStmtsPWith C stmt (s :: ss)) sc st memo (P ++ Q) out memo₂ := by
  change (do
    let ((p, st₁), m₁) ← ((stmt s).run sc).run st |>.run memo
    let ((q, st₂), m₂) ← ((elabStmtsPWith C stmt ss).run sc).run st₁ |>.run m₁
    pure ((p ++ q, st₂), m₂)) = _
  rw [head]
  change (do
    let ((q, st₂), m₂) ← ((elabStmtsPWith C stmt ss).run sc).run mid |>.run memo₁
    pure ((P ++ q, st₂), m₂)) = _
  rw [tail]
  rfl

/-- Compose a list from its individual child receipts. -/
theorem list_run {stmt : RawStmt → ElabM (SProg C)} {sc ss st memo P out memo'}
    (children : Children stmt sc ss st memo P out memo') :
    Runs (elabStmtsPWith C stmt ss) sc st memo P out memo' := by
  induction children with
  | nil => exact list_nil _ _ _ _
  | cons head _ ih => exact list_cons head ih

/-- Branch children run with `top = false`, all other reader fields unchanged.
Entry locals are restored; the resulting fresh counter and memo survive. -/
theorem branch_run {stmt : RawStmt → ElabM (SProg C)} {sc ss Γ k memo P Δ k' memo'}
    (children : Children stmt { sc with top := false } ss (Γ, k) memo P (Δ, k') memo') :
    Runs (elabBranchWith C stmt ss) sc (Γ, k) memo P (Γ, k') memo' := by
  have h := list_run children
  change (do
    let ((p, st'), m) ← ((elabStmtsPWith C stmt ss).run { sc with top := false }).run
      (Γ, k) |>.run memo
    pure ((p, (Γ, st'.2)), m)) = _
  rw [h]
  rfl

/-- The chain's empty program retains the exact context. -/
theorem chain_nil (ns : List Var) (Δ : Ctx) :
    SProg.chain (C := C) ns Δ [] = .ok ⟨Δ, .nil⟩ := rfl

variable [FreshNames]

/-- Chain compatibility is checked at the names produced by the placed head. -/
theorem chain_cons {ns : List Var} {Δ Δ₁ Δ₂ : Ctx} {p : SStmt C} {ps : SProg C}
    {s : Stmt C Δ Δ₁} {q : Prog C Δ₁ Δ₂}
    (place : p.place ns Δ = .ok ⟨Δ₁, s⟩)
    (rest : SProg.chain (s.outNames ns) Δ₁ ps = .ok ⟨Δ₂, q⟩) :
    SProg.chain ns Δ (p :: ps) = .ok ⟨Δ₂, .cons s q⟩ := by
  simp only [SProg.chain]
  rw [place]
  change (do
    let ⟨Δ₂, P⟩ ← SProg.chain (s.outNames ns) Δ₁ ps
    pure (⟨Δ₂, .cons s P⟩ : Blk C Δ)) = _
  rw [rest]
  rfl

/-- A scope uses the supplied context's exact names and types for chaining. -/
theorem scope_run {branch : List RawStmt → ElabM (SProg C)} {Γ : NCtx}
    {ss sc st memo P out memo' b}
    (run : Runs (branch ss) sc st memo P out memo')
    (chain : SProg.chain Γ.names Γ.ctx P = .ok b) :
    Runs (elabScopeWith C branch Γ ss) sc st memo b out memo' := by
  change (do
    let ((p, st'), m) ← ((branch ss).run sc).run st |>.run memo
    ((ElabM.lift (SProg.chain Γ.names Γ.ctx p)).run sc).run st' |>.run m) = _
  rw [run]
  change (((ElabM.lift (SProg.chain Γ.names Γ.ctx P)).run sc).run out).run memo' = _
  rw [chain]
  rfl

/-- Actual list producer, with the same exact child state threading. -/
theorem actual_list {sc ss st memo P out memo'}
    (children : Children (elabStmtP C) sc ss st memo P out memo') :
    Runs (elabStmtsP C ss) sc st memo P out memo' :=
  list_run children

/-- Actual producer specialization, from individual statement receipts. -/
theorem actual_branch {sc ss Γ k memo P Δ k' memo'}
    (children : Children (elabStmtP C) { sc with top := false } ss
      (Γ, k) memo P (Δ, k') memo') :
    Runs (elabBranch C ss) sc (Γ, k) memo P (Γ, k') memo' :=
  branch_run children

/-- Actual scope producer, with branch execution derived from the children. -/
theorem actual_scope {sc ss} {Γ : NCtx} {entry k memo P Δ k' memo' b}
    (children : Children (elabStmtP C) { sc with top := false } ss
      (entry, k) memo P (Δ, k') memo')
    (chain : SProg.chain Γ.names Γ.ctx P = .ok b) :
    Runs (elabScope C Γ ss) sc (entry, k) memo b (entry, k') memo' :=
  scope_run (actual_branch children) chain

/-- The block arm of the actual producer follows from the kernel equations.
`hk` is supplied by the composing lane, rather than assumed as a new axiom. -/
theorem actual_block (hk : Solidity.Goals.elabKernelTotal)
    {sc ss Γ k memo P Δ k' memo'}
    (children : Children (elabStmtP C) { sc with top := false } ss
      (Γ, k) memo P (Δ, k') memo') :
    Runs (elabStmt1 C (.block ss)) sc (Γ, k) memo P (Γ, k') memo' := by
  have fix := (hk.1 C).1
  have names := (hk.1 C).2.1
  have hs : (elabRec C ()).elabStmt1 = elabStmt1 C :=
    names.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hb : (elabRec C ()).elabBranch = elabBranch C :=
    names.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have equation : elabStmt1 C (.block ss) = elabBranch C ss := by
    rw [← hs, fix.2.2.2.1]
    change (elabRec C ()).elabBranch ss = _
    rw [hb]
  rw [equation]
  exact actual_branch children

end Solidity.Correctness.Lowering.Sim.CoverageBranch
