import Solidity.Calculus.Shift

/-!
# Sequential local assignments for a joined branch

A branch is recognized without substituting a value into its successors.
The recognizer uses an explicit indexed program motive (Gate G0), delaying
its tail so rejected branches are not traversed. A Boolean
snapshot is a fresh intrinsic head local. Every original write is shifted
past it, so changing the source guard cannot change the selected branch.
-/

namespace Solidity
variable {C : Contract} {Γ : Ctx}

/-- A sequence of value-local writes, all in one intrinsic context. -/
abbrev LocalWrites (C : Contract) (Γ : Ctx) :=
  List ((p : PrimTy) × Idx Γ (.val p) × Val C Γ p)

/-- Add a local write to a decoded tail. All other statements refuse it.
The tail is delayed so a refusal does not demand a recursive decoded value. -/
def Stmt.prependLocalWrites? {Δ : Ctx} (s : Stmt C Γ Δ) :
    (Unit → Option (LocalWrites C Δ)) → Option (LocalWrites C Γ) :=
  Stmt.casesOn (motive_1 := fun Γ Δ _ => (Unit → Option (LocalWrites C Δ)) → Option (LocalWrites C Γ)) s
    (assign := fun _ _ => fun _ => none) (rebind := fun _ _ => fun _ => none)
    (assignLocal := fun i r rest => (rest ()).map (fun writes => ⟨_, i, r⟩ :: writes))
    (declLocal := fun _ _ _ => fun _ => none) (declStorage := fun _ _ _ => fun _ => none)
    (opAssign := fun _ _ _ _ _ => fun _ => none) (incDec := fun _ _ _ => fun _ => none)
    (assignIncDec := fun _ _ _ _ _ => fun _ => none) (assignLocalPush := fun _ _ => fun _ => none)
    (push := fun _ _ _ => fun _ => none) (pop := fun _ => fun _ => none) (transfer := fun _ _ => fun _ => none)
    (send := fun _ _ _ _ => fun _ => none) (declMem := fun _ _ _ _ _ => fun _ => none)
    (rebindMem := fun _ _ => fun _ => none) (assignFromMem := fun _ _ => fun _ => none)
    (assignMem := fun _ _ => fun _ => none) (delete := fun _ => fun _ => none) (deleteMem := fun _ _ => fun _ => none)
    (assignNew := fun _ _ _ => fun _ => none) (ite := fun _ _ _ => fun _ => none) (require := fun _ => fun _ => none)
    (assert := fun _ => fun _ => none) (revert := fun _ => none) (assumeFalse := fun _ => none)
    (call := fun _ _ _ _ => fun _ => none) (tryCall := fun _ _ _ _ _ _ _ _ _ _ => fun _ => none)
    (loop := fun _ _ _ => fun _ => none) (block := fun _ => fun _ => none)
    (pushOpAssign := fun _ _ _ _ _ => fun _ => none) (pushIncDec := fun _ _ _ => fun _ => none)
    (callReceiver := fun _ _ _ _ _ => fun _ => none) (callReceiverPush := fun _ _ _ _ _ _ => fun _ => none)
    (callRec := fun _ _ _ _ _ => fun _ => none) (revertData := fun _ => fun _ => none)
    (catchData := fun _ _ _ _ _ _ _ _ => fun _ => none)

/-- Recognize exactly a sequence of value-local assignments. The explicit
indexed `casesOn` motive never matches on the context; a rejected head does
not force decoding its tail or any nested loop/call/branch body. -/
def Prog.localWrites? {Γ Δ : Ctx} (P : Prog C Γ Δ) : Option (LocalWrites C Γ) :=
  Prog.casesOn (motive_2 := fun Γ _ _ => Option (LocalWrites C Γ)) P
    (some []) (fun s tail => s.prependLocalWrites? (fun _ => tail.localWrites?))
termination_by structural P

/-- The original writes, in order; each right-hand side reads the state
left by its predecessors, never a substituted term. -/
def LocalWrites.program (writes : LocalWrites C Γ) : Prog C Γ Γ :=
  writes.foldr (fun w tail => .cons (.assignLocal w.2.1 w.2.2) tail) .nil

/-- Each write is guarded by the snapshot at `.here`. The source target is
`.there i`, and its RHS is shifted once. An untaken RHS is never evaluated.
The explicit tail avoids joining programs through a context-indexed matcher. -/
def LocalWrites.guarded (positive : Bool) (writes : LocalWrites C Γ)
    (tail : Prog C (.val .bool :: Γ) (.val .bool :: Γ) := .nil) :
    Prog C (.val .bool :: Γ) (.val .bool :: Γ) :=
  writes.foldr (fun w rest =>
    let one : Prog C (.val .bool :: Γ) (.val .bool :: Γ) :=
      .cons (.assignLocal w.2.1.there w.2.2.up) .nil
    let guard : Stmt C (.val .bool :: Γ) (.val .bool :: Γ) :=
      if positive then .ite (.simple (.local .here)) one .nil
      else .ite (.simple (.local .here)) .nil one
    .cons guard rest) tail

/-- Snapshot `c` once, then the selected branch's writes in their original
order. A caller must pop the fresh head after the program. Names are supplied
by the caller's existing fresh-name budget; freshness is positional. -/
def LocalWrites.joined (name : Var) (c : Simple C Γ .bool) (thn els : LocalWrites C Γ) :
    Prog C Γ (.val .bool :: Γ) :=
  .cons (.declLocal .bool name (some (.simple c)))
    (thn.guarded true (els.guarded false))

/-- Solidity `x = a; y = b;`: decoding computes under bound contexts,
indices, values and primitive types (Gate G0). -/
theorem Prog.localWrites?_two {p q : PrimTy} (i : Idx Γ (.val p)) (j : Idx Γ (.val q))
    (a : Val C Γ p) (b : Val C Γ q) :
    (Prog.cons (.assignLocal i a) (.cons (.assignLocal j b) .nil)).localWrites? =
      some [⟨p, i, a⟩, ⟨q, j, b⟩] := by
  rfl

/-- The empty Solidity block has no writes. -/
theorem Prog.localWrites?_nil : (Prog.nil : Prog C Γ Γ).localWrites? = some [] := rfl

/-- Inspect one statement only; the recursive tail remains delayed. -/
theorem Prog.localWrites?_cons {Δ Ε : Ctx} (s : Stmt C Γ Δ) (tail : Prog C Δ Ε) :
    (Prog.cons s tail).localWrites? = s.prependLocalWrites? (fun _ => tail.localWrites?) := rfl

/-- A rejected Solidity head `revert();` does not inspect its continuation. -/
theorem Prog.localWrites?_revert {Δ : Ctx} (tail : Prog C Γ Δ) :
    (Prog.cons .revert tail).localWrites? = none := rfl

/-- Solidity `x = a; …`: the typed assignment is prepended without changing
any later RHS or its intrinsic input context. -/
theorem Prog.localWrites?_cons_assign {Δ : Ctx} {p : PrimTy} (i : Idx Γ (.val p))
    (a : Val C Γ p) (tail : Prog C Γ Δ) :
    (Prog.cons (.assignLocal i a) tail).localWrites? =
      tail.localWrites?.map (fun rest => ⟨p, i, a⟩ :: rest) := rfl

/-- Successful decoding of Solidity `x = a; …` preserves the output context
and reconstructs the entire intrinsic program, not merely its final values. -/
theorem Prog.localWrites?_reconstruct {Γ Δ : Ctx} (P : Prog C Γ Δ) (writes : LocalWrites C Γ)
    (h : P.localWrites? = some writes) : Δ = Γ ∧ HEq P writes.program := by
  induction writes generalizing Δ P with
  | nil =>
    cases P with
    | nil =>
      exact ⟨rfl, HEq.rfl⟩
    | cons s tail =>
      cases s <;> try cases h
      rename_i i r
      cases ht : tail.localWrites? <;> rw [Prog.localWrites?_cons_assign, ht] at h <;> cases h
  | cons w rest ih =>
    cases P with
    | nil => cases h
    | cons s tail =>
      cases s <;> try cases h
      rename_i i r
      cases ht : tail.localWrites? <;> rw [Prog.localWrites?_cons_assign, ht] at h <;> try cases h
      rcases ih tail ht with ⟨rfl, rfl⟩
      exact ⟨rfl, HEq.rfl⟩

end Solidity
