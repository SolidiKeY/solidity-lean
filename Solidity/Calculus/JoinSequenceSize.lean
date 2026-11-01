import Solidity.Calculus.JoinSequence
import Solidity.Calculus.TermSize

/-! # Size of joined assignment programs
These count emitted program syntax, separately from walked leaves. -/
namespace Solidity
variable {C : Contract} {Γ : Ctx}

/-- Guarding each Solidity write adds exactly three syntax nodes. -/
theorem LocalWrites.guarded_size (writes : LocalWrites C Γ) (positive : Bool)
    (tail : Prog C (.val .bool :: Γ) (.val .bool :: Γ)) :
    (writes.guarded positive tail).size =
      writes.program.size + 3 * writes.length + tail.size := by
  induction writes with
  | nil => simp only [LocalWrites.guarded, LocalWrites.program, List.foldr_nil, Prog.size, List.length_nil, Nat.mul_zero, Nat.zero_add, Nat.add_zero]
  | cons w rest ih =>
    cases positive <;>
      simp only [LocalWrites.guarded, LocalWrites.program, List.foldr_cons, Bool.false_eq_true, ↓reduceIte, Prog.size,
        Stmt.size, Val.size, Simple.size, Val.size_up, List.length_cons] at * <;> omega

/-- The snapshot adds three nodes; every original write gains three guard
nodes. This counts both branches, including the unselected one. -/
theorem LocalWrites.joined_size (name : Var) (c : Simple C Γ .bool)
    (thn els : LocalWrites C Γ) :
    (LocalWrites.joined name c thn els).size =
      (Stmt.ite (.simple c) thn.program els.program).size +
        3 * (thn.length + els.length) := by
  simp only [LocalWrites.joined, Prog.size, Stmt.size, Val.size, Simple.size, LocalWrites.guarded_size]
  omega

/-- Every Solidity write contributes at least its assignment node. -/
theorem LocalWrites.length_le_program_size (writes : LocalWrites C Γ) :
    writes.length ≤ writes.program.size := by
  induction writes with
  | nil => exact Nat.le_refl 0
  | cons w rest ih =>
    simp only [LocalWrites.program, List.foldr_cons, Prog.size, Stmt.size, List.length_cons] at *
    omega

/-- Joined assignment syntax grows at most linearly, including both guarded
branches and the snapshot. This is a program-size law, not a leaf-size law. -/
theorem LocalWrites.joined_size_le (name : Var) (c : Simple C Γ .bool)
    (thn els : LocalWrites C Γ) :
    (LocalWrites.joined name c thn els).size ≤
      4 * (Stmt.ite (.simple c) thn.program els.program).size := by
  rw [LocalWrites.joined_size]
  have ht : thn.length ≤ thn.program.size := LocalWrites.length_le_program_size thn
  have he : els.length ≤ els.program.size := LocalWrites.length_le_program_size els
  simp only [Stmt.size, Val.size, Simple.size]
  omega

/-- The dispatcher capture emits one block node beyond the raw builder.
Both guarded branches and the snapshot declaration are counted. -/
theorem LocalWrites.captured_size (name : Var) (c : Simple C Γ .bool)
    (thn els : LocalWrites C Γ) :
    (Prog.cons (.declLocal .bool name (some (.simple c)))
      (.cons (.block (thn.guarded true (els.guarded false))) .nil)).size =
      (Stmt.ite (.simple c) thn.program els.program).size +
        3 * (thn.length + els.length) + 1 := by
  simp only [Prog.size, Stmt.size, Val.size, Simple.size, LocalWrites.guarded_size]
  omega

/-- The actual selected Solidity dispatcher plan, including its snapshot and
block, has linear emitted program size. This does not bound walked leaves. -/
theorem LocalWrites.joinPlan_size_le (name : Var) (c : Simple C Γ .bool)
    {Δ Ε : Ctx} (thn : Prog C Γ Δ) (els : Prog C Γ Ε)
    (body : Prog C (.val .bool :: Γ) (.val .bool :: Γ))
    (h : Upd.ifJoin? c.lower thn els = some (.inr body)) :
    (Prog.cons (.declLocal .bool name (some (.simple c)))
      (.cons (.block body) .nil)).size ≤
      4 * (Stmt.ite (.simple c) thn els).size + 1 := by
  cases hs : Upd.ifJoinSingle? c.lower thn els with
  | some u => simp only [Upd.ifJoin?, hs] at h; cases h
  | none =>
    cases ht : thn.localWrites? with
    | none => simp only [Upd.ifJoin?, hs, ht] at h; cases h
    | some a =>
      cases he : els.localWrites? with
      | none => simp only [Upd.ifJoin?, hs, ht, he] at h; cases h
      | some b =>
        cases hp : JoinBoundary.boundary a b with
        | true => simp only [Upd.ifJoin?, hs, ht, he, hp] at h; cases h
        | false =>
          simp only [Upd.ifJoin?, hs, ht, he, hp, Bool.false_eq_true, ↓reduceIte,
            Option.some.injEq, Sum.inr.injEq] at h
          subst body
          rcases Prog.localWrites?_reconstruct thn a ht with ⟨rfl, rfl⟩
          rcases Prog.localWrites?_reconstruct els b he with ⟨rfl, rfl⟩
          rw [LocalWrites.captured_size]
          have ha : a.length ≤ a.program.size := LocalWrites.length_le_program_size a
          have hb : b.length ≤ b.program.size := LocalWrites.length_le_program_size b
          simp only [Stmt.size, Val.size, Simple.size]
          omega

end Solidity
