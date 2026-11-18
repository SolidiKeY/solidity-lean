import Solidity.Correctness.Lowering.Sim.Smoke

/-!
# Statement cases: the jumps

`jump_cases`: the `jump` conjunct of `StmtCases` (`return`, `break`,
`continue`, `_`), for both arms at every callback record.

* `elabStmt1With` refuses a jump (`jump_arm`, `Sim/Smoke.lean`).
* `elabStmtPWith` at an arbitrary record returns whatever the record's
  callbacks return, so its case is read at the site: `SiteSim` has the receipt
  of the actual elaboration of `[s]` as a premise, and the actual knot refuses
  a jump (`jump_refuses`, at the record `elabRec C ()` by the equations of
  `elabKernelTotal`: the rewriting passes keep a jump, `hoistStmtWith`
  captures nothing of it and `elabStmt1With` throws). No body is elaborated
  to the output of a jump, so the obligations hold of no run.

The passes that rewrite the expression of `return e` (`RawExpr.orderNamed`,
`fnPure`, `bytesPure`, `narrowPure`, the last three `partial`) are not
unfolded: whatever they return, what follows refuses (`Refuses.bind`).
-/

namespace Solidity.Correctness.Lowering.Sim

open Solidity.Goals (ElabRan elabKernelTotal)

/-- `x` refuses: no run of it succeeds. -/
def Refuses {α : Type} (x : ElabM α) : Prop :=
  ∀ (sc : ElabScope) (st : ECtx × Nat) (m : CallMemo), ∃ e, ((x.run sc).run st).run m = .error e

/-- A step followed by a refusal refuses. -/
theorem Refuses.bind {α β : Type} (x : ElabM α) (k : α → ElabM β) (h : ∀ a, Refuses (k a)) :
    Refuses (x >>= k) := by
  intro sc st m
  cases hx : x sc st m with
  | error e => exact ⟨e, by show (x sc st m >>= _) = _; rw [hx]; rfl⟩
  | ok r =>
    obtain ⟨⟨a, st'⟩, m'⟩ := r
    obtain ⟨e, he⟩ := h a sc st' m'
    exact ⟨e, by show (x sc st m >>= _) = _; rw [hx]; exact he⟩

/-- A refusal followed by anything refuses. -/
theorem Refuses.first {α β : Type} {x : ElabM α} (h : Refuses x) (k : α → ElabM β) :
    Refuses (x >>= k) := by
  intro sc st m
  obtain ⟨e, he⟩ := h sc st m
  exact ⟨e, by show (x sc st m >>= _) = _; rw [show x sc st m = .error e from he]; rfl⟩

theorem lift_pure {α : Type} (x : α) : ElabM.lift (pure x) = pure x := rfl

theorem lift_bind {α β : Type} (x : Except String α) (f : α → Except String β) :
    ElabM.lift (x >>= f) = ElabM.lift x >>= fun a => ElabM.lift (f a) := by
  cases x <;> rfl

variable [FreshNames] (C : Contract)

/-- The record's statement-capture and statement fields are their arms
(two clauses of `ElabKernelFix`). -/
def Tied (rc : ElabRec C) : Prop :=
  rc.hoistStmt = hoistStmtWith C rc ∧ rc.elabStmt1 = elabStmt1With C rc

theorem ret_capture (rc : ElabRec C) (i : Option RawExpr) :
    hoistStmtWith C rc (.ret i) = pure ([], .ret i) := rfl

theorem ret_refused (rc : ElabRec C) (i : Option RawExpr) :
    elabStmt1With C rc (.ret i) = throw "`return` outside a function's body" := rfl

/-- `elabStmtPWith` on a jump, at a tied record: the passes reduced on the
statement, then every remaining step skipped up to the refusal. -/
macro "refuse_jump" tied:ident : tactic => `(tactic| (
  unfold elabStmtPWith
  simp only [($tied).1, ($tied).2, RawStmt.mapExprsM, bytesStmt, RawStmt.exprs, lift_pure,
    lift_bind, map_eq_pure_bind, pure_bind, bind_assoc, Bool.false_eq_true, if_false, List.map_nil,
    List.forIn_nil, ite_self, Option.mapM, Option.toList, ret_capture, ret_refused]
  repeat (first | exact fun _ _ _ => ⟨_, rfl⟩ | refine Refuses.bind _ _ fun _ => ?_)))

theorem brk_refuses (rc : ElabRec C) (tied : Tied C rc) : Refuses (elabStmtPWith C rc .brk) := by
  refuse_jump tied

theorem cont_refuses (rc : ElabRec C) (tied : Tied C rc) : Refuses (elabStmtPWith C rc .cont) := by
  refuse_jump tied

theorem hole_refuses (rc : ElabRec C) (tied : Tied C rc) : Refuses (elabStmtPWith C rc .hole) := by
  refuse_jump tied

theorem ret_refuses (rc : ElabRec C) (tied : Tied C rc) :
    Refuses (elabStmtPWith C rc (.ret none)) := by
  refuse_jump tied

theorem retValue_refuses (rc : ElabRec C) (tied : Tied C rc) (e : RawExpr) :
    Refuses (elabStmtPWith C rc (.ret (some e))) := by
  refuse_jump tied

omit [FreshNames] in
/-- The statements of the jump family. -/
theorem jump_shape {s : RawStmt} (family : stmtFamily s = .jump) :
    s = .brk ∨ s = .cont ∨ s = .hole ∨ ∃ i, s = .ret i := by
  unfold stmtFamily at family
  split at family <;> first
    | (cases family; done) | exact .inl rfl | exact .inr (.inl rfl) | exact .inr (.inr (.inl rfl))
    | exact .inr (.inr (.inr ⟨_, rfl⟩))

/-- **A tied record refuses every jump** in `elabStmtPWith`. -/
theorem jump_refuses (rc : ElabRec C) (tied : Tied C rc) (s : RawStmt)
    (family : stmtFamily s = .jump) : Refuses (elabStmtPWith C rc s) := by
  obtain rfl | rfl | rfl | ⟨i, rfl⟩ := jump_shape family
  · exact brk_refuses C rc tied
  · exact cont_refuses C rc tied
  · exact hole_refuses C rc tied
  · cases i
    · exact ret_refuses C rc tied
    · exact retValue_refuses C rc tied _

/-- **The jump case** of `StmtCases`: both arms, at every record. -/
theorem jump_cases (kernel : elabKernelTotal) (rc : ElabRec C) : StmtArm C rc .jump := by
  refine ⟨fun s family sc st P st' _ b Γ o m run => ?_, jump_arm C rc⟩
  obtain ⟨raw, _, _, _, _, ran, _⟩ := run
  obtain ⟨⟨_, cons, stmtP, stmt1, capture, _⟩, names, _⟩ := kernel.1 C
  have block : (elabRec C ()).elabStmtsP = elabStmtsP C :=
    names.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  rw [raw, ← block, cons, stmtP] at ran
  obtain ⟨e, refused⟩ := (jump_refuses C _ ⟨capture, stmt1⟩ s family).first
    (fun P => do let Q ← (elabRec C ()).elabStmtsP []; pure (P ++ Q))
    o.elabScope o.beforeElab.locals o.beforeElab.memo
  cases refused.symm.trans ran

end Solidity.Correctness.Lowering.Sim
