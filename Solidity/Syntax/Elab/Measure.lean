import Solidity.Syntax.Elab.Arms

/-!
# A termination measure for the elaborator knot

The vocabulary in which a well-founded totalization of the `mutual` knot of
`Syntax/Elab/Stmt.lean` states its decrease, over the five recursive fields
that clause 2 of `Solidity.Goals.elabKernelTotal` (`ElabKernelInduction`)
names: `hoist`, `hoistStmt`, `elabStmtP`, `elabStmt1`, `elabStmtsP`.

* `ElabMeasure α`: one measure per field, of the input and the scope (the
  functions still inlinable, `ElabScope.funs`/`recs`), into a well-founded `α`.
* `ElabMeasure.cut μ a r`: `r` with each of the five fields failing at every
  call whose measure is not below `a`, the other fields kept.
* `ElabMeasure.Stable μ J m arm`: the arm at `x` gives the same result over
  `r` as over `cut μ (m x sc) r`, for every record `r` whose runs below the
  measure of `x` meet the guard `J`: the arm calls the five fields only below
  its own measure.  This is "the arm at `x` gives the same result for two
  records that agree below the measure of `x`", relativized to `J`.

The guard is needed.  With the trivial guard (`ElabPreds.top`) the shape
fails for every well-founded measure along one path
(`Solidity/Examples/ElabTotal/Measure.lean`, `rel_cycle_forT_blk`):
`elabStmtPWith` passes the statement `rc.hoistStmt` returns to `rc.elabStmt1`
(nested recursion), so over a record whose `hoistStmt` returns a `for` loop
with an initializer the arms call
`elabStmtP blk → elabStmt1 (for …) → elabStmtsP [blk] → elabStmtP blk` at one
scope.  Which guard makes the five arms stable is open: a candidate bounds
what `hoistStmt` and `hoist` return by their inputs, in the measure, and is
not established here.  `Solidity/Examples/ElabTotal/Measure.lean` shows that
clause 2 follows from guarded stability of the five arms and the guard's
preservation by them, for any guard.
-/

namespace Solidity

open Semantics

/-- A statement's block-bearing constructor and its unvisited child lists.
Statements without child blocks share `leaf`; loop forms remain distinct. -/
inductive StmtControl where
  | leaf
  | block (body : List RawStmt)
  | unchecked (body : List RawStmt)
  | checked (body : List RawStmt)
  | ite (yes no : List RawStmt)
  | tryCall (ok err panic other : List RawStmt)
  | whileLoop (body : List RawStmt)
  | doWhile (body : List RawStmt)
  | loop (body : List RawStmt)
  | forLoop (init update body : List RawStmt)

/-- Forget a statement's own expressions without forgetting its
block-bearing constructor or any statement inside a child block. -/
def RawStmt.control : RawStmt → StmtControl
  | .block b => .block b
  | .unchecked b => .unchecked b
  | .checked _ b => .checked b
  | .ite _ t e => .ite t e
  | .tryCall _ _ _ _ ok err _ panic other => .tryCall ok err panic other
  | .whileLoop _ _ b => .whileLoop b
  | .doWhile _ b _ => .doWhile b
  | .loop _ _ b => .loop b
  | .forLoop _ i _ u b => .forLoop i u b
  | _ => .leaf

/-- Expression rewriting preserves more than numeric weight: it keeps the
block-bearing constructor and every unvisited child statement, with the same effects. -/
theorem RawStmt.mapExprsM_control {m : Type → Type} [Monad m] [LawfulMonad m]
    (f : RawExpr → m RawExpr) (s : RawStmt) :
    control <$> s.mapExprsM f = (fun _ => control s) <$> s.mapExprsM f := by
  cases s <;> simp only [RawStmt.mapExprsM, map_bind,
    LawfulApplicative.map_pure, control]

/-- Rewriting a statement's own expressions leaves its control-tree
weight unchanged, including the blocks held by loops and branches. The
callback's effects are retained on both sides. -/
theorem CalleeKernel.mapExprsM_weight {m : Type → Type} [Monad m] [LawfulMonad m]
    (f : RawExpr → m RawExpr) (s : RawStmt) :
    stmtWeight <$> s.mapExprsM f =
      (fun _ => stmtWeight s) <$> s.mapExprsM f := by
  cases s <;> simp only [RawStmt.mapExprsM, map_bind,
    LawfulApplicative.map_pure, stmtWeight]

/-- The control-weight equality also holds of a successful expression
rewrite that accumulates a program while running the elaborator's states. -/
theorem CalleeKernel.mapExprsM_run_weight {C : Contract}
    (f : RawExpr → StateT (SProg C) ElabM RawExpr) (s s' : RawStmt)
    (P P' : SProg C) (sc : ElabScope) (st st' : ECtx × Nat) (m m' : CallMemo)
    (h : ((((s.mapExprsM f).run P).run sc).run st).run m = .ok (((s', P'), st'), m')) :
    stmtWeight s' = stmtWeight s := by
  have e := congrArg (fun x : StateT (SProg C) ElabM Nat => x P sc st m)
    (mapExprsM_weight f s)
  simp only [StateT.run, ReaderT.run] at h
  simp only [Functor.map, StateT.map, bind, ReaderT.bind, StateT.bind,
    pure, ReaderT.pure, StateT.pure, h, Except.bind, Except.pure] at e
  exact congrArg (fun x => x.1.1.1) (Except.ok.inj e)

namespace ElabControlProof

private def Obs {α : Type} (x : ElabM α) (Q : α → Prop) : Prop :=
  ∀ sc st m a st' m', x sc st m = .ok ((a, st'), m') → Q a
private theorem obs_pure {α : Type} {a : α} {Q : α → Prop} (h : Q a) :
    Obs (pure a) Q := by
  intro sc st m b st' m' he
  cases he
  exact h
private theorem obs_bind {α β : Type} {x : ElabM α} {f : α → ElabM β}
    {P : α → Prop} {Q : β → Prop} (hx : Obs x P)
    (hf : ∀ a, P a → Obs (f a) Q) : Obs (x >>= f) Q := by
  intro sc st m b st' m' h
  change (do let ((a, s), n) ← x sc st m; f a sc s n) = .ok ((b, st'), m') at h
  cases he : x sc st m with
  | error err => simp only [he, bind, Except.bind] at h; cases h
  | ok v =>
    rcases v with ⟨⟨a, s⟩, n⟩
    simp only [he, bind, Except.bind] at h
    exact hf a (hx sc st m a s n he) sc s n b st' m' h
private theorem obs_any {α β : Type} {x : ElabM α} {f : α → ElabM β}
    {Q : β → Prop} (hf : ∀ a, Obs (f a) Q) : Obs (x >>= f) Q :=
  obs_bind (P := fun _ => True) (fun _ _ _ _ _ _ _ => trivial) (fun a _ => hf a)
private theorem obs_throw {α : Type} {err : String} {Q : α → Prop} :
    Obs (throw err : ElabM α) Q := by
  intro sc st m a st' m' h
  cases h
private theorem obs_map {C : Contract} (f : RawExpr → StateT (SProg C) ElabM RawExpr)
    (s : RawStmt) (P : SProg C) :
    Obs ((s.mapExprsM f).run P) (fun out => out.1.control = s.control) := by
  intro sc st m out st' m' h
  have he := congrArg (fun x : StateT (SProg C) ElabM StmtControl => x P sc st m)
    (RawStmt.mapExprsM_control f s)
  simp only [Functor.map, StateT.map, bind, ReaderT.bind, StateT.bind,
    pure, ReaderT.pure, StateT.pure, StateT.run] at h he
  simp only [h, Except.bind, Except.pure] at he
  exact congrArg (fun x => x.1.1.1) (Except.ok.inj he)
private theorem assign_control [FreshNames] (C : Contract) (rc : ElabRec C)
    (ha : ∀ l r, Obs (rc.hoistAssign l r) (fun out => out.2.control = .leaf))
    (l r : RawExpr) : Obs (hoistStmtWith C rc (.assign l r))
      (fun out => out.2.control = .leaf) := by
  simp only [hoistStmtWith, bind_pure, pure_bind]
  repeat (with_reducible first
    | contradiction
    | (apply obs_pure; dsimp only [RawStmt.control] <;> rfl)
    | exact obs_throw
    | exact ha _ _
    | (apply obs_any; intro x)
    | split)
private theorem hoist_control [FreshNames] (C : Contract) (rc : ElabRec C)
    (ha : ∀ l r, Obs (rc.hoistAssign l r) (fun out => out.2.control = .leaf))
    (s : RawStmt) : Obs (hoistStmtWith C rc s) (fun out => out.2.control = s.control) := by
  cases s
  case assign l r => exact assign_control C rc ha l r
  all_goals simp only [hoistStmtWith, bind_pure, pure_bind, RawStmt.control]
  all_goals repeat (with_reducible first
    | contradiction
    | (apply obs_pure; dsimp only [RawStmt.control] <;> rfl)
    | exact obs_throw
    | exact ha _ _
    | (apply obs_bind (obs_map ..); intro out h
       apply obs_pure
       simpa only [RawStmt.control] using h)
    | (apply obs_any; intro x)
    | split)

end ElabControlProof

/-- Numeric control weight is a projection of the retained constructor and child lists. -/
def StmtControl.weight : StmtControl → Nat
  | .leaf => 1
  | .block b | .unchecked b | .checked b | .whileLoop b | .doWhile b | .loop b =>
      CalleeKernel.listWeight b + 1
  | .ite t e => CalleeKernel.listWeight t + CalleeKernel.listWeight e + 1
  | .tryCall ok err panic other => CalleeKernel.listWeight ok + CalleeKernel.listWeight err +
      CalleeKernel.listWeight panic + CalleeKernel.listWeight other + 1
  | .forLoop i u b => 2 * CalleeKernel.listWeight i + CalleeKernel.listWeight u +
      CalleeKernel.listWeight b + 1

/-- Retaining a statement's control also retains its existing termination weight. -/
theorem RawStmt.control_weight (s : RawStmt) : s.control.weight = CalleeKernel.stmtWeight s := by
  cases s <;> rfl

/-- Successful hoisting keeps the block-bearing constructor and all child
statements, provided assignment hoisting returns a statement without child blocks. -/
theorem hoistStmtWith_control [FreshNames] {C : Contract} (rc : ElabRec C)
    (ha : ∀ l r sc st m out st' m',
      (((rc.hoistAssign l r).run sc).run st).run m = .ok ((out, st'), m') →
        out.2.control = .leaf)
    (s : RawStmt) (sc : ElabScope) (st : ECtx × Nat) (m : CallMemo)
    (out : SProg C × RawStmt) (st' : ECtx × Nat) (m' : CallMemo)
    (h : (((hoistStmtWith C rc s).run sc).run st).run m = .ok ((out, st'), m')) :
    out.2.control = s.control :=
  ElabControlProof.hoist_control C rc ha s sc st m out st' m' h

/-- No element of a well-founded relation lies on a cycle of three. -/
theorem rel_cycle3 {α : Type} [WellFoundedRelation α] {a b c : α}
    (h1 : WellFoundedRelation.rel a b) (h2 : WellFoundedRelation.rel b c)
    (h3 : WellFoundedRelation.rel c a) : False :=
  WellFounded.induction (C := fun a => ∀ b c, WellFoundedRelation.rel a b →
      WellFoundedRelation.rel b c → WellFoundedRelation.rel c a → False)
    WellFoundedRelation.wf a (fun _ ih b c h1 h2 h3 => ih c h3 _ b h3 h1 h2) b c h1 h2 h3

/-- What a run of each of the five fields may be asked to meet: the shapes of
`ElabKernelInduction`'s predicates. -/
structure ElabPreds (C : Contract) where
  hoist : RawExpr → ElabScope → ECtx × Nat → SProg C × RawExpr → ECtx × Nat → Prop
  hoistStmt : RawStmt → ElabScope → ECtx × Nat → SProg C × RawStmt → ECtx × Nat → Prop
  elabStmtP : RawStmt → ElabScope → ECtx × Nat → SProg C → ECtx × Nat → Prop
  elabStmt1 : RawStmt → ElabScope → ECtx × Nat → SProg C → ECtx × Nat → Prop
  elabStmtsP : List RawStmt → ElabScope → ECtx × Nat → SProg C → ECtx × Nat → Prop

/-- The trivial guard. -/
def ElabPreds.top (C : Contract) : ElabPreds C :=
  ⟨fun _ _ _ _ _ => True, fun _ _ _ _ _ => True, fun _ _ _ _ _ => True,
    fun _ _ _ _ _ => True, fun _ _ _ _ _ => True⟩

/-- Every successful run of `f x` from the scope `sc` meets `Q`. -/
def RunsMeet {β γ : Type} (Q : β → ElabScope → ECtx × Nat → γ → ECtx × Nat → Prop)
    (f : β → ElabM γ) (x : β) (sc : ElabScope) : Prop :=
  ∀ st b st' m m', (((f x).run sc).run st).run m = .ok ((b, st'), m') → Q x sc st b st'

/-- One measure per recursive field: of the input and the scope. -/
structure ElabMeasure (α : Type) where
  hoist : RawExpr → ElabScope → α
  hoistStmt : RawStmt → ElabScope → α
  elabStmtP : RawStmt → ElabScope → α
  elabStmt1 : RawStmt → ElabScope → α
  elabStmtsP : List RawStmt → ElabScope → α

namespace ElabMeasure

variable {α : Type} [WellFoundedRelation α]

open Classical in
/-- `f` below `a`: a call whose measure is not below `a` fails. -/
noncomputable def cutF {β γ : Type} (m : β → ElabScope → α) (a : α) (f : β → ElabM γ) :
    β → ElabM γ :=
  fun x sc => if WellFoundedRelation.rel (m x sc) a then (f x).run sc else (throw "" : ElabM γ).run sc

open Classical in
theorem cutF_run {β γ : Type} (m : β → ElabScope → α) (a : α) (f : β → ElabM γ) (x : β)
    (sc : ElabScope) :
    (cutF m a f x).run sc =
      if WellFoundedRelation.rel (m x sc) a then (f x).run sc else (throw "" : ElabM γ).run sc :=
  rfl

/-- The cut meets what `f` meets below `a`, everywhere. -/
theorem cutF_meets {β γ : Type} {m : β → ElabScope → α} {a : α} {f : β → ElabM γ}
    {Q : β → ElabScope → ECtx × Nat → γ → ECtx × Nat → Prop}
    (h : ∀ x sc, WellFoundedRelation.rel (m x sc) a → RunsMeet Q f x sc) :
    ∀ x sc, RunsMeet Q (cutF m a f) x sc := by
  intro x sc st b st' m0 m1 hrun
  by_cases hlt : WellFoundedRelation.rel (m x sc) a
  · rw [cutF_run, if_pos hlt] at hrun
    exact h x sc hlt st b st' m0 m1 hrun
  · rw [cutF_run, if_neg hlt] at hrun
    cases hrun

/-- `r`'s five recursive fields cut below `a`; its other fields kept. -/
noncomputable def cut {C : Contract} (μ : ElabMeasure α) (a : α) (r : ElabRec C) : ElabRec C :=
  { r with
    hoist := cutF μ.hoist a r.hoist
    hoistStmt := cutF μ.hoistStmt a r.hoistStmt
    elabStmtP := cutF μ.elabStmtP a r.elabStmtP
    elabStmt1 := cutF μ.elabStmt1 a r.elabStmt1
    elabStmtsP := cutF μ.elabStmtsP a r.elabStmtsP }

/-- The runs of `r`'s five fields below `a` meet `J`. -/
def MeetsBelow {C : Contract} (μ : ElabMeasure α) (J : ElabPreds C) (a : α) (r : ElabRec C) :
    Prop :=
  (∀ x sc, WellFoundedRelation.rel (μ.hoist x sc) a → RunsMeet J.hoist r.hoist x sc) ∧
  (∀ x sc, WellFoundedRelation.rel (μ.hoistStmt x sc) a → RunsMeet J.hoistStmt r.hoistStmt x sc) ∧
  (∀ x sc, WellFoundedRelation.rel (μ.elabStmtP x sc) a → RunsMeet J.elabStmtP r.elabStmtP x sc) ∧
  (∀ x sc, WellFoundedRelation.rel (μ.elabStmt1 x sc) a → RunsMeet J.elabStmt1 r.elabStmt1 x sc) ∧
  (∀ x sc, WellFoundedRelation.rel (μ.elabStmtsP x sc) a → RunsMeet J.elabStmtsP r.elabStmtsP x sc)

/-- **The arm's decrease**: at `x`, `arm` gives over `r` what it gives over
`r` cut below the measure of `x`, for every `r` whose runs below meet `J`. -/
def Stable {C : Contract} {β γ : Type} (μ : ElabMeasure α) (J : ElabPreds C)
    (m : β → ElabScope → α) (arm : ElabRec C → β → ElabM γ) : Prop :=
  ∀ (r : ElabRec C) x sc, MeetsBelow μ J (m x sc) r →
    (arm (cut μ (m x sc) r) x).run sc = (arm r x).run sc

/-- The block's `elabStmtsP`, over the record (`Goals.elabStmtsStep`). -/
def stmtsArm {C : Contract} (rc : ElabRec C) : List RawStmt → ElabM (SProg C)
  | [] => pure []
  | s :: ss => do
    let P ← rc.elabStmtP s
    let Q ← rc.elabStmtsP ss
    pure (P ++ Q)

/-- **The measure decreases on `elabStmtsP`'s arm**: it calls `elabStmtP` at
the head and `elabStmtsP` at the tail, both at its own scope. -/
theorem stmtsArm_stable {C : Contract} (μ : ElabMeasure α) (J : ElabPreds C)
    (hhead : ∀ s ss sc, WellFoundedRelation.rel (μ.elabStmtP s sc) (μ.elabStmtsP (s :: ss) sc))
    (htail : ∀ s ss sc, WellFoundedRelation.rel (μ.elabStmtsP ss sc) (μ.elabStmtsP (s :: ss) sc)) :
    Stable μ J μ.elabStmtsP (stmtsArm (C := C)) := by
  intro r x sc _
  cases x with
  | nil => rfl
  | cons s ss =>
    have e1 : ((cut μ (μ.elabStmtsP (s :: ss) sc) r).elabStmtP s).run sc =
        (r.elabStmtP s).run sc := by
      exact (cutF_run ..).trans (if_pos (hhead s ss sc))
    have e2 : ((cut μ (μ.elabStmtsP (s :: ss) sc) r).elabStmtsP ss).run sc =
        (r.elabStmtsP ss).run sc := by
      exact (cutF_run ..).trans (if_pos (htail s ss sc))
    simp only [stmtsArm, ReaderT.run, bind, ReaderT.bind] at e1 e2 ⊢
    rw [e1]
    funext st m
    simp only [e2]

end ElabMeasure

end Solidity
