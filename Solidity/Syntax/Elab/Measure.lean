import Solidity.Syntax.Elab.Arms

/-!
# A termination measure for the elaborator knot

The vocabulary in which a well-founded totalization of the `mutual` knot of
`Syntax/Elab/Stmt.lean` states its decrease, over the five recursive fields
that the induction clause of `Solidity.Goals.elabKernelTotal` (`ElabKernelInduction`)
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

`StableFor` specializes the obligation to one record, so proofs can use
invariants of its actual helper fields. `ElabScope.callRank` handles scope
changes on body entry; local expression and statement transformations still
need further measure components.

`ElabLoopMeasure` supplies a loop-lowering component: a successful singleton
lowering removes the source-loop root without increasing nested source loops.

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

private theorem reachableBy_missing (callees : FunDecl → List String)
    (funs : List (Name × FunDecl)) (f : String) (h : lookupBy f funs = none) :
    reachableBy callees funs f = [] := by
  simp only [reachableBy, h, Option.map_none, Option.getD_none]
  simp only [forIn, forIn', Std.Range.forIn']
  -- Unfold the private range loop once. Its general list-range theorem
  -- brings Classical.choice through an arithmetic helper; this early exit
  -- needs only the defining equation. Find the helper from the public body
  -- rather than relying on its generated private-name index.
  run_tac
    let info ← Lean.getConstInfo ``Std.Range.forIn'
    let some body := info.value? | throwError "range body unavailable"
    let some loop := body.find? (fun e => match e with
      | .const (.str _ "loop") _ => true
      | _ => false)
      | throwError "range loop unavailable"
    Lean.Elab.Tactic.evalTactic (← `(tactic| unfold $(Lean.mkIdent loop.constName!)))
  simp only [Nat.zero_lt_succ, ↓reduceDIte, List.filter_nil, List.eraseDups_nil,
    List.isEmpty_nil, ↓reduceIte, pure_bind, Id.run_pure]
private theorem recursive_has_decl (C : Contract) (f : String) (hr : isRecursiveC C f = true) :
    ∃ d, (f, d) ∈ C.funs := by
  cases h : lookupBy f C.funs with
  | none =>
    have hz : reachableC C f = [] := reachableBy_missing _ _ _ h
    simp only [isRecursiveC, hz, List.contains_nil, Bool.false_eq_true] at hr
  | some d => exact ⟨d, lookupBy_eq_some_mem h⟩
/-- Contract functions not yet represented by an active recursive frame. -/
def ElabScope.unframedCount (C : Contract) (sc : ElabScope) : Nat :=
  (C.funs.filter fun p => !(sc.recs.any (·.name == p.1))).length

private theorem filter_lt_of_rejected {α : Type} (p : α → Bool) (a : α)
    (xs : List α) (hm : a ∈ xs) (hf : p a = false) :
    (xs.filter p).length < xs.length := by
  induction xs with
  | nil => cases hm
  | cons b xs ih =>
    simp only [List.mem_cons] at hm
    rcases hm with h | h
    · subst b
      simpa only [List.filter_cons, hf, Bool.false_eq_true, ↓reduceIte, List.length_cons]
        using Nat.lt_succ_of_le (List.length_filter_le p xs)
    · have ht := ih h
      cases hb : p b <;>
        simp only [List.filter_cons, hb, Bool.false_eq_true, ↓reduceIte, List.length_cons] <;> omega

/-- Opening a previously absent recursive frame strictly decreases the count,
even if the recursive call widens the list of callable functions. -/
private theorem ElabScope.unframedCount_push_of_mem (C : Contract) (sc : ElabScope) (rf : RecFrame)
    (d : FunDecl) (hm : (rf.name, d) ∈ C.funs)
    (hn : sc.recs.any (·.name == rf.name) = false) :
    ({ sc with recs := rf :: sc.recs } : ElabScope).unframedCount C < sc.unframedCount C := by
  unfold ElabScope.unframedCount
  have he : C.funs.filter (fun p => !((rf :: sc.recs).any (·.name == p.1))) =
      (C.funs.filter fun p => !(sc.recs.any (·.name == p.1))).filter
        (fun p => !(rf.name == p.1)) := by
    simp only [List.any_cons, Bool.not_or, List.filter_filter]
  rw [he]
  apply filter_lt_of_rejected _ (rf.name, d)

  · exact List.mem_filter.mpr ⟨hm, by simp only [hn, Bool.not_false]⟩
  · have hb : (rf.name == rf.name) = true := beq_iff_eq.mpr rfl
    rw [hb]
    rfl

/-- A recursive body gains a new active frame, removing a contract function
from the finite count of possible recursive-body expansions. -/
theorem ElabScope.unframedCount_push (C : Contract) (sc : ElabScope) (rf : RecFrame)
    (hr : isRecursiveC C rf.name = true) (hn : sc.recs.any (·.name == rf.name) = false) :
    ({ sc with recs := rf :: sc.recs } : ElabScope).unframedCount C < sc.unframedCount C := by
  obtain ⟨d, hm⟩ := recursive_has_decl C rf.name hr
  exact ElabScope.unframedCount_push_of_mem C sc rf d hm hn

/-- A rank for scope changes during body expansion: deployment permission,
unopened recursive functions, then the callable prefix length. Expression and
statement transformations need further measure components. `ctor` covers
public constructor-call entry even when the supplied scope has `top = false`. -/
def ElabScope.callRank (C : Contract) (sc : ElabScope) (ctor : Bool := false) : Nat × Nat × Nat :=
  (if sc.top || ctor then 1 else 0, sc.unframedCount C, sc.funs.length)

/-- Entering a body that cannot deploy decreases the first component. -/
theorem ElabScope.callRank_top (C : Contract) (sc sc' : ElabScope)
    (ht : sc.top = true) (hf : sc'.top = false) :
    WellFoundedRelation.rel (sc'.callRank C) (sc.callRank C) := by
  unfold ElabScope.callRank
  apply Prod.Lex.left
  simp only [ht, hf]
  exact Nat.zero_lt_one

/-- Explicit constructor entry decreases when its body disables deployment,
including a public call entered with `scope.top = false`. -/
theorem ElabScope.callRank_ctor (C : Contract) (sc sc' : ElabScope)
    (hf : sc'.top = false) :
    WellFoundedRelation.rel (sc'.callRank C) (sc.callRank C true) := by
  unfold ElabScope.callRank
  apply Prod.Lex.left
  simp only [hf, Bool.or_true]
  exact Nat.zero_lt_one

/-- A recursive body may widen its callable scope, but its fresh frame
strictly reduces the second component. -/
theorem ElabScope.callRank_push (C : Contract) (sc : ElabScope) (rf : RecFrame)
    (funs : List (Name × FunDecl)) (hr : isRecursiveC C rf.name = true)
    (hn : sc.recs.any (·.name == rf.name) = false) :
    WellFoundedRelation.rel
      (({ sc with top := false, funs := funs, recs := rf :: sc.recs } : ElabScope).callRank C)
      (sc.callRank C) := by
  cases ht : sc.top with
  | true => exact ElabScope.callRank_top C _ _ ht rfl
  | false =>
    unfold ElabScope.callRank
    simp only [ht]
    exact Prod.Lex.right 0 (Prod.Lex.left _ _ (ElabScope.unframedCount_push C sc rf hr hn))

/-- Ordinary inlining restricts calls to a strict prefix. -/
theorem ElabScope.callRank_prefix (C : Contract) (sc : ElabScope) (i : Nat)
    (hi : i < sc.funs.length) :
    WellFoundedRelation.rel
      (({ sc with top := false, funs := sc.funs.take i } : ElabScope).callRank C)
      (sc.callRank C) := by
  cases ht : sc.top with
  | true => exact ElabScope.callRank_top C _ _ ht rfl
  | false =>
    unfold ElabScope.callRank
    simp only [ht]
    exact Prod.Lex.right 0 (Prod.Lex.right (sc.unframedCount C)
      (Nat.lt_of_le_of_lt (List.length_take_le i sc.funs) hi))


/-- The actual declaration lookup yields the strict prefix needed by ordinary inlining. -/
theorem ElabScope.callRank_found (C : Contract) (sc : ElabScope) (f : String) (i : Nat)
    (h : sc.funs.findIdx? (·.1 == f) = some i) :
    WellFoundedRelation.rel
      (({sc with top := false, funs := sc.funs.take i} : ElabScope).callRank C)
      (sc.callRank C) := by
  apply ElabScope.callRank_prefix
  exact (List.findIdx?_eq_some_iff_getElem.mp h).1

/-- The actual missing-frame test supplies the strict recursive-frame decrease. -/
theorem ElabScope.callRank_freshFrame (C : Contract) (sc : ElabScope) (rf : RecFrame)
    (funs : List (Name × FunDecl)) (hr : isRecursiveC C rf.name = true)
    (h : sc.recs.find? (·.name == rf.name) = none) :
    WellFoundedRelation.rel
      (({sc with top := false, funs := funs, recs := rf :: sc.recs} : ElabScope).callRank C)
      (sc.callRank C) := by
  apply ElabScope.callRank_push C sc rf funs hr
  exact List.any_eq_false.mpr (List.find?_eq_none.mp h)

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

/-- The decrease obligation for one specified record. Its helper fields may
satisfy invariants that do not hold for arbitrary `ElabRec` values. -/
def StableFor {C : Contract} {β γ : Type} (μ : ElabMeasure α) (J : ElabPreds C)
    (m : β → ElabScope → α) (arm : ElabRec C → β → ElabM γ) (r : ElabRec C) : Prop :=
  ∀ x sc, MeetsBelow μ J (m x sc) r →
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

namespace ElabLoopMeasure

/-! Source `while`, `for`, and `do` loops remaining before loop lowering.
Canonical `loop` nodes contribute no root count. All child lists are counted,
including a `for` loop's initializer and update, which lowering carries through. -/
mutual
  def stmtCount : RawStmt → Nat
    | .block b | .unchecked b | .checked _ b | .loop _ _ b => listCount b
    | .ite _ t e => listCount t + listCount e
    | .tryCall _ _ _ _ ok err _ pnc other =>
        listCount ok + listCount err + listCount pnc + listCount other
    | .whileLoop _ _ b | .doWhile _ b _ => listCount b + 1
    | .forLoop _ i _ u b => listCount i + listCount u + listCount b + 1
    | _ => 0
  def listCount : List RawStmt → Nat
    | [] => 0
    | s :: ss => stmtCount s + listCount ss
end

private theorem count_nil : listCount [] = 0 := rfl
private theorem count_cons (s : RawStmt) (ss : List RawStmt) :
    listCount (s :: ss) = stmtCount s + listCount ss := rfl

theorem listCount_append (xs ys : List RawStmt) :
    listCount (xs ++ ys) = listCount xs + listCount ys := by
  induction xs with
  | nil => simp only [List.nil_append, listCount, Nat.zero_add]
  | cons s ss ih => simp only [List.cons_append, listCount, ih, Nat.add_assoc]

def controlCount : StmtControl → Nat
  | .leaf => 0
  | .block b | .unchecked b | .checked b | .loop b => listCount b
  | .ite t e => listCount t + listCount e
  | .tryCall ok err pnc other => listCount ok + listCount err + listCount pnc + listCount other
  | .whileLoop b | .doWhile b => listCount b + 1
  | .forLoop i u b => listCount i + listCount u + listCount b + 1

theorem controlCount_eq (s : RawStmt) : controlCount s.control = stmtCount s := by
  cases s <;> rfl

theorem mapExprsM_count {m : Type → Type} [Monad m] [LawfulMonad m]
    (f : RawExpr → m RawExpr) (s : RawStmt) :
    stmtCount <$> s.mapExprsM f = (fun _ => stmtCount s) <$> s.mapExprsM f := by
  have h := congrArg (fun x => controlCount <$> x) (RawStmt.mapExprsM_control f s)
  simpa only [Functor.map_map, Function.comp_def, controlCount_eq] using h

private def Obs {α : Type} (x : LowerM α) (Q : α → Prop) : Prop :=
  ∀ fl sc st m a fl' st' m', x fl sc st m = .ok (((a, fl'), st'), m') → Q a
private theorem obs_pure {α : Type} {a : α} {Q : α → Prop} (h : Q a) :
    Obs (pure a) Q := by
  intro fl sc st m b fl' st' m' he
  cases he
  exact h
private theorem obs_bind {α β : Type} {x : LowerM α} {f : α → LowerM β}
    {P : α → Prop} {Q : β → Prop} (hx : Obs x P)
    (hf : ∀ a, P a → Obs (f a) Q) : Obs (x >>= f) Q := by
  intro fl sc st m b fl' st' m' h
  change (do let (((a, fl₁), s), n) ← x fl sc st m; f a fl₁ sc s n) =
    .ok (((b, fl'), st'), m') at h
  cases he : x fl sc st m with
  | error err => simp only [he, bind, Except.bind] at h; cases h
  | ok v =>
    rcases v with ⟨⟨⟨a, fl₁⟩, s⟩, n⟩
    simp only [he, bind, Except.bind] at h
    exact hf a (hx fl sc st m a fl₁ s n he) fl₁ sc s n b fl' st' m' h
private theorem obs_any {α β : Type} {x : LowerM α} {f : α → LowerM β}
    {Q : β → Prop} (hf : ∀ a, Obs (f a) Q) : Obs (x >>= f) Q :=
  obs_bind (P := fun _ => True) (fun _ _ _ _ _ _ _ _ _ => trivial) (fun a _ => hf a)
private theorem obs_throw {α : Type} {err : String} {Q : α → Prop} :
    Obs (throw err : LowerM α) Q := by
  intro fl sc st m a fl' st' m' h
  cases h
private theorem obs_mono {α : Type} {x : LowerM α} {P Q : α → Prop}
    (hx : Obs x P) (h : ∀ a, P a → Q a) : Obs x Q :=
  fun fl sc st m a fl' st' m' he => h a (hx fl sc st m a fl' st' m' he)
local macro "count_tail " h:ident : tactic =>
  `(tactic| repeat' first
    | with_reducible apply $h
    | (with_reducible refine obs_mono (by apply $h) ?_
       intro result bound
       simp only [listCount_append, count_cons, count_nil, stmtCount, RawStmt.declBool, RawStmt.setBool] at bound ⊢
       omega)
    | (with_reducible apply obs_pure
       simp only [listCount_append, count_cons, count_nil, stmtCount, RawStmt.declBool, RawStmt.setBool]
       omega)
    | (with_reducible apply obs_any; intro x)
    | split
    | extract_lets)
private theorem finish_count_bound [FreshNames] (spec : RawLoopSpec) (c : RawExpr)
    (init upd : List RawStmt) (isDo : Bool) (bodyCall : LowerM (List RawStmt × List Abrupt))
    (n : Nat) (hb : Obs bodyCall (fun out => listCount out.1 ≤ n)) :
    Obs (LowerKernel.loopFinish spec c init upd isDo bodyCall)
      (fun out => stmtCount out.1 ≤ listCount init + listCount upd + n) := by
  unfold LowerKernel.loopFinish
  with_reducible apply obs_any
  intro outer
  with_reducible apply obs_any
  intro unused
  with_reducible apply obs_bind hb
  intro out hbody
  split
  simp only at hbody
  -- Keep the generated continuations shared: unfolding all branches at once
  -- duplicates the later proof obligations and exceeds the checking budget.
  extract_lets exits before iter cond heads returns ab' j2 j1 j0
  -- After the body and update are added, only zero-count flag statements and
  -- canonical control nodes are introduced around the two statement lists.
  have h2 : ∀ a b c d y, Obs (j2 a b c d y)
      (fun r => stmtCount r.1 ≤ listCount a + listCount d) := by
    intro a b c d y
    simp -zeta only [j2]
    extract_lets j3
    have h3 : ∀ a b c y, Obs (j3 a b c y)
        (fun r => stmtCount r.1 ≤ listCount a + listCount d) := by
      intro a b c y
      simp -zeta only [j3]
      with_reducible apply obs_any
      intro fl
      extract_lets retX j5 j4
      have h5 : ∀ a b y, Obs (j5 a b y)
          (fun r => stmtCount r.1 ≤ listCount a + listCount d) := by
        intro a b y
        simp -zeta only [j5]
        extract_lets spec' w j7 j6
        have hw : stmtCount w = listCount d := rfl
        have h7 : ∀ a y, Obs (j7 a y)
            (fun r => stmtCount r.1 ≤ listCount a + listCount d) := by
          intro a y
          simp -zeta only [j7]
          with_reducible apply obs_any
          intro unused
          extract_lets j9 j8
          have h9 : ∀ y, Obs (j9 y)
              (fun r => stmtCount r.1 ≤ listCount a + listCount d) := by
            intro y
            with_reducible apply obs_pure
            simp only [stmtCount, listCount_append, count_cons, count_nil, hw]
            omega
          clear_value j9
          have h8 : ∀ y, Obs (j8 y)
              (fun r => stmtCount r.1 ≤ listCount a + listCount d) := by
            intro y
            simp -zeta only [j8]
            count_tail h9
          clear_value j8
          count_tail h8
        clear_value j7
        have h6 : ∀ a y, Obs (j6 a y)
            (fun r => stmtCount r.1 ≤ listCount a + listCount d) := by
          intro a y
          simp -zeta only [j6]
          count_tail h7
        clear_value j6
        count_tail h6
      clear_value j5
      have h4 : ∀ a b y, Obs (j4 a b y)
          (fun r => stmtCount r.1 ≤ listCount a + listCount d) := by
        intro a b y
        simp -zeta only [j4]
        count_tail h5
      clear_value j4
      count_tail h4
    clear_value j3
    count_tail h3
  clear_value j2
  -- This continuation adds the lowered body and either the update directly
  -- or an `if` containing it; both forms have the same source-loop count.
  have h1 : ∀ a b c d y, Obs (j1 a b c d y)
      (fun r => stmtCount r.1 ≤ listCount a + listCount d + listCount upd + n) := by
    intro a b c d y
    simp -zeta only [j1]
    count_tail h2
  clear_value j1
  -- The continue flag, and then the do-loop flag at entry, add zero count.
  have h0 : ∀ a b c d y, Obs (j0 a b c d y)
      (fun r => stmtCount r.1 ≤ listCount a + listCount d + listCount upd + n) := by
    intro a b c d y
    simp -zeta only [j0]
    count_tail h1
  clear_value j0
  simp only [before, iter]
  count_tail h0
private theorem obs_throw_bind {α β : Type} {err : String} {f : α → LowerM β}
    {Q : β → Prop} : Obs ((throw err : LowerM α) >>= f) Q := by
  intro fl sc st m a fl' st' m' h
  cases h
private theorem obs_outside {α : Type} {x : LowerM α} {Q : α → Prop}
    (h : Obs x Q) : Obs (LowerM.outside x) Q := by
  unfold LowerM.outside
  with_reducible apply obs_any
  intro fl
  with_reducible apply obs_any
  intro unused
  with_reducible apply obs_bind h
  intro a ha
  with_reducible apply obs_any
  intro unused
  exact obs_pure ha
private theorem obs_lift {α : Type} {x : Except String α} {Q : α → Prop}
    (hx : ∀ a, x = .ok a → Q a) : Obs (ElabM.lift x) Q := by
  intro fl sc st m a fl' st' m' h
  cases he : x with
  | error e => simp only [he] at h; cases h
  | ok v =>
    simp only [he] at h
    cases h
    exact hx _ he
private theorem return_count (rs : List String) (e : RawExpr) :
    Obs (ElabM.lift (lowerReturn rs e)) (fun out => listCount out = 0) := by
  apply obs_lift
  intro out h
  have hm (xs : List (String × RawExpr)) :
      listCount (xs.map fun (n, e) => RawStmt.assign (.name n) e) = 0 := by
    induction xs with
    | nil => rfl
    | cons a as ih => simp only [List.map_cons, count_cons, stmtCount, ih, Nat.add_zero]
  unfold lowerReturn at h
  repeat' first
    | split at h
    | (cases h <;> simp only [count_cons, count_nil, stmtCount, Nat.zero_add, hm])

def rootCount : RawStmt → Nat
  | .whileLoop .. | .doWhile .. | .forLoop .. => 1
  | _ => 0
private theorem parts_count (s : RawStmt) :
    listCount (LowerKernel.loopParts s).2.2.1 +
      listCount (LowerKernel.loopParts s).2.2.2.1 +
      listCount (LowerKernel.loopBody s) + rootCount s ≤ stmtCount s := by
  cases s <;> simp only [LowerKernel.loopParts, LowerKernel.loopBody, rootCount, stmtCount, count_nil] <;> omega
private theorem rewrite_count (s : RawStmt) (h : LowerKernel.loopGuard s = true) :
    stmtCount (LowerKernel.loopRewrite s) = stmtCount s ∧
      rootCount (LowerKernel.loopRewrite s) = rootCount s := by
  cases s <;> simp only [LowerKernel.loopGuard, LowerKernel.loopParts, Bool.false_and, Bool.false_eq_true] at h
  all_goals try contradiction
  simp only [LowerKernel.loopRewrite, LowerKernel.loopParts, stmtCount, count_cons, count_nil, rootCount,
    Nat.zero_add, Nat.add_zero, and_self]
private theorem bound_key [FreshNames] (n : Nat) :
    (∀ rs ss, LowerKernel.listMeasure ss = n →
      Obs (lowerList rs ss) (fun out => listCount out.1 ≤ listCount ss)) ∧
    (∀ rs s, LowerKernel.stmtMeasure s = n →
      Obs (lowerStmt rs s) (fun out => stmtCount out.1 + rootCount s ≤ stmtCount s)) ∧
    (∀ rs s, LowerKernel.loopMeasure s = n →
      Obs (lowerLoop rs s) (fun out => stmtCount out.1 + rootCount s ≤ stmtCount s)) := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    refine ⟨?_, ?_, ?_⟩
    · intro rs ss hn
      subst n
      rw [LowerKernel.fixed.1]
      cases ss with
      | nil => exact obs_pure (Nat.le_refl _)
      | cons s ss =>
        have hs := (ih _ (LowerKernel.list_head_lt s ss)).2.1 rs s rfl
        have ht := (ih _ (LowerKernel.list_tail_lt s ss)).1 rs ss rfl
        simp only [LowerKernel.listStep]
        repeat' (first
          | (with_reducible apply obs_pure
             simp only [stmtCount, count_cons, count_nil] at *
             omega)
          | (with_reducible apply obs_bind hs; intro out h)
          | (with_reducible apply obs_bind ht; intro out h)
          | (with_reducible apply obs_any; intro x)
          | split)
    · intro rs s hn
      subst n
      have hloop := (ih _ (LowerKernel.loop_phase_lt s)).2.2 rs s rfl
      have recL (b : List RawStmt) (h : LowerKernel.listMeasure b < LowerKernel.stmtMeasure s) :
          Obs (lowerList rs b) (fun out => listCount out.1 ≤ listCount b) :=
        (ih _ h).1 rs b rfl
      rw [LowerKernel.fixed.2.1]
      cases s <;> simp only [LowerKernel.stmtStep, LowerKernel.stmtOutside, LowerKernel.stmtInside,
        bind_assoc, pure_bind, bind_pure]
      all_goals repeat' (first
        | contradiction
        | with_reducible exact hloop
        | (with_reducible apply obs_pure
           simp only [stmtCount, rootCount, count_cons, count_nil, listCount_append, RawStmt.setBool] at *
           omega)
        | with_reducible exact obs_throw
        | with_reducible exact obs_throw_bind
        | (with_reducible apply obs_bind (recL _ (by
             simp only [LowerKernel.listMeasure, LowerKernel.stmtMeasure, LowerKernel.stmtWeight]
             omega))
           intro out h)
        | (with_reducible apply obs_bind (return_count _ _); intro out h)
        | with_reducible apply obs_outside
        | (with_reducible apply obs_any; intro x)
        | split)
    · intro rs s hn
      subst n
      have hb := (ih _ (LowerKernel.loop_body_lt s)).1 rs (LowerKernel.loopBody s) rfl
      have hp (h : LowerKernel.loopGuard s = true) :=
        (ih _ (LowerKernel.loop_rewrite_lt s h)).2.2 rs (LowerKernel.loopRewrite s) rfl
      have hparts := parts_count s
      rw [LowerKernel.fixed.2.2, ← LowerKernel.factoredStep_eq]
      unfold LowerKernel.factoredStep
      unfold LowerKernel.loopBody at hb hparts
      generalize he : LowerKernel.loopParts s = parts at *
      rcases parts with ⟨a, c, i, u, b, isDo⟩
      simp only at hb hparts ⊢
      split
      · rename_i hg
        have hr := rewrite_count s hg
        simpa only [hr.1, hr.2, bind_pure] using hp hg
      · simp only [pure_bind]
        with_reducible apply obs_mono (finish_count_bound a c i u isDo _ _ hb)
        intro out h
        omega

private theorem single_count [FreshNames] (rs : Option (List String)) (s : RawStmt) :
    Obs (lowerList rs [s]) (fun out => listCount out.1 + rootCount s ≤ stmtCount s) := by
  have hs := (bound_key (LowerKernel.stmtMeasure s)).2.1 rs s rfl
  rw [LowerKernel.fixed.1]
  simp only [LowerKernel.listStep, lowerList.eq_def, pure_bind]
  repeat' (first
    | (with_reducible apply obs_pure
       simp only [count_cons, count_nil, stmtCount] at *
       omega)
    | (with_reducible apply obs_bind hs; intro out h)
    | (with_reducible apply obs_any; intro x)
    | split)

/-- The singleton boundary used when the elaborator lowers one source loop. -/
theorem lowerLoops_single_count [FreshNames] (rs : Option (List String)) (s : RawStmt)
    (sc : ElabScope) (st st' : ECtx × Nat) (m m' : CallMemo) (out : List RawStmt)
    (h : (((lowerLoops rs [s]).run sc).run st).run m = .ok ((out, st'), m')) :
    listCount out + rootCount s ≤ stmtCount s := by
  cases he : lowerList rs [s] {} sc st m with
  | error err =>
    simp only [lowerLoops, StateT.run', Functor.map, StateT.map, ReaderT.run,
      StateT.run, bind, ReaderT.bind, StateT.bind, he,
      Except.bind] at h
    cases h
  | ok r =>
    rcases r with ⟨⟨⟨⟨program, abrupt⟩, fl⟩, st₁⟩, m₁⟩
    simp only [lowerLoops, StateT.run', Functor.map, StateT.map, ReaderT.run,
      StateT.run, bind, ReaderT.bind, StateT.bind, pure, ReaderT.pure, StateT.pure, he,
      Except.bind] at h
    cases h
    exact single_count rs s {} sc st m (program, abrupt) fl st₁ m₁ he

end ElabLoopMeasure

namespace UncheckMeasureProof
private def Obs {α : Type} (x : Except String α) (Q : α → Prop) : Prop :=
  ∀ a, x = .ok a → Q a
private theorem obs_pure {α : Type} {a : α} {Q : α → Prop} (h : Q a) :
    Obs (pure a) Q := by
  intro b he
  cases he
  exact h
private theorem obs_bind {α β : Type} {x : Except String α} {f : α → Except String β}
    {P : α → Prop} {Q : β → Prop} (hx : Obs x P)
    (hf : ∀ a, P a → Obs (f a) Q) : Obs (x >>= f) Q := by
  intro b h
  cases he : x with
  | error err => simp only [he, bind, Except.bind] at h; cases h
  | ok a =>
    simp only [he, bind, Except.bind] at h
    exact hf a (hx a he) b h
private theorem obs_any {α β : Type} {x : Except String α} {f : α → Except String β}
    {Q : β → Prop} (hf : ∀ a, Obs (f a) Q) : Obs (x >>= f) Q :=
  obs_bind (P := fun _ => True) (fun _ _ => trivial) (fun a _ => hf a)
private theorem obs_throw {α : Type} {err : String} {Q : α → Prop} :
    Obs (throw err : Except String α) Q := by
  intro a h
  cases h
private theorem obs_throw_bind {α β : Type} {err : String}
    {f : α → Except String β} {Q : β → Prop} :
    Obs ((throw err : Except String α) >>= f) Q := by
  intro a h
  cases h
private theorem obs_map (f : RawExpr → Except String RawExpr) (s : RawStmt) :
    Obs (s.mapExprsM f) (fun out =>
      CalleeKernel.stmtWeight out = CalleeKernel.stmtWeight s ∧
      ElabLoopMeasure.stmtCount out = ElabLoopMeasure.stmtCount s) := by
  intro out h
  constructor
  · have he := CalleeKernel.mapExprsM_weight f s
    rw [h] at he
    exact Except.ok.inj he
  · have he := ElabLoopMeasure.mapExprsM_count f s
    rw [h] at he
    exact Except.ok.inj he
private theorem weight_cons (s : RawStmt) (ss : List RawStmt) :
    CalleeKernel.listWeight (s :: ss) = CalleeKernel.stmtWeight s + CalleeKernel.listWeight ss := rfl

/-- One traversal preserves both measures used by unchecked elaboration. -/
private theorem preserves_key (n : Nat) : ∀ ss, CalleeKernel.listWeight ss = n →
    Obs (uncheckStmts ss) (fun out =>
      CalleeKernel.listWeight out = CalleeKernel.listWeight ss ∧
      ElabLoopMeasure.listCount out = ElabLoopMeasure.listCount ss) := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro ss hn
    subst n
    cases ss with
    | nil =>
      rw [uncheckStmts.eq_def]
      exact obs_pure ⟨rfl, rfl⟩
    | cons s ss =>
      have recCall (b : List RawStmt)
          (hb : CalleeKernel.listWeight b < CalleeKernel.listWeight (s :: ss)) :
          Obs (uncheckStmts b)
            (fun out => CalleeKernel.listWeight out = CalleeKernel.listWeight b ∧
              ElabLoopMeasure.listCount out = ElabLoopMeasure.listCount b) :=
        ih _ hb b rfl
      rw [uncheckStmts.eq_def]
      cases s
      case' checked o b => cases o
      all_goals simp only [pure_bind]
      all_goals repeat (first
        | (with_reducible apply obs_pure
           constructor <;>
             simp only [weight_cons, CalleeKernel.stmtWeight,
               ElabLoopMeasure.listCount, ElabLoopMeasure.stmtCount] at * <;> omega)
        | with_reducible exact obs_throw
        | with_reducible exact obs_throw_bind
        | (with_reducible apply obs_bind (recCall _ (by
             simp only [weight_cons, CalleeKernel.stmtWeight]
             omega))
           intro outTail hTail)
        | (with_reducible apply obs_bind (obs_map _ _); intro out h)
        | (with_reducible apply obs_any; intro x)
        | split)
end UncheckMeasureProof

/-- Wrapping arithmetic preserves the control weight of every successful output. -/
theorem uncheckStmts_weight (ss out : List RawStmt)
    (h : uncheckStmts ss = .ok out) :
    CalleeKernel.listWeight out = CalleeKernel.listWeight ss :=
  (UncheckMeasureProof.preserves_key (CalleeKernel.listWeight ss) ss rfl out h).1

/-- Wrapping arithmetic preserves the source-loop count of every successful output. -/
theorem uncheckStmts_loopCount (ss out : List RawStmt)
    (h : uncheckStmts ss = .ok out) :
    ElabLoopMeasure.listCount out = ElabLoopMeasure.listCount ss :=
  (UncheckMeasureProof.preserves_key (CalleeKernel.listWeight ss) ss rfl out h).2

namespace ElabLoopMeasure

/-- Local statement descent before expression-generated statements are considered. -/
def stmtRank (s : RawStmt) : Nat × Nat := (stmtCount s, CalleeKernel.stmtWeight s)
def listRank (ss : List RawStmt) : Nat × Nat := (listCount ss, CalleeKernel.listWeight ss)

theorem lowerLoops_rank [FreshNames] (rs : Option (List String)) (s : RawStmt)
    (hs : rootCount s = 1) (sc : ElabScope) (st st' : ECtx × Nat)
    (m m' : CallMemo) (out : List RawStmt)
    (h : (((lowerLoops rs [s]).run sc).run st).run m = .ok ((out, st'), m')) :
    WellFoundedRelation.rel (listRank out) (stmtRank s) := by
  apply Prod.Lex.left
  change listCount out < stmtCount s
  have hc := lowerLoops_single_count rs s sc st st' m m' out h
  rw [hs] at hc
  omega

end ElabLoopMeasure

private theorem bytesArgs_shape (as : List RawExpr) (bs : List Nat)
    (h : as.mapM (fun | .num n => some n | _ => none) = some bs) :
    as = bs.map RawExpr.num := by
  induction as generalizing bs with
  | nil => cases h; rfl
  | cons a as ih =>
    cases a <;> simp only [List.mapM_cons, bind, Option.bind, pure] at h
    all_goals try contradiction
    rename_i n
    cases he : as.mapM (fun | .num n => some n | _ => none) with
    | none => simp only [he] at h; contradiction
    | some ns =>
      simp only [he, Option.some.injEq] at h
      cases h
      simp only [List.map_cons, ih ns he]

/-- Successful byte-literal recognition exposes only numeric arguments. -/
theorem bytesLit_shape (e : RawExpr) (bs : List Nat)
    (h : e.bytesLit? = some bs) : e = RawExpr.bytesLit bs := by
  cases e <;> simp only [RawExpr.bytesLit?] at h
  all_goals try contradiction
  rename_i f as
  split at h
  next hf =>
    have hf' : f = bytesLitName := beq_iff_eq.mp hf
    subst f
    rw [bytesArgs_shape as bs h]
    rfl
  next => contradiction


namespace ElabCaptureProof

open ElabControlProof

/-- An operand accepted without capture, or a captured local name. -/
def CaptureAtom (e : RawExpr) : Prop :=
  (e.isLit || e.bytesLit?.isSome || (e matches .bool _)) = true ∨
    ∃ x, e = .name x

/-- Captured atoms have only these literal or name forms. -/
theorem captureAtom_cases (e : RawExpr) (h : CaptureAtom e) :
    (∃ n, e = .num n) ∨ (∃ n, e = .unop .neg (.num n)) ∨
      (∃ b, e = .bool b) ∨ (∃ x, e = .name x) ∨ (∃ bs, e = .bytesLit bs) := by
  rcases h with h | ⟨x, hx⟩
  · simp only [Bool.or_eq_true] at h
    rcases h with (hl | hb) | hb
    · unfold RawExpr.isLit at hl
      split at hl
      next n => exact Or.inl ⟨n, rfl⟩
      next n => exact Or.inr (Or.inl ⟨n, rfl⟩)
      next => contradiction
    · cases he : e.bytesLit? with
      | none => simp only [he, Option.isSome_none, Bool.false_eq_true] at hb
      | some bs => exact Or.inr (Or.inr (Or.inr (Or.inr ⟨bs, bytesLit_shape e bs he⟩)))
    · cases e <;> simp only [Bool.false_eq_true] at hb
      rename_i b
      exact Or.inr (Or.inr (Or.inl ⟨b, rfl⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨x, hx⟩)))

variable (C : Contract) [FreshNames]

private theorem forceArg_obs (e : RawExpr) (p : PrimTy) :
    Obs (forceArg C e (some p)) (fun out => CaptureAtom out.2) := by
  simp only [forceArg]
  change Obs (if (e.isLit || e.bytesLit?.isSome || (e matches .bool _)) = true
    then _ else _) _
  by_cases he : (e.isLit || e.bytesLit?.isSome || (e matches .bool _)) = true
  · rw [if_pos he]
    exact obs_pure (Or.inl he)
  · rw [if_neg he]
    simp only [pure_bind]
    apply obs_any
    intro ⟨Γ, t⟩
    cases t <;> try (rename_i T _; cases T)
    all_goals
      repeat first
      | apply obs_pure; exact Or.inr ⟨_, rfl⟩
      | apply obs_any; intro a

theorem forceArg_captureAtom (e : RawExpr) (p : PrimTy)
    (sc : ElabScope) (st st' : ECtx × Nat) (m m') (out : SProg C × RawExpr)
    (h : (((forceArg C e (some p)).run sc).run st).run m = .ok ((out, st'), m')) :
    CaptureAtom out.2 := forceArg_obs C e p sc st m out st' m' h
private theorem eager_pair_obs (hoist : RawExpr → ElabM (SProg C × RawExpr))
    (a b : RawExpr) (p q : PrimTy) :
    Obs (eagerArgsWith C hoist [a, b] false [some p, some q])
      (fun out => ∃ x y, out.2 = [x, y] ∧ CaptureAtom x ∧ CaptureAtom y) := by
  simp only [eagerArgsWith, List.zipIdx_cons, List.zipIdx_nil,
    List.forIn_cons, List.forIn_nil, bind_assoc, pure_bind,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  repeat first
  | (with_reducible apply obs_pure
     exact ⟨_, _, rfl, by assumption, by assumption⟩)
  | (with_reducible apply obs_bind (forceArg_obs C _ _); intro out hatom)
  | (with_reducible apply obs_any; intro value)

theorem eagerArgs_pair_captureAtoms
    (hoist : RawExpr → ElabM (SProg C × RawExpr)) (a b : RawExpr) (p q : PrimTy)
    (sc : ElabScope) (st st' : ECtx × Nat) (m m') (out : SProg C × List RawExpr)
    (h : (((eagerArgsWith C hoist [a, b] false [some p, some q]).run sc).run st).run m =
      .ok ((out, st'), m')) :
    ∃ x y, out.2 = [x, y] ∧ CaptureAtom x ∧ CaptureAtom y :=
  eager_pair_obs C hoist a b p q sc st m out st' m' h

end ElabCaptureProof

section
variable (C : Contract) [FreshNames]

/-- Two operands in evaluation order: hold the first read before the second
operand's effects or explicit overflow guards. -/
def hoistPairWith (hoist : RawExpr → ElabM (SProg C × RawExpr)) (first last : RawExpr) : ElabM (SProg C × RawExpr × RawExpr) := do
  let (P, first) ← hoist first
  let powerData := powerDataNeeded C (← read) (← ctx) last
  -- Expanding a pure later power inserts failing guards too. Evaluate the
  -- earlier operand before those guards, even when neither operand writes.
  let (Pc, first) ← if powerData then captureExpr C first else captureBefore C first [last]
  let (Q, last) ← if last.hasIncDec || last.hasIdxLen || last.hasCast || hasNarrow C (← ctx) last || powerData
    then hoist last else pure ([], last)
  pure (P ++ Pc ++ Q, first, last)

/-- Binary operands follow the contract's schedule; their positions in the
operator stay fixed, including for subtraction and comparisons. -/
def hoistBinopWith (hoist : RawExpr → ElabM (SProg C × RawExpr)) (op : BinOp) (a b : RawExpr) : ElabM (SProg C × RawExpr) := do
  let ltr := C.evalOrder.binaryLeftToRight
  let (P, first, last) ← if ltr then hoistPairWith C hoist a b else hoistPairWith C hoist b a
  pure (P, if ltr then .binop op first last else .binop op last first)

/-- A call's arguments, left to right. A non-simple earlier value is held
before hoisting any later argument: casts, fixed-length bases, narrow checks
and modular guards can fail even when they do not modify the state. Bare
names still use the effect-aware capture policy. Already held fresh values
and literals need no additional capture (`captureExpr`). -/
def hoistArgsWith (hoist : RawExpr → ElabM (SProg C × RawExpr)) : List RawExpr → ElabM (SProg C × List RawExpr)
  | [] => pure ([], [])
  | a :: as => do
    let (P, a) ← hoist a
    let (Pc, a) ← if !as.isEmpty && !(a matches .name _) then
        captureExpr C a
      else captureBefore C a as
    let (Q, as) ← hoistArgsWith hoist as
    pure (P ++ Pc ++ Q, a :: as)

end

namespace ElabHoist
variable [FreshNames]

omit [FreshNames] in
def structural (e : RawExpr) : Bool :=
  match e with
  | .call .. | .named .. => false
  | _ => true

/-- A bounded evaluator for structural expression recursion. The public helper
uses the proven sufficient node count; no fuel failure is exposed. -/
def hoistFuel (C : Contract)
    (record : (RawExpr → ElabM (SProg C × RawExpr)) → ElabRec C)
    (stmts : List RawStmt → ElabM (SProg C))
    (fallback : RawExpr → ElabM (SProg C × RawExpr)) : Nat → RawExpr → ElabM (SProg C × RawExpr)
  | 0, e => fallback e
  | n + 1, e =>
    if structural e then
      let child := hoistFuel C record stmts fallback n
      hoistWith C {record child with
        hoist := child, elabStmtsP := stmts,
        hoistArgs := hoistArgsWith C child, hoistBinop := hoistBinopWith C child} e
    else fallback e

/-- Structural recursion with one node-count computation; calls, named calls
retain the supplied fallback behavior; folding runs only in the original arm. -/
def hoistStructural (C : Contract)
    (record : (RawExpr → ElabM (SProg C × RawExpr)) → ElabRec C)
    (stmts : List RawStmt → ElabM (SProg C))
    (fallback : RawExpr → ElabM (SProg C × RawExpr)) (e : RawExpr) :
    ElabM (SProg C × RawExpr) :=
  hoistFuel C record stmts fallback e.nodes e

/-- Named arguments make at most one ordinary-call request, even with duplicate names. -/
def namedClosure (C : Contract) (rc : ElabRec C)
    (fallback : RawExpr → ElabM (SProg C × RawExpr)) : RawExpr → ElabM (SProg C × RawExpr)
  | e@(.named ..) => hoistWith C {rc with hoist := fallback} e
  | e => fallback e


/-- Structural expression recursion with the named-argument rewrite closed. -/
def namedStructural (C : Contract)
    (record : (RawExpr → ElabM (SProg C × RawExpr)) → ElabRec C)
    (stmts : List RawStmt → ElabM (SProg C))
    (fallback : RawExpr → ElabM (SProg C × RawExpr)) :=
  hoistStructural C record stmts (namedClosure C (record fallback) fallback)


end ElabHoist

end Solidity
