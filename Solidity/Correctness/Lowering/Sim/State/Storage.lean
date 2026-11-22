import Solidity.Correctness.Lowering.Sim.Match.Cases
import Solidity.Correctness.Lowering.Total.Coverage

/-!
# State cases, storage declarations and state statements: no associated body

Two leaf conjuncts of `StateCases` (`Sim/Match/Cases.lean`), at every callback
record: `declStorage_arm : StmtArm C rc .declStorage` and
`state_arm : StmtArm C rc .state`. Neither uses the arm or `RecSim`: the site
obligation `SiteSim C [s] ..` of a storage declaration or a state-family
statement `s` holds of no body (`no_site`), so the forward, stability and
backward clauses are obliged of no run.

* An associated body is a standalone-loop site whose raw input is spelled
  (`Total.Spells`), and the decoder spells no statement of these two families
  (`spelled_family`).
* The standalone lowering keeps the head (`lowered_head`): the output's first
  statement is the lowering of the input's first, which has the same family
  (`stmtOutside_family`) or is a lowered loop, a `loop` or a block
  (`lowerLoop_shape`, from `loopFinish_shape`). So `[s]` is the lowering of no
  spelled input.

`Yields x fl Q` (every successful run of `x` from the flags `fl` returns a
value in `Q`) is the postcondition these are proved with, over the equations
of `lowerKernel_total` (`LowerKernel.fixed`). `lowered_head` is the inversion
`Sim/Smoke.lean` leaves open for `revert_arm_of`.

Not proved: `StmtArm C rc .call` (the decoder spells calls) and the two
conjuncts over every `raw`, which `Sim/State/Calls.lean` shows are the whole
per-run statement.
-/
namespace Solidity.Correctness.Lowering.Sim

open Solidity.Goals.Shrink.Lowering
open Solidity.LowerKernel

variable [FreshNames]

/-- Every successful run of `x` from the flags `fl` returns a value in `Q`. -/
def Yields {α : Type} (x : LowerM α) (fl : LoopFlags) (Q : α → Prop) : Prop :=
  ∀ sc st memo r, x fl sc st memo = .ok r → Q r.1.1.1

omit [FreshNames] in
theorem Yields.trivial {α : Type} {x : LowerM α} {fl : LoopFlags} : Yields x fl fun _ => True :=
  fun _ _ _ _ _ => True.intro

omit [FreshNames] in
theorem Yields.pure {α : Type} {a : α} {fl : LoopFlags} {Q : α → Prop} (h : Q a) :
    Yields (Pure.pure a) fl Q := fun _ _ _ _ e => by cases e; exact h

omit [FreshNames] in
theorem Yields.throw {α : Type} {msg : String} {fl : LoopFlags} {Q : α → Prop} :
    Yields (throw msg : LowerM α) fl Q := fun _ _ _ _ e => nomatch e

omit [FreshNames] in
theorem Yields.bind {α β : Type} {x : LowerM α} {f : α → LowerM β} {fl : LoopFlags}
    {P : α → Prop} {Q : β → Prop} (hx : Yields x fl P)
    (hf : ∀ a fl', P a → Yields (f a) fl' Q) : Yields (x >>= f) fl Q := by
  intro sc st memo r h
  have e : (x >>= f) fl sc st memo =
      match x fl sc st memo with
      | .ok (((a, fl'), st'), memo') => f a fl' sc st' memo'
      | .error e => .error e := by
    show (do let v ← x fl sc st memo; f v.1.1.1 v.1.1.2 sc v.1.2 v.2 : Except String _) = _
    cases x fl sc st memo <;> rfl
  rw [e] at h
  cases hxr : x fl sc st memo with
  | error e => rw [hxr] at h; cases h
  | ok v =>
    obtain ⟨⟨⟨a, fl'⟩, st'⟩, memo'⟩ := v
    rw [hxr] at h
    exact hf a fl' (hx _ _ _ _ hxr) _ _ _ _ h

omit [FreshNames] in
theorem Yields.mono {α : Type} {x : LowerM α} {fl : LoopFlags} {P Q : α → Prop}
    (h : Yields x fl P) (le : ∀ a, P a → Q a) : Yields x fl Q :=
  fun _ _ _ _ e => le _ (h _ _ _ _ e)

omit [FreshNames] in
theorem Yields.ret {α : Type} {x : LowerM α} {fl : LoopFlags} {Q : α → Prop}
    (h : Yields x fl Q) : Yields (do let a ← x; Pure.pure a) fl Q :=
  Yields.bind h fun _ _ q => Yields.pure q

omit [FreshNames] in
theorem Yields.get (fl : LoopFlags) : Yields (get : LowerM LoopFlags) fl fun a => a = fl :=
  fun _ _ _ _ e => by cases e; rfl

/-- A lowered loop: a `loop`, or a block. -/
def Shape (s : RawStmt) : Prop := stmtFamily s = .loop ∨ stmtFamily s = .block

/-- The tail of a join point: binds, branches and the calls of the next one. -/
local macro "tail " h:ident : tactic =>
  `(tactic| repeat' first
    | apply $h
    | exact Yields.pure (Or.inl rfl)
    | exact Yields.pure (Or.inr rfl)
    | refine Yields.bind Yields.trivial (fun _ _ _ => ?_)
    | split
    | extract_lets)

theorem loopFinish_shape (spec : RawLoopSpec) (c : RawExpr) (init upd : List RawStmt) (isDo : Bool)
    (bodyCall : LowerM (List RawStmt × List Abrupt)) (fl : LoopFlags) :
    Yields (loopFinish spec c init upd isDo bodyCall) fl fun r => Shape r.1 := by
  unfold loopFinish
  refine Yields.bind Yields.trivial (fun outer _ _ => ?_)
  refine Yields.bind Yields.trivial (fun _ _ _ => ?_)
  refine Yields.bind Yields.trivial (fun _ _ _ => ?_)
  split
  extract_lets exits before iter cond heads returns ab' j2 j1 j0
  have h2 : ∀ a b c d y fl, Yields (j2 a b c d y) fl fun r => Shape r.1 := by
    intro a b c d y fl
    simp -zeta only [j2]
    extract_lets j3
    have h3 : ∀ a b c y fl, Yields (j3 a b c y) fl fun r => Shape r.1 := by
      intro a b c y fl
      simp -zeta only [j3]
      refine Yields.bind Yields.trivial (fun fl' _ _ => ?_)
      extract_lets retX j5 j4
      have h5 : ∀ a b y fl, Yields (j5 a b y) fl fun r => Shape r.1 := by
        intro a b y fl
        simp -zeta only [j5]
        extract_lets spec' w j7 j6
        have h7 : ∀ a y fl, Yields (j7 a y) fl fun r => Shape r.1 := by
          intro a y fl
          simp -zeta only [j7]
          refine Yields.bind Yields.trivial (fun _ _ _ => ?_)
          extract_lets j9 j8
          have h9 : ∀ y fl, Yields (j9 y) fl fun r => Shape r.1 := fun _ _ => .pure (.inr rfl)
          clear_value j9
          have h8 : ∀ y fl, Yields (j8 y) fl fun r => Shape r.1 := by
            intro y fl
            simp -zeta only [j8]
            tail h9
          clear_value j8
          tail h8
        clear_value j7
        have h6 : ∀ a y fl, Yields (j6 a y) fl fun r => Shape r.1 := by
          intro a y fl
          simp -zeta only [j6]
          tail h7
        clear_value j6
        tail h6
      clear_value j5
      have h4 : ∀ a b y fl, Yields (j4 a b y) fl fun r => Shape r.1 := by
        intro a b y fl
        simp -zeta only [j4]
        tail h5
      clear_value j4
      tail h4
    clear_value j3
    tail h3
  clear_value j2
  have h1 : ∀ a b c d y fl, Yields (j1 a b c d y) fl fun r => Shape r.1 := by
    intro a b c d y fl
    simp -zeta only [j1]
    tail h2
  clear_value j1
  have h0 : ∀ a b c d y fl, Yields (j0 a b c d y) fl fun r => Shape r.1 := by
    intro a b c d y fl
    simp -zeta only [j0]
    tail h1
  clear_value j0
  tail h0

/-- A loop whose condition has no effect is finished directly. -/
theorem lowerLoop_plain (rs : Option (List String)) (a : RawLoopSpec) (b : List RawStmt)
    (fl : LoopFlags) :
    Yields (lowerLoop rs (.whileLoop a (.bool true) b)) fl fun r => Shape r.1 := by
  rw [fixed.2.2]
  have plain : (RawExpr.bool true).hasIncDec = false := by simp [RawExpr.hasIncDec, RawExpr.any]
  simp only [LowerKernel.loopStep, plain, Bool.and_false, Bool.false_and, Bool.false_eq_true, if_false]
  exact Yields.bind Yields.trivial fun _ _ _ => loopFinish_shape _ _ _ _ _ _ _

/-- A lowered loop is a `loop` or a block. -/
theorem lowerLoop_shape (rs : Option (List String)) (s : RawStmt) (fl : LoopFlags) :
    Yields (lowerLoop rs s) fl fun r => Shape r.1 := by
  rw [fixed.2.2]
  simp only [LowerKernel.loopStep]
  repeat' first
    | with_reducible exact Yields.ret (lowerLoop_plain _ _ _ _)
    | with_reducible exact loopFinish_shape _ _ _ _ _ _ _
    | with_reducible refine Yields.bind Yields.trivial (fun _ _ _ => ?_)
    | split

omit [FreshNames] in
/-- Outside a loop a statement that is not a loop keeps its family. -/
theorem stmtOutside_family (L : ListCalls) (rs : Option (List String)) (x : RawStmt)
    (fl : LoopFlags) :
    Yields (LowerKernel.stmtOutside L rs x) fl fun r => stmtFamily r.1 = stmtFamily x := by
  unfold LowerKernel.stmtOutside
  split <;> repeat' first
    | exact Yields.throw
    | exact Yields.pure rfl
    | refine Yields.bind Yields.trivial (fun _ _ _ => ?_)

/-- Outside a loop a lowered statement keeps its family or is a lowered loop. -/
theorem lowerStmt_head (rs : Option (List String)) (x : RawStmt) (fl : LoopFlags)
    (outside : fl.inLoop = false) :
    Yields (lowerStmt rs x) fl fun r => stmtFamily r.1 = stmtFamily x ∨ Shape r.1 := by
  rw [fixed.2.1]
  simp only [LowerKernel.stmtStep]
  split <;> simp only [if_true, Bool.false_eq_true, if_false]
  case h_5 =>
    rw [pure_bind]
    refine Yields.bind (Yields.get fl) (fun a fl' same => ?_)
    subst same
    simp only [outside, Bool.false_eq_true, if_false]
    exact Yields.ret ((stmtOutside_family _ rs x _).mono fun _ => Or.inl)
  all_goals exact Yields.ret ((lowerLoop_shape rs _ fl).mono fun _ => Or.inr)

/-- **The head of a lowered block**, outside a loop: the lowering of the
block's first statement. -/
theorem lowerList_head (rs : Option (List String)) (x : RawStmt) (rest : List RawStmt)
    (fl : LoopFlags) (outside : fl.inLoop = false) :
    Yields (lowerList rs (x :: rest)) fl fun r =>
      ∃ s tail, r.1 = s :: tail ∧ (stmtFamily s = stmtFamily x ∨ Shape s) := by
  rw [fixed.1]
  simp only [LowerKernel.listStep]
  refine Yields.bind (lowerStmt_head rs x fl outside) (fun a _ head => ?_)
  repeat' first
    | exact Yields.pure ⟨_, _, rfl, head⟩
    | refine Yields.bind Yields.trivial (fun _ _ _ => ?_)
    | split

/-- A standalone lowering run is a run of `lowerList` from no flags. -/
theorem lowerAt_run (raw : List RawStmt) (sc : ElabScope) (st : ECtx × Nat) (memo : CallMemo) :
    (((lowerAt none raw).run sc).run st).run memo =
      match lowerList none raw {} sc st memo with
      | .ok v => .ok ((v.1.1.1.1, v.1.2), v.2)
      | .error e => .error e := by
  simp only [lowerAt, lowerLoops]
  generalize lowerList none raw = x
  show (((do let r ← (do let p ← x {} ; pure p.1 : ElabM _); pure r.1 : ElabM (List RawStmt)) sc)
    st) memo = _
  rw [Total.Coverage.elabBind, Total.Coverage.elabBind]
  cases x {} sc st memo <;> rfl

/-- **The standalone lowering, inverted at its head**: the output is empty,
or its first statement is the lowering of the input's first: of the same
family, or a lowered loop. -/
theorem lowered_head {raw out : List RawStmt} {sc : ElabScope} {st st' : ECtx × Nat}
    {memo memo' : CallMemo}
    (run : (((lowerAt none raw).run sc).run st).run memo = .ok ((out, st'), memo')) :
    out = [] ∨ ∃ x rest s tail, raw = x :: rest ∧ out = s :: tail ∧
      (stmtFamily s = stmtFamily x ∨ Shape s) := by
  rw [lowerAt_run] at run
  cases raw with
  | nil => rw [fixed.1] at run; cases run; exact .inl rfl
  | cons x rest =>
    cases hv : lowerList none (x :: rest) {} sc st memo with
    | error e => rw [hv] at run; cases run
    | ok v =>
      rw [hv] at run
      cases run
      obtain ⟨s, tail, eq, family⟩ := lowerList_head none x rest {} rfl _ _ _ _ hv
      exact .inr ⟨x, rest, s, tail, rfl, eq, family⟩

omit [FreshNames] in
/-- The decoder spells no storage declaration and no state statement. -/
theorem spelled_family {k : Source.SCtx} {x : RawStmt} {rest : List RawStmt}
    {b : Source.Syn (.list (.item k))} (h : Total.Spells.Items k (x :: rest) b) :
    stmtFamily x ≠ .declStorage ∧ stmtFamily x ≠ .state := by
  cases h with
  | unchecked => (constructor <;> intro h <;> cases h)
  | stmt hs =>
    cases hs <;> first | (constructor <;> intro h <;> cases h) | skip
    rename_i simple
    cases simple <;> first | (constructor <;> intro h <;> cases h) | skip
    all_goals
      rename_i value
      cases value <;> (constructor <;> intro h <;> cases h)

variable (C : Contract)

/-- **No associated body lowers to a storage declaration or a state
statement**: the site obligation of such a statement holds of no body. -/
theorem no_site (s : RawStmt) (family : stmtFamily s = .declStorage ∨ stmtFamily s = .state)
    (sc : ElabScope) (st : ECtx × Nat) (P : SProg C) (st' : ECtx × Nat) :
    SiteSim C [s] sc st P st' := by
  intro b Γ o m el low _ _ assoc
  obtain ⟨_, _, _, _, ⟨plain, _, _, syn, _, _, _, _, items, _⟩, _⟩ := (assoc : Assoc b ⟨C, Γ, o⟩ m)
  have site : b.site = .loop := by
    cases hs : b.site <;> simp [Total.Decode.plain, request, siteCallee, hs] at plain <;> rfl
  simp only [Lowered, site] at low
  rcases lowered_head low.2 with empty | ⟨x, rest, s', tail, hraw, hout, hfam⟩
  · exact nomatch el.1.symm.trans empty
  · cases el.1.symm.trans hout
    have items : Total.Spells.Items .body (x :: rest) syn := hraw ▸ items
    obtain ⟨n1, n2⟩ := spelled_family items
    rcases family with f | f <;> rcases hfam with h | h | h <;>
      first
        | exact (n1 (h.symm.trans f)).elim
        | exact (n2 (h.symm.trans f)).elim
        | exact absurd (f.symm.trans h) (by decide)

/-- **The storage declarations**: the leaf conjuncts hold of no body. -/
theorem declStorage_arm (rc : ElabRec C) : StmtArm C rc .declStorage :=
  ⟨fun s family sc st P st' _ => no_site C s (.inl family) sc st P st',
    fun s family sc st P st' _ => no_site C s (.inl family) sc st P st'⟩

/-- **The remaining state statements**: the leaf conjuncts hold of no body. -/
theorem state_arm (rc : ElabRec C) : StmtArm C rc .state :=
  ⟨fun s family sc st P st' _ => no_site C s (.inr family) sc st P st',
    fun s family sc st P st' _ => no_site C s (.inr family) sc st P st'⟩

end Solidity.Correctness.Lowering.Sim
