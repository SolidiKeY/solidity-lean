import Solidity.Correctness.Lowering.Total.Contract
import Solidity.Correctness.Lowering.Loops.Capture

/-!
# Raw coverage of the loop families by `LowersTo` (e2e-loops-coverage)

What is proved here, about the frozen relation `Total.LowersTo` alone (no
production totality, no `lowerLoops`):

* `LowersTo.unique`: the relation is a partial function of the input and the
  whole incoming state. A deeper derivation refines a shallower one
  (`derive_mono`), so two derivations of any depths agree.
* `covered`: on every raw input shape behind the e1 families (`FamilyInput`:
  the six `Loops.Shape` loops, the `lowerLoops` half of the four
  `Loops.RetShape` bodies, and two nested loops), at every scope, state,
  return-slot list and spelling of fresh names, the relation holds of exactly
  one output and outgoing state, written out. Conditions, assigned
  expressions, `for` initializers and updates, and dropped tails are
  arbitrary, not the Boolean pair `i, a` of the samples.
* `sample_inputs`, `rawProbe_actual`: the e1 sample inputs are instances, and
  the quoted actual producer output of the while/break probe is the relation's.

What is not proved, and cannot be from this interface. The loop families
(`Loops.NormalFamilyCorrect`, `Loops.ReturnFamilyCorrect`) are statements about
intrinsic programs (`Blk`), reached from a raw output only through `elabStmtsP`
and `SProg.chain`. `elabStmtsP` is a `partial` definition, so nothing follows
in the kernel from `Total.SuccessfulElaboration`: no theorem here or elsewhere
can conclude `Loops.Accepts` from a `LowersTo` output. And `LowersTo` holds far
outside the families' raw image (`nestedBreak`, `nestedReturn`, every loop-free
block, every body the six shapes do not list), where no family member and no
semantic lemma exists. So "every `LowersTo` output lies in the loop families"
is false as a universal statement and unreachable on the family inputs; this
module is its raw half. `Solidity.Goals.lowerLoopsCorrect` is left unstated.
-/
namespace Solidity.Correctness.Lowering.Total.Coverage

open Solidity.LowerKernel

/-- Success refinement: every successful run of `x` is the same run of `y`. -/
structure Le {α : Type} (x y : LowerM α) : Prop where
  run : ∀ fl sc st memo r, x fl sc st memo = .ok r → y fl sc st memo = .ok r

theorem Le.refl {α : Type} (x : LowerM α) : Le x x := ⟨fun _ _ _ _ _ h => h⟩

theorem Le.bind {α β : Type} {x x' : LowerM α} {f f' : α → LowerM β}
    (hx : Le x x') (hf : ∀ a, Le (f a) (f' a)) : Le (x >>= f) (x' >>= f') := by
  refine ⟨fun fl sc st memo r h => ?_⟩
  have e : ∀ (y : LowerM α) (g : α → LowerM β), (y >>= g) fl sc st memo =
      match y fl sc st memo with
      | .ok (((a, fl'), st'), memo') => g a fl' sc st' memo'
      | .error e => .error e := by
    intro y g
    show (do let v ← y fl sc st memo; g v.1.1.1 v.1.1.2 sc v.1.2 v.2 : Except String _) = _
    cases y fl sc st memo <;> rfl
  rw [e] at h ⊢
  cases hxr : x fl sc st memo with
  | error e => rw [hxr] at h; cases h
  | ok v =>
    obtain ⟨⟨⟨a, fl'⟩, st'⟩, memo'⟩ := v
    rw [hxr] at h
    rw [hx.run _ _ _ _ _ hxr]
    exact (hf a).run _ _ _ _ _ h

section Names

variable [FreshNames]

/- Structural refinement of two computations built alike from refined calls. -/
set_option hygiene false in
local macro "le_calls" : tactic => `(tactic|
  repeat' first
    | with_reducible exact Le.refl _
    | with_reducible exact h
    | with_reducible exact hL _ _
    | with_reducible exact hP _ _
    | with_reducible apply outside_mono
    | with_reducible apply Le.bind
    | (intro a; rcases a with ⟨_, _⟩; dsimp only)
    | (intro _)
    | split)

theorem listStep_mono {L L' : ListCalls} {S S' : StmtCalls}
    (hL : ∀ rs ss, Le (L rs ss) (L' rs ss)) (hP : ∀ rs s, Le (S rs s) (S' rs s))
    (rs : Option (List String)) (ss : List RawStmt) :
    Le (LowerKernel.listStep L S rs ss) (LowerKernel.listStep L' S' rs ss) := by
  cases ss with
  | nil => exact Le.refl _
  | cons s ss =>
    simp only [LowerKernel.listStep]
    le_calls

omit [FreshNames] in
theorem outside_mono {α : Type} {x y : LowerM α} (h : Le x y) :
    Le (LowerM.outside x) (LowerM.outside y) := by
  simp only [LowerM.outside]
  le_calls

omit [FreshNames] in
theorem stmtOutside_mono {L L' : ListCalls} (hL : ∀ rs ss, Le (L rs ss) (L' rs ss))
    (rs : Option (List String)) (s : RawStmt) :
    Le (stmtOutside L rs s) (stmtOutside L' rs s) := by
  cases s <;> simp only [stmtOutside] <;> le_calls

theorem stmtInside_mono {L L' : ListCalls} (hL : ∀ rs ss, Le (L rs ss) (L' rs ss))
    (rs : Option (List String)) (s : RawStmt) :
    Le (stmtInside L rs s) (stmtInside L' rs s) := by
  cases s <;> simp only [stmtInside] <;> le_calls

theorem stmtStep_mono {L L' : ListCalls} {P P' : StmtCalls}
    (hL : ∀ rs ss, Le (L rs ss) (L' rs ss)) (hP : ∀ rs s, Le (P rs s) (P' rs s))
    (rs : Option (List String)) (s : RawStmt) :
    Le (LowerKernel.stmtStep L P rs s) (LowerKernel.stmtStep L' P' rs s) := by
  have h := stmtOutside_mono hL rs s
  have hi := stmtInside_mono hL rs s
  simp only [LowerKernel.stmtStep]
  repeat' first
    | with_reducible exact Le.refl _
    | with_reducible exact h
    | with_reducible exact hi
    | with_reducible exact hP _ _
    | with_reducible apply Le.bind
    | (intro _)
    | split

theorem loopFinish_mono (spec : RawLoopSpec) (c : RawExpr) (init upd : List RawStmt)
    (isDo : Bool) {x y : LowerM (List RawStmt × List Abrupt)} (h : Le x y) :
    Le (loopFinish spec c init upd isDo x) (loopFinish spec c init upd isDo y) := by
  unfold LowerKernel.loopFinish
  le_calls

theorem loopStep_mono {L L' : ListCalls} {P P' : StmtCalls}
    (hL : ∀ rs ss, Le (L rs ss) (L' rs ss)) (hP : ∀ rs s, Le (P rs s) (P' rs s))
    (rs : Option (List String)) (s : RawStmt) :
    Le (LowerKernel.loopStep L P rs s) (LowerKernel.loopStep L' P' rs s) := by
  rw [← factoredStep_eq, ← factoredStep_eq]
  unfold factoredStep
  generalize loopParts s = parts
  rcases parts with ⟨spec, c, init, upd, body, isDo⟩
  dsimp only
  split
  · le_calls
  · exact loopFinish_mono spec c init upd isDo (hL rs body)

/-- A deeper derivation refines a shallower one, rule by rule. -/
theorem derive_succ : ∀ n : Nat,
    (∀ rs ss, Le ((derive n).list rs ss) ((derive (n + 1)).list rs ss)) ∧
    (∀ rs s, Le ((derive n).stmt rs s) ((derive (n + 1)).stmt rs s)) ∧
    (∀ rs s, Le ((derive n).loop rs s) ((derive (n + 1)).loop rs s))
  | 0 => ⟨fun _ _ => ⟨fun _ _ _ _ _ h => nomatch h⟩, fun _ _ => ⟨fun _ _ _ _ _ h => nomatch h⟩,
      fun _ _ => ⟨fun _ _ _ _ _ h => nomatch h⟩⟩
  | n + 1 =>
    have ih := derive_succ n
    ⟨listStep_mono ih.1 ih.2.1, stmtStep_mono ih.1 ih.2.2, loopStep_mono ih.1 ih.2.2⟩

omit [FreshNames] in
theorem Le.trans {α : Type} {x y z : LowerM α} (h : Le x y) (k : Le y z) : Le x z :=
  ⟨fun _ _ _ _ _ e => k.run _ _ _ _ _ (h.run _ _ _ _ _ e)⟩

theorem derive_mono {m n : Nat} (h : m ≤ n) (rs : Option (List String)) (ss : List RawStmt) :
    Le ((derive m).list rs ss) ((derive n).list rs ss) := by
  induction h with
  | refl => exact Le.refl _
  | step _ ih => exact ih.trans ((derive_succ _).1 rs ss)

/-- The run inside `LowersTo`, at one depth. -/
def runAt (depth : Nat) (rs : Option (List String)) (input : List RawStmt) (scope : ElabScope)
    (before : Checker.Snapshot) : Except String ((List RawStmt × ECtx × Nat) × CallMemo) :=
  (((do pure (← ((derive depth).list rs input).run' {}).1 :
    ElabM (List RawStmt)).run scope).run before.locals).run before.memo

omit [FreshNames] in
theorem elabBind {α β : Type} (x : ElabM α) (f : α → ElabM β) (sc : ElabScope)
    (l : ECtx × Nat) (m : CallMemo) :
    (x >>= f) sc l m = (do let v ← x sc l m; f v.1.1 sc v.1.2 v.2 : Except String _) := by
  show (do let v ← x sc l m; f v.1.1 sc v.1.2 v.2 : Except String _) = _
  cases x sc l m <;> rfl

theorem runAt_eq (depth : Nat) (rs : Option (List String)) (input : List RawStmt)
    (scope : ElabScope) (before : Checker.Snapshot) :
    runAt depth rs input scope before =
      match (derive depth).list rs input {} scope before.locals before.memo with
      | .ok v => .ok ((v.1.1.1.1, v.1.2), v.2)
      | .error e => .error e := by
  generalize hx : (derive depth).list rs input = x
  unfold runAt
  rw [hx]
  show (((do let r ← (do let p ← x {} ; pure p.1 : ElabM _); pure r.1 : ElabM (List RawStmt)) scope)
    before.locals) before.memo = _
  rw [elabBind, elabBind]
  cases x {} scope before.locals before.memo <;> rfl

theorem runAt_mono {m n : Nat} (h : m ≤ n) {rs : Option (List String)} {input : List RawStmt}
    {scope : ElabScope} {before : Checker.Snapshot} {r}
    (run : runAt m rs input scope before = .ok r) : runAt n rs input scope before = .ok r := by
  rw [runAt_eq] at run ⊢
  cases hv : (derive m).list rs input {} scope before.locals before.memo with
  | error e => rw [hv] at run; cases run
  | ok v => rw [hv] at run; rw [(derive_mono h rs input).run _ _ _ _ _ hv]; exact run

theorem loopStep_finish (L : ListCalls) (P : StmtCalls) (rs : Option (List String))
    (s : RawStmt) (hg : loopGuard s = false) :
    LowerKernel.loopStep L P rs s =
      loopFinish (loopParts s).1 (loopParts s).2.1 (loopParts s).2.2.1 (loopParts s).2.2.2.1
        (loopParts s).2.2.2.2.2 (L rs (loopBody s)) := by
  rw [← factoredStep_eq]
  unfold factoredStep loopBody
  generalize loopParts s = parts
  rcases parts with ⟨spec, c, init, upd, body, isDo⟩
  simp [hg]

theorem derive_list (n : Nat) :
    (derive (n + 1)).list = LowerKernel.listStep (derive n).list (derive n).stmt := rfl
theorem derive_stmt (n : Nat) :
    (derive (n + 1)).stmt = LowerKernel.stmtStep (derive n).list (derive n).loop := rfl
theorem derive_loop (n : Nat) :
    (derive (n + 1)).loop = LowerKernel.loopStep (derive n).list (derive n).loop := rfl

theorem derive_list_nil (n : Nat) (rs : Option (List String)) :
    (derive (n + 1)).list rs [] = pure ([], []) := rfl

theorem list_cons (n : Nat) (rs : Option (List String)) (s : RawStmt) (rest : List RawStmt) :
    (derive (n + 1)).list rs (s :: rest) =
      (derive n).stmt rs s >>= fun r =>
        LowerKernel.listStep (derive n).list (fun _ _ => pure r) rs (s :: rest) := by
  rw [derive_list]
  simp only [LowerKernel.listStep, pure_bind]

theorem stmt_while (n : Nat) (rs : Option (List String)) (a : RawLoopSpec) (c : RawExpr)
    (b : List RawStmt) (hg : loopGuard (.whileLoop a c b) = false) :
    (derive (n + 2)).stmt rs (.whileLoop a c b) =
      loopFinish a c [] [] false ((derive n).list rs b) := by
  rw [derive_stmt (n + 1), derive_loop n]
  simp only [LowerKernel.stmtStep, loopStep_finish _ _ _ _ hg]
  simp only [loopParts, loopBody, ↓reduceIte, bind_pure]

theorem stmt_for (n : Nat) (rs : Option (List String)) (a : RawLoopSpec) (i : List RawStmt)
    (c : Option RawExpr) (u b : List RawStmt) :
    (derive (n + 2)).stmt rs (.forLoop a i c u b) =
      loopFinish a (c.getD (.bool true)) i u false ((derive n).list rs b) := by
  rw [derive_stmt (n + 1), derive_loop n]
  simp only [LowerKernel.stmtStep,
    loopStep_finish _ _ _ _ (rfl : loopGuard (.forLoop a i c u b) = false)]
  simp only [loopParts, loopBody, ↓reduceIte, bind_pure]

theorem stmt_do (n : Nat) (rs : Option (List String)) (a : RawLoopSpec) (b : List RawStmt)
    (c : RawExpr) :
    (derive (n + 2)).stmt rs (.doWhile a b c) =
      loopFinish a c [] [] true ((derive n).list rs b) := by
  rw [derive_stmt (n + 1), derive_loop n]
  simp only [LowerKernel.stmtStep,
    loopStep_finish _ _ _ _ (rfl : loopGuard (.doWhile a b c) = false)]
  simp only [loopParts, loopBody, ↓reduceIte, bind_pure]

omit [FreshNames] in
theorem whileGuard_false (a : RawLoopSpec) (c : RawExpr) (b : List RawStmt)
    (hc : c.hasIncDec = false) : loopGuard (.whileLoop a c b) = false := by
  simp [loopGuard, loopParts, hc]

omit [FreshNames] in
theorem whileGuard_true (c : RawExpr) (b : List RawStmt) (hc : c.hasIncDec = true) :
    loopGuard (.whileLoop {} c b) = true := by
  simp [loopGuard, loopParts, hc]

theorem loopStep_rewrite (L : ListCalls) (P : StmtCalls) (rs : Option (List String))
    (s : RawStmt) (hg : loopGuard s = true) :
    LowerKernel.loopStep L P rs s = P rs (loopRewrite s) := by
  rw [← factoredStep_eq]
  unfold factoredStep loopRewrite
  generalize loopParts s = parts
  rcases parts with ⟨spec, c, init, upd, body, isDo⟩
  simp [hg]

/-- An effectful `while` condition with no specification: the synthetic head. -/
theorem stmt_while_effect (n : Nat) (rs : Option (List String)) (c : RawExpr)
    (b : List RawStmt) (hc : c.hasIncDec = true) :
    (derive (n + 3)).stmt rs (.whileLoop {} c b) =
      loopFinish {} (.bool true) [] [] false
        ((derive n).list rs [.ite (.unop .not c) [.brk] [], .block b]) := by
  have hf : loopGuard (.whileLoop {} (.bool true) [.ite (.unop .not c) [.brk] [], .block b]) =
      false := whileGuard_false _ _ _ (by simp [RawExpr.hasIncDec, RawExpr.any])
  rw [derive_stmt (n + 2), derive_loop (n + 1)]
  simp only [LowerKernel.stmtStep, loopStep_rewrite _ _ _ _ (whileGuard_true c b hc)]
  simp only [loopRewrite, loopParts, ↓reduceIte, bind_pure]
  rw [derive_loop n, loopStep_finish _ _ _ _ hf]
  rfl

/-- A derivation's list rule, rewritten to `x`, with a successful run of `x`. -/
theorem lowersTo_of_run {depth : Nat} {rs : Option (List String)} {input output : List RawStmt}
    {scope : ElabScope} {before after : Checker.Snapshot} {x : LowerM (List RawStmt × List Abrupt)}
    {ab : List Abrupt} {fl : LoopFlags} (eq : (derive depth).list rs input = x)
    (run : x {} scope before.locals before.memo =
      .ok ((((output, ab), fl), after.locals), after.memo)) :
    LowersTo rs input output scope before after := by
  refine ⟨depth, ?_⟩
  show runAt depth rs input scope before = _
  rw [runAt_eq, eq, run]

/-- `LowersTo` is a partial function of the input and the whole incoming state:
two derivations, of any depths, give the same output and the same outgoing
state. No totality of the production kernel is used. -/
theorem LowersTo.unique {rs : Option (List String)} {input output output' : List RawStmt}
    {scope : ElabScope} {before after after' : Checker.Snapshot}
    (h : LowersTo rs input output scope before after)
    (k : LowersTo rs input output' scope before after') : output = output' ∧ after = after' := by
  obtain ⟨m, hm⟩ := h
  obtain ⟨n, hn⟩ := k
  have hm' : runAt (max m n) rs input scope before = _ := runAt_mono (Nat.le_max_left m n) hm
  have hn' : runAt (max m n) rs input scope before = _ := runAt_mono (Nat.le_max_right m n) hn
  rw [hm'] at hn'
  cases after
  cases after'
  simp only [Except.ok.injEq, Prod.mk.injEq] at hn'
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hn'
  exact ⟨rfl, rfl⟩

/-- A derived instance characterizes every output of its input and state. -/
theorem LowersTo.iff_of {rs : Option (List String)} {input output output' : List RawStmt}
    {scope : ElabScope} {before after after' : Checker.Snapshot}
    (h : LowersTo rs input output scope before after) :
    LowersTo rs input output' scope before after' ↔ output' = output ∧ after' = after :=
  ⟨fun k => ⟨(LowersTo.unique h k).1.symm, (LowersTo.unique h k).2.symm⟩, fun e => e.1 ▸ e.2 ▸ h⟩

/-! ### Raw outputs of the family inputs -/

/-- The spelling of the `j`-th fresh name after the incoming counter. -/
def flag (base : String) (st : Checker.Snapshot) (j : Nat) : String :=
  toString (Var.fresh base (st.locals.2 + j))

/-- `!x`. -/
def nb (x : String) : RawExpr := .unop .not (.name x)

/-- The incoming state with `k` fresh names taken; locals and memo unchanged. -/
def taken (st : Checker.Snapshot) (k : Nat) : Checker.Snapshot :=
  ⟨(st.locals.1, st.locals.2 + k), st.memo⟩

omit [FreshNames] in
theorem hasIncDec_assign (l r : RawExpr) : (RawExpr.assign l r).hasIncDec = true := by
  simp [RawExpr.hasIncDec, RawExpr.any]

/- Rewrite the derivation's list rule with the loop equations, then run it. -/
local macro "lower_run " d:num " [" rules:Lean.Parser.Tactic.rwRule,* "]" : tactic => `(tactic|
  (refine lowersTo_of_run (depth := $d) (x := ?x) (ab := ?ab) (fl := ?fl) ?eq ?run
   case eq => rw [$rules,*]
   case run => rfl))

/-- `while (c) break;`, `c` with an effect (`Shape.whileBreak`, any condition). -/
theorem whileBreak (rs : Option (List String)) (c : RawExpr) (hc : c.hasIncDec = true)
    (sc : ElabScope) (st : Checker.Snapshot) :
    LowersTo rs [.whileLoop {} c [.brk]]
      [.block [.declBool (flag "brk" st 0) false,
        .loop {} (.binop .and (nb (flag "brk" st 0)) (.bool true))
          [.ite (.unop .not c) [.setBool (flag "brk" st 0) true] [],
           .ite (nb (flag "brk" st 0)) [.block [.setBool (flag "brk" st 0) true]] []]]]
      sc st (taken st 1) := by
  lower_run 12 [list_cons, stmt_while_effect _ _ _ _ hc]

/-- `while (c) break;`, `c` without an effect: the condition stays in the head. -/
theorem whileBreakPure (rs : Option (List String)) (c : RawExpr) (hc : c.hasIncDec = false)
    (sc : ElabScope) (st : Checker.Snapshot) :
    LowersTo rs [.whileLoop {} c [.brk]]
      [.block [.declBool (flag "brk" st 0) false,
        .loop {} (.binop .and (nb (flag "brk" st 0)) c) [.setBool (flag "brk" st 0) true]]]
      sc st (taken st 1) := by
  lower_run 12 [list_cons, stmt_while _ _ _ _ _ (whileGuard_false _ _ _ hc)]

/-- `for (init; ; ) break;` (`Shape.forBreak` without an update, any initializer). -/
theorem forBreak (rs : Option (List String)) (init : List RawStmt)
    (sc : ElabScope) (st : Checker.Snapshot) :
    LowersTo rs [.forLoop {} init none [] [.brk]]
      [.block (init ++ [.declBool (flag "brk" st 0) false] ++
        [.loop {} (.binop .and (nb (flag "brk" st 0)) (.bool true))
          [.setBool (flag "brk" st 0) true]])]
      sc st (taken st 1) := by
  cases init <;> lower_run 12 [list_cons, stmt_for]

/-- `for (init; ; u, us) break;` (`Shape.forBreak` with an update): the update
is guarded by the break flag. -/
theorem forBreakUpdate (rs : Option (List String)) (init : List RawStmt) (u : RawStmt)
    (us : List RawStmt) (sc : ElabScope) (st : Checker.Snapshot) :
    LowersTo rs [.forLoop {} init none (u :: us) [.brk]]
      [.block (init ++ [.declBool (flag "brk" st 0) false] ++
        [.loop {} (.binop .and (nb (flag "brk" st 0)) (.bool true))
          [.setBool (flag "brk" st 0) true, .ite (nb (flag "brk" st 0)) (u :: us) []]])]
      sc st (taken st 1) := by
  cases init <;> lower_run 12 [list_cons, stmt_for]

/-- `while (c) { l = r; continue; tail }`, `c` with an effect
(`Shape.whileContinue`): the statements after `continue` are dropped unread. -/
theorem whileContinue (rs : Option (List String)) (c l r : RawExpr) (tail : List RawStmt)
    (hc : c.hasIncDec = true) (sc : ElabScope) (st : Checker.Snapshot) :
    LowersTo rs [.whileLoop {} c (.assign l r :: .cont :: tail)]
      [.block [.declBool (flag "brk" st 0) false,
        .loop {} (.binop .and (nb (flag "brk" st 0)) (.bool true))
          [.declBool (flag "cnt" st 1) false,
           .ite (.unop .not c) [.setBool (flag "brk" st 0) true] [],
           .ite (nb (flag "brk" st 0))
             [.block [.assign l r, .setBool (flag "cnt" st 1) true]] []]]]
      sc st (taken st 2) := by
  lower_run 12 [list_cons, stmt_while_effect _ _ _ _ hc]

/-- `do { l = r; break; } while (c);` (`Shape.doBreak`, any condition). -/
theorem doBreak (rs : Option (List String)) (c l r : RawExpr)
    (sc : ElabScope) (st : Checker.Snapshot) :
    LowersTo rs [.doWhile {} [.assign l r, .brk] c]
      [.block [.declBool (flag "first" st 1) true, .declBool (flag "brk" st 0) false,
        .loop {} (.binop .and (nb (flag "brk" st 0)) (.binop .or (.name (flag "first" st 1)) c))
          [.setBool (flag "first" st 1) false, .assign l r, .setBool (flag "brk" st 0) true]]]
      sc st (taken st 2) := by
  lower_run 12 [list_cons, stmt_do]

/-- `while (c) l = r;`, `c` with an effect (`Shape.whileReset`). -/
theorem whileReset (rs : Option (List String)) (c l r : RawExpr) (hc : c.hasIncDec = true)
    (sc : ElabScope) (st : Checker.Snapshot) :
    LowersTo rs [.whileLoop {} c [.assign l r]]
      [.block [.declBool (flag "brk" st 0) false,
        .loop {} (.binop .and (nb (flag "brk" st 0)) (.bool true))
          [.ite (.unop .not c) [.setBool (flag "brk" st 0) true] [],
           .ite (nb (flag "brk" st 0)) [.block [.assign l r]] []]]]
      sc st (taken st 1) := by
  lower_run 12 [list_cons, stmt_while_effect _ _ _ _ hc]

/-- `do { l = r; continue; tail } while (c);` (`Shape.doContinue`, any
condition): no break or return exit, so no guard and no outer flag. -/
theorem doContinue (rs : Option (List String)) (c l r : RawExpr) (tail : List RawStmt)
    (sc : ElabScope) (st : Checker.Snapshot) :
    LowersTo rs [.doWhile {} (.assign l r :: .cont :: tail) c]
      [.block [.declBool (flag "first" st 1) true,
        .loop {} (.binop .or (.name (flag "first" st 1)) c)
          [.setBool (flag "first" st 1) false, .declBool (flag "cnt" st 0) false,
           .assign l r, .setBool (flag "cnt" st 0) true]]]
      sc st (taken st 2) := by
  lower_run 12 [list_cons, stmt_do]

/-- The lowered `while (c) return;`, `c` with an effect, before `lowerReturns`. -/
def whileReturnOut (c : RawExpr) (st : Checker.Snapshot) : RawStmt :=
  .block [.declBool (flag "brk" st 0) false, .declBool (flag "ret" st 1) false,
    .loop {} (.binop .and (nb (flag "brk" st 0))
        (.binop .and (nb (flag "ret" st 1)) (.bool true)))
      [.ite (.unop .not c) [.setBool (flag "brk" st 0) true] [],
       .ite (nb (flag "brk" st 0)) [.block [.block [.setBool (flag "ret" st 1) true]]] []],
    .ite (.name (flag "ret" st 1)) [.ret none] []]

/-- `while (c) return;` in a body with return variables `slots`
(`RetShape.whileReturn`, the `lowerLoops` half of the callee-body pass). -/
theorem whileReturn (slots : List String) (c : RawExpr) (hc : c.hasIncDec = true)
    (sc : ElabScope) (st : Checker.Snapshot) :
    LowersTo (some slots) [.whileLoop {} c [.ret none]] [whileReturnOut c st]
      sc st (taken st 2) := by
  lower_run 12 [list_cons, stmt_while_effect _ _ _ _ hc]

/-- `do { l = r; return; } while (c);` (`RetShape.doReturn`, same half). -/
theorem doReturn (slots : List String) (c l r : RawExpr)
    (sc : ElabScope) (st : Checker.Snapshot) :
    LowersTo (some slots) [.doWhile {} [.assign l r, .ret none] c]
      [.block [.declBool (flag "first" st 1) true, .declBool (flag "ret" st 0) false,
        .loop {} (.binop .and (nb (flag "ret" st 0)) (.binop .or (.name (flag "first" st 1)) c))
          [.setBool (flag "first" st 1) false, .assign l r,
           .block [.setBool (flag "ret" st 0) true]],
        .ite (.name (flag "ret" st 0)) [.ret none] []]]
      sc st (taken st 2) := by
  lower_run 12 [list_cons, stmt_do]

/-- `while (c) return; l = r;` (`RetShape.whileReturnThen`, same half): the
suffix is left after the block; `lowerReturns` moves it later. -/
theorem whileReturnThen (slots : List String) (c l r : RawExpr) (hc : c.hasIncDec = true)
    (sc : ElabScope) (st : Checker.Snapshot) :
    LowersTo (some slots) [.whileLoop {} c [.ret none], .assign l r]
      [whileReturnOut c st, .assign l r] sc st (taken st 2) := by
  lower_run 12 [list_cons, stmt_while_effect _ _ _ _ hc]

/-- `if (c) return;` outside a loop (`RetShape.returnFlag`): unchanged, no
fresh name; all of its lowering is `lowerReturns`. -/
theorem returnFlag (rs : Option (List String)) (c : RawExpr)
    (sc : ElabScope) (st : Checker.Snapshot) :
    LowersTo rs [.ite c [.ret none] []] [.ite c [.ret none] []] sc st st :=
  ⟨6, rfl⟩

/-- Nested: `while (c) { while (d) break; }`, neither condition with an effect.
The inner loop keeps its own flag, declared inside the outer body; the outer
loop has no exit and no flag. -/
theorem nestedBreak (rs : Option (List String)) (c d : RawExpr) (hc : c.hasIncDec = false)
    (hd : d.hasIncDec = false) (sc : ElabScope) (st : Checker.Snapshot) :
    LowersTo rs [.whileLoop {} c [.whileLoop {} d [.brk]]]
      [.loop {} c [.block [.declBool (flag "brk" st 0) false,
        .loop {} (.binop .and (nb (flag "brk" st 0)) d) [.setBool (flag "brk" st 0) true]]]]
      sc st (taken st 1) := by
  lower_run 12 [list_cons, stmt_while _ _ _ _ _ (whileGuard_false _ _ _ hc),
    list_cons, stmt_while _ _ _ _ _ (whileGuard_false _ _ _ hd)]

/-- Nested: `while (c) { while (d) return; }`: one return flag shared by the
nest, declared and tested once, around the outermost loop. -/
theorem nestedReturn (slots : List String) (c d : RawExpr) (hc : c.hasIncDec = false)
    (hd : d.hasIncDec = false) (sc : ElabScope) (st : Checker.Snapshot) :
    LowersTo (some slots) [.whileLoop {} c [.whileLoop {} d [.ret none]]]
      [.block [.declBool (flag "ret" st 0) false,
        .loop {} (.binop .and (nb (flag "ret" st 0)) c)
          [.loop {} (.binop .and (nb (flag "ret" st 0)) d)
            [.block [.setBool (flag "ret" st 0) true]]],
        .ite (.name (flag "ret" st 0)) [.ret none] []]]
      sc st (taken st 1) := by
  lower_run 12 [list_cons, stmt_while _ _ _ _ _ (whileGuard_false _ _ _ hc),
    list_cons, stmt_while _ _ _ _ _ (whileGuard_false _ _ _ hd)]

/-! ### One statement for the family inputs -/

/-- The raw inputs covered: `FamilyInput rs input st output after` lists an
input shape with its return slots and incoming state, and the output and
outgoing state the lowering rules give it. -/
inductive FamilyInput : Option (List String) → List RawStmt → Checker.Snapshot →
    List RawStmt → Checker.Snapshot → Prop
  | whileBreak (rs c st) (hc : c.hasIncDec = true) :
    FamilyInput rs [.whileLoop {} c [.brk]] st
      [.block [.declBool (flag "brk" st 0) false,
        .loop {} (.binop .and (nb (flag "brk" st 0)) (.bool true))
          [.ite (.unop .not c) [.setBool (flag "brk" st 0) true] [],
           .ite (nb (flag "brk" st 0)) [.block [.setBool (flag "brk" st 0) true]] []]]]
      (taken st 1)
  | whileBreakPure (rs c st) (hc : c.hasIncDec = false) :
    FamilyInput rs [.whileLoop {} c [.brk]] st
      [.block [.declBool (flag "brk" st 0) false,
        .loop {} (.binop .and (nb (flag "brk" st 0)) c) [.setBool (flag "brk" st 0) true]]]
      (taken st 1)
  | forBreak (rs init st) :
    FamilyInput rs [.forLoop {} init none [] [.brk]] st
      [.block (init ++ [.declBool (flag "brk" st 0) false] ++
        [.loop {} (.binop .and (nb (flag "brk" st 0)) (.bool true))
          [.setBool (flag "brk" st 0) true]])]
      (taken st 1)
  | forBreakUpdate (rs init u us st) :
    FamilyInput rs [.forLoop {} init none (u :: us) [.brk]] st
      [.block (init ++ [.declBool (flag "brk" st 0) false] ++
        [.loop {} (.binop .and (nb (flag "brk" st 0)) (.bool true))
          [.setBool (flag "brk" st 0) true, .ite (nb (flag "brk" st 0)) (u :: us) []]])]
      (taken st 1)
  | whileContinue (rs c l r tail st) (hc : c.hasIncDec = true) :
    FamilyInput rs [.whileLoop {} c (.assign l r :: .cont :: tail)] st
      [.block [.declBool (flag "brk" st 0) false,
        .loop {} (.binop .and (nb (flag "brk" st 0)) (.bool true))
          [.declBool (flag "cnt" st 1) false,
           .ite (.unop .not c) [.setBool (flag "brk" st 0) true] [],
           .ite (nb (flag "brk" st 0))
             [.block [.assign l r, .setBool (flag "cnt" st 1) true]] []]]]
      (taken st 2)
  | doBreak (rs c l r st) :
    FamilyInput rs [.doWhile {} [.assign l r, .brk] c] st
      [.block [.declBool (flag "first" st 1) true, .declBool (flag "brk" st 0) false,
        .loop {} (.binop .and (nb (flag "brk" st 0)) (.binop .or (.name (flag "first" st 1)) c))
          [.setBool (flag "first" st 1) false, .assign l r, .setBool (flag "brk" st 0) true]]]
      (taken st 2)
  | whileReset (rs c l r st) (hc : c.hasIncDec = true) :
    FamilyInput rs [.whileLoop {} c [.assign l r]] st
      [.block [.declBool (flag "brk" st 0) false,
        .loop {} (.binop .and (nb (flag "brk" st 0)) (.bool true))
          [.ite (.unop .not c) [.setBool (flag "brk" st 0) true] [],
           .ite (nb (flag "brk" st 0)) [.block [.assign l r]] []]]]
      (taken st 1)
  | doContinue (rs c l r tail st) :
    FamilyInput rs [.doWhile {} (.assign l r :: .cont :: tail) c] st
      [.block [.declBool (flag "first" st 1) true,
        .loop {} (.binop .or (.name (flag "first" st 1)) c)
          [.setBool (flag "first" st 1) false, .declBool (flag "cnt" st 0) false,
           .assign l r, .setBool (flag "cnt" st 0) true]]]
      (taken st 2)
  | whileReturn (slots c st) (hc : c.hasIncDec = true) :
    FamilyInput (some slots) [.whileLoop {} c [.ret none]] st [whileReturnOut c st] (taken st 2)
  | doReturn (slots c l r st) :
    FamilyInput (some slots) [.doWhile {} [.assign l r, .ret none] c] st
      [.block [.declBool (flag "first" st 1) true, .declBool (flag "ret" st 0) false,
        .loop {} (.binop .and (nb (flag "ret" st 0)) (.binop .or (.name (flag "first" st 1)) c))
          [.setBool (flag "first" st 1) false, .assign l r,
           .block [.setBool (flag "ret" st 0) true]],
        .ite (.name (flag "ret" st 0)) [.ret none] []]]
      (taken st 2)
  | whileReturnThen (slots c l r st) (hc : c.hasIncDec = true) :
    FamilyInput (some slots) [.whileLoop {} c [.ret none], .assign l r] st
      [whileReturnOut c st, .assign l r] (taken st 2)
  | returnFlag (rs c st) :
    FamilyInput rs [.ite c [.ret none] []] st [.ite c [.ret none] []] st
  | nestedBreak (rs c d st) (hc : c.hasIncDec = false) (hd : d.hasIncDec = false) :
    FamilyInput rs [.whileLoop {} c [.whileLoop {} d [.brk]]] st
      [.loop {} c [.block [.declBool (flag "brk" st 0) false,
        .loop {} (.binop .and (nb (flag "brk" st 0)) d) [.setBool (flag "brk" st 0) true]]]]
      (taken st 1)
  | nestedReturn (slots c d st) (hc : c.hasIncDec = false) (hd : d.hasIncDec = false) :
    FamilyInput (some slots) [.whileLoop {} c [.whileLoop {} d [.ret none]]] st
      [.block [.declBool (flag "ret" st 0) false,
        .loop {} (.binop .and (nb (flag "ret" st 0)) c)
          [.loop {} (.binop .and (nb (flag "ret" st 0)) d)
            [.block [.setBool (flag "ret" st 0) true]]],
        .ite (.name (flag "ret" st 0)) [.ret none] []]]
      (taken st 1)

/-- Every listed input is in the relation, with its listed output, at every scope. -/
theorem FamilyInput.lowers {rs : Option (List String)} {input output : List RawStmt}
    {st after : Checker.Snapshot} (h : FamilyInput rs input st output after) (sc : ElabScope) :
    LowersTo rs input output sc st after := by
  cases h with
  | whileBreak _ c _ hc => exact Coverage.whileBreak rs c hc sc st
  | whileBreakPure _ c _ hc => exact Coverage.whileBreakPure rs c hc sc st
  | forBreak _ init _ => exact Coverage.forBreak rs init sc st
  | forBreakUpdate _ init u us _ => exact Coverage.forBreakUpdate rs init u us sc st
  | whileContinue _ c l r tail _ hc => exact Coverage.whileContinue rs c l r tail hc sc st
  | doBreak _ c l r _ => exact Coverage.doBreak rs c l r sc st
  | whileReset _ c l r _ hc => exact Coverage.whileReset rs c l r hc sc st
  | doContinue _ c l r tail _ => exact Coverage.doContinue rs c l r tail sc st
  | whileReturn slots c _ hc => exact Coverage.whileReturn slots c hc sc st
  | doReturn slots c l r _ => exact Coverage.doReturn slots c l r sc st
  | whileReturnThen slots c l r _ hc => exact Coverage.whileReturnThen slots c l r hc sc st
  | returnFlag _ c _ => exact Coverage.returnFlag rs c sc st
  | nestedBreak _ c d _ hc hd => exact Coverage.nestedBreak rs c d hc hd sc st
  | nestedReturn slots c d _ hc hd => exact Coverage.nestedReturn slots c d hc hd sc st

/-- **Raw coverage.** On a family input, the outputs `LowersTo` admits are
exactly the listed one, with the listed outgoing state: at every scope, and
whatever the depth of the derivation. -/
theorem covered {rs : Option (List String)} {input output : List RawStmt}
    {st after : Checker.Snapshot} (h : FamilyInput rs input st output after) (sc : ElabScope)
    (output' : List RawStmt) (after' : Checker.Snapshot) :
    LowersTo rs input output' sc st after' ↔ output' = output ∧ after' = after :=
  LowersTo.iff_of (h.lowers sc)

/-! ### The e1 sample inputs are instances

Each raw input the e1 lane ran through the actual producer
(`Checker.RawProbe.input`, `Loops.Capture`) is an instance of a template above,
so its `LowersTo` output is known at every scope, state and spelling of fresh
names, not only at the probed one. -/

open Loops in
theorem sample_inputs (sc : ElabScope) (st : Checker.Snapshot) (slots : List String) :
    (∃ out, LowersTo none Checker.RawProbe.input out sc st (taken st 1)) ∧
    (∃ out, LowersTo none Capture.forBreakInput out sc st (taken st 1)) ∧
    (∃ out, LowersTo none Capture.forBreakUpdateInput out sc st (taken st 1)) ∧
    (∃ out, LowersTo none Capture.whileContinueInput out sc st (taken st 2)) ∧
    (∃ out, LowersTo none Capture.whileContinueTailInput out sc st (taken st 2)) ∧
    (∃ out, LowersTo none Capture.doBreakInput out sc st (taken st 2)) ∧
    (∃ out, LowersTo none Capture.whileResetInput out sc st (taken st 1)) ∧
    (∃ out, LowersTo none Capture.doContinueInput out sc st (taken st 2)) ∧
    (∃ out, LowersTo (some slots) Capture.whileReturnBody out sc st (taken st 2)) ∧
    (∃ out, LowersTo (some slots) Capture.doReturnBody out sc st (taken st 2)) ∧
    (∃ out, LowersTo (some slots) Capture.whileReturnThenBody out sc st (taken st 2)) ∧
    (∃ out, LowersTo (some slots) Capture.returnFlagBody out sc st st) :=
  ⟨⟨_, whileBreak none _ (hasIncDec_assign _ _) sc st⟩,
   ⟨_, forBreak none _ sc st⟩,
   ⟨_, forBreakUpdate none _ _ _ sc st⟩,
   ⟨_, whileContinue none _ _ _ [] (hasIncDec_assign _ _) sc st⟩,
   ⟨_, whileContinue none _ _ _ [_] (hasIncDec_assign _ _) sc st⟩,
   ⟨_, doBreak none _ _ _ sc st⟩,
   ⟨_, whileReset none _ _ _ (hasIncDec_assign _ _) sc st⟩,
   ⟨_, doContinue none _ _ _ [] sc st⟩,
   ⟨_, whileReturn slots _ (hasIncDec_assign _ _) sc st⟩,
   ⟨_, doReturn slots _ _ _ sc st⟩,
   ⟨_, whileReturnThen slots _ _ _ (hasIncDec_assign _ _) sc st⟩,
   ⟨_, returnFlag (some slots) _ sc st⟩⟩

end Names

/-- The actual quoted producer output of the e1 while/break probe is the
relation's output at the probed state (and so its only one, `LowersTo.unique`). -/
theorem rawProbe_actual :
    LowersTo none Checker.RawProbe.input Checker.RawProbe.actual.raw Checker.RawProbe.scope
      ⟨(Checker.RawProbe.inputLocals, 1), {}⟩
      ⟨(Checker.RawProbe.actual.locals, Checker.RawProbe.actual.counter),
        Checker.RawProbe.actual.memo⟩ :=
  whileBreak none (.assign (.name "i") (.name "a")) (hasIncDec_assign _ _)
    Checker.RawProbe.scope ⟨(Checker.RawProbe.inputLocals, 1), {}⟩

end Solidity.Correctness.Lowering.Total.Coverage
