import Solidity.Correctness.Lowering.Total.Relation

/-!
# Raw coverage of the loop family inputs by `LowersTo` (e2e-loops-coverage)

About the frozen relation `Total.LowersTo` alone (no production totality):

* `LowersTo.unique`: for fixed return slots, scope, fresh-name spelling, input
  and incoming state, the relation has at most one output and outgoing state.
* `covered`: on each `Template` input the relation holds of exactly the listed
  output and outgoing state, at every scope, state and spelling of fresh names.
  The templates are the raw inputs of the six `Loops.Shape` loops and of the
  four `Loops.RetShape` bodies (for these, only the `lowerLoops` call inside
  `calleeBody`, on an input already renamed, before `lowerReturns`), and three
  inputs outside the e1 families: `whileBreakPure`, `nestedBreak`,
  `nestedReturn`. Every template has the empty loop specification. "With an
  effect" is the lowering's own test `RawExpr.hasIncDec`; each constructor
  states which conditions, bodies and slots it takes.
* `Coverage.Checks`: the e1 sample inputs are template instances, and the
  quoted actual output of the while/break probe is the relation's only output.

Not provable from this interface: that these outputs lie in the loop families
(`Loops.NormalFamilyCorrect`, `Loops.ReturnFamilyCorrect`). Those speak of
intrinsic programs, reached only through `elabStmtsP`, which is `partial`:
`Total.SuccessfulElaboration` constrains nothing in the kernel. Membership also
needs operand typing and name safety, not assumed here; and `LowersTo` holds
outside the families' raw image (the three templates above, `[]`, general
bodies). `Solidity.Goals.lowerLoopsCorrect` stays unstated.
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
    | with_reducible exact Le.refl _ | with_reducible exact h | with_reducible exact hi
    | with_reducible exact hP _ _ | with_reducible apply Le.bind | (intro _) | split

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

theorem loopStep_rewrite (L : ListCalls) (P : StmtCalls) (rs : Option (List String))
    (s : RawStmt) (hg : loopGuard s = true) :
    LowerKernel.loopStep L P rs s = P rs (loopRewrite s) := by
  rw [← factoredStep_eq]
  unfold factoredStep loopRewrite
  generalize loopParts s = parts
  rcases parts with ⟨spec, c, init, upd, body, isDo⟩
  simp [hg]

theorem stmt_while_effect (n : Nat) (rs : Option (List String)) (c : RawExpr)
    (b : List RawStmt) (hc : c.hasIncDec = true) :
    (derive (n + 3)).stmt rs (.whileLoop {} c b) =
      loopFinish {} (.bool true) [] [] false
        ((derive n).list rs [.ite (.unop .not c) [.brk] [], .block b]) := by
  have hf : loopGuard (.whileLoop {} (.bool true) [.ite (.unop .not c) [.brk] [], .block b]) =
      false := whileGuard_false _ _ _ (by simp [RawExpr.hasIncDec, RawExpr.any])
  rw [derive_stmt (n + 2), derive_loop (n + 1)]
  simp only [LowerKernel.stmtStep, loopStep_rewrite _ _ _ _ (show loopGuard (.whileLoop {} c b) = true by simp [loopGuard, loopParts, hc])]
  simp only [loopRewrite, loopParts, ↓reduceIte, bind_pure]
  rw [derive_loop n, loopStep_finish _ _ _ _ hf]
  rfl

theorem lowersTo_of_run {depth : Nat} {rs : Option (List String)} {input output : List RawStmt}
    {scope : ElabScope} {before after : Checker.Snapshot} {x : LowerM (List RawStmt × List Abrupt)}
    {ab : List Abrupt} {fl : LoopFlags} (eq : (derive depth).list rs input = x)
    (run : x {} scope before.locals before.memo =
      .ok ((((output, ab), fl), after.locals), after.memo)) :
    LowersTo rs input output scope before after := by
  refine ⟨depth, ?_⟩
  show runAt depth rs input scope before = _
  rw [runAt_eq, eq, run]

/-- For fixed return slots, scope and spelling, two derivations of any depths
give the same output and the same outgoing state. -/
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

/-! ### Raw outputs of the family inputs -/

/-- Spelling of the `j`-th fresh name after the incoming counter; `taken`: `k` names used. -/
def flag (base : String) (st : Checker.Snapshot) (j : Nat) : String :=
  toString (Var.fresh base (st.locals.2 + j))

def nb (x : String) : RawExpr := .unop .not (.name x)

def taken (st : Checker.Snapshot) (k : Nat) : Checker.Snapshot :=
  ⟨(st.locals.1, st.locals.2 + k), st.memo⟩

omit [FreshNames] in
theorem hasIncDec_assign (l r : RawExpr) : (RawExpr.assign l r).hasIncDec = true := by
  simp [RawExpr.hasIncDec, RawExpr.any]

local macro "lower_run " d:num " [" rules:Lean.Parser.Tactic.rwRule,* "]" : tactic => `(tactic|
  (refine lowersTo_of_run (depth := $d) (x := ?x) (ab := ?ab) (fl := ?fl) ?eq ?run
   case eq => rw [$rules,*]
   case run => rfl))

/-- The lowered `while (c) return;`, `c` with an effect, before `lowerReturns`. -/
def whileReturnOut (c : RawExpr) (st : Checker.Snapshot) : RawStmt :=
  .block [.declBool (flag "brk" st 0) false, .declBool (flag "ret" st 1) false,
    .loop {} (.binop .and (nb (flag "brk" st 0))
        (.binop .and (nb (flag "ret" st 1)) (.bool true)))
      [.ite (.unop .not c) [.setBool (flag "brk" st 0) true] [],
       .ite (nb (flag "brk" st 0)) [.block [.block [.setBool (flag "ret" st 1) true]]] []],
    .ite (.name (flag "ret" st 1)) [.ret none] []]

/-- An input shape with its return slots and incoming state, and the output
and outgoing state the rules give it. A tail after `continue` is dropped unread. -/
inductive Template : Option (List String) → List RawStmt → Checker.Snapshot →
    List RawStmt → Checker.Snapshot → Prop
  | whileBreak (rs c st) (hc : c.hasIncDec = true) :
    Template rs [.whileLoop {} c [.brk]] st
      [.block [.declBool (flag "brk" st 0) false,
        .loop {} (.binop .and (nb (flag "brk" st 0)) (.bool true))
          [.ite (.unop .not c) [.setBool (flag "brk" st 0) true] [],
           .ite (nb (flag "brk" st 0)) [.block [.setBool (flag "brk" st 0) true]] []]]]
      (taken st 1)
  | whileBreakPure (rs c st) (hc : c.hasIncDec = false) :
    Template rs [.whileLoop {} c [.brk]] st
      [.block [.declBool (flag "brk" st 0) false,
        .loop {} (.binop .and (nb (flag "brk" st 0)) c) [.setBool (flag "brk" st 0) true]]]
      (taken st 1)
  | forBreak (rs init st) :
    Template rs [.forLoop {} init none [] [.brk]] st
      [.block (init ++ [.declBool (flag "brk" st 0) false] ++
        [.loop {} (.binop .and (nb (flag "brk" st 0)) (.bool true))
          [.setBool (flag "brk" st 0) true]])]
      (taken st 1)
  | forBreakUpdate (rs init u us st) :
    Template rs [.forLoop {} init none (u :: us) [.brk]] st
      [.block (init ++ [.declBool (flag "brk" st 0) false] ++
        [.loop {} (.binop .and (nb (flag "brk" st 0)) (.bool true))
          [.setBool (flag "brk" st 0) true, .ite (nb (flag "brk" st 0)) (u :: us) []]])]
      (taken st 1)
  | whileContinue (rs c l r tail st) (hc : c.hasIncDec = true) :
    Template rs [.whileLoop {} c (.assign l r :: .cont :: tail)] st
      [.block [.declBool (flag "brk" st 0) false,
        .loop {} (.binop .and (nb (flag "brk" st 0)) (.bool true))
          [.declBool (flag "cnt" st 1) false,
           .ite (.unop .not c) [.setBool (flag "brk" st 0) true] [],
           .ite (nb (flag "brk" st 0))
             [.block [.assign l r, .setBool (flag "cnt" st 1) true]] []]]]
      (taken st 2)
  | doBreak (rs c l r st) :
    Template rs [.doWhile {} [.assign l r, .brk] c] st
      [.block [.declBool (flag "first" st 1) true, .declBool (flag "brk" st 0) false,
        .loop {} (.binop .and (nb (flag "brk" st 0)) (.binop .or (.name (flag "first" st 1)) c))
          [.setBool (flag "first" st 1) false, .assign l r, .setBool (flag "brk" st 0) true]]]
      (taken st 2)
  | whileReset (rs c l r st) (hc : c.hasIncDec = true) :
    Template rs [.whileLoop {} c [.assign l r]] st
      [.block [.declBool (flag "brk" st 0) false,
        .loop {} (.binop .and (nb (flag "brk" st 0)) (.bool true))
          [.ite (.unop .not c) [.setBool (flag "brk" st 0) true] [],
           .ite (nb (flag "brk" st 0)) [.block [.assign l r]] []]]]
      (taken st 1)
  | doContinue (rs c l r tail st) :
    Template rs [.doWhile {} (.assign l r :: .cont :: tail) c] st
      [.block [.declBool (flag "first" st 1) true,
        .loop {} (.binop .or (.name (flag "first" st 1)) c)
          [.setBool (flag "first" st 1) false, .declBool (flag "cnt" st 0) false,
           .assign l r, .setBool (flag "cnt" st 0) true]]]
      (taken st 2)
  | whileReturn (slots c st) (hc : c.hasIncDec = true) :
    Template (some slots) [.whileLoop {} c [.ret none]] st [whileReturnOut c st] (taken st 2)
  | doReturn (slots c l r st) :
    Template (some slots) [.doWhile {} [.assign l r, .ret none] c] st
      [.block [.declBool (flag "first" st 1) true, .declBool (flag "ret" st 0) false,
        .loop {} (.binop .and (nb (flag "ret" st 0)) (.binop .or (.name (flag "first" st 1)) c))
          [.setBool (flag "first" st 1) false, .assign l r,
           .block [.setBool (flag "ret" st 0) true]],
        .ite (.name (flag "ret" st 0)) [.ret none] []]]
      (taken st 2)
  | whileReturnThen (slots c l r st) (hc : c.hasIncDec = true) :
    Template (some slots) [.whileLoop {} c [.ret none], .assign l r] st
      [whileReturnOut c st, .assign l r] (taken st 2)
  | returnFlag (rs c st) :
    Template rs [.ite c [.ret none] []] st [.ite c [.ret none] []] st
  | nestedBreak (rs c d st) (hc : c.hasIncDec = false) (hd : d.hasIncDec = false) :
    Template rs [.whileLoop {} c [.whileLoop {} d [.brk]]] st
      [.loop {} c [.block [.declBool (flag "brk" st 0) false,
        .loop {} (.binop .and (nb (flag "brk" st 0)) d) [.setBool (flag "brk" st 0) true]]]]
      (taken st 1)
  | nestedReturn (slots c d st) (hc : c.hasIncDec = false) (hd : d.hasIncDec = false) :
    Template (some slots) [.whileLoop {} c [.whileLoop {} d [.ret none]]] st
      [.block [.declBool (flag "ret" st 0) false,
        .loop {} (.binop .and (nb (flag "ret" st 0)) c)
          [.loop {} (.binop .and (nb (flag "ret" st 0)) d)
            [.block [.setBool (flag "ret" st 0) true]]],
        .ite (.name (flag "ret" st 0)) [.ret none] []]]
      (taken st 1)

/-- Every listed input is in the relation, with its listed output, at every scope. -/
theorem Template.lowers {rs : Option (List String)} {input output : List RawStmt}
    {st after : Checker.Snapshot} (h : Template rs input st output after) (sc : ElabScope) :
    LowersTo rs input output sc st after := by
  cases h with
  | forBreak _ init _ | forBreakUpdate _ init _ _ _ =>
    cases init <;> lower_run 12 [list_cons, stmt_for]
  | whileBreak _ c _ hc | whileContinue _ c _ _ _ _ hc | whileReset _ c _ _ _ hc
  | whileReturn _ c _ hc | whileReturnThen _ c _ _ _ hc =>
    lower_run 12 [list_cons, stmt_while_effect _ _ _ _ hc]
  | whileBreakPure _ c _ hc =>
    lower_run 12 [list_cons, stmt_while _ _ _ _ _ (whileGuard_false _ _ _ hc)]
  | doBreak | doContinue | doReturn => lower_run 12 [list_cons, stmt_do]
  | returnFlag => exact ⟨6, rfl⟩
  | nestedBreak _ c d _ hc hd | nestedReturn _ c d _ hc hd =>
    lower_run 12 [list_cons, stmt_while _ _ _ _ _ (whileGuard_false _ _ _ hc),
      list_cons, stmt_while _ _ _ _ _ (whileGuard_false _ _ _ hd)]

/-- **Raw coverage.** On a template input `LowersTo` admits exactly the listed
output and outgoing state, at every scope and derivation depth. -/
theorem covered {rs : Option (List String)} {input output : List RawStmt}
    {st after : Checker.Snapshot} (h : Template rs input st output after) (sc : ElabScope)
    (output' : List RawStmt) (after' : Checker.Snapshot) :
    LowersTo rs input output' sc st after' ↔ output' = output ∧ after' = after :=
  ⟨fun k => ⟨(LowersTo.unique (h.lowers sc) k).1.symm, (LowersTo.unique (h.lowers sc) k).2.symm⟩,
    fun e => e.1 ▸ e.2 ▸ h.lowers sc⟩

end Names

end Solidity.Correctness.Lowering.Total.Coverage
