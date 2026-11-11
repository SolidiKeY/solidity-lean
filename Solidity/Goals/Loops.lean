import Solidity.Tools.Goal
import Solidity.Syntax.Elab.Lower

/-! Finish-line component 3: `Solidity.Correctness.Lowering.lowerLoops_correct`
(owner: e1-loops), and the pa-lowering study target that reuses its statement. -/

namespace Solidity.Goals

open Solidity.Goal

@[goal Solidity.Correctness.Lowering.lowerLoops_correct "e1-loops"]
def lowerLoopsCorrect : Prop := Unstated

@[goal Solidity.Correctness.Lowering.lowerLoops_correct "pa-lowering" ← lowerLoopsCorrect]
def loweringStudyTarget : Prop := lowerLoopsCorrect

/-! ### The lowering kernel, total (e2a-lower-total)

`lowerLoops` (`Syntax/Elab/Lower.lean`) runs the mutually recursive `partial`
family `lowerList`/`lowerStmt`/`lowerLoop` in `LowerM = StateT LoopFlags ElabM`.
Being `partial`, the three are opaque constants: the kernel knows nothing of
them.  The contract below holds of them only once they are total definitions
with their present behaviour:

* `LoweringKernelFix`: they satisfy their own defining equations, written out
  verbatim below as one step of the recursion (`loweringKernelList`,
  `loweringKernelStmt`, `loweringKernelLoop`), the recursive calls abstracted.
  Equality is of whole `LowerM` computations, so it fixes the returned syntax,
  the abrupt kinds, every error string, the loop flags threaded and restored,
  the reader scope read, the locals and fresh counter (`freshCapture`) and the
  callee memo, for every argument and every initial state.
* `LoweringKernelContractive`: the step is well founded, by a `Nat` measure on
  the syntax: at an argument of measure `n` it reads the recursive calls only
  at arguments of measure below `n`.  This is the finite-termination
  obligation: every call tree is at most as deep as the measure of its root,
  including the synthetic rewrite of an effectful `while` condition, whose
  rewritten loop is larger than the original.  With `LoweringKernelFix` it
  makes the production triple the step's only fixpoint.
* `LoweringKernelHelpers`: the helpers in `Lower.lean` that the family and
  `lowerLoops` reach keep their present behaviour.  The helpers outside it
  (`freshCapture`, `ElabM.lift`, `RawExpr.hasIncDec`, `RawExpr.mentions`, and
  `RawStmt.anyDeep`, which is `partial` and only gates a refusal) are used as
  they are; none calls back into the family.

The proof, `Solidity.lowerKernel_total`, belongs in `Lower.lean`, which this
module imports and which imports no goal module: it states its type again,
with its own copies of these definitions, definitionally equal to
`loweringKernelTotal` (the roadmap checks the binding by `isDefEq`).  Once the
family is total, `LoweringKernelFix` is its unfolding equations, the measures
count the syntax with extra weight on a `while` loop whose condition has an
effect, and `LoweringKernelHelpers` holds by `rfl`. -/

section Kernel

variable [FreshNames]

/-- One step of `lowerList`, its calls of `lowerList` and `lowerStmt` given. -/
def loweringKernelList
    (L : Option (List String) → List RawStmt → LowerM (List RawStmt × List Abrupt))
    (S : Option (List String) → RawStmt → LowerM (RawStmt × List Abrupt))
    (rs : Option (List String)) : List RawStmt → LowerM (List RawStmt × List Abrupt)
  | [] => pure ([], [])
  | s :: ss => do
    let (s', ab) ← S rs s
    if ab.isEmpty then
      let (ss', ab') ← L rs ss
      pure (s' :: ss', ab')
    else if s.isJump then pure ([s'], ab)
    else
      let (ss', ab') ← L rs ss
      if ss'.isEmpty then pure ([s'], ab)
      else pure ([s', .ite (← notAny ab) ss' []], Abrupt.union ab ab')

/-- One step of `lowerStmt`, its calls of `lowerList` and `lowerLoop` given. -/
def loweringKernelStmt
    (L : Option (List String) → List RawStmt → LowerM (List RawStmt × List Abrupt))
    (P : Option (List String) → RawStmt → LowerM (RawStmt × List Abrupt))
    (rs : Option (List String)) (s : RawStmt) : LowerM (RawStmt × List Abrupt) := do
  if s matches .whileLoop .. | .forLoop .. | .doWhile .. | .loop .. then return ← P rs s
  let lowerB (b : List RawStmt) : LowerM (List RawStmt) := do pure (← L rs b).1
  unless (← get).inLoop do
    return ← match s with
      | .block b => do pure (.block (← lowerB b), [])
      | .unchecked b => do pure (.unchecked (← lowerB b), [])
      | .checked o b => do pure (.checked o (← lowerB b), [])
      | .ite c t e => do pure (.ite c (← lowerB t) (← lowerB e), [])
      | .tryCall e g as rets ok err code pnc other => do
        pure (.tryCall e g as rets (← lowerB ok) (← lowerB err) code (← lowerB pnc) (← lowerB other),
          [])
      | .brk => throw "`break` outside a loop"
      | .cont => throw "`continue` outside a loop"
      | s => pure (s, [])
  match s with
  | .brk => pure (.setBool (← LoopFlags.flag .brk) true, [.brk])
  | .cont => pure (.setBool (← LoopFlags.flag .cnt) true, [.cnt])
  | .ret e =>
    let some rs := rs | throw "`return` outside a function's body"
    let pre ← match e with
      | none => pure []
      | some e => ElabM.lift (lowerReturn rs e)
    pure (.block (pre ++ [.setBool (← LoopFlags.flag .ret) true]), [.ret])
  | .block b => do
    let (b', ab) ← L rs b
    pure (.block b', ab)
  | .unchecked b => do
    let (b', ab) ← L rs b
    pure (.unchecked b', ab)
  | .checked o b => do
    let (b', ab) ← L rs b
    pure (.checked o b', ab)
  | .ite c t e => do
    let (t', a) ← L rs t
    let (e', b) ← L rs e
    pure (.ite c t' e', Abrupt.union a b)
  | .tryCall e g as rets ok err code pnc other => do
    if s.hasJump then throw "`break`, `continue` or `return` inside `try` inside a loop"
    LowerM.outside do
      pure (.tryCall e g as rets (← lowerB ok) (← lowerB err) code (← lowerB pnc) (← lowerB other),
        [])
  | s => pure (s, [])

/-- One step of `lowerLoop`, its calls of `lowerList` and `lowerLoop` given; the
second is the synthetic rewrite of an effectful `while` condition. -/
def loweringKernelLoop
    (L : Option (List String) → List RawStmt → LowerM (List RawStmt × List Abrupt))
    (P : Option (List String) → RawStmt → LowerM (RawStmt × List Abrupt))
    (rs : Option (List String)) (s : RawStmt) : LowerM (RawStmt × List Abrupt) := do
  let (spec, c, init, upd, body, isDo) := match s with
    | .forLoop a i c u b => (a, c.getD (.bool true), i, u, b, false)
    | .doWhile a b c => (a, c, [], [], b, true)
    | .whileLoop a c b | .loop a c b => (a, c, [], [], b, false)
    | _ => ({}, .bool true, [], [], [], false)
  if (s matches .whileLoop ..) && c.hasIncDec && spec.inv.isEmpty &&
      spec.qinv.isEmpty && spec.dec.isNone && spec.unwind.isNone then
    return ← P rs (.whileLoop spec (.bool true)
      [.ite (.unop .not c) [.brk] [], .block body])
  let outer ← get
  let outermost := !outer.inLoop
  set ({ ret := if outermost then none else outer.ret, inLoop := true } : LoopFlags)
  let (body', ab) ← L rs body
  let exits := ab.filter (· != .cnt)
  let mut before : List RawStmt := init
  let mut iter : List RawStmt := []
  let mut cond := c
  let mut heads : List String := []
  if isDo then
    let first := toString (← freshCapture "first")
    before := before ++ [.declBool first true]
    iter := [.setBool first false]
    cond := .binop .or (.name first) cond
    heads := heads ++ [first]
  if let some x := (← get).cnt then iter := iter ++ [.declBool x false]
  iter := iter ++ body'
  unless upd.isEmpty do
    if exits.isEmpty then iter := iter ++ upd
    else iter := iter ++ [.ite (← notAny exits) upd []]
  unless exits.isEmpty do cond ← notAny exits (some cond)
  let fl ← get
  if exits.contains .brk then heads := heads ++ fl.brk.toList
  if exits.contains .ret then heads := heads ++ fl.ret.toList
  if let some x := fl.brk then before := before ++ [.declBool x false]
  let returns := exits.contains .ret
  let retX := fl.ret.getD ""
  if returns && outermost then before := before ++ [.declBool retX false]
  set { outer with ret := if outermost then outer.ret else fl.ret }
  let spec := if spec.inv.isEmpty && spec.qinv.isEmpty then spec else
    { spec with inv := spec.inv ++ heads.map fun f => .binop .or (.name f) (.unop .not (.name f)),
                brk := spec.brk || exits.contains .brk }
  let w := RawStmt.loop spec cond iter
  let ab' := if returns then [Abrupt.ret] else []
  if before.isEmpty && !(returns && outermost) then return (w, ab')
  if returns && outermost then
    return (.block (before ++ [w, .ite (.name retX) [.ret none] []]), [])
  pure (.block (before ++ [w]), ab')

/-- `L`, `S`, `P` satisfy the lowering kernel's defining equations. -/
def LoweringKernelFix
    (L : Option (List String) → List RawStmt → LowerM (List RawStmt × List Abrupt))
    (S P : Option (List String) → RawStmt → LowerM (RawStmt × List Abrupt)) : Prop :=
  (∀ rs ss, L rs ss = loweringKernelList L S rs ss) ∧
  (∀ rs s, S rs s = loweringKernelStmt L P rs s) ∧
  (∀ rs s, P rs s = loweringKernelLoop L P rs s)

/-- The kernel's step reads the recursive calls only below the measure of its
argument: two sets of calls that agree below `n` give the same step at measure
`n`.  Lists are measured by `μL`, statements given to `lowerStmt` by `μS` and to
`lowerLoop` by `μP`. -/
def LoweringKernelContractive (μL : List RawStmt → Nat) (μS μP : RawStmt → Nat) : Prop :=
  ∀ (n : Nat)
    (L L' : Option (List String) → List RawStmt → LowerM (List RawStmt × List Abrupt))
    (S S' P P' : Option (List String) → RawStmt → LowerM (RawStmt × List Abrupt)),
    (∀ rs ss, μL ss < n → L rs ss = L' rs ss) →
    (∀ rs s, μS s < n → S rs s = S' rs s) →
    (∀ rs s, μP s < n → P rs s = P' rs s) →
    (∀ rs ss, μL ss = n → loweringKernelList L S rs ss = loweringKernelList L' S' rs ss) ∧
    (∀ rs s, μS s = n → loweringKernelStmt L P rs s = loweringKernelStmt L' P' rs s) ∧
    (∀ rs s, μP s = n → loweringKernelLoop L P rs s = loweringKernelLoop L' P' rs s)

/-- The helpers in `Lower.lean` that `lowerLoops` reaches, as they are. -/
def LoweringKernelHelpers : Prop :=
  (∀ rs ss, lowerLoops rs ss = do pure (← (lowerList rs ss).run' {}).1) ∧
  (∀ k, LoopFlags.flag k = do
    let fl ← get
    let cur := match k with
      | .brk => fl.brk
      | .cnt => fl.cnt
      | .ret => fl.ret
    if let some x := cur then return x
    let x := toString (← freshCapture (match k with | .brk => "brk" | .cnt => "cnt" | .ret => "ret"))
    match k with
    | .brk => set { fl with brk := some x }
    | .cnt => set { fl with cnt := some x }
    | .ret => set { fl with ret := some x }
    pure x) ∧
  (∀ ks c, notAny ks c = do
    let gs ← ks.mapM fun k => do pure (RawExpr.unop .not (.name (← LoopFlags.flag k)))
    match c, gs.reverse with
    | some c, _ => pure (RawExpr.andAll gs c)
    | none, g :: rest => pure (RawExpr.andAll rest.reverse g)
    | none, [] => pure (.bool true)) ∧
  (∀ {α : Type} (x : LowerM α), LowerM.outside x = do
    let fl ← get
    set ({} : LoopFlags)
    let r ← x
    set fl
    pure r) ∧
  (∀ rs e, lowerReturn rs e =
    match rs, e with
    | [], _ => throw "`return` of a value from a function that returns none"
    | [_], .tuple es => throw s!"`return` of {es.length} values from a function that returns one"
    | [n], e => pure [.assign (.name n) e]
    | rs, .tuple es =>
      if es.length != rs.length then
        throw s!"`return` of {es.length} values from a function that returns {rs.length}"
      else if es.any fun e => rs.any e.mentions then
        pure [.tupleAssign (rs.map fun n => some (.name n)) (.tuple es)]
      else pure ((rs.zip es).map fun (n, e) => .assign (.name n) e)
    | rs, e@(.call ..) => pure [.tupleAssign (rs.map fun n => some (.name n)) e]
    | rs, e@(.ternary _ (.call ..) (.call ..)) =>
      pure [.tupleAssign (rs.map fun n => some (.name n)) e]
    | rs, _ => throw s!"`return` of one value from a function that returns {rs.length}") ∧
  (∀ es c, RawExpr.andAll es c = es.foldr (fun e acc => .binop .and e acc) c) ∧
  (∀ a b, Abrupt.union a b = [.brk, .cnt, .ret].filter fun k => a.contains k || b.contains k) ∧
  (∀ x b, RawStmt.declBool x b = .decl (.named "bool") x (some (.bool b))) ∧
  (∀ x b, RawStmt.setBool x b = .assign (.name x) (.bool b)) ∧
  (∀ s, RawStmt.isJump s = match s with
    | .brk | .cont | .ret _ => true
    | _ => false) ∧
  (∀ s, RawStmt.hasJump s = s.anyDeep RawStmt.isJump)

end Kernel

/-- **The lowering kernel, total** (e2a-lower-total): at every spelling of fresh
names, the production `lowerList`/`lowerStmt`/`lowerLoop` satisfy their
defining equations, the recursion they define is well founded by a `Nat`
measure on the syntax, and `lowerLoops` and the helpers it reaches in
`Lower.lean` keep their behaviour.  Nothing here is about the meaning of the
lowered program (`lowerLoopsCorrect`). -/
@[goal Solidity.lowerKernel_total "e2a-lower-total"]
def loweringKernelTotal : Prop :=
  ∀ [FreshNames],
    LoweringKernelFix lowerList lowerStmt lowerLoop ∧
    (∃ (μL : List RawStmt → Nat) (μS μP : RawStmt → Nat), LoweringKernelContractive μL μS μP) ∧
    LoweringKernelHelpers

end Solidity.Goals
