import Solidity.Syntax.Elab.Lower

/-!
# Checks: the callee-side producers' equations

`renameStmts`, `lowerReturns` and `wrapMods` are total, so a callee's body
unfolds by their named equations, with no `native_decide`.  Each unfolding
stops at what is still opaque: `RawExpr.rename` (through the partial `RawExpr.mapM`) and
`RawStmt.hasReturn`, `RawStmt.mentions` (through the partial
`RawStmt.anyDeep`), all of `Syntax/Elab/Context.lean`.  Concrete runs agree
with the unfolded forms.
-/

namespace Solidity.Examples.ElabTotal.Lower

open Solidity

variable [FreshNames]

/-! ### `renameStmts` -/

/-- `T x = i; l = r;`: the declaration numbered, the assignment renamed
under the extended map. -/
theorem renameStmts_decl_assign (ρ : List (String × String)) (T : RawTy) (x : String)
    (i : Option RawExpr) (l r : RawExpr) :
    renameStmts ρ [.decl T x i, .assign l r] = (do
      let y := toString (← freshCapture "se")
      pure [.decl T y (i.map (RawExpr.rename ρ)),
        Id.run ((RawStmt.assign l r).mapExprsM (pure ∘ RawExpr.rename ((x, y) :: ρ)))]) := by
  rw [renameStmts_decl]
  simp only [renameStmts_leaf _ _ (.assign l r) rfl, renameStmts_nil, pure_bind]

/-- Every declaration takes a capture of its kind, in order. -/
theorem renameStmts_decls (ρ : List (String × String)) (T : RawTy) (e : RawExpr) :
    renameStmts ρ [.declStorage T "a" none, .declMemory T "b" none, .declStoragePush T "c" e,
        .declPush T "d" e, .send (some T) (.name "x") e e true] = (do
      let a := toString (← freshCapture "sp")
      let b := toString (← freshCapture "mv")
      let c := toString (← freshCapture "sp")
      let d := toString (← freshCapture "se")
      let x := toString (← freshCapture "se")
      let ρc := ("c", c) :: ("b", b) :: ("a", a) :: ρ
      pure [.declStorage T a none, .declMemory T b none,
        .declStoragePush T c (e.rename (("b", b) :: ("a", a) :: ρ)), .declPush T d (e.rename ρc),
        .send (some T) (.name x) (e.rename (("d", d) :: ρc)) (e.rename (("d", d) :: ρc)) true]) := by
  simp only [renameStmts_declStorage, renameStmts_declMemory, renameStmts_declStoragePush,
    renameStmts_declPush, renameStmts_send, renameStmts_nil, bind_assoc, pure_bind,
    Option.map_none]

/-- Blocks and loops keep their map; a loop's specification is renamed. -/
theorem renameStmts_nested (ρ : List (String × String)) (a : RawLoopSpec) (c : RawExpr)
    (o : OFMode) :
    renameStmts ρ [.ite c [.unchecked [.checked o [.block []]]] [],
        .whileLoop a c [.doWhile a [.loop a c [.forLoop a [] none [] []]] c]] =
      pure [.ite (c.rename ρ) [.unchecked [.checked o [.block []]]] [],
        .whileLoop (a.rename ρ) (c.rename ρ) [.doWhile (a.rename ρ)
          [.loop (a.rename ρ) (c.rename ρ) [.forLoop (a.rename ρ) [] none [] []]] (c.rename ρ)]] := by
  simp only [renameStmts_ite, renameStmts_unchecked, renameStmts_checked, renameStmts_block,
    renameStmts_whileLoop, renameStmts_doWhile, renameStmts_loop, renameStmts_forLoop_nil,
    renameStmts_nil, pure_bind, Option.map_none]

/-- A tuple declaration and a `try` that bind nothing take no capture. -/
theorem renameStmts_binders (ρ : List (String × String)) (e : RawExpr) (g : String) :
    renameStmts ρ [.tupleDecl [] e, .tryCall e g [] [] [] [] none [] []] =
      pure [.tupleDecl [] (e.rename ρ), .tryCall (e.rename ρ) g [] [] [] [] none [] []] := by
  rw [renameStmts_tupleDecl]
  simp only [List.forIn_nil, pure_bind, renameStmts_tryCall, renameStmts_nil]
  rfl

/-- `for (s₀; c; u) b`: the initialisation and the loop without it, renamed
as one list; the measure counts the initialisation twice for this call. -/
theorem renameStmts_for (ρ : List (String × String)) (a : RawLoopSpec) (s₀ : RawStmt)
    (c : Option RawExpr) (u b : List RawStmt) :
    renameStmts ρ [.forLoop a [s₀] c u b] = (do
      let out ← renameStmts ρ [s₀, .forLoop a [] c u b]
      match out.getLast? with
      | some (.forLoop a' [] c' u' b') => pure [.forLoop a' out.dropLast c' u' b']
      | _ => throw "a `for` loop's initialisation, renamed") := by
  rw [renameStmts_forLoop_cons, renameStmts_nil]
  simp only [pure_bind]
  rfl

/-! ### `lowerReturns` -/

omit [FreshNames] in
/-- What follows a `return` is dropped. -/
theorem lowerReturns_dead (r : String) (l : RawExpr) (ss : List RawStmt) :
    lowerReturns [r] (.assign l (.num 0) :: .ret (some (.num 1)) :: ss) =
      pure [.assign l (.num 0), .assign (.name r) (.num 1)] := by
  rw [lowerReturns_leaf _ _ _ rfl, lowerReturns_ret_some]
  rfl

omit [FreshNames] in
/-- Blocks with nothing after them are lowered in place, whatever they hold
(the guard's second conjunct is false); `{ return; }` is `{ }`. -/
theorem lowerReturns_last (r : List String) (c e : RawExpr) (o : OFMode) (g : String) :
    lowerReturns r [.ite c [.unchecked [.checked o [.tryCall e g [] [] [] [] none [] []]]]
        [.block [.ret none]]] =
      pure [.ite c [.unchecked [.checked o [.tryCall e g [] [] [] [] none [] []]]]
        [.block []]] := by
  simp only [lowerReturns_ite, lowerReturns_unchecked, lowerReturns_checked,
    lowerReturns_tryCall, lowerReturns_block, lowerReturns_ret_none, lowerReturns_nil,
    List.isEmpty_nil, Bool.not_true, Bool.and_false, Bool.false_eq_true, ↓reduceIte, pure_bind]

/-! ### `wrapMods` -/

/-- No modifier: the body. One: `wrapMod` around the body. -/
theorem wrapMods_one (C : Contract) (body : List RawStmt)
    (frame : Option (FunDecl × List (String × String))) (m : ModApp) :
    wrapMods C body frame [m] = wrapMod C frame m body := by
  rw [wrapMods_cons, wrapMods_nil, pure_bind]

/-- Two: the first listed is outermost. -/
theorem wrapMods_two (C : Contract) (body : List RawStmt)
    (frame : Option (FunDecl × List (String × String))) (m₁ m₂ : ModApp) :
    wrapMods C body frame [m₁, m₂] = (do
      let inner ← wrapMod C frame m₂ body
      wrapMod C frame m₁ inner) := by
  rw [wrapMods_cons, wrapMods_one]

/-! ### Concrete runs -/

private def C0 : Contract := { vars := [] }

private def run {α : Type} [Repr α] (x : ElabM α) : String :=
  match x.runFrom { funs := [] } ([], 1) with
  | .ok (a, (_, k)) => s!"{repr a} @{k}"
  | .error e => s!"error: {e}"

private def pureRun {α : Type} [Repr α] (x : Except String α) : String :=
  match x with
  | .ok a => s!"{repr a}"
  | .error e => s!"error: {e}"

private def uintT : RawTy := .named "uint"
private def body : List RawStmt :=
  [.decl uintT "x" (some (.name "p")), .ite (.name "x") [.ret (some (.name "x"))] [],
   .assign (.name "x") (.num 2), .ret (some (.name "x"))]

-- The renamed body agrees with its equations' unfolding: the declaration
-- takes the capture, the rest is renamed under the extended map.
#guard run (renameStmts [("p", "q")] body) ==
  run (do
    let y := toString (← freshCapture "se")
    let rest ← renameStmts [("x", y), ("p", "q")] body.tail
    pure (RawStmt.decl uintT y (some (.name "q")) :: rest))

-- `if (x) { return x; } x = 2; return x;`: the rest moves into both branches.
#guard pureRun (lowerReturns ["r"] body.tail) ==
  pureRun (pure (f := Except String)
    [RawStmt.ite (.name "x") [.assign (.name "r") (.name "x")]
      [.assign (.name "x") (.num 2), .assign (.name "r") (.name "x")]])

-- A `for` loop's initialisation declares over the loop: one capture, used in
-- the condition.
#guard run (renameStmts []
    [.forLoop {} [.decl uintT "i" none] (some (.name "i")) [] []]) ==
  run (do
    let y := toString (← freshCapture "se")
    pure [RawStmt.forLoop {} [.decl uintT y none] (some (.name y)) [] []])

-- A `return` inside `unchecked` with statements after it is refused, as before.
#guard pureRun (lowerReturns [] [.unchecked [.ret none], .brk]) ==
  "error: `return` inside `unchecked { … }` with statements after the block"

-- Modifiers: none is the body; `m` with the body `_; _;` runs it twice.
private def m : ModApp := { name := "m", params := [], args := [], body := [.hole, .hole] }
#guard run (wrapMods C0 [.brk] none []) == run (pure (f := ElabM) [RawStmt.brk])
#guard run (wrapMods C0 [.brk] none [m]) ==
  run (pure (f := ElabM) [RawStmt.block [.brk], RawStmt.block [.brk]])
#guard pureRun ((RawStmt.unchecked [.hole]).fillHole []) ==
  "error: `_;` inside `unchecked { … }`"

end Solidity.Examples.ElabTotal.Lower
