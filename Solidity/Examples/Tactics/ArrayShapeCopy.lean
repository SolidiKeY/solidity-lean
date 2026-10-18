import Solidity.Calculus.Surface
import Solidity.Calculus.Closers
import Solidity.Calculus.Close
import Solidity.Calculus.Print
import Solidity.Syntax.Splice
import Solidity.Typing.Values

/-!
# Intrinsic fixed-array shape copies

The source remains one typed snapshot. Its converted outer shape is a term;
the ordinary write overlays it on the destination, retaining destination
histories. The adapter rules are explicit Lean-only instances of the copy
updates because KeY's `Struct` sort erases both outer array types.
-/

namespace Solidity.Examples.Tactics.ArrayShapeCopy
open Semantics
open scoped Scoped

def Shapes : Contract := contract!{
  uint[2] small;
  uint[4] big;
  uint[] values;
  uint[][] rows;
}

local instance : InContract := ⟨Shapes⟩

private def copies := sol{
  small[0] = 1; small[1] = 2;
  big = small; values = small; rows.push(small);
  assert(big[3] == 0); assert(values.length == 2);
  assert(rows[0].length == 2); assert(rows[0][1] == 2);
}

/-- The printed copy syntax executes all three compatible copy forms. -/
theorem copies_run : (Prog.run (State.init Shapes) copies).toOption.isSome = true := by
  decide +kernel

/-- A shorter fixed copy clears the entire typed target tail in every state. -/
theorem tail_proved : ⊨ dl!{ defined(wt(storage)) → [ big = small; ] big[3] == 0 } := by
  sol_prove (steps := 128)

example : (NSTerm.save (C := Shapes) NSTerm.storage (NPTerm.root "big")
    (NSValT.find NSTerm.storage (NPTerm.root "small"))).check .st [] =
    .ok (Tm.app3 .save (.app0 .storage) (.app0 (.root "big" rfl))
      (.app1 (.fixedCopy (.fixed 4 (by decide)))
        (.app2 .sfind (.app0 .storage) (.app0 (.root "small" rfl))))) := rfl

private def composed : Tm Shapes [] (.sv (.ref (.array Ty.uint))) :=
  .app1 (.fixedCopy (.dynamic (by decide)))
    (.app1 (.fixedCopy (.fixed 4 (by decide)))
      (.app2 .sfind (.app0 .storage) (.app0 (.root "small" rfl))))

/-- info: fixedCopy(uint[], fixedCopy(uint[4], find(storage, small))) -/
#guard_msgs in
run_meta do
  let value ← Delab.withPrinter (← Lean.getConstInfo ``composed).value! false
    (Delab.ppSValS [] (← Lean.getConstInfo ``composed).value!)
  Lean.logInfo m!"{value}"

/-- Each conversion prints its destination, so the composed one reads back as
it was (`NSValT.fixedCopy`, the formulas' reading of the text above). -/
example : (NSValT.fixedCopy (C := Shapes) (.array Ty.uint) (NSValT.fixedCopy (.fixed Ty.uint 4)
    (NSValT.find NSTerm.storage (NPTerm.root "small")))).check (.sv (.ref (.array Ty.uint))) [] =
    .ok composed := rfl

/-- …and the formulas' reader reads the printed text back as it was. -/
example : dl!{ { storage := save(storage, values, fixedCopy(uint[], fixedCopy(uint[4], find(storage, small)))) } true } =
    Fml.upd .diamond (Upd.snoc .nil (.storage (.app3 .save (.app0 .storage) (.app0 (.root "values" rfl)) composed)))
      .tt := rfl

/-- `tm{ … }` reads a conversion too, its schema variables Lean's. -/
example (s : Tm Shapes [] .st) (p : Tm Shapes [] (.path (.ref (.fixed Ty.uint 2)))) :
    tm{ fixedCopy(uint[], find(s, p)) } = .app1 (.fixedCopy (.dynamic (by decide))) (.app2 .sfind s p) :=
  rfl

private def word (n : Nat) : SVal Ty.uint := .prim (uintOfNat n)
private def fixed (xs : List (SVal Ty.uint)) : SVal (.ref (.fixed Ty.uint xs.length)) :=
  .fixed (SVec.ofList xs)
private def array (xs sh : List (SVal Ty.uint)) (h : xs.length < 2 ^ 256) :
    SVal (.ref (.array Ty.uint)) := .array (SVec.ofList xs) (SList.ofList sh) h

example : (fixed [word 9, word 8, word 7, word 6]).overlay
    ((FixedCopy.fixed 4 (by decide)).apply (fixed [word 1, word 2])) =
      fixed [word 1, word 2, word 0, word 0] := by decide +kernel

example : (array [word 9, word 8, word 7] [word 99] (by decide)).overlay
    ((FixedCopy.dynamic (by decide)).apply (fixed [word 1, word 2])) =
      array [word 1, word 2] [word 0, word 99] (by decide) := by decide +kernel

private def rows (xs : List (SVal (.ref (.array Ty.uint)))) :
    SVal (.ref (.fixed (.ref (.array Ty.uint)) xs.length)) := .fixed (SVec.ofList xs)

example : (rows [array [word 91, word 92] [word 93] (by decide),
      array [word 94] [word 95] (by decide), array [word 96] [word 97] (by decide)]).overlay
    ((FixedCopy.fixed (n := 2) 3 (by decide)).apply
      (rows [array [word 11] [word 70] (by decide), array [] [word 71] (by decide)])) =
      rows [array [word 11] [word 0, word 93] (by decide),
        array [] [word 0, word 95] (by decide), array [] [word 0, word 97] (by decide)] := by
  decide +kernel

/-- info: shape copies roundtrip through both source printers -/
#guard_msgs in
run_meta do
  for name in [``copies] do
    let info ← Lean.getConstInfo name
    let original := info.value!
    let some ss ← Delab.withPrinter original false (Delab.ppProgS [] original)
      | throwError "shape copy printer failed: {name}"
    let printed ← `(sol[Shapes]{ $[$ss;]* })
    let parsed ← Lean.Elab.Term.TermElabM.run' do
      let p ← Lean.Elab.Term.elabTermEnsuringType printed info.type
      Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
      pure p
    let state := Lean.mkApp (Lean.mkConst ``State.init) (Lean.mkConst ``Shapes)
    let originalRun ← Lean.Meta.mkAppM ``Prog.run #[state, original]
    let parsedRun ← Lean.Meta.mkAppM ``Prog.run #[state, parsed]
    unless ← Lean.Meta.isDefEq originalRun parsedRun do
      throwError "shape copy roundtrip changed execution of {name}: {printed}"
    let shownExpr ← Lean.Meta.mkAppM ``Prog.show #[Lean.toExpr ([] : List Var), original]
    let shown ← unsafe Lean.Meta.evalExpr String (Lean.mkConst ``String) shownExpr
    let .ok stx := Lean.Parser.runParserCategory (← Lean.getEnv) `term s!"sol[Shapes]\{ {shown} }"
      | throwError "shape copy display does not parse: {shown}"
    let parsed ← Lean.Elab.Term.TermElabM.run' do
      let p ← Lean.Elab.Term.elabTermEnsuringType stx info.type
      Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
      pure p
    let parsedRun ← Lean.Meta.mkAppM ``Prog.run #[state, parsed]
    unless ← Lean.Meta.isDefEq originalRun parsedRun do
      throwError "shape copy display roundtrip changed execution of {name}: {shown}"
    let shownAgainExpr ← Lean.Meta.mkAppM ``Prog.show #[Lean.toExpr ([] : List Var), parsed]
    let shownAgain ← unsafe Lean.Meta.evalExpr String (Lean.mkConst ``String) shownAgainExpr
    unless shown == shownAgain do
      throwError "shape copy display is not stable for {name}: {shownAgain}"
  Lean.logInfo "shape copies roundtrip through both source printers"

end Solidity.Examples.Tactics.ArrayShapeCopy
