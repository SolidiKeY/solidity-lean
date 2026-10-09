import Solidity.Calculus.Delab
import Solidity.Examples.Tactics.CoreSymex
import Solidity.Tools.Inspect
import Solidity.Tools.Taclet

/-!
# Scoped taclets and formulas, printed

`Calculus/Delab.lean`'s printers pinned: scoped taclets print
their rule lines as today's did (today's `Calculus/Rules`, deleted at W4
`calc-del`), all but five (`functionBodyExpand`, `internalCallExpand`,
`tryCallNoCallbackBox`, `functionCallArgCapture`, `tryCallDiamond`), also under
`#taclet` (`Tools/Inspect.lean`), and a formula the
scoped strategy leaves prints, from its `Expr`, as `Fml.show` prints
the value: calls (with a tuple and a memory return) and `try` among them.
The premises of `branches`, `cases`, `inv` and `inline` print from their
`Expr` (a premise read alone names the locals of its context `_`), and a
`Proves` goal prints as today's sequent.
-/

namespace Solidity.Examples.Tactics.CorePrint

open Solidity Lean Meta

local instance : InContract := ⟨StandardExample⟩

private abbrev SE := StandardExample

/--
info: @Taclet.localValueAssign : ∀ {C : Contract} {k : Nat} {m : Modality} {Γ : Ctx} {x : PrimTy}
  {v : Idx Γ (LTy.val x)} {se : Simple C Γ x}, dl{ ⟨[ v = se; ]⟩ ⇝ { v := se } ⟨[ ]⟩ }
-/
#guard_msgs in #check @Taclet.localValueAssign

/--
info: @Taclet.storageFieldDelete_unfold_leftFst : ∀ {C : Contract} {k : Nat} {m : Modality} {Γ : Ctx} {x : Name}
  {nsp : SPath C Γ (Ty.struct x)} {fld : Name} {x_1 : Ty},
  dl{ ⟨[ delete nsp.fld; ]⟩ ⇝ ⟨[ T storage sp = nsp; delete sp.fld; ]⟩ }
-/
#guard_msgs in #check @Taclet.storageFieldDelete_unfold_leftFst

/--
info: @Taclet.ifElseSplit : ∀ {C : Contract} {k : Nat} {m : Modality} {Γ : Ctx} {se : Simple C Γ PrimTy.bool}
  {x : Ctx} {thenStm : Prog C Γ x} {x_1 : Ctx} {elseStm : Prog C Γ x_1},
  dl{ ⟨[ if (se) thenStm else elseStm; ]⟩ ⇝
    "if s#se true": se ≐ true ⟹ ⟨[ thenStm ]⟩ ; "if s#se false": se ≐ false ⟹ ⟨[ elseStm ]⟩ }
-/
#guard_msgs in #check @Taclet.ifElseSplit

/-! `#taclet` on a scoped taclet: its line, today's solkey taclets.  The
rule is one that prints as today's did (all but the five above do). -/

/--
info: Solidity.Taclet.storageFieldDelete_unfold_leftFst : ∀ {C : Contract} {k : Nat} {m : Modality} {Γ : Ctx}
  {x : Name} {nsp : SPath C Γ (Ty.struct x)} {fld : Name} {x_1 : Ty},
  dl{ ⟨[ delete nsp.fld; ]⟩ ⇝ ⟨[ T storage sp = nsp; delete sp.fld; ]⟩ }
solkey: storageFieldDelete_unfold_leftFst (simplify_prog)
printed: storageFieldDelete_unfold_leftFst
sound: Solidity.Taclet.toStep (the premise is Stmt.step's; Stmt.Sound)
-/
#guard_msgs in #taclet Taclet.storageFieldDelete_unfold_leftFst

/-! A rule's premise for a statement, quoted (`Premise.quote`), checked
by the kernel's type checker and printed: a position outside the term is
`_`, as `Idx.name` names it. -/

private def readS : Stmt SE [.val .uint] [.val .uint] :=
  .assignLocal .here (.read (.field (.loc (.root "alice" rfl)) "age" rfl))

/-- info: dl{ { _ := find(storage, alice.age) } ⟨[ ]⟩ } -/
#guard_msgs in
run_meta do
  let some p := readS.step 1 .box | throwError "no rule"
  let e := Premise.quote (mkConst ``StandardExample) p
  Meta.check e
  logInfo m!"{e}"

/-! A formula whose program runs into a branch's end: `}`, then the rest. -/

/-- info: dl{ ∀ uint x; x > 0 → [ uint y = x; x = y; } x = 2; ] x = 1 } : Fml SE [] -/
#guard_msgs in
#check (Fml.all (.user "x") .uint
  (.imp (.eqD (.app2 (.binop .gt .uint) (.pvV .here) (.app0 (.lit (.int 0))))
      (.app0 (.lit (.bool true))))
    (.modal .box
      (.cons (.declLocal .uint (.user "y") (some (.simple (.local .here))))
        (.cons (.assignLocal (.there .here) (.simple (.local .here))) .nil))
      (.pop .block (.push .refl) (.seq (.cons (.assignLocal .here (.simple (.lit 2 rfl))) .nil) .nil))
      (.eqD (.pvV .here) (.app0 (.lit (.int 1)))))) : Fml SE [])

/-- `∀ x₁; … ∀ xₙ; ψ` over the value locals of `Γ` (innermost first). -/
private def closeAll {C : Contract} : (Γ : NCtx) → Fml C Γ.ctx → MetaM (Fml C [])
  | [], ψ => pure ψ
  | (x, .val p) :: Γ, ψ => closeAll Γ (.all x p ψ)
  | _, _ => throwError "a local that is not a value"

/-- The scoped strategy's formula after `n` steps on `φ`, its program read
under the value locals `Γ`, each bound by `∀`, printed from its quoted
`Expr` and checked against `Fml.show` on the value. -/
private def stepsShowOf {C : Contract} (c : Expr) (φ : Solidity.Surface.Fml C) (n : Nat)
    (Γ : NCtx := []) : MetaM Unit := do
  let .modal m P _ := φ | throwError "not a modality"
  let .ok ⟨_, Pc⟩ := Prog.resolve (C := C) Γ P | throwError "the program does not resolve"
  let ψ := symex n (← closeAll Γ (.modal m Pc .nil .tt))
  let a ← Delab.fmtFml (Fml.quote c ψ)
  let b ← ψ.show c []
  unless a == b do throwError "from the Expr\n{a}\nbut the value prints\n{b}"
  logInfo a

private def stepsShow (φ : Solidity.Surface.Fml SE) (n : Nat) : MetaM Unit :=
  stepsShowOf (mkConst ``StandardExample) φ n

/-- The premise of the rule on the first statement of a program, quoted. -/
private def headPremiseOf {C : Contract} (c : Expr) (m : Modality) :
    {Γ Γ' : Ctx} → Prog C Γ Γ' → MetaM Expr
  | _, _, .cons s _ => do
    let some p := s.step 1 m | throwError "no rule"
    return Premise.quote c p
  | _, _, .nil => throwError "no statement"

/-- The premise of the rule on the first statement of `φ`'s program, read in
the context `Γ`, quoted, checked by the kernel's type checker and printed. -/
private def headPremise {C : Contract} (c : Expr) (Γ : NCtx) (φ : Solidity.Surface.Fml C) :
    MetaM Unit := do
  let .modal m P _ := φ | throwError "not a modality"
  let .ok ⟨_, Pc⟩ := Prog.resolve (C := C) Γ P | throwError "the program does not resolve"
  let e ← headPremiseOf c m Pc
  Meta.check e
  logInfo m!"{e}"

private def branchφ : Solidity.Surface.Fml SE :=
  dl!{ [ if (alice.age > 4) { uint z = 1; total = z; } else { total = 2; }; uint y = total; ] true }

/--
info: { se2 := find(storage, alice.age) } [ se1 = se2 > 4; if (se1) {uint z = 1;total = z;} else {total = 2;}; uint y = total; ] true
-/
#guard_msgs in run_meta stepsShow branchφ 5

/--
info: { se2 := find(storage, alice.age) } { se1 := se2 > 4 } ((se1 ≐ true → [ uint z = 1; total = z; } uint y = total; ] true) ∧ (se1 ≐ false → [ total = 2; } uint y = total; ] true))
-/
#guard_msgs in run_meta stepsShow branchφ 7

/--
info: { se2 := find(storage, alice.age) } { se1 := se2 > 4 } ((se1 ≐ true → { z := 1 } [ total = z; } uint y = total; ] true) ∧ (se1 ≐ false → [ total = 2; } uint y = total; ] true))
-/
#guard_msgs in run_meta stepsShow branchφ 9

/-! After a call with a tuple return, the statements read their locals past
the return variables (`CallRet.outNames`): `uint y = a;`, not the caller's
`x`.  The call prints from the `Expr` as `Fml.show` prints it from the
value, folded with the statements after it that assign its returns;
returns that none assigns but one reads print as the declarations they
are. -/

private def retsφ : Fml SE [] :=
  .all (.user "x") .uint (.modal .box
    (.cons (.call "h" .nil (.rets ((Binders.nil.snoc .uint (.user "a")).snoc .uint (.user "b"))) .nil)
      (.cons (.declLocal .uint (.user "y") (some (.simple (.local (.there .here))))) .nil))
    .nil .tt)

/-- info: ∀ uint x; [ (uint a, uint b) = h(); uint y = a; ] true -/
#guard_msgs in
run_meta do
  let c := mkConst ``StandardExample
  let a ← Delab.fmtFml (Fml.quote c retsφ)
  let b ← retsφ.show c []
  unless a == b do throwError "from the Expr\n{a}\nbut the value prints\n{b}"
  logInfo a

/-! An update that is a schema variable prints as itself, its elements on
top of it after it (a position it did not declare is `_`). -/

/-- info: fun U => dl{ { U ‖ _ := 1 } true } : Upd SE [] [LTy.val PrimTy.uint] → Fml SE [] -/
#guard_msgs in
#check fun (U : Upd SE [] [.val .uint]) =>
  (Fml.upd .box (U.snoc (.local .here (.val (.app0 (.lit (.int 1)))))) .tt : Fml SE [])

/-! ## Calls and `try`

A call and a `try` print as the statements they are elaborated from, from
the `Expr` as from the value: no `‹…›`. -/

section Calls

local instance : InContract := ⟨CallsExample⟩

private def callsφ : Solidity.Surface.Fml CallsExample :=
  dl!{ [ uint y = addOne(4); credit(y, 5); bump(); ] true }

/--
info: [ uint y; y = addOne(4); credit(y, 5); bump(); ] true
-/
#guard_msgs in run_meta stepsShowOf (mkConst ``CallsExample) callsφ 0

/--
info: { y := 0 } [ se1 = 4; uint se2; se2 = se1 + 1; y = se2; credit(y, 5); bump(); ] true
-/
#guard_msgs in run_meta stepsShowOf (mkConst ``CallsExample) callsφ 3

end Calls

/-- Functions returning a pair and a memory object (`CoreStep.lean`'s). -/
def Rets : Contract := contract!{
  uint total;
  function pair(uint x) returns (uint lo, uint hi) { return (x, x + 1); }
  function mk(uint x) returns (Person memory p) { p.age = x; }
}

section Rets

local instance : InContract := ⟨Rets⟩

private def re : Expr := mkConst ``Solidity.Examples.Tactics.CorePrint.Rets

private def retsCallφ : Solidity.Surface.Fml Rets :=
  dl!{ [ uint a; uint b; (a, b) = pair(3); Person memory m = mk(2); uint y = m.age; ] true }

private def pairφ : Solidity.Surface.Fml Rets := dl!{ [ (a, b) = pair(3); ] true }

private def abΓ : NCtx := [(.user "b", .val .uint), (.user "a", .val .uint)]

/--
info: [ uint a; uint b; (a, b) = pair(3); Person memory m = mk(2); uint y = m.age; ] true
-/
#guard_msgs in run_meta stepsShowOf re retsCallφ 0

/--
info: { a := 0 } { b := 0 } [ se1 = 3; uint se2; uint se3; se2 = se1; se3 = se1 + 1; a = se2; b = se3; Person memory m = mk(2); uint y = m.age; ] true
-/
#guard_msgs in run_meta stepsShowOf re retsCallφ 4

-- `functionBodyExpand`: a block whose end drops the parameters from under
-- the return variables (`Premise.inline`).
/--
info: dl{ ⟨[ uint se1 = 3; uint se2; uint se3; se2 = se1; se3 = se1 + 1; ]⟩ }
-/
#guard_msgs in
run_meta headPremise re abΓ pairφ

/--
info: ∀ uint a; ∀ uint b; [ uint se1 = 3; uint se2; uint se3; se2 = se1; se3 = se1 + 1; a = se2; b = se3; ] true
-/
#guard_msgs in run_meta stepsShowOf re pairφ 1 abΓ

end Rets

/-- A contract that pings another. -/
def Pinger : Contract := contract!{ uint pings; uint last; }

section Try

local instance : InContract := ⟨Pinger⟩

private def pe : Expr := mkConst ``Solidity.Examples.Tactics.CorePrint.Pinger

private def tryφ : Solidity.Surface.Fml Pinger :=
  dl!{ [ try I(7).get() returns (uint v) { last = v; } catch Panic(uint c) { last = c; }
         catch { last = 0; }; pings = 1; ] true }

/--
info: [ try address(7).get() returns (uint v) {last = v;} catch Error(string memory) {last = 0;} catch Panic(uint c) {last = c;} catch {last = 0;}; pings = 1; ] true
-/
#guard_msgs in run_meta stepsShowOf pe tryφ 0

/--
info: (∀ uint v; [ last = v; } pings = 1; ] true) ∧ [ last = 0; } pings = 1; ] true ∧ (∀ uint c; [ last = c; } pings = 1; ] true) ∧ [ last = 0; } pings = 1; ] true
-/
#guard_msgs in run_meta stepsShowOf pe tryφ 1

-- `tryCallNoCallbackBox`: a goal per clause (`Premise.branches`).
/--
info: dl{ ⟨[ {last = 1;} ]⟩ ; ⟨[ {last = 0;} ]⟩ ; ⟨[ {last = 0;} ]⟩ ; ⟨[ {last = 0;} ]⟩ }
-/
#guard_msgs in
run_meta headPremise pe [] dl!{ [ try I(7).get() { last = 1; } catch { last = 0; }; ] true }

end Try

/-! ## The other premises -/

private def sendφ : Solidity.Surface.Fml SE := dl!{ [ ok = owner.send(3); ] true }

private def sendSimpleφ : Solidity.Surface.Fml SE := dl!{ [ ok = to.send(3); ] true }

private def okToΓ : NCtx := [(.user "ok", .val .bool), (.user "to", .val .uint)]

private def loopφ : Solidity.Surface.Fml SE :=
  dl!{ [ /// @custom:key invariant i <= 3
         while (i < 3) { i = i + 1; total = i; }; ] true }

-- `sendNoCallbackBox`: labelled goals (`Premise.cases`).
/--
info: dl{ { net := if(_ = this) then net else store(net, at(_), net(_) - 3) ‖ _ := true } ⟨[ ]⟩ ; { _ := false } ⟨[ ]⟩ }
-/
#guard_msgs in
run_meta headPremise (mkConst ``StandardExample) okToΓ sendSimpleφ

/--
info: ∀ bool ok; [ uint se1 = owner; ok = se1 .send(3); ] true
-/
#guard_msgs in run_meta stepsShowOf (mkConst ``StandardExample) sendφ 1 [(.user "ok", .val .bool)]

/--
info: ∀ bool ok; { se1 := find(storage, owner) } ({ net := if(se1 = this) then net else store(net, at(se1), net(se1) - 3) ‖ ok := true } true ∧ { ok := false } true)
-/
#guard_msgs in run_meta stepsShowOf (mkConst ``StandardExample) sendφ 4 [(.user "ok", .val .bool)]

-- `whileInvariantBox` (`Premise.inv`).
/--
info: dl{
  _ <= 3 ; { anon({_ = _ + 1;total = _;}) } (_ <= 3 → { se1 := _ < 3 } (se1 = true ⟹ ⟨[ {_ = _ + 1;total = _;} ]⟩
    _ <= 3 ; se1 = false ⟹ ⟨[ ]⟩)) }
-/
#guard_msgs in
run_meta headPremise (mkConst ``StandardExample) [(.user "i", .val .uint)] loopφ

/--
info: ∀ uint i; i <= 3 ∧ { anon(i) } { havoc } (i <= 3 → { se1 := i < 3 } ((se1 = true → [ i = i + 1; total = i; } ] i <= 3) ∧ (se1 = false → true)))
-/
#guard_msgs in run_meta stepsShowOf (mkConst ``StandardExample) loopφ 1 [(.user "i", .val .uint)]

/-! ## Sequents

`Proves C R Γ₀ H φ` prints as today's sequent: the context's entries
left of `⟹`, a variable context as `..H`; an update of pops and the hidden
binder print as nothing. -/

/--
info: dl{ ∀ uint x, x = 1, { y := x } ⟹ [ x = y; ] true } : Prop
-/
#guard_msgs in
#check (Proves SE .all [] (((Hyps.nil.all (.user "x") .uint).pre
    (.eqD (.pvV .here) (.app0 (.lit (.int 1))))).upd .box
      (Upd.nil.decl (.user "y") (.val (.pvV .here))))
  (.modal .box (.cons (.assignLocal (.there .here) (.simple (.local .here))) .nil) .nil .tt))

/--
info: fun H => dl{ ..H ⟹ₖ _ = 1 } : Hyps SE [] [LTy.val PrimTy.uint] → Prop
-/
#guard_msgs in
#check fun (H : Hyps SE [] [.val .uint]) =>
  Proves SE .solkey [] (H.bind .box (.user "z") (.val .bool)) (.eqD (.pvV (.there .here)) (.app0 (.lit (.int 1))))

-- A goal of a walk prints as the line it is.
/--
trace: case h.thn
⊢ dl{ ∀ bool b, b ≐ true ⟹ true }
-/
#guard_msgs in
example : Proves SE .all [] .nil (.all (.user "b") .bool
    (.modal .box (.cons (.ite (.simple (.local .here)) .nil .nil) .nil) .nil .tt)) := by
  apply Proves.allIntro
  apply Proves.split rfl
  · trace_state
    exact .updIntro (.closeTrue rfl)
  · exact .updIntro (.closeTrue rfl)

end Solidity.Examples.Tactics.CorePrint
