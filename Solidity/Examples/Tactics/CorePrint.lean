import Solidity.Calculus.Core.Delab
import Solidity.Examples.Tactics.CoreSymex

/-!
# Scoped taclets and formulas, printed

`Calculus/Core/Delab.lean`'s printers pinned: the three scoped taclets print
their rule lines as today's do (`Calculus/Rules.lean`), and a formula the
scoped strategy leaves prints, from its `Expr`, as `Core.Fml.show` prints
the value.
-/

namespace Solidity.Examples.Tactics.CorePrint

open Solidity Lean Meta

local instance : InContract := ⟨StandardExample⟩

private abbrev SE := StandardExample

/--
info: @Core.Taclet.localValueAssign : ∀ {C : Contract} {k : Nat} {m : Modality} {Γ : Core.Ctx} {p : PrimTy}
  {v : Core.Idx Γ (Core.LTy.val p)} {se : Core.Simple C Γ p}, dl{ ⟨[ v = se; ]⟩ ⇝ { v := se } ⟨[ ]⟩ }
-/
#guard_msgs in #check @Core.Taclet.localValueAssign

/--
info: @Core.Taclet.storageFieldRead_unfold_rightFst : ∀ {C : Contract} {k : Nat} {m : Modality} {Γ : Core.Ctx} {p : PrimTy}
  {s : Name} {v : Core.Idx Γ (Core.LTy.val p)} {nsp : Core.SPath C Γ (Ty.struct s)} {fld : Name}
  {h : C.fieldType s fld = some (Ty.prim p)} (hn : nsp.isSimple = false),
  dl{ ⟨[ v = nsp.fld; ]⟩ ⇝ ⟨[ T storage sp = nsp; v = sp.fld; ]⟩ }
-/
#guard_msgs in #check @Core.Taclet.storageFieldRead_unfold_rightFst

/--
info: @Core.Taclet.ifElseSplit : ∀ {C : Contract} {k : Nat} {m : Modality} {Γ Γ₁ Γ₂ : Core.Ctx}
  {se : Core.Simple C Γ PrimTy.bool} {thn : Core.Prog C Γ Γ₁} {els : Core.Prog C Γ Γ₂},
  dl{ ⟨[ if (se) thn else els; ]⟩ ⇝ "if s#se true": se ≐ true ⟹ ⟨[ thn ]⟩ ; "if s#se false": se ≐ false ⟹ ⟨[ els ]⟩ }
-/
#guard_msgs in #check @Core.Taclet.ifElseSplit

/-! A formula whose program runs into a branch's end: `}`, then the rest. -/

/-- info: dl{ ∀ uint x; x > 0 → [ uint y = x; x = y; } x = 2; ] x = 1 } : Core.Fml SE [] -/
#guard_msgs in
#check (Core.Fml.all (.user "x") .uint
  (.imp (.eqD (.app2 (.binop .gt .uint) (.pvV .here) (.app0 (.lit (.int 0))))
      (.app0 (.lit (.bool true))))
    (.modal .box
      (.cons (.declLocal .uint (.user "y") (some (.simple (.local .here))))
        (.cons (.assignLocal (.there .here) (.simple (.local .here))) .nil))
      (.pop .block (.push .refl) (.seq (.cons (.assignLocal .here (.simple (.lit 2 rfl))) .nil) .nil))
      (.eqD (.pvV .here) (.app0 (.lit (.int 1)))))) : Core.Fml SE [])

/-- The scoped strategy's formula after `n` steps on `φ`, printed from its
quoted `Expr` and checked against `Core.Fml.show` on the value. -/
private def stepsShow (φ : Solidity.Fml SE) (n : Nat) : MetaM Unit := do
  let c := mkConst ``StandardExample
  let .modal m P _ := φ | throwError "not a modality"
  let .ok ⟨_, Pc⟩ := Core.Prog.resolve (C := SE) [] P | throwError "the program does not resolve"
  let ψ := Core.symex n (.modal m Pc .nil .tt : Core.Fml SE [])
  let a ← Core.Delab.fmtFml (Core.Fml.quote c ψ)
  let b ← ψ.show c []
  unless a == b do throwError "from the Expr\n{a}\nbut the value prints\n{b}"
  logInfo a

private def branchφ : Solidity.Fml SE :=
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

end Solidity.Examples.Tactics.CorePrint
