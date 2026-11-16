import Solidity.Lowering.V08.LiteralFailureLowering

/-! Actual typed addition at the checked/unchecked range boundary.
No new arithmetic semantics or admission predicate. -/
namespace Solidity.Lowering.V08.LiteralFailureOverflowReason
open Solidity Source

def context (t : IntTy) (Γ : RCtx) : RCtx := .int t :: .int t :: Γ

def caller {E : Env} {Γ : RCtx} (t : IntTy) (x y : Int)
 (hx : t.lo≤x ∧ x≤t.hi) (hy : t.lo≤y ∧ y≤t.hi) (older : Locals E.layout Γ) :
 Locals E.layout (context t Γ) := .cons (.int x hx) (.cons (.int y hy) older)

def addition {E : Env} {Γ : RCtx} (t : IntTy) : RExpr E (context t Γ) (.int t) :=
 .binary .add (.local .here) (.local (.there .here))

theorem add_value {D : Source.Layout} (t : IntTy) (checked : Bool) (x y : Int)
 (hx : t.lo≤x ∧ x≤t.hi) (hy : t.lo≤y ∧ y≤t.hi) :
 binVal (D:=D) checked .add (.int x hx) (.int y hy)=intRes t checked (x+y) := by rfl

theorem checked_overflow {E : Env} {Γ : RCtx} (G : Glob E) (F : Fr) (n : Nat)
 (t : IntTy) (x y : Int) (hx : t.lo≤x ∧ x≤t.hi) (hy : t.lo≤y ∧ y≤t.hi)
 (outside : ¬(t.lo≤x+y ∧ x+y≤t.hi)) (older : Locals E.layout Γ) (state : St E) :
 (evalE G {F with checked:=true} (n+5) (addition t)).run (caller t x y hx hy older,state)=
 (.error (.revert (panicData .arithmetic)),(caller t x y hx hy older,state)) := by
 cases order : G.pipeline <;>
  simp only [addition,caller,evalE,evalPair,withLibraryCalldata,order,Bool.false_eq_true,↓reduceIte] <;>
  dsimp [EM.lift,EM.locals,getV,RVal.get,bind,pure,ExceptT.bind,ExceptT.pure,ExceptT.bindCont,
   ExceptT.run,ExceptT.mk,StateT.bind,StateT.pure,StateT.get,get,getThe,MonadStateOf.get,
   liftM,monadLift,MonadLift.monadLift,ExceptT.lift,Functor.map,StateT.map,
   Except.pure,Locals.get] <;>
  first | (simp only [add_value,intRes,outside,Bool.false_eq_true,↓reduceIte]; rfl) | rfl

theorem unchecked_overflow {E : Env} {Γ : RCtx} (G : Glob E) (F : Fr) (n : Nat)
 (t : IntTy) (x y : Int) (hx : t.lo≤x ∧ x≤t.hi) (hy : t.lo≤y ∧ y≤t.hi)
 (outside : ¬(t.lo≤x+y ∧ x+y≤t.hi)) (older : Locals E.layout Γ) (state : St E) :
 (evalE G {F with checked:=false} (n+5) (addition t)).run (caller t x y hx hy older,state)=
 (.ok (.val (intWrap t (x+y))),(caller t x y hx hy older,state)) := by
 cases order : G.pipeline <;>
  simp only [addition,caller,evalE,evalPair,withLibraryCalldata,order,Bool.false_eq_true,↓reduceIte] <;>
  dsimp [EM.lift,EM.locals,getV,RVal.get,bind,pure,ExceptT.bind,ExceptT.pure,ExceptT.bindCont,
   ExceptT.run,ExceptT.mk,StateT.bind,StateT.pure,StateT.get,get,getThe,MonadStateOf.get,
   liftM,monadLift,MonadLift.monadLift,ExceptT.lift,Functor.map,StateT.map,
   Except.pure,Locals.get] <;>
  first | (simp only [add_value,intRes,outside,Bool.false_eq_true,↓reduceIte]; rfl) | rfl

theorem in_range {E : Env} {Γ : RCtx} (G : Glob E) (F : Fr) (n : Nat)
 (t : IntTy) (x y : Int) (hx : t.lo≤x ∧ x≤t.hi) (hy : t.lo≤y ∧ y≤t.hi)
 (within : t.lo≤x+y ∧ x+y≤t.hi) (older : Locals E.layout Γ) (state : St E) :
 (evalE G F (n+5) (addition t)).run (caller t x y hx hy older,state)=
 (.ok (.val (.int (x+y) within)),(caller t x y hx hy older,state)) := by
 cases order : G.pipeline <;>
  simp only [addition,caller,evalE,evalPair,withLibraryCalldata,order,Bool.false_eq_true,↓reduceIte] <;>
  dsimp [EM.lift,EM.locals,getV,RVal.get,bind,pure,ExceptT.bind,ExceptT.pure,ExceptT.bindCont,
   ExceptT.run,ExceptT.mk,StateT.bind,StateT.pure,StateT.get,get,getThe,MonadStateOf.get,
   liftM,monadLift,MonadLift.monadLift,ExceptT.lift,Functor.map,StateT.map,
   Except.pure,Locals.get] <;>
  first | (simp only [add_value,intRes,within,Bool.false_eq_true,↓reduceIte]; rfl) | rfl
end Solidity.Lowering.V08.LiteralFailureOverflowReason
