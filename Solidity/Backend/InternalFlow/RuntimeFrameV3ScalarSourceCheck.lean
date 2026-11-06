import Solidity.Backend.InternalFlow.RuntimeFrameV3ScalarRecursiveSource

/-! Exact source-syntax recognition for the existing scalar recursive family.
The checker inspects the supplied quotation and its child thunks; its only
recursion index is the quotation index already carried by the source. It
introduces no runtime cutoff, evaluator, source admission or target oracle. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.ScalarSourceCheck
open ScalarRecursiveSource

def checkGuard {C : Contract} {R : RefTy} (value : Val C (Frame R) .bool) :
 Option (PLift (value=ScalarRecursiveSource.guard)) :=
 match value with
 | .binop .gt _ _ (.simple (.local (.there .here))) (.simple (.lit n _)) =>
   if h : n=0 then some ⟨by simp only [ScalarRecursiveSource.guard,h]⟩ else none
 | _ => none

def checkZero {C : Contract} {R : RefTy} (statement : Stmt C (Frame R) (Frame R)) :
 Option (PLift (statement=zero)) :=
 match statement with
 | .assignLocal .here (.simple (.lit n _)) =>
   if h : n=0 then some ⟨by simp only [zero,h]⟩ else none
 | _ => none

def checkIncrement {C : Contract} {R : RefTy} (statement : Stmt C (Frame R) (Frame R)) :
 Option (PLift (statement=increment)) :=
 match statement with
 | .assignLocal .here (.binop .add _ _ (.simple (.local .here)) (.simple (.lit n _))) =>
   if h : n=1 then some ⟨by simp only [increment,h]⟩ else none
 | _ => none

def checkNext {C : Contract} {R : RefTy} (hm : (Ty.ref R).mapFree=true)
 (args : Args C (Frame R) (RecursiveSource.Parameters R)) : Option (PLift (args=next R hm)) :=
 match args with
 | .snoc (.snocMemory .nil _ x (.var (.there (.there .here)) _)) .uint y
     (.binop .sub _ _ (.simple (.local (.there .here))) (.simple (.lit n _))) =>
   if hx : x=.user "alias" then
     if hy : y=.user "count" then
       if hn : n=1 then some ⟨by simp only [next,hx,hy,hn]⟩ else none
     else none
   else none
 | _ => none

def checkResult {R : RefTy} (ret : CallRet (Frame R) [.val .uint] (Frame R)) :
 Option (PLift (ret=result R)) :=
 match ret with
 | .val .uint name (some .here) =>
   if h : name=.user "result" then some ⟨by simp only [result,h]⟩ else none
 | _ => none

/-- One inspected layer, retaining the actual child thunk. The shape field
is constructed by syntax matching; it does not assert anything about the
child or target execution. -/
structure Head {C : Contract} (R : RefTy) (hm : (Ty.ref R).mapFree=true)
 (program : Prog C (Frame R) (Frame R)) where
 index : Nat
 child : Unit → Prog C (Frame R) (Frame R)
 shape : program=step R hm index child

def readHead {C : Contract} (R : RefTy) (hm : (Ty.ref R).mapFree=true)
 (program : Prog C (Frame R) (Frame R)) : Option (Head R hm program) :=
 match program with
 | .cons (.ite condition
     (.cons (.callRec name index
       (.snoc (.snocMemory .nil _ aliasName (.var (.there (.there .here)) actualHm)) .uint countName countExpr)
       (.val .uint resultName (some .here)) child)
       (.cons (.assignLocal .here advanceExpr) .nil))
     (.cons (.assignLocal .here emptyExpr) .nil)) .nil => do
   let guardEq ← checkGuard condition
   let argsEq ← checkNext hm (.snoc (.snocMemory .nil R aliasName (.var (.there (.there .here)) actualHm)) .uint countName countExpr)
   let retEq ← checkResult (R:=R) (.val .uint resultName (some .here))
   let advanceEq ← checkIncrement (C:=C) (R:=R) (.assignLocal .here advanceExpr)
   let emptyEq ← checkZero (C:=C) (R:=R) (.assignLocal .here emptyExpr)
   if nameEq : name="scalarCountdown" then
     pure ⟨index,child,by
       rw [guardEq.down,argsEq.down,retEq.down,advanceEq.down,emptyEq.down,nameEq]
       rfl⟩
   else none
 | _ => none

def checkBase {C : Contract} {R : RefTy} (program : Prog C (Frame R) (Frame R)) :
 Option (PLift (program=Prog.recBase)) :=
 match program with
 | .cons .assumeFalse .nil => some ⟨rfl⟩
 | _ => none

theorem step_eq {C : Contract} {R : RefTy} (hm : (Ty.ref R).mapFree=true)
 (depth : Nat) (child : Unit → Prog C (Frame R) (Frame R))
 (same : child ()=body R hm depth) : step R hm depth child=body R hm (depth+1) := by
 have thunkEq : child=(fun _ => body R hm depth) := funext (fun point => by cases point;exact same)
 rw [thunkEq]
 rfl

/-- Recursive verification visits every actual child at the supplied source
quotation index. No independent runtime/admission cutoff is introduced. -/
def check {C : Contract} (R : RefTy) (hm : (Ty.ref R).mapFree=true) :
 (depth : Nat) → (program : Prog C (Frame R) (Frame R)) → Option (PLift (program=body R hm depth))
 | 0, program => checkBase program
 | depth+1, program => do
   let head ← readHead R hm program
   if indexEq : head.index=depth then
     let childEq ← check R hm depth (head.child ())
     pure ⟨head.shape.trans (by rw [indexEq];exact step_eq hm depth head.child childEq.down)⟩
   else none

end Solidity.Backend.InternalFlow.RuntimeFrame.ScalarSourceCheck
