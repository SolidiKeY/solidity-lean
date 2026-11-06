import Solidity.Backend.InternalFlow.RuntimeFrameV3AllocatingHeadViews

/-! Exact recognition of the existing unused-default-local decorator.
Readers keep the actual inner program and every context/constructor equation.
No indexed AST match, evaluator, execution or compiler premise is introduced. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScopeView
open Evm Evm.Memory AllocatingHeadViews

structure Declaration {C : Contract} {Γ Δ : Ctx} (source : Stmt C Γ Δ) : Type where
 primitive : PrimTy
 name : Var
 initial : Option (Val C Γ primitive)
 output : Δ=.val primitive::Γ
 shape : HEq source (Stmt.declLocal primitive name initial)

def readDeclaration {C : Contract} {Γ Δ : Ctx} (source : Stmt C Γ Δ) : Option (Declaration source) :=
 Stmt.casesOn (motive_1:=fun _ _ source => Option (Declaration source)) source
   (declLocal:=fun primitive name initial => some ⟨primitive,name,initial,rfl,HEq.rfl⟩)
   (assign:=by intros;exact none)
   (rebind:=by intros;exact none)
   (assignLocal:=by intros;exact none)
   (declStorage:=by intros;exact none)
   (opAssign:=by intros;exact none)
   (incDec:=by intros;exact none)
   (assignIncDec:=by intros;exact none)
   (assignLocalPush:=by intros;exact none)
   (push:=by intros;exact none)
   (pop:=by intros;exact none)
   (transfer:=by intros;exact none)
   (send:=by intros;exact none)
   (declMem:=by intros;exact none)
   (rebindMem:=by intros;exact none)
   (assignFromMem:=by intros;exact none)
   (assignMem:=by intros;exact none)
   (delete:=by intros;exact none)
   (deleteMem:=by intros;exact none)
   (assignNew:=by intros;exact none)
   (ite:=by intros;exact none)
   (require:=by intros;exact none)
   (assert:=by intros;exact none)
   (revert:=by intros;exact none)
   (assumeFalse:=by intros;exact none)
   (call:=by intros;exact none)
   (tryCall:=by intros;exact none)
   (loop:=by intros;exact none)
   (block:=by intros;exact none)
   (pushOpAssign:=by intros;exact none)
   (pushIncDec:=by intros;exact none)
   (callReceiver:=by intros;exact none)
   (callReceiverPush:=by intros;exact none)
   (callRec:=by intros;exact none)
   (revertData:=by intros;exact none)
   (catchData:=by intros;exact none)

structure ClosedBlock {C : Contract} {Γ Δ : Ctx} (source : Stmt C Γ Δ) : Type where
 body : Prog C Γ Γ
 output : Δ=Γ
 shape : HEq source (Stmt.block body)

def closeBlock {C : Contract} {Γ Δ : Ctx} {source : Stmt C Γ Δ}
 (view : Block source) (same : view.inside=Γ) : ClosedBlock source := by
 rcases view with ⟨inside,body,output,shape⟩
 simp only [] at same
 subst inside
 exact ⟨body,output,shape⟩

structure Scope {C : Contract} {Γ : Ctx} (source : Prog C Γ Γ) : Type where
 body : Prog C Γ Γ
 primitive : PrimTy
 name : Var
 shape : source=ScopedSource.decorate body primitive name

def assemble {C : Contract} {Γ : Ctx} {source : Prog C Γ Γ}
 (root : AllocatingSourceViews.ClosedCons source) (rootEnd : NilView root.tail)
 (outer : Block root.head) (parts : AllocatingSourceViews.ConsView outer.body)
 (inner : ClosedBlock parts.head) (rest : AllocatingSourceViews.ConsView parts.tail)
 (declaration : Declaration rest.head) (ending : NilView rest.tail)
 (initialEq : declaration.initial=none) : Scope source := by
 rcases root with ⟨head,tail,rootShape⟩
 rcases rootEnd with ⟨rootOutput,rootNil⟩
 rcases outer with ⟨inside,body,outerOutput,outerShape⟩
 rcases parts with ⟨middle,first,remaining,bodyShape⟩
 rcases inner with ⟨actualBody,middleOutput,innerShape⟩
 rcases rest with ⟨next,localHead,localTail,restShape⟩
 rcases declaration with ⟨primitive,name,initial,nextOutput,declarationShape⟩
 rcases ending with ⟨insideOutput,endingShape⟩
 simp only [] at *
 have middleEq : middle=Γ := middleOutput
 subst middle
 have nextEq : next=.val primitive::Γ := nextOutput
 have insideEq : inside=.val primitive::Γ := insideOutput.trans nextEq
 clear insideOutput
 subst next
 simp only [] at *
 subst inside
 subst initial
 have headEq : head=Stmt.block body := eq_of_heq outerShape
 have bodyEq : body=Prog.cons first remaining := bodyShape
 have firstEq : first=Stmt.block actualBody := eq_of_heq innerShape
 have remainingEq : remaining=Prog.cons localHead localTail := restShape
 have localEq : localHead=Stmt.declLocal primitive name none := eq_of_heq declarationShape
 have localTailEq : localTail=(.nil : Prog C (.val primitive::Γ) (.val primitive::Γ)) := eq_of_heq endingShape
 have tailEq : tail=(.nil : Prog C Γ Γ) := eq_of_heq rootNil
 refine ⟨actualBody,primitive,name,?_⟩
 simp only [ScopedSource.decorate,rootShape,headEq,bodyEq,firstEq,remainingEq,localEq,localTailEq,tailEq]

def read {C : Contract} {Γ : Ctx} (source : Prog C Γ Γ) : Option (Scope source) := do
 let root ← AllocatingSourceViews.readClosedCons source
 let rootEnd ← readNil root.tail
 let outer ← readBlock root.head
 let parts ← AllocatingSourceViews.readCons outer.body
 let rawInner ← readBlock parts.head
 if innerContext : rawInner.inside=Γ then
   let inner := closeBlock rawInner innerContext
   let rest ← AllocatingSourceViews.readCons parts.tail
   let declaration ← readDeclaration rest.head
   let ending ← readNil rest.tail
   match initialEq : declaration.initial with
   | none => pure (assemble root rootEnd outer parts inner rest declaration ending initialEq)
   | some _ => none
 else none

end Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScopeView
/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScopeView.closeBlock' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScopeView.closeBlock
/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScopeView.assemble' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingScopeView.assemble
