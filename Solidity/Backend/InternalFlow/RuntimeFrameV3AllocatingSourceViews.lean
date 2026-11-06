import Solidity.Backend.InternalFlow.RuntimeFrameV3AllocatingSourceCertificate

/-! The read views generalize context indices over actual intrinsic syntax. Views keep
all source contexts and constructor equations. No indexed AST match, untyped
IR, source evaluator, target assumption or compiler admission is introduced.
The executable base checker certifies only the exact existing recBase. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingSourceViews
open Evm Evm.Memory RecursiveSource ScalarRecursiveSource

structure ConsView {C : Contract} {Γ Δ : Ctx} (source : Prog C Γ Δ) where
 middle : Ctx
 head : Stmt C Γ middle
 tail : Prog C middle Δ
 shape : source=.cons head tail

def readCons {C : Contract} {Γ Δ : Ctx} (source : Prog C Γ Δ) : Option (ConsView source) :=
 Prog.casesOn (motive_2:=fun _ _ source => Option (ConsView source)) source
   none (fun head tail => some ⟨_,head,tail,rfl⟩)

def readNil {C : Contract} {Γ Δ : Ctx} (source : Prog C Γ Δ) :
 Option (PLift (HEq source (.nil : Prog C Γ Γ))) :=
 Prog.casesOn (motive_2:=fun Γ _ source => Option (PLift (HEq source (.nil : Prog C Γ Γ)))) source
   (some ⟨HEq.rfl⟩) (fun _ _ => none)

def readAssumeFalse {C : Contract} {Γ Δ : Ctx} (source : Stmt C Γ Δ) :
 Option (PLift (HEq source (.assumeFalse : Stmt C Γ Γ))) :=
 Stmt.casesOn (motive_1:=fun Γ _ source => Option (PLift (HEq source (.assumeFalse : Stmt C Γ Γ)))) source
   (assign := by intros;exact none)
   (rebind := by intros;exact none)
   (assignLocal := by intros;exact none)
   (declLocal := by intros;exact none)
   (declStorage := by intros;exact none)
   (opAssign := by intros;exact none)
   (incDec := by intros;exact none)
   (assignIncDec := by intros;exact none)
   (assignLocalPush := by intros;exact none)
   (push := by intros;exact none)
   (pop := by intros;exact none)
   (transfer := by intros;exact none)
   (send := by intros;exact none)
   (declMem := by intros;exact none)
   (rebindMem := by intros;exact none)
   (assignFromMem := by intros;exact none)
   (assignMem := by intros;exact none)
   (delete := by intros;exact none)
   (deleteMem := by intros;exact none)
   (assignNew := by intros;exact none)
   (ite := by intros;exact none)
   (require := by intros;exact none)
   (assert := by intros;exact none)
   (revert := by intros;exact none)
   (assumeFalse := by intros;exact some ⟨HEq.rfl⟩)
   (call := by intros;exact none)
   (tryCall := by intros;exact none)
   (loop := by intros;exact none)
   (block := by intros;exact none)
   (pushOpAssign := by intros;exact none)
   (pushIncDec := by intros;exact none)
   (callReceiver := by intros;exact none)
   (callReceiverPush := by intros;exact none)
   (callRec := by intros;exact none)
   (revertData := by intros;exact none)
   (catchData := by intros;exact none)

theorem context_eq {Γ Δ : Ctx} (forward : Ext Γ Δ) (backward : Ext Δ Γ) : Γ=Δ := by
 cases forward with
 | refl => rfl
 | push previous =>
   have first := previous.length_eq
   have second := backward.length_eq
   simp only [List.length_cons] at second
   omega

structure ClosedCons {C : Contract} {Γ : Ctx} (source : Prog C Γ Γ) where
 head : Stmt C Γ Γ
 tail : Prog C Γ Γ
 shape : source=.cons head tail

def closeCons {C : Contract} {Γ : Ctx} {source : Prog C Γ Γ} (observed : ConsView source) : ClosedCons source := by
 rcases observed with ⟨middle,head,tail,shape⟩
 have same : middle=Γ := context_eq tail.ext head.ext
 subst middle
 exact ⟨head,tail,shape⟩

def readClosedCons {C : Contract} {Γ : Ctx} (source : Prog C Γ Γ) : Option (ClosedCons source) :=
 (readCons source).map closeCons

def checkBase {C : Contract} {Γ : Ctx} (source : Prog C Γ Γ) : Option (PLift (source=Prog.recBase)) := do
 let observed ← readClosedCons source
 let headEq ← readAssumeFalse observed.head
 let tailEq ← readNil observed.tail
 pure ⟨observed.shape.trans (by rw [eq_of_heq headEq.down,eq_of_heq tailEq.down];rfl)⟩

def certifyBase {C : Contract} (R : RefTy) (hm : (Ty.ref R).mapFree=true) (source : Prog C (Frame R) (Frame R)) :
 Option (PLift (AllocatingSourceCertificate.Certificate R hm 0 source)) := do
 let checked ← checkBase source
 pure ⟨checked.down.symm ▸ AllocatingSourceCertificate.Certificate.base⟩

end Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingSourceViews
/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingSourceViews.context_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatingSourceViews.context_eq
