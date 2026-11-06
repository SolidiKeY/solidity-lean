import Solidity.Backend.InternalFlow.RuntimeFrameV3RecursiveScopeLaws
import Solidity.Backend.InternalFlow.RuntimeFrameV3ScalarSourceCompiler
import Solidity.Backend.InternalFlow.RuntimeFrameV3ScalarDemandClaims

/-! Actual call selection with complete semantic recognition of optional
scopes inside every recursive quotation level. Existing target return and
bare-revert claims are reused only after the actual full source execution
equality is proved; general profile and failure/termination closure stay open. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.RecursiveScopeCompiler
open Evm Evm.Memory ScalarRecursiveSource

open ScalarSourceCompiler (call)

/-- All fields are extracted data or proved source/compiler equations.
There is no target simulation, caller whitelist or pending proof field. -/
structure Selected {C : Contract} {Γ : Ctx} (b c frame pointer bottom : Nat)
 (F : Frag Γ) (source : Stmt C Γ Γ) where
 R : RefTy
 memoryFree : (Ty.ref R).mapFree=true
 reference : Idx Γ (.mem R)
 count : Val C Γ .uint
 destination : Idx Γ (.val .uint)
 aliasName : Var
 countName : Var
 resultName : Var
 function : Name
 depth : Nat
 child : Unit → Prog C (Frame R) (Frame R)
 head : source=call memoryFree reference count destination aliasName countName resultName function depth child
 body_run : (child ()).runR=(ScalarRecursiveSource.body R memoryFree depth).runR
 checked : RecursiveScopes.check R memoryFree depth (child ())=some ⟨body_run⟩
 emitted : ScalarEmitter.Emission b c frame pointer bottom F count
 emitted_root : ScalarEmitter.compile b c frame pointer bottom F count=some emitted

def make {C : Contract} {Γ : Ctx} {R : RefTy} {b c frame pointer bottom : Nat}
 {F : Frag Γ} (hm : (Ty.ref R).mapFree=true) (reference : Idx Γ (.mem R))
 (count : Val C Γ .uint) (destination : Idx Γ (.val .uint)) (aliasName countName resultName : Var)
 (function : Name) (depth : Nat) (child : Unit → Prog C (Frame R) (Frame R))
 (same : (child ()).runR=(ScalarRecursiveSource.body R hm depth).runR)
 (checked : RecursiveScopes.check R hm depth (child ())=some ⟨same⟩)
 (emitted : ScalarEmitter.Emission b c frame pointer bottom F count)
 (root : ScalarEmitter.compile b c frame pointer bottom F count=some emitted) :
 Selected b c frame pointer bottom F (call hm reference count destination aliasName countName resultName function depth child) :=
 { R:=R,memoryFree:=hm,reference:=reference,count:=count,destination:=destination,
   aliasName:=aliasName,countName:=countName,resultName:=resultName,function:=function,
   depth:=depth,child:=child,head:=rfl,body_run:=same,checked:=checked,emitted:=emitted,emitted_root:=root }

def compileCall {C : Contract} {Γ : Ctx} {R : RefTy} (b c frame pointer bottom : Nat)
 (F : Frag Γ) (hm : (Ty.ref R).mapFree=true) (reference : Idx Γ (.mem R))
 (count : Val C Γ .uint) (destination : Idx Γ (.val .uint)) (aliasName countName resultName : Var)
 (function : Name) (depth : Nat) (child : Unit → Prog C (Frame R) (Frame R)) :
 Option (Selected b c frame pointer bottom F
   (call hm reference count destination aliasName countName resultName function depth child)) :=
 match checked : RecursiveScopes.check R hm depth (child ()) with
 | none => none
 | some observed =>
   match root : ScalarEmitter.compile b c frame pointer bottom F count with
   | none => none
   | some emitted => some (make hm reference count destination aliasName countName resultName function depth child observed.down checked emitted root)

def compile {C : Contract} {Γ : Ctx} (b c frame pointer bottom : Nat)
 (F : Frag Γ) (source : Stmt C Γ Γ) : Option (Selected b c frame pointer bottom F source) :=
 match source with
 | .callRec function depth
     (.snoc (.snocMemory .nil R aliasName (.var reference hm)) .uint countName count)
     (.val .uint resultName (some destination)) child =>
   compileCall (R:=R) b c frame pointer bottom F hm reference count destination aliasName countName resultName function depth child
 | _ => none

/-- A small public constructor equation preserves the actual body check and
public argument-selection receipt without reducing independent certificates. -/
theorem compile_call {C : Contract} {Γ : Ctx} {R : RefTy} {b c frame pointer bottom : Nat}
 {F : Frag Γ} (hm : (Ty.ref R).mapFree=true) (reference : Idx Γ (.mem R))
 (count : Val C Γ .uint) (destination : Idx Γ (.val .uint)) (aliasName countName resultName : Var)
 (function : Name) (depth : Nat) (child : Unit → Prog C (Frame R) (Frame R))
 (same : (child ()).runR=(ScalarRecursiveSource.body R hm depth).runR)
 (checked : RecursiveScopes.check R hm depth (child ())=some ⟨same⟩)
 (emitted : ScalarEmitter.Emission b c frame pointer bottom F count)
 (root : ScalarEmitter.compile b c frame pointer bottom F count=some emitted) :
 compile b c frame pointer bottom F (call hm reference count destination aliasName countName resultName function depth child)=
 some (make hm reference count destination aliasName countName resultName function depth child same checked emitted root) := by
 change compileCall b c frame pointer bottom F hm reference count destination aliasName countName resultName function depth child=_
 unfold compileCall
 split
 · rename_i absent
   have impossible := absent.symm.trans checked
   cases impossible
 · rename_i observed observedRoot
   have sameObserved : observed=⟨same⟩ := Option.some.inj (observedRoot.symm.trans checked)
   subst observed
   split
   · rename_i absent
     have impossible := absent.symm.trans root
     cases impossible
   · rename_i actual actualRoot
     have sameActual : actual=emitted := Option.some.inj (actualRoot.symm.trans root)
     subst actual
     rfl

def Selected.plan {C : Contract} {Γ : Ctx} {b c frame pointer bottom : Nat}
 {F : Frag Γ} {source : Stmt C Γ Γ} (selected : Selected b c frame pointer bottom F source) :
 InterfaceV1.Emission C Γ Γ :=
 (ScalarDemand.plan selected.emitted selected.reference selected.destination).at selected.depth

/-- Parameter names are retained in the actual syntax. The existing native
call evaluator ignores these binder labels; its arguments and return binder
remain the same typed ones, and the checked full body-execution equality is applied. -/
theorem Selected.source_run {C : Contract} {Γ : Ctx} {b c frame pointer bottom : Nat}
 {F : Frag Γ} {source : Stmt C Γ Γ} (selected : Selected b c frame pointer bottom F source)
 (caller : State C Γ) :
 source.run caller=(DisjointScalarReturn.call selected.memoryFree selected.reference selected.count
   selected.destination selected.function selected.depth).run caller := by
 refine (congrArg (fun statement : Stmt C Γ Γ => statement.run caller) selected.head).trans ?_
 change TRun.call
   (.snoc (.snocMemory .nil selected.R selected.aliasName (.var selected.reference selected.memoryFree)) .uint selected.countName selected.count)
   (.val .uint selected.resultName (some selected.destination)) (selected.child ()).ext (selected.child ()).runR caller=
   TRun.call (DisjointScalarEntry.args selected.memoryFree selected.reference selected.count)
     (.val .uint (.user "result") (some selected.destination))
     (ScalarRecursiveSource.body (C:=C) selected.R selected.memoryFree selected.depth).ext
     (ScalarRecursiveSource.body (C:=C) selected.R selected.memoryFree selected.depth).runR caller
 have scope : (selected.child ()).ext=(ScalarRecursiveSource.body (C:=C) selected.R selected.memoryFree selected.depth).ext := Subsingleton.elim _ _
 rw [scope,selected.body_run]
 rfl

theorem Selected.value_root {C : Contract} {Γ : Ctx} {b c frame pointer bottom : Nat}
 {F : Frag Γ} {source : Stmt C Γ Γ} (selected : Selected b c frame pointer bottom F source) :
 Memory.compileVal b F selected.count=some selected.emitted.value :=
 ScalarEmitter.selected_value selected.emitted_root

theorem Selected.returns {C : Contract} {Γ : Ctx} {b c frame pointer bottom : Nat}
 {F : Frag Γ} {source : Stmt C Γ Γ} (selected : Selected b c frame pointer bottom F source)
 (below : bottom<pointer) : InterfaceV1.ReturnClaim b F source selected.plan := by
 intro L fr caller base before start entry out actual
 apply ScalarDemand.returns selected.emitted below selected.memoryFree selected.reference selected.destination
   selected.function selected.depth L fr caller base before start entry out
 exact (selected.source_run caller).symm.trans actual

theorem Selected.bare_revert {C : Contract} {Γ : Ctx} {b c frame pointer bottom : Nat}
 {F : Frag Γ} {source : Stmt C Γ Γ} (selected : Selected b c frame pointer bottom F source)
 (below : bottom<pointer) : InterfaceV1.BareRevertClaim b F source selected.plan := by
 intro L fr caller base before start entry actual
 apply ScalarDemand.bare_revert selected.emitted below selected.memoryFree selected.reference selected.destination
   selected.function selected.depth L fr caller base before start entry
 exact (selected.source_run caller).symm.trans actual

end Solidity.Backend.InternalFlow.RuntimeFrame.RecursiveScopeCompiler
