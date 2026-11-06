import Solidity.Backend.InternalFlow.RuntimeFrameScopedSource
import Solidity.Backend.InternalFlow.RuntimeFrameV3ScalarSourceCompiler

/-! Source-aware selection of a checked scalar recursive body inside an
actual block that introduces and drops one unused default primitive local.
The existing recursive body and argument selectors remain checked inputs;
there is no target execution or profile witness in the selection result. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.ScopedScalarCompiler
open Evm Evm.Memory ScalarRecursiveSource

/-- Actual source syntax, using the exact fields of the inner checked call. -/
def wrap {C : Contract} {Γ : Ctx} {b c frame pointer bottom : Nat} {F : Frag Γ}
 {plain : Stmt C Γ Γ} (selected : ScalarSourceCompiler.Selected b c frame pointer bottom F plain)
 (p : PrimTy) (name : Var) : Stmt C Γ Γ :=
 ScalarSourceCompiler.call selected.memoryFree selected.reference selected.count selected.destination
   selected.aliasName selected.countName selected.resultName selected.function selected.depth
   (fun _ => ScopedSource.decorate (selected.child ()) p name)

structure Selected {C : Contract} {Γ : Ctx} (b c frame pointer bottom : Nat) (F : Frag Γ)
 (source : Stmt C Γ Γ) where
 plain : Stmt C Γ Γ
 selected : ScalarSourceCompiler.Selected b c frame pointer bottom F plain
 localType : PrimTy
 localName : Var
 shape : source=wrap selected localType localName

/-- Construct from the actual inspected thunk equation and existing checked
receipts. The equality is source syntax, not a simulation premise. -/
def assemble {C : Contract} {Γ : Ctx} {R : RefTy} {b c frame pointer bottom : Nat} {F : Frag Γ}
 (hm : (Ty.ref R).mapFree=true) (reference : Idx Γ (.mem R)) (count : Val C Γ .uint)
 (destination : Idx Γ (.val .uint)) (aliasName countName resultName : Var) (function : Name)
 (depth : Nat) (child : Unit → Prog C (Frame R) (Frame R))
 (inner : Prog C (Frame R) (Frame R)) (p : PrimTy) (name : Var)
 (shape : child ()=ScopedSource.decorate inner p name)
 (same : inner=ScalarRecursiveSource.body R hm depth)
 (checked : ScalarSourceCheck.check R hm depth inner=some ⟨same⟩)
 (emitted : ScalarEmitter.Emission b c frame pointer bottom F count)
 (root : ScalarEmitter.compile b c frame pointer bottom F count=some emitted) :
 Selected b c frame pointer bottom F
   (ScalarSourceCompiler.call hm reference count destination aliasName countName resultName function depth child) := by
 have childEq : child=(fun _ => ScopedSource.decorate inner p name) :=
   funext (fun point => by cases point;exact shape)
 exact {
   plain:=ScalarSourceCompiler.call hm reference count destination aliasName countName resultName function depth (fun _ => inner)
   selected:=ScalarSourceCompiler.make hm reference count destination aliasName countName resultName function depth (fun _ => inner)
     same checked emitted root
   localType:=p
   localName:=name
   shape:=by
     change ScalarSourceCompiler.call hm reference count destination aliasName countName resultName function depth child=
       ScalarSourceCompiler.call hm reference count destination aliasName countName resultName function depth (fun _ => ScopedSource.decorate inner p name)
     rw [childEq] }

def compileCall {C : Contract} {Γ : Ctx} {R : RefTy} (b c frame pointer bottom : Nat) (F : Frag Γ)
 (hm : (Ty.ref R).mapFree=true) (reference : Idx Γ (.mem R)) (count : Val C Γ .uint)
 (destination : Idx Γ (.val .uint)) (aliasName countName resultName : Var) (function : Name)
 (depth : Nat) (child : Unit → Prog C (Frame R) (Frame R)) :
 Option (Selected b c frame pointer bottom F
   (ScalarSourceCompiler.call hm reference count destination aliasName countName resultName function depth child)) :=
 match shape : child () with
 | .cons (.block (.cons (@Stmt.block _ _ Δ inner) (.cons (.declLocal p name none) .nil))) .nil =>
   if context : Δ=Frame R then by
    subst Δ
    exact match checked : ScalarSourceCheck.check R hm depth inner with
    | none => none
    | some same =>
      match root : ScalarEmitter.compile b c frame pointer bottom F count with
      | none => none
      | some emitted => some (assemble hm reference count destination aliasName countName resultName function depth child
        inner p name shape same.down checked emitted root)
   else none
 | _ => none

def compile {C : Contract} {Γ : Ctx} (b c frame pointer bottom : Nat) (F : Frag Γ)
 (source : Stmt C Γ Γ) : Option (Selected b c frame pointer bottom F source) :=
 match source with
 | .callRec function depth
   (.snoc (.snocMemory .nil R aliasName (.var reference hm)) .uint countName count)
   (.val .uint resultName (some destination)) child =>
   compileCall (R:=R) b c frame pointer bottom F hm reference count destination aliasName countName resultName function depth child
 | _ => none

/-- Actual public selection, sharing the checked inner constructor receipts. -/
theorem compile_decorated {C : Contract} {Γ : Ctx} {R : RefTy} {b c frame pointer bottom : Nat} {F : Frag Γ}
 (hm : (Ty.ref R).mapFree=true) (reference : Idx Γ (.mem R)) (count : Val C Γ .uint)
 (destination : Idx Γ (.val .uint)) (aliasName countName resultName : Var) (function : Name)
 (depth : Nat) (inner : Prog C (Frame R) (Frame R)) (p : PrimTy) (name : Var)
 (same : inner=ScalarRecursiveSource.body R hm depth)
 (checked : ScalarSourceCheck.check R hm depth inner=some ⟨same⟩)
 (emitted : ScalarEmitter.Emission b c frame pointer bottom F count)
 (root : ScalarEmitter.compile b c frame pointer bottom F count=some emitted) :
 compile b c frame pointer bottom F
   (ScalarSourceCompiler.call hm reference count destination aliasName countName resultName function depth
     (fun _ => ScopedSource.decorate inner p name))=
 some (assemble hm reference count destination aliasName countName resultName function depth
   (fun _ => ScopedSource.decorate inner p name) inner p name rfl same checked emitted root) := by
 change compileCall b c frame pointer bottom F hm reference count destination aliasName countName resultName function depth
   (fun _ => ScopedSource.decorate inner p name)=_
 unfold compileCall
 dsimp only [ScopedSource.decorate]
 simp only
 rw [dif_pos True.intro]
 split
 · rename_i absent
   cases absent.symm.trans checked
 · rename_i actual actualRoot
   have equal : actual=⟨same⟩ := Option.some.inj (actualRoot.symm.trans checked)
   subst actual
   split
   · rename_i absent
     cases absent.symm.trans root
   · rename_i actual actualRoot
     have equal : actual=emitted := Option.some.inj (actualRoot.symm.trans root)
     subst actual
     rfl

def Selected.plan {C : Contract} {Γ : Ctx} {b c frame pointer bottom : Nat} {F : Frag Γ}
 {source : Stmt C Γ Γ} (selection : Selected b c frame pointer bottom F source) := selection.selected.plan

theorem Selected.source_run {C : Contract} {Γ : Ctx} {b c frame pointer bottom : Nat} {F : Frag Γ}
 {source : Stmt C Γ Γ} (selection : Selected b c frame pointer bottom F source) (caller : State C Γ) :
 source.run caller=selection.plain.run caller := by
 refine (congrArg (fun statement : Stmt C Γ Γ => statement.run caller) selection.shape).trans ?_
 refine Eq.trans ?_ (congrArg (fun statement : Stmt C Γ Γ => statement.run caller) selection.selected.head).symm
 exact congrFun (ScopedSource.call_run
   (.snoc (.snocMemory .nil selection.selected.R selection.selected.aliasName
     (.var selection.selected.reference selection.selected.memoryFree)) .uint selection.selected.countName selection.selected.count)
   (.val .uint selection.selected.resultName (some selection.selected.destination))
   (selection.selected.child ()) selection.localType selection.localName) caller

theorem Selected.returns {C : Contract} {Γ : Ctx} {b c frame pointer bottom : Nat} {F : Frag Γ}
 {source : Stmt C Γ Γ} (selection : Selected b c frame pointer bottom F source) (below : bottom<pointer) :
 InterfaceV1.ReturnClaim b F source selection.plan := by
 intro L fr caller base before start entry out actual
 exact selection.selected.returns below L fr caller base before start entry out
   ((selection.source_run caller).symm.trans actual)

theorem Selected.bare_revert {C : Contract} {Γ : Ctx} {b c frame pointer bottom : Nat} {F : Frag Γ}
 {source : Stmt C Γ Γ} (selection : Selected b c frame pointer bottom F source) (below : bottom<pointer) :
 InterfaceV1.BareRevertClaim b F source selection.plan := by
 intro L fr caller base before start entry actual
 exact selection.selected.bare_revert below L fr caller base before start entry
   ((selection.source_run caller).symm.trans actual)

end Solidity.Backend.InternalFlow.RuntimeFrame.ScopedScalarCompiler
