import Solidity.Backend.InternalFlow.RuntimeFrameV3EffectfulSourceCheck
import Solidity.Backend.InternalFlow.RuntimeFrameV3OrderedCalleeFailure

/-! A checked source selector for the existing write-then-scalar-recursion
family. Actual call fields and the whole child quotation are inspected;
count code comes from the public memory compiler. Geometry, runtime capacity
and original approved-profile provenance remain separate obligations. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.EffectfulSourceSelection
open Evm Evm.Memory RecursiveSource ScalarRecursiveSource
abbrev A := EffectfulScalarSource.A

def call {C : Contract} {Γ : Ctx} (reference : Idx Γ (.mem A)) (count : Val C Γ .uint)
 (destination : Idx Γ (.val .uint)) (aliasName countName resultName : Var)
 (function : Name) (depth : Nat) (child : Unit → Prog C (Frame A) (Frame A)) : Stmt C Γ Γ :=
 .callRec function depth
   (.snoc (.snocMemory .nil A aliasName (.var reference rfl)) .uint countName count)
   (.val .uint resultName (some destination)) child

/-- Extracted fields, actual syntax equality and compiler receipts only.
    No execution claim or pending producer premise is stored. -/
structure Selected {C : Contract} {Γ : Ctx} (b : Nat) (F : Frag Γ) (source : Stmt C Γ Γ) where
 reference : Idx Γ (.mem A)
 count : Val C Γ .uint
 destination : Idx Γ (.val .uint)
 aliasName : Var
 countName : Var
 resultName : Var
 function : Name
 depth : Nat
 child : Unit → Prog C (Frame A) (Frame A)
 head : source=call reference count destination aliasName countName resultName function depth child
 body_eq : child ()=EffectfulScalarSource.body depth
 checked : EffectfulSourceCheck.check depth (child ())=some ⟨body_eq⟩
 value : CompiledVal b F count
 value_root : Memory.compileVal b F count=some value

def make {C : Contract} {Γ : Ctx} {b : Nat} {F : Frag Γ}
 (reference : Idx Γ (.mem A)) (count : Val C Γ .uint) (destination : Idx Γ (.val .uint))
 (aliasName countName resultName : Var) (function : Name) (depth : Nat)
 (child : Unit → Prog C (Frame A) (Frame A))
 (same : child ()=EffectfulScalarSource.body depth)
 (checked : EffectfulSourceCheck.check depth (child ())=some ⟨same⟩)
 (value : CompiledVal b F count) (root : Memory.compileVal b F count=some value) :
 Selected b F (call reference count destination aliasName countName resultName function depth child) :=
 ⟨reference,count,destination,aliasName,countName,resultName,function,depth,child,rfl,same,checked,value,root⟩

def compileCall {C : Contract} {Γ : Ctx} (b : Nat) (F : Frag Γ)
 (reference : Idx Γ (.mem A)) (count : Val C Γ .uint) (destination : Idx Γ (.val .uint))
 (aliasName countName resultName : Var) (function : Name) (depth : Nat)
 (child : Unit → Prog C (Frame A) (Frame A)) :
 Option (Selected b F (call reference count destination aliasName countName resultName function depth child)) :=
 match checked : EffectfulSourceCheck.check depth (child ()) with
 | none => none
 | some observed =>
   match root : Memory.compileVal b F count with
   | none => none
   | some value => some (make reference count destination aliasName countName resultName function depth child
       observed.down checked value root)

def compile {C : Contract} {Γ : Ctx} (b : Nat) (F : Frag Γ) (source : Stmt C Γ Γ) :
 Option (Selected b F source) :=
 match source with
 | .callRec function depth
     (.snoc (.snocMemory .nil (.array (.prim .uint)) aliasName (.var reference _)) .uint countName count)
     (.val .uint resultName (some destination)) child =>
   compileCall b F reference count destination aliasName countName resultName function depth child
 | _ => none

theorem compile_call {C : Contract} {Γ : Ctx} {b : Nat} {F : Frag Γ}
 (reference : Idx Γ (.mem A)) (count : Val C Γ .uint) (destination : Idx Γ (.val .uint))
 (aliasName countName resultName : Var) (function : Name) (depth : Nat)
 (child : Unit → Prog C (Frame A) (Frame A))
 (same : child ()=EffectfulScalarSource.body depth)
 (checked : EffectfulSourceCheck.check depth (child ())=some ⟨same⟩)
 (value : CompiledVal b F count) (root : Memory.compileVal b F count=some value) :
 compile b F (call reference count destination aliasName countName resultName function depth child)=
 some (make reference count destination aliasName countName resultName function depth child same checked value root) := by
 change compileCall b F reference count destination aliasName countName resultName function depth child=_
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
     have sameActual : actual=value := Option.some.inj (actualRoot.symm.trans root)
     subst actual
     rfl

def Selected.code {C : Contract} {Γ : Ctx} {b : Nat} {F : Frag Γ} {source : Stmt C Γ Γ}
 (selected : Selected b F source) (c pointer bottom : Nat) : List Instr :=
 OrderedEffectfulScalar.code b c selected.reference selected.value selected.destination pointer bottom

theorem Selected.source_run {C : Contract} {Γ : Ctx} {b : Nat} {F : Frag Γ} {source : Stmt C Γ Γ}
 (selected : Selected b F source) (caller : State C Γ) :
 source.run caller=(OrderedEffectfulScalar.call selected.reference selected.count selected.destination
   selected.function selected.depth).run caller := by
 refine (congrArg (fun statement : Stmt C Γ Γ => statement.run caller) selected.head).trans ?_
 change TRun.call
   (.snoc (.snocMemory .nil A selected.aliasName (.var selected.reference rfl)) .uint selected.countName selected.count)
   (.val .uint selected.resultName (some selected.destination)) (selected.child ()).ext (selected.child ()).runR caller=
   TRun.call (DisjointScalarEntry.args rfl selected.reference selected.count)
     (.val .uint (.user "result") (some selected.destination))
     (EffectfulScalarSource.body (C:=C) selected.depth).ext
     (EffectfulScalarSource.body (C:=C) selected.depth).runR caller
 rw [selected.body_eq]
 rfl

/-- This is the public callee selector used by the selected image, independent
    of quotation depth. It does not replace the checked whole child. -/
theorem Selected.callee_root {C : Contract} {Γ : Ctx} {b : Nat} {F : Frag Γ} {source : Stmt C Γ Γ}
 (_selected : Selected b F source) (c : Nat) :
 (Memory.compileStmt c (Frag.init (Frame A)) (EffectfulScalarSource.write (C:=C))).map (fun checked => checked.code)=
 some (OrderedEffectfulScalar.calleeCode (C:=C) c) := OrderedEffectfulScalar.callee_public_root c

theorem Selected.callee_failure {C : Contract} {Γ : Ctx} {b : Nat} {F : Frag Γ} {source : Stmt C Γ Γ}
 (selected : Selected b F source) {L c frame : Nat}
 (caller : State C Γ) (ref : HRef caller.H A) (alias : TEnv.get selected.reference caller.env=some ref)
 (n : Nat) (bound : n<W) (evaluated : selected.count.evalT caller=.ok (countValue n bound))
 (failed : caller.heap.writeAddr (.index ref .dyn (countValue 0 W_pos)) EffectfulScalarSource.replacement=none)
 (base : Nat → Fin W) (before : Machine) (repr : StateRepr L b frame F caller base before)
 (disjoint : b+Γ.length≤c) (space : c+3≤frame) (pointer bottom : Nat) :
 source.run caller=.error .revert ∧ (∀ suffix,run (selected.code c pointer bottom++suffix) before=.revert) := by
 have actual := OrderedCalleeFailure.transport (c:=c) caller selected.reference ref alias selected.count selected.value
   n bound evaluated failed base before repr disjoint space
 obtain ⟨entered,entryRun,childRepr,callerRepr,stack,referenceWord,counterWord,resultWord,outside,growth,bodyFailure,sourceFailure,targetFailure⟩ := actual.2
 exact ⟨(selected.source_run caller).trans (sourceFailure selected.function selected.depth selected.destination),
   targetFailure selected.destination pointer bottom⟩


theorem Selected.argument_failure {C : Contract} {Γ : Ctx} {b : Nat} {F : Frag Γ} {source : Stmt C Γ Γ}
 (selected : Selected b F source) {L c frame : Nat}
 (caller : State C Γ) (failed : selected.count.evalT caller=.error .revert)
 (base : Nat → Fin W) (before : Machine) (repr : StateRepr L b frame F caller base before)
 (disjoint : b+Γ.length≤c) (space : c+3≤frame) (pointer bottom : Nat) :
 source.run caller=.error .revert ∧ (∀ suffix,run (selected.code c pointer bottom++suffix) before=.revert) := by
 have actual := OrderedArgumentFailure.transport (c:=c) caller selected.reference selected.count selected.value failed
   base before repr disjoint space
 exact ⟨(selected.source_run caller).trans (actual.2.1 selected.function selected.depth selected.destination),
   actual.2.2 selected.destination pointer bottom⟩

end Solidity.Backend.InternalFlow.RuntimeFrame.EffectfulSourceSelection
