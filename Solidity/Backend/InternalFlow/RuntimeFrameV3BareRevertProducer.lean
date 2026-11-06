import Solidity.Backend.InternalFlow.RuntimeFrameInterfaceV3
import Solidity.Backend.InternalFlow.RuntimeFrameNoneProducer
import Solidity.Backend.InternalFlow.RuntimeFrameMutation
import Solidity.Evm.MemoryCompileExamples

/-! Failure-only V3 producers over a typed physical initial-input domain.
Universal Entry coverage and bare-revert target execution reuse the existing
checked program/capture laws. Populated direct-OOB and callee-OOB applications
supply actual admitted source failures. Approved-profile provenance remains
EXACTLY the external frozen V3 AdmissionAgreement hypothesis; no approved
judgment, success claim, rollback, panic/payload or exhaustion proof is added. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.V3BareRevertProducer
open Evm Evm.Memory
section
variable {C : Contract} {Γ Δ : Ctx} {b : Nat} {F : Frag Γ} {P : Prog C Γ Δ}

/-- Typed initial inputs: the `Entry` resource fields restated (indexed by the
selected code's `need`/`cost`), so `coverage` is a repackaging.
Neither a finite whitelist nor a desired-success condition occurs here. -/
structure InitialInput (need resultCells lo pointer cost : Nat)
 (L frame : Nat) (caller : State C Γ) (base : Nat → Fin W)
 (machine : Machine) (start : Nat) : Prop where
 represented : StateRepr L b frame F caller base machine
 locals : b+Γ.length≤lo
 results : b+resultCells≤lo
 workspace : b+need≤lo
 pointerAbove : lo≤pointer
 pointerBelow : pointer<frame
 payloadAbove : lo≤start
 reserve : start+(Γ.length+1)≤frame
 separate : pointer<start ∨ start+(Γ.length+1)≤pointer
 noWrap : start+(Γ.length+1)<W
 cursor : machine.mem pointer=.val (wmod start)
 capacity : AllocationInput b frame cost caller base machine

def admitted (selected : Composition.Program b F P) (lo pointer : Nat) :
 InterfaceV3.Admission C Γ := fun L frame caller base machine start =>
 InitialInput (b := b) (F := F) selected.checked.need Δ.length lo pointer
  (selected.checked.cost caller) L frame caller base machine start

/-- Concrete capture/body/restore code. Bare failure absorbs the restore suffix,
as proved below; no unwind execution or world rollback is inferred. -/
def plan (selected : Composition.Program b F P) (lo pointer : Nat) :
 InterfaceV1.Emission C Γ Δ :=
 ⟨Restore.saveCells pointer (Restore.contextCells b Γ) ++ selected.checked.code ++
   Restore.restoreCells pointer (Restore.contextCells b Γ),
 selected.checked.frag,selected.checked.need,lo,pointer,
 (fun _ => Γ.length+1),selected.checked.cost⟩
theorem coverage (selected : Composition.Program b F P) (lo pointer : Nat) :
 InterfaceV3.EntryCoverage b F (admitted selected lo pointer) (plan selected lo pointer) := by
 intro L frame caller base machine start h
 exact ⟨h.represented,h.locals,h.results,h.workspace,h.pointerAbove,h.pointerBelow,
  h.payloadAbove,h.reserve,Nat.le_refl _,h.separate,h.noWrap,h.cursor,h.capacity⟩

theorem bare_revert {statement : Stmt C Γ Δ}
 (selected : Composition.Program b F (.cons statement .nil)) (lo pointer : Nat) :
 InterfaceV1.BareRevertClaim b F statement (plan selected lo pointer) := by
 intro L frame caller base machine start entry source
 have reserve : start+Γ.length≤frame := by
  have h := entry.reserve
  change start+(Γ.length+1)≤frame at h
  omega
 have separate : pointer<start ∨ start+Γ.length≤pointer := by
  have h := entry.separate
  change pointer<start ∨ start+(Γ.length+1)≤pointer at h
  omega
 have fits : start+Γ.length<W := by
  have h := entry.noWrap
  change start+(Γ.length+1)<W at h
  omega
 obtain ⟨saved,captureRun,captured,failed,whole⟩ :=
  CapturedProgram.bare_revert selected entry.represented lo pointer start
   entry.callerBound entry.workspace entry.pointerAbove entry.pointerBelow
   entry.payloadAbove reserve separate fits entry.cursor entry.capacity
   (CallAgreement.singleton_failure source)
   (Restore.restoreCells pointer (Restore.contextCells b Γ))
 exact whole

/-- Conditional construction only (the producers below are built directly, not
through `make`). Approved provenance stays external. -/
def make {statement : Stmt C Γ Δ}
 (selected : Composition.Program b F (.cons statement .nil)) (lo pointer : Nat)
 (approved : InterfaceV3.Admission C Γ)
 (hprof : InterfaceV3.AdmissionAgreement approved (admitted selected lo pointer))
 (witness : ∃ L frame caller base machine start,
  admitted selected lo pointer L frame caller base machine start ∧
  statement.run caller=.error .revert) :
 InterfaceV3.PendingBareRevertProducer b F approved (admitted selected lo pointer) statement := by
 refine ⟨plan selected lo pointer,hprof,coverage selected lo pointer,?_,bare_revert selected lo pointer⟩
 obtain ⟨L,frame,caller,base,machine,start,input,source⟩ := witness
 exact ⟨L,frame,caller,base,machine,start,input,
  coverage selected lo pointer L frame caller base machine start input,source⟩

end

namespace Checks
abbrev A : RefTy := .array (.prim .uint)
namespace P
abbrev C := Solidity.Evm.Memory.CompileExamples.C
abbrev Γ := Solidity.Evm.Memory.CompileExamples.Γ
abbrev σ := Solidity.Evm.Memory.CompileExamples.σ
abbrev base := Solidity.Evm.Memory.CompileExamples.base
abbrev machine := Solidity.Evm.Memory.CompileExamples.machine
abbrev uint := Solidity.Evm.Memory.CompileExamples.uint
abbrev fixture := Solidity.Evm.Memory.CompileExamples.fixture_six_cells
end P
abbrev F := Frag.init P.Γ

def caller := P.σ.setLocal (.here : Idx P.Γ (.val .uint)) (P.uint 9 (by decide))
def machine := writeMachine (writeMachine {P.machine with stack := [w[77]]} 3 w[9]) 8 w[10]

/-- The first access is valid and mutates; the second is out of bounds. -/
def directBody : Prog P.C P.Γ P.Γ :=
 .cons (.assignMem (.index .dyn (.var (.there .here) rfl) (.simple (.lit 0 rfl)))
  (.val (.simple (.lit 37 rfl))))
 (.cons (.assignMem (.index .dyn (.var (.there .here) rfl) (.simple (.lit 2 rfl)))
  (.val (.simple (.lit 53 rfl)))) .nil)
def direct : Stmt P.C P.Γ P.Γ := .block directBody

def args : Args P.C P.Γ [.mem A] := .snocMemory .nil A (.user "input") (.var (.there .here) rfl)
def callee : Prog P.C [.mem A] [.mem A] :=
 .cons (.assignMem (.index .dyn (.var .here rfl) (.simple (.lit 0 rfl)))
  (.val (.simple (.lit 37 rfl))))
 (.cons (.assignMem (.index .dyn (.var .here rfl) (.simple (.lit 2 rfl)))
  (.val (.simple (.lit 53 rfl)))) .nil)
def call : Stmt P.C P.Γ P.Γ := .call "fails" args .none callee

def directSelected : Composition.Program 0 F (.cons direct .nil) :=
 (Mutation.compileProgram 0 F (.cons direct .nil)).get (by decide +kernel)
def callStatement : Composition.Statement 0 F call :=
 (Mutation.compileCall 0 F "fails" args .none callee).get (by decide +kernel)
def callSelected : Composition.Program 0 F (.cons call .nil) :=
 Composition.cons callStatement (Composition.nil 0 callStatement.checked.frag)
theorem initial : StateRepr 1 0 16 F caller P.base machine := by
 have changed := (P.fixture.stack [w[77]]).setVal (.here : Idx P.Γ (.val .uint))
  (P.uint 9 (by decide)) w[9] (ReprV.uint_of rfl)
 have widened : StateRepr 1 0 16 F caller P.base
  (writeMachine {P.machine with stack := [w[77]]} 3 w[9]) := by
  refine ⟨changed.core,⟨changed.heap.arrays,?_,changed.heap.separated⟩,
   changed.pointers,by decide,⟨changed.structs.objects,?_,changed.structs.separated⟩,
   changed.separated,changed.refs⟩
  · intro p r
    rcases r with ⟨i,hi⟩
    cases i with
    | zero => change 16≤16; decide
    | succ i => cases i with
      | zero => change 16≤20; decide
      | succ i => cases hi
  · intro name r
    rcases r with ⟨i,hi⟩
    cases i with
    | zero => cases hi
    | succ i => cases i with
      | zero => cases hi
      | succ i => cases hi
 exact reserved_write widened 8 (by decide) (by decide) w[10]

theorem direct_source : direct.run caller=.error .revert := by
 with_unfolding_all rfl

theorem call_source : call.run caller=.error .revert := by
 with_unfolding_all rfl
theorem metadata : directSelected.checked.need≤8 ∧ callSelected.checked.need≤8 ∧
 directSelected.checked.allocates=false ∧ callSelected.checked.allocates=false := by
 decide
theorem fixture_input {statement : Stmt P.C P.Γ P.Γ}
 (selected : Composition.Program 0 F (.cons statement .nil))
 (room : selected.checked.need≤8) (nonallocating : selected.checked.allocates=false) :
 admitted selected 8 8 1 16 caller P.base machine 10 := by
 exact { represented := initial
         locals := by decide
         results := by decide
         workspace := by simpa only [Nat.zero_add] using room
         pointerAbove := by decide
         pointerBelow := by decide
         payloadAbove := by decide
         reserve := by decide
         separate := by decide
         noWrap := by decide
         cursor := rfl
         capacity := .inl (selected.checked.zeroCost nonallocating caller) }
theorem direct_input : admitted directSelected 8 8 1 16 caller P.base machine 10 :=
 fixture_input directSelected metadata.1 metadata.2.2.1

theorem call_input : admitted callSelected 8 8 1 16 caller P.base machine 10 :=
 fixture_input callSelected metadata.2.1 metadata.2.2.2

/-- Source-independent typed physical caller domain. These constants describe
four retained caller cells, pointer cell8 and five capture cells starting above
it. There is no compiler/plan/Entry/run predicate or caller/heap whitelist. -/
structure CallerInput (L frame : Nat) (caller : State P.C P.Γ)
 (base : Nat → Fin W) (machine : Machine) (start : Nat) : Prop where
 represented : StateRepr L 0 frame F caller base machine
 above : 8<start
 reserve : start+5≤frame
 noWrap : start+5<W
 cursor : machine.mem 8=.val (wmod start)

def sourceInputs : InterfaceV3.Admission P.C P.Γ := CallerInput

theorem source_coverage {statement : Stmt P.C P.Γ P.Γ}
 (selected : Composition.Program 0 F (.cons statement .nil))
 (room : selected.checked.need≤8) (nonallocating : selected.checked.allocates=false) :
 InterfaceV3.EntryCoverage 0 F sourceInputs (plan selected 8 8) := by
 intro L frame caller base machine start input
 apply coverage selected 8 8 L frame caller base machine start
 exact { represented := input.represented
         locals := by decide
         results := by decide
         workspace := by simpa only [Nat.zero_add] using room
         pointerAbove := by decide
         pointerBelow := by have above:=input.above; have reserve:=input.reserve; omega
         payloadAbove := by have above:=input.above; omega
         reserve := input.reserve
         separate := .inl input.above
         noWrap := input.noWrap
         cursor := input.cursor
         capacity := .inl (selected.checked.zeroCost nonallocating caller) }

theorem source_input : sourceInputs 1 16 caller P.base machine 10 := by
 exact ⟨initial,by decide,by decide,by decide,rfl⟩

/-- Real OOB-after-write producer over sourceInputs; only provenance external. -/
def directProducer (approved : InterfaceV3.Admission P.C P.Γ)
 (hprof : InterfaceV3.AdmissionAgreement approved sourceInputs) :
 InterfaceV3.PendingBareRevertProducer 0 F approved sourceInputs direct := by
 let covered := source_coverage directSelected metadata.1 metadata.2.2.1
 exact ⟨plan directSelected 8 8,hprof,covered,
  ⟨1,16,caller,P.base,machine,10,source_input,
   covered 1 16 caller P.base machine 10 source_input,direct_source⟩,
  bare_revert directSelected 8 8⟩

/-- Real callee-bare-revert producer over the SAME source-independent domain. -/
def callProducer (approved : InterfaceV3.Admission P.C P.Γ)
 (hprof : InterfaceV3.AdmissionAgreement approved sourceInputs) :
 InterfaceV3.PendingBareRevertProducer 0 F approved sourceInputs call := by
 let covered := source_coverage callSelected metadata.2.1 metadata.2.2.2
 exact ⟨plan callSelected 8 8,hprof,covered,
  ⟨1,16,caller,P.base,machine,10,source_input,
   covered 1 16 caller P.base machine 10 source_input,call_source⟩,
  bare_revert callSelected 8 8⟩

theorem direct_endpoint : Evm.run (plan directSelected 8 8).code machine=.revert :=
 bare_revert directSelected 8 8 1 16 caller P.base machine 10
  (coverage directSelected 8 8 1 16 caller P.base machine 10 direct_input) direct_source

theorem call_endpoint : Evm.run (plan callSelected 8 8).code machine=.revert :=
 bare_revert callSelected 8 8 1 16 caller P.base machine 10
  (coverage callSelected 8 8 1 16 caller P.base machine 10 call_input) call_source
def firstWrite : Stmt P.C P.Γ P.Γ := .assignMem
 (.index .dyn (.var (.there .here) rfl) (.simple (.lit 0 rfl)))
 (.val (.simple (.lit 37 rfl)))
def changed := caller.withHeap (caller.heap.set Solidity.Evm.Memory.CompileExamples.r0
 (MObj.setElem .dyn (caller.heap.get Solidity.Evm.Memory.CompileExamples.r0)
  0 (P.uint 37 (by decide))))

theorem prefix_source : firstWrite.run caller=.ok ⟨changed,List.prefix_refl _⟩ := by
 with_unfolding_all rfl

theorem arguments_source : args.evalT caller=.ok (some Solidity.Evm.Memory.CompileExamples.r0, ()) := by
 rfl

theorem callee_source : callee.run (caller.withEnv (Δ := [.mem A]) (some Solidity.Evm.Memory.CompileExamples.r0, ()))=.error .revert := by
 with_unfolding_all rfl

theorem refuses_literal :
 (Mutation.compileCall 0 F "literal" args .none
  (.cons .revert .nil : Prog P.C [.mem A] [.mem A])).isSome=false := by
 decide

theorem input_words :
 (machine.stack,[machine.mem 0,machine.mem 1,machine.mem 2,machine.mem 3,machine.mem 8,
  machine.mem 16,machine.mem 17,machine.mem 18,machine.mem 20,machine.mem 21])=
 ([w[77]],[w[20],w[16],w[16],w[9],w[10],w[2],w[7],w[9],w[1],w[4]]) := by
 decide

theorem prefix_words :
 ((TEnv.get (.here : Idx P.Γ (.val .uint)) changed.env).1,
  (TEnv.get (.there .here : Idx P.Γ (.mem A)) changed.env).map HRef.id,
  (TEnv.get (.there (.there .here) : Idx P.Γ (.mem A)) changed.env).map HRef.id,
  (TEnv.get (.there (.there (.there .here)) : Idx P.Γ (.mem A)) changed.env).map HRef.id,
  (MObj.elems .dyn (changed.heap.get Solidity.Evm.Memory.CompileExamples.r0)).map (fun v=>v.1),
  (MObj.elems .dyn (changed.heap.get Solidity.Evm.Memory.CompileExamples.r1)).map (fun v=>v.1))=
 (9,some 0,some 0,some 1,[37,9],[4]) := by
 with_unfolding_all rfl

theorem wrong_cursor : ¬ admitted callSelected 8 8 1 16 caller P.base machine 11 := by
 intro h
 have cursor := h.cursor
 change w[10]=w[11] at cursor
 exact (by decide : w[10]≠w[11]) cursor

theorem direct_other_halt (halt : THalt) (different : halt≠.revert) :
 direct.run caller≠.error halt := by
 intro other
 have same : THalt.revert=halt := Except.error.inj (direct_source.symm.trans other)
 exact different same.symm

theorem call_other_halt (halt : THalt) (different : halt≠.revert) :
 call.run caller≠.error halt := by
 intro other
 have same : THalt.revert=halt := Except.error.inj (call_source.symm.trans other)
 exact different same.symm
end Checks

end Solidity.Backend.InternalFlow.RuntimeFrame.V3BareRevertProducer

#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.V3BareRevertProducer.coverage
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.V3BareRevertProducer.bare_revert
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.V3BareRevertProducer.make
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.V3BareRevertProducer.Checks.initial
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.V3BareRevertProducer.Checks.direct_source
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.V3BareRevertProducer.Checks.call_source
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.V3BareRevertProducer.Checks.metadata
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.V3BareRevertProducer.Checks.fixture_input
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.V3BareRevertProducer.Checks.direct_input
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.V3BareRevertProducer.Checks.call_input
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.V3BareRevertProducer.Checks.directProducer
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.V3BareRevertProducer.Checks.callProducer
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.V3BareRevertProducer.Checks.direct_endpoint
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.V3BareRevertProducer.Checks.call_endpoint
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.V3BareRevertProducer.Checks.prefix_source
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.V3BareRevertProducer.Checks.arguments_source
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.V3BareRevertProducer.Checks.callee_source
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.V3BareRevertProducer.Checks.refuses_literal
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.V3BareRevertProducer.Checks.input_words
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.V3BareRevertProducer.Checks.prefix_words
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.V3BareRevertProducer.Checks.wrong_cursor
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.V3BareRevertProducer.Checks.direct_other_halt
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.V3BareRevertProducer.Checks.call_other_halt

#check Solidity.Backend.InternalFlow.RuntimeFrame.V3BareRevertProducer.admitted
#check Solidity.Backend.InternalFlow.RuntimeFrame.V3BareRevertProducer.coverage
#check Solidity.Backend.InternalFlow.RuntimeFrame.V3BareRevertProducer.bare_revert
#check Solidity.Backend.InternalFlow.RuntimeFrame.V3BareRevertProducer.make
#check Solidity.Backend.InternalFlow.RuntimeFrame.V3BareRevertProducer.Checks.directProducer
#check Solidity.Backend.InternalFlow.RuntimeFrame.V3BareRevertProducer.Checks.callProducer

#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.V3BareRevertProducer.Checks.source_coverage
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.V3BareRevertProducer.Checks.source_input
#check Solidity.Backend.InternalFlow.RuntimeFrame.V3BareRevertProducer.Checks.sourceInputs
