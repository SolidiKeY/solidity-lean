import Solidity.Backend.InternalFlow.RuntimeFrameNoneProducer
import Solidity.Backend.InternalFlow.RuntimeFrameInterfaceV3
import Solidity.Backend.InternalFlow.RuntimeFrameMutation
import Solidity.Evm.MemoryCompileExamples

/-! P1-THUNK, H14 D: generic fixed-thunk V3 producer construction.
Frozen V3 and the V2 producers remain read-only; approved provenance is external.

For a fixed thunk : Unit → Prog C ps ps and a
checked singleton ordinary void call selected, construct
InterfaceV3.PendingFixedCallRecProducer b F approved
 (admitted b F selected.checked.need lo pointer) f args .none thunk,
with hprof : InterfaceV3.AdmissionAgreement approved
 (admitted b F selected.checked.need lo pointer) EXPLICIT, and derive return
and bare-revert claims from the existing NoneProducer theorems at EVERY d.
No desired simulation or return correctness may be supplied as an input.
NoneProducer.returns also needs the genuine fragment compatibility
InterfaceV1.NoAliasPromotion F selected.checked.frag .refl. Retain this premise
for generic F, or derive it with NoneProducer.init_flags for the concrete
Frag.init fixture. It is not implied by physical geometry.

The domain below is independent of quotation index, plan Entry, target run and
source outcome. A nonallocating certificate must prove cost zero for all callers
before its capacity is discharged. Non-vacuity below uses one fixed
bounds-sensitive array-writing thunk with BOTH an index0 successful
caller and an out-of-bounds bare-reverting caller. No index whitelist is added.
The literal revert body remains refused by the selector.
The generic constructor and concrete dual-outcome instance are below; only
approved-profile provenance remains an explicit external hypothesis. "Every
index" is immediate: `Stmt.callRec` ignores its depth argument. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.V3FixedThunkProducer
open Evm Evm.Memory

/-- Initial typed representation and static physical workspace constraints.
No candidate plan, Entry predicate, quotation index or execution is mentioned. -/
def admitted {C : Contract} {Γ : Ctx} (b : Nat) (F : Frag Γ)
    (need localLimit pointerCell : Nat) : InterfaceV3.Admission C Γ :=
  fun L frame caller base machine start =>
    StateRepr L b frame F caller base machine ∧
    b + Γ.length ≤ localLimit ∧ b + need ≤ localLimit ∧
    localLimit ≤ pointerCell ∧ pointerCell < frame ∧ localLimit ≤ start ∧
    start + (Γ.length + 1) ≤ frame ∧
    (pointerCell < start ∨ start + (Γ.length + 1) ≤ pointerCell) ∧
    start + (Γ.length + 1) < W ∧ machine.mem pointerCell = .val (wmod start)

variable {C : Contract} {Γ ps : Ctx} {b : Nat} {F : Frag Γ}
 {f : Name} {args : Args C Γ ps}

/-- Universal coverage for the exact input, not replacement by a witness.
The zero-cost duty comes from the real nonallocation certificate. -/
theorem coverage (thunk : Unit → Prog C ps ps)
    (selected : Composition.Program b F (.cons (.call f args .none (thunk ())) .nil))
    (lo pointer : Nat) (nonallocating : selected.checked.allocates=false) :
    InterfaceV3.EntryCoverage b F (admitted b F selected.checked.need lo pointer)
      (NoneProducer.plan selected lo pointer) := by
  intro L frame caller base machine start member
  obtain ⟨represented,callerBound,workspace,pointerAbove,pointerBelow,payloadAbove,
    reserve,separate,noWrap,cursor⟩ := member
  exact ⟨represented,callerBound,callerBound,workspace,pointerAbove,pointerBelow,
    payloadAbove,reserve,Nat.le_refl _,separate,noWrap,cursor,
    .inl (selected.checked.zeroCost nonallocating caller)⟩

/-- Actual ordinary source success in the same physical domain. There is no
Entry, target run or correctness claim in this witness. -/
def SuccessfulInput (thunk : Unit → Prog C ps ps) (need lo pointer : Nat) : Prop :=
  ∃ (L frame : Nat) (caller : State C Γ) (base : Nat → Fin W)
    (machine : Machine) (start : Nat) (out : Solidity.Out C caller.H Γ),
    admitted b F need lo pointer L frame caller base machine start ∧
    (.call f args .none (thunk ()) : Stmt C Γ Γ).run caller=.ok out

def RevertingInput (thunk : Unit → Prog C ps ps) (need lo pointer : Nat) : Prop :=
  ∃ (L frame : Nat) (caller : State C Γ) (base : Nat → Fin W)
    (machine : Machine) (start : Nat),
    admitted b F need lo pointer L frame caller base machine start ∧
    (.call f args .none (thunk ()) : Stmt C Γ Γ).run caller=.error .revert

/-- The V3 fixed-thunk producer is constructed from real source witnesses.
Both witnesses still must be inhabited by a concrete instance; hprof belongs
to the independent approved-profile producer. This is void-return transport,
not unbounded recursion or arbitrary CallRet correctness. -/
def make (thunk : Unit → Prog C ps ps)
    (selected : Composition.Program b F (.cons (.call f args .none (thunk ())) .nil))
    (lo pointer : Nat) (nonallocating : selected.checked.allocates=false)
    (flags : InterfaceV1.NoAliasPromotion F selected.checked.frag .refl)
    (approved : InterfaceV3.Admission C Γ)
    (hprof : InterfaceV3.AdmissionAgreement approved (admitted b F selected.checked.need lo pointer))
    (successful : SuccessfulInput (b := b) (F := F) (f := f) (args := args)
      thunk selected.checked.need lo pointer)
    (reverting : RevertingInput (b := b) (F := F) (f := f) (args := args)
      thunk selected.checked.need lo pointer) :
    InterfaceV3.PendingFixedCallRecProducer b F approved
      (admitted b F selected.checked.need lo pointer) f args .none thunk where
  plan := NoneProducer.plan selected lo pointer
  required_profile := hprof
  required_coverage := coverage thunk selected lo pointer nonallocating
  required_successful_entry := by
    intro d
    obtain ⟨L,frame,caller,base,machine,start,out,member,source⟩ := successful
    exact ⟨L,frame,caller,base,machine,start,out,member,
      coverage thunk selected lo pointer nonallocating L frame caller base machine start member,source⟩
  required_reverting_entry := by
    intro d
    obtain ⟨L,frame,caller,base,machine,start,member,source⟩ := reverting
    exact ⟨L,frame,caller,base,machine,start,member,
      coverage thunk selected lo pointer nonallocating L frame caller base machine start member,source⟩
  required_return := fun _ => NoneProducer.returns selected lo pointer flags
  required_bare_revert := fun _ => NoneProducer.bare_revert selected lo pointer

end Solidity.Backend.InternalFlow.RuntimeFrame.V3FixedThunkProducer

/-! Generated scoped axiom guards from the actual focused output. -/

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.V3FixedThunkProducer.admitted' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.V3FixedThunkProducer.admitted

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.V3FixedThunkProducer.coverage' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.V3FixedThunkProducer.coverage

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.V3FixedThunkProducer.SuccessfulInput' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.V3FixedThunkProducer.SuccessfulInput

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.V3FixedThunkProducer.RevertingInput' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.V3FixedThunkProducer.RevertingInput

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.V3FixedThunkProducer.make' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.V3FixedThunkProducer.make

/-! A genuine dual-outcome typed input family for ONE fixed thunk. These are
intrinsic THalt outcomes, not solc/EVM panic-byte or source-admission claims. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.V3FixedThunkProducer.Witness
open Evm Evm.Memory
namespace P
abbrev C := Solidity.Evm.Memory.CompileExamples.C
abbrev Γ := Solidity.Evm.Memory.CompileExamples.Γ
abbrev σ := Solidity.Evm.Memory.CompileExamples.σ
abbrev r0 := Solidity.Evm.Memory.CompileExamples.r0
abbrev base := Solidity.Evm.Memory.CompileExamples.base
abbrev machine := Solidity.Evm.Memory.CompileExamples.machine
abbrev uint := Solidity.Evm.Memory.CompileExamples.uint
end P
abbrev A : RefTy := .array (.prim .uint)
abbrev F := Frag.init P.Γ

def args : Args P.C P.Γ [.val .uint,.mem A] :=
  .snoc (.snocMemory .nil A (.user "input") (.var (.there .here) rfl))
    .uint (.user "index") (.simple (.local .here))

def thunk (_ : Unit) : Prog P.C [.val .uint,.mem A] [.val .uint,.mem A] :=
  .cons (.assignMem (.index .dyn (.var (.there .here) rfl) (.simple (.local .here)))
    (.val (.simple (.lit 37 rfl)))) .nil

def call : Stmt P.C P.Γ P.Γ := .call "fixedBounds" args .none (thunk ())
def statement : Composition.Statement 0 F call :=
  (Mutation.compileCall 0 F "fixedBounds" args .none (thunk ())).get
    (by first | rfl | decide | omega | decide +kernel)
def selected : Composition.Program 0 F (.cons call .nil) :=
  Composition.cons statement (Composition.nil 0 statement.checked.frag)

theorem room : 0+selected.checked.need≤8 := by
  first | rfl | decide | omega | decide +kernel

theorem nonallocating : selected.checked.allocates=false := by
  first | rfl | decide | omega | decide +kernel

def caller0 := P.σ
def caller9 := caller0.setLocal (.here : Idx P.Γ (.val .uint)) (P.uint 9 (by decide))
def machine0 := writeMachine (writeMachine {P.machine with stack := [w[77]]} 8 w[10]) 9 w[99]
def machine9 := writeMachine machine0 3 w[9]
def reached := caller0.withHeap (caller0.heap.set P.r0
  (MObj.setElem .dyn (caller0.heap.get P.r0) 0 (P.uint 37 (by decide))))

/-- Enumerate the actual typed heap.
No ownership is inferred merely from equal pointer words. -/
theorem frame16 : StateRepr 1 0 16 F caller0 P.base P.machine := by
  have h : StateRepr 1 0 6 F caller0 P.base P.machine :=
    Solidity.Evm.Memory.CompileExamples.fixture_six_cells
  refine ⟨h.core,⟨h.heap.arrays,?_,h.heap.separated⟩,h.pointers,by decide,
    ⟨h.structs.objects,?_,h.structs.separated⟩,h.separated,h.refs⟩
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

theorem represented0 : StateRepr 1 0 16 F caller0 P.base machine0 :=
  reserved_write (reserved_write (frame16.stack [w[77]]) 8 (by decide) (by decide) w[10])
    9 (by decide) (by decide) w[99]

theorem represented9 : StateRepr 1 0 16 F caller9 P.base machine9 :=
  represented0.setVal (.here : Idx P.Γ (.val .uint)) (P.uint 9 (by decide)) w[9] (ReprV.uint_of rfl)

theorem source0 : call.run caller0=.ok ⟨reached,List.prefix_refl _⟩ := by
  first
  | (simp only [Solidity.Stmt.runR_eq,Solidity.Prog.runR_eq]; done)
  | decide
  | omega
  | rfl
  | with_unfolding_all rfl

theorem source9 : call.run caller9=.error .revert := by
  first
  | (simp only [Solidity.Stmt.runR_eq,Solidity.Prog.runR_eq]; done)
  | decide
  | omega
  | rfl
  | with_unfolding_all rfl

abbrev domain : InterfaceV3.Admission P.C P.Γ :=
  admitted 0 F selected.checked.need 8 8

theorem member0 : domain 1 16 caller0 P.base machine0 10 :=
  ⟨represented0,by decide,room,by decide,by decide,by decide,by decide,
    .inl (by decide),by decide,by rfl⟩

theorem member9 : domain 1 16 caller9 P.base machine9 10 :=
  ⟨represented9,by decide,room,by decide,by decide,by decide,by decide,
    .inl (by decide),by decide,by rfl⟩

theorem successful : SuccessfulInput (b := 0) (F := F) (f := "fixedBounds") (args := args)
    thunk selected.checked.need 8 8 :=
  ⟨1,16,caller0,P.base,machine0,10,⟨reached,List.prefix_refl _⟩,member0,source0⟩

theorem reverting : RevertingInput (b := 0) (F := F) (f := "fixedBounds") (args := args)
    thunk selected.checked.need 8 8 :=
  ⟨1,16,caller9,P.base,machine9,10,member9,source9⟩

/-- The approved-domain agreement is the remaining semantic hypothesis.
Both source outcomes and physical memberships are closed above. -/
def producer (approved : InterfaceV3.Admission P.C P.Γ)
    (hprof : InterfaceV3.AdmissionAgreement approved domain) :
    InterfaceV3.PendingFixedCallRecProducer 0 F approved domain "fixedBounds" args .none thunk :=
  make thunk selected 8 8 nonallocating (NoneProducer.init_flags selected.checked.frag .refl)
    approved hprof successful reverting

/-- Unsupported literal-revert code remains refused by the original selector. -/
theorem literal_revert_refused :
    (Mutation.compileCall 0 F "explicitRevert" args .none
      (.cons .revert .nil : Prog P.C [.val .uint,.mem A] [.val .uint,.mem A])).isSome=false := by
  first | rfl | decide | omega | decide +kernel

/-- Actual successful and reverting entries hold at EVERY quotation index. -/
theorem successful_at (d : Nat) :
    InterfaceV3.SuccessfulEntry 0 F domain (.callRec "fixedBounds" d args .none thunk)
      (NoneProducer.plan selected 8 8) :=
  ⟨1,16,caller0,P.base,machine0,10,⟨reached,List.prefix_refl _⟩,member0,
    coverage thunk selected 8 8 nonallocating 1 16 caller0 P.base machine0 10 member0,source0⟩

theorem reverting_at (d : Nat) :
    InterfaceV3.RevertingEntry 0 F domain (.callRec "fixedBounds" d args .none thunk)
      (NoneProducer.plan selected 8 8) :=
  ⟨1,16,caller9,P.base,machine9,10,member9,
    coverage thunk selected 8 8 nonallocating 1 16 caller9 P.base machine9 10 member9,source9⟩

theorem return_at (d : Nat) :
    InterfaceV1.ReturnClaim 0 F (.callRec "fixedBounds" d args .none thunk)
      (NoneProducer.plan selected 8 8) :=
  NoneProducer.returns selected 8 8 (NoneProducer.init_flags selected.checked.frag .refl)

theorem bare_revert_at (d : Nat) :
    InterfaceV1.BareRevertClaim 0 F (.callRec "fixedBounds" d args .none thunk)
      (NoneProducer.plan selected 8 8) :=
  NoneProducer.bare_revert selected 8 8

/-- The actual five-word arena does not fit this changed frame. -/
theorem insufficient_frame_refused : ¬ domain 1 14 caller0 P.base machine0 10 := by
  simp only [domain,admitted,P.Γ,Solidity.Evm.Memory.CompileExamples.Γ,List.length_cons,List.length_nil]
  omega

end Solidity.Backend.InternalFlow.RuntimeFrame.V3FixedThunkProducer.Witness

namespace Solidity.Backend.InternalFlow.RuntimeFrame.V3FixedThunkProducer
open Evm Evm.Memory

/-- General fixed-thunk transport consumes the actual ordinary producer;
it does not implement the ordinary-call piece or authenticate its profile.
All four source/transport obligations retain the SAME domain and code image.
This supports arbitrary typed CallRet when its ordinary producer is available. -/
def of_call {C : Contract} {Γ Δ ps rs : Ctx} {b : Nat} {F : Frag Γ}
    {f : Name} {args : Args C Γ ps} (ret : CallRet Γ rs Δ)
    (thunk : Unit → Prog C (rs ++ ps) (rs ++ ps))
    (approved domain : InterfaceV3.Admission C Γ)
    (hprof : InterfaceV3.AdmissionAgreement approved domain)
    (ordinary : InterfaceV3.PendingCallProducer b F approved domain f args ret (thunk ())) :
    InterfaceV3.PendingFixedCallRecProducer b F approved domain f args ret thunk where
  plan := ordinary.plan
  required_profile := hprof
  required_coverage := ordinary.required_coverage
  required_successful_entry := fun _ => ordinary.required_successful_entry
  required_reverting_entry := fun _ => ordinary.required_reverting_entry
  required_return := fun _ => ordinary.required_return
  required_bare_revert := fun _ => ordinary.required_bare_revert

end Solidity.Backend.InternalFlow.RuntimeFrame.V3FixedThunkProducer

/-! Generated scoped axiom pins from actual retained kernel output. -/

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.V3FixedThunkProducer.of_call' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.V3FixedThunkProducer.of_call

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.V3FixedThunkProducer.Witness.producer' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.V3FixedThunkProducer.Witness.producer

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.V3FixedThunkProducer.Witness.successful_at' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.V3FixedThunkProducer.Witness.successful_at

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.V3FixedThunkProducer.Witness.reverting_at' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.V3FixedThunkProducer.Witness.reverting_at

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.V3FixedThunkProducer.Witness.return_at' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.V3FixedThunkProducer.Witness.return_at

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.V3FixedThunkProducer.Witness.bare_revert_at' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.V3FixedThunkProducer.Witness.bare_revert_at

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.V3FixedThunkProducer.Witness.literal_revert_refused' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.V3FixedThunkProducer.Witness.literal_revert_refused

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.V3FixedThunkProducer.Witness.insufficient_frame_refused' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.V3FixedThunkProducer.Witness.insufficient_frame_refused
