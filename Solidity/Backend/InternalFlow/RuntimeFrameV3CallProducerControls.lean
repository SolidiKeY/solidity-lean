import Solidity.Backend.InternalFlow.RuntimeFrameV3CallProducer
import Solidity.Evm.MemoryCompileExamples

/-! Actual source/target controls for the P1-CALL primitive-result plan.
One call reads its array at a caller-provided index: index zero returns seven;
index two bare-reverts. The domain is physical input capacity, not these two
examples, and approved-profile agreement is never manufactured here. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.V3CallProducer.Controls
open Evm Evm.Memory
abbrev P := Solidity.Evm.Memory.CompileExamples.C
abbrev Γ := Solidity.Evm.Memory.CompileExamples.Γ
abbrev A : RefTy := .array (.prim .uint)
abbrev F := Frag.init Γ
abbrev initial := Solidity.Evm.Memory.CompileExamples.σ
abbrev bases := Solidity.Evm.Memory.CompileExamples.base
abbrev uint := Solidity.Evm.Memory.CompileExamples.uint

def args : Args P Γ [.mem A,.val .uint] :=
 .snocMemory (.snoc .nil .uint (.user "index") (.simple (.local .here)))
  A (.user "array") (.var (.there .here) rfl)
def body : Prog P [.val .uint,.mem A,.val .uint] [.val .uint,.mem A,.val .uint] :=
 .cons (.assignLocal .here (.readMem (.index .dyn (.var (.there .here) rfl)
  (.simple (.local (.there (.there .here))))))) .nil
def ret : CallRet Γ [.val .uint] Γ := .val .uint (.user "result") (some .here)
def call : Stmt P Γ Γ := .call "readAt" args ret body

def statement : Composition.Statement 0 F call :=
 (Composition.compileCall 0 F "readAt" args ret body).get (by first | decide +kernel | rfl)
def selected : Composition.Program 0 F (.cons call .nil) :=
 Composition.cons statement (Composition.nil 0 statement.checked.frag)
def output := initial.setLocal (.here : Idx Γ (.val .uint)) (uint 7 (by decide))
def failing := initial.setLocal (.here : Idx Γ (.val .uint)) (uint 2 (by decide))
def machine := writeMachine
 ({Solidity.Evm.Memory.CompileExamples.machine with stack := [w[77]]}) 8 w[10]
def failedMachine := writeMachine machine 3 w[2]

theorem source_success : call.run initial=.ok ⟨output,List.prefix_refl _⟩ := by
 with_unfolding_all rfl
theorem source_revert : call.run failing=.error .revert := by
 with_unfolding_all rfl
theorem zero_cost (caller : State P Γ) : selected.checked.cost caller=0 :=
 selected.checked.zeroCost (by first | decide +kernel | rfl) caller
theorem room : need selected=8 := by first | decide +kernel | rfl

theorem initial_repr : StateRepr 1 0 16 F initial bases machine := by
 have baseRepr := (Solidity.Evm.Memory.CompileExamples.fixture_six_cells).stack [w[77]]
 have widened : StateRepr 1 0 16 F initial bases
     {Solidity.Evm.Memory.CompileExamples.machine with stack := [w[77]]} := by
  refine ⟨baseRepr.core,⟨baseRepr.heap.arrays,?_,baseRepr.heap.separated⟩,
   baseRepr.pointers,by decide,⟨baseRepr.structs.objects,?_,baseRepr.structs.separated⟩,
   baseRepr.separated,baseRepr.refs⟩
  · intro p reference
    rcases reference with ⟨i,hi⟩
    cases i with
    | zero => change 16≤16; decide
    | succ i => cases i with
      | zero => change 16≤20; decide
      | succ i => cases hi
  · intro name reference
    rcases reference with ⟨i,hi⟩
    cases i with
    | zero => cases hi
    | succ i => cases i with
      | zero => cases hi
      | succ i => cases hi
 exact reserved_write widened 8 (by decide) (by decide) w[10]
theorem failing_repr : StateRepr 1 0 16 F failing bases failedMachine :=
 initial_repr.setVal (.here : Idx Γ (.val .uint)) (uint 2 (by decide)) w[2] (ReprV.uint_of rfl)

/-- Same physical domain admits both outcomes of the SAME source call. -/
theorem positive_member : admitted selected 8 8 1 16 initial bases machine 10 :=
 ⟨initial_repr,by decide +kernel,by decide,by decide,by decide,by decide,
  by decide,by decide,rfl,.inl (zero_cost initial)⟩
theorem negative_member : admitted selected 8 8 1 16 failing bases failedMachine 10 :=
 ⟨failing_repr,by decide +kernel,by decide,by decide,by decide,by decide,
  by decide,by decide,rfl,.inl (zero_cost failing)⟩

theorem positive_entry : InterfaceV1.Entry (plan selected 8 8) 1 0 16 F initial bases machine 10 where
 represented := initial_repr
 callerBound := by decide
 resultBound := by decide
 workspace := by decide +kernel
 pointerAbove := by decide
 pointerBelow := by decide
 payloadAbove := by decide
 reserve := by decide
 controlSpace := by decide
 separate := by decide
 noWrap := by decide
 cursor := rfl
 capacity := .inl (zero_cost initial)
theorem negative_entry : InterfaceV1.Entry (plan selected 8 8) 1 0 16 F failing bases failedMachine 10 where
 represented := failing_repr
 callerBound := by decide
 resultBound := by decide
 workspace := by decide +kernel
 pointerAbove := by decide
 pointerBelow := by decide
 payloadAbove := by decide
 reserve := by decide
 controlSpace := by decide
 separate := by decide
 noWrap := by decide
 cursor := rfl
 capacity := .inl (zero_cost failing)

theorem successful : InterfaceV3.SuccessfulEntry 0 F (admitted selected 8 8) call (plan selected 8 8) :=
 ⟨1,16,initial,bases,machine,10,⟨output,List.prefix_refl _⟩,positive_member,positive_entry,source_success⟩
theorem reverting : InterfaceV3.RevertingEntry 0 F (admitted selected 8 8) call (plan selected 8 8) :=
 ⟨1,16,failing,bases,failedMachine,10,negative_member,negative_entry,source_revert⟩


/-- Alias compatibility is vacuous only because this fixture has no storage
alias local; its memory parameters still carry real heap-reference identities. -/
theorem flags : InterfaceV1.NoAliasPromotion F selected.checked.frag .refl := by
 intro R index live
 nomatch index

theorem target_return : InterfaceV1.Returned (plan selected 8 8) 1 0 16 initial bases machine 10
    ⟨output,List.prefix_refl _⟩ :=
 returns selected 8 8 flags 1 16 initial bases machine 10 positive_entry
  ⟨output,List.prefix_refl _⟩ source_success

theorem target_reverts : Evm.run (plan selected 8 8).code failedMachine=.revert :=
 bare_revert selected 8 8 1 16 failing bases failedMachine 10 negative_entry source_revert

theorem target_value : ∃ target,
 Evm.run (plan selected 8 8).code machine=.ok target 0 ∧ target.mem 3=w[7] := by
 obtain ⟨target,addresses,actual,represented,stack,extension,growth,cursor,older⟩ := target_return
 have value := represented.core.vals (.here : Idx Γ (.val .uint))
 change ReprV .uint (uint 7 (by decide)) (target.mem 3) at value
 exact ⟨target,actual,Restored.value_unique value (ReprV.uint_of rfl)⟩

theorem refused_literal_revert :
 (Composition.compileCall 0 F "literalRevert" args ret
  (.cons .revert .nil : Prog P [.val .uint,.mem A,.val .uint] [.val .uint,.mem A,.val .uint])).isSome=false := by
 first | decide +kernel | rfl

def capacityMachine := writeMachine machine 8 w[14]
theorem capacity_repr : StateRepr 1 0 16 F initial bases capacityMachine :=
 reserved_write initial_repr 8 (by decide) (by decide) w[14]
theorem capacity_cursor : capacityMachine.mem 8=w[14] := rfl

theorem refuses_arena_capacity : ¬ admitted selected 8 8 1 16 initial bases capacityMachine 14 := by
 simp only [admitted,Γ,Solidity.Evm.Memory.CompileExamples.Γ,List.length_cons,List.length_nil]
 omega

/-- A genuinely dual-outcome example producer, conditional only on the
external approved-domain agreement; neither outcome nor coverage is assumed. -/
def producer (approved : InterfaceV3.Admission P Γ)
 (hprof : InterfaceV3.AdmissionAgreement approved (admitted selected 8 8)) :
 InterfaceV3.PendingCallProducer 0 F approved (admitted selected 8 8)
  "readAt" args ret body :=
 make selected 8 8 approved hprof flags successful reverting


end Solidity.Backend.InternalFlow.RuntimeFrame.V3CallProducer.Controls
