import Solidity.Backend.InternalFlow.RuntimeFrameV3CallProducerRef
import Solidity.Backend.MemoryOps.StructDefaults.WordControls

/-! Inhabited allocating memory-return calls with a reference parameter.
The body redirects its returned pointer to the old argument and reads through
it; index zero succeeds and index two bare-reverts after default allocation. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.V3CallProducerRef.ArrayControls
open Evm Evm.Memory
namespace Seed
abbrev C := Solidity.Backend.MemoryOps.StructDefaults.WordControls.C
abbrev state := Solidity.Backend.MemoryOps.StructDefaults.WordControls.initial
abbrev bases := Solidity.Backend.MemoryOps.StructDefaults.WordControls.bases
abbrev machine := Solidity.Backend.MemoryOps.StructDefaults.WordControls.machine
abbrev represented := Solidity.Backend.MemoryOps.StructDefaults.WordControls.initial_repr
end Seed
abbrev C := Seed.C
abbrev A : RefTy := .array (.prim .uint)
abbrev Γ : Ctx := [.val .uint,.mem A]
abbrev F := Frag.init Γ

def one : Fin W := wmod 1
def old := Seed.state.allocPush (defaultArray .uint one)
def bases := upd Seed.bases 0 (wmod 128)
def oldMachine := writeMachine (allocateMachine Seed.machine (wmod 128) one) 1 w[128]
def caller (n : Fin W) : State C Γ := old.push (t := .val .uint) (indexValue n)
def machine (n : Fin W) := writeMachine (writeMachine oldMachine 2 (.val n)) 16 w[20]

theorem initial (n : Fin W) : StateRepr 1 1 64 F (caller n) bases (machine n) ∧
 StructAllocatorRepr (caller n).heap bases 64 (wmod 130) (machine n) := by
 have allocated := newArray_correct Seed.represented.1 Seed.represented.2 (by decide)
  .uint (.lit 1 rfl) rfl one rfl (by decide) (by decide)
 have represented := allocated.2.2.1.consVal (indexValue n) (.val n) (ReprV.uint_of rfl) (by decide)
 have allocator := allocated.2.2.2.1.localWrite 2 (by decide) (by decide) (.val n)
 exact ⟨reserved_write represented 16 (by decide) (by decide) w[20],
  allocator.localWrite 16 (by decide) (by decide) w[20]⟩

def args : Args C Γ [.mem A,.val .uint] :=
 .snocMemory (.snoc .nil .uint (.user "index") (.simple (.local .here)))
  A (.user "input") (.var (.there .here) rfl)
def ret : CallRet Γ [.mem A] (.mem A::Γ) := .mem A (.user "result") rfl rfl
def body : Prog C [.mem A,.mem A,.val .uint] [.val .uint,.mem A,.mem A,.val .uint] :=
 .cons (.rebindMem .here (.alias (.var (.there .here) rfl)))
 (.cons (.declLocal .uint (.user "observed")
  (some (.readMem (.index .dyn (.var .here rfl) (.simple (.local (.there (.there .here)))))))) .nil)
def call : Stmt C Γ (.mem A::Γ) := .call "returnAlias" args ret body

def statement : Composition.Statement 1 F call :=
 (Composition.compileCall 1 F "returnAlias" args ret body).get (by decide +kernel)
def selected : Composition.Program 1 F (.cons call .nil) :=
 Composition.cons statement (Composition.nil 1 statement.checked.frag)

theorem cost (n : Fin W) : selected.checked.cost (caller n)=1 := by
 with_unfolding_all rfl

theorem source_success : ∃ out : Solidity.Out C (caller (wmod 0)).H (.mem A::Γ),
 call.run (caller (wmod 0))=.ok out := by
 with_unfolding_all exact ⟨_,rfl⟩
theorem source_revert : call.run (caller (wmod 2))=.error .revert := by
 with_unfolding_all rfl

def scope : Ext Γ (.mem A::Γ) := .push .refl
theorem form : Form Γ ret scope := Form.memory A (.user "result") rfl rfl
theorem flags : InterfaceV1.NoAliasPromotion F selected.checked.frag scope := by
 intro R index live
 nomatch index

/-- Actual shared allocator and whole-call capacity, including the mandatory
default return object even when the body later redirects the return. -/
theorem capacity (n : Fin W) : AllocationInput 1 64 (selected.checked.cost (caller n))
 (caller n) bases (machine n) :=
 .inr ⟨by decide,wmod 130,(initial n).2,by rw [cost];decide⟩

theorem member (n : Fin W) : admitted selected 16 16 1 64 (caller n) bases (machine n) 20 :=
 ⟨(initial n).1,by decide +kernel,by decide,by decide,by decide,by decide,
  by decide,by decide,rfl,capacity n⟩

theorem entered (n : Fin W) : InterfaceV1.Entry (plan selected 16 16) 1 1 64 F
 (caller n) bases (machine n) 20 := coverage selected 16 16 1 64 (caller n) bases (machine n) 20 (member n)

theorem successful : InterfaceV3.SuccessfulEntry 1 F (admitted selected 16 16)
 call (plan selected 16 16) := by
 obtain ⟨out,source⟩ := source_success
 exact ⟨1,64,caller (wmod 0),bases,machine (wmod 0),20,out,
  member _,entered _,source⟩

theorem reverting : InterfaceV3.RevertingEntry 1 F (admitted selected 16 16)
 call (plan selected 16 16) :=
 ⟨1,64,caller (wmod 2),bases,machine (wmod 2),20,member _,entered _,source_revert⟩

def producer (approved : InterfaceV3.Admission C Γ)
 (hprof : InterfaceV3.AdmissionAgreement approved (admitted selected 16 16)) :
 InterfaceV3.PendingCallProducer 1 F approved (admitted selected 16 16)
  "returnAlias" args ret body :=
 make form selected 16 16 approved hprof flags successful reverting

theorem simulated_success : ∃ out : Solidity.Out C (caller (wmod 0)).H (.mem A::Γ),
 call.run (caller (wmod 0))=.ok out ∧
 InterfaceV1.Returned (plan selected 16 16) 1 1 64 (caller (wmod 0)) bases (machine (wmod 0)) 20 out := by
 obtain ⟨out,source⟩ := source_success
 exact ⟨out,source,returns form selected 16 16 flags 1 64 (caller (wmod 0)) bases
  (machine (wmod 0)) 20 (entered _) out source⟩

theorem simulated_revert : Evm.run (plan selected 16 16).code (machine (wmod 2))=.revert :=
 bare_revert selected 16 16 1 64 (caller (wmod 2)) bases (machine (wmod 2)) 20 (entered _) source_revert

/-- Literal revert remains selector-refused; success/revert witnesses above
come from actual checked reads, not a newly admitted revert leaf. -/
theorem refused_literal_revert :
 (Composition.compileCall 1 F "literalRevert" args ret
  (.cons .revert .nil : Prog C [.mem A,.mem A,.val .uint] [.mem A,.mem A,.val .uint])).isSome=false := by
 first | decide +kernel | rfl

/-- Countercontrol: actual expansion without the required result compaction.
The result destination initially contains the numeric argument, so a missing
pointer export cannot accidentally pass the alias observation. -/
def expanded : Composition.Program 1 F (Calls.expandMem args A (.user "result") rfl rfl body) :=
 (Composition.compileProgram 1 F (Calls.expandMem args A (.user "result") rfl rfl body)).get (by decide +kernel)
def missingExport : List Instr :=
 Restore.saveCells 16 (Restore.contextCells 1 Γ) ++ expanded.checked.code ++
 Restore.restoreCells 16 (Restore.contextCells 1 Γ)

/-- Capacity is a real reached allocation premise (the return default costs
one), not a runtime failure observation. -/
theorem capacity_refusal : ¬ AllocationInput 1 64 (selected.checked.cost (caller (wmod 0)))
 (caller (wmod 0)) bases (writeMachine (machine (wmod 0)) 0 (.val wMax)) := by
 intro input
 rcases input with zero | ⟨positive,cursor,allocator,space⟩
 · rw [cost] at zero
   contradiction
 · have cell := allocator.arrays.free.cell
   change upd (machine (wmod 0)).mem 0 (.val wMax) 0=.val cursor at cell
   rw [upd_same] at cell
   have same : wMax=cursor := Word.val.inj cell
   subst cursor
   rw [cost] at space
   change W-1+1<W at space
   have positive := W_pos
   omega

/-- Actual old tuple-selector refusal, before the new tuple emitter is built. -/
theorem old_tuple_selector_refused :
 (Composition.compileCall 1 F "tuple" (.nil : Args C Γ [])
  (.rets (.snoc .nil .uint (.user "result")))
  (.nil : Prog C [.val .uint] [.val .uint])).isSome=false := by
 first | decide +kernel | rfl

/-- The missing finite reference-struct default leaf is explicit. Its G33
DefaultPlan exists; the old footprint selector does not consume it yet. -/
theorem old_struct_default_selector_refused :
 (Composition.compileStatement 1 F
  (.declMem (.struct Solidity.Backend.MemoryOps.StructDefaults.WordControls.pairName)
   (.user "result") none rfl rfl : Stmt C Γ _)).isSome=false := by
 first | decide +kernel | rfl

end Solidity.Backend.InternalFlow.RuntimeFrame.V3CallProducerRef.ArrayControls
