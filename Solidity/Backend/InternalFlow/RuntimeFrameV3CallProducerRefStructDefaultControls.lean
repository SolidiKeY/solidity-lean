import Solidity.Backend.InternalFlow.RuntimeFrameV3CallProducerRefStructDefaultCompile
import Solidity.Backend.InternalFlow.RuntimeFrameV3CallProducerRefArrayControls
import Solidity.Backend.MemoryOps.StructDefaults.NestedWordControls

/-! Inhabited nested finite struct return construction with an existing array
argument and a real bounds-sensitive success/failure split. Struct argument and
whole-struct return rebinding are in StructRebindControls. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.V3CallProducerRef.StructDefault.Controls
open Evm Evm.Memory
abbrev C := ArrayControls.C
abbrev Γ := ArrayControls.Γ
abbrev F := ArrayControls.F
abbrev S : RefTy := .struct Solidity.Backend.MemoryOps.StructDefaults.NestedWordControls.nestedName

def body : Prog C [.mem S,.mem ArrayControls.A,.val .uint]
    [.val .uint,.mem S,.mem ArrayControls.A,.val .uint] :=
  .cons (.declLocal .uint (.user "observed")
    (some (.readMem (.index .dyn (.var (.there .here) rfl)
      (.simple (.local (.there (.there .here)))))))) .nil

def ret : CallRet Γ [.mem S] (.mem S :: Γ) := .mem S (.user "result") (by decide +kernel) (by decide +kernel)
def call : Stmt C Γ (.mem S :: Γ) := .call "nestedDefault" ArrayControls.args ret body

def statement : Composition.Statement 1 F call :=
  (compileMemoryCall 1 F "nestedDefault" ArrayControls.args S (.user "result")
    (by decide +kernel) (by decide +kernel) body).get (by decide +kernel)
def selected : Composition.Program 1 F (.cons call .nil) :=
  Composition.cons statement (Composition.nil 1 statement.checked.frag)

abbrev args := ArrayControls.args
abbrev caller := ArrayControls.caller
abbrev bases := ArrayControls.bases
abbrev machine := ArrayControls.machine
abbrev initial := ArrayControls.initial

theorem cost (n : Fin W) : selected.checked.cost (caller n)=5 := by
 with_unfolding_all rfl

theorem source_success : ∃ out : Solidity.Out C (caller (wmod 0)).H (.mem S::Γ),
 call.run (caller (wmod 0))=.ok out := by
 with_unfolding_all exact ⟨_,rfl⟩
theorem source_revert : call.run (caller (wmod 2))=.error .revert := by
 with_unfolding_all rfl

def scope : Ext Γ (.mem S::Γ) := .push .refl
theorem form : Form Γ ret scope := Form.memory S (.user "result") (by decide +kernel) (by decide +kernel)
theorem flags : InterfaceV1.NoAliasPromotion F selected.checked.frag scope := by
 intro R index live
 nomatch index

/-- Actual shared allocator and whole-call capacity, including the mandatory
child and parent default allocations. -/
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
  "nestedDefault" args ret body :=
 make form selected 16 16 approved hprof flags successful reverting

theorem simulated_success : ∃ out : Solidity.Out C (caller (wmod 0)).H (.mem S::Γ),
 call.run (caller (wmod 0))=.ok out ∧
 InterfaceV1.Returned (plan selected 16 16) 1 1 64 (caller (wmod 0)) bases (machine (wmod 0)) 20 out := by
 obtain ⟨out,source⟩ := source_success
 exact ⟨out,source,returns form selected 16 16 flags 1 64 (caller (wmod 0)) bases
  (machine (wmod 0)) 20 (entered _) out source⟩

theorem simulated_revert : Evm.run (plan selected 16 16).code (machine (wmod 2))=.revert :=
 bare_revert selected 16 16 1 64 (caller (wmod 2)) bases (machine (wmod 2)) 20 (entered _) source_revert

/-- The real cost5 capacity premise is rejected at the top address. -/
theorem capacity_refused : ¬ AllocationInput 1 64 (selected.checked.cost (caller (wmod 0)))
    (caller (wmod 0)) bases (writeMachine (machine (wmod 0)) 0 (.val (wmod (W-1)))) := by
  rw [cost]
  intro capacity
  rcases capacity with zero | ⟨positive,cursor,allocator,space⟩
  · cases zero
  · have word := allocator.arrays.free.cell
    change Evm.Word.val (wmod (W-1)) = Evm.Word.val cursor at word
    have equal := Evm.Word.val.inj word
    have top : (wmod (W-1)).val = W-1 := Nat.mod_eq_of_lt (by have := W_pos; omega)
    rw [← equal, top] at space
    have positive := W_pos
    omega

theorem literal_revert_refused : (compileMemoryCall 1 F "literalRevert" args S (.user "result")
    (by decide +kernel) (by decide +kernel)
    (.cons .revert .nil : Prog C [.mem S,.mem ArrayControls.A,.val .uint]
      [.mem S,.mem ArrayControls.A,.val .uint])).isSome = false := by decide +kernel

theorem zero_base_refused : (compileStatement 0 F
    (.declMem S (.user "bad") none (by decide +kernel) (by decide +kernel) : Stmt C Γ _)).isSome =
    false := by decide +kernel

theorem reference_array_refused :
    (select? (.array (.ref (.array (.prim .uint))))).isSome = false := by decide +kernel

def sourceObservation (n : Fin W) : Option (List Nat) :=
  match call.run (caller n) with
  | .ok out => do
    let root ← out.st.env.1
    let old ← out.st.env.2.2.1
    let inner := out.st.heap.field root
      Solidity.Backend.MemoryOps.StructDefaults.NestedWordControls.layout.inner_type
    let child := out.st.heap.field inner
      Solidity.Backend.MemoryOps.StructDefaults.WordControls.layout.child_type
    let flag : Bool := out.st.heap.field root
      Solidity.Backend.MemoryOps.StructDefaults.NestedWordControls.layout.flag_type
    let tag := out.st.heap.field inner
      Solidity.Backend.MemoryOps.StructDefaults.WordControls.layout.tag_type
    pure [root.id,inner.id,child.id,old.id,out.st.H.length,out.st.heap.len child .dyn,
      if flag = true then 1 else 0,tag.val.toNat,out.st.heap.len old .dyn]
  | _ => none

def targetObservation : Evm.Out → Option (List Nat)
  | .ok target _ => (target.stack ++ [target.mem 0,target.mem 1,target.mem 2,target.mem 3,
      target.mem 16,target.mem 63] ++ (List.range 8).map (fun i => target.mem (128+i))).mapM
      (fun word => match word with | .val value => some value.val | _ => none)
  | _ => none

def expanded : Composition.Program 1 F
    (Calls.expandMem args S (.user "result") (by decide +kernel) (by decide +kernel) body) :=
  (compileProgram 1 F (Calls.expandMem args S (.user "result")
    (by decide +kernel) (by decide +kernel) body)).get (by decide +kernel)
def missingExport : List Instr := Restore.saveCells 16 (Restore.contextCells 1 Γ) ++
  expanded.checked.code ++ Restore.restoreCells 16 (Restore.contextCells 1 Γ)

#print axioms producer
#print axioms simulated_success
#print axioms simulated_revert
#print axioms capacity_refused

theorem source_observation : sourceObservation (wmod 0) = some [3,2,1,0,4,0,0,0,1] := by
  decide +kernel

theorem target_observation : targetObservation (Evm.run (plan selected 16 16).code (machine (wmod 0))) =
    some [77,135,128,0,133,20,99,1,0,0,0,130,131,0,0] := by decide +kernel

theorem missing_export_refused : targetObservation (Evm.run missingExport (machine (wmod 0))) ≠
    some [77,135,128,0,133,20,99,1,0,0,0,130,131,0,0] := by decide +kernel

#print axioms source_observation
#print axioms target_observation
#print axioms missing_export_refused
end Solidity.Backend.InternalFlow.RuntimeFrame.V3CallProducerRef.StructDefault.Controls
