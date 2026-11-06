import Solidity.Backend.InternalFlow.RuntimeFrameV3CallProducerRefStructDefaultControls

/-! Real struct arguments and whole-struct return rebinding. The old nested
struct is itself constructed by the checked default declaration; its initial
representation is derived from that real source/compiled prefix. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.V3CallProducerRef.StructDefault.RebindControls
open Evm Evm.Memory
abbrev C := ArrayControls.C
abbrev S := Controls.S
abbrev Γ : Ctx := .mem S :: ArrayControls.Γ
abbrev F := Frag.init Γ

def seed : Composition.Statement 1 ArrayControls.F
    (.declMem S (.user "old") none (by decide +kernel) (by decide +kernel) : Stmt C ArrayControls.Γ Γ) :=
  (compileStatement 1 ArrayControls.F
    (.declMem S (.user "old") none (by decide +kernel) (by decide +kernel))).get (by decide +kernel)
def grown (n : Fin W) := (ArrayControls.caller n).allocDefaultG S (by decide +kernel)
def caller (n : Fin W) : State C Γ :=
  (grown n).st.push (t := .mem S) (some (grown n).val)
def machine (n : Fin W) : Machine :=
  match Evm.run seed.checked.code (ArrayControls.machine n) with
  | .ok target _ => target
  | _ => ArrayControls.machine n

def InitialGoal : Prop := ∀ n : Fin W, ∃ base : Nat → Fin W,
  StateRepr 1 1 64 F (caller n) base (machine n) ∧
  StructAllocatorRepr (caller n).heap base 64 (wmod 135) (machine n)

theorem seed_cost (n : Fin W) : seed.checked.cost (ArrayControls.caller n) = 5 := by
  with_unfolding_all rfl

/-- Obtain the old graph and its representation from the real checked
allocation prefix, not from an initial-representation assumption. -/
theorem initial_exists : InitialGoal := by
  intro n
  have capacity : AllocationInput 1 64 (seed.checked.cost (ArrayControls.caller n))
      (ArrayControls.caller n) ArrayControls.bases (ArrayControls.machine n) :=
    .inr ⟨by decide, wmod 130, (ArrayControls.initial n).2, by rw [seed_cost]; decide⟩
  rcases seed.checked.sound (ArrayControls.initial n).1 (by decide +kernel) capacity with
    ⟨out,target,base,source,executed,reached,stack,extension,growth⟩ | ⟨source,executed⟩
  · have stateSame : out.st = caller n := by
      have equation := congrArg (fun res => res.map (fun out => out.st)) source
      change (Except.ok (caller n) : TRes (State C Γ)) = Except.ok out.st at equation
      exact (Except.ok.inj equation).symm
    have targetSame : target = machine n := by
      unfold machine
      rw [executed]
    have owned := growth (wmod 130) (by decide) (ArrayControls.initial n).2
      (by rw [seed_cost]; decide)
    rw [stateSame, targetSame] at reached owned
    exact ⟨base, reached, by simpa only [seed_cost] using owned⟩
  · change (Except.ok _ : TRes (Solidity.Out C (ArrayControls.caller n).H Γ)) =
      Except.error .revert at source
    cases source

/-- Choice fixes a represented identity/base map for proofs only. Neither
source execution nor target instruction execution evaluates this map. -/
noncomputable def bases (n : Fin W) : Nat → Fin W := Classical.choose (initial_exists n)
theorem initial (n : Fin W) : StateRepr 1 1 64 F (caller n) (bases n) (machine n) ∧
    StructAllocatorRepr (caller n).heap (bases n) 64 (wmod 135) (machine n) :=
  Classical.choose_spec (initial_exists n)

#print axioms initial_exists

def args : Args C Γ [.mem S,.mem ArrayControls.A,.val .uint] :=
  .snocMemory (.snocMemory
    (.snoc .nil .uint (.user "index") (.simple (.local (.there .here))))
    ArrayControls.A (.user "array") (.var (.there (.there .here)) rfl))
    S (.user "old") (.var .here (by decide +kernel))
def ret : CallRet Γ [.mem S] (.mem S :: Γ) :=
  .mem S (.user "result") (by decide +kernel) (by decide +kernel)
def body : Prog C [.mem S,.mem S,.mem ArrayControls.A,.val .uint]
    [.val .uint,.mem S,.mem S,.mem ArrayControls.A,.val .uint] :=
  .cons (.rebindMem .here (.alias (.var (.there .here) (by decide +kernel))))
    (.cons (.declLocal .uint (.user "observed")
      (some (.readMem (.index .dyn (.var (.there (.there .here)) rfl)
        (.simple (.local (.there (.there (.there .here))))))))) .nil)
def call : Stmt C Γ (.mem S :: Γ) := .call "structAlias" args ret body

def statement : Composition.Statement 1 F call :=
  (compileMemoryCall 1 F "structAlias" args S (.user "result")
    (by decide +kernel) (by decide +kernel) body).get (by decide +kernel)
def selected : Composition.Program 1 F (.cons call .nil) :=
  Composition.cons statement (Composition.nil 1 statement.checked.frag)

/-- Reuse checked prefix execution, avoiding repeated reduction of its code. -/
theorem seed_executed (n : Fin W) : Evm.run seed.checked.code (ArrayControls.machine n) =
    .ok (machine n) 0 := by
  have capacity : AllocationInput 1 64 (seed.checked.cost (ArrayControls.caller n))
      (ArrayControls.caller n) ArrayControls.bases (ArrayControls.machine n) :=
    .inr ⟨by decide, wmod 130, (ArrayControls.initial n).2, by rw [seed_cost]; decide⟩
  rcases seed.checked.sound (ArrayControls.initial n).1 (by decide +kernel) capacity with
    ⟨out,target,base,source,executed,reached,stack,extension,growth⟩ | ⟨source,executed⟩
  · unfold machine
    rw [executed]
  · change (Except.ok _ : TRes (Solidity.Out C (ArrayControls.caller n).H Γ)) =
      Except.error .revert at source
    cases source

/-- The actual prefix footprint proves the runtime cursor word is unchanged. -/
theorem machine_runtime (n : Fin W) : (machine n).mem 16 = .val (wmod 20) := by
  have capacity : AllocationInput 1 64 (seed.checked.cost (ArrayControls.caller n))
      (ArrayControls.caller n) ArrayControls.bases (ArrayControls.machine n) :=
    .inr ⟨by decide, wmod 130, (ArrayControls.initial n).2, by rw [seed_cost]; decide⟩
  have words := seed.safe (ArrayControls.initial n).1 (lo := 16) (by decide +kernel)
    (by decide) capacity (seed_executed n)
  exact (words 16 (by decide) (by decide)).trans rfl

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
 (caller n) (bases n) (machine n) :=
 .inr ⟨by decide,wmod 135,(initial n).2,by rw [cost];decide⟩

theorem member (n : Fin W) : admitted selected 16 16 1 64 (caller n) (bases n) (machine n) 20 :=
 ⟨(initial n).1,by decide +kernel,by decide,by decide,by decide,by decide,
  by decide,by decide,machine_runtime n,capacity n⟩

theorem entered (n : Fin W) : InterfaceV1.Entry (plan selected 16 16) 1 1 64 F
 (caller n) (bases n) (machine n) 20 := coverage selected 16 16 1 64 (caller n) (bases n) (machine n) 20 (member n)

theorem successful : InterfaceV3.SuccessfulEntry 1 F (admitted selected 16 16)
 call (plan selected 16 16) := by
 obtain ⟨out,source⟩ := source_success
 exact ⟨1,64,caller (wmod 0),bases (wmod 0),machine (wmod 0),20,out,
  member _,entered _,source⟩

theorem reverting : InterfaceV3.RevertingEntry 1 F (admitted selected 16 16)
 call (plan selected 16 16) :=
 ⟨1,64,caller (wmod 2),bases (wmod 2),machine (wmod 2),20,member _,entered _,source_revert⟩

def producer (approved : InterfaceV3.Admission C Γ)
 (hprof : InterfaceV3.AdmissionAgreement approved (admitted selected 16 16)) :
 InterfaceV3.PendingCallProducer 1 F approved (admitted selected 16 16)
  "structAlias" args ret body :=
 make form selected 16 16 approved hprof flags successful reverting

theorem simulated_success : ∃ out : Solidity.Out C (caller (wmod 0)).H (.mem S::Γ),
 call.run (caller (wmod 0))=.ok out ∧
 InterfaceV1.Returned (plan selected 16 16) 1 1 64 (caller (wmod 0)) (bases (wmod 0)) (machine (wmod 0)) 20 out := by
 obtain ⟨out,source⟩ := source_success
 exact ⟨out,source,returns form selected 16 16 flags 1 64 (caller (wmod 0)) (bases (wmod 0))
  (machine (wmod 0)) 20 (entered _) out source⟩

theorem simulated_revert : Evm.run (plan selected 16 16).code (machine (wmod 2))=.revert :=
 bare_revert selected 16 16 1 64 (caller (wmod 2)) (bases (wmod 2)) (machine (wmod 2)) 20 (entered _) source_revert

theorem capacity_refused : ¬ AllocationInput 1 64 (selected.checked.cost (caller (wmod 0)))
    (caller (wmod 0)) (bases (wmod 0)) (writeMachine (machine (wmod 0)) 0 (.val (wmod (W-1)))) := by
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

def sourceObservation (n : Fin W) : Option (List Nat) :=
  match call.run (caller n) with
  | .ok out => do
    let returned ← out.st.env.1
    let old ← out.st.env.2.1
    let oldArray ← out.st.env.2.2.2.1
    let inner := out.st.heap.field returned
      Solidity.Backend.MemoryOps.StructDefaults.NestedWordControls.layout.inner_type
    let child := out.st.heap.field inner
      Solidity.Backend.MemoryOps.StructDefaults.WordControls.layout.child_type
    pure [returned.id,old.id,inner.id,child.id,oldArray.id,out.st.H.length,
      out.st.heap.len child .dyn,out.st.heap.len oldArray .dyn]
  | _ => none

def targetObservation : Evm.Out → Option (List Nat)
  | .ok target _ => (target.stack ++ [target.mem 0,target.mem 1,target.mem 2,target.mem 3,
      target.mem 4,target.mem 16,target.mem 63] ++
      (List.range 13).map (fun i => target.mem (128+i))).mapM
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

theorem source_observation : sourceObservation (wmod 0) = some [3,3,2,1,0,7,0,1] := by
  decide +kernel

theorem target_observation : targetObservation (Evm.run (plan selected 16 16).code (machine (wmod 0))) =
    some [77,140,128,0,133,133,20,99,1,0,0,0,130,131,0,0,0,135,136,0,0] := by decide +kernel

theorem missing_export_refused : targetObservation (Evm.run missingExport (machine (wmod 0))) ≠
    some [77,140,128,0,133,133,20,99,1,0,0,0,130,131,0,0,0,135,136,0,0] := by decide +kernel

/-- Returning the newly defaulted root would lose the required old alias. -/
theorem default_root_refused : sourceObservation (wmod 0) ≠ some [6,3,5,4,0,7,0,1] := by
  decide +kernel

#print axioms source_observation
#print axioms target_observation
#print axioms missing_export_refused
#print axioms default_root_refused

end Solidity.Backend.InternalFlow.RuntimeFrame.V3CallProducerRef.StructDefault.RebindControls
