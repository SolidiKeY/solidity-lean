import Solidity.Backend.InternalFlow.LocalStoreLoop
import Solidity.Backend.InternalFlow.MixedLoopPrefixes
import tests.«internal-flow».FragileReturnCalls
/-! A new two-turn actual mutating loop. Its local-only invariant is derived
from syntax plans despite old-object writes; iteration locals really unwind. -/
namespace Solidity.Backend.InternalFlow.LoopLocalChecks
open Controls (contract arrayType persistent transient)
open AllocationFrameChecks (CallerCtx contents)
open LocalStoreFlow
private def resultEq {α : Type} [DecidableEq α] : DecidableEq (TRes α)
  | .ok a,.ok b => if h : a = b then isTrue (h ▸ rfl) else isFalse (fun e => h (Except.ok.inj e))
  | .error a,.error b => if h : a = b then isTrue (h ▸ rfl) else isFalse (fun e => h (Except.error.inj e))
  | .ok _,.error _ => isFalse (by intro h; cases h)
  | .error _,.ok _ => isFalse (by intro h; cases h)
local instance {α : Type} [DecidableEq α] : DecidableEq (TRes α) := resultEq
abbrev Iteration : Ctx := .val .uint :: .mem arrayType :: CallerCtx

def initial : State contract CallerCtx := MixedLoopPrefixes.initial
def condition : Val contract CallerCtx .bool := MixedLoopPrefixes.condition

def write {Γ : Ctx} (i : Idx Γ (.mem arrayType)) (index v : Simple contract Γ .uint) :
    Stmt contract Γ Γ :=
  .assignMem (.index .dyn (.var i rfl) (.simple index)) (.val (.simple v))

def bodyWith (tail : Prog contract Iteration Iteration) : Prog contract CallerCtx Iteration :=
  .cons (.assign (.root "p" rfl) (.val
    (.binop .add rfl rfl (.read (.root "p" rfl)) (.simple (.lit 1 rfl)))))
  (.cons (.assign (.root "t" rfl) (.val
    (.binop .add rfl rfl (.read (.root "t" rfl)) (.simple (.lit 2 rfl)))))
  (.cons (write .here (.lit 0 rfl) (.local (.there (.there .here))))
  (.cons (.assignLocal (.there (.there .here))
    (.binop .add rfl rfl (.simple (.local (.there (.there .here)))) (.simple (.lit 1 rfl))))
  (.cons (.declMem arrayType (.user "iterationScratch") (some (.newArr (.lit 1 rfl) rfl)) rfl rfl)
  (.cons (write .here (.lit 0 rfl) (.local (.there (.there (.there .here)))))
  (.cons (.declLocal .uint (.user "iterationMarker") (some (.simple (.lit 77 rfl)))) tail))))))
def body : Prog contract CallerCtx Iteration := bodyWith .nil

def bodyPlan {t : LTy} (i : Idx CallerCtx t)
    (safe : (t,i.toNat) ∉ [(LTy.val .uint,2)]) : ProgPlan t body i := by
  refine .cons (.storage _ _ _) (.cons (.storage _ _ _) (.cons (.memory _ _ _)
    (.cons ?_ (.cons ?_ (.cons (.memory _ _ _) (.cons ?_ (.nil _)))))))
  · exact .existing .nonpayable _ _ (by decide +kernel) safe
  · exact .existing .nonpayable _ _ (by decide +kernel) (by exact List.not_mem_nil)
  · exact .existing .nonpayable _ _ (by decide +kernel) (by exact List.not_mem_nil)

private theorem actual_get {α : Type} (result : TRes α)
    (h : result.toOption.isSome = true) : result = .ok (result.toOption.get h) := by
  cases result with
  | error e => cases h
  | ok value => rfl

def start : Out contract initial.H CallerCtx := ⟨initial,List.prefix_refl _⟩
private theorem first_ok : (body.runR initial).toOption.isSome = true := by decide +kernel
def firstBody : Out contract initial.H Iteration := (body.runR initial).toOption.get first_ok
def first : Out contract initial.H CallerCtx := ⟨firstBody.st.drop body.ext,firstBody.ext⟩
private theorem second_ok : (body.runR first.st).toOption.isSome = true := by decide +kernel
def secondBody : Out contract first.st.H Iteration := (body.runR first.st).toOption.get second_ok
def second : Out contract initial.H CallerCtx :=
  ⟨secondBody.st.drop body.ext,first.ext.trans secondBody.ext⟩
theorem first_execution : body.runR initial = .ok firstBody := actual_get _ first_ok
theorem second_execution : body.runR first.st = .ok secondBody := actual_get _ second_ok
theorem first_step : scopedLoopBody body start = .ok first := by
  unfold scopedLoopBody
  change (body.runR initial).map _ = _
  rw [first_execution]
  rfl
theorem second_step : scopedLoopBody body first = .ok second := by
  unfold scopedLoopBody
  rw [second_execution]
  rfl
theorem conditions : condition.evalT start.st = .ok true ∧
    condition.evalT first.st = .ok true ∧ condition.evalT second.st = .ok false := by
  decide +kernel
theorem horizon_one : TLoop.iterN (scopedLoopBody body) (fun o => condition.evalT o.st) 1 start = .inl first := by
  simp only [TLoop.iterN,TLoop.step,conditions.1,first_step]
theorem horizon_two : TLoop.iterN (scopedLoopBody body) (fun o => condition.evalT o.st) 2 start = .inl second := by
  rw [loop_prefix_continue _ _ 1 1 start first horizon_one]
  simp only [TLoop.iterN,TLoop.step,conditions.2.1,second_step]
theorem horizon_three : TLoop.iterN (scopedLoopBody body) (fun o => condition.evalT o.st) 3 start = .inr (.ok second) := by
  rw [loop_prefix_continue _ _ 2 1 start second horizon_two]
  simp only [TLoop.iterN,TLoop.step,conditions.2.2]
theorem actual_loop : TRun.loop condition body.ext body.runR initial = .ok second :=
  TLoop.run_of_iterN horizon_three

/-- The invariant is applied to both actual live horizons, not assumed at a midpoint. -/
theorem protected_prefixes {t : LTy} (i : Idx CallerCtx t)
    (safe : (t,i.toNat) ∉ [(LTy.val .uint,2)]) :
    TEnv.get i first.st.env = LTy.TDenote.wk first.ext t (TEnv.get i initial.env) ∧
    TEnv.get i second.st.env = LTy.TDenote.wk second.ext t (TEnv.get i initial.env) :=
  ⟨(bodyPlan i safe).loop_prefix condition initial 1 first (.inl horizon_one),
   (bodyPlan i safe).loop_success condition initial second actual_loop⟩

structure Observation where
  heapSize : Nat
  aliasA : Option Nat
  aliasB : Option Nat
  oldA : Option (List Int)
  oldB : Option (List Int)
  counter : Int
  untouched : Int
  persistent : Int
  transient : Int
  liveLength : Nat
  liveValues : List Int
  sender : Int
  value : Int
  balance : Int
  deriving DecidableEq, Repr

def observe (out : Out contract initial.H CallerCtx) : Observation :=
  let array := (out.st.storage.get (f := "a") (T := .ref arrayType) rfl).view
  ⟨out.st.H.length,out.st.env.1.map HRef.id,out.st.env.2.1.map HRef.id,
    contents out.st .here,contents out.st (.there .here),out.st.env.2.2.1.1,out.st.env.2.2.2.1.1,
    (out.st.storage.get persistent.declared).view.1,(out.st.storage.get transient.declared).view.1,
    array.n,array.elems.toList.map (fun v => v.view.1),out.st.tx.msgSender.1,out.st.tx.msgValue.1,out.st.selfBalance.1⟩
def zeroObservation : Observation :=
  ⟨1,some 0,some 0,some [7,11],some [7,11],9,17,7,9,2,[13,17],9,7,11⟩
def oneObservation : Observation :=
  ⟨2,some 0,some 0,some [9,11],some [9,11],10,17,8,11,2,[13,17],9,7,11⟩
def twoObservation : Observation :=
  ⟨3,some 0,some 0,some [10,11],some [10,11],11,17,9,13,2,[13,17],9,7,11⟩
theorem complete_source : observe start = zeroObservation ∧ observe first = oneObservation ∧
    observe second = twoObservation := by decide +kernel

theorem private_locals :
    (firstBody.st.env.1.1,firstBody.st.env.2.1.map HRef.id,
      secondBody.st.env.1.1,secondBody.st.env.2.1.map HRef.id) = (77,some 1,77,some 2) := by decide +kernel

theorem original_guard_rejects : Prog.withinM .nonpayable body = false := by decide +kernel

theorem actual_statement : (Stmt.loop .auto condition body).run initial = .ok second := by
  rw [Stmt.run_loop]
  exact actual_loop

abbrev ProtectedCtx : Ctx := [.mem arrayType,.mem arrayType,.val .uint]
def protection : Thin ProtectedCtx CallerCtx := .keep (.keep (.drop (.keep .refl)))
theorem protected_unwritten {t : LTy} (i : Idx ProtectedCtx t) :
    (t,(i.wk protection).toNat) ∉ [(LTy.val .uint,2)] := by
  cases i with
  | here => decide +kernel
  | there i => cases i with
    | here => decide +kernel
    | there i => cases i with
      | here => decide +kernel
      | there i => cases i

theorem captured_locals : TEnv.thin protection second.st.env =
    TEnv.wk second.ext ProtectedCtx (TEnv.thin protection initial.env) := by
  apply TEnv.ext
  intro t i
  rw [CallerFrame.read_thin,TEnv.get_wk,CallerFrame.read_thin]
  exact (bodyPlan (i.wk protection) (protected_unwritten i)).loop_statement
    .auto condition initial second actual_statement

/-- A syntactic plan for the actually written scalar would give a false equation. -/
theorem written_scalar_rejected : ¬ ProgPlan (.val .uint) body (.there (.there .here)) := by
  intro plan
  have equation := congrArg Subtype.val (plan.sound first_execution)
  have after : (TEnv.get (.there (.there .here) : Idx CallerCtx (.val .uint))
      (TEnv.drop body.ext firstBody.st.env)).1 = 10 := by decide +kernel
  change (TEnv.get (.there (.there .here) : Idx CallerCtx (.val .uint))
    (TEnv.drop body.ext firstBody.st.env)).1 = _ at equation
  rw [after] at equation
  exact (by decide +kernel : (10 : Int) ≠ 9) equation

theorem wrong_alias : (observe second).aliasA ≠ some 1 := by
  rw [complete_source.2.2]
  decide +kernel

theorem private_marker_nonescape : (observe second).untouched ≠ 77 := by
  rw [complete_source.2.2]
  decide +kernel

theorem old_contents_changed : (observe second).oldA ≠ some [7,11] := by
  rw [complete_source.2.2]
  decide +kernel

theorem heap_keeps_rejected : ¬ Heap.Keeps second.ext initial.heap second.st.heap := by
  intro kept
  let ref : HRef initial.H arrayType := ⟨0,by decide +kernel⟩
  have equation := congrArg (fun o : MObj second.st.H arrayType => o.1.map Subtype.val) (kept ref)
  have actual : (second.st.heap.get (ref.wk second.ext)).1.map Subtype.val = [10,11] := by decide +kernel
  have old : (MObj.wk second.ext arrayType (initial.heap.get ref)).1.map Subtype.val = [7,11] := by decide +kernel
  change (second.st.heap.get (ref.wk second.ext)).1.map Subtype.val =
    (MObj.wk second.ext arrayType (initial.heap.get ref)).1.map Subtype.val at equation
  rw [actual,old] at equation
  exact (by decide +kernel : ([10,11] : List Int) ≠ [7,11]) equation

/-- Source identity is not an unconditional liveness guarantee. Consume the
existing actual shrink/refusal witness unchanged, rather than assuming live. -/
theorem source_alias_not_unconditionally_live :
    ¬ (∀ r : SRef FragileReturnChecks.C (.ref FragileReturnChecks.R),
      FragileReturnChecks.staleOut.st.env.1 = some r →
      ∃ sv, FragileReturnChecks.staleOut.st.storage.findLive r = some sv) := by
  intro allLive
  obtain ⟨r,bound,dead,_,_⟩ := FragileReturnChecks.CapturedResult.stale_is_not_live
  obtain ⟨sv,live⟩ := allLive r bound
  rw [dead] at live
  cases live

/-- Allocations/mutations in turn two precede this actual assert failure;
TRes.error does not expose the failed state. -/
def iterationCounter : Idx Iteration (.val .uint) := .there (.there (.there (.there .here)))
def assertCondition : Val contract Iteration .bool :=
  .binop .lt rfl rfl (.simple (.local iterationCounter)) (.simple (.lit 11 rfl))
def failingBody : Prog contract CallerCtx Iteration :=
  bodyWith (.cons (.assert assertCondition) .nil)

private theorem failing_first_ok : (failingBody.runR initial).toOption.isSome = true := by decide +kernel
def failingFirstBody : Out contract initial.H Iteration :=
  (failingBody.runR initial).toOption.get failing_first_ok
def failingFirst : Out contract initial.H CallerCtx :=
  ⟨failingFirstBody.st.drop failingBody.ext,failingFirstBody.ext⟩
theorem failing_first_execution : failingBody.runR initial = .ok failingFirstBody :=
  actual_get _ failing_first_ok
theorem failing_first : scopedLoopBody failingBody start = .ok failingFirst := by
  unfold scopedLoopBody
  change (failingBody.runR initial).map _ = _
  rw [failing_first_execution]
  rfl
theorem failing_first_observed : observe failingFirst = oneObservation := by decide +kernel
theorem failing_horizon_one : TLoop.iterN (scopedLoopBody failingBody)
    (fun o => condition.evalT o.st) 1 start = .inl failingFirst := by
  simp only [TLoop.iterN,TLoop.step,conditions.1,failing_first]

theorem failed_horizon : TLoop.iterN (scopedLoopBody failingBody)
    (fun o => condition.evalT o.st) 2 start = .inr (.error .panic) := by
  have certificate : (match TLoop.iterN (scopedLoopBody failingBody)
      (fun o => condition.evalT o.st) 2 start with
    | .inr (.error halt) => decide (halt = .panic) | _ => false) = true := by decide +kernel
  cases h : TLoop.iterN (scopedLoopBody failingBody) (fun o => condition.evalT o.st) 2 start with
  | inl out => rw [h] at certificate; cases certificate
  | inr result => cases result with
    | ok out => rw [h] at certificate; cases certificate
    | error halt =>
      rw [h] at certificate
      have same : halt = .panic := of_decide_eq_true certificate
      rw [same]

theorem failure_absorbs (n : Nat) (hn : 2 ≤ n) :
    TLoop.iterN (scopedLoopBody failingBody) (fun o => condition.evalT o.st) n start =
      .inr (.error .panic) := TLoop.iterN_done_le hn failed_horizon

theorem actual_failure : TRun.loop condition failingBody.ext failingBody.runR initial = .error .panic :=
  TLoop.run_of_iterN failed_horizon

theorem failure_classes :
    TRun.loop condition failingBody.ext failingBody.runR initial ≠ .error .revert ∧
    TRun.loop condition failingBody.ext failingBody.runR initial ≠ .error .exhausted ∧
    TRun.loop condition failingBody.ext failingBody.runR initial ≠ .error .diverge := by
  rw [actual_failure]
  constructor
  · intro h; cases h
  · constructor
    · intro h; cases h
    · intro h; cases h

def badCondition : Val contract CallerCtx .bool :=
  .binop .eqB rfl rfl (.readMem (.index .dyn (.var .here rfl) (.simple (.lit 99 rfl))))
    (.simple (.lit 0 rfl))
theorem condition_error : badCondition.evalT initial = .error .revert := by decide +kernel
theorem condition_failure : TRun.loop badCondition body.ext body.runR initial = .error .revert := by
  apply TLoop.run_of_iterN (n := 1)
  simp only [TLoop.iterN,TLoop.step,condition_error]

def spin : Prog contract CallerCtx CallerCtx := .nil
theorem spin_horizon (n : Nat) : TLoop.iterN (scopedLoopBody spin)
    (fun _ => (.ok true : TRes Bool)) n start = .inl start := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih

theorem actual_divergence : TRun.loop (.simple (.bool true)) spin.ext spin.runR initial = .error .diverge := by
  exact loop_all_prefixes_running (scopedLoopBody spin) (fun _ => .ok true) start
    (fun n => ⟨start,spin_horizon n⟩)

def scratchOne : HRef second.st.H arrayType := ⟨1,by decide +kernel⟩
def scratchTwo : HRef second.st.H arrayType := ⟨2,by decide +kernel⟩
theorem complete_scratch_contents :
    ((second.st.heap.get scratchOne).1.map Subtype.val,
     (second.st.heap.get scratchTwo).1.map Subtype.val) = ([10],[11]) := by decide +kernel

theorem exact_unwind : second.st.env = TEnv.drop body.ext secondBody.st.env ∧
    second.ext = first.ext.trans secondBody.ext := ⟨rfl,rfl⟩

theorem skipped_success : TRun.loop (.simple (.bool false)) body.ext body.runR initial = .ok start := by
  apply TLoop.run_of_iterN (n := 1)
  rfl


theorem ordered_horizons :
    ([0,1,2,3].map fun n => (TLoop.iterN (scopedLoopBody body)
      (fun o => condition.evalT o.st) n start).map observe (Except.map observe)) =
      [.inl zeroObservation,.inl oneObservation,.inl twoObservation,.inr (.ok twoObservation)] := by
  simp only [List.map_cons,List.map_nil]
  rw [show TLoop.iterN (scopedLoopBody body) (fun o => condition.evalT o.st) 0 start = .inl start from rfl,
    horizon_one,horizon_two,horizon_three]
  simp only [Sum.map_inl,Sum.map_inr,Except.map,complete_source.1,
    complete_source.2.1,complete_source.2.2]

theorem ordered_failure_horizons :
    ([0,1,2,3].map fun n => (TLoop.iterN (scopedLoopBody failingBody)
      (fun o => condition.evalT o.st) n start).map observe (Except.map observe)) =
      [.inl zeroObservation,.inl oneObservation,.inr (.error .panic),.inr (.error .panic)] := by
  simp only [List.map_cons,List.map_nil]
  rw [show TLoop.iterN (scopedLoopBody failingBody) (fun o => condition.evalT o.st) 0 start = .inl start from rfl,
    failing_horizon_one,failed_horizon,failure_absorbs 3 (by decide +kernel)]
  simp only [Sum.map_inl,Sum.map_inr,Except.map,complete_source.1,failing_first_observed]

end Solidity.Backend.InternalFlow.LoopLocalChecks

#print axioms Solidity.Backend.InternalFlow.LocalStoreFlow.ProgPlan.scoped_step
#print axioms Solidity.Backend.InternalFlow.LocalStoreFlow.ProgPlan.loop_prefix
#print axioms Solidity.Backend.InternalFlow.LocalStoreFlow.ProgPlan.loop_success
#print axioms Solidity.Backend.InternalFlow.LocalStoreFlow.ProgPlan.loop_statement
#print axioms Solidity.Backend.InternalFlow.LoopLocalChecks.bodyPlan
#print axioms Solidity.Backend.InternalFlow.LoopLocalChecks.first_execution
#print axioms Solidity.Backend.InternalFlow.LoopLocalChecks.second_execution
#print axioms Solidity.Backend.InternalFlow.LoopLocalChecks.first_step
#print axioms Solidity.Backend.InternalFlow.LoopLocalChecks.second_step
#print axioms Solidity.Backend.InternalFlow.LoopLocalChecks.conditions
#print axioms Solidity.Backend.InternalFlow.LoopLocalChecks.horizon_one
#print axioms Solidity.Backend.InternalFlow.LoopLocalChecks.horizon_two
#print axioms Solidity.Backend.InternalFlow.LoopLocalChecks.horizon_three
#print axioms Solidity.Backend.InternalFlow.LoopLocalChecks.actual_loop
#print axioms Solidity.Backend.InternalFlow.LoopLocalChecks.protected_prefixes
#print axioms Solidity.Backend.InternalFlow.LoopLocalChecks.complete_source
#print axioms Solidity.Backend.InternalFlow.LoopLocalChecks.private_locals
#print axioms Solidity.Backend.InternalFlow.LoopLocalChecks.original_guard_rejects
#print axioms Solidity.Backend.InternalFlow.LoopLocalChecks.actual_statement
#print axioms Solidity.Backend.InternalFlow.LoopLocalChecks.protected_unwritten
#print axioms Solidity.Backend.InternalFlow.LoopLocalChecks.captured_locals
#print axioms Solidity.Backend.InternalFlow.LoopLocalChecks.written_scalar_rejected
#print axioms Solidity.Backend.InternalFlow.LoopLocalChecks.wrong_alias
#print axioms Solidity.Backend.InternalFlow.LoopLocalChecks.private_marker_nonescape
#print axioms Solidity.Backend.InternalFlow.LoopLocalChecks.old_contents_changed
#print axioms Solidity.Backend.InternalFlow.LoopLocalChecks.heap_keeps_rejected
#print axioms Solidity.Backend.InternalFlow.LoopLocalChecks.source_alias_not_unconditionally_live
#print axioms Solidity.Backend.InternalFlow.LoopLocalChecks.failing_first_execution
#print axioms Solidity.Backend.InternalFlow.LoopLocalChecks.failing_first
#print axioms Solidity.Backend.InternalFlow.LoopLocalChecks.failing_first_observed
#print axioms Solidity.Backend.InternalFlow.LoopLocalChecks.failing_horizon_one
#print axioms Solidity.Backend.InternalFlow.LoopLocalChecks.failed_horizon
#print axioms Solidity.Backend.InternalFlow.LoopLocalChecks.failure_absorbs
#print axioms Solidity.Backend.InternalFlow.LoopLocalChecks.actual_failure
#print axioms Solidity.Backend.InternalFlow.LoopLocalChecks.failure_classes
#print axioms Solidity.Backend.InternalFlow.LoopLocalChecks.condition_error
#print axioms Solidity.Backend.InternalFlow.LoopLocalChecks.condition_failure
#print axioms Solidity.Backend.InternalFlow.LoopLocalChecks.spin_horizon
#print axioms Solidity.Backend.InternalFlow.LoopLocalChecks.actual_divergence
#print axioms Solidity.Backend.InternalFlow.LoopLocalChecks.complete_scratch_contents
#print axioms Solidity.Backend.InternalFlow.LoopLocalChecks.exact_unwind
#print axioms Solidity.Backend.InternalFlow.LoopLocalChecks.skipped_success
#print axioms Solidity.Backend.InternalFlow.LoopLocalChecks.ordered_horizons
#print axioms Solidity.Backend.InternalFlow.LoopLocalChecks.ordered_failure_horizons
