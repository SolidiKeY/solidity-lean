import Solidity.Backend.InternalFlow.ScopedLoopFrame
import Solidity.Backend.InternalFlow.AllocationFrameChecks

/-! Actual multi-iteration mixed-state loop controls. Finite horizons are
observations of TLoop.iterN, not synthetic events or a new evaluator. -/
namespace Solidity.Backend.InternalFlow.MixedLoopPrefixes
open Controls (contract arrayType persistent transient)
open AllocationFrameChecks (CallerCtx contents)

private def resultEq {α : Type} [DecidableEq α] : DecidableEq (TRes α)
  | .ok a, .ok b => if h : a = b then isTrue (h ▸ rfl) else isFalse (fun e => h (Except.ok.inj e))
  | .error a, .error b => if h : a = b then isTrue (h ▸ rfl) else isFalse (fun e => h (Except.error.inj e))
  | .ok _, .error _ => isFalse (by intro h; cases h)
  | .error _, .ok _ => isFalse (by intro h; cases h)

abbrev Local : Ctx := .mem arrayType :: CallerCtx

def initial : State contract CallerCtx :=
  AllocationFrameChecks.caller.setLocal (.there (.there (.there .here))) ⟨17, rfl⟩
def condition : Val contract CallerCtx .bool :=
  .binop .lt rfl rfl (.simple (.local (.there (.there .here)))) (.simple (.lit 11 rfl))

def bodyWith (tail : Prog contract Local Local) : Prog contract CallerCtx Local :=
  .cons (.assign (.root "p" rfl) (.val
    (.binop .add rfl rfl (.read (.root "p" rfl)) (.simple (.lit 1 rfl)))))
  (.cons (.assign (.root "t" rfl) (.val
    (.binop .add rfl rfl (.read (.root "t" rfl)) (.simple (.lit 2 rfl)))))
  (.cons (.push (.loc (.root "a" rfl))
    (some (.val (.simple (.local (.there (.there .here)))))) rfl)
  (.cons (.pop (.loc (.root "a" rfl)))
  (.cons (.pop (.loc (.root "a" rfl)))
  (.cons (.assignLocal (.there (.there .here))
    (.binop .add rfl rfl (.simple (.local (.there (.there .here)))) (.simple (.lit 1 rfl))))
  (.cons (.declMem arrayType (.user "scratch") (some (.newArr (.lit 2 rfl) rfl)) rfl rfl) tail))))))
def body : Prog contract CallerCtx Local := bodyWith .nil

def start : Out contract initial.H CallerCtx := ⟨initial, List.prefix_refl _⟩
@[irreducible] def firstBody : Out contract initial.H Local :=
  match body.runR initial with
  | .ok out => out
  | .error _ => ⟨initial.push (t := .mem arrayType) none, List.prefix_refl _⟩
def first : Out contract initial.H CallerCtx := ⟨firstBody.st.drop body.ext, firstBody.ext⟩
@[irreducible] def secondBody : Out contract first.st.H Local :=
  match body.runR first.st with
  | .ok out => out
  | .error _ => ⟨first.st.push (t := .mem arrayType) none, List.prefix_refl _⟩
def second : Out contract initial.H CallerCtx :=
  ⟨secondBody.st.drop body.ext, first.ext.trans secondBody.ext⟩

/-- Published withinM rejects push/pop even at nonpayable. No relaxation. -/
theorem mixed_body_rejected : Prog.withinM .nonpayable body = false := rfl

theorem first_execution : body.runR initial = .ok firstBody := by
  have success : (match body.runR initial with | .ok _ => true | .error _ => false) = true := by decide +kernel
  cases h : body.runR initial with
  | ok out => simp only [firstBody, h]
  | error halt => rw [h] at success; cases success

theorem second_execution : body.runR first.st = .ok secondBody := by
  have success : (match body.runR first.st with | .ok _ => true | .error _ => false) = true := by decide +kernel
  cases h : body.runR first.st with
  | ok out => simp only [secondBody, h]
  | error halt => rw [h] at success; cases success

theorem first_step : scopedLoopBody body start = .ok first := by
  unfold scopedLoopBody
  change (body.runR initial).map _ = _
  rw [first_execution]
  rfl

theorem second_step : scopedLoopBody body first = .ok second := by
  unfold scopedLoopBody
  rw [second_execution]
  rfl

theorem initial_condition : condition.evalT start.st = .ok true := by rfl

theorem first_condition : condition.evalT first.st = .ok true := by
  apply @of_decide_eq_true _ (resultEq _ _)
  decide +kernel

theorem second_condition : condition.evalT second.st = .ok false := by
  apply @of_decide_eq_true _ (resultEq _ _)
  decide +kernel

theorem horizon_zero : TLoop.iterN (scopedLoopBody body) (fun o => condition.evalT o.st) 0 start = .inl start := rfl

theorem horizon_one : TLoop.iterN (scopedLoopBody body) (fun o => condition.evalT o.st) 1 start = .inl first := by
  simp only [TLoop.iterN, TLoop.step, initial_condition, first_step]

theorem horizon_two : TLoop.iterN (scopedLoopBody body) (fun o => condition.evalT o.st) 2 start = .inl second := by
  rw [loop_prefix_continue (scopedLoopBody body) (fun o => condition.evalT o.st) 1 1 start first horizon_one]
  simp only [TLoop.iterN, TLoop.step, first_condition, second_step]

/-- The exact published horizon-split consumer, at a nonzero split. -/
theorem horizon_split : TLoop.iterN (scopedLoopBody body) (fun o => condition.evalT o.st) (1 + 2) start =
    TLoop.iterN (scopedLoopBody body) (fun o => condition.evalT o.st) 2 first :=
  loop_prefix_continue (scopedLoopBody body) (fun o => condition.evalT o.st) 1 2 start first horizon_one

theorem horizon_three : TLoop.iterN (scopedLoopBody body) (fun o => condition.evalT o.st) 3 start = .inr (.ok second) := by
  rw [horizon_split]
  simp only [TLoop.iterN, TLoop.step, first_condition, second_step, second_condition]

theorem actual_loop : TRun.loop condition body.ext body.runR initial = .ok second :=
  TLoop.run_of_iterN horizon_three

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
  shadowLength : Nat
  liveValues : List Int
  shadowValues : List Int
  sender : Int
  value : Int
  balance : Int
  deriving DecidableEq, Repr

def observe (out : Out contract initial.H CallerCtx) : Observation :=
  let array := (out.st.storage.get (f := "a") (T := .ref arrayType) rfl).view
  ⟨out.st.H.length, out.st.env.1.map HRef.id, out.st.env.2.1.map HRef.id,
    contents out.st .here, contents out.st (.there .here), out.st.env.2.2.1.1, out.st.env.2.2.2.1.1,
    (out.st.storage.get persistent.declared).view.1, (out.st.storage.get transient.declared).view.1,
    array.n, array.shadow.toList.length, array.elems.toList.map (fun v => v.view.1),
    array.shadow.toList.map (fun v => v.view.1), out.st.tx.msgSender.1, out.st.tx.msgValue.1, out.st.selfBalance.1⟩

def zeroObservation : Observation :=
  ⟨1, some 0, some 0, some [7,11], some [7,11], 9,17,7,9,2,0,[13,17],[],9,7,11⟩
def oneObservation : Observation :=
  ⟨2, some 0, some 0, some [7,11], some [7,11], 10,17,8,11,1,2,[13],[0,0],9,7,11⟩
def twoObservation : Observation :=
  ⟨3, some 0, some 0, some [7,11], some [7,11], 11,17,9,13,0,3,[],[0,0,0],9,7,11⟩

theorem every_state_observed : observe start = zeroObservation ∧ observe first = oneObservation ∧
    observe second = twoObservation := by decide +kernel

/-- Ordered complete projections of each actual horizon, including running
versus successful completion; no event semantics is introduced. -/
theorem ordered_horizons :
    ([0,1,2,3].map fun n => (TLoop.iterN (scopedLoopBody body) (fun o => condition.evalT o.st) n start).map
      observe (Except.map observe)) =
      [.inl zeroObservation, .inl oneObservation, .inl twoObservation, .inr (.ok twoObservation)] := by
  simp only [List.map_cons, List.map_nil]
  rw [horizon_zero, horizon_one, horizon_two, horizon_three]
  simp only [Sum.map_inl, Sum.map_inr, Except.map, every_state_observed.1,
    every_state_observed.2.1, every_state_observed.2.2]

theorem successful_observation : (TRun.loop condition body.ext body.runR initial).map observe = .ok twoObservation := by
  rw [actual_loop]
  exact congrArg Except.ok every_state_observed.2.2

theorem allocations : (firstBody.st.env.1.map HRef.id, secondBody.st.env.1.map HRef.id,
    first.st.H.length, second.st.H.length) = (some 1, some 2, 2, 3) := by decide +kernel

theorem transaction_boundary :
    ((second.st.glob.transactionEntry.storage.get persistent.declared).view.1,
      (second.st.glob.transactionEntry.storage.get transient.declared).view.1,
      second.st.glob.transactionEntry.H.length) = (9,0,0) := by decide +kernel

/-- Every object in this actual caller heap, not just an endpoint projection.
The singleton heap's typed-reference cases are exhausted explicitly. -/
theorem concrete_old_heap : Heap.Keeps second.ext initial.heap second.st.heap := by
  intro R r
  obtain ⟨i, hi⟩ := r
  have shape : initial.H = [arrayType] := by decide +kernel
  have hb : i < 1 := by simpa only [shape, List.length_singleton] using (List.getElem?_eq_some_iff.mp hi).1
  have hz : i = 0 := by omega
  subst i
  have hR : R = arrayType := by
    rw [shape] at hi
    exact (Option.some.inj hi).symm
  subst R
  apply Subtype.ext
  change (second.st.heap.get (HRef.wk second.ext (⟨0, by decide +kernel⟩ : HRef initial.H arrayType))).1 =
    (MObj.wk second.ext arrayType (initial.heap.get (⟨0, by decide +kernel⟩ : HRef initial.H arrayType))).1
  apply @of_decide_eq_true _ ((inferInstance : DecidableEq (List PrimTy.uint.Denote)) _ _)
  decide +kernel


def failureBytes : List UInt8 := [0xde,0xad,0x22,0]
def failureCondition : Val contract Local .bool :=
  .binop .eqB rfl rfl (.simple (.local (.there (.there (.there .here))))) (.simple (.lit 11 rfl))
def failingBody : Prog contract CallerCtx Local := bodyWith
  (.cons (.ite failureCondition (.cons (.revertData [.bytes failureBytes]) .nil) .nil) .nil)

def failedHorizon (n : Nat) : Out contract initial.H CallerCtx ⊕ TRes (Out contract initial.H CallerCtx) :=
  TLoop.iterN (scopedLoopBody failingBody) (fun o => condition.evalT o.st) n start

private def sumEq {α β : Type} [DecidableEq α] [DecidableEq β] : DecidableEq (Sum α β)
  | .inl a, .inl b => if h : a = b then isTrue (h ▸ rfl) else isFalse (fun e => h (Sum.inl.inj e))
  | .inr a, .inr b => if h : a = b then isTrue (h ▸ rfl) else isFalse (fun e => h (Sum.inr.inj e))
  | .inl _, .inr _ => isFalse (by intro h; cases h)
  | .inr _, .inl _ => isFalse (by intro h; cases h)
private def observedEq : DecidableEq (Observation ⊕ TRes Observation) := @sumEq _ _ inferInstance (@resultEq _ inferInstance)

theorem failure_first_horizon : (failedHorizon 1).map observe (Except.map observe) = .inl oneObservation := by
  apply @of_decide_eq_true _ (observedEq _ _)
  decide +kernel

theorem failure_second_horizon : failedHorizon 2 = .inr (.error (.revertWith failureBytes)) := by
  have certificate : (match failedHorizon 2 with
    | .inr (.error halt) => decide (halt = .revertWith failureBytes) | _ => false) = true := by decide +kernel
  cases h : failedHorizon 2 with
  | inl out => rw [h] at certificate; cases certificate
  | inr outcome =>
    cases outcome with
    | ok out => rw [h] at certificate; cases certificate
    | error halt =>
      rw [h] at certificate
      have hh : halt = .revertWith failureBytes := of_decide_eq_true certificate
      rw [hh]

theorem second_body_failure : failingBody.runR first.st = .error (.revertWith failureBytes) := by
  have certificate : (match failingBody.runR first.st with
    | .error halt => decide (halt = .revertWith failureBytes) | .ok _ => false) = true := by decide +kernel
  cases h : failingBody.runR first.st with
  | ok out => rw [h] at certificate; cases certificate
  | error halt =>
    rw [h] at certificate
    have hh : halt = .revertWith failureBytes := of_decide_eq_true certificate
    rw [hh]

theorem failure_absorbs (n : Nat) (hn : 2 ≤ n) : failedHorizon n = .inr (.error (.revertWith failureBytes)) :=
  TLoop.iterN_done_le hn failure_second_horizon

theorem failure_zero_horizon : failedHorizon 0 = .inl start := rfl

theorem ordered_failure_horizons :
    ([0,1,2,3].map fun n => (failedHorizon n).map observe (Except.map observe)) =
      [.inl zeroObservation, .inl oneObservation, .inr (.error (.revertWith failureBytes)),
        .inr (.error (.revertWith failureBytes))] := by
  simp only [List.map_cons, List.map_nil]
  rw [failure_zero_horizon, failure_first_horizon, failure_second_horizon, failure_absorbs 3 (by decide)]
  simp only [Sum.map_inl, Sum.map_inr, Except.map, every_state_observed.1]

theorem actual_failing_loop : TRun.loop condition failingBody.ext failingBody.runR initial =
    .error (.revertWith failureBytes) := TLoop.run_of_iterN failure_second_horizon

theorem failure_not_exhaustion : TRun.loop condition failingBody.ext failingBody.runR initial ≠ .error .exhausted := by
  rw [actual_failing_loop]
  intro h
  cases h

theorem failure_not_divergence : TRun.loop condition failingBody.ext failingBody.runR initial ≠ .error .diverge := by
  rw [actual_failing_loop]
  intro h
  cases h

theorem wrong_payload : TRun.loop condition failingBody.ext failingBody.runR initial ≠ .error (.revertWith [0xde,0xad,0,0x22]) := by
  rw [actual_failing_loop]
  intro h
  have hh : failureBytes = [0xde,0xad,0,0x22] := THalt.revertWith.inj (Except.error.inj h)
  have bad : (failureBytes[2]!) = (0 : UInt8) := congrArg (fun xs => xs[2]!) hh
  contradiction

private theorem reference_option_ext {H : HTy} {R : RefTy} {a b : Option (HRef H R)}
    (h : a.map HRef.id = b.map HRef.id) : a = b := by
  cases a with
  | none => cases b <;> cases h; rfl
  | some a =>
    cases b with
    | none => cases h
    | some b =>
      obtain ⟨i, hi⟩ := a
      obtain ⟨j, hj⟩ := b
      have hij : i = j := Option.some.inj h
      cases hij
      rfl

theorem mixed_alias_transport :
    second.st.env.1 = LTy.TDenote.wk second.ext (.mem arrayType) initial.env.1 ∧
    second.st.env.2.1 = LTy.TDenote.wk second.ext (.mem arrayType) initial.env.2.1 := by
  constructor <;> apply reference_option_ext <;> decide +kernel

theorem exact_second_extension_and_unwind :
    second.ext = first.ext.trans secondBody.ext ∧
    second.st.env = TEnv.drop body.ext secondBody.st.env := ⟨rfl, rfl⟩

def scratchContents {H : HTy} (heap : Heap H) (reference : Option (HRef H arrayType)) : Option (List Int) :=
  reference.map (fun (r : HRef H arrayType) => (heap.get r).1.map Subtype.val)

@[irreducible] def firstScratchFinal : Option (HRef second.st.H arrayType) :=
  firstBody.st.env.1.map (@HRef.wk firstBody.st.H second.st.H arrayType secondBody.ext)

def scratchOne : HRef second.st.H arrayType := ⟨1, by decide +kernel⟩
def scratchTwo : HRef second.st.H arrayType := ⟨2, by decide +kernel⟩

theorem transported_scratch_identities : firstScratchFinal = some scratchOne ∧
    secondBody.st.env.1 = some scratchTwo := by
  constructor
  · apply @reference_option_ext second.st.H arrayType firstScratchFinal (some scratchOne)
    change firstScratchFinal.map HRef.id = some 1
    decide +kernel
  · apply @reference_option_ext second.st.H arrayType secondBody.st.env.1 (some scratchTwo)
    change secondBody.st.env.1.map HRef.id = some 2
    exact congrArg (fun v => v.2.1) allocations

theorem scratch_contents_canonical :
    (@scratchContents second.st.H second.st.heap (some scratchOne),
      @scratchContents second.st.H second.st.heap (some scratchTwo)) = (some [0,0], some [0,0]) := by
  decide +kernel

theorem scratch_contents_survive :
    (@scratchContents second.st.H second.st.heap firstScratchFinal,
      @scratchContents second.st.H second.st.heap secondBody.st.env.1) = (some [0,0], some [0,0]) := by
  have a : @scratchContents second.st.H second.st.heap firstScratchFinal =
      @scratchContents second.st.H second.st.heap (some scratchOne) :=
    congrArg (@scratchContents second.st.H second.st.heap) transported_scratch_identities.1
  have b : @scratchContents second.st.H second.st.heap secondBody.st.env.1 =
      @scratchContents second.st.H second.st.heap (some scratchTwo) :=
    congrArg (@scratchContents second.st.H second.st.heap) transported_scratch_identities.2
  exact (congrArg (fun x : Option (List Int) =>
    (x, @scratchContents second.st.H second.st.heap secondBody.st.env.1)) a).trans
      ((congrArg (fun y : Option (List Int) =>
        (@scratchContents second.st.H second.st.heap (some scratchOne), y)) b).trans
          scratch_contents_canonical)

/-- A real admitted allocation/local-update body exercises the generic frame
consumer. The full mixed push/pop body above is expressly NOT admitted. -/
def allocationBody : Prog contract CallerCtx Local :=
  .cons (.assignLocal (.there (.there .here))
    (.binop .add rfl rfl (.simple (.local (.there (.there .here)))) (.simple (.lit 1 rfl))))
  (.cons (.declMem arrayType (.user "scratch") (some (.newArr (.lit 2 rfl) rfl)) rfl rfl) .nil)

def allocationHorizon : Out contract initial.H CallerCtx ⊕ TRes (Out contract initial.H CallerCtx) :=
  TLoop.iterN (scopedLoopBody allocationBody) (fun o => condition.evalT o.st) 2 start
@[irreducible] def allocationResult : Out contract initial.H CallerCtx :=
  match allocationHorizon with | .inl out => out | .inr _ => start

theorem allocation_admitted : Prog.withinM .nonpayable allocationBody = true := rfl

theorem allocation_prefix : allocationHorizon = .inl allocationResult := by
  have success : (match allocationHorizon with | .inl _ => true | .inr _ => false) = true := by decide +kernel
  cases h : allocationHorizon with
  | inl out => simp only [allocationResult, h]
  | inr outcome => rw [h] at success; cases success

theorem admitted_prefix_frame : TGFrameM .nonpayable initial allocationResult.st allocationResult.ext ∧
    TLocAgreeM allocationResult.ext 0 (Prog.writesAt 0 allocationBody) initial.env allocationResult.st.env :=
  scoped_loop_prefix_frame .nonpayable allocationBody allocation_admitted condition initial 2 allocationResult
    (.inl allocation_prefix)

theorem admitted_old_heap : Heap.Keeps allocationResult.ext initial.heap allocationResult.st.heap :=
  admitted_prefix_frame.1.keeps

theorem admitted_alias_transport :
    allocationResult.st.env.1 = LTy.TDenote.wk allocationResult.ext (.mem arrayType) initial.env.1 ∧
    allocationResult.st.env.2.1 = LTy.TDenote.wk allocationResult.ext (.mem arrayType) initial.env.2.1 :=
  ⟨admitted_prefix_frame.2 _ .here (by decide) (by decide +kernel),
    admitted_prefix_frame.2 _ (.there .here) (by decide) (by decide +kernel)⟩

def allocationObservation : Observation :=
  ⟨3, some 0, some 0, some [7,11], some [7,11], 11,17,7,9,2,0,[13,17],[],9,7,11⟩

theorem admitted_observations : observe allocationResult = allocationObservation := by decide +kernel

theorem wrong_order :
    ([0,1,2,3].map fun n => (TLoop.iterN (scopedLoopBody body) (fun o => condition.evalT o.st) n start).map
      observe (Except.map observe)) ≠
      [.inl zeroObservation, .inl twoObservation, .inl oneObservation, .inr (.ok twoObservation)] := by
  rw [ordered_horizons]
  intro h
  have bad : (10 : Int) = 11 := congrArg (fun xs => match xs[1]? with | some (.inl o) => o.counter | _ => 0) h
  cases bad

theorem wrong_old_content : (TRun.loop condition body.ext body.runR initial).map
    (fun out => (observe out).oldA) ≠ .ok (some [99,11]) := by
  rw [actual_loop]
  intro h
  have observed : (observe second).oldA = some [7,11] := congrArg Observation.oldA every_state_observed.2.2
  have bad : (some [7,11] : Option (List Int)) = some [99,11] := observed.symm.trans (Except.ok.inj h)
  have impossible : (7 : Int) = 99 := congrArg (fun xs => xs.head!) (Option.some.inj bad)
  cases impossible

theorem wrong_heap_identity : secondBody.st.env.1.map HRef.id ≠ some 1 := by
  have observed : secondBody.st.env.1.map HRef.id = some 2 := congrArg (fun v => v.2.1) allocations
  rw [observed]
  intro h
  have bad : (2 : Nat) = 1 := Option.some.inj h
  cases bad

theorem premature_reset : (TRun.loop condition body.ext body.runR initial).map
    (fun out => (observe out).transient) ≠ .ok 0 := by
  rw [actual_loop]
  intro h
  have observed : (observe second).transient = 13 := congrArg Observation.transient every_state_observed.2.2
  have bad : (13 : Int) = 0 := observed.symm.trans (Except.ok.inj h)
  cases bad

/-- The published compiler's no-push/no-shrink guard excludes this very loop. -/
theorem mixed_target_refused (frame : Evm.Frag CallerCtx) (ann : LoopAnn contract CallerCtx) :
    Evm.inFrag frame (.loop ann condition body) = none := by
  have pushes : (Evm.Prog.pushes body == 0) = false := rfl
  simp only [Evm.inFrag, pushes, Bool.and_false, Bool.false_and, Bool.false_eq_true, if_false]

/-- info: 'Solidity.Backend.InternalFlow.MixedLoopPrefixes.mixed_body_rejected' depends on axioms: [propext] -/
#guard_msgs in
#print axioms mixed_body_rejected
/-- info: 'Solidity.Backend.InternalFlow.MixedLoopPrefixes.first_execution' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms first_execution
/-- info: 'Solidity.Backend.InternalFlow.MixedLoopPrefixes.second_execution' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms second_execution
/-- info: 'Solidity.Backend.InternalFlow.MixedLoopPrefixes.first_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms first_step
/-- info: 'Solidity.Backend.InternalFlow.MixedLoopPrefixes.second_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms second_step
/-- info: 'Solidity.Backend.InternalFlow.MixedLoopPrefixes.initial_condition' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms initial_condition
/-- info: 'Solidity.Backend.InternalFlow.MixedLoopPrefixes.first_condition' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms first_condition
/-- info: 'Solidity.Backend.InternalFlow.MixedLoopPrefixes.second_condition' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms second_condition
/-- info: 'Solidity.Backend.InternalFlow.MixedLoopPrefixes.horizon_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms horizon_zero
/-- info: 'Solidity.Backend.InternalFlow.MixedLoopPrefixes.horizon_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms horizon_one
/-- info: 'Solidity.Backend.InternalFlow.MixedLoopPrefixes.horizon_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms horizon_two
/-- info: 'Solidity.Backend.InternalFlow.MixedLoopPrefixes.horizon_split' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms horizon_split
/-- info: 'Solidity.Backend.InternalFlow.MixedLoopPrefixes.horizon_three' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms horizon_three
/-- info: 'Solidity.Backend.InternalFlow.MixedLoopPrefixes.actual_loop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms actual_loop
/-- info: 'Solidity.Backend.InternalFlow.MixedLoopPrefixes.every_state_observed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms every_state_observed
/-- info: 'Solidity.Backend.InternalFlow.MixedLoopPrefixes.ordered_horizons' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ordered_horizons
/-- info: 'Solidity.Backend.InternalFlow.MixedLoopPrefixes.successful_observation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms successful_observation
/-- info: 'Solidity.Backend.InternalFlow.MixedLoopPrefixes.allocations' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms allocations
/-- info: 'Solidity.Backend.InternalFlow.MixedLoopPrefixes.transaction_boundary' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms transaction_boundary
/-- info: 'Solidity.Backend.InternalFlow.MixedLoopPrefixes.concrete_old_heap' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms concrete_old_heap
/-- info: 'Solidity.Backend.InternalFlow.MixedLoopPrefixes.failure_first_horizon' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms failure_first_horizon
/-- info: 'Solidity.Backend.InternalFlow.MixedLoopPrefixes.failure_second_horizon' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms failure_second_horizon
/-- info: 'Solidity.Backend.InternalFlow.MixedLoopPrefixes.second_body_failure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms second_body_failure
/-- info: 'Solidity.Backend.InternalFlow.MixedLoopPrefixes.failure_absorbs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms failure_absorbs
/-- info: 'Solidity.Backend.InternalFlow.MixedLoopPrefixes.failure_zero_horizon' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms failure_zero_horizon
/-- info: 'Solidity.Backend.InternalFlow.MixedLoopPrefixes.ordered_failure_horizons' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ordered_failure_horizons
/-- info: 'Solidity.Backend.InternalFlow.MixedLoopPrefixes.actual_failing_loop' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms actual_failing_loop
/-- info: 'Solidity.Backend.InternalFlow.MixedLoopPrefixes.failure_not_exhaustion' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms failure_not_exhaustion
/-- info: 'Solidity.Backend.InternalFlow.MixedLoopPrefixes.failure_not_divergence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms failure_not_divergence
/-- info: 'Solidity.Backend.InternalFlow.MixedLoopPrefixes.wrong_payload' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms wrong_payload
/-- info: 'Solidity.Backend.InternalFlow.MixedLoopPrefixes.mixed_alias_transport' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms mixed_alias_transport
/-- info: 'Solidity.Backend.InternalFlow.MixedLoopPrefixes.exact_second_extension_and_unwind' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms exact_second_extension_and_unwind
/-- info: 'Solidity.Backend.InternalFlow.MixedLoopPrefixes.transported_scratch_identities' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms transported_scratch_identities
/-- info: 'Solidity.Backend.InternalFlow.MixedLoopPrefixes.scratch_contents_canonical' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms scratch_contents_canonical
/-- info: 'Solidity.Backend.InternalFlow.MixedLoopPrefixes.scratch_contents_survive' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms scratch_contents_survive
/-- info: 'Solidity.Backend.InternalFlow.MixedLoopPrefixes.allocation_admitted' depends on axioms: [propext] -/
#guard_msgs in
#print axioms allocation_admitted
/-- info: 'Solidity.Backend.InternalFlow.MixedLoopPrefixes.allocation_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms allocation_prefix
/-- info: 'Solidity.Backend.InternalFlow.MixedLoopPrefixes.admitted_prefix_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms admitted_prefix_frame
/-- info: 'Solidity.Backend.InternalFlow.MixedLoopPrefixes.admitted_old_heap' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms admitted_old_heap
/-- info: 'Solidity.Backend.InternalFlow.MixedLoopPrefixes.admitted_alias_transport' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms admitted_alias_transport
/-- info: 'Solidity.Backend.InternalFlow.MixedLoopPrefixes.admitted_observations' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms admitted_observations
/-- info: 'Solidity.Backend.InternalFlow.MixedLoopPrefixes.wrong_order' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms wrong_order
/-- info: 'Solidity.Backend.InternalFlow.MixedLoopPrefixes.wrong_old_content' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms wrong_old_content
/-- info: 'Solidity.Backend.InternalFlow.MixedLoopPrefixes.wrong_heap_identity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms wrong_heap_identity
/-- info: 'Solidity.Backend.InternalFlow.MixedLoopPrefixes.premature_reset' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms premature_reset
/-- info: 'Solidity.Backend.InternalFlow.MixedLoopPrefixes.mixed_target_refused' depends on axioms: [propext] -/
#guard_msgs in
#print axioms mixed_target_refused

end Solidity.Backend.InternalFlow.MixedLoopPrefixes
