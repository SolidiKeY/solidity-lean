import Solidity.Backend.InternalFlow.AllocationFrameChecks

/-! Consumers of the published finite recursive unrolling, including its
exhausted bottom. No unbounded source/target recursive simulation is asserted. -/
namespace Solidity.Backend.InternalFlow

/-- Uniform finite-unrolling return/frame consumer. The induction obligation
is syntactic withinM admission, not a desired execution preservation equation.
Argument/body successes remain explicit genuine execution premises. -/
theorem finite_recursive_return {C : Contract} {Γ Δ ps rs : Ctx}
    (μ : Mutability) (f : Name) (ret : CallRet Γ rs Δ) (args : Args C Γ ps)
    (step : Nat → (Unit → Prog C (rs ++ ps) (rs ++ ps)) → Prog C (rs ++ ps) (rs ++ ps))
    (hs : ∀ n t, Prog.withinM μ (t ()) = true → Prog.withinM μ (step n t) = true)
    (d : Nat) (caller : State C Γ) (arguments : TEnv C caller.H ps)
    (ha : args.evalT caller = .ok arguments)
    (out : Out C (ret.enterT (caller.withEnv arguments)).st.H (rs ++ ps))
    (hb : (recUnroll Prog.recBase step d).runR (ret.enterT (caller.withEnv arguments)).st = .ok out) :
    let body := recUnroll Prog.recBase step d
    let entry := ret.enterT (caller.withEnv arguments)
    let extension := entry.ext.trans out.ext
    let final : Out C caller.H Δ :=
      ⟨out.st.withEnv (ret.leaveT (TEnv.wk extension Γ caller.env)
        (TEnv.take rs (TEnv.drop body.ext out.st.env))), extension⟩
    (Stmt.callRec f d args ret (fun _ => body)).runR caller = .ok final ∧
      TGFrameM μ caller final.st final.ext ∧ Heap.Keeps final.ext caller.heap final.st.heap := by
  have hw : Prog.withinM μ (recUnroll Prog.recBase step d) = true := Prog.withinM_recUnroll hs d
  have entered : TGFrameM μ caller (ret.enterT (caller.withEnv arguments)).st
      (ret.enterT (caller.withEnv arguments)).ext := (TGFrameM.env (μ := μ) caller arguments (List.prefix_refl _)).trans
    (CallRet.enterT_frameM (μ := μ) ret (caller.withEnv arguments))
      (ret.enterT (caller.withEnv arguments)).ext
  have framed : TGFrameM μ (ret.enterT (caller.withEnv arguments)).st out.st out.ext := (Prog.run_frameM (recUnroll Prog.recBase step d) hw 0 hb).1
  have composed : TGFrameM μ caller out.st
      ((ret.enterT (caller.withEnv arguments)).ext.trans out.ext) := entered.trans framed
    ((ret.enterT (caller.withEnv arguments)).ext.trans out.ext)
  refine ⟨?_, composed.withEnv _, composed.keeps⟩
  change Stmt.run caller (.callRec f d args ret (fun _ => recUnroll Prog.recBase step d)) = _
  rw [Stmt.run_callRec]
  exact call_return args ret (recUnroll Prog.recBase step d).ext
    (recUnroll Prog.recBase step d).runR caller arguments ha out hb

/-- info: 'Solidity.Backend.InternalFlow.finite_recursive_return' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms finite_recursive_return

namespace RecursiveUnroll
open Controls (contract arrayType seven nine eleven persistent transient)
open AllocationFrameChecks (CallerCtx caller contents)

abbrev Params : Ctx := [.val .uint, .mem arrayType]
abbrev Frame : Ctx := [.val .uint, .val .uint, .mem arrayType]
abbrev Local : Ctx := .mem arrayType :: Frame

def nextArgs : Args contract Local Params :=
  .snoc (.snocMemory .nil arrayType (.user "alias")
    (.var (.there (.there (.there .here))) rfl)) .uint (.user "n")
    (.binop .sub rfl rfl (.simple (.local (.there (.there .here)))) (.simple (.lit 1 rfl)))
def recurseRet : CallRet Local [.val .uint] Local :=
  .val .uint (.user "result") (some (.there .here))
def zeroTest : Val contract Local .bool :=
  .binop .eqB rfl rfl (.simple (.local (.there (.there .here)))) (.simple (.lit 0 rfl))
def baseAssign : Stmt contract Local Local := .assignLocal (.there .here) (.simple (.lit 13 rfl))
def increment : Stmt contract Local Local := .assignLocal (.there .here)
  (.binop .add rfl rfl (.simple (.local (.there .here))) (.simple (.lit 1 rfl)))

def step (d : Nat) (below : Unit → Prog contract Frame Frame) : Prog contract Frame Frame :=
  .cons (.block (.cons (.declMem arrayType (.user "scratch") (some (.newArr (.lit 1 rfl) rfl)) rfl rfl)
    (.cons (.ite zeroTest
      (.cons baseAssign .nil)
      (.cons (.callRec "count" d nextArgs recurseRet below)
        (.cons increment .nil))) .nil))) .nil

theorem step_within (d : Nat) (below : Unit → Prog contract Frame Frame)
    (h : Prog.withinM .view (below ()) = true) : Prog.withinM .view (step d below) = true := by
  have hr : nextArgs.readsIn .view = true := rfl
  have hc : zeroTest.readsIn .view = true := rfl
  have hb : Stmt.within .view baseAssign = true := rfl
  have hi : Stmt.within .view increment = true := rfl
  simp only [step, Prog.withinM_cons, Prog.withinM_nil, Stmt.withinM,
    MRhs.allocIn, hr, hc, h, hb, hi, Bool.and_true, Bool.or_true, Bool.true_or]

def args : Args contract CallerCtx Params :=
  .snoc (.snocMemory .nil arrayType (.user "alias") (.var .here rfl))
    .uint (.user "n") (.simple (.lit 2 rfl))
def ret : CallRet CallerCtx [.val .uint] CallerCtx :=
  .val .uint (.user "result") (some (.there (.there .here)))
def call (depth : Nat) : Stmt contract CallerCtx CallerCtx :=
  .callRec "count" depth args ret (fun _ => recUnroll Prog.recBase step depth)

/-- Extract a witness only after independently proving actual success below.
The fallback has no execution claim; nested_execution rules it out. -/
@[irreducible] def result : Out contract caller.H CallerCtx :=
  match (call 3).runR caller with
  | .ok out => out
  | .error _ => ⟨caller, List.prefix_refl _⟩

theorem nested_execution : (call 3).runR caller = .ok result := by
  have success : (match (call 3).runR caller with | .ok _ => true | .error _ => false) = true := by
    decide +kernel
  cases h : (call 3).runR caller with
  | ok out => simp only [result, h]
  | error e => rw [h] at success; cases success

def arguments : TEnv contract caller.H Params := (⟨2, rfl⟩, caller.env.1, ())
def entry : Out contract caller.H Frame := ret.enterT (caller.withEnv arguments)
@[irreducible] def bodyResult : Out contract entry.st.H Frame :=
  match (recUnroll Prog.recBase step 3).runR entry.st with
  | .ok out => out
  | .error _ => ⟨entry.st, List.prefix_refl _⟩

theorem arguments_evaluate : args.evalT caller = .ok arguments := rfl

theorem body_execution : (recUnroll Prog.recBase step 3).runR entry.st = .ok bodyResult := by
  have success : (match (recUnroll Prog.recBase step 3).runR entry.st with
      | .ok _ => true | .error _ => false) = true := by decide +kernel
  cases h : (recUnroll Prog.recBase step 3).runR entry.st with
  | ok out => simp only [bodyResult, h]
  | error e => rw [h] at success; cases success

/-- Exact call-return instantiation, including the entry/body heap extension
and typed caller export. Success was discharged above on the actual run. -/
theorem exact_recursive_export : result =
    (⟨bodyResult.st.withEnv (ret.leaveT
      (TEnv.wk (entry.ext.trans bodyResult.ext) CallerCtx caller.env)
      (TEnv.take [.val .uint] (TEnv.drop (recUnroll Prog.recBase step 3).ext bodyResult.st.env))),
      entry.ext.trans bodyResult.ext⟩ : Out contract caller.H CallerCtx) :=
  Except.ok.inj (nested_execution.symm.trans
    (finite_recursive_return .view "count" ret args step step_within 3 caller arguments
      arguments_evaluate bodyResult body_execution).1)


theorem body_within (d : Nat) : Prog.withinM .view (recUnroll Prog.recBase step d) = true :=
  Prog.withinM_recUnroll step_within d

theorem call_within (d : Nat) : (call d).withinM .view = true := by
  have h : Prog.withinM .view (recUnroll Prog.recBase step d) = true := body_within d
  have hr : args.readsIn .view = true := rfl
  simp only [call, Stmt.withinM, hr, h, Bool.true_and, Bool.or_true]

theorem recursive_frame : TGFrameM .view caller result.st result.ext :=
  (Stmt.run_frameM (call 3) (call_within 3) 0 nested_execution).1

theorem recursive_heap_contents : Heap.Keeps result.ext caller.heap result.st.heap := recursive_frame.keeps

theorem caller_aliases_transport :
    result.st.env.1 = LTy.TDenote.wk result.ext (.mem arrayType) caller.env.1 ∧
    result.st.env.2.1 = LTy.TDenote.wk result.ext (.mem arrayType) caller.env.2.1 := by
  have h : TLocAgreeM result.ext 0 ((call 3).writesAt 0) caller.env
      (TEnv.drop (call 3).ext result.st.env) := (Stmt.run_frameM (call 3) (call_within 3) 0 nested_execution).2
  exact ⟨h _ .here (by decide) (by decide +kernel),
    h _ (.there .here) (by decide) (by decide +kernel)⟩


theorem recursive_globals : result.st.storage = caller.storage ∧ result.st.tx = caller.tx ∧
    result.st.net = caller.net ∧ result.st.selfBalance = caller.selfBalance :=
  ⟨(recursive_frame.keepsSt (by decide)).1, recursive_frame.tx,
    (recursive_frame.keepsSt (by decide)).2, recursive_frame.selfBalance (by decide)⟩

theorem nested_observations : ((call 3).runR caller).map (fun out =>
    (contents out.st .here, contents out.st (.there .here),
      (out.st.env.2.2.1).1, (out.st.env.2.2.2.1).1, out.st.H.length)) =
      .ok (some [7,11], some [7,11], 15, 11, 4) := by
  rw [nested_execution]
  apply congrArg Except.ok
  decide +kernel

theorem exhausted_zero : (call 0).runR caller = .error .exhausted := rfl

theorem exhausted_two : (call 2).runR caller = .error .exhausted := by
  have certificate : (match (call 2).runR caller with
      | .error e => decide (e = .exhausted) | .ok _ => false) = true := by decide +kernel
  cases h : (call 2).runR caller with
  | ok out => rw [h] at certificate; cases certificate
  | error e =>
    rw [h] at certificate
    have he : e = .exhausted := of_decide_eq_true certificate
    rw [he]

theorem wrong_result : ((call 3).runR caller).map (fun out => (out.st.env.2.2.1).1) ≠ .ok 14 := by
  rw [nested_execution]
  intro h
  have observed : (result.st.env.2.2.1).1 = (15 : Int) := by decide +kernel
  have bad : (15 : Int) = 14 := observed.symm.trans (Except.ok.inj h)
  cases bad

theorem wrong_destination : ((call 3).runR caller).map (fun out => (out.st.env.2.2.2.1).1) ≠ .ok 15 := by
  rw [nested_execution]
  intro h
  have observed : (result.st.env.2.2.2.1).1 = (11 : Int) := by decide +kernel
  have bad : (11 : Int) = 15 := observed.symm.trans (Except.ok.inj h)
  cases bad

theorem wrong_reference : ((call 3).runR caller).map (fun out => out.st.env.1.map HRef.id) ≠ .ok (some 3) := by
  rw [nested_execution]
  intro h
  have observed : result.st.env.1.map HRef.id = some 0 := by decide +kernel
  have bad : (0 : Nat) = 3 := Option.some.inj (observed.symm.trans (Except.ok.inj h))
  cases bad

theorem lost_caller_prefix : ((call 3).runR caller).map (fun out => contents out.st .here) ≠ .ok none := by
  rw [nested_execution]
  intro h
  have observed : contents result.st .here = some [7, 11] := by decide +kernel
  have bad : (some [7,11] : Option (List Int)) = none := observed.symm.trans (Except.ok.inj h)
  cases bad

theorem exhaustion_is_not_return (out : Out contract caller.H CallerCtx) :
    (call 2).runR caller ≠ .ok out := by
  rw [exhausted_two]
  intro h
  cases h

theorem exhaustion_is_not_revert : (call 2).runR caller ≠ .error .revert := by
  rw [exhausted_two]
  intro h
  cases h


/-- The actual first scratch allocation and next recursive call boundary. -/
def firstScratch : Grew contract Frame entry.st.H (MVal · (.ref arrayType)) := entry.st.copyStToMG (newArrT arrayType ⟨1, rfl⟩ rfl) rfl
def middleCaller : State contract Local := firstScratch.st.push (t := .mem arrayType) (some firstScratch.val)
def middleArguments : TEnv contract middleCaller.H Params :=
  (⟨1, rfl⟩, middleCaller.env.2.2.2.1, ())
def middleCall : Stmt contract Local Local :=
  .callRec "count" 2 nextArgs recurseRet (fun _ => recUnroll Prog.recBase step 2)

theorem nested_argument_boundary : nextArgs.evalT middleCaller = .ok middleArguments := rfl

private def observationEq {α : Type} [DecidableEq α] : DecidableEq (TRes α)
  | .ok a, .ok b => if h : a = b then isTrue (h ▸ rfl) else isFalse (fun e => h (Except.ok.inj e))
  | .error a, .error b => if h : a = b then isTrue (h ▸ rfl) else isFalse (fun e => h (Except.error.inj e))
  | .ok _, .error _ => isFalse (by intro h; cases h)
  | .error _, .ok _ => isFalse (by intro h; cases h)

theorem nested_boundary_observations : (middleCall.runR middleCaller).map (fun out =>
    ((out.st.env.2.1).1, (out.st.env.2.2.1).1,
      contents out.st (.there (.there (.there .here))), out.st.H.length)) =
      .ok (14, 2, some [7, 11], 4) := by
  apply @of_decide_eq_true _ (observationEq _ _)
  decide +kernel

/-- info: 'Solidity.Backend.InternalFlow.RecursiveUnroll.nested_argument_boundary' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms nested_argument_boundary
/-- info: 'Solidity.Backend.InternalFlow.RecursiveUnroll.nested_boundary_observations' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms nested_boundary_observations
/-- info: 'Solidity.Backend.InternalFlow.RecursiveUnroll.step_within' depends on axioms: [propext] -/
#guard_msgs in
#print axioms step_within
/-- info: 'Solidity.Backend.InternalFlow.RecursiveUnroll.nested_execution' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms nested_execution
/-- info: 'Solidity.Backend.InternalFlow.RecursiveUnroll.arguments_evaluate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms arguments_evaluate
/-- info: 'Solidity.Backend.InternalFlow.RecursiveUnroll.body_execution' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms body_execution
/-- info: 'Solidity.Backend.InternalFlow.RecursiveUnroll.exact_recursive_export' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms exact_recursive_export
/-- info: 'Solidity.Backend.InternalFlow.RecursiveUnroll.body_within' depends on axioms: [propext] -/
#guard_msgs in
#print axioms body_within
/-- info: 'Solidity.Backend.InternalFlow.RecursiveUnroll.call_within' depends on axioms: [propext] -/
#guard_msgs in
#print axioms call_within
/-- info: 'Solidity.Backend.InternalFlow.RecursiveUnroll.recursive_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms recursive_frame
/-- info: 'Solidity.Backend.InternalFlow.RecursiveUnroll.recursive_heap_contents' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms recursive_heap_contents
/-- info: 'Solidity.Backend.InternalFlow.RecursiveUnroll.caller_aliases_transport' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms caller_aliases_transport
/-- info: 'Solidity.Backend.InternalFlow.RecursiveUnroll.recursive_globals' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms recursive_globals
/-- info: 'Solidity.Backend.InternalFlow.RecursiveUnroll.nested_observations' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms nested_observations
/-- info: 'Solidity.Backend.InternalFlow.RecursiveUnroll.exhausted_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms exhausted_zero
/-- info: 'Solidity.Backend.InternalFlow.RecursiveUnroll.exhausted_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exhausted_two
/-- info: 'Solidity.Backend.InternalFlow.RecursiveUnroll.wrong_result' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms wrong_result
/-- info: 'Solidity.Backend.InternalFlow.RecursiveUnroll.wrong_destination' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms wrong_destination
/-- info: 'Solidity.Backend.InternalFlow.RecursiveUnroll.wrong_reference' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms wrong_reference
/-- info: 'Solidity.Backend.InternalFlow.RecursiveUnroll.lost_caller_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms lost_caller_prefix
/-- info: 'Solidity.Backend.InternalFlow.RecursiveUnroll.exhaustion_is_not_return' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms exhaustion_is_not_return
/-- info: 'Solidity.Backend.InternalFlow.RecursiveUnroll.exhaustion_is_not_revert' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms exhaustion_is_not_revert

end RecursiveUnroll
end Solidity.Backend.InternalFlow
