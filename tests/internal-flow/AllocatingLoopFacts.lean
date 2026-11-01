import tests.«internal-flow».CallLoopFacts
import Solidity.Evm.MemoryLoopScopeBudget

/-! A reached allocating loop turn after the unchanged ordinary call prefix.
Failure has no successful State; the separately observed allocation prefix is
an actual successful execution before the explicit revert. -/
namespace Solidity.Backend.InternalFlow.AllocatingLoopHalts
open Evm Evm.Memory PublishedLoops PublishedLoopChecks

def allocate : Stmt C Caller (.mem A :: Caller) :=
  .declMem A (.user "turn") (some (.newArr (.lit 2 rfl) rfl)) rfl rfl
def failingBody : Prog C Caller (.mem A :: Caller) := .cons allocate (.cons .revert .nil)
def condition (selected : Bool) : Val C Caller .bool := .simple (.bool selected)
def bodyCompiled : Memory.CompiledProg 1 callBefore.frag failingBody :=
  (Memory.compileProg 1 callBefore.frag failingBody).get (by decide +kernel)
def conditionCompiled (selected : Bool) :=
  (Memory.compileVal 1 callBefore.frag (condition selected)).get (by cases selected <;> decide +kernel)
theorem body_stable : bodyCompiled.frag.restrict Caller = callBefore.frag := by decide +kernel

def program (selected : Bool) : Prog C Caller Caller :=
  .cons (.loop .auto (condition selected) failingBody) .nil
def loopCert (selected : Bool) := Loops.StmtCert.loop .auto (condition selected) failingBody
  (conditionCompiled selected).code bodyCompiled.code bodyCompiled.frag
  (conditionCompiled selected).cert bodyCompiled.cert body_stable
def code (selected : Bool) : List Instr := [.loop (conditionCompiled selected).code bodyCompiled.code] ++ []
def cert (selected : Bool) : LoopScopes.ProgCert 1 callBefore.frag callBefore.frag (program selected) (code selected) :=
  .cons (.base (loopCert selected)) (.nil callBefore.frag)

theorem body_reverts (σ : State C Caller) : failingBody.run σ = .error .revert := by
  have ha : allocate.run σ = .ok ⟨σ.allocPush (defaultArray .uint (wmod 2)),List.prefix_append _ _⟩ :=
    newArray_decl σ .uint (.lit 2 rfl) (wmod 2) rfl
  change (Prog.cons allocate (.cons .revert .nil)).run σ = _
  rw [Prog.run_cons_ok ha]
  rfl

theorem body_cost (σ : State C Caller) : allocationCostProg failingBody σ = 3 := rfl

theorem prefix_zero {selected : Bool} {σ : State C Caller} {o amount}
    (hp : LoopPrefix (condition selected) failingBody σ o amount) : amount = 0 := by
  cases hp with
  | start => rfl
  | next hp hv hs => rw [body_reverts] at hs; cases hs

theorem demand_bound (selected : Bool) (amount : Nat)
    (hd : LoopScopes.Demand (cert selected) callMid.st amount) : amount ≤ 3 := by
  rcases hd.view with head | ⟨o,cost,rest,ho,hc,tail,he⟩
  · have h := head.view
    change ((∃ o, LoopPrefix (condition selected) failingBody callMid.st o amount) ∨
      (∃ o cost, LoopPrefix (condition selected) failingBody callMid.st o cost ∧
        (condition selected).evalT o.st = .ok true ∧ amount = cost + allocationCostProg failingBody o.st)) ∨ _ at h
    rcases h with (⟨o,hp⟩ | ⟨o,cost,hp,hv,he⟩) | ⟨o,cost,rest,ho,hc,tail,he⟩
    · rw [prefix_zero hp]; decide
    · rw [prefix_zero hp,body_cost,Nat.zero_add] at he; omega
    · exact tail.elim
  · exact tail.view.elim

theorem source_revert : (program true).run callMid.st = .error .revert := by
  have hf : (program true).runF 1 callMid.st = .error .revert := rfl
  exact ((Prog.runF_approx 1 (program true) callMid.st).eq (by rw [hf]; intro h; cases h)).symm.trans hf

theorem frame (selected : Bool) : 1 + (cert selected).need ≤ 64 := by cases selected <;> decide +kernel

theorem capacity : AllocationInput 1 64 (callBefore.cost (State.init C) + 3) (State.init C) bases machine := by
  rw [callPrefix_cost]
  exact .inr ⟨by decide,wmod 128,(initial_repr C).2,by decide +kernel⟩

/-- Closed actual composition, including reached caller frame and capacity. -/
theorem target_revert : ∃ m₁ base₁,
    run callBefore.code machine = .ok m₁ 0 ∧
    StateRepr 1 1 64 callBefore.frag callMid.st base₁ m₁ ∧
    m₁.stack = machine.stack ∧ BaseExtends (State.init C).H bases base₁ ∧
    GrowsAllocator 1 64 (callBefore.cost (State.init C)) (State.init C) bases machine callMid.st base₁ m₁ ∧
    run (code true) m₁ = .revert ∧ run (callBefore.code ++ code true) machine = .revert :=
  after_allocating_prefix_revert callBefore (cert true) (initial_repr C).1 callPrefix_frame (frame true)
    capacity callMid call_prefix_actual (demand_bound true) source_revert

theorem reached_demand : LoopScopes.Demand (cert true) callMid.st 3 := by
  apply LoopScopes.Demand.head
  apply LoopScopes.StmtDemand.base
  apply Loops.Demand.head
  change (∃ o, LoopPrefix (condition true) failingBody callMid.st o 3) ∨ _
  exact .inr ⟨⟨callMid.st,List.prefix_refl _⟩,0,.start,rfl,rfl⟩

theorem prefix_initial {selected : Bool} {σ : State C Caller} {o amount}
    (hp : LoopPrefix (condition selected) failingBody σ o amount) :
    o = ⟨σ,List.prefix_refl _⟩ := by
  cases hp with
  | start => rfl
  | next hp hv hs => rw [body_reverts] at hs; cases hs

theorem skipped_demand_zero (amount : Nat)
    (hd : LoopScopes.Demand (cert false) callMid.st amount) : amount = 0 := by
  rcases hd.view with head | ⟨o,cost,rest,ho,hc,tail,he⟩
  · have h := head.view
    change ((∃ o, LoopPrefix (condition false) failingBody callMid.st o amount) ∨
      (∃ o cost, LoopPrefix (condition false) failingBody callMid.st o cost ∧
        (condition false).evalT o.st = .ok true ∧ amount = cost + allocationCostProg failingBody o.st)) ∨ _ at h
    rcases h with (⟨o,hp⟩ | ⟨o,cost,hp,hv,he⟩) | ⟨o,cost,rest,ho,hc,tail,he⟩
    · exact prefix_zero hp
    · rw [prefix_initial hp] at hv; cases hv
    · exact tail.elim
  · exact tail.view.elim

def fullCursor (m : Machine) : Machine := {m with mem := upd m.mem 0 (.val wMax)}
/-- Capacity refusal is a failed Input premise, not a runtime halt. -/
theorem full_capacity_refused (m : Machine) (base : Nat → Fin W) :
    ¬ AllocationInput 1 64 3 callMid.st base (fullCursor m) := by
  intro ha
  rcases ha with hz | ⟨hb,c,hr,space⟩
  · cases hz
  · have cell : (fullCursor m).mem 0 = .val wMax := by simp only [fullCursor,upd_same]
    have he : wMax = c := Word.val.inj (cell.symm.trans hr.arrays.free.cell)
    have hc : c.val = W - 1 := (congrArg Fin.val he).symm
    have hw := W_pos
    omega

theorem reached_room_refused (m : Machine) (base : Nat → Fin W) :
    ¬ LoopScopes.Room (cert true) 64 callMid.st base (fullCursor m) :=
  fun room => full_capacity_refused m base (room 3 reached_demand)
theorem skipped_room_full (m : Machine) (base : Nat → Fin W) :
    LoopScopes.Room (cert false) 64 callMid.st base (fullCursor m) :=
  fun amount hd => .inl (skipped_demand_zero amount hd)
theorem syntax_still_allocates : (cert true).allocates = true ∧ (cert false).allocates = true := by decide +kernel

theorem wrong_failure_class :
    run (callBefore.code ++ code true) machine ≠ .fault := by
  obtain ⟨m,base,hp,hr,hk,he,hg,ht,whole⟩ := target_revert
  rw [whole]; intro h; cases h

def allocated : Solidity.Out C callMid.st.H (.mem A :: Caller) :=
  ⟨callMid.st.allocPush (defaultArray .uint (wmod 2)),List.prefix_append _ _⟩
theorem source_allocation : allocate.run callMid.st = .ok allocated :=
  newArray_decl callMid.st .uint (.lit 2 rfl) (wmod 2) rfl

def allocationCompiled : Memory.CompiledStmt 1 callBefore.frag allocate :=
  (Memory.compileStmt 1 callBefore.frag allocate).get (by decide +kernel)
theorem allocation_cost : (Calls.plainStmt allocationCompiled).cost callMid.st = 3 := rfl
theorem allocation_frame : 1 + (Calls.plainStmt allocationCompiled).need ≤ 64 := by decide +kernel

attribute [irreducible] allocationCompiled

theorem allocation_only {m : Machine} {base : Nat → Fin W}
    (repr : StateRepr 1 1 64 callBefore.frag callMid.st base m)
    (input : AllocationInput 1 64 ((Calls.plainStmt allocationCompiled).cost callMid.st) callMid.st base m) :
    ∃ m' base', run allocationCompiled.code m = .ok m' 0 ∧
      StateRepr 1 1 64 allocationCompiled.frag allocated.st base' m' ∧
      m'.stack = m.stack ∧ BaseExtends callMid.st.H base base' ∧
      GrowsAllocator 1 64 ((Calls.plainStmt allocationCompiled).cost callMid.st) callMid.st base m allocated.st base' m' :=
  PublishedDirectCalls.statement_endpoint (σ := callMid.st) (Calls.plainStmt allocationCompiled)
    repr allocation_frame input allocated source_allocation

theorem body_code : bodyCompiled.code = allocationCompiled.code ++ [.revert] := by
  have ha : Memory.compileStmt 1 callBefore.frag allocate = some allocationCompiled := by
    unfold allocationCompiled
    exact (Option.some_get _).symm
  have hb : Memory.compileProg 1 callBefore.frag failingBody = some bodyCompiled :=
    (Option.some_get _).symm
  have codes := congrArg (Option.map (fun p : Memory.CompiledProg 1 callBefore.frag failingBody => p.code)) hb
  change ((Memory.compileStmt 1 callBefore.frag allocate).bind (fun head =>
    some (head.code ++ [.revert]))) = some bodyCompiled.code at codes
  rw [ha] at codes
  exact (Option.some.inj codes).symm

def fresh : HRef allocated.st.H A := ⟨2,by decide +kernel⟩
theorem source_observations :
    (allocated.st.H.length,
      [callArray allocated.st 0,callArray allocated.st 1,callArray allocated.st 2],
      caller (allocated.st.drop (Ext.append Caller [.mem A])),count allocated.st) =
    (3,[some [0],some [2,7,11],some [2,0,0]],[some 1,some 1,some 42],some 9) := by decide +kernel

private theorem some_ref_of_id {H : HTy} (v : Option (HRef H A)) (r : HRef H A)
    (h : v.map (fun t => t.id) = some r.id) : v = some r := by
  cases v with
  | none => cases h
  | some t =>
    have same : t.id = r.id := Option.some.inj h
    have eq : t = r := by cases t; cases r; cases same; rfl
    exact congrArg some eq

theorem old_alias_first : TEnv.get (.there .here : Idx (.mem A :: Caller) (.mem A)) allocated.st.env =
    some (returned.wk allocated.ext) := some_ref_of_id _ _ (by decide +kernel)
theorem old_alias_second : TEnv.get (.there (.there .here) : Idx (.mem A :: Caller) (.mem A)) allocated.st.env =
    some (returned.wk allocated.ext) := some_ref_of_id _ _ (by decide +kernel)
theorem fresh_alias : TEnv.get (.here : Idx (.mem A :: Caller) (.mem A)) allocated.st.env = some fresh := some_ref_of_id _ _ (by decide +kernel)

def spin : Prog C (.mem A :: Caller) (.mem A :: Caller) :=
  .cons (.loop .auto (.simple (.bool true)) .nil) .nil
def spinCompiled := (LoopScopes.compileProg 1 spin allocationCompiled.frag).get (by decide +kernel)
attribute [irreducible] spinCompiled
def diverging : Prog C Caller (.mem A :: Caller) := .cons allocate spin
def divergingCode : List Instr := allocationCompiled.code ++ spinCompiled.code
def divergingCert : LoopScopes.ProgCert 1 callBefore.frag spinCompiled.frag diverging divergingCode :=
  .cons (.base (.finite allocationCompiled.cert)) spinCompiled.cert

theorem spin_nonalloc : spinCompiled.cert.allocates = false := by decide +kernel
theorem divergence_frame : 1 + divergingCert.need ≤ 64 := by decide +kernel

theorem spin_diverges (σ : State C (.mem A :: Caller)) : spin.run σ = .error .diverge := by
  let go : Solidity.Out C σ.H (.mem A :: Caller) → TRes (Solidity.Out C σ.H (.mem A :: Caller)) :=
    InternalFlow.scopedLoopBody (Prog.nil : Prog C (.mem A :: Caller) (.mem A :: Caller))
  let cond := fun _ : Solidity.Out C σ.H (.mem A :: Caller) => (.ok true : TRes Bool)
  let entry : Solidity.Out C σ.H (.mem A :: Caller) := ⟨σ,List.prefix_refl _⟩
  have step : TLoop.step go cond entry = .inl entry := rfl
  have iter : ∀ n, TLoop.iterN go cond n entry = .inl entry := by
    intro n; induction n with
    | zero => rfl
    | succ n ih => rw [TLoop.iterN,step]; exact ih
  have hl : (Stmt.loop .auto (.simple (.bool true)) (Prog.nil : Prog C (.mem A :: Caller) (.mem A :: Caller))).run σ = .error .diverge := by
    rw [Stmt.run_loop]
    exact InternalFlow.loop_all_prefixes_running go cond entry (fun n => ⟨entry,iter n⟩)
  show TRun.seq (Stmt.loop .auto (.simple (.bool true)) (Prog.nil : Prog C (.mem A :: Caller) (.mem A :: Caller))).runR Prog.nil.runR σ = _
  simp only [TRun.seq,Stmt.run] at hl ⊢
  rw [hl]

theorem source_diverges : diverging.run callMid.st = .error .diverge := by
  unfold diverging
  rw [Prog.run_cons_ok source_allocation,spin_diverges]
  rfl

theorem finite_demand_exact {amount : Nat}
    (hd : LoopScopes.StmtDemand (.base (.finite allocationCompiled.cert)) callMid.st amount) : amount = 3 := by
  have h := hd.view
  change (amount = allocationCostStmt allocate callMid.st) ∨ _ at h
  rcases h with h | ⟨o,cost,rest,ho,hc,ht,he⟩
  · exact h
  · exact ht.elim

theorem divergence_demand (amount : Nat)
    (hd : LoopScopes.Demand divergingCert callMid.st amount) : amount ≤ 3 := by
  rcases hd.view with head | ⟨o,cost,rest,ho,hc,tail,he⟩
  · exact Nat.le_of_eq (finite_demand_exact head)
  · have hc' : cost = 3 := finite_demand_exact (.base (LoopScopes.base_success_demand (.finite allocationCompiled.cert) hc))
    have hz : rest = 0 := LoopScopes.demand_nonallocating spinCompiled.cert spin_nonalloc tail
    omega

theorem allocated_values :
    allocated.st.heap.len (callPrivate.wk allocated.ext) .dyn = 0 ∧
    allocated.st.heap.len (returned.wk allocated.ext) .dyn = 2 ∧
    allocated.st.heap.len fresh .dyn = 2 ∧
    (MObj.elems .dyn (allocated.st.heap.get (returned.wk allocated.ext)))[0]? = some (indexValue (wmod 7)) ∧
    (MObj.elems .dyn (allocated.st.heap.get (returned.wk allocated.ext)))[1]? = some (indexValue (wmod 11)) ∧
    (MObj.elems .dyn (allocated.st.heap.get fresh))[0]? = some (indexValue (wmod 0)) ∧
    (MObj.elems .dyn (allocated.st.heap.get fresh))[1]? = some (indexValue (wmod 0)) ∧
    allocated.st.storage.get (rfl : C.rootType "count" = some (.prim .uint)) = .prim (indexValue (wmod 9)) ∧
    Look.ofTEnv allocated.st.env (.there (.there (.there .here)) : Idx (.mem A :: Caller) (.val .uint)) = indexValue (wmod 42) := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> decide +kernel

/-- runF uses a divergence MARKER at its horizon, not THalt.exhausted.
The same marker occurs for a skipped, actually terminating loop. -/
theorem bounded_run_marker : diverging.runF 0 callMid.st = .error .diverge := rfl
theorem skipped_run_marker : (program false).runF 0 callMid.st = .error .diverge := rfl
def skippedOut : Solidity.Out C callMid.st.H Caller := ⟨callMid.st,List.prefix_refl _⟩
theorem skipped_source : (program false).run callMid.st = .ok skippedOut := by
  have hf : (program false).runF 1 callMid.st = .ok skippedOut := rfl
  exact ((Prog.runF_approx 1 (program false) callMid.st).eq (by rw [hf]; intro h; cases h)).symm.trans hf
theorem exhaustion_source : (Stmt.assumeFalse : Stmt C Caller Caller).run callMid.st = .error .exhausted := rfl

theorem zero_budget_refused : ¬ (∀ amount, LoopScopes.Demand (cert true) callMid.st amount → amount ≤ 0) := by
  intro bound
  have h := bound 3 reached_demand
  omega

#print axioms zero_budget_refused
#print axioms allocated_values
#print axioms bounded_run_marker
#print axioms skipped_run_marker
#print axioms skipped_source
#print axioms exhaustion_source
#print axioms body_code
#print axioms source_observations
#print axioms old_alias_first
#print axioms old_alias_second
#print axioms fresh_alias
#print axioms spin_nonalloc
#print axioms divergence_frame
#print axioms spin_diverges
#print axioms source_diverges
#print axioms finite_demand_exact
#print axioms divergence_demand
#print axioms allocation_only
#print axioms reached_demand
#print axioms prefix_initial
#print axioms skipped_demand_zero
#print axioms full_capacity_refused
#print axioms reached_room_refused
#print axioms skipped_room_full
#print axioms syntax_still_allocates
#print axioms wrong_failure_class
#print axioms source_allocation
#print axioms allocation_cost
#print axioms allocation_frame
#print axioms body_reverts
#print axioms body_cost
#print axioms prefix_zero
#print axioms demand_bound
#print axioms source_revert
#print axioms frame
#print axioms capacity
#print axioms target_revert
#print axioms PublishedLoops.allocating_prefix_room
#print axioms PublishedLoops.after_allocating_prefix_revert
#print axioms PublishedLoops.after_allocating_prefix_diverge
end Solidity.Backend.InternalFlow.AllocatingLoopHalts
