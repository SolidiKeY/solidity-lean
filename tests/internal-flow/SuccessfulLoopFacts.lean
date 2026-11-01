import tests.«internal-flow».AllocatingLoopFacts

/-! An actual successful allocating loop after the unchanged callBefore.
The loop allocates once and resets its own primitive condition local. -/
namespace Solidity.Backend.InternalFlow.SuccessfulLoop
open Evm Evm.Memory PublishedLoops PublishedLoopChecks
open AllocatingLoopHalts (allocate allocated source_allocation)

abbrev Turn : Ctx := .mem A :: Caller
def reset : Stmt C Turn Turn :=
  .assignLocal (.there (.there (.there .here))) (.simple (.lit 0 rfl))
def body : Prog C Caller Turn := .cons allocate (.cons reset .nil)
def guard : Val C Caller .bool := .binop .gt rfl rfl
  (.simple (.local (.there (.there .here)))) (.simple (.lit 0 rfl))
def condition (selected : Bool) : Val C Caller .bool := if selected then guard else .simple (.bool false)
def checkedBody : Memory.CompiledProg 1 callBefore.frag body :=
  (Memory.compileProg 1 callBefore.frag body).get (by decide +kernel)
def checkedCondition (selected : Bool) :=
  (Memory.compileVal 1 callBefore.frag (condition selected)).get (by cases selected <;> decide +kernel)
theorem stable : checkedBody.frag.restrict Caller = callBefore.frag := by decide +kernel

def program (selected : Bool) : Prog C Caller Caller := .cons (.loop .auto (condition selected) body) .nil
def loopCert (selected : Bool) := Loops.StmtCert.loop .auto (condition selected) body
  (checkedCondition selected).code checkedBody.code checkedBody.frag
  (checkedCondition selected).cert checkedBody.cert stable
def code (selected : Bool) : List Instr := [.loop (checkedCondition selected).code checkedBody.code] ++ []
def cert (selected : Bool) : LoopScopes.ProgCert 1 callBefore.frag callBefore.frag (program selected) (code selected) :=
  .cons (.base (loopCert selected)) (.nil callBefore.frag)

def turn (σ : State C Caller) : Solidity.Out C σ.H Turn :=
  ⟨(σ.allocPush (defaultArray .uint (wmod 2))).setLocal
    (.there (.there (.there .here))) (indexValue (wmod 0)),List.prefix_append _ _⟩
theorem body_run (σ : State C Caller) : body.run σ = .ok (turn σ) := by
  have ha : allocate.run σ = .ok ⟨σ.allocPush (defaultArray .uint (wmod 2)),List.prefix_append _ _⟩ :=
    newArray_decl σ .uint (.lit 2 rfl) (wmod 2) rfl
  change (Prog.cons allocate (.cons reset .nil)).run σ = _
  rw [Prog.run_cons_ok ha]
  rfl

theorem stops (selected : Bool) (σ : State C Caller) (o : Solidity.Out C σ.H Turn)
    (ran : body.run σ = .ok o) : (condition selected).evalT (o.st.drop body.ext) = .ok false := by
  rw [body_run] at ran
  cases ran
  cases selected <;> rfl

theorem body_cost (σ : State C Caller) : allocationCostProg body σ = 3 := rfl

theorem enabled_cost_zero {selected : Bool} {σ : State C Caller} {o amount}
    (hp : LoopPrefix (condition selected) body σ o amount)
    (enabled : (condition selected).evalT o.st = .ok true) : amount = 0 := by
  cases hp with
  | start => rfl
  | next hp hc hs => rw [stops selected _ _ hs] at enabled; cases enabled

theorem prefix_cost_bound {selected : Bool} {σ : State C Caller} {o amount}
    (hp : LoopPrefix (condition selected) body σ o amount) : amount ≤ 3 := by
  cases hp with
  | start => decide
  | next hp hc hs => rw [enabled_cost_zero hp hc,body_cost,Nat.zero_add]; exact Nat.le_refl _

theorem demand_bound (selected : Bool) (amount : Nat)
    (hd : LoopScopes.Demand (cert selected) callMid.st amount) : amount ≤ 3 := by
  rcases hd.view with head | ⟨o,cost,rest,ho,hc,tail,he⟩
  · have h := head.view
    change ((∃ o, LoopPrefix (condition selected) body callMid.st o amount) ∨
      (∃ o cost, LoopPrefix (condition selected) body callMid.st o cost ∧
        (condition selected).evalT o.st = .ok true ∧ amount = cost + allocationCostProg body o.st)) ∨ _ at h
    rcases h with (⟨o,hp⟩ | ⟨o,cost,hp,hv,he⟩) | ⟨o,cost,rest,ho,hc,tail,he⟩
    · exact prefix_cost_bound hp
    · rw [enabled_cost_zero hp hv,body_cost,Nat.zero_add] at he; omega
    · exact tail.elim
  · exact tail.view.elim

def finalOut : Solidity.Out C callMid.st.H Caller :=
  ((program true).runF 2 callMid.st).toOption.get (by decide +kernel)
private theorem actual_get {α : Type} (r : TRes α) (h : r.toOption.isSome = true) :
    r = .ok (r.toOption.get h) := by cases r <;> cases h <;> rfl

theorem source_run : (program true).run callMid.st = .ok finalOut := by
  have hf : (program true).runF 2 callMid.st = .ok finalOut := actual_get _ (by decide +kernel)
  exact ((Prog.runF_approx 2 (program true) callMid.st).eq (by rw [hf]; intro h; cases h)).symm.trans hf

theorem frame (selected : Bool) : 1 + (cert selected).need ≤ 64 := by cases selected <;> decide +kernel
theorem total_capacity : AllocationInput 1 64 (callBefore.cost (State.init C) + 3)
    (State.init C) bases machine := AllocatingLoopHalts.capacity

theorem source_values :
    (finalOut.st.H.length,[callArray finalOut.st 0,callArray finalOut.st 1,callArray finalOut.st 2],
      caller finalOut.st,count finalOut.st) =
    (3,[some [0],some [2,7,11],some [2,0,0]],[some 1,some 1,some 0],some 9) := by decide +kernel

/-- Logical one-layer views of the EXISTING cost evidence. No alternative
cost/evaluator is introduced; these avoid non-injective code-list inversion. -/
private def scopedCostView {K : Contract} {b Γ Δ F G P code}
    (hp : LoopScopes.ProgCert (C := K) b (Γ := Γ) (Δ := Δ) F G P code)
    (σ : State K Γ) (out : Solidity.Out K σ.H Δ) (amount : Nat) : Prop :=
  LoopScopes.ProgCert.casesOn
    (motive_2 := fun {Γ Δ} _ _ _ _ _ => (σ : State K Γ) → Solidity.Out K σ.H Δ → Nat → Prop) hp
    (fun _ σ out amount => out.st = σ ∧ amount = 0)
    (fun {_ _ _ _ _ _ st _ _ _} hs ht σ out amount =>
      ∃ o cost rest last, st.run σ = .ok o ∧ LoopScopes.StmtCost hs σ o cost ∧
        LoopScopes.Cost ht o.st last rest ∧ amount = cost + rest ∧ out.st = last.st) σ out amount

private theorem scoped_cost_view {K : Contract} {b Γ Δ F G P code}
    {hp : LoopScopes.ProgCert (C := K) b (Γ := Γ) (Δ := Δ) F G P code}
    {σ : State K Γ} {out amount} (hc : LoopScopes.Cost hp σ out amount) : scopedCostView hp σ out amount := by
  cases hc with
  | nil => exact ⟨rfl,rfl⟩
  | cons ho head tail => exact ⟨_,_,_,_,ho,head,tail,rfl,rfl⟩

private def oldCostView {K : Contract} {b Γ Δ F G P code}
    (hp : Loops.ProgCert (C := K) b (Γ := Γ) (Δ := Δ) F G P code)
    (σ : State K Γ) (out : Solidity.Out K σ.H Δ) (amount : Nat) : Prop :=
  Loops.ProgCert.casesOn
    (motive := fun {Γ Δ} _ _ _ _ _ => (σ : State K Γ) → Solidity.Out K σ.H Δ → Nat → Prop) hp
    (fun _ σ out amount => out.st = σ ∧ amount = 0)
    (fun {_ _ _ _ _ _ st _ _ _} hs ht σ out amount =>
      ∃ o cost rest last, st.run σ = .ok o ∧ hs.Cost σ o cost ∧
        Loops.Cost ht o.st last rest ∧ amount = cost + rest ∧ out.st = last.st) σ out amount

private theorem old_cost_view {K : Contract} {b Γ Δ F G P code}
    {hp : Loops.ProgCert (C := K) b (Γ := Γ) (Δ := Δ) F G P code}
    {σ : State K Γ} {out amount} (hc : Loops.Cost hp σ out amount) : oldCostView hp σ out amount := by
  cases hc with
  | nil => exact ⟨rfl,rfl⟩
  | cons ho head tail => exact ⟨_,_,_,_,ho,head,tail,rfl,rfl⟩

private theorem scoped_singleton_cost {K : Contract} {b : Nat} {Γ Δ : Ctx} {F : Frag Γ} {G : Frag Δ}
    {st : Stmt K Γ Δ} {code : List Instr} {hs : LoopScopes.StmtCert b F G st code}
    {σ : State K Γ} {out : Solidity.Out K σ.H Δ} {amount : Nat}
    (hc : LoopScopes.Cost (.cons hs (.nil G)) σ out amount) :
    ∃ o, st.run σ = .ok o ∧ LoopScopes.StmtCost hs σ o amount ∧ out.st = o.st := by
  obtain ⟨o,cost,rest,last,ho,head,tail,he,hout⟩ := scoped_cost_view hc
  have hz : last.st = o.st ∧ rest = 0 := scoped_cost_view tail
  have same : amount = cost := by omega
  rw [same]
  exact ⟨o,ho,head,hout.trans hz.1⟩

private theorem old_singleton_cost {K : Contract} {b : Nat} {Γ Δ : Ctx} {F : Frag Γ} {G : Frag Δ}
    {st : Stmt K Γ Δ} {code : List Instr} {hs : Loops.StmtCert b F G st code}
    {σ : State K Γ} {out : Solidity.Out K σ.H Δ} {amount : Nat}
    (hc : Loops.Cost (.cons hs (.nil G)) σ out amount) :
    ∃ o, st.run σ = .ok o ∧ hs.Cost σ o amount ∧ out.st = o.st := by
  obtain ⟨o,cost,rest,last,ho,head,tail,he,hout⟩ := old_cost_view hc
  have hz : last.st = o.st ∧ rest = 0 := old_cost_view tail
  have same : amount = cost := by omega
  rw [same]
  exact ⟨o,ho,head,hout.trans hz.1⟩

theorem final_heap_length : finalOut.st.H.length = 3 := by decide +kernel
theorem initial_heap_length : callMid.st.H.length = 2 := by decide +kernel

theorem prefix_grown_cost {selected : Bool} {σ : State C Caller} {o amount}
    (hp : LoopPrefix (condition selected) body σ o amount)
    (changed : o.st.H.length ≠ σ.H.length) : amount = 3 := by
  cases hp with
  | start => exact (changed rfl).elim
  | next hp hv hs => rw [enabled_cost_zero hp hv,body_cost,Nat.zero_add]

theorem exact_cost {amount : Nat} (hc : LoopScopes.Cost (cert true) callMid.st finalOut amount) : amount = 3 := by
  obtain ⟨o,ho,head,he⟩ := scoped_singleton_cost hc
  obtain ⟨o',ho',hprefix,he'⟩ := old_singleton_cost head.view
  change LoopPrefix (condition true) body callMid.st o' amount at hprefix
  apply prefix_grown_cost hprefix
  have hlength : o'.st.H.length = 3 := by rw [←he',←he]; exact final_heap_length
  rw [hlength,initial_heap_length]
  decide

theorem condition_true : (condition true).evalT callMid.st = .ok true := by
  have ht : ((condition true).evalT callMid.st).toOption = some true := by decide +kernel
  cases he : (condition true).evalT callMid.st with
  | error e => rw [he] at ht; cases ht
  | ok b =>
    rw [he] at ht
    cases Option.some.inj ht
    rfl

theorem reached_demand : LoopScopes.Demand (cert true) callMid.st 3 := by
  apply LoopScopes.Demand.head
  apply LoopScopes.StmtDemand.base
  apply Loops.Demand.head
  change (∃ o, LoopPrefix (condition true) body callMid.st o 3) ∨ _
  exact .inr ⟨⟨callMid.st,List.prefix_refl _⟩,0,.start,condition_true,rfl⟩

def fresh : HRef finalOut.st.H A := ⟨2,by decide +kernel⟩
private theorem some_ref_of_id {H : HTy} (v : Option (HRef H A)) (r : HRef H A)
    (h : v.map (fun t => t.id) = some r.id) : v = some r := by
  cases v with
  | none => cases h
  | some t =>
    have same : t.id = r.id := Option.some.inj h
    have eq : t = r := by cases t; cases r; cases same; rfl
    exact congrArg some eq

theorem alias_first : TEnv.get (.here : Idx Caller (.mem A)) finalOut.st.env =
    some (returned.wk finalOut.ext) := some_ref_of_id _ _ (by decide +kernel)
theorem alias_second : TEnv.get (.there .here : Idx Caller (.mem A)) finalOut.st.env =
    some (returned.wk finalOut.ext) := some_ref_of_id _ _ (by decide +kernel)

theorem final_values :
    finalOut.st.heap.len (callPrivate.wk finalOut.ext) .dyn = 0 ∧
    finalOut.st.heap.len (returned.wk finalOut.ext) .dyn = 2 ∧
    finalOut.st.heap.len fresh .dyn = 2 ∧
    (MObj.elems .dyn (finalOut.st.heap.get (returned.wk finalOut.ext)))[0]? = some (indexValue (wmod 7)) ∧
    (MObj.elems .dyn (finalOut.st.heap.get (returned.wk finalOut.ext)))[1]? = some (indexValue (wmod 11)) ∧
    (MObj.elems .dyn (finalOut.st.heap.get fresh))[0]? = some (indexValue (wmod 0)) ∧
    (MObj.elems .dyn (finalOut.st.heap.get fresh))[1]? = some (indexValue (wmod 0)) ∧
    finalOut.st.storage.get (rfl : C.rootType "count" = some (.prim .uint)) = .prim (indexValue (wmod 9)) ∧
    Look.ofTEnv finalOut.st.env (.there (.there .here) : Idx Caller (.val .uint)) = indexValue (wmod 0) := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> decide +kernel

theorem zero_budget_refused : ¬ (∀ amount, LoopScopes.Demand (cert true) callMid.st amount → amount ≤ 0) := by
  intro bound
  have h := bound 3 reached_demand
  omega

theorem skipped_prefix_zero {σ : State C Caller} {o amount}
    (hp : LoopPrefix (condition false) body σ o amount) : amount = 0 := by
  cases hp with
  | start => rfl
  | next hp hc hs => cases hc

theorem skipped_demand_zero (amount : Nat)
    (hd : LoopScopes.Demand (cert false) callMid.st amount) : amount = 0 := by
  rcases hd.view with head | ⟨o,cost,rest,ho,hc,tail,he⟩
  · have h := head.view
    change ((∃ o, LoopPrefix (condition false) body callMid.st o amount) ∨
      (∃ o cost, LoopPrefix (condition false) body callMid.st o cost ∧
        (condition false).evalT o.st = .ok true ∧ amount = cost + allocationCostProg body o.st)) ∨ _ at h
    rcases h with (⟨o,hp⟩ | ⟨o,cost,hp,hv,he⟩) | ⟨o,cost,rest,ho,hc,tail,he⟩
    · exact skipped_prefix_zero hp
    · cases hv
    · exact tail.elim
  · exact tail.view.elim

theorem reached_room_refused (m : Machine) (base : Nat → Fin W) :
    ¬ LoopScopes.Room (cert true) 64 callMid.st base (AllocatingLoopHalts.fullCursor m) :=
  fun room => AllocatingLoopHalts.full_capacity_refused m base (room 3 reached_demand)
theorem skipped_room_full (m : Machine) (base : Nat → Fin W) :
    LoopScopes.Room (cert false) 64 callMid.st base (AllocatingLoopHalts.fullCursor m) :=
  fun amount hd => .inl (skipped_demand_zero amount hd)
theorem syntax_allocates : (cert true).allocates = true ∧ (cert false).allocates = true := by decide +kernel

def skippedOut : Solidity.Out C callMid.st.H Caller := ⟨callMid.st,List.prefix_refl _⟩
theorem skipped_source : (program false).run callMid.st = .ok skippedOut := by
  have hf : (program false).runF 1 callMid.st = .ok skippedOut := rfl
  exact ((Prog.runF_approx 1 (program false) callMid.st).eq (by rw [hf]; intro h; cases h)).symm.trans hf

theorem need_exact : (cert true).need = 4 := by decide +kernel
theorem final_context_only_frame_refused : ¬ 1 + (cert true).need ≤ 1 + Caller.length := by decide +kernel

/-- A separate ready caller-use regression: after loop-local drop, write
through one retained alias and read through the other into a new scalar. -/
abbrev After : Ctx := .val .uint :: Caller
def followup : Prog C Caller After :=
  .cons (.assignMem (.index .dyn (.var .here rfl) (.simple (.lit 1 rfl))) (.val (.simple (.lit 99 rfl))))
  (.cons (.declLocal .uint (.user "answer")
    (some (.readMem (.index .dyn (.var (.there .here) rfl) (.simple (.lit 1 rfl)))))) .nil)
def checkedUse := (Calls.compile 1 callBefore.frag followup).get (by decide +kernel)
theorem use_frame : 1 + checkedUse.need ≤ 64 := by decide +kernel
theorem use_cost : checkedUse.cost finalOut.st = 0 := by decide +kernel
attribute [irreducible] checkedUse

def usedOut : Solidity.Out C finalOut.st.H After :=
  (followup.run finalOut.st).toOption.get (by decide +kernel)
theorem use_source : followup.run finalOut.st = .ok usedOut := actual_get _ (by decide +kernel)
theorem use_values :
    (usedOut.st.H.length,[callArray usedOut.st 0,callArray usedOut.st 1,callArray usedOut.st 2],
      (TEnv.get (.here : Idx After (.val .uint)) usedOut.st.env).1,
      caller (usedOut.st.drop (Ext.append Caller [.val .uint])),count usedOut.st) =
    (3,[some [0],some [2,7,99],some [2,0,0]],99,[some 1,some 1,some 0],some 9) := by decide +kernel

theorem use_result : Look.ofTEnv usedOut.st.env (.here : Idx After (.val .uint)) = indexValue (wmod 99) := by decide +kernel

theorem omitted_loop_cost_refused : ¬ LoopScopes.Cost (cert true) callMid.st finalOut 0 := by
  intro h
  have impossible := exact_cost h
  cases impossible

theorem use_elements :
    (MObj.elems .dyn (usedOut.st.heap.get ((returned.wk finalOut.ext).wk usedOut.ext)))[1]? = some (indexValue (wmod 99)) ∧
    (MObj.elems .dyn (usedOut.st.heap.get (fresh.wk usedOut.ext)))[0]? = some (indexValue (wmod 0)) := by
  constructor <;> decide +kernel

/-- Preserve the published loop-syntax refusal, while checking the actual body. -/
theorem loop_guard_refused : Prog.withinM .view (program true) = false := by decide +kernel
theorem allocation_body_within : Prog.withinM .view body = true := by decide +kernel

/-- The actual body result retains its frame through local unwind.
No syntactic loop guard is weakened, and no claim covers the later alias writer. -/
theorem scoped_body_frame : TGFrameM .view callMid.st
    ((turn callMid.st).st.drop body.ext) (turn callMid.st).ext :=
  ((Prog.run_frameM body allocation_body_within 0 (body_run callMid.st)).1).withEnv _

theorem old_heap_contents_kept : Heap.Keeps (turn callMid.st).ext callMid.st.heap
    ((turn callMid.st).st.drop body.ext).heap := scoped_body_frame.keeps

#print axioms loop_guard_refused
#print axioms allocation_body_within
#print axioms scoped_body_frame
#print axioms old_heap_contents_kept
#print axioms omitted_loop_cost_refused
#print axioms use_elements
#print axioms need_exact
#print axioms final_context_only_frame_refused
#print axioms use_frame
#print axioms use_cost
#print axioms use_source
#print axioms use_values
#print axioms use_result
#print axioms zero_budget_refused
#print axioms skipped_prefix_zero
#print axioms skipped_demand_zero
#print axioms reached_room_refused
#print axioms skipped_room_full
#print axioms syntax_allocates
#print axioms skipped_source
#print axioms alias_first
#print axioms alias_second
#print axioms final_values
#print axioms final_heap_length
#print axioms initial_heap_length
#print axioms prefix_grown_cost
#print axioms exact_cost
#print axioms condition_true
#print axioms reached_demand
#print axioms stable
#print axioms body_run
#print axioms stops
#print axioms body_cost
#print axioms enabled_cost_zero
#print axioms prefix_cost_bound
#print axioms demand_bound
#print axioms source_run
#print axioms frame
#print axioms total_capacity
#print axioms source_values
end Solidity.Backend.InternalFlow.SuccessfulLoop
