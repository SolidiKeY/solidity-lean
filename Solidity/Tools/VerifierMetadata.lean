import Solidity.Tools.Counterexample

/-!
# Kernel facts for failed postcondition slots

Guards the editor regression in which a reported failing index is mistaken for
an arbitrary clause. A slot is tied to the exact typed postcondition and state
used by `postFails`, with a proof that its clause does not hold. This additive
foundation neither identifies source spans nor connects a displayed candidate
to the original verification obligation; those producer obligations remain.
Canonical counting recovers the supplied clause list exactly, even when its
last clause is itself a conjunction. Connecting that list to source ensures
and their locations remains a producer obligation. It does not turn an unknown
outcome, panic, or tested candidate into a proof.
-/

namespace Solidity

variable {C : Contract} {Γ : Ctx}

/-- Counting the actual canonical list recovers precisely its clauses, including
an internally conjunctive last clause; an arbitrary count is not substituted. -/
theorem Fml.conjN_conj (clauses : List (Fml C Γ)) :
    Fml.conjN clauses.length (Fml.conj clauses) = clauses := by
  induction clauses with
  | nil => rfl
  | cons head tail ih =>
    cases tail with
    | nil => rfl
    | cons next rest =>
      simpa only [List.length_cons, Fml.conj, Fml.conjN] using congrArg (List.cons head) ih

/-- A reported index names a member of the exact typed postcondition split,
and that clause is false in the same typed state. No source location is inferred. -/
def Fml.FailedPostSlot (n : Nat) (post : Fml C Γ) (σ : State C Γ) (i : Nat) : Prop :=
  ∃ clause : Fml C Γ,
    (i, clause) ∈ (List.range n).zip (Fml.conjN n post) ∧ ¬ holds σ clause

/-- Every index selected by the existing `ff` filter has a kernel-sound clause
identity; the finite evaluator's unknown cases cannot establish this fact. -/
theorem Fml.failedPostSlot_of_mem (dom : TDom) (n : Nat)
    (post : Fml C Γ) (σ : State C Γ) (i : Nat)
    (h : i ∈ ((List.range n).zip (Fml.conjN n post)).filterMap
      (fun (j, clause) => if clause.eval3 dom σ = .ff then some j else none)) :
    Fml.FailedPostSlot n post σ i := by
  rcases List.mem_filterMap.mp h with ⟨⟨j, clause⟩, hslot, hselected⟩
  grind [Fml.FailedPostSlot, Fml.eval3_ff]

/-- A successful typed run and the exact existing `postFails` result tie every
reported index to a false clause in that run's final state. This says nothing
about source spans or entry premises of the enclosing verification obligation. -/
theorem Fml.failedPostSlot_of_modal_postFails {Γ₁ Γ₀ : Ctx}
    (dom : TDom) (n : Nat) (σ : State C Γ) (m : Modality)
    (program : Prog C Γ Γ₁) (frames : Frames C Γ₁ Γ₀)
    (post : Fml C Γ₀) (finalState : State C Γ₀) (indices : List Nat) (i : Nat)
    (hrun : Prog.runFramesF loopFuel σ program frames = .ok finalState)
    (hresult : Fml.postFails dom n σ (.modal m program frames post) = some (none, indices))
    (hindex : i ∈ indices) : Fml.FailedPostSlot n post finalState i := by
  simp only [Fml.postFails, hrun] at hresult
  cases hresult
  exact Fml.failedPostSlot_of_mem dom n post finalState i hindex

/-- With the actual canonical count, a certified split slot names one member
of that same input clause list. This does not associate the list with source spans. -/
theorem Fml.failedPostSlot_conj_iff (clauses : List (Fml C Γ))
    (σ : State C Γ) (i : Nat) :
    Fml.FailedPostSlot clauses.length (Fml.conj clauses) σ i ↔
      ∃ clause : Fml C Γ,
        (i, clause) ∈ (List.range clauses.length).zip clauses ∧ ¬ holds σ clause := by
  simp only [Fml.FailedPostSlot, Fml.conjN_conj]

/-- A successful existing update/run path reaches the exact false typed slot.
Each update and run is the one used by postFails; the terminal clause carries
¬ holds. This is a semantic witness, not another evaluator. -/
def Fml.ReachedFailedPostSlotV1 (n i : Nat) : {Γ : Ctx} → State C Γ → Fml C Γ → Prop
  | _, state, .upd _ update body =>
    ∃ values, update.applyV state = some values ∧
      ∃ next, state.lift? values = some next ∧ ReachedFailedPostSlotV1 n i next body
  | _, state, .modal _ program frames post =>
    ∃ finalState, Prog.runFramesF loopFuel state program frames = .ok finalState ∧
      FailedPostSlot n post finalState i
  | _, _, _ => False

/-- Soundness through the original old-state updates and typed call. -/
theorem Fml.reachedFailedPostSlotV1_of_postFails (domain : TDom) (n i : Nat)
    {Γ : Ctx} (formula : Fml C Γ) : ∀ (state : State C Γ) (indices : List Nat),
    Fml.postFails domain n state formula = some (none, indices) →
    i ∈ indices → Fml.ReachedFailedPostSlotV1 n i state formula := by
  induction formula with
  | upd mode update body ih =>
    intro state indices result member
    cases applied : update.applyV state with
    | none =>
      simp only [Fml.postFails, applied] at result
      exact Option.noConfusion (congrArg Prod.fst (Option.some.inj result))
    | some values =>
      cases lifted : state.lift? values with
      | none =>
        simp only [Fml.postFails, applied, lifted] at result
        exact Option.noConfusion result
      | some next =>
        exact ⟨values, applied, next, lifted,
          ih next indices (by simpa only [Fml.postFails, applied, lifted] using result) member⟩
  | modal mode program frames post _ =>
    intro state indices result member
    cases ran : Prog.runFramesF loopFuel state program frames with
    | ok finalState =>
      exact ⟨finalState, ran,
        Fml.failedPostSlot_of_modal_postFails domain n state mode program frames post
          finalState indices i ran result member⟩
    | error halt =>
      cases halt <;> simp only [Fml.postFails, ran] at result
      all_goals first
        | exact Option.noConfusion result
        | exact Option.noConfusion (congrArg Prod.fst (Option.some.inj result))
  | _ =>
    intro state indices result member
    simp only [Fml.postFails] at result
    exact Option.noConfusion result

/-- Select an existing postFails slot only after its typed entry is true. -/
def Fml.enteredPostFailsV1 (domain : TDom) (n i : Nat)
    {Γ : Ctx} (state : State C Γ) : Fml C Γ → Bool
  | .imp pre execution =>
    if pre.eval3 domain state != .tt then false else
    match Fml.postFails domain n state execution with
    | some (none, indices) => indices.contains i
    | _ => false
  | _ => false

/-- A semantic true entry and a successful typed path to a false post slot. -/
def Fml.EnteredFailedPostSlotV1 (n i : Nat) {Γ : Ctx}
    (state : State C Γ) : Fml C Γ → Prop
  | .imp pre execution => holds state pre ∧ ReachedFailedPostSlotV1 n i state execution
  | _ => False

/-- Finite checking is only ingress: the output is a semantic ¬ holds witness
for the selected slot in the same successful typed run. -/
theorem Fml.enteredFailedPostSlotV1_of_true (domain : TDom) (n i : Nat)
    {Γ : Ctx} (state : State C Γ) (formula : Fml C Γ)
    (checked : enteredPostFailsV1 domain n i state formula = true) :
    EnteredFailedPostSlotV1 n i state formula := by
  cases formula with
  | imp pre execution =>
    cases premise : pre.eval3 domain state with
    | tt =>
      refine ⟨Fml.eval3_tt premise, ?_⟩
      cases result : Fml.postFails domain n state execution with
      | none =>
        simp only [enteredPostFailsV1, premise, result] at checked
        cases checked
      | some pair =>
        rcases pair with ⟨halt, indices⟩
        cases halt with
        | some halt =>
          simp only [enteredPostFailsV1, premise, result] at checked
          cases checked
        | none =>
          have selected : indices.contains i = true := by
            simpa only [enteredPostFailsV1, premise, result] using checked
          exact reachedFailedPostSlotV1_of_postFails domain n i execution state indices result
            (List.contains_iff.mp selected)
    | ff | unknown =>
      simp only [enteredPostFailsV1, premise] at checked
      cases checked
  | _ =>
    simp only [enteredPostFailsV1] at checked
    cases checked

/-- Check the retained typed formula itself, without invoking a source compiler
or searching for a different candidate. The supplied split count and slot are
explicit; this predicate establishes no source ordinal or span correspondence. -/
def Fml.retainedPostFailsV1 (domain : TDom) (n i : Nat)
    (values : List (Var × Semantics.CallValue)) (state : State C []) (formula : Fml C []) : Bool :=
  let ⟨_, current, body⟩ := Fml.peel values state formula
  Fml.enteredPostFailsV1 domain n i current body

def Fml.RetainedFailedPostSlotV1 (n i : Nat)
    (values : List (Var × Semantics.CallValue)) (state : State C []) (formula : Fml C []) : Prop :=
  let ⟨_, current, body⟩ := Fml.peel values state formula
  Fml.EnteredFailedPostSlotV1 n i current body

/-- A checked failure in the original formula reaches a false typed slot at
those exact inputs; a full-goal refutation is not used as this witness. -/
theorem Fml.retainedFailedPostSlotV1_of_true (domain : TDom) (n i : Nat)
    (values : List (Var × Semantics.CallValue)) (state : State C []) (formula : Fml C [])
    (checked : Fml.retainedPostFailsV1 domain n i values state formula = true) :
    Fml.RetainedFailedPostSlotV1 n i values state formula :=
  Fml.enteredFailedPostSlotV1_of_true domain n i
    (Fml.peel values state formula).2.1 (Fml.peel values state formula).2.2 checked

/-- A typed clause is available only in its actual output context. -/
abbrev TypedPostFamilyV1 (C : Contract) := {context : Ctx} → Option (Fml C context)

def typedPostFamilyV1 {output : Ctx} (clause : Fml C output) : TypedPostFamilyV1 C :=
  fun {context} => if h : context = output then some (h.symm ▸ clause) else none

/-- A structural equality from the actual terminal slot to a typed named clause.
It traverses no program and interprets no source or candidate. -/
def Fml.PostSlotMatchesV1 (n i : Nat) (family : TypedPostFamilyV1 C) :
    {Γ : Ctx} → Fml C Γ → Prop
  | _, .upd _ _ body => PostSlotMatchesV1 n i family body
  | _, .modal _ _ _ post => ∃ clause,
      (Fml.conjN n post)[i]? = some clause ∧ family = some clause
  | _, _ => False

/-- The same successful typed path, ending with the particular named clause
false. Its dependent context is retained through the family lookup. -/
def Fml.ReachedNamedPostFailureV1 (family : TypedPostFamilyV1 C) :
    {Γ : Ctx} → State C Γ → Fml C Γ → Prop
  | _, state, .upd _ update body => ∃ values, update.applyV state = some values ∧
      ∃ next, state.lift? values = some next ∧ ReachedNamedPostFailureV1 family next body
  | _, state, .modal _ program frames _ => ∃ finalState,
      Prog.runFramesF loopFuel state program frames = .ok finalState ∧
      ∃ clause, family = some clause ∧ ¬ holds finalState clause
  | _, _, _ => False

theorem Fml.failedPostSlot_at_indexV1 (n i : Nat) (post clause : Fml C Γ) (state : State C Γ)
    (failed : FailedPostSlot n post state i) (selected : (Fml.conjN n post)[i]? = some clause) :
    ¬ holds state clause := by
  rcases failed with ⟨actual, member, refuted⟩
  rcases List.mem_iff_getElem?.mp member with ⟨j, found⟩
  have components := List.getElem?_zip_eq_some.mp found
  rcases List.getElem?_eq_some_iff.mp components.1 with ⟨bound, identifier⟩
  have position : j = i := (List.getElem_range bound).symm.trans identifier
  have value := components.2
  rw [position] at value
  have same : actual = clause := Option.some.inj (value.symm.trans selected)
  simpa only [same] using refuted

/-- Exact slot equality transports semantic failure to that named clause. -/
theorem Fml.reachedNamedPostFailureV1_of_slot (n i : Nat) (family : TypedPostFamilyV1 C)
    {Γ : Ctx} (formula : Fml C Γ) : ∀ (state : State C Γ),
    ReachedFailedPostSlotV1 n i state formula → PostSlotMatchesV1 n i family formula →
    ReachedNamedPostFailureV1 family state formula := by
  induction formula with
  | upd mode update body ih =>
    intro state reached matched
    rcases reached with ⟨values, applied, next, lifted, tail⟩
    exact ⟨values, applied, next, lifted, ih next tail matched⟩
  | modal mode program frames post _ =>
    intro state reached matched
    rcases reached with ⟨finalState, ran, failed⟩
    rcases matched with ⟨clause, selected, belongs⟩
    exact ⟨finalState, ran, clause, belongs, failedPostSlot_at_indexV1 n i post clause finalState failed selected⟩
  | _ => intro state reached matched; exact False.elim reached

def Fml.EnteredSlotMatchesV1 (n i : Nat) (family : TypedPostFamilyV1 C) : {Γ : Ctx} → Fml C Γ → Prop
  | _, .imp _ body => PostSlotMatchesV1 n i family body
  | _, _ => False

def Fml.EnteredNamedPostFailureV1 (family : TypedPostFamilyV1 C) : {Γ : Ctx} → State C Γ → Fml C Γ → Prop
  | _, state, .imp pre body => holds state pre ∧ ReachedNamedPostFailureV1 family state body
  | _, _, _ => False

theorem Fml.enteredNamedPostFailureV1_of_slot (n i : Nat) (family : TypedPostFamilyV1 C)
    {Γ : Ctx} (state : State C Γ) (formula : Fml C Γ)
    (failed : EnteredFailedPostSlotV1 n i state formula) (matched : EnteredSlotMatchesV1 n i family formula) :
    EnteredNamedPostFailureV1 family state formula := by
  cases formula with
  | imp pre body => exact ⟨failed.1, reachedNamedPostFailureV1_of_slot n i family body state failed.2 matched⟩
  | _ => exact False.elim failed

/-- Constructor used by the opt-in proof builder: the equality is checked
against the actual terminal typed clause, never a textual post label. -/
theorem Fml.postSlotMatchesV1_modal (n i : Nat) (family : TypedPostFamilyV1 C)
    {Γ₁ Γ₀ : Ctx} (mode : Modality) (program : Prog C Γ Γ₁) (frames : Frames C Γ₁ Γ₀)
    (post clause : Fml C Γ₀) (selected : (Fml.conjN n post)[i]? = some clause)
    (belongs : family = some clause) : PostSlotMatchesV1 n i family (.modal mode program frames post) :=
  ⟨clause, selected, belongs⟩

end Solidity
