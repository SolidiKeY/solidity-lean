import Solidity.Semantics.Properties

/-!
# States that agree off a few scratch names

`EnvAgreeExcept ns s₁ s₂`: two states that agree everywhere but on the
environment entries of `ns`, the scratch names a rule declares.  The kit
below shows every state operation of the interpreter respects it, which is
what an unfolding rule's soundness proof composes.
-/

namespace Solidity
namespace Semantics

open SemanticsProperties

/-! ## State agreement off a set of scratch names -/

/-- `s₁` and `s₂` agree everywhere except possibly on the environment
entries for the names in `ns`. -/
structure EnvAgreeExcept (ns : List Var) (s₁ s₂ : State) : Prop where
  storage : s₁.storage = s₂.storage
  heap : s₁.heap = s₂.heap
  nextId : s₁.nextId = s₂.nextId
  net : s₁.net = s₂.net
  env : ∀ n, n ∉ ns -> lookupBy n s₁.env = lookupBy n s₂.env
  selfBalance : s₁.selfBalance = s₂.selfBalance

/-- Agreement of two executions: identical aborts, or final states that
agree off `ns`. -/
def ResultsAgree (ns : List Var) : Res State -> Res State -> Prop
  | .error e₁, .error e₂ => e₁ = e₂
  | .ok s₁, .ok s₂ => EnvAgreeExcept ns s₁ s₂
  | _, _ => False

/-- Agreement of two stateful computations returning a payload:
identical aborts, or equal payloads in states that agree off `ns`. -/
def ResAgree (ns : List Var) :
    Res (State × α) -> Res (State × α) -> Prop
  | .error e₁, .error e₂ => e₁ = e₂
  | .ok (s₁, a₁), .ok (s₂, a₂) => a₁ = a₂ ∧ EnvAgreeExcept ns s₁ s₂
  | _, _ => False

/-- Agreement of two evaluations: identical aborts, or equal values in
states that agree off `ns`. -/
abbrev ValuesAgree (ns : List Var) :
    Res (State × Value) -> Res (State × Value) -> Prop :=
  ResAgree ns

namespace EnvAgreeExcept

theorem refl (ns : List Var) (s : State) : EnvAgreeExcept ns s s :=
  ⟨rfl, rfl, rfl, rfl, fun _ _ => rfl, rfl⟩

end EnvAgreeExcept

/-! ## Monadic combinators for the agreement relations

The interpreter is written in the `Res` monad; these combinators let the
congruence proofs follow its `do`-structure instead of re-doing the case
analysis on aborts at every step. -/

theorem ResultsAgree.refl (ns : List Var) (x : Res State) :
    ResultsAgree ns x x := by
  cases x with
  | error e => exact rfl
  | ok s => exact EnvAgreeExcept.refl ns s

theorem ResAgree.refl (ns : List Var) (x : Res (State × α)) :
    ResAgree ns x x := by
  match x with
  | .error e => exact rfl
  | .ok (s, a) => exact ⟨rfl, EnvAgreeExcept.refl ns s⟩

theorem ResAgree.ok {ns : List Var} {s₁ s₂ : State} {a : α}
    (h : EnvAgreeExcept ns s₁ s₂) :
    ResAgree ns (.ok (s₁, a)) (.ok (s₂, a)) :=
  ⟨rfl, h⟩

theorem ResAgree.bind {ns : List Var} {x₁ x₂ : Res (State × α)}
    (hx : ResAgree ns x₁ x₂)
    {f₁ f₂ : State × α -> Res (State × β)}
    (hf : ∀ s₁ s₂ a, EnvAgreeExcept ns s₁ s₂ ->
      ResAgree ns (f₁ (s₁, a)) (f₂ (s₂, a))) :
    ResAgree ns (x₁ >>= f₁) (x₂ >>= f₂) := by
  match x₁, x₂, hx with
  | .error e₁, .error e₂, hx =>
      subst hx
      exact rfl
  | .ok (s₁, a₁), .ok (s₂, a₂), ⟨heq, hs⟩ =>
      subst heq
      exact hf s₁ s₂ a₁ hs

/-- `ResAgree.bind`, additionally handing the continuation the two
`ok`-equations — for continuations whose proof needs to *invert* the
prefix (e.g. to extract the freshness of a resolved `Loc`). -/
theorem ResAgree.bindWith {ns : List Var} {x₁ x₂ : Res (State × α)}
    (hx : ResAgree ns x₁ x₂)
    {f₁ f₂ : State × α -> Res (State × β)}
    (hf : ∀ s₁ s₂ a, x₁ = .ok (s₁, a) -> x₂ = .ok (s₂, a) ->
      EnvAgreeExcept ns s₁ s₂ ->
      ResAgree ns (f₁ (s₁, a)) (f₂ (s₂, a))) :
    ResAgree ns (x₁ >>= f₁) (x₂ >>= f₂) := by
  match x₁, x₂, hx with
  | .error e₁, .error e₂, hx =>
      subst hx
      exact rfl
  | .ok (s₁, a₁), .ok (s₂, a₂), ⟨heq, hs⟩ =>
      subst heq
      exact hf s₁ s₂ a₁ rfl rfl hs

theorem ResAgree.bindState {ns : List Var} {x₁ x₂ : Res (State × α)}
    (hx : ResAgree ns x₁ x₂)
    {f₁ f₂ : State × α -> Res State}
    (hf : ∀ s₁ s₂ a, EnvAgreeExcept ns s₁ s₂ ->
      ResultsAgree ns (f₁ (s₁, a)) (f₂ (s₂, a))) :
    ResultsAgree ns (x₁ >>= f₁) (x₂ >>= f₂) := by
  match x₁, x₂, hx with
  | .error e₁, .error e₂, hx =>
      subst hx
      exact rfl
  | .ok (s₁, a₁), .ok (s₂, a₂), ⟨heq, hs⟩ =>
      subst heq
      exact hf s₁ s₂ a₁ hs

/-- `ResAgree.bindState`, additionally handing the continuation the two
`ok`-equations (see `ResAgree.bindWith`). -/
theorem ResAgree.bindStateWith {ns : List Var} {x₁ x₂ : Res (State × α)}
    (hx : ResAgree ns x₁ x₂)
    {f₁ f₂ : State × α -> Res State}
    (hf : ∀ s₁ s₂ a, x₁ = .ok (s₁, a) -> x₂ = .ok (s₂, a) ->
      EnvAgreeExcept ns s₁ s₂ ->
      ResultsAgree ns (f₁ (s₁, a)) (f₂ (s₂, a))) :
    ResultsAgree ns (x₁ >>= f₁) (x₂ >>= f₂) := by
  match x₁, x₂, hx with
  | .error e₁, .error e₂, hx =>
      subst hx
      exact rfl
  | .ok (s₁, a₁), .ok (s₂, a₂), ⟨heq, hs⟩ =>
      subst heq
      exact hf s₁ s₂ a₁ rfl rfl hs

/-- A shared effect-free prefix (`v.asValue`, `applyBinOp`, a storage
lookup evaluated at already-agreeing states) binds into agreeing
continuations. -/
theorem bindPureRes_agree {ns : List Var} (r : Res α)
    {f₁ f₂ : α -> Res (State × β)}
    (hf : ∀ a, ResAgree ns (f₁ a) (f₂ a)) :
    ResAgree ns (r >>= f₁) (r >>= f₂) := by
  cases r with
  | error e => exact rfl
  | ok a => exact hf a

theorem bindPureResults_agree {ns : List Var} (r : Res α)
    {f₁ f₂ : α -> Res State}
    (hf : ∀ a, ResultsAgree ns (f₁ a) (f₂ a)) :
    ResultsAgree ns (r >>= f₁) (r >>= f₂) := by
  cases r with
  | error e => exact rfl
  | ok a => exact hf a

theorem ResultsAgree.bindRes {ns : List Var} {x₁ x₂ : Res State}
    (hx : ResultsAgree ns x₁ x₂)
    {f₁ f₂ : State -> Res (State × α)}
    (hf : ∀ s₁ s₂, EnvAgreeExcept ns s₁ s₂ ->
      ResAgree ns (f₁ s₁) (f₂ s₂)) :
    ResAgree ns (x₁ >>= f₁) (x₂ >>= f₂) := by
  match x₁, x₂, hx with
  | .error e₁, .error e₂, hx =>
      subst hx
      exact rfl
  | .ok s₁, .ok s₂, hs =>
      exact hf s₁ s₂ hs

theorem ResultsAgree.bind {ns : List Var} {x₁ x₂ : Res State}
    (hx : ResultsAgree ns x₁ x₂)
    {f₁ f₂ : State -> Res State}
    (hf : ∀ s₁ s₂, EnvAgreeExcept ns s₁ s₂ ->
      ResultsAgree ns (f₁ s₁) (f₂ s₂)) :
    ResultsAgree ns (x₁ >>= f₁) (x₂ >>= f₂) := by
  match x₁, x₂, hx with
  | .error e₁, .error e₂, hx =>
      subst hx
      exact rfl
  | .ok s₁, .ok s₂, hs =>
      exact hf s₁ s₂ hs

/-- Destructor: an agreeing pair is either the same abort or two `ok`s
with equal payloads. -/
theorem ResAgree.cases {ns : List Var} {x₁ x₂ : Res (State × α)}
    (h : ResAgree ns x₁ x₂) :
    (∃ e, x₁ = .error e ∧ x₂ = .error e) ∨
      (∃ s₁ s₂ a, x₁ = .ok (s₁, a) ∧ x₂ = .ok (s₂, a) ∧
        EnvAgreeExcept ns s₁ s₂) := by
  match x₁, x₂, h with
  | .error e₁, .error e₂, h =>
      subst h
      exact Or.inl ⟨e₁, rfl, rfl⟩
  | .ok (s₁, a₁), .ok (s₂, a₂), ⟨heq, hs⟩ =>
      subst heq
      exact Or.inr ⟨s₁, s₂, a₁, rfl, rfl, hs⟩

theorem ResultsAgree.cases {ns : List Var} {x₁ x₂ : Res State}
    (h : ResultsAgree ns x₁ x₂) :
    (∃ e, x₁ = .error e ∧ x₂ = .error e) ∨
      (∃ s₁ s₂, x₁ = .ok s₁ ∧ x₂ = .ok s₂ ∧ EnvAgreeExcept ns s₁ s₂) := by
  match x₁, x₂, h with
  | .error e₁, .error e₂, h =>
      subst h
      exact Or.inl ⟨e₁, rfl, rfl⟩
  | .ok s₁, .ok s₂, hs =>
      exact Or.inr ⟨s₁, s₂, rfl, rfl, hs⟩

/-- Lift a state-agreeing pair of `Res (State × α)` computations whose
payload feeds a pure continuation into `Res State`. -/
theorem ResAgree.toResults {ns : List Var} {x₁ x₂ : Res (State × α)}
    (hx : ResAgree ns x₁ x₂)
    {f₁ f₂ : State × α -> State}
    (hf : ∀ s₁ s₂ a, EnvAgreeExcept ns s₁ s₂ ->
      EnvAgreeExcept ns (f₁ (s₁, a)) (f₂ (s₂, a))) :
    ResultsAgree ns (x₁.map f₁) (x₂.map f₂) := by
  match x₁, x₂, hx with
  | .error e₁, .error e₂, hx =>
      subst hx
      exact rfl
  | .ok (s₁, a₁), .ok (s₂, a₂), ⟨heq, hs⟩ =>
      subst heq
      exact hf s₁ s₂ a₁ hs

/-- Inserting a scratch binding moves a state within its
`EnvAgreeExcept` class. -/
theorem EnvAgreeExcept.setEnv_right {ns : List Var} {s₁ s₂ : State}
    (h : EnvAgreeExcept ns s₁ s₂) {n : Var} (hn : n ∈ ns) (b : Binding) :
    EnvAgreeExcept ns s₁ (s₂.setEnv n b) :=
  ⟨h.storage, h.heap, h.nextId, h.net, fun m hm => by
    have hne : m ≠ n := fun heq => hm (heq ▸ hn)
    simpa [State.setEnv, lookupBy_setBy_ne hne] using h.env m hm,
    h.selfBalance⟩

/-- Setting the same (non-scratch or scratch) binding on both sides
preserves agreement. -/
theorem EnvAgreeExcept.setEnv_both {ns : List Var} {s₁ s₂ : State}
    (h : EnvAgreeExcept ns s₁ s₂) (n : Var) (b : Binding) :
    EnvAgreeExcept ns (s₁.setEnv n b) (s₂.setEnv n b) :=
  ⟨h.storage, h.heap, h.nextId, h.net, fun m hm => by
    by_cases he : m = n
    · subst he
      simp [State.setEnv, lookupBy_setBy_self]
    · simp [State.setEnv, lookupBy_setBy_ne he, h.env m hm],
    h.selfBalance⟩

/-! ## Relational lemmas for the storage primitives -/

theorem findStorage_congr {ns : List Var} {s₁ s₂ : State}
    (h : EnvAgreeExcept ns s₁ s₂) (root : Name) (segs : List Seg) :
    s₁.findStorage root segs = s₂.findStorage root segs := by
  unfold State.findStorage
  rw [h.storage]

theorem saveStorage_agree {ns : List Var} {s₁ s₂ : State}
    (h : EnvAgreeExcept ns s₁ s₂) (root : Name) (segs : List Seg)
    (new : SVal) :
    ResultsAgree ns (s₁.saveStorage root segs new)
      (s₂.saveStorage root segs new) := by
  have hsave : ∀ (r : Res SVal),
      ResultsAgree ns
        (r.bind fun updated =>
          .ok { s₁ with storage := setBy root updated s₂.storage })
        (r.bind fun updated =>
          .ok { s₂ with storage := setBy root updated s₂.storage }) := by
    intro r
    cases r with
    | error e => exact rfl
    | ok updated => exact ⟨rfl, h.heap, h.nextId, h.net, h.env,
        h.selfBalance⟩
  unfold State.saveStorage
  rw [h.storage]
  cases lookupBy root s₂.storage with
  | none => exact rfl
  | some v => exact hsave (v.save segs new)

theorem getEnv_congr {ns : List Var} {s₁ s₂ : State}
    (h : EnvAgreeExcept ns s₁ s₂) {n : Var} (hn : n ∉ ns) :
    s₁.getEnv n = s₂.getEnv n := by
  unfold State.getEnv
  rw [h.env n hn]

/-! ## Further state-primitive congruences -/

theorem getObj_congr {ns : List Var} {s₁ s₂ : State}
    (h : EnvAgreeExcept ns s₁ s₂) (id : Nat) :
    s₁.getObj id = s₂.getObj id := by
  unfold State.getObj
  rw [h.heap]

theorem setObj_agree {ns : List Var} {s₁ s₂ : State}
    (h : EnvAgreeExcept ns s₁ s₂) (id : Nat) (obj : MObj) :
    EnvAgreeExcept ns (s₁.setObj id obj) (s₂.setObj id obj) :=
  ⟨h.storage, by simp [State.setObj, h.heap], h.nextId, h.net, h.env,
    h.selfBalance⟩

theorem setNet_agree {ns : List Var} {s₁ s₂ : State}
    (h : EnvAgreeExcept ns s₁ s₂) (addr amount : Int) :
    EnvAgreeExcept ns (s₁.setNet addr amount) (s₂.setNet addr amount) :=
  ⟨h.storage, h.heap, h.nextId, by simp [State.setNet, h.net], h.env,
    h.selfBalance⟩

theorem getNet_congr {ns : List Var} {s₁ s₂ : State}
    (h : EnvAgreeExcept ns s₁ s₂) (addr : Int) :
    s₁.getNet addr = s₂.getNet addr := by
  unfold State.getNet
  rw [h.net]

theorem alloc_agree {ns : List Var} {s₁ s₂ : State}
    (h : EnvAgreeExcept ns s₁ s₂) (obj : MObj) :
    (s₁.alloc obj).2 = (s₂.alloc obj).2 ∧
      EnvAgreeExcept ns (s₁.alloc obj).1 (s₂.alloc obj).1 :=
  ⟨by simp [State.alloc, h.nextId],
    ⟨h.storage, by simp [State.alloc, h.heap, h.nextId],
      by simp [State.alloc, h.nextId], h.net, h.env, h.selfBalance⟩⟩

/-! ## Congruence for the cross-domain copies -/

mutual
theorem copyStToM_agree {ns : List Var} {s₁ s₂ : State}
    (h : EnvAgreeExcept ns s₁ s₂) (v : SVal) :
    ResAgree ns (copyStToM s₁ v) (copyStToM s₂ v) := by
  match v with
  | .int v => rw [copyStToM, copyStToM]; exact ⟨rfl, h⟩
  | .bool b => rw [copyStToM, copyStToM]; exact ⟨rfl, h⟩
  | .struct fields =>
      rw [copyStToM, copyStToM]
      refine ResAgree.bind (copyStFields_agree h fields) ?_
      intro t₁ t₂ mfields ht
      exact ⟨by simp [ht.nextId],
        ht.storage, by simp [ht.heap, ht.nextId],
        by simp [ht.nextId], ht.net, ht.env, ht.selfBalance⟩
  | .array elems _ =>
      rw [copyStToM, copyStToM]
      refine ResAgree.bind (copyStElems_agree h elems) ?_
      intro t₁ t₂ melems ht
      exact ⟨by simp [ht.nextId],
        ht.storage, by simp [ht.heap, ht.nextId],
        by simp [ht.nextId], ht.net, ht.env, ht.selfBalance⟩
  | .map entries dflt => rw [copyStToM, copyStToM]; exact rfl

theorem copyStFields_agree {ns : List Var} {s₁ s₂ : State}
    (h : EnvAgreeExcept ns s₁ s₂) (fields : List (Name × SVal)) :
    ResAgree ns (copyStFields s₁ fields) (copyStFields s₂ fields) := by
  match fields with
  | [] => rw [copyStFields, copyStFields]; exact ⟨rfl, h⟩
  | (name, v) :: rest =>
      rw [copyStFields, copyStFields]
      refine ResAgree.bind (copyStToM_agree h v) ?_
      intro t₁ t₂ mv ht
      refine ResAgree.bind (copyStFields_agree ht rest) ?_
      intro u₁ u₂ mrest hu
      exact ⟨rfl, hu⟩

theorem copyStElems_agree {ns : List Var} {s₁ s₂ : State}
    (h : EnvAgreeExcept ns s₁ s₂) (elems : List SVal) :
    ResAgree ns (copyStElems s₁ elems) (copyStElems s₂ elems) := by
  match elems with
  | [] => rw [copyStElems, copyStElems]; exact ⟨rfl, h⟩
  | v :: rest =>
      rw [copyStElems, copyStElems]
      refine ResAgree.bind (copyStToM_agree h v) ?_
      intro t₁ t₂ mv ht
      refine ResAgree.bind (copyStElems_agree ht rest) ?_
      intro u₁ u₂ mrest hu
      exact ⟨rfl, hu⟩
end

theorem allocDefault_agree {ns : List Var} {s₁ s₂ : State}
    (h : EnvAgreeExcept ns s₁ s₂) (ref : RefTy) :
    ResAgree ns (allocDefault s₁ ref) (allocDefault s₂ ref) := by
  unfold allocDefault
  rcases (copyStToM_agree h (defaultForRef ref)).cases with
    ⟨e, h₁, h₂⟩ | ⟨t₁, t₂, mv, h₁, h₂, ht⟩
  · rw [h₁, h₂]
    exact rfl
  · rw [h₁, h₂]
    cases mv with
    | prim p => cases p <;> exact rfl
    | ref id => exact ⟨rfl, ht⟩

mutual
theorem copyMToSt_congr {ns : List Var} {s₁ s₂ : State}
    (h : EnvAgreeExcept ns s₁ s₂) (rem : List Nat) (v : MVal) :
    copyMToSt s₁ rem v = copyMToSt s₂ rem v := by
  match v with
  | .int v => rw [copyMToSt.eq_def, copyMToSt.eq_def]
  | .bool b => rw [copyMToSt.eq_def, copyMToSt.eq_def]
  | .ref id =>
      rw [copyMToSt.eq_def, copyMToSt.eq_def]
      by_cases hmem : id ∈ rem
      · simp only [hmem, dif_pos, getObj_congr h,
          copyMFields_congr h (rem.erase id),
          copyMElems_congr h (rem.erase id)]
      · simp only [hmem, dif_neg, not_false_iff]
termination_by (rem.length, 0)
decreasing_by all_goals
  (apply Prod.Lex.left
   have h1 := List.length_erase_of_mem hmem
   have h2 := List.length_pos_of_mem hmem
   omega)

theorem copyMFields_congr {ns : List Var} {s₁ s₂ : State}
    (h : EnvAgreeExcept ns s₁ s₂) (rem : List Nat)
    (fields : List (Name × MVal)) :
    copyMFields s₁ rem fields = copyMFields s₂ rem fields := by
  match fields with
  | [] => rw [copyMFields, copyMFields]
  | (name, v) :: rest =>
      rw [copyMFields, copyMFields, copyMToSt_congr h rem v,
        copyMFields_congr h rem rest]
termination_by (rem.length, fields.length + 1)

theorem copyMElems_congr {ns : List Var} {s₁ s₂ : State}
    (h : EnvAgreeExcept ns s₁ s₂) (rem : List Nat) (elems : List MVal) :
    copyMElems s₁ rem elems = copyMElems s₂ rem elems := by
  match elems with
  | [] => rw [copyMElems, copyMElems]
  | v :: rest =>
      rw [copyMElems, copyMElems, copyMToSt_congr h rem v,
        copyMElems_congr h rem rest]
termination_by (rem.length, elems.length + 1)
end

theorem copyMem_congr {ns : List Var} {s₁ s₂ : State}
    (h : EnvAgreeExcept ns s₁ s₂) (v : MVal) :
    copyMem s₁ v = copyMem s₂ v := by
  unfold copyMem
  rw [h.heap, copyMToSt_congr h]

end Semantics
end Solidity
