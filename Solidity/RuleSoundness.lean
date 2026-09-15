import Solidity.Rules
import Solidity.Semantics

/-!
# Symbolic soundness of the unfold rules

The bridge between `Rules.lean` and `Semantics.lean`, quantified over
states: executing an unfold rule's residual block agrees with executing
the original statement, up to the scratch alias bindings the captures
introduce (`EnvAgreeExcept aliasNames`). This is the formal sense in
which the rewrite rules are derivable from the executable semantics.
**Every rule of `ruleNames` with a non-empty residual block has a
`<rule>_sound` theorem below** — adding an unfold rule without one
silently weakens that claim.

The file is layered: agreement relations and monadic combinators; the
interpreter congruence kit (states agreeing off a set of names evaluate
to agreeing results, provided the program does not mention them); the
purity kit; capture read-backs; workhorse lemmas; then one `<rule>_sound`
per unfold rule, stated against `(ruleEffect r).cond`/`.block`.

Hypothesis conventions. Every theorem assumes the alias names are fresh
for the statement (`stmtUsesVar … = false`; they are reserved for the
calculus, KeY's `\newTypeOf` variables).

Evaluation order.  The interpreter evaluates an assignment's right-hand
side *before* resolving its target (solc order, `execAssignNested`).
The theorems fall into four shapes:

* **Unconditional** (`ifElseTrue_sound`, the declaration splits, the
  left-operand captures, `exprStmtCapture_sound`, …): quantified over
  every state, only `hcond` and freshness.
* **Target pre-resolves** (`*ReadUnfoldRight*`, `*SndResult`, the
  `*ValueRhsCapture` trio): `hlhs : resolveLoc s lhs.expr = .ok (s, loc)`
  and `pureExpr lhs.expr`.  These residuals hoist the right-hand side,
  which the interpreter evaluates first anyway, so no order is swapped;
  the hypotheses are proof-technique residue of the congruence kit, not
  a semantic restriction, and could be weakened.
* **Value frozen ahead of the capture** (`*WriteUnfoldLeft*`,
  `*SndIndex`): only `hcond`, `hprim : rhs.ty.isPrimitive = true` and
  freshness.  `Rules.freezeRhs` binds the value into `rv` before any
  target capture, so the order matches `execAssignNested`; the templates
  are `fieldWriteResolve{Storage,Memory}_sound` and
  `indexWriteResolve{Storage,Memory}_sound`, and `people[i++].age = i`
  and `values[i++] = i` are inside them
  (`Counterexamples/EvaluationOrder.lean`).

  The freeze cannot be made conditional on the path being impure.
  *Interference* is the obvious reason.  *Error ordering* is the other,
  and it bites even on a pure path: the interpreter evaluates the value
  first, so a failing right-hand side decides the outcome, while an
  unfrozen residual resolves the path first — and a simple right-hand
  side can only get stuck whereas a pure path can revert.
  `Counterexamples/ErrorOrder.lean` refutes the unfrozen residual on
  `people[1 / 0].age = ghost`.  That is what the old `hev` hypothesis was
  hiding: assuming the right-hand side *succeeds* removes exactly those
  states.

  The reference-typed value operand keeps its side conditions, because
  `freezeRhs` only freezes primitives — binding a reference is aliasing,
  not a read (`fieldWriteResolveStorage_ref_sound`, witness
  `alice.accounts[mv.x++] = mv`).  `hprim` itself is about the
  *interpreter*, not the rule: see `Counterexamples/RefSourceOrder.lean`.
* **Operand pre-evaluates** (`binopUnfoldRight`, compound-assign
  captures, `storagePushLhsToPushValue`): `evalValue s l = .ok (s, lv)`
  and similar; a residual re-reads an operand after a capture, so the
  operand must not depend on the capture's effects.

A few theorems also carry typing-shaped side conditions that the
surface language guarantees but the untyped statement model does not:
declaration splits assume the initializer does not mention the declared
name, `storageLocalDeclInitDrop` assumes the local name does not
shadow a contract global, the value-capture rules for identity-typed
memory reads assume reads of identity-typed expressions yield
references, and rules with non-place targets assume the target's
location shape matches its kind (`loc ≠ Loc.stack _`, etc.).
-/

namespace Solidity
namespace RuleSoundness

open Rules Semantics

/-- The fresh names reserved by the rule captures. -/
def aliasNames : List Name :=
  [valueAliasName, storagePathAliasName, memoryPathAliasName,
    indexAliasName, rhsValueAliasName]

/-! ## Variable occurrence -/

mutual
/-- `usesVar e n`: the variable `n` occurs in `e`. Only variable
binding-names matter for freshness — environment lookups key on the
`var` field name; struct field selectors never reach the environment. -/
def usesVar : WrappedExpr -> Name -> Bool
  | .var _ _ fld, n => fld.name = n
  | .field _ _ base _, n => usesVar base n
  | .index _ _ base index, n => usesVar base n || usesVar index n
  | .pushPlace target, n => usesVar target n
  | .bool _, _ => false
  | .intLit _ _, _ => false
  | .mkCall _ _ _ args, n => usesVarList args n
  | .mkBinop _ l r, n => usesVar l n || usesVar r n
  | .mkUnop _ arg, n => usesVar arg n
  | .mkIncDec _ target, n => usesVar target n
  | .mkTernary c t e, n => usesVar c n || usesVar t n || usesVar e n

def usesVarList : List WrappedExpr -> Name -> Bool
  | [], _ => false
  | e :: rest, n => usesVar e n || usesVarList rest n
end

/-! ## State agreement off a set of scratch names -/

/-- `s₁` and `s₂` agree everywhere except possibly on the environment
entries for the names in `ns`. -/
structure EnvAgreeExcept (ns : List Name) (s₁ s₂ : State) : Prop where
  storage : s₁.storage = s₂.storage
  heap : s₁.heap = s₂.heap
  nextId : s₁.nextId = s₂.nextId
  net : s₁.net = s₂.net
  env : ∀ n, n ∉ ns -> lookupBy n s₁.env = lookupBy n s₂.env
  selfBalance : s₁.selfBalance = s₂.selfBalance

/-- Agreement of two executions: identical aborts, or final states that
agree off `ns`. -/
def ResultsAgree (ns : List Name) : Res State -> Res State -> Prop
  | .error e₁, .error e₂ => e₁ = e₂
  | .ok s₁, .ok s₂ => EnvAgreeExcept ns s₁ s₂
  | _, _ => False

/-- Agreement of two stateful computations returning a payload:
identical aborts, or equal payloads in states that agree off `ns`. -/
def ResAgree (ns : List Name) :
    Res (State × α) -> Res (State × α) -> Prop
  | .error e₁, .error e₂ => e₁ = e₂
  | .ok (s₁, a₁), .ok (s₂, a₂) => a₁ = a₂ ∧ EnvAgreeExcept ns s₁ s₂
  | _, _ => False

/-- Agreement of two evaluations: identical aborts, or equal values in
states that agree off `ns`. -/
abbrev ValuesAgree (ns : List Name) :
    Res (State × Value) -> Res (State × Value) -> Prop :=
  ResAgree ns

namespace EnvAgreeExcept

theorem refl (ns : List Name) (s : State) : EnvAgreeExcept ns s s :=
  ⟨rfl, rfl, rfl, rfl, fun _ _ => rfl, rfl⟩

end EnvAgreeExcept

/-! ## Monadic combinators for the agreement relations

The interpreter is written in the `Res` monad; these combinators let the
congruence proofs follow its `do`-structure instead of re-doing the case
analysis on aborts at every step. -/

theorem ResultsAgree.refl (ns : List Name) (x : Res State) :
    ResultsAgree ns x x := by
  cases x with
  | error e => exact rfl
  | ok s => exact EnvAgreeExcept.refl ns s

theorem ResAgree.refl (ns : List Name) (x : Res (State × α)) :
    ResAgree ns x x := by
  match x with
  | .error e => exact rfl
  | .ok (s, a) => exact ⟨rfl, EnvAgreeExcept.refl ns s⟩

theorem ResAgree.ok {ns : List Name} {s₁ s₂ : State} {a : α}
    (h : EnvAgreeExcept ns s₁ s₂) :
    ResAgree ns (.ok (s₁, a)) (.ok (s₂, a)) :=
  ⟨rfl, h⟩

theorem ResAgree.bind {ns : List Name} {x₁ x₂ : Res (State × α)}
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
theorem ResAgree.bindWith {ns : List Name} {x₁ x₂ : Res (State × α)}
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

theorem ResAgree.bindState {ns : List Name} {x₁ x₂ : Res (State × α)}
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
theorem ResAgree.bindStateWith {ns : List Name} {x₁ x₂ : Res (State × α)}
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
theorem bindPureRes_agree {ns : List Name} (r : Res α)
    {f₁ f₂ : α -> Res (State × β)}
    (hf : ∀ a, ResAgree ns (f₁ a) (f₂ a)) :
    ResAgree ns (r >>= f₁) (r >>= f₂) := by
  cases r with
  | error e => exact rfl
  | ok a => exact hf a

theorem bindPureResults_agree {ns : List Name} (r : Res α)
    {f₁ f₂ : α -> Res State}
    (hf : ∀ a, ResultsAgree ns (f₁ a) (f₂ a)) :
    ResultsAgree ns (r >>= f₁) (r >>= f₂) := by
  cases r with
  | error e => exact rfl
  | ok a => exact hf a

theorem ResultsAgree.bindRes {ns : List Name} {x₁ x₂ : Res State}
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

theorem ResultsAgree.bind {ns : List Name} {x₁ x₂ : Res State}
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
theorem ResAgree.cases {ns : List Name} {x₁ x₂ : Res (State × α)}
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

theorem ResultsAgree.cases {ns : List Name} {x₁ x₂ : Res State}
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
theorem ResAgree.toResults {ns : List Name} {x₁ x₂ : Res (State × α)}
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

/-! ## Association-list lemmas -/

theorem lookupBy_setBy_self [DecidableEq κ] (k : κ) (v : α)
    (l : List (κ × α)) : lookupBy k (setBy k v l) = some v := by
  induction l with
  | nil => simp [setBy, lookupBy]
  | cons hd tl ih =>
      obtain ⟨k', v'⟩ := hd
      by_cases h : k = k'
      · simp [setBy, lookupBy, h]
      · simp [setBy, lookupBy, h, ih]

theorem lookupBy_setBy_ne [DecidableEq κ] {k k' : κ} (h : k ≠ k')
    (v : α) (l : List (κ × α)) :
    lookupBy k (setBy k' v l) = lookupBy k l := by
  induction l with
  | nil => simp [setBy, lookupBy, h]
  | cons hd tl ih =>
      obtain ⟨k'', v''⟩ := hd
      by_cases h2 : k' = k''
      · subst h2
        simp [setBy, lookupBy, h]
      · by_cases h3 : k = k''
        · simp [setBy, lookupBy, h2, h3]
        · simp [setBy, lookupBy, h2, h3, ih]

/-- Inserting a scratch binding moves a state within its
`EnvAgreeExcept` class. -/
theorem EnvAgreeExcept.setEnv_right {ns : List Name} {s₁ s₂ : State}
    (h : EnvAgreeExcept ns s₁ s₂) {n : Name} (hn : n ∈ ns) (b : Binding) :
    EnvAgreeExcept ns s₁ (s₂.setEnv n b) :=
  ⟨h.storage, h.heap, h.nextId, h.net, fun m hm => by
    have hne : m ≠ n := fun heq => hm (heq ▸ hn)
    simpa [State.setEnv, lookupBy_setBy_ne hne] using h.env m hm,
    h.selfBalance⟩

/-- Setting the same (non-scratch or scratch) binding on both sides
preserves agreement. -/
theorem EnvAgreeExcept.setEnv_both {ns : List Name} {s₁ s₂ : State}
    (h : EnvAgreeExcept ns s₁ s₂) (n : Name) (b : Binding) :
    EnvAgreeExcept ns (s₁.setEnv n b) (s₂.setEnv n b) :=
  ⟨h.storage, h.heap, h.nextId, h.net, fun m hm => by
    by_cases he : m = n
    · subst he
      simp [State.setEnv, lookupBy_setBy_self]
    · simp [State.setEnv, lookupBy_setBy_ne he, h.env m hm],
    h.selfBalance⟩

/-! ## Relational lemmas for the storage primitives -/

theorem findStorage_congr {ns : List Name} {s₁ s₂ : State}
    (h : EnvAgreeExcept ns s₁ s₂) (root : Name) (segs : List Seg) :
    s₁.findStorage root segs = s₂.findStorage root segs := by
  unfold State.findStorage
  rw [h.storage]

theorem saveStorage_agree {ns : List Name} {s₁ s₂ : State}
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

theorem getEnv_congr {ns : List Name} {s₁ s₂ : State}
    (h : EnvAgreeExcept ns s₁ s₂) {n : Name} (hn : n ∉ ns) :
    s₁.getEnv n = s₂.getEnv n := by
  unfold State.getEnv
  rw [h.env n hn]

/-! ## Further state-primitive congruences -/

theorem getObj_congr {ns : List Name} {s₁ s₂ : State}
    (h : EnvAgreeExcept ns s₁ s₂) (id : Nat) :
    s₁.getObj id = s₂.getObj id := by
  unfold State.getObj
  rw [h.heap]

theorem setObj_agree {ns : List Name} {s₁ s₂ : State}
    (h : EnvAgreeExcept ns s₁ s₂) (id : Nat) (obj : MObj) :
    EnvAgreeExcept ns (s₁.setObj id obj) (s₂.setObj id obj) :=
  ⟨h.storage, by simp [State.setObj, h.heap], h.nextId, h.net, h.env,
    h.selfBalance⟩

theorem setNet_agree {ns : List Name} {s₁ s₂ : State}
    (h : EnvAgreeExcept ns s₁ s₂) (addr amount : Int) :
    EnvAgreeExcept ns (s₁.setNet addr amount) (s₂.setNet addr amount) :=
  ⟨h.storage, h.heap, h.nextId, by simp [State.setNet, h.net], h.env,
    h.selfBalance⟩

theorem getNet_congr {ns : List Name} {s₁ s₂ : State}
    (h : EnvAgreeExcept ns s₁ s₂) (addr : Int) :
    s₁.getNet addr = s₂.getNet addr := by
  unfold State.getNet
  rw [h.net]

theorem alloc_agree {ns : List Name} {s₁ s₂ : State}
    (h : EnvAgreeExcept ns s₁ s₂) (obj : MObj) :
    (s₁.alloc obj).2 = (s₂.alloc obj).2 ∧
      EnvAgreeExcept ns (s₁.alloc obj).1 (s₂.alloc obj).1 :=
  ⟨by simp [State.alloc, h.nextId],
    ⟨h.storage, by simp [State.alloc, h.heap, h.nextId],
      by simp [State.alloc, h.nextId], h.net, h.env, h.selfBalance⟩⟩

/-! ## Congruence for the cross-domain copies -/

mutual
theorem copyStToM_agree {ns : List Name} {s₁ s₂ : State}
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
  | .array elems =>
      rw [copyStToM, copyStToM]
      refine ResAgree.bind (copyStElems_agree h elems) ?_
      intro t₁ t₂ melems ht
      exact ⟨by simp [ht.nextId],
        ht.storage, by simp [ht.heap, ht.nextId],
        by simp [ht.nextId], ht.net, ht.env, ht.selfBalance⟩
  | .map entries dflt => rw [copyStToM, copyStToM]; exact rfl

theorem copyStFields_agree {ns : List Name} {s₁ s₂ : State}
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

theorem copyStElems_agree {ns : List Name} {s₁ s₂ : State}
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

theorem allocDefault_agree {ns : List Name} {s₁ s₂ : State}
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
theorem copyMToSt_congr {ns : List Name} {s₁ s₂ : State}
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

theorem copyMFields_congr {ns : List Name} {s₁ s₂ : State}
    (h : EnvAgreeExcept ns s₁ s₂) (rem : List Nat)
    (fields : List (Name × MVal)) :
    copyMFields s₁ rem fields = copyMFields s₂ rem fields := by
  match fields with
  | [] => rw [copyMFields, copyMFields]
  | (name, v) :: rest =>
      rw [copyMFields, copyMFields, copyMToSt_congr h rem v,
        copyMFields_congr h rem rest]
termination_by (rem.length, fields.length + 1)

theorem copyMElems_congr {ns : List Name} {s₁ s₂ : State}
    (h : EnvAgreeExcept ns s₁ s₂) (rem : List Nat) (elems : List MVal) :
    copyMElems s₁ rem elems = copyMElems s₂ rem elems := by
  match elems with
  | [] => rw [copyMElems, copyMElems]
  | v :: rest =>
      rw [copyMElems, copyMElems, copyMToSt_congr h rem v,
        copyMElems_congr h rem rest]
termination_by (rem.length, elems.length + 1)
end

theorem copyMem_congr {ns : List Name} {s₁ s₂ : State}
    (h : EnvAgreeExcept ns s₁ s₂) (v : MVal) :
    copyMem s₁ v = copyMem s₂ v := by
  unfold copyMem
  rw [h.heap, copyMToSt_congr h]

/-! ## Freshness extraction -/

theorem fresh_base {ns : List Name} {kind : Kind} {ty : Ty}
    {base : WrappedExpr} {fld : Field}
    (hf : ∀ n ∈ ns, usesVar (WrappedExpr.field kind ty base fld) n = false) :
    ∀ n ∈ ns, usesVar base n = false := fun n hn => by
  have := hf n hn
  simpa [usesVar] using this

theorem fresh_index_base {ns : List Name} {kind : Kind} {ty : Ty}
    {base index : WrappedExpr}
    (hf : ∀ n ∈ ns, usesVar (WrappedExpr.index kind ty base index) n = false) :
    ∀ n ∈ ns, usesVar base n = false := fun n hn => by
  have := hf n hn
  simp [usesVar] at this
  exact this.1

theorem fresh_index_index {ns : List Name} {kind : Kind} {ty : Ty}
    {base index : WrappedExpr}
    (hf : ∀ n ∈ ns, usesVar (WrappedExpr.index kind ty base index) n = false) :
    ∀ n ∈ ns, usesVar index n = false := fun n hn => by
  have := hf n hn
  simp [usesVar] at this
  exact this.2

theorem fresh_push {ns : List Name} {target : WrappedExpr}
    (hf : ∀ n ∈ ns, usesVar (WrappedExpr.pushPlace target) n = false) :
    ∀ n ∈ ns, usesVar target n = false := fun n hn => by
  have := hf n hn
  simpa [usesVar] using this

/-- Bind inversion on a successful computation. -/
theorem bindOk_inv {x : Res α} {f : α -> Res β} {b : β}
    (h : (x >>= f) = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => exact nomatch h
  | ok a => exact ⟨a, rfl, h⟩

/-! ## Resolved-location freshness and congruence

`++`/`--` and `op=` resolve their l-value once and then read and write
through the resulting `Loc` (`readLoc`/`writeLoc`). The congruence for
those reads and writes needs to know that a root `Loc`'s name is not a
scratch name; `resolveLoc_fresh` extracts that from the freshness of
the resolved expression. -/

/-- The environment names a resolved location can touch are not scratch
names. Nested locations address storage or the heap and are trivially
fresh. -/
def LocFresh (ns : List Name) : Loc -> Prop
  | Loc.stack n => n ∉ ns
  | Loc.storageLocal n => n ∉ ns
  | Loc.memoryRoot n => n ∉ ns
  | _ => True

theorem resolveLoc_fresh {ns : List Name} {s t : State}
    {e : WrappedExpr} {loc : Loc}
    (hf : ∀ n ∈ ns, usesVar e n = false)
    (h : resolveLoc s e = .ok (t, loc)) : LocFresh ns loc := by
  match e with
  | .var kind ty fld =>
      have hn : fld.name ∉ ns := fun hmem => by
        have := hf fld.name hmem
        simp [usesVar] at this
      cases kind with
      | stack =>
          rw [resolveLoc] at h
          cases h
          exact hn
      | memory =>
          rw [resolveLoc] at h
          cases h
          exact hn
      | storage =>
          rw [resolveLoc] at h
          by_cases ho : fld.origin = some StorageOrigin.global
          · rw [if_pos ho] at h
            cases h
            exact trivial
          · rw [if_neg ho] at h
            cases h
            exact hn
  | .field kind ty base fld =>
      cases kind with
      | storage =>
          rw [resolveLoc] at h
          obtain ⟨⟨t', root, segs⟩, _, h2⟩ := bindOk_inv h
          cases h2
          exact trivial
      | memory =>
          rw [resolveLoc] at h
          obtain ⟨⟨t', baseId⟩, _, h2⟩ := bindOk_inv h
          cases h2
          exact trivial
      | stack =>
          rw [resolveLoc] at h
          · exact nomatch h
          all_goals nofun
  | .index kind ty base index =>
      cases kind with
      | storage =>
          rw [resolveLoc] at h
          obtain ⟨⟨t', root, segs⟩, _, h2⟩ := bindOk_inv h
          obtain ⟨⟨u', i⟩, _, h3⟩ := bindOk_inv h2
          cases h3
          exact trivial
      | memory =>
          rw [resolveLoc] at h
          obtain ⟨⟨t', baseId⟩, _, h2⟩ := bindOk_inv h
          obtain ⟨⟨u', i⟩, _, h3⟩ := bindOk_inv h2
          cases h3
          exact trivial
      | stack =>
          rw [resolveLoc] at h
          · exact nomatch h
          all_goals nofun
  | .pushPlace target =>
      rw [resolveLoc] at h
      obtain ⟨⟨t', root, segs⟩, _, h2⟩ := bindOk_inv h
      cases h2
      exact trivial
  | .bool b => rw [resolveLoc.eq_def] at h; exact nomatch h
  | .intLit ty v => rw [resolveLoc.eq_def] at h; exact nomatch h
  | .mkCall kind ty nm args => rw [resolveLoc.eq_def] at h; exact nomatch h
  | .mkBinop op l r => rw [resolveLoc.eq_def] at h; exact nomatch h
  | .mkUnop op arg => rw [resolveLoc.eq_def] at h; exact nomatch h
  | .mkIncDec op target => rw [resolveLoc.eq_def] at h; exact nomatch h
  | .mkTernary c t el => rw [resolveLoc.eq_def] at h; exact nomatch h

/-- The data location a resolved `Loc` addresses. -/
def locKind : Loc -> Kind
  | .stack _ => Kind.stack
  | .storageLocal _ => Kind.storage
  | .storage _ _ => Kind.storage
  | .memoryRoot _ => Kind.memory
  | .memoryField _ _ => Kind.memory
  | .memoryIndex _ _ => Kind.memory

/-- Resolution is kind-coherent: the location addresses the place
expression's own data location. -/
theorem resolveLoc_kind {s t : State} {e : WrappedExpr} {loc : Loc}
    (h : resolveLoc s e = .ok (t, loc)) : locKind loc = e.kind := by
  match e with
  | .var kind ty fld =>
      cases kind with
      | stack => rw [resolveLoc] at h; cases h; rfl
      | memory => rw [resolveLoc] at h; cases h; rfl
      | storage =>
          rw [resolveLoc] at h
          by_cases ho : fld.origin = some StorageOrigin.global
          · rw [if_pos ho] at h; cases h; rfl
          · rw [if_neg ho] at h; cases h; rfl
  | .field kind ty base fld =>
      cases kind with
      | storage =>
          rw [resolveLoc] at h
          obtain ⟨⟨t', root, segs⟩, _, h2⟩ := bindOk_inv h
          cases h2
          rfl
      | memory =>
          rw [resolveLoc] at h
          obtain ⟨⟨t', baseId⟩, _, h2⟩ := bindOk_inv h
          cases h2
          rfl
      | stack =>
          rw [resolveLoc] at h
          · exact nomatch h
          all_goals nofun
  | .index kind ty base index =>
      cases kind with
      | storage =>
          rw [resolveLoc] at h
          obtain ⟨⟨t', root, segs⟩, _, h2⟩ := bindOk_inv h
          obtain ⟨⟨u', i⟩, _, h3⟩ := bindOk_inv h2
          cases h3
          rfl
      | memory =>
          rw [resolveLoc] at h
          obtain ⟨⟨t', baseId⟩, _, h2⟩ := bindOk_inv h
          obtain ⟨⟨u', i⟩, _, h3⟩ := bindOk_inv h2
          cases h3
          rfl
      | stack =>
          rw [resolveLoc] at h
          · exact nomatch h
          all_goals nofun
  | .pushPlace target =>
      rw [resolveLoc] at h
      obtain ⟨⟨t', root, segs⟩, _, h2⟩ := bindOk_inv h
      cases h2
      rfl
  | .bool b => rw [resolveLoc.eq_def] at h; exact nomatch h
  | .intLit ty v => rw [resolveLoc.eq_def] at h; exact nomatch h
  | .mkCall kind ty nm args => rw [resolveLoc.eq_def] at h; exact nomatch h
  | .mkBinop op l r => rw [resolveLoc.eq_def] at h; exact nomatch h
  | .mkUnop op arg => rw [resolveLoc.eq_def] at h; exact nomatch h
  | .mkIncDec op target => rw [resolveLoc.eq_def] at h; exact nomatch h
  | .mkTernary c t el => rw [resolveLoc.eq_def] at h; exact nomatch h

/-- A root location (stack, alias, memory root) only comes from a
`var` place. -/
theorem resolveLoc_rootLoc_var {s t : State} {e : WrappedExpr} {loc : Loc}
    (h : resolveLoc s e = .ok (t, loc))
    (hroot : (∃ n, loc = Loc.stack n) ∨ (∃ n, loc = Loc.storageLocal n) ∨
      (∃ n, loc = Loc.memoryRoot n)) :
    ∃ kind ty fld, e = WrappedExpr.var kind ty fld := by
  match e with
  | .var kind ty fld => exact ⟨kind, ty, fld, rfl⟩
  | .field kind ty base fld =>
      cases kind with
      | storage =>
          rw [resolveLoc] at h
          obtain ⟨⟨t', root, segs⟩, _, h2⟩ := bindOk_inv h
          cases h2
          rcases hroot with ⟨n, h⟩ | ⟨n, h⟩ | ⟨n, h⟩ <;> exact nomatch h
      | memory =>
          rw [resolveLoc] at h
          obtain ⟨⟨t', baseId⟩, _, h2⟩ := bindOk_inv h
          cases h2
          rcases hroot with ⟨n, h⟩ | ⟨n, h⟩ | ⟨n, h⟩ <;> exact nomatch h
      | stack =>
          rw [resolveLoc] at h
          · exact nomatch h
          all_goals nofun
  | .index kind ty base index =>
      cases kind with
      | storage =>
          rw [resolveLoc] at h
          obtain ⟨⟨t', root, segs⟩, _, h2⟩ := bindOk_inv h
          obtain ⟨⟨u', i⟩, _, h3⟩ := bindOk_inv h2
          cases h3
          rcases hroot with ⟨n, h⟩ | ⟨n, h⟩ | ⟨n, h⟩ <;> exact nomatch h
      | memory =>
          rw [resolveLoc] at h
          obtain ⟨⟨t', baseId⟩, _, h2⟩ := bindOk_inv h
          obtain ⟨⟨u', i⟩, _, h3⟩ := bindOk_inv h2
          cases h3
          rcases hroot with ⟨n, h⟩ | ⟨n, h⟩ | ⟨n, h⟩ <;> exact nomatch h
      | stack =>
          rw [resolveLoc] at h
          · exact nomatch h
          all_goals nofun
  | .pushPlace target =>
      rw [resolveLoc] at h
      obtain ⟨⟨t', root, segs⟩, _, h2⟩ := bindOk_inv h
      cases h2
      rcases hroot with ⟨n, h⟩ | ⟨n, h⟩ | ⟨n, h⟩ <;> exact nomatch h
  | .bool b => rw [resolveLoc.eq_def] at h; exact nomatch h
  | .intLit ty v => rw [resolveLoc.eq_def] at h; exact nomatch h
  | .mkCall kind ty nm args => rw [resolveLoc.eq_def] at h; exact nomatch h
  | .mkBinop op l r => rw [resolveLoc.eq_def] at h; exact nomatch h
  | .mkUnop op arg => rw [resolveLoc.eq_def] at h; exact nomatch h
  | .mkIncDec op target => rw [resolveLoc.eq_def] at h; exact nomatch h
  | .mkTernary c t el => rw [resolveLoc.eq_def] at h; exact nomatch h

/-- Reading through a fresh resolved location is insensitive to the
scratch names: `readLoc` returns equal results on agreeing states. -/
theorem readLoc_congr {ns : List Name} {s₁ s₂ : State} {loc : Loc}
    (h : EnvAgreeExcept ns s₁ s₂) (hfresh : LocFresh ns loc) :
    readLoc s₁ loc = readLoc s₂ loc := by
  cases loc with
  | stack n =>
      rw [readLoc, readLoc, getEnv_congr h hfresh]
  | storageLocal n => rfl
  | memoryRoot n => rfl
  | storage root segs =>
      rw [readLoc, readLoc, findStorage_congr h]
  | memoryField id fld =>
      rw [readLoc, readLoc, getObj_congr h id]
  | memoryIndex id i =>
      rw [readLoc, readLoc, getObj_congr h id]

/-- Writing the same value through the same resolved location preserves
agreement (any location: an identical write cannot break agreement, so
no freshness is needed). -/
theorem writeLoc_agree {ns : List Name} {s₁ s₂ : State} {loc : Loc}
    (h : EnvAgreeExcept ns s₁ s₂) (v : Value) :
    ResultsAgree ns (writeLoc s₁ loc v) (writeLoc s₂ loc v) := by
  cases loc with
  | stack n => exact EnvAgreeExcept.setEnv_both h n _
  | storageLocal n => exact rfl
  | memoryRoot n => exact rfl
  | storage root segs => exact saveStorage_agree h root segs v.toSVal
  | memoryField id fld =>
      rw [writeLoc, writeLoc, getObj_congr h id]
      refine bindPureResults_agree _ fun obj => ?_
      cases obj with
      | struct fields => exact setObj_agree h id _
      | array elems => exact rfl
  | memoryIndex id i =>
      rw [writeLoc, writeLoc, getObj_congr h id]
      refine bindPureResults_agree _ fun obj => ?_
      cases obj with
      | struct fields => exact rfl
      | array elems =>
          by_cases hb : 0 ≤ i ∧ i.toNat < elems.length
          · simp only [if_pos hb]
            exact setObj_agree h id _
          · simp only [if_neg hb]
            exact rfl

/-! ## The interpreter congruence

The heart of the soundness bridge: every function of the mutual
evaluation block in `Semantics.lean` sends states that agree off `ns`
to results that agree off `ns`, provided the evaluated expression does
not mention the names in `ns`. The recursion mirrors the interpreter's
own (same measure `4 * size + rank`). -/

mutual

theorem resolveS_agree {ns : List Name} {s₁ s₂ : State}
    (h : EnvAgreeExcept ns s₁ s₂) (e : WrappedExpr)
    (hf : ∀ n ∈ ns, usesVar e n = false) :
    ResAgree ns (resolveS s₁ e) (resolveS s₂ e) := by
  match e with
  | .var kind ty fld =>
      have hn : fld.name ∉ ns := fun hmem => by
        have := hf fld.name hmem
        simp [usesVar] at this
      rw [resolveS, resolveS, h.env fld.name hn]
      cases lookupBy fld.name s₂.env with
      | none =>
          by_cases ho : fld.origin = some StorageOrigin.global
          · simp only [if_pos ho]
            exact ⟨rfl, h⟩
          · simp only [if_neg ho]
            exact rfl
      | some b =>
          cases b with
          | val v => exact rfl
          | spath root segs => exact ⟨rfl, h⟩
          | mref id => exact rfl
  | .field kind ty base fld =>
      rw [resolveS, resolveS]
      refine ResAgree.bind (resolveS_agree h base (fresh_base hf)) ?_
      intro t₁ t₂ a ht
      exact ⟨rfl, ht⟩
  | .index kind ty base index =>
      rw [resolveS, resolveS]
      refine ResAgree.bind (resolveS_agree h base (fresh_index_base hf)) ?_
      intro t₁ t₂ a ht
      refine ResAgree.bind (evalInt_agree ht index (fresh_index_index hf)) ?_
      intro u₁ u₂ i hu
      exact ⟨rfl, hu⟩
  | .pushPlace target =>
      rw [resolveS, resolveS]
      refine ResAgree.bind (resolveS_agree h target (fresh_push hf)) ?_
      intro t₁ t₂ a ht
      obtain ⟨root, segs⟩ := a
      simp only [findStorage_congr ht]
      refine bindPureRes_agree _ fun arr => ?_
      cases arr with
      | array elems =>
          match hty : target.ty with
          | Ty.ref (RefTy.array elemTy) =>
              refine ResultsAgree.bindRes
                (saveStorage_agree ht root segs
                  (SVal.array (elems ++ [defaultForTy elemTy]))) ?_
              intro u₁ u₂ hu
              exact ⟨rfl, hu⟩
          | Ty.bool => exact rfl
          | Ty.uint => exact rfl
          | Ty.int => exact rfl
          | Ty.ref (RefTy.struct nm) => exact rfl
          | Ty.ref (RefTy.mapping k v) => exact rfl
      | prim p => cases p <;> exact rfl
      | struct fields => exact rfl
      | map entries dflt => exact rfl
  | .bool b => rw [resolveS.eq_def, resolveS.eq_def]; exact rfl
  | .intLit ty v => rw [resolveS.eq_def, resolveS.eq_def]; exact rfl
  | .mkCall kind ty nm args => rw [resolveS.eq_def, resolveS.eq_def]; exact rfl
  | .mkBinop op l r => rw [resolveS.eq_def, resolveS.eq_def]; exact rfl
  | .mkUnop op arg => rw [resolveS.eq_def, resolveS.eq_def]; exact rfl
  | .mkIncDec op target => rw [resolveS.eq_def, resolveS.eq_def]; exact rfl
  | .mkTernary c t el => rw [resolveS.eq_def, resolveS.eq_def]; exact rfl
termination_by 4 * e.size + 0
decreasing_by all_goals
  first
  | omega
  | (simp [Typed.WrappedExpr.size] <;> omega)

theorem resolveMBase_agree {ns : List Name} {s₁ s₂ : State}
    (h : EnvAgreeExcept ns s₁ s₂) (e : WrappedExpr)
    (hf : ∀ n ∈ ns, usesVar e n = false) :
    ResAgree ns (resolveMBase s₁ e) (resolveMBase s₂ e) := by
  match e with
  | .var kind ty fld =>
      have hn : fld.name ∉ ns := fun hmem => by
        have := hf fld.name hmem
        simp [usesVar] at this
      rw [resolveMBase, resolveMBase, getEnv_congr h hn]
      refine bindPureRes_agree _ fun b => ?_
      cases b with
      | val v => exact rfl
      | spath root segs => exact rfl
      | mref id => exact ⟨rfl, h⟩
  | .field kind ty base fld =>
      rw [resolveMBase, resolveMBase]
      refine ResAgree.bind (resolveMBase_agree h base (fresh_base hf)) ?_
      intro t₁ t₂ baseId ht
      simp only [getObj_congr ht]
      refine bindPureRes_agree _ fun obj => ?_
      cases obj with
      | array elems => exact rfl
      | struct fields =>
          simp only []
          cases lookupBy fld.name fields with
          | none => exact rfl
          | some v =>
              cases v with
              | prim p => cases p <;> exact rfl
              | ref id => exact ⟨rfl, ht⟩
  | .index kind ty base index =>
      rw [resolveMBase, resolveMBase]
      refine ResAgree.bind (resolveMBase_agree h base (fresh_index_base hf)) ?_
      intro t₁ t₂ baseId ht
      refine ResAgree.bind (evalInt_agree ht index (fresh_index_index hf)) ?_
      intro u₁ u₂ i hu
      simp only [getObj_congr hu]
      refine bindPureRes_agree _ fun obj => ?_
      cases obj with
      | struct fields => exact rfl
      | array elems =>
          by_cases hb : 0 ≤ i ∧ i.toNat < elems.length
          · simp only [dif_pos hb]
            cases elems.get ⟨i.toNat, hb.2⟩ with
            | prim p => cases p <;> exact rfl
            | ref id => exact ⟨rfl, hu⟩
          · simp only [dif_neg hb]
            exact rfl
  | .bool b => rw [resolveMBase.eq_def, resolveMBase.eq_def]; exact rfl
  | .intLit ty v => rw [resolveMBase.eq_def, resolveMBase.eq_def]; exact rfl
  | .pushPlace target => rw [resolveMBase.eq_def, resolveMBase.eq_def]; exact rfl
  | .mkCall kind ty nm args =>
      rw [resolveMBase.eq_def, resolveMBase.eq_def]; exact rfl
  | .mkBinop op l r => rw [resolveMBase.eq_def, resolveMBase.eq_def]; exact rfl
  | .mkUnop op arg => rw [resolveMBase.eq_def, resolveMBase.eq_def]; exact rfl
  | .mkIncDec op target =>
      rw [resolveMBase.eq_def, resolveMBase.eq_def]; exact rfl
  | .mkTernary c t el =>
      rw [resolveMBase.eq_def, resolveMBase.eq_def]; exact rfl
termination_by 4 * e.size + 0
decreasing_by all_goals
  first
  | omega
  | (simp [Typed.WrappedExpr.size] <;> omega)

theorem readM_agree {ns : List Name} {s₁ s₂ : State}
    (h : EnvAgreeExcept ns s₁ s₂) (e : WrappedExpr)
    (hf : ∀ n ∈ ns, usesVar e n = false) :
    ResAgree ns (readM s₁ e) (readM s₂ e) := by
  match e with
  | .var kind ty fld =>
      have hn : fld.name ∉ ns := fun hmem => by
        have := hf fld.name hmem
        simp [usesVar] at this
      rw [readM, readM, getEnv_congr h hn]
      refine bindPureRes_agree _ fun b => ?_
      cases b with
      | val v => exact rfl
      | spath root segs => exact rfl
      | mref id => exact ⟨rfl, h⟩
  | .field kind ty base fld =>
      rw [readM, readM]
      refine ResAgree.bind (resolveMBase_agree h base (fresh_base hf)) ?_
      intro t₁ t₂ baseId ht
      simp only [getObj_congr ht]
      refine bindPureRes_agree _ fun obj => ?_
      cases obj with
      | array elems => exact rfl
      | struct fields =>
          simp only []
          cases lookupBy fld.name fields with
          | none => exact rfl
          | some v => exact ⟨rfl, ht⟩
  | .index kind ty base index =>
      rw [readM, readM]
      refine ResAgree.bind (resolveMBase_agree h base (fresh_index_base hf)) ?_
      intro t₁ t₂ baseId ht
      refine ResAgree.bind (evalInt_agree ht index (fresh_index_index hf)) ?_
      intro u₁ u₂ i hu
      simp only [getObj_congr hu]
      refine bindPureRes_agree _ fun obj => ?_
      cases obj with
      | struct fields => exact rfl
      | array elems =>
          by_cases hb : 0 ≤ i ∧ i.toNat < elems.length
          · simp only [dif_pos hb]
            exact ⟨rfl, hu⟩
          · simp only [dif_neg hb]
            exact rfl
  | .bool b => rw [readM.eq_def, readM.eq_def]; exact rfl
  | .intLit ty v => rw [readM.eq_def, readM.eq_def]; exact rfl
  | .pushPlace target => rw [readM.eq_def, readM.eq_def]; exact rfl
  | .mkCall kind ty nm args => rw [readM.eq_def, readM.eq_def]; exact rfl
  | .mkBinop op l r => rw [readM.eq_def, readM.eq_def]; exact rfl
  | .mkUnop op arg => rw [readM.eq_def, readM.eq_def]; exact rfl
  | .mkIncDec op target => rw [readM.eq_def, readM.eq_def]; exact rfl
  | .mkTernary c t el => rw [readM.eq_def, readM.eq_def]; exact rfl
termination_by 4 * e.size + 1
decreasing_by all_goals
  first
  | omega
  | (simp [Typed.WrappedExpr.size] <;> omega)

theorem resolveLoc_agree {ns : List Name} {s₁ s₂ : State}
    (h : EnvAgreeExcept ns s₁ s₂) (e : WrappedExpr)
    (hf : ∀ n ∈ ns, usesVar e n = false) :
    ResAgree ns (resolveLoc s₁ e) (resolveLoc s₂ e) := by
  match e with
  | .var kind ty fld =>
      cases kind with
      | stack => rw [resolveLoc, resolveLoc]; exact ⟨rfl, h⟩
      | memory => rw [resolveLoc, resolveLoc]; exact ⟨rfl, h⟩
      | storage =>
          rw [resolveLoc, resolveLoc]
          by_cases ho : fld.origin = some StorageOrigin.global
          · simp only [if_pos ho]
            exact ⟨rfl, h⟩
          · simp only [if_neg ho]
            exact ⟨rfl, h⟩
  | .field kind ty base fld =>
      cases kind with
      | storage =>
          rw [resolveLoc, resolveLoc]
          refine ResAgree.bind
            (resolveS_agree h (WrappedExpr.field Kind.storage Ty.uint base fld)
              (fun n hn => by
                have := hf n hn
                simpa [usesVar] using this)) ?_
          intro t₁ t₂ a ht
          exact ⟨rfl, ht⟩
      | memory =>
          rw [resolveLoc, resolveLoc]
          refine ResAgree.bind (resolveMBase_agree h base (fresh_base hf)) ?_
          intro t₁ t₂ baseId ht
          exact ⟨rfl, ht⟩
      | stack =>
          rw [resolveLoc, resolveLoc]
          · exact rfl
          all_goals nofun
  | .index kind ty base index =>
      cases kind with
      | storage =>
          rw [resolveLoc, resolveLoc]
          refine ResAgree.bind (resolveS_agree h base (fresh_index_base hf)) ?_
          intro t₁ t₂ a ht
          refine ResAgree.bind (evalInt_agree ht index (fresh_index_index hf)) ?_
          intro u₁ u₂ i hu
          exact ⟨rfl, hu⟩
      | memory =>
          rw [resolveLoc, resolveLoc]
          refine ResAgree.bind (resolveMBase_agree h base (fresh_index_base hf)) ?_
          intro t₁ t₂ baseId ht
          refine ResAgree.bind (evalInt_agree ht index (fresh_index_index hf)) ?_
          intro u₁ u₂ i hu
          exact ⟨rfl, hu⟩
      | stack =>
          rw [resolveLoc, resolveLoc]
          · exact rfl
          all_goals nofun
  | .pushPlace target =>
      rw [resolveLoc, resolveLoc]
      refine ResAgree.bind
        (resolveS_agree h (WrappedExpr.pushPlace target) hf) ?_
      intro t₁ t₂ a ht
      exact ⟨rfl, ht⟩
  | .bool b => rw [resolveLoc.eq_def, resolveLoc.eq_def]; exact rfl
  | .intLit ty v => rw [resolveLoc.eq_def, resolveLoc.eq_def]; exact rfl
  | .mkCall kind ty nm args =>
      rw [resolveLoc.eq_def, resolveLoc.eq_def]; exact rfl
  | .mkBinop op l r => rw [resolveLoc.eq_def, resolveLoc.eq_def]; exact rfl
  | .mkUnop op arg => rw [resolveLoc.eq_def, resolveLoc.eq_def]; exact rfl
  | .mkIncDec op target => rw [resolveLoc.eq_def, resolveLoc.eq_def]; exact rfl
  | .mkTernary c t el => rw [resolveLoc.eq_def, resolveLoc.eq_def]; exact rfl
termination_by 4 * e.size + 1
decreasing_by all_goals
  first
  | omega
  | (simp [Typed.WrappedExpr.size] <;> omega)

theorem evalValue_agree {ns : List Name} {s₁ s₂ : State}
    (h : EnvAgreeExcept ns s₁ s₂) (e : WrappedExpr)
    (hf : ∀ n ∈ ns, usesVar e n = false) :
    ResAgree ns (evalValue s₁ e) (evalValue s₂ e) := by
  match e with
  | .bool b => rw [evalValue, evalValue]; exact ⟨rfl, h⟩
  | .intLit ty v => rw [evalValue, evalValue]; exact ⟨rfl, h⟩
  | .var kind ty fld =>
      cases kind with
      | stack =>
          have hn : fld.name ∉ ns := fun hmem => by
            have := hf fld.name hmem
            simp [usesVar] at this
          rw [evalValue, evalValue]
          simp only [getEnv_congr h hn]
          refine bindPureRes_agree _ fun b => ?_
          cases b with
          | val v => exact ⟨rfl, h⟩
          | spath root segs => exact rfl
          | mref id => exact rfl
      | storage =>
          rw [evalValue, evalValue]
          refine ResAgree.bind
            (resolveS_agree h (WrappedExpr.var Kind.storage ty fld) hf) ?_
          intro t₁ t₂ a ht
          obtain ⟨root, segs⟩ := a
          simp only [findStorage_congr ht]
          refine bindPureRes_agree _ fun v => ?_
          exact bindPureRes_agree _ fun val => ⟨rfl, ht⟩
      | memory => rw [evalValue, evalValue]; exact rfl
  | .field kind ty base fld =>
      cases kind with
      | storage =>
          rw [evalValue, evalValue]
          refine ResAgree.bind
            (resolveS_agree h (WrappedExpr.field Kind.storage ty base fld) hf) ?_
          intro t₁ t₂ a ht
          obtain ⟨root, segs⟩ := a
          simp only [findStorage_congr ht]
          refine bindPureRes_agree _ fun v => ?_
          exact bindPureRes_agree _ fun val => ⟨rfl, ht⟩
      | memory =>
          rw [evalValue, evalValue]
          refine ResAgree.bind
            (readM_agree h (WrappedExpr.field Kind.memory ty base fld) hf) ?_
          intro t₁ t₂ v ht
          exact bindPureRes_agree _ fun val => ⟨rfl, ht⟩
      | stack =>
          rw [evalValue, evalValue]
          · exact rfl
          all_goals nofun
  | .index kind ty base index =>
      cases kind with
      | storage =>
          rw [evalValue, evalValue]
          refine ResAgree.bind
            (resolveS_agree h (WrappedExpr.index Kind.storage ty base index) hf) ?_
          intro t₁ t₂ a ht
          obtain ⟨root, segs⟩ := a
          simp only [findStorage_congr ht]
          refine bindPureRes_agree _ fun v => ?_
          exact bindPureRes_agree _ fun val => ⟨rfl, ht⟩
      | memory =>
          rw [evalValue, evalValue]
          refine ResAgree.bind
            (readM_agree h (WrappedExpr.index Kind.memory ty base index) hf) ?_
          intro t₁ t₂ v ht
          exact bindPureRes_agree _ fun val => ⟨rfl, ht⟩
      | stack =>
          rw [evalValue, evalValue]
          · exact rfl
          all_goals nofun
  | .mkBinop op l r =>
      have hfl : ∀ n ∈ ns, usesVar l n = false := fun n hn => by
        have := hf n hn
        simp [usesVar] at this
        exact this.1
      have hfr : ∀ n ∈ ns, usesVar r n = false := fun n hn => by
        have := hf n hn
        simp [usesVar] at this
        exact this.2
      rw [evalValue, evalValue]
      refine ResAgree.bind (evalValue_agree h l hfl) ?_
      intro t₁ t₂ lv ht
      have hrest : ResAgree ns
          ((evalValue t₁ r) >>= fun x =>
            (applyBinOp op lv x.2) >>= fun v =>
              (checkArith (op.retTy l.ty) v) >>= fun v' =>
                Except.ok (x.1, v'))
          ((evalValue t₂ r) >>= fun x =>
            (applyBinOp op lv x.2) >>= fun v =>
              (checkArith (op.retTy l.ty) v) >>= fun v' =>
                Except.ok (x.1, v')) := by
        refine ResAgree.bind (evalValue_agree ht r hfr) ?_
        intro u₁ u₂ rv hu
        refine bindPureRes_agree _ fun v => ?_
        exact bindPureRes_agree _ fun v' => ⟨rfl, hu⟩
      cases op <;>
        first
        | exact hrest
        | (cases lv with
            | int v => exact hrest
            | bool b => cases b <;> first | exact ⟨rfl, ht⟩ | exact hrest)
  | .mkUnop op arg =>
      have hfa : ∀ n ∈ ns, usesVar arg n = false := fun n hn => by
        have := hf n hn
        simpa [usesVar] using this
      rw [evalValue, evalValue]
      refine ResAgree.bind (evalValue_agree h arg hfa) ?_
      intro t₁ t₂ v ht
      refine bindPureRes_agree _ fun v' => ?_
      split
      · exact bindPureRes_agree _ fun v'' => ⟨rfl, ht⟩
      · exact ⟨rfl, ht⟩
  | .mkIncDec op target =>
      have hft : ∀ n ∈ ns, usesVar target n = false := fun n hn => by
        have := hf n hn
        simpa [usesVar] using this
      rw [evalValue, evalValue]
      refine ResAgree.bindWith (resolveLoc_agree h target hft) ?_
      intro t₁ t₂ loc h₁ _ ht
      have hfresh : LocFresh ns loc := resolveLoc_fresh hft h₁
      show ResAgree ns
        ((readLoc t₁ loc) >>= fun old =>
          old.asInt >>= fun oldInt =>
            (checkArith target.ty
                (Value.int (if op.isIncrement then oldInt + 1
                  else oldInt - 1))) >>= fun newVal =>
              (writeLoc t₁ loc newVal) >>= fun s' =>
                Except.ok (s', if op.isPre then newVal else old))
        ((readLoc t₂ loc) >>= fun old =>
          old.asInt >>= fun oldInt =>
            (checkArith target.ty
                (Value.int (if op.isIncrement then oldInt + 1
                  else oldInt - 1))) >>= fun newVal =>
              (writeLoc t₂ loc newVal) >>= fun s' =>
                Except.ok (s', if op.isPre then newVal else old))
      rw [readLoc_congr ht hfresh]
      refine bindPureRes_agree _ fun old => ?_
      refine bindPureRes_agree _ fun oldInt => ?_
      refine bindPureRes_agree _ fun newVal => ?_
      refine ResultsAgree.bindRes (writeLoc_agree ht newVal) ?_
      intro u₁ u₂ hu
      exact ⟨rfl, hu⟩
  | .mkCall kind ty nm args =>
      by_cases hnm : nm = "net"
      · subst hnm
        match hargs : args with
        | [addr] =>
            have hszl : Typed.WrappedExpr.sizeList args = addr.size := by
              rw [hargs]
              simp [Typed.WrappedExpr.sizeList]
            have hfa : ∀ n ∈ ns, usesVar addr n = false := fun n hn => by
              have := hf n hn
              simp [usesVar, usesVarList] at this
              exact this
            rw [evalValue, evalValue]
            refine ResAgree.bind (evalInt_agree h addr hfa) ?_
            intro t₁ t₂ a ht
            exact ⟨by rw [getNet_congr ht], ht⟩
        | [] =>
            rw [evalValue, evalValue]
            · exact rfl
            all_goals simp
        | a :: b :: rest =>
            rw [evalValue, evalValue]
            · exact rfl
            all_goals simp
      · rw [evalValue, evalValue]
        · exact rfl
        all_goals simp [hnm]
  | .pushPlace target =>
      rw [evalValue.eq_def, evalValue.eq_def]
      exact rfl
  | .mkTernary c t el =>
      have hfc : ∀ n ∈ ns, usesVar c n = false := fun n hn => by
        have := hf n hn
        simp [usesVar] at this
        exact this.1.1
      have hft : ∀ n ∈ ns, usesVar t n = false := fun n hn => by
        have := hf n hn
        simp [usesVar] at this
        exact this.1.2
      have hfe : ∀ n ∈ ns, usesVar el n = false := fun n hn => by
        have := hf n hn
        simp [usesVar] at this
        exact this.2
      rw [evalValue, evalValue]
      refine ResAgree.bind (evalValue_agree h c hfc) ?_
      intro t₁ t₂ cv ht
      cases cv with
      | int v => exact rfl
      | bool b =>
          cases b with
          | true => exact evalValue_agree ht t hft
          | false => exact evalValue_agree ht el hfe
termination_by 4 * e.size + 2
decreasing_by all_goals
  first
  | omega
  | (simp [Typed.WrappedExpr.size] <;> omega)

theorem evalInt_agree {ns : List Name} {s₁ s₂ : State}
    (h : EnvAgreeExcept ns s₁ s₂) (e : WrappedExpr)
    (hf : ∀ n ∈ ns, usesVar e n = false) :
    ResAgree ns (evalInt s₁ e) (evalInt s₂ e) := by
  rw [evalInt, evalInt]
  refine ResAgree.bind (evalValue_agree h e hf) ?_
  intro t₁ t₂ v ht
  exact bindPureRes_agree _ fun i => ⟨rfl, ht⟩
termination_by 4 * e.size + 3
decreasing_by all_goals omega

theorem writeValue_agree {ns : List Name} {s₁ s₂ : State}
    (h : EnvAgreeExcept ns s₁ s₂) (target : WrappedExpr)
    (hf : ∀ n ∈ ns, usesVar target n = false) (v : Value) :
    ResultsAgree ns (writeValue s₁ target v) (writeValue s₂ target v) := by
  rw [writeValue, writeValue]
  refine ResAgree.bindState (resolveLoc_agree h target hf) ?_
  intro t₁ t₂ loc ht
  exact writeLoc_agree ht v
termination_by 4 * target.size + 2
decreasing_by all_goals omega

end


/-! ## Binding preservation

The congruence kit above runs the *same* expression from two different
states.  The LHS-unfold rules need the orthogonal fact: running an
expression that mentions none of `ns` leaves those bindings alone.

That is what lets the value frozen into `rv` (`Rules.freezeRhs`) survive
the target capture that runs next, and it is what the `pureExpr index`
side conditions used to stand in for.  Purity is far stronger than
non-interference with a reserved name — strong enough to exclude
`values[i++] = i`, which is exactly the program the calculus must
handle. -/

/-- Every name of `ns` has the same binding in any successful result. -/
def EnvKeeps (ns : List Name) (s : State) {α : Type} (r : Res (State × α)) :
    Prop :=
  ∀ t a, r = .ok (t, a) -> ∀ n ∈ ns, lookupBy n t.env = lookupBy n s.env

/-- The `Res State` form, for `writeLoc`. -/
def EnvKeepsS (ns : List Name) (s : State) (r : Res State) : Prop :=
  ∀ t, r = .ok t -> ∀ n ∈ ns, lookupBy n t.env = lookupBy n s.env

namespace EnvKeeps

theorem ok {ns : List Name} {s : State} {a : α} :
    EnvKeeps ns s (.ok (s, a)) := by
  intro t b h n _; cases h; rfl

theorem err {ns : List Name} {s : State} {e : Halt} :
    EnvKeeps ns s (α := α) (.error e) := by
  intro t a h; exact nomatch h

theorem step {ns : List Name} {s t : State} {a : α}
    (h : ∀ n ∈ ns, lookupBy n t.env = lookupBy n s.env) :
    EnvKeeps ns s (.ok (t, a)) := by
  intro u b hu; cases hu; exact h

theorem bind {ns : List Name} {s : State} {x : Res (State × α)}
    {f : State × α -> Res (State × β)}
    (hx : EnvKeeps ns s x)
    (hf : ∀ t a, x = .ok (t, a) -> EnvKeeps ns t (f (t, a))) :
    EnvKeeps ns s (x >>= f) := by
  intro u b hu n hn
  cases hxv : x with
  | error e => rw [hxv] at hu; exact nomatch hu
  | ok p =>
      obtain ⟨t, a⟩ := p
      rw [hxv] at hu
      exact (hf t a hxv u b hu n hn).trans (hx t a hxv n hn)

/-- Bind through a state-free (`Res α`) prefix such as `findStorage`. -/
theorem bindPure {ns : List Name} {s : State} {x : Res α}
    {f : α -> Res (State × β)}
    (hf : ∀ a, x = .ok a -> EnvKeeps ns s (f a)) :
    EnvKeeps ns s (x >>= f) := by
  intro u b hu n hn
  cases hxv : x with
  | error e => rw [hxv] at hu; exact nomatch hu
  | ok a => rw [hxv] at hu; exact hf a hxv u b hu n hn

theorem bindS {ns : List Name} {s : State} {x : Res State}
    {f : State -> Res (State × β)}
    (hx : EnvKeepsS ns s x)
    (hf : ∀ t, x = .ok t -> EnvKeeps ns t (f t)) :
    EnvKeeps ns s (x >>= f) := by
  intro u b hu n hn
  cases hxv : x with
  | error e => rw [hxv] at hu; exact nomatch hu
  | ok t =>
      rw [hxv] at hu
      exact (hf t hxv u b hu n hn).trans (hx t hxv n hn)

end EnvKeeps

/-- A successful storage write leaves the local bindings alone. -/
theorem saveStorage_env {t t' : State} {r : Name} {sg : List Seg}
    {x : SVal} (h : t.saveStorage r sg x = .ok t') :
    t'.env = t.env := by
  unfold State.saveStorage at h
  cases hlk : lookupBy r t.storage with
  | none => rw [hlk] at h; exact nomatch h
  | some sv =>
      rw [hlk] at h
      simp only [] at h
      obtain ⟨upd, hs, hfin⟩ := bindOk_inv h
      cases hfin
      rfl

/-- A write through a location that is fresh for `ns` keeps those
bindings: the only env-touching location is `Loc.stack`, and
`resolveLoc_fresh` says an expression free of `ns` never resolves to
one. -/
theorem writeLoc_keepS {ns : List Name} {s : State} {loc : Loc} {v : Value}
    (hfresh : LocFresh ns loc) : EnvKeepsS ns s (writeLoc s loc v) := by
  intro t ht n hn
  cases loc with
  | stack m =>
      have hm : m ∉ ns := hfresh
      rw [writeLoc] at ht
      cases ht
      refine lookupBy_setBy_ne ?_ _ _
      intro h
      exact hm (h ▸ hn)
  | storageLocal m => simp [writeLoc] at ht
  | memoryRoot m => simp [writeLoc] at ht
  | storage r sg =>
      rw [writeLoc] at ht
      rw [saveStorage_env ht]
  | memoryField id fld =>
      rw [writeLoc] at ht
      obtain ⟨obj, _, h2⟩ := bindOk_inv ht
      split at h2
      · cases h2; rfl
      · exact nomatch h2
  | memoryIndex id i =>
      rw [writeLoc] at ht
      obtain ⟨obj, _, h2⟩ := bindOk_inv ht
      split at h2
      · split at h2
        · cases h2; rfl
        · exact nomatch h2
      · exact nomatch h2


/-- Discharge a tail of nested pattern matches whose branches all either
keep the state or abort. -/
macro "keep_tail" : tactic =>
  `(tactic|
      (try simp only []
       repeat' (first
         | exact EnvKeeps.ok
         | exact EnvKeeps.err
         | (refine EnvKeeps.bindPure ?_
            intro _ _)
         | split)))

theorem saveStorage_keepS {ns : List Name} {t : State} {r : Name}
    {sg : List Seg} {x : SVal} : EnvKeepsS ns t (t.saveStorage r sg x) := by
  intro u hu n _
  rw [saveStorage_env hu]

mutual

theorem resolveS_keep {ns : List Name} (s : State) (e : WrappedExpr)
    (hf : ∀ n ∈ ns, usesVar e n = false) :
    EnvKeeps ns s (resolveS s e) := by
  match e with
  | .var kind ty fld =>
      rw [resolveS]
      cases lookupBy fld.name s.env with
      | none =>
          by_cases ho : fld.origin = some StorageOrigin.global
          · simp only [if_pos ho]; exact EnvKeeps.ok
          · simp only [if_neg ho]; exact EnvKeeps.err
      | some b =>
          cases b with
          | val v => exact EnvKeeps.err
          | spath root segs => exact EnvKeeps.ok
          | mref id => exact EnvKeeps.err
  | .field kind ty base fld =>
      rw [resolveS]
      refine EnvKeeps.bind (resolveS_keep s base (fresh_base hf)) ?_
      intro t a _
      exact EnvKeeps.ok
  | .index kind ty base index =>
      rw [resolveS]
      refine EnvKeeps.bind (resolveS_keep s base (fresh_index_base hf)) ?_
      intro t a _
      refine EnvKeeps.bind (evalInt_keep t index (fresh_index_index hf)) ?_
      intro u i _
      exact EnvKeeps.ok
  | .pushPlace target =>
      rw [resolveS]
      refine EnvKeeps.bind (resolveS_keep s target (fresh_push hf)) ?_
      intro t a _
      obtain ⟨root, segs⟩ := a
      refine EnvKeeps.bindPure ?_
      intro arr _
      cases arr with
      | array elems =>
          match hty : target.ty with
          | Ty.ref (RefTy.array elemTy) =>
              refine EnvKeeps.bindS saveStorage_keepS ?_
              intro u _
              exact EnvKeeps.ok
          | Ty.bool => exact EnvKeeps.err
          | Ty.uint => exact EnvKeeps.err
          | Ty.int => exact EnvKeeps.err
          | Ty.ref (RefTy.struct nm) => exact EnvKeeps.err
          | Ty.ref (RefTy.mapping k v) => exact EnvKeeps.err
      | prim p => cases p <;> exact EnvKeeps.err
      | struct fields => exact EnvKeeps.err
      | map entries dflt => exact EnvKeeps.err
  | .bool b => rw [resolveS.eq_def]; exact EnvKeeps.err
  | .intLit ty v => rw [resolveS.eq_def]; exact EnvKeeps.err
  | .mkCall kind ty nm args => rw [resolveS.eq_def]; exact EnvKeeps.err
  | .mkBinop op l r => rw [resolveS.eq_def]; exact EnvKeeps.err
  | .mkUnop op arg => rw [resolveS.eq_def]; exact EnvKeeps.err
  | .mkIncDec op target => rw [resolveS.eq_def]; exact EnvKeeps.err
  | .mkTernary c t el => rw [resolveS.eq_def]; exact EnvKeeps.err
termination_by 4 * e.size + 0
decreasing_by all_goals
  first
  | omega
  | (simp [Typed.WrappedExpr.size] <;> omega)

theorem resolveMBase_keep {ns : List Name} (s : State) (e : WrappedExpr)
    (hf : ∀ n ∈ ns, usesVar e n = false) :
    EnvKeeps ns s (resolveMBase s e) := by
  match e with
  | .var kind ty fld =>
      rw [resolveMBase]
      refine EnvKeeps.bindPure ?_
      intro b _
      keep_tail
  | .field kind ty base fld =>
      rw [resolveMBase]
      refine EnvKeeps.bind (resolveMBase_keep s base (fresh_base hf)) ?_
      intro t a _
      refine EnvKeeps.bindPure ?_
      intro obj _
      keep_tail
  | .index kind ty base index =>
      rw [resolveMBase]
      refine EnvKeeps.bind (resolveMBase_keep s base (fresh_index_base hf)) ?_
      intro t a _
      refine EnvKeeps.bind (evalInt_keep t index (fresh_index_index hf)) ?_
      intro u i _
      refine EnvKeeps.bindPure ?_
      intro obj _
      keep_tail
  | .pushPlace target => rw [resolveMBase.eq_def]; exact EnvKeeps.err
  | .bool b => rw [resolveMBase.eq_def]; exact EnvKeeps.err
  | .intLit ty v => rw [resolveMBase.eq_def]; exact EnvKeeps.err
  | .mkCall kind ty nm args => rw [resolveMBase.eq_def]; exact EnvKeeps.err
  | .mkBinop op l r => rw [resolveMBase.eq_def]; exact EnvKeeps.err
  | .mkUnop op arg => rw [resolveMBase.eq_def]; exact EnvKeeps.err
  | .mkIncDec op target => rw [resolveMBase.eq_def]; exact EnvKeeps.err
  | .mkTernary c t el => rw [resolveMBase.eq_def]; exact EnvKeeps.err
termination_by 4 * e.size + 0
decreasing_by all_goals
  first
  | omega
  | (simp [Typed.WrappedExpr.size] <;> omega)

theorem readM_keep {ns : List Name} (s : State) (e : WrappedExpr)
    (hf : ∀ n ∈ ns, usesVar e n = false) :
    EnvKeeps ns s (readM s e) := by
  match e with
  | .var kind ty fld =>
      rw [readM]
      refine EnvKeeps.bindPure ?_
      intro b _
      keep_tail
  | .field kind ty base fld =>
      rw [readM]
      refine EnvKeeps.bind (resolveMBase_keep s base (fresh_base hf)) ?_
      intro t a _
      refine EnvKeeps.bindPure ?_
      intro obj _
      keep_tail
  | .index kind ty base index =>
      rw [readM]
      refine EnvKeeps.bind (resolveMBase_keep s base (fresh_index_base hf)) ?_
      intro t a _
      refine EnvKeeps.bind (evalInt_keep t index (fresh_index_index hf)) ?_
      intro u i _
      refine EnvKeeps.bindPure ?_
      intro obj _
      keep_tail
  | .pushPlace target => rw [readM.eq_def]; exact EnvKeeps.err
  | .bool b => rw [readM.eq_def]; exact EnvKeeps.err
  | .intLit ty v => rw [readM.eq_def]; exact EnvKeeps.err
  | .mkCall kind ty nm args => rw [readM.eq_def]; exact EnvKeeps.err
  | .mkBinop op l r => rw [readM.eq_def]; exact EnvKeeps.err
  | .mkUnop op arg => rw [readM.eq_def]; exact EnvKeeps.err
  | .mkIncDec op target => rw [readM.eq_def]; exact EnvKeeps.err
  | .mkTernary c t el => rw [readM.eq_def]; exact EnvKeeps.err
termination_by 4 * e.size + 1
decreasing_by all_goals
  first
  | omega
  | (simp [Typed.WrappedExpr.size] <;> omega)

theorem resolveLoc_keep {ns : List Name} (s : State) (e : WrappedExpr)
    (hf : ∀ n ∈ ns, usesVar e n = false) :
    EnvKeeps ns s (resolveLoc s e) := by
  match e with
  | .var kind ty fld =>
      cases kind with
      | stack => rw [resolveLoc]; exact EnvKeeps.ok
      | memory => rw [resolveLoc]; exact EnvKeeps.ok
      | storage =>
          rw [resolveLoc]
          by_cases ho : fld.origin = some StorageOrigin.global
          · rw [if_pos ho]; exact EnvKeeps.ok
          · rw [if_neg ho]; exact EnvKeeps.ok
  | .field kind ty base fld =>
      cases kind with
      | storage =>
          rw [resolveLoc]
          refine EnvKeeps.bind
            (resolveS_keep s (WrappedExpr.field Kind.storage Ty.uint base fld)
              (by intro n hn; simpa [usesVar] using fresh_base hf n hn)) ?_
          intro t a _
          exact EnvKeeps.ok
      | memory =>
          rw [resolveLoc]
          refine EnvKeeps.bind (resolveMBase_keep s base (fresh_base hf)) ?_
          intro t a _
          exact EnvKeeps.ok
      | stack =>
          rw [resolveLoc]
          · exact EnvKeeps.err
          all_goals simp
  | .index kind ty base index =>
      cases kind with
      | storage =>
          rw [resolveLoc]
          refine EnvKeeps.bind (resolveS_keep s base (fresh_index_base hf)) ?_
          intro t a _
          refine EnvKeeps.bind (evalInt_keep t index (fresh_index_index hf)) ?_
          intro u i _
          exact EnvKeeps.ok
      | memory =>
          rw [resolveLoc]
          refine EnvKeeps.bind (resolveMBase_keep s base (fresh_index_base hf)) ?_
          intro t a _
          refine EnvKeeps.bind (evalInt_keep t index (fresh_index_index hf)) ?_
          intro u i _
          exact EnvKeeps.ok
      | stack =>
          rw [resolveLoc]
          · exact EnvKeeps.err
          all_goals simp
  | .pushPlace target =>
      rw [resolveLoc]
      refine EnvKeeps.bind
        (resolveS_keep s (WrappedExpr.pushPlace target) hf) ?_
      intro t a _
      exact EnvKeeps.ok
  | .bool b => rw [resolveLoc.eq_def]; exact EnvKeeps.err
  | .intLit ty v => rw [resolveLoc.eq_def]; exact EnvKeeps.err
  | .mkCall kind ty nm args => rw [resolveLoc.eq_def]; exact EnvKeeps.err
  | .mkBinop op l r => rw [resolveLoc.eq_def]; exact EnvKeeps.err
  | .mkUnop op arg => rw [resolveLoc.eq_def]; exact EnvKeeps.err
  | .mkIncDec op target => rw [resolveLoc.eq_def]; exact EnvKeeps.err
  | .mkTernary c t el => rw [resolveLoc.eq_def]; exact EnvKeeps.err
termination_by 4 * e.size + 1
decreasing_by all_goals
  first
  | omega
  | (simp [Typed.WrappedExpr.size] <;> omega)

theorem evalValue_keep {ns : List Name} (s : State) (e : WrappedExpr)
    (hf : ∀ n ∈ ns, usesVar e n = false) :
    EnvKeeps ns s (evalValue s e) := by
  match e with
  | .bool b => rw [evalValue]; exact EnvKeeps.ok
  | .intLit ty v => rw [evalValue]; exact EnvKeeps.ok
  | .var kind ty fld =>
      cases kind with
      | stack =>
          rw [evalValue]
          refine EnvKeeps.bindPure ?_
          intro b _
          keep_tail
      | storage =>
          rw [evalValue]
          refine EnvKeeps.bind (resolveS_keep s _ hf) ?_
          intro t a _
          refine EnvKeeps.bindPure ?_
          intro v _
          refine EnvKeeps.bindPure ?_
          intro w _
          exact EnvKeeps.ok
      | memory =>
          rw [evalValue]
          · exact EnvKeeps.err
          all_goals simp
  | .field kind ty base fld =>
      cases kind with
      | storage =>
          rw [evalValue]
          refine EnvKeeps.bind (resolveS_keep s _ hf) ?_
          intro t a _
          refine EnvKeeps.bindPure ?_
          intro v _
          refine EnvKeeps.bindPure ?_
          intro w _
          exact EnvKeeps.ok
      | memory =>
          rw [evalValue]
          refine EnvKeeps.bind (readM_keep s _ hf) ?_
          intro t a _
          refine EnvKeeps.bindPure ?_
          intro w _
          exact EnvKeeps.ok
      | stack =>
          rw [evalValue]
          · exact EnvKeeps.err
          all_goals simp
  | .index kind ty base index =>
      cases kind with
      | storage =>
          rw [evalValue]
          refine EnvKeeps.bind (resolveS_keep s _ hf) ?_
          intro t a _
          refine EnvKeeps.bindPure ?_
          intro v _
          refine EnvKeeps.bindPure ?_
          intro w _
          exact EnvKeeps.ok
      | memory =>
          rw [evalValue]
          refine EnvKeeps.bind (readM_keep s _ hf) ?_
          intro t a _
          refine EnvKeeps.bindPure ?_
          intro w _
          exact EnvKeeps.ok
      | stack =>
          rw [evalValue]
          · exact EnvKeeps.err
          all_goals simp
  | .mkBinop op l r =>
      have hfl : ∀ n ∈ ns, usesVar l n = false := fun n hn => by
        have := hf n hn; simp [usesVar] at this; exact this.1
      have hfr : ∀ n ∈ ns, usesVar r n = false := fun n hn => by
        have := hf n hn; simp [usesVar] at this; exact this.2
      rw [evalValue]
      refine EnvKeeps.bind (evalValue_keep s l hfl) ?_
      intro t lv _
      simp only []
      split
      all_goals
        first
          | exact EnvKeeps.ok
          | (refine EnvKeeps.bind (evalValue_keep t r hfr) ?_
             intro u rv _
             keep_tail)
          | keep_tail
  | .mkUnop op arg =>
      have hfa : ∀ n ∈ ns, usesVar arg n = false := fun n hn => by
        have := hf n hn; simpa [usesVar] using this
      rw [evalValue]
      refine EnvKeeps.bind (evalValue_keep s arg hfa) ?_
      intro t v _
      keep_tail
  | .mkIncDec op target =>
      have hft : ∀ n ∈ ns, usesVar target n = false := fun n hn => by
        have := hf n hn; simpa [usesVar] using this
      rw [evalValue]
      refine EnvKeeps.bind (resolveLoc_keep s target hft) ?_
      intro t loc hloc
      have hfresh : LocFresh ns loc := resolveLoc_fresh hft hloc
      refine EnvKeeps.bindPure ?_
      intro old _
      refine EnvKeeps.bindPure ?_
      intro oldInt _
      refine EnvKeeps.bindPure ?_
      intro newVal _
      refine EnvKeeps.bindS (writeLoc_keepS hfresh) ?_
      intro u _
      exact EnvKeeps.ok
  | .mkTernary c t el =>
      have hfc : ∀ n ∈ ns, usesVar c n = false := fun n hn => by
        have := hf n hn; simp [usesVar] at this; exact this.1.1
      have hft : ∀ n ∈ ns, usesVar t n = false := fun n hn => by
        have := hf n hn; simp [usesVar] at this; exact this.1.2
      have hfe : ∀ n ∈ ns, usesVar el n = false := fun n hn => by
        have := hf n hn; simp [usesVar] at this; exact this.2
      rw [evalValue]
      refine EnvKeeps.bind (evalValue_keep s c hfc) ?_
      intro u cv _
      cases cv with
      | int v => exact EnvKeeps.err
      | bool b =>
          cases b with
          | true => exact evalValue_keep u t hft
          | false => exact evalValue_keep u el hfe
  | .mkCall kind ty nm args =>
      by_cases hnm : nm = "net"
      · subst hnm
        match hargs : args with
        | [addr] =>
            have hszl : Typed.WrappedExpr.sizeList args = addr.size := by
              rw [hargs]; simp [Typed.WrappedExpr.sizeList]
            have hfa : ∀ n ∈ ns, usesVar addr n = false := fun n hn => by
              have := hf n hn
              simp [usesVar, usesVarList] at this
              exact this
            rw [evalValue]
            refine EnvKeeps.bind (evalInt_keep s addr hfa) ?_
            intro t a _
            exact EnvKeeps.ok
        | [] =>
            rw [evalValue]
            · exact EnvKeeps.err
            all_goals simp
        | a :: b :: rest =>
            rw [evalValue]
            · exact EnvKeeps.err
            all_goals simp
      · rw [evalValue]
        · exact EnvKeeps.err
        all_goals simp [hnm]
  | .pushPlace target => rw [evalValue.eq_def]; exact EnvKeeps.err
termination_by 4 * e.size + 2
decreasing_by all_goals
  subst_vars
  first
  | omega
  | (simp [Typed.WrappedExpr.size, Typed.WrappedExpr.sizeList] <;> omega)

theorem evalInt_keep {ns : List Name} (s : State) (e : WrappedExpr)
    (hf : ∀ n ∈ ns, usesVar e n = false) :
    EnvKeeps ns s (evalInt s e) := by
  rw [evalInt]
  refine EnvKeeps.bind (evalValue_keep s e hf) ?_
  intro t v _
  refine EnvKeeps.bindPure ?_
  intro i _
  exact EnvKeeps.ok
termination_by 4 * e.size + 3
decreasing_by all_goals omega

end

/-! ## Statement-level freshness -/

def optUsesVar : Option WrappedExpr -> Name -> Bool
  | none, _ => false
  | some e, n => usesVar e n

mutual
/-- `stmtUsesVar stmt n`: the variable `n` occurs in `stmt` — as a
declared name or inside any embedded expression. Conservative: a block
that re-reads a name it declared itself also counts as using it. -/
def stmtUsesVar : Stmt -> Name -> Bool
  | .expr e, n => usesVar e n
  | .assign lhs rhs, n => usesVar lhs.expr n || usesVar rhs n
  | .storageDecl _ name init, n => name = n || optUsesVar init n
  | .storagePlaceAlias _ name init, n => name = n || usesVar init n
  | .memoryDecl _ name init, n => name = n || optUsesVar init n
  | .stackDecl _ name init, n => name = n || optUsesVar init n
  | .delete target, n => usesVar target.expr n
  | .push target value, n => usesVar target.expr n || optUsesVar value n
  | .pushAssign target value, n =>
      usesVar target.expr n || usesVar value n
  | .pushFieldAssign target _ value, n =>
      usesVar target.expr n || usesVar value n
  | .pop target, n => usesVar target.expr n
  | .revert msg, n => optUsesVar msg n
  | .compoundAssign _ lhs rhs, n =>
      usesVar lhs.expr n || usesVar rhs n
  | .ite cond thn els, n =>
      usesVar cond n || blockUsesVar thn n || blockUsesVar els n
  | .assertStmt cond, n => usesVar cond n
  | .requireStmt cond, n => usesVar cond n
  | .transfer recipient amount, n =>
      usesVar recipient n || usesVar amount n
  | .callStmt res _ args, n =>
      (res.elim false fun p => usesVar p.expr n) ||
        args.any fun a => usesVar a n

def blockUsesVar : List Stmt -> Name -> Bool
  | [], _ => false
  | stmt :: rest, n => stmtUsesVar stmt n || blockUsesVar rest n
end

/-! ## Statement-level congruence -/

/-- The memory-slot write local to the interpreter's `delete` case
(`writeM`), as a standalone function (definitionally equal to the
interpreter's local closure). -/
def writeMSlot (s : State) (loc : Loc) (mv : MVal) : Res State :=
  match loc with
  | Loc.memoryField id fld =>
      (s.getObj id).bind fun obj =>
        match obj with
        | MObj.struct fields =>
            .ok (s.setObj id (MObj.struct (setBy fld mv fields)))
        | MObj.array _ => .error .stuck
  | Loc.memoryIndex id i =>
      (s.getObj id).bind fun obj =>
        match obj with
        | MObj.array elems =>
            if 0 ≤ i ∧ i.toNat < elems.length then
              .ok (s.setObj id (MObj.array (elems.set i.toNat mv)))
            else .error .revert
        | MObj.struct _ => .error .stuck
  | Loc.stack _ => .error .stuck
  | Loc.storage _ _ => .error .stuck
  | Loc.storageLocal _ => .error .stuck
  | Loc.memoryRoot _ => .error .stuck

theorem writeMSlot_agree {ns : List Name} {w₁ w₂ : State}
    (hw : EnvAgreeExcept ns w₁ w₂) (loc : Loc) (mv : MVal) :
    ResultsAgree ns (writeMSlot w₁ loc mv) (writeMSlot w₂ loc mv) := by
  unfold writeMSlot
  cases loc with
  | memoryField id fld =>
      simp only [getObj_congr hw]
      refine bindPureResults_agree _ fun obj => ?_
      cases obj with
      | array elems => exact rfl
      | struct fields => exact setObj_agree hw id _
  | memoryIndex id i =>
      simp only [getObj_congr hw]
      refine bindPureResults_agree _ fun obj => ?_
      cases obj with
      | struct fields => exact rfl
      | array elems =>
          by_cases hb : 0 ≤ i ∧ i.toNat < elems.length
          · simp only [if_pos hb]
            exact setObj_agree hw id _
          · simp only [if_neg hb]
            exact rfl
  | stack name => exact rfl
  | storageLocal name => exact rfl
  | memoryRoot name => exact rfl
  | storage root segs => exact rfl

/-- Congruence for the storage-target right-hand-side reading. -/
theorem rhsToSVal_agree {ns : List Name} {s₁ s₂ : State}
    (h : EnvAgreeExcept ns s₁ s₂) (rhs : WrappedExpr)
    (hf : ∀ n ∈ ns, usesVar rhs n = false) :
    ResAgree ns (rhsToSVal s₁ rhs) (rhsToSVal s₂ rhs) := by
  rw [rhsToSVal, rhsToSVal]
  cases hp : rhs.ty.isPrimitive with
  | true =>
      refine ResAgree.bind (evalValue_agree h rhs hf) ?_
      intro t₁ t₂ v ht
      exact ⟨rfl, ht⟩
  | false =>
      match hk : rhs.kind with
      | Kind.storage =>
          cases hm : tyHasMapping rhs.ty with
          | true => exact rfl
          | false =>
              refine ResAgree.bind (resolveS_agree h rhs hf) ?_
              intro t₁ t₂ a ht
              obtain ⟨rroot, rsegs⟩ := a
              simp only [findStorage_congr ht]
              exact bindPureRes_agree _ fun v => ⟨rfl, ht⟩
      | Kind.memory =>
          refine ResAgree.bind (readM_agree h rhs hf) ?_
          intro t₁ t₂ mv ht
          simp only [copyMem_congr ht]
          exact bindPureRes_agree _ fun sval => ⟨rfl, ht⟩
      | Kind.stack => exact rfl

/-- Congruence for the memory-target right-hand-side reading. -/
theorem rhsToMVal_agree {ns : List Name} {s₁ s₂ : State}
    (h : EnvAgreeExcept ns s₁ s₂) (rhs : WrappedExpr)
    (hf : ∀ n ∈ ns, usesVar rhs n = false) :
    ResAgree ns (rhsToMVal s₁ rhs) (rhsToMVal s₂ rhs) := by
  rw [rhsToMVal, rhsToMVal]
  cases hp : rhs.ty.isPrimitive with
  | true =>
      refine ResAgree.bind (evalValue_agree h rhs hf) ?_
      intro t₁ t₂ v ht
      exact ⟨rfl, ht⟩
  | false =>
      match hk : rhs.kind with
      | Kind.memory => exact readM_agree h rhs hf
      | Kind.storage =>
          refine ResAgree.bind (resolveS_agree h rhs hf) ?_
          intro t₁ t₂ a ht
          obtain ⟨rroot, rsegs⟩ := a
          simp only [findStorage_congr ht]
          refine bindPureRes_agree _ fun sval => ?_
          exact copyStToM_agree ht sval
      | Kind.stack => exact rfl

/-- Congruence for nested-target assignment. -/
theorem execAssignNested_agree {ns : List Name} {s₁ s₂ : State}
    (h : EnvAgreeExcept ns s₁ s₂) (e rhs : WrappedExpr)
    (hfl : ∀ n ∈ ns, usesVar e n = false)
    (hfr : ∀ n ∈ ns, usesVar rhs n = false) :
    ResultsAgree ns (execAssignNested s₁ e rhs)
      (execAssignNested s₂ e rhs) := by
  rw [execAssignNested, execAssignNested]
  cases hk : e.kind with
  | storage =>
      refine ResAgree.bindState (rhsToSVal_agree h rhs hfr) ?_
      intro u₁ u₂ sv hu
      refine ResAgree.bindState (resolveLoc_agree hu e hfl) ?_
      intro w₁ w₂ loc hw
      cases loc with
      | storage root segs => exact saveStorage_agree hw root segs sv
      | stack n => exact rfl
      | storageLocal n => exact rfl
      | memoryRoot n => exact rfl
      | memoryField id fld => exact rfl
      | memoryIndex id i => exact rfl
  | memory =>
      refine ResAgree.bindState (rhsToMVal_agree h rhs hfr) ?_
      intro u₁ u₂ mv hu
      refine ResAgree.bindState (resolveLoc_agree hu e hfl) ?_
      intro w₁ w₂ loc hw
      cases loc with
      | memoryField id fld =>
          simp only [getObj_congr hw]
          refine bindPureResults_agree _ fun obj => ?_
          cases obj with
          | array elems => exact rfl
          | struct fields => exact setObj_agree hw id _
      | memoryIndex id i =>
          simp only [getObj_congr hw]
          refine bindPureResults_agree _ fun obj => ?_
          cases obj with
          | struct fields => exact rfl
          | array elems =>
              by_cases hb : 0 ≤ i ∧ i.toNat < elems.length
              · simp only [if_pos hb]
                exact setObj_agree hw id _
              · simp only [if_neg hb]
                exact rfl
      | stack n => exact rfl
      | storageLocal n => exact rfl
      | memoryRoot n => exact rfl
      | storage root segs => exact rfl
  | stack => exact rfl

theorem execAssign_agree {ns : List Name} {s₁ s₂ : State}
    (h : EnvAgreeExcept ns s₁ s₂) (lhs : PlaceExpr) (rhs : WrappedExpr)
    (hfl : ∀ n ∈ ns, usesVar lhs.expr n = false)
    (hfr : ∀ n ∈ ns, usesVar rhs n = false) :
    ResultsAgree ns (execAssign s₁ lhs rhs) (execAssign s₂ lhs rhs) := by
  rw [execAssign, execAssign]
  match hlhs : lhs.expr with
  | .var kind ty fld =>
      cases kind with
      | stack =>
          refine ResAgree.bindState (evalValue_agree h rhs hfr) ?_
          intro u₁ u₂ v hu
          exact hu.setEnv_both fld.name (Binding.val v)
      | storage =>
          by_cases ho : fld.origin = some StorageOrigin.global
          · simp only [if_pos ho]
            refine ResAgree.bindState (rhsToSVal_agree h rhs hfr) ?_
            intro u₁ u₂ sv hu
            exact saveStorage_agree hu fld.name [] sv
          · simp only [if_neg ho]
            refine ResAgree.bindState (resolveS_agree h rhs hfr) ?_
            intro u₁ u₂ a hu
            obtain ⟨root, segs⟩ := a
            exact hu.setEnv_both fld.name (Binding.spath root segs)
      | memory =>
          match hk : rhs.kind with
          | Kind.memory =>
              refine ResAgree.bindState (readM_agree h rhs hfr) ?_
              intro u₁ u₂ mv hu
              cases mv with
              | ref id => exact hu.setEnv_both fld.name (Binding.mref id)
              | prim p => cases p <;> exact rfl
          | Kind.storage =>
              refine ResAgree.bindState (resolveS_agree h rhs hfr) ?_
              intro u₁ u₂ a hu
              obtain ⟨root, segs⟩ := a
              simp only [findStorage_congr hu]
              refine bindPureResults_agree _ fun sval => ?_
              refine ResAgree.bindState (copyStToM_agree hu sval) ?_
              intro w₁ w₂ mv hw
              cases mv with
              | ref id => exact hw.setEnv_both fld.name (Binding.mref id)
              | prim p => cases p <;> exact rfl
          | Kind.stack => exact rfl
  | .field kind ty base fld =>
      exact execAssignNested_agree h _ rhs
        (fun n hn => by have := hfl n hn; rw [hlhs] at this; exact this) hfr
  | .index kind ty base index =>
      exact execAssignNested_agree h _ rhs
        (fun n hn => by have := hfl n hn; rw [hlhs] at this; exact this) hfr
  | .pushPlace target =>
      exact execAssignNested_agree h _ rhs
        (fun n hn => by have := hfl n hn; rw [hlhs] at this; exact this) hfr
  | .bool b =>
      exact execAssignNested_agree h _ rhs (fun n hn => rfl) hfr
  | .intLit ty v =>
      exact execAssignNested_agree h _ rhs (fun n hn => rfl) hfr
  | .mkCall kind ty nm args =>
      exact execAssignNested_agree h _ rhs
        (fun n hn => by have := hfl n hn; rw [hlhs] at this; exact this) hfr
  | .mkBinop op l r =>
      exact execAssignNested_agree h _ rhs
        (fun n hn => by have := hfl n hn; rw [hlhs] at this; exact this) hfr
  | .mkUnop op arg =>
      exact execAssignNested_agree h _ rhs
        (fun n hn => by have := hfl n hn; rw [hlhs] at this; exact this) hfr
  | .mkIncDec op target =>
      exact execAssignNested_agree h _ rhs
        (fun n hn => by have := hfl n hn; rw [hlhs] at this; exact this) hfr
  | .mkTernary c t el =>
      exact execAssignNested_agree h _ rhs
        (fun n hn => by have := hfl n hn; rw [hlhs] at this; exact this) hfr

/-- Agreement for the interpreter's memory-`delete` general branch:
resolve the place, then reset the addressed slot to the type default. -/
theorem deleteMemSlot_agree {ns : List Name} {s₁ s₂ : State}
    (h : EnvAgreeExcept ns s₁ s₂) (e' : WrappedExpr)
    (hf : ∀ n ∈ ns, usesVar e' n = false) :
    ResultsAgree ns
      ((resolveLoc s₁ e').bind fun x =>
        match e'.ty with
        | Ty.bool => writeMSlot x.1 x.2 (MVal.bool false)
        | Ty.uint => writeMSlot x.1 x.2 (MVal.int 0)
        | Ty.int => writeMSlot x.1 x.2 (MVal.int 0)
        | Ty.ref ref =>
            (allocDefault x.1 ref).bind fun y =>
              writeMSlot y.1 x.2 (MVal.ref y.2))
      ((resolveLoc s₂ e').bind fun x =>
        match e'.ty with
        | Ty.bool => writeMSlot x.1 x.2 (MVal.bool false)
        | Ty.uint => writeMSlot x.1 x.2 (MVal.int 0)
        | Ty.int => writeMSlot x.1 x.2 (MVal.int 0)
        | Ty.ref ref =>
            (allocDefault x.1 ref).bind fun y =>
              writeMSlot y.1 x.2 (MVal.ref y.2)) := by
  refine ResAgree.bindState (resolveLoc_agree h e' hf) ?_
  intro t₁ t₂ loc ht
  match e'.ty with
  | Ty.bool => exact writeMSlot_agree ht loc (MVal.bool false)
  | Ty.uint => exact writeMSlot_agree ht loc (MVal.int 0)
  | Ty.int => exact writeMSlot_agree ht loc (MVal.int 0)
  | Ty.ref ref =>
      refine ResAgree.bindState (allocDefault_agree ht ref) ?_
      intro u₁ u₂ id hu
      exact writeMSlot_agree hu loc (MVal.ref id)

mutual

theorem execStmt_agree {ns : List Name} {s₁ s₂ : State}
    (h : EnvAgreeExcept ns s₁ s₂) (stmt : Stmt)
    (hf : ∀ n ∈ ns, stmtUsesVar stmt n = false) :
    ResultsAgree ns (execStmt s₁ stmt) (execStmt s₂ stmt) := by
  match stmt with
  | .expr e =>
      have hfe : ∀ n ∈ ns, usesVar e n = false := fun n hn => by
        have := hf n hn
        simpa [stmtUsesVar] using this
      rw [execStmt, execStmt]
      refine ResAgree.bindState (evalValue_agree h e hfe) ?_
      intro t₁ t₂ v ht
      exact ht
  | .assign lhs rhs =>
      have hfl : ∀ n ∈ ns, usesVar lhs.expr n = false := fun n hn => by
        have := hf n hn
        simp [stmtUsesVar] at this
        exact this.1
      have hfr : ∀ n ∈ ns, usesVar rhs n = false := fun n hn => by
        have := hf n hn
        simp [stmtUsesVar] at this
        exact this.2
      rw [execStmt, execStmt]
      exact execAssign_agree h lhs rhs hfl hfr
  | .storageDecl ty name init =>
      match init with
      | none =>
          rw [execStmt, execStmt]
          exact h
      | some rhs =>
          have hfr : ∀ n ∈ ns, usesVar rhs n = false := fun n hn => by
            have := hf n hn
            simp [stmtUsesVar, optUsesVar] at this
            exact this.2
          rw [execStmt, execStmt]
          refine ResAgree.bindState (resolveS_agree h rhs hfr) ?_
          intro t₁ t₂ a ht
          obtain ⟨root, segs⟩ := a
          exact ht.setEnv_both name (Binding.spath root segs)
  | .storagePlaceAlias ty name init =>
      have hfi : ∀ n ∈ ns, usesVar init n = false := fun n hn => by
        have := hf n hn
        simp [stmtUsesVar] at this
        exact this.2
      rw [execStmt, execStmt]
      refine ResAgree.bindState (resolveS_agree h init hfi) ?_
      intro t₁ t₂ a ht
      obtain ⟨root, segs⟩ := a
      exact ht.setEnv_both name (Binding.spath root segs)
  | .memoryDecl ty name init =>
      match init with
      | none =>
          match ty with
          | Ty.ref ref =>
              rw [execStmt, execStmt]
              refine ResAgree.bindState (allocDefault_agree h ref) ?_
              intro t₁ t₂ id ht
              exact ht.setEnv_both name (Binding.mref id)
          | Ty.bool =>
              rw [execStmt, execStmt]
              · exact rfl
              all_goals nofun
          | Ty.uint =>
              rw [execStmt, execStmt]
              · exact rfl
              all_goals nofun
          | Ty.int =>
              rw [execStmt, execStmt]
              · exact rfl
              all_goals nofun
      | some rhs =>
          have hfr : ∀ n ∈ ns, usesVar rhs n = false := fun n hn => by
            have := hf n hn
            simp [stmtUsesVar, optUsesVar] at this
            exact this.2
          rw [execStmt, execStmt]
          match hk : rhs.kind with
          | Kind.memory =>
              refine ResAgree.bindState (readM_agree h rhs hfr) ?_
              intro t₁ t₂ mv ht
              cases mv with
              | ref id => exact ht.setEnv_both name (Binding.mref id)
              | prim p => cases p <;> exact rfl
          | Kind.storage =>
              refine ResAgree.bindState (resolveS_agree h rhs hfr) ?_
              intro t₁ t₂ a ht
              obtain ⟨root, segs⟩ := a
              simp only [findStorage_congr ht]
              refine bindPureResults_agree _ fun sval => ?_
              refine ResAgree.bindState (copyStToM_agree ht sval) ?_
              intro w₁ w₂ mv hw
              cases mv with
              | ref id => exact hw.setEnv_both name (Binding.mref id)
              | prim p => cases p <;> exact rfl
          | Kind.stack => exact rfl
  | .stackDecl ty name init =>
      match init with
      | none =>
          match ty with
          | Ty.bool =>
              rw [execStmt, execStmt]
              exact h.setEnv_both name (Binding.val (Value.bool false))
          | Ty.uint =>
              rw [execStmt, execStmt]
              · exact h.setEnv_both name (Binding.val (Value.int 0))
              all_goals nofun
          | Ty.int =>
              rw [execStmt, execStmt]
              · exact h.setEnv_both name (Binding.val (Value.int 0))
              all_goals nofun
          | Ty.ref ref =>
              rw [execStmt, execStmt]
              · exact h.setEnv_both name (Binding.val (Value.int 0))
              all_goals nofun
      | some rhs =>
          have hfr : ∀ n ∈ ns, usesVar rhs n = false := fun n hn => by
            have := hf n hn
            simp [stmtUsesVar, optUsesVar] at this
            exact this.2
          rw [execStmt, execStmt]
          refine ResAgree.bindState (evalValue_agree h rhs hfr) ?_
          intro t₁ t₂ v ht
          exact ht.setEnv_both name (Binding.val v)
  | .delete target =>
      have hft : ∀ n ∈ ns, usesVar target.expr n = false := fun n hn => by
        have := hf n hn
        simpa [stmtUsesVar] using this
      rw [execStmt, execStmt]
      match hk : target.expr.kind with
      | Kind.storage =>
          refine ResAgree.bindState (resolveS_agree h target.expr hft) ?_
          intro t₁ t₂ a ht
          obtain ⟨root, segs⟩ := a
          simp only [findStorage_congr ht]
          refine bindPureResults_agree _ fun cur => ?_
          exact saveStorage_agree ht root segs cur.defaultOf
      | Kind.memory =>
          cases htgt : target.expr with
          | var k ty fld =>
              rw [htgt] at hft
              match ty with
              | Ty.ref ref =>
                  refine ResAgree.bindState (allocDefault_agree h ref) ?_
                  intro t₁ t₂ id ht
                  exact ht.setEnv_both fld.name (Binding.mref id)
              | Ty.bool => exact rfl
              | Ty.uint => exact rfl
              | Ty.int => exact rfl
          | field k ty base fld =>
              rw [htgt] at hft
              exact deleteMemSlot_agree h _ hft
          | index k ty base index =>
              rw [htgt] at hft
              exact deleteMemSlot_agree h _ hft
          | pushPlace t =>
              rw [htgt] at hft
              exact deleteMemSlot_agree h _ hft
          | bool b => exact deleteMemSlot_agree h _ (by intro n hn; simp [usesVar])
          | intLit ty v => exact deleteMemSlot_agree h _ (by intro n hn; simp [usesVar])
          | mkCall k ty nm args =>
              rw [htgt] at hft
              exact deleteMemSlot_agree h _ hft
          | mkBinop op l r =>
              rw [htgt] at hft
              exact deleteMemSlot_agree h _ hft
          | mkUnop op arg =>
              rw [htgt] at hft
              exact deleteMemSlot_agree h _ hft
          | mkIncDec op t =>
              rw [htgt] at hft
              exact deleteMemSlot_agree h _ hft
          | mkTernary c t el =>
              rw [htgt] at hft
              exact deleteMemSlot_agree h _ hft
      | Kind.stack => exact rfl
  | .push target value =>
      have hft : ∀ n ∈ ns, usesVar target.expr n = false := fun n hn => by
        have := hf n hn
        simp [stmtUsesVar] at this
        exact this.1
      rw [execStmt, execStmt]
      refine ResAgree.bindState (resolveS_agree h target.expr hft) ?_
      intro t₁ t₂ a ht
      obtain ⟨root, segs⟩ := a
      simp only [findStorage_congr ht]
      refine bindPureResults_agree _ fun arr => ?_
      cases arr with
      | array elems =>
          match hty : target.expr.ty with
          | Ty.ref (RefTy.array elemTy) =>
              match value with
              | none => exact saveStorage_agree ht root segs _
              | some rhs =>
                  have hfr : ∀ n ∈ ns, usesVar rhs n = false := fun n hn => by
                    have := hf n hn
                    simp [stmtUsesVar, optUsesVar] at this
                    exact this.2
                  refine ResAgree.bindState (rhsToSVal_agree ht rhs hfr) ?_
                  intro u₁ u₂ sv hu
                  exact saveStorage_agree hu root segs _
          | Ty.bool => exact rfl
          | Ty.uint => exact rfl
          | Ty.int => exact rfl
          | Ty.ref (RefTy.struct nm) => exact rfl
          | Ty.ref (RefTy.mapping k v) => exact rfl
      | prim p => cases p <;> exact rfl
      | struct fields => exact rfl
      | map entries dflt => exact rfl
  | .pushAssign target value =>
      have hfl : ∀ n ∈ ns, usesVar target.expr n = false := fun n hn => by
        have := hf n hn
        simp [stmtUsesVar] at this
        exact this.1
      have hfr : ∀ n ∈ ns, usesVar value n = false := fun n hn => by
        have := hf n hn
        simp [stmtUsesVar] at this
        exact this.2
      rw [execStmt, execStmt]
      exact execAssign_agree h (PlaceExpr.pushPlace target) value
        (fun n hn => by simpa [usesVar] using hfl n hn) hfr
  | .pushFieldAssign target fld value =>
      have hfl : ∀ n ∈ ns, usesVar target.expr n = false := fun n hn => by
        have := hf n hn
        simp [stmtUsesVar] at this
        exact this.1
      have hfr : ∀ n ∈ ns, usesVar value n = false := fun n hn => by
        have := hf n hn
        simp [stmtUsesVar] at this
        exact this.2
      rw [execStmt, execStmt]
      refine execAssign_agree h _ value ?_ hfr
      intro n hn
      simpa [usesVar] using hfl n hn
  | .pop target =>
      have hft : ∀ n ∈ ns, usesVar target.expr n = false := fun n hn => by
        have := hf n hn
        simpa [stmtUsesVar] using this
      rw [execStmt, execStmt]
      refine ResAgree.bindState (resolveS_agree h target.expr hft) ?_
      intro t₁ t₂ a ht
      obtain ⟨root, segs⟩ := a
      simp only [findStorage_congr ht]
      refine bindPureResults_agree _ fun arr => ?_
      cases arr with
      | array elems =>
          simp only []
          cases elems.reverse with
          | nil => exact rfl
          | cons hd restRev => exact saveStorage_agree ht root segs _
      | prim p => cases p <;> exact rfl
      | struct fields => exact rfl
      | map entries dflt => exact rfl
  | .revert msg =>
      rw [execStmt, execStmt]
      exact rfl
  | .compoundAssign op lhs rhs =>
      have hfl : ∀ n ∈ ns, usesVar lhs.expr n = false := fun n hn => by
        have := hf n hn
        simp [stmtUsesVar] at this
        exact this.1
      have hfr : ∀ n ∈ ns, usesVar rhs n = false := fun n hn => by
        have := hf n hn
        simp [stmtUsesVar] at this
        exact this.2
      rw [execStmt, execStmt]
      refine ResAgree.bindState (evalValue_agree h rhs hfr) ?_
      intro t₁ t₂ v ht
      refine ResAgree.bindStateWith (resolveLoc_agree ht lhs.expr hfl) ?_
      intro u₁ u₂ loc h₁ _ hu
      have hfresh : LocFresh ns loc := resolveLoc_fresh hfl h₁
      show ResultsAgree ns
        ((readLoc u₁ loc) >>= fun old =>
          (applyBinOp op old v) >>= fun new =>
            (checkArith lhs.expr.ty new) >>= fun new' =>
              writeLoc u₁ loc new')
        ((readLoc u₂ loc) >>= fun old =>
          (applyBinOp op old v) >>= fun new =>
            (checkArith lhs.expr.ty new) >>= fun new' =>
              writeLoc u₂ loc new')
      rw [readLoc_congr hu hfresh]
      refine bindPureResults_agree _ fun old => ?_
      refine bindPureResults_agree _ fun new => ?_
      refine bindPureResults_agree _ fun new' => ?_
      exact writeLoc_agree hu new'
  | .ite cond thn els =>
      have hfc : ∀ n ∈ ns, usesVar cond n = false := fun n hn => by
        have := hf n hn
        simp [stmtUsesVar] at this
        exact this.1.1
      have hfthn : ∀ n ∈ ns, blockUsesVar thn n = false := fun n hn => by
        have := hf n hn
        simp [stmtUsesVar] at this
        exact this.1.2
      have hfels : ∀ n ∈ ns, blockUsesVar els n = false := fun n hn => by
        have := hf n hn
        simp [stmtUsesVar] at this
        exact this.2
      rw [execStmt, execStmt]
      refine ResAgree.bindState (evalValue_agree h cond hfc) ?_
      intro t₁ t₂ c ht
      cases c with
      | int v => exact rfl
      | bool b =>
          cases b with
          | true => exact execBlock_agree ht thn hfthn
          | false => exact execBlock_agree ht els hfels
  | .assertStmt cond =>
      have hfc : ∀ n ∈ ns, usesVar cond n = false := fun n hn => by
        have := hf n hn
        simpa [stmtUsesVar] using this
      rw [execStmt, execStmt]
      refine ResAgree.bindState (evalValue_agree h cond hfc) ?_
      intro t₁ t₂ c ht
      cases c with
      | int v => exact rfl
      | bool b => cases b with
          | true => exact ht
          | false => exact rfl
  | .requireStmt cond =>
      have hfc : ∀ n ∈ ns, usesVar cond n = false := fun n hn => by
        have := hf n hn
        simpa [stmtUsesVar] using this
      rw [execStmt, execStmt]
      refine ResAgree.bindState (evalValue_agree h cond hfc) ?_
      intro t₁ t₂ c ht
      cases c with
      | int v => exact rfl
      | bool b => cases b with
          | true => exact ht
          | false => exact rfl
  | .callStmt res fn args =>
      rw [execStmt, execStmt]
      exact rfl
  | .transfer recipient amount =>
      have hfr : ∀ n ∈ ns, usesVar recipient n = false := fun n hn => by
        have := hf n hn
        simp [stmtUsesVar] at this
        exact this.1
      have hfa : ∀ n ∈ ns, usesVar amount n = false := fun n hn => by
        have := hf n hn
        simp [stmtUsesVar] at this
        exact this.2
      rw [execStmt, execStmt]
      refine ResAgree.bindState (evalInt_agree h recipient hfr) ?_
      intro t₁ t₂ addr ht
      refine ResAgree.bindState (evalInt_agree ht amount hfa) ?_
      intro u₁ u₂ amt hu
      by_cases hneg : amt < 0
      · simp only [if_pos hneg]
        exact rfl
      · simp only [if_neg hneg]
        rw [hu.selfBalance]
        by_cases hbal : u₂.selfBalance < amt
        · simp only [if_pos hbal]
          exact rfl
        · simp only [if_neg hbal]
          simp only [getNet_congr hu]
          exact ⟨hu.storage, hu.heap, hu.nextId,
            by simp [State.setNet, hu.net], hu.env, rfl⟩
termination_by sizeOf stmt

theorem execBlock_agree {ns : List Name} {s₁ s₂ : State}
    (h : EnvAgreeExcept ns s₁ s₂) (block : List Stmt)
    (hf : ∀ n ∈ ns, blockUsesVar block n = false) :
    ResultsAgree ns (execBlock s₁ block) (execBlock s₂ block) := by
  match block with
  | [] =>
      rw [execBlock, execBlock]
      exact h
  | stmt :: rest =>
      have hf1 : ∀ n ∈ ns, stmtUsesVar stmt n = false := fun n hn => by
        have := hf n hn
        simp [blockUsesVar] at this
        exact this.1
      have hf2 : ∀ n ∈ ns, blockUsesVar rest n = false := fun n hn => by
        have := hf n hn
        simp [blockUsesVar] at this
        exact this.2
      rw [execBlock, execBlock]
      refine ResultsAgree.bind (execStmt_agree h stmt hf1) ?_
      intro t₁ t₂ ht
      exact execBlock_agree ht rest hf2
termination_by sizeOf block

end

/-! ## Purity: successful evaluation of operator-free expressions
does not change the state

`pureExpr` is conservative: no `push`-lvalues, no `++`/`--`, no calls.
Together with the congruence kit this discharges the evaluation-order
swap in the `*ReadUnfoldRight*`/`*SndResult` rules: the interpreter
resolves the assignment target first, the rule hoists the right-hand
side first, and the two orders agree when both prefixes leave the state
unchanged. -/

def pureExpr : WrappedExpr -> Bool
  | .var .. => true
  | .bool _ => true
  | .intLit _ _ => true
  | .field _ _ base _ => pureExpr base
  | .index _ _ base index => pureExpr base && pureExpr index
  | .mkBinop _ l r => pureExpr l && pureExpr r
  | .mkUnop _ arg => pureExpr arg
  | _ => false

/-- Invert a successful bind. -/
theorem bind_ok_inv {x : Res α} {f : α -> Res β} {b : β}
    (h : (x >>= f) = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => exact nomatch h
  | ok a => exact ⟨a, rfl, h⟩

mutual

theorem resolveS_pure {s t : State} {e : WrappedExpr}
    (hp : pureExpr e = true) {r : Name × List Seg}
    (heq : resolveS s e = .ok (t, r)) : t = s := by
  match e with
  | .var kind ty fld =>
      rw [resolveS] at heq
      split at heq
      · exact (congrArg Prod.fst (Except.ok.inj heq)).symm
      -- one branch per non-path binding (`val`, `mref`), then `none`
      · exact nomatch heq
      · exact nomatch heq
      · split at heq
        · exact (congrArg Prod.fst (Except.ok.inj heq)).symm
        · exact nomatch heq
  | .field kind ty base fld =>
      rw [resolveS] at heq
      obtain ⟨⟨t', a⟩, hx, hf⟩ := bind_ok_inv heq
      cases hf
      exact resolveS_pure (by simpa [pureExpr] using hp) hx
  | .index kind ty base index =>
      rw [resolveS] at heq
      obtain ⟨⟨t₁, a⟩, hx, hf⟩ := bind_ok_inv heq
      obtain ⟨⟨t₂, i⟩, hi, hf2⟩ := bind_ok_inv hf
      cases hf2
      have h1 := resolveS_pure (by simp [pureExpr] at hp; exact hp.1) hx
      have h2 := evalInt_pure (by simp [pureExpr] at hp; exact hp.2) hi
      exact h2.trans h1
  | .bool b =>
      rw [resolveS.eq_def] at heq
      exact nomatch heq
  | .intLit ty v =>
      rw [resolveS.eq_def] at heq
      exact nomatch heq
  | .pushPlace target => exact nomatch hp
  | .mkCall kind ty nm args => exact nomatch hp
  | .mkBinop op l r =>
      rw [resolveS.eq_def] at heq
      exact nomatch heq
  | .mkUnop op arg =>
      rw [resolveS.eq_def] at heq
      exact nomatch heq
  | .mkIncDec op target => exact nomatch hp
  | .mkTernary c t el => exact nomatch hp
termination_by 4 * e.size + 0
decreasing_by all_goals
  first
  | omega
  | (simp [Typed.WrappedExpr.size] <;> omega)

theorem resolveMBase_pure {s t : State} {e : WrappedExpr}
    (hp : pureExpr e = true) {r : Nat}
    (heq : resolveMBase s e = .ok (t, r)) : t = s := by
  match e with
  | .var kind ty fld =>
      rw [resolveMBase] at heq
      obtain ⟨b, hx, hf⟩ := bind_ok_inv heq
      cases b with
      | val v => exact nomatch hf
      | spath root segs => exact nomatch hf
      | mref id =>
          cases hf
          rfl
  | .field kind ty base fld =>
      rw [resolveMBase] at heq
      obtain ⟨⟨t', baseId⟩, hx, hf⟩ := bind_ok_inv heq
      obtain ⟨obj, hobj, hf2⟩ := bind_ok_inv hf
      have h1 := resolveMBase_pure (by simpa [pureExpr] using hp) hx
      cases obj with
      | array elems => exact nomatch hf2
      | struct fields =>
          simp only [] at hf2
          cases hlk : lookupBy fld.name fields with
          | none => rw [hlk] at hf2; exact nomatch hf2
          | some v =>
              rw [hlk] at hf2
              cases v with
              | prim p => cases p <;> exact nomatch hf2
              | ref id =>
                  cases hf2
                  exact h1
  | .index kind ty base index =>
      rw [resolveMBase] at heq
      obtain ⟨⟨t₁, baseId⟩, hx, hf⟩ := bind_ok_inv heq
      obtain ⟨⟨t₂, i⟩, hi, hf2⟩ := bind_ok_inv hf
      obtain ⟨obj, hobj, hf3⟩ := bind_ok_inv hf2
      have h1 := resolveMBase_pure (by simp [pureExpr] at hp; exact hp.1) hx
      have h2 := evalInt_pure (by simp [pureExpr] at hp; exact hp.2) hi
      cases obj with
      | struct fields => exact nomatch hf3
      | array elems =>
          simp only [] at hf3
          by_cases hb : 0 ≤ i ∧ i.toNat < elems.length
          · rw [dif_pos hb] at hf3
            cases hget : elems.get ⟨i.toNat, hb.2⟩ with
            | prim p => cases p <;> (rw [hget] at hf3; exact nomatch hf3)
            | ref id =>
                rw [hget] at hf3
                cases hf3
                exact h2.trans h1
          · rw [dif_neg hb] at hf3
            exact nomatch hf3
  | .bool b =>
      rw [resolveMBase.eq_def] at heq
      exact nomatch heq
  | .intLit ty v =>
      rw [resolveMBase.eq_def] at heq
      exact nomatch heq
  | .pushPlace target => exact nomatch hp
  | .mkCall kind ty nm args => exact nomatch hp
  | .mkBinop op l r =>
      rw [resolveMBase.eq_def] at heq
      exact nomatch heq
  | .mkUnop op arg =>
      rw [resolveMBase.eq_def] at heq
      exact nomatch heq
  | .mkIncDec op target => exact nomatch hp
  | .mkTernary c t el => exact nomatch hp
termination_by 4 * e.size + 0
decreasing_by all_goals
  first
  | omega
  | (simp [Typed.WrappedExpr.size] <;> omega)

theorem readM_pure {s t : State} {e : WrappedExpr}
    (hp : pureExpr e = true) {r : MVal}
    (heq : readM s e = .ok (t, r)) : t = s := by
  match e with
  | .var kind ty fld =>
      rw [readM] at heq
      obtain ⟨b, hx, hf⟩ := bind_ok_inv heq
      cases b with
      | val v => exact nomatch hf
      | spath root segs => exact nomatch hf
      | mref id =>
          cases hf
          rfl
  | .field kind ty base fld =>
      rw [readM] at heq
      obtain ⟨⟨t', baseId⟩, hx, hf⟩ := bind_ok_inv heq
      obtain ⟨obj, hobj, hf2⟩ := bind_ok_inv hf
      have h1 := resolveMBase_pure (by simpa [pureExpr] using hp) hx
      cases obj with
      | array elems => exact nomatch hf2
      | struct fields =>
          simp only [] at hf2
          cases hlk : lookupBy fld.name fields with
          | none => rw [hlk] at hf2; exact nomatch hf2
          | some v =>
              rw [hlk] at hf2
              cases hf2
              exact h1
  | .index kind ty base index =>
      rw [readM] at heq
      obtain ⟨⟨t₁, baseId⟩, hx, hf⟩ := bind_ok_inv heq
      obtain ⟨⟨t₂, i⟩, hi, hf2⟩ := bind_ok_inv hf
      obtain ⟨obj, hobj, hf3⟩ := bind_ok_inv hf2
      have h1 := resolveMBase_pure (by simp [pureExpr] at hp; exact hp.1) hx
      have h2 := evalInt_pure (by simp [pureExpr] at hp; exact hp.2) hi
      cases obj with
      | struct fields => exact nomatch hf3
      | array elems =>
          simp only [] at hf3
          by_cases hb : 0 ≤ i ∧ i.toNat < elems.length
          · rw [dif_pos hb] at hf3
            cases hf3
            exact h2.trans h1
          · rw [dif_neg hb] at hf3
            exact nomatch hf3
  | .bool b =>
      rw [readM.eq_def] at heq
      exact nomatch heq
  | .intLit ty v =>
      rw [readM.eq_def] at heq
      exact nomatch heq
  | .pushPlace target => exact nomatch hp
  | .mkCall kind ty nm args => exact nomatch hp
  | .mkBinop op l r =>
      rw [readM.eq_def] at heq
      exact nomatch heq
  | .mkUnop op arg =>
      rw [readM.eq_def] at heq
      exact nomatch heq
  | .mkIncDec op target => exact nomatch hp
  | .mkTernary c t el => exact nomatch hp
termination_by 4 * e.size + 1
decreasing_by all_goals
  first
  | omega
  | (simp [Typed.WrappedExpr.size] <;> omega)

theorem resolveLoc_pure {s t : State} {e : WrappedExpr}
    (hp : pureExpr e = true) {loc : Loc}
    (heq : resolveLoc s e = .ok (t, loc)) : t = s := by
  match e with
  | .var kind ty fld =>
      cases kind with
      | stack =>
          rw [resolveLoc] at heq
          cases heq
          rfl
      | memory =>
          rw [resolveLoc] at heq
          cases heq
          rfl
      | storage =>
          rw [resolveLoc] at heq
          by_cases ho : fld.origin = some StorageOrigin.global
          · simp only [if_pos ho] at heq
            cases heq
            rfl
          · simp only [if_neg ho] at heq
            cases heq
            rfl
  | .field kind ty base fld =>
      cases kind with
      | storage =>
          rw [resolveLoc] at heq
          obtain ⟨⟨t', a⟩, hx, hf⟩ := bind_ok_inv heq
          cases hf
          exact resolveS_pure (e := WrappedExpr.field Kind.storage Ty.uint base fld)
            (by simpa [pureExpr] using hp) hx
      | memory =>
          rw [resolveLoc] at heq
          obtain ⟨⟨t', baseId⟩, hx, hf⟩ := bind_ok_inv heq
          cases hf
          exact resolveMBase_pure (by simpa [pureExpr] using hp) hx
      | stack =>
          rw [resolveLoc] at heq
          · exact nomatch heq
          all_goals nofun
  | .index kind ty base index =>
      cases kind with
      | storage =>
          rw [resolveLoc] at heq
          obtain ⟨⟨t₁, a⟩, hx, hf⟩ := bind_ok_inv heq
          obtain ⟨⟨t₂, i⟩, hi, hf2⟩ := bind_ok_inv hf
          cases hf2
          have h1 := resolveS_pure (by simp [pureExpr] at hp; exact hp.1) hx
          have h2 := evalInt_pure (by simp [pureExpr] at hp; exact hp.2) hi
          exact h2.trans h1
      | memory =>
          rw [resolveLoc] at heq
          obtain ⟨⟨t₁, baseId⟩, hx, hf⟩ := bind_ok_inv heq
          obtain ⟨⟨t₂, i⟩, hi, hf2⟩ := bind_ok_inv hf
          cases hf2
          have h1 := resolveMBase_pure (by simp [pureExpr] at hp; exact hp.1) hx
          have h2 := evalInt_pure (by simp [pureExpr] at hp; exact hp.2) hi
          exact h2.trans h1
      | stack =>
          rw [resolveLoc] at heq
          · exact nomatch heq
          all_goals nofun
  | .bool b =>
      rw [resolveLoc.eq_def] at heq
      exact nomatch heq
  | .intLit ty v =>
      rw [resolveLoc.eq_def] at heq
      exact nomatch heq
  | .pushPlace target => exact nomatch hp
  | .mkCall kind ty nm args => exact nomatch hp
  | .mkBinop op l r =>
      rw [resolveLoc.eq_def] at heq
      exact nomatch heq
  | .mkUnop op arg =>
      rw [resolveLoc.eq_def] at heq
      exact nomatch heq
  | .mkIncDec op target => exact nomatch hp
  | .mkTernary c t el => exact nomatch hp
termination_by 4 * e.size + 1
decreasing_by all_goals
  first
  | omega
  | (simp [Typed.WrappedExpr.size] <;> omega)

theorem evalValue_pure {s t : State} {e : WrappedExpr}
    (hp : pureExpr e = true) {v : Value}
    (heq : evalValue s e = .ok (t, v)) : t = s := by
  match e with
  | .bool b =>
      rw [evalValue] at heq
      cases heq
      rfl
  | .intLit ty v =>
      rw [evalValue] at heq
      cases heq
      rfl
  | .var kind ty fld =>
      cases kind with
      | stack =>
          rw [evalValue] at heq
          obtain ⟨b, hx, hf⟩ := bind_ok_inv heq
          cases b with
          | val v =>
              cases hf
              rfl
          | spath root segs => exact nomatch hf
          | mref id => exact nomatch hf
      | storage =>
          rw [evalValue] at heq
          obtain ⟨⟨t', a⟩, hx, hf⟩ := bind_ok_inv heq
          obtain ⟨sv, hsv, hf2⟩ := bind_ok_inv hf
          obtain ⟨val, hval, hf3⟩ := bind_ok_inv hf2
          cases hf3
          exact resolveS_pure (e := WrappedExpr.var Kind.storage ty fld) rfl hx
      | memory =>
          rw [evalValue] at heq
          exact nomatch heq
  | .field kind ty base fld =>
      cases kind with
      | storage =>
          rw [evalValue] at heq
          obtain ⟨⟨t', a⟩, hx, hf⟩ := bind_ok_inv heq
          obtain ⟨sv, hsv, hf2⟩ := bind_ok_inv hf
          obtain ⟨val, hval, hf3⟩ := bind_ok_inv hf2
          cases hf3
          exact resolveS_pure (e := WrappedExpr.field Kind.storage ty base fld)
            (by simpa [pureExpr] using hp) hx
      | memory =>
          rw [evalValue] at heq
          obtain ⟨⟨t', mv⟩, hx, hf⟩ := bind_ok_inv heq
          obtain ⟨val, hval, hf2⟩ := bind_ok_inv hf
          cases hf2
          exact readM_pure (e := WrappedExpr.field Kind.memory ty base fld)
            (by simpa [pureExpr] using hp) hx
      | stack =>
          rw [evalValue] at heq
          · exact nomatch heq
          all_goals nofun
  | .index kind ty base index =>
      cases kind with
      | storage =>
          rw [evalValue] at heq
          obtain ⟨⟨t', a⟩, hx, hf⟩ := bind_ok_inv heq
          obtain ⟨sv, hsv, hf2⟩ := bind_ok_inv hf
          obtain ⟨val, hval, hf3⟩ := bind_ok_inv hf2
          cases hf3
          exact resolveS_pure (e := WrappedExpr.index Kind.storage ty base index)
            (by simpa [pureExpr] using hp) hx
      | memory =>
          rw [evalValue] at heq
          obtain ⟨⟨t', mv⟩, hx, hf⟩ := bind_ok_inv heq
          obtain ⟨val, hval, hf2⟩ := bind_ok_inv hf
          cases hf2
          exact readM_pure (e := WrappedExpr.index Kind.memory ty base index)
            (by simpa [pureExpr] using hp) hx
      | stack =>
          rw [evalValue] at heq
          · exact nomatch heq
          all_goals nofun
  | .mkBinop op l r =>
      have hpl : pureExpr l = true := by
        simp [pureExpr] at hp
        exact hp.1
      have hpr : pureExpr r = true := by
        simp [pureExpr] at hp
        exact hp.2
      rw [evalValue] at heq
      obtain ⟨⟨t₁, lv⟩, hx, hf⟩ := bind_ok_inv heq
      have h1 := evalValue_pure hpl hx
      have hrest : ∀ (heq2 : ((evalValue t₁ r) >>= fun x =>
          (applyBinOp op lv x.2) >>= fun w =>
            (checkArith (op.retTy l.ty) w) >>= fun w' =>
              Except.ok (x.1, w')) = .ok (t, v)),
          t = s := by
        intro heq2
        obtain ⟨⟨t₂, rv⟩, hr, hf2⟩ := bind_ok_inv heq2
        obtain ⟨w, hw, hf3⟩ := bind_ok_inv hf2
        obtain ⟨w', hw', hf4⟩ := bind_ok_inv hf3
        cases hf4
        exact (evalValue_pure hpr hr).trans h1
      cases op <;>
        first
        | exact hrest hf
        | (cases lv with
            | int v' => exact hrest hf
            | bool b =>
                cases b <;>
                  first
                  | (cases hf; exact h1)
                  | exact hrest hf)
  | .mkUnop op arg =>
      have hpa : pureExpr arg = true := by
        simpa [pureExpr] using hp
      rw [evalValue] at heq
      obtain ⟨⟨t₁, av⟩, hx, hf⟩ := bind_ok_inv heq
      obtain ⟨w, hw, hf2⟩ := bind_ok_inv hf
      have ht₁ : t = t₁ := by
        split at hf2
        · obtain ⟨w', hw', hf3⟩ := bind_ok_inv hf2
          cases hf3
          rfl
        · cases hf2
          rfl
      rw [ht₁]
      exact evalValue_pure hpa hx
  | .mkIncDec op target => exact nomatch hp
  | .mkTernary c t el => exact nomatch hp
  | .mkCall kind ty nm args => exact nomatch hp
  | .pushPlace target => exact nomatch hp
termination_by 4 * e.size + 2
decreasing_by all_goals
  first
  | omega
  | (simp [Typed.WrappedExpr.size] <;> omega)

theorem evalInt_pure {s t : State} {e : WrappedExpr}
    (hp : pureExpr e = true) {i : Int}
    (heq : evalInt s e = .ok (t, i)) : t = s := by
  rw [evalInt] at heq
  obtain ⟨⟨t', v⟩, hx, hf⟩ := bind_ok_inv heq
  obtain ⟨w, hw, hf2⟩ := bind_ok_inv hf
  cases hf2
  exact evalValue_pure hp hx
termination_by 4 * e.size + 3
decreasing_by all_goals omega

end

/-! ## Alias read-back

After a capture statement binds a scratch alias, reading through the
alias variable returns the captured resolution from an unchanged
state. -/

theorem aliasField_name (kind : Kind) (ty : Ty) (n : Name) :
    (aliasField kind ty n).name = n := by
  cases kind <;> cases ty <;> rfl

theorem resolveS_alias {s : State} {n root : Name} {segs : List Seg}
    (ty : Ty) (hb : lookupBy n s.env = some (Binding.spath root segs)) :
    resolveS s (aliasExpr Kind.storage ty n) = .ok (s, root, segs) := by
  rw [aliasExpr, resolveS, aliasField_name, hb]

theorem readM_alias {s : State} {n : Name} {id : Nat}
    (ty : Ty) (hb : lookupBy n s.env = some (Binding.mref id)) :
    readM s (aliasExpr Kind.memory ty n) = .ok (s, MVal.ref id) := by
  rw [aliasExpr, readM]
  unfold State.getEnv
  rw [aliasField_name, hb]
  rfl

theorem resolveMBase_alias {s : State} {n : Name} {id : Nat}
    (ty : Ty) (hb : lookupBy n s.env = some (Binding.mref id)) :
    resolveMBase s (aliasExpr Kind.memory ty n) = .ok (s, id) := by
  rw [aliasExpr, resolveMBase]
  unfold State.getEnv
  rw [aliasField_name, hb]
  rfl

theorem evalValue_alias {s : State} {n : Name} {v : Value}
    (ty : Ty) (hb : lookupBy n s.env = some (Binding.val v)) :
    evalValue s (aliasExpr Kind.stack ty n) = .ok (s, v) := by
  rw [aliasExpr, evalValue]
  unfold State.getEnv
  rw [aliasField_name, hb]
  rfl

theorem evalInt_alias {s : State} {n : Name} {i : Int}
    (ty : Ty) (hb : lookupBy n s.env = some (Binding.val (Value.int i))) :
    evalInt s (aliasExpr Kind.stack ty n) = .ok (s, i) := by
  rw [evalInt, evalValue_alias ty hb]
  rfl

/-! ## Block-shape helpers -/

theorem execBlock_single (s : State) (a : Stmt) :
    execBlock s [a] = execStmt s a := by
  rw [execBlock.eq_def]
  simp only []
  cases hx : execStmt s a with
  | error e => rfl
  | ok t =>
      show execBlock t [] = Except.ok t
      rw [execBlock]

theorem execBlock_pair (s : State) (a b : Stmt) :
    execBlock s [a, b] =
      (execStmt s a) >>= fun t => execStmt t b := by
  rw [execBlock.eq_def]
  simp only []
  cases hx : execStmt s a with
  | error e => rfl
  | ok t =>
      show execBlock t [b] = execStmt t b
      exact execBlock_single t b

/-- Three-statement residuals appear once the LHS-unfold rules freeze the
value operand ahead of the target capture (`Rules.freezeRhs`). -/
theorem execBlock_triple (s : State) (a b c : Stmt) :
    execBlock s [a, b, c] =
      (execStmt s a) >>= fun t => execBlock t [b, c] := by
  rw [execBlock.eq_def]

/-- Four-statement residual: value freeze, path capture, index capture,
write (`Rules.indexWriteResolveBlock` on a complex index). -/
theorem execBlock_quad (s : State) (a b c d : Stmt) :
    execBlock s [a, b, c, d] =
      (execStmt s a) >>= fun t => execBlock t [b, c, d] := by
  rw [execBlock.eq_def]

/-! ## Assignment with swapped-prefix side conditions

The write-unfold rules hoist the target's path ahead of the right-hand
side, while the interpreter — like solc — computes the right-hand side
first. The templates below therefore carry non-interference side
conditions: the right-hand side is pure, succeeds in the initial state,
and reads the same value after the path capture's effects. -/

/-! ## Per-rule soundness -/

theorem pv_mem : valueAliasName ∈ aliasNames :=
  List.mem_cons_self ..
theorem sp_mem : storagePathAliasName ∈ aliasNames :=
  List.mem_cons_of_mem _ (List.mem_cons_self ..)
theorem mp_mem : memoryPathAliasName ∈ aliasNames :=
  List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
theorem idx_mem : indexAliasName ∈ aliasNames :=
  List.mem_cons_of_mem _
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
theorem rv_mem : rhsValueAliasName ∈ aliasNames :=
  List.mem_cons_of_mem _
    (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))

theorem placeVar_expr (kind : Kind) (ty : Ty) (fld : Field) :
    (PlaceExpr.var kind ty fld).expr = WrappedExpr.var kind ty fld := rfl

theorem placeField_expr (kind : Kind) (ty : Ty) (base : WrappedExpr)
    (fld : Field) :
    (PlaceExpr.field kind ty base fld).expr =
      WrappedExpr.field kind ty base fld := rfl

theorem placeIndex_expr (kind : Kind) (ty : Ty) (base index : WrappedExpr) :
    (PlaceExpr.index kind ty base index).expr =
      WrappedExpr.index kind ty base index := rfl

/-- `Res` bind reductions as rewrite rules (the `do`-blocks hide the
`Except.bind` applications from `rw`). -/
theorem resOk_bind (a : α) (f : α -> Res β) :
    (Except.ok a >>= f : Res β) = f a := rfl

theorem resError_bind (e : Halt) (f : α -> Res β) :
    ((Except.error e : Res α) >>= f) = .error e := rfl

/-- Transport a pure, fresh base resolution along an env-agreement. -/
theorem resolveS_transport {ns : List Name} {s t' : State}
    {path : WrappedExpr} {root : Name} {segs : List Seg}
    (hagree : EnvAgreeExcept ns s t')
    (hf : ∀ n ∈ ns, usesVar path n = false)
    (hp : pureExpr path = true)
    (hbase : resolveS s path = .ok (s, root, segs)) :
    resolveS t' path = .ok (t', root, segs) := by
  have h := resolveS_agree hagree path hf
  rw [hbase] at h
  rcases h.cases with ⟨e, h1, h2⟩ | ⟨u₁, u₂, a, h1, h2, hu⟩
  · exact nomatch h1
  · have ha : a = (root, segs) := (congrArg Prod.snd (Except.ok.inj h1)).symm
    have hu2 : u₂ = t' := resolveS_pure hp h2
    rw [h2, hu2, ha]

/-- A pure right-hand-side reading leaves the state unchanged. -/
theorem rhsToSVal_pure {s t : State} {rhs : WrappedExpr} {x : SVal}
    (hp : pureExpr rhs = true)
    (h : rhsToSVal s rhs = .ok (t, x)) : t = s := by
  rw [rhsToSVal] at h
  by_cases hprim : rhs.ty.isPrimitive = true
  · rw [if_pos hprim] at h
    obtain ⟨⟨t', v⟩, h1, h2⟩ := bind_ok_inv h
    cases h2
    exact evalValue_pure hp h1
  · rw [if_neg hprim] at h
    match hk : rhs.kind with
    | Kind.storage =>
        rw [hk] at h
        by_cases hm : tyHasMapping rhs.ty = true
        · rw [if_pos hm] at h
          exact nomatch h
        · rw [if_neg hm] at h
          obtain ⟨⟨t', root, segs⟩, h1, h2⟩ := bind_ok_inv h
          obtain ⟨v, h3, h4⟩ := bind_ok_inv h2
          cases h4
          exact resolveS_pure hp h1
    | Kind.memory =>
        rw [hk] at h
        obtain ⟨⟨t', mv⟩, h1, h2⟩ := bind_ok_inv h
        obtain ⟨sval, h3, h4⟩ := bind_ok_inv h2
        cases h4
        exact readM_pure hp h1
    | Kind.stack =>
        rw [hk] at h
        exact nomatch h

/-- Transport a pure, fresh, successful right-hand-side reading along
an env-agreement. -/
theorem rhsToSVal_transportOk {ns : List Name} {s t' : State}
    {rhs : WrappedExpr} {x : SVal}
    (hagree : EnvAgreeExcept ns s t')
    (hf : ∀ n ∈ ns, usesVar rhs n = false)
    (hp : pureExpr rhs = true)
    (hbase : rhsToSVal s rhs = .ok (s, x)) :
    rhsToSVal t' rhs = .ok (t', x) := by
  have h := rhsToSVal_agree hagree rhs hf
  rw [hbase] at h
  rcases h.cases with ⟨err, h1, h2⟩ | ⟨u₁, u₂, a, h1, h2, hu⟩
  · exact nomatch h1
  · have ha : a = x := (congrArg Prod.snd (Except.ok.inj h1)).symm
    have hu2 : u₂ = t' := rhsToSVal_pure hp h2
    rw [h2, hu2, ha]

/-- Transport a fresh right-hand-side reading's failure along an
env-agreement. -/
theorem rhsToSVal_transportErr {ns : List Name} {s t' : State}
    {rhs : WrappedExpr} {e : Halt}
    (hagree : EnvAgreeExcept ns s t')
    (hf : ∀ n ∈ ns, usesVar rhs n = false)
    (hbase : rhsToSVal s rhs = .error e) :
    rhsToSVal t' rhs = .error e := by
  have h := rhsToSVal_agree hagree rhs hf
  rw [hbase] at h
  rcases h.cases with ⟨err, h1, h2⟩ | ⟨u₁, u₂, a, h1, h2, hu⟩
  · cases h1
    exact h2
  · exact nomatch h1

/-- A pure memory-target right-hand-side reading leaves the state
unchanged (a storage source would allocate, so it is excluded). -/
theorem rhsToMVal_pure {s t : State} {rhs : WrappedExpr} {x : MVal}
    (hp : pureExpr rhs = true)
    (hk : rhs.kind = Kind.memory ∨ rhs.ty.isPrimitive = true)
    (h : rhsToMVal s rhs = .ok (t, x)) : t = s := by
  rw [rhsToMVal] at h
  by_cases hprim : rhs.ty.isPrimitive = true
  · rw [if_pos hprim] at h
    obtain ⟨⟨t', v⟩, h1, h2⟩ := bind_ok_inv h
    cases h2
    exact evalValue_pure hp h1
  · rw [if_neg hprim] at h
    cases hk with
    | inr hpv => exact absurd hpv hprim
    | inl hkm =>
        rw [hkm] at h
        exact readM_pure hp h

/-- Transport a pure, fresh, successful memory-target right-hand-side
reading along an env-agreement. -/
theorem rhsToMVal_transportOk {ns : List Name} {s t' : State}
    {rhs : WrappedExpr} {x : MVal}
    (hagree : EnvAgreeExcept ns s t')
    (hf : ∀ n ∈ ns, usesVar rhs n = false)
    (hp : pureExpr rhs = true)
    (hk : rhs.kind = Kind.memory ∨ rhs.ty.isPrimitive = true)
    (hbase : rhsToMVal s rhs = .ok (s, x)) :
    rhsToMVal t' rhs = .ok (t', x) := by
  have h := rhsToMVal_agree hagree rhs hf
  rw [hbase] at h
  rcases h.cases with ⟨err, h1, h2⟩ | ⟨u₁, u₂, a, h1, h2, hu⟩
  · exact nomatch h1
  · have ha : a = x := (congrArg Prod.snd (Except.ok.inj h1)).symm
    have hu2 : u₂ = t' := rhsToMVal_pure hp hk h2
    rw [h2, hu2, ha]

/-- Post-RHS resolution from purity: a pure right-hand side leaves the
state unchanged, so the initial resolution serves after it. -/
theorem locAfterEval_of_pure {s : State} {rhs e : WrappedExpr}
    {loc : Loc} (hp : pureExpr rhs = true)
    (hlhs : resolveLoc s e = .ok (s, loc)) :
    ∀ {u : State} {v : Value}, evalValue s rhs = .ok (u, v) ->
      resolveLoc u e = .ok (u, loc) := fun h => by
  rw [evalValue_pure hp h]
  exact hlhs

theorem locAfterSVal_of_pure {s : State} {rhs e : WrappedExpr}
    {loc : Loc} (hp : pureExpr rhs = true)
    (hlhs : resolveLoc s e = .ok (s, loc)) :
    ∀ {u : State} {x : SVal}, rhsToSVal s rhs = .ok (u, x) ->
      resolveLoc u e = .ok (u, loc) := fun h => by
  rw [rhsToSVal_pure hp h]
  exact hlhs

theorem locAfterMVal_of_pure {s : State} {rhs e : WrappedExpr}
    {loc : Loc} (hp : pureExpr rhs = true)
    (hk : rhs.kind = Kind.memory ∨ rhs.ty.isPrimitive = true)
    (hlhs : resolveLoc s e = .ok (s, loc)) :
    ∀ {u : State} {x : MVal}, rhsToMVal s rhs = .ok (u, x) ->
      resolveLoc u e = .ok (u, loc) := fun h => by
  rw [rhsToMVal_pure hp hk h]
  exact hlhs

/-- Simple expressions are pure. -/
theorem pure_of_simple {e : WrappedExpr} (h : e.simple = true) :
    pureExpr e = true := by
  match e with
  | .var .. => rfl
  | .bool _ => rfl
  | .intLit .. => rfl

/-- Reading the frozen value operand back: `rv` holds a primitive, so
`rhsToSVal` on the alias is a pure environment lookup. -/
theorem rhsToSVal_stackAlias {s : State} {ty : Ty} {v : Value} {n : Name}
    (hprim : ty.isPrimitive = true)
    (hb : lookupBy n s.env = some (Binding.val v)) :
    rhsToSVal s (aliasExpr Kind.stack ty n) = .ok (s, v.toSVal) := by
  have hty : (aliasExpr Kind.stack ty n).ty = ty := rfl
  rw [rhsToSVal, hty, hprim]
  simp only [if_pos, evalValue_alias ty hb]
  rfl

/-- The memory twin. -/
theorem rhsToMVal_stackAlias {s : State} {ty : Ty} {v : Value} {n : Name}
    (hprim : ty.isPrimitive = true)
    (hb : lookupBy n s.env = some (Binding.val v)) :
    rhsToMVal s (aliasExpr Kind.stack ty n) = .ok (s, v.toMVal) := by
  have hty : (aliasExpr Kind.stack ty n).ty = ty := rfl
  rw [rhsToMVal, hty, hprim]
  simp only [if_pos, evalValue_alias ty hb]
  rfl

theorem sp_ne_rv : storagePathAliasName ≠ rhsValueAliasName := by decide
theorem mp_ne_rv : memoryPathAliasName ≠ rhsValueAliasName := by decide
theorem idx_ne_rv : indexAliasName ≠ rhsValueAliasName := by decide
theorem idx_ne_sp : indexAliasName ≠ storagePathAliasName := by decide
theorem idx_ne_mp : indexAliasName ≠ memoryPathAliasName := by decide

/-- Template: the storage field-write unfold on a **reference-typed**
value operand.  `Rules.freezeRhs` deliberately does not freeze one:
binding a reference is aliasing, not a read, so the declaration would not
snapshot the content `rhsToSVal` copies out of the heap.  The order swap
therefore survives here, and the rule stays conditional — `hev`/`hstable`
say the source still reads the same value after the path capture.

That is not a proof gap that better bookkeeping would close: on
`alice.accounts[mv.x++] = mv` the capture mutates the very heap object
the source copies.  The hypothesis can only be moved into the taclet's
side condition, not removed. -/
theorem fieldWriteResolveStorage_ref_sound (s : State) (ty : Ty)
    (path : WrappedExpr) (fld : Field) (rhs : WrappedExpr) {sv : SVal}
    (hnp : rhs.ty.isPrimitive = false)
    (hfr : ∀ n ∈ aliasNames, usesVar rhs n = false)
    (hpr : pureExpr rhs = true)
    (hev : rhsToSVal s rhs = .ok (s, sv))
    (hstable : ∀ {t : State} {root : Name} {segs : List Seg},
      resolveS s path = .ok (t, root, segs) ->
        rhsToSVal t rhs = .ok (t, sv)) :
    ResultsAgree aliasNames
      (execStmt s (Stmt.assign (PlaceExpr.field Kind.storage ty path fld) rhs))
      (execBlock s (fieldWriteResolveBlock Kind.storage storagePathAliasName
        ty path fld rhs)) := by
  show ResultsAgree aliasNames
    (execStmt s (Stmt.assign (PlaceExpr.field Kind.storage ty path fld) rhs))
    (execBlock s (freezeRhs rhs fun v =>
      [captureStoragePath path,
        Stmt.assign
          (fieldFromAlias Kind.storage storagePathAliasName ty path fld) v]))
  rw [freezeRhs, if_neg (by simp [hnp])]
  show ResultsAgree aliasNames
    (execStmt s (Stmt.assign (PlaceExpr.field Kind.storage ty path fld) rhs))
    (execBlock s [captureStoragePath path,
      Stmt.assign
        (fieldFromAlias Kind.storage storagePathAliasName ty path fld) rhs])
  rw [execStmt, execBlock_pair, captureStoragePath, capture]
  cases hres : resolveS s path with
  | error err =>
      have hL : execAssign s (PlaceExpr.field Kind.storage ty path fld) rhs =
          .error err := by
        show execAssignNested s
          (WrappedExpr.field Kind.storage ty path fld) rhs = .error err
        rw [execAssignNested, hev]
        simp only [Typed.WrappedExpr.kind, resOk_bind]
        rw [resolveLoc, resolveS, hres]
        rfl
      have hR : execStmt s
          (Stmt.storagePlaceAlias path.ty storagePathAliasName path) =
          .error err := by
        rw [execStmt, hres]
        rfl
      rw [hL, hR]
      exact rfl
  | ok x =>
      obtain ⟨t, root, segs⟩ := x
      have hR : execStmt s
          (Stmt.storagePlaceAlias path.ty storagePathAliasName path) =
          .ok (t.setEnv storagePathAliasName (Binding.spath root segs)) := by
        rw [execStmt, hres]
        rfl
      rw [hR]
      have ht' : EnvAgreeExcept aliasNames t
          (t.setEnv storagePathAliasName (Binding.spath root segs)) :=
        (EnvAgreeExcept.refl _ t).setEnv_right sp_mem _
      have hL : execAssign s (PlaceExpr.field Kind.storage ty path fld) rhs =
          t.saveStorage root (segs ++ [Seg.field fld.name]) sv := by
        show execAssignNested s
          (WrappedExpr.field Kind.storage ty path fld) rhs = _
        rw [execAssignNested, hev]
        simp only [Typed.WrappedExpr.kind, resOk_bind]
        rw [resolveLoc, resolveS, hres]
        rfl
      have hRhs' : rhsToSVal
          (t.setEnv storagePathAliasName (Binding.spath root segs)) rhs =
          .ok (t.setEnv storagePathAliasName (Binding.spath root segs), sv) :=
        rhsToSVal_transportOk ht' hfr hpr (hstable hres)
      have hRA : execStmt
          (t.setEnv storagePathAliasName (Binding.spath root segs))
          (Stmt.assign
            (fieldFromAlias Kind.storage storagePathAliasName ty path fld)
            rhs) =
          (t.setEnv storagePathAliasName
            (Binding.spath root segs)).saveStorage
            root (segs ++ [Seg.field fld.name]) sv := by
        rw [execStmt]
        show execAssignNested
          (t.setEnv storagePathAliasName (Binding.spath root segs))
          (WrappedExpr.field Kind.storage ty
            (aliasExpr Kind.storage path.ty storagePathAliasName) fld)
          rhs = _
        rw [execAssignNested, hRhs']
        simp only [Typed.WrappedExpr.kind, resOk_bind]
        rw [resolveLoc, resolveS,
          resolveS_alias path.ty
            (lookupBy_setBy_self storagePathAliasName
              (Binding.spath root segs) t.env)]
        rfl
      show ResultsAgree aliasNames
        (execAssign s (PlaceExpr.field Kind.storage ty path fld) rhs)
        (execStmt (t.setEnv storagePathAliasName (Binding.spath root segs))
          (Stmt.assign
            (fieldFromAlias Kind.storage storagePathAliasName ty path fld)
            rhs))
      rw [hL, hRA]
      exact saveStorage_agree ht' root (segs ++ [Seg.field fld.name]) sv

/-- Template: the storage field-write unfold (`fieldWriteResolveBlock`
at `Kind.storage`) on a **primitive** value operand.

`Rules.freezeRhs` binds the value into `rv` before the path capture runs,
so the two sides agree with nothing assumed about interference: the old
`hev`/`hstable` — which `people[i++].age = i` violates, see
`Counterexamples/EvaluationOrder.lean` — are gone, and so is purity of
the right-hand side.  All that is left is that the path does not mention
the reserved alias names.

The frozen binding survives the path capture by `resolveS_keep`; that is
the fact the old side conditions were standing in for.

Shared by `storageFieldWriteUnfoldLeftFst` and
`memoryToStorageUnfoldLeftFstTarget`. -/
theorem fieldWriteResolveStorage_sound (s : State) (ty : Ty)
    (path : WrappedExpr) (fld : Field) (rhs : WrappedExpr)
    (hprim : rhs.ty.isPrimitive = true)
    (hfp : ∀ n ∈ aliasNames, usesVar path n = false) :
    ResultsAgree aliasNames
      (execStmt s (Stmt.assign (PlaceExpr.field Kind.storage ty path fld) rhs))
      (execBlock s (fieldWriteResolveBlock Kind.storage storagePathAliasName
        ty path fld rhs)) := by
  show ResultsAgree aliasNames
    (execStmt s (Stmt.assign (PlaceExpr.field Kind.storage ty path fld) rhs))
    (execBlock s (freezeRhs rhs fun v =>
      [captureStoragePath path,
        Stmt.assign
          (fieldFromAlias Kind.storage storagePathAliasName ty path fld) v]))
  rw [freezeRhs, if_pos hprim, execStmt, execBlock_triple, captureRhsValue,
    capture, execStmt]
  cases hevR : evalValue s rhs with
  | error err =>
      have hL : execAssign s (PlaceExpr.field Kind.storage ty path fld) rhs =
          .error err := by
        show execAssignNested s
          (WrappedExpr.field Kind.storage ty path fld) rhs = .error err
        rw [execAssignNested, rhsToSVal, hprim]
        simp only [if_pos, hevR]
        rfl
      rw [hL]
      rfl
  | ok x =>
      obtain ⟨s₁, v⟩ := x
      simp only [hevR, resOk_bind]
      have hrv₁ : lookupBy rhsValueAliasName
          (s₁.setEnv rhsValueAliasName (Binding.val v)).env =
            some (Binding.val v) := lookupBy_setBy_self ..
      have hagree₁ : EnvAgreeExcept aliasNames s₁
          (s₁.setEnv rhsValueAliasName (Binding.val v)) :=
        (EnvAgreeExcept.refl _ s₁).setEnv_right rv_mem _
      have hL : execAssign s (PlaceExpr.field Kind.storage ty path fld) rhs =
          (resolveS s₁ path) >>= fun x =>
            match x with
            | (s₂, root, segs) =>
                s₂.saveStorage root (segs ++ [Seg.field fld.name]) v.toSVal := by
        show execAssignNested s
          (WrappedExpr.field Kind.storage ty path fld) rhs = _
        rw [execAssignNested, rhsToSVal, hprim]
        simp only [if_pos, hevR, resOk_bind, Typed.WrappedExpr.kind]
        rw [resolveLoc, resolveS]
        cases resolveS s₁ path with
        | error e => rfl
        | ok y => obtain ⟨s₂, root, segs⟩ := y; rfl
      have hR : execBlock (s₁.setEnv rhsValueAliasName (Binding.val v))
          [captureStoragePath path,
            Stmt.assign
              (fieldFromAlias Kind.storage storagePathAliasName ty path fld)
              (rhsValueAlias rhs)] =
          (resolveS (s₁.setEnv rhsValueAliasName (Binding.val v)) path) >>=
            fun x =>
              match x with
              | (t₂, root, segs) =>
                  execStmt (t₂.setEnv storagePathAliasName
                      (Binding.spath root segs))
                    (Stmt.assign
                      (fieldFromAlias Kind.storage storagePathAliasName ty path
                        fld)
                      (rhsValueAlias rhs)) := by
        rw [execBlock_pair, captureStoragePath, capture, execStmt]
        cases resolveS (s₁.setEnv rhsValueAliasName (Binding.val v)) path with
        | error e => rfl
        | ok y => obtain ⟨t₂, root, segs⟩ := y; rfl
      rw [hL, hR]
      refine ResAgree.bindStateWith (resolveS_agree hagree₁ path hfp) ?_
      intro s₂ t₂ a _ hres₂ hagree₂
      obtain ⟨root, segs⟩ := a
      have hrv₃ : lookupBy rhsValueAliasName
          (t₂.setEnv storagePathAliasName (Binding.spath root segs)).env =
            some (Binding.val v) := by
        rw [State.setEnv, lookupBy_setBy_ne (Ne.symm sp_ne_rv)]
        rw [resolveS_keep (s₁.setEnv rhsValueAliasName (Binding.val v)) path hfp
          t₂ (root, segs) hres₂ _ rv_mem]
        exact hrv₁
      have hsp₃ : lookupBy storagePathAliasName
          (t₂.setEnv storagePathAliasName (Binding.spath root segs)).env =
            some (Binding.spath root segs) := lookupBy_setBy_self ..
      have hRA : execStmt
          (t₂.setEnv storagePathAliasName (Binding.spath root segs))
          (Stmt.assign
            (fieldFromAlias Kind.storage storagePathAliasName ty path fld)
            (rhsValueAlias rhs)) =
          (t₂.setEnv storagePathAliasName
            (Binding.spath root segs)).saveStorage root
              (segs ++ [Seg.field fld.name]) v.toSVal := by
        rw [execStmt]
        show execAssignNested
          (t₂.setEnv storagePathAliasName (Binding.spath root segs))
          (WrappedExpr.field Kind.storage ty
            (aliasExpr Kind.storage path.ty storagePathAliasName) fld)
          (rhsValueAlias rhs) = _
        rw [execAssignNested, rhsValueAlias, rhsToSVal_stackAlias hprim hrv₃]
        simp only [Typed.WrappedExpr.kind, resOk_bind]
        rw [resolveLoc, resolveS, resolveS_alias path.ty hsp₃]
        rfl
      simp only []
      rw [hRA]
      exact saveStorage_agree (hagree₂.setEnv_right sp_mem _) root
        (segs ++ [Seg.field fld.name]) v.toSVal

/-! ### Tails of the storage index-write residual

Both are stated from the state right after the path capture; they differ
only in whether a complex index was captured into `idx` or left in place.
Together they are what makes `pureExpr index` unnecessary. -/

/-- Tail with the index captured (`index.complex`).  The frozen value and
the captured path both survive the index evaluation — `evalValue_keep` —
however impure that evaluation is. -/
theorem indexWriteTailCapture_agree {ty : Ty} {path index rhs : WrappedExpr}
    {s₂ t₂ : State} {v : Value} {root : Name} {segs : List Seg}
    (hprim : rhs.ty.isPrimitive = true)
    (hfi : ∀ n ∈ aliasNames, usesVar index n = false)
    (hrv₂ : lookupBy rhsValueAliasName t₂.env = some (Binding.val v))
    (hagree₂ : EnvAgreeExcept aliasNames s₂ t₂) :
    ResultsAgree aliasNames
      ((evalInt s₂ index) >>= fun y =>
        match y with
        | (s₃, i) => s₃.saveStorage root (segs ++ [Seg.at i]) v.toSVal)
      (execBlock (t₂.setEnv storagePathAliasName (Binding.spath root segs))
        [captureIndex index,
          Stmt.assign
            (indexFromAlias Kind.storage storagePathAliasName ty path
              (indexAlias index))
            (rhsValueAlias rhs)]) := by
  have hrv₃ : lookupBy rhsValueAliasName
      (t₂.setEnv storagePathAliasName (Binding.spath root segs)).env =
        some (Binding.val v) := by
    rw [State.setEnv, lookupBy_setBy_ne (Ne.symm sp_ne_rv)]
    exact hrv₂
  have hsp₃ : lookupBy storagePathAliasName
      (t₂.setEnv storagePathAliasName (Binding.spath root segs)).env =
        some (Binding.spath root segs) := lookupBy_setBy_self ..
  have hagree₃ : EnvAgreeExcept aliasNames s₂
      (t₂.setEnv storagePathAliasName (Binding.spath root segs)) :=
    hagree₂.setEnv_right sp_mem _
  have hLn : ((evalInt s₂ index) >>= fun y =>
        match y with
        | (s₃, i) => s₃.saveStorage root (segs ++ [Seg.at i]) v.toSVal) =
      (evalValue s₂ index) >>= fun y =>
        match y with
        | (s₃, w) => w.asInt >>= fun i =>
            s₃.saveStorage root (segs ++ [Seg.at i]) v.toSVal := by
    rw [evalInt]
    cases evalValue s₂ index with
    | error e => rfl
    | ok z =>
        obtain ⟨s₃, w⟩ := z
        simp only [resOk_bind]
        cases w.asInt with
        | error e => rfl
        | ok i => rfl
  have hRn : execBlock (t₂.setEnv storagePathAliasName (Binding.spath root segs))
        [captureIndex index,
          Stmt.assign
            (indexFromAlias Kind.storage storagePathAliasName ty path
              (indexAlias index))
            (rhsValueAlias rhs)] =
      (evalValue (t₂.setEnv storagePathAliasName (Binding.spath root segs))
        index) >>= fun y =>
        match y with
        | (t₄, w) =>
            execStmt (t₄.setEnv indexAliasName (Binding.val w))
              (Stmt.assign
                (indexFromAlias Kind.storage storagePathAliasName ty path
                  (indexAlias index))
                (rhsValueAlias rhs)) := by
    rw [execBlock_pair, captureIndex, capture, execStmt]
    cases evalValue (t₂.setEnv storagePathAliasName (Binding.spath root segs))
        index with
    | error e => rfl
    | ok z => obtain ⟨t₄, w⟩ := z; rfl
  rw [hLn, hRn]
  refine ResAgree.bindStateWith (evalValue_agree hagree₃ index hfi) ?_
  intro s₃ t₄ w _ hev₄ hagree₄
  have hkeep := evalValue_keep
    (t₂.setEnv storagePathAliasName (Binding.spath root segs)) index hfi t₄ w hev₄
  have hrv₅ : lookupBy rhsValueAliasName
      (t₄.setEnv indexAliasName (Binding.val w)).env = some (Binding.val v) := by
    rw [State.setEnv, lookupBy_setBy_ne (Ne.symm idx_ne_rv),
      hkeep rhsValueAliasName rv_mem]
    exact hrv₃
  have hsp₅ : lookupBy storagePathAliasName
      (t₄.setEnv indexAliasName (Binding.val w)).env =
        some (Binding.spath root segs) := by
    rw [State.setEnv, lookupBy_setBy_ne (Ne.symm idx_ne_sp),
      hkeep storagePathAliasName sp_mem]
    exact hsp₃
  have hidx₅ : lookupBy indexAliasName
      (t₄.setEnv indexAliasName (Binding.val w)).env = some (Binding.val w) :=
    lookupBy_setBy_self ..
  have hR : execStmt (t₄.setEnv indexAliasName (Binding.val w))
      (Stmt.assign
        (indexFromAlias Kind.storage storagePathAliasName ty path
          (indexAlias index))
        (rhsValueAlias rhs)) =
      w.asInt >>= fun i =>
        (t₄.setEnv indexAliasName (Binding.val w)).saveStorage root
          (segs ++ [Seg.at i]) v.toSVal := by
    rw [execStmt]
    show execAssignNested (t₄.setEnv indexAliasName (Binding.val w))
      (WrappedExpr.index Kind.storage ty
        (aliasExpr Kind.storage path.ty storagePathAliasName)
        (indexAlias index))
      (rhsValueAlias rhs) = _
    rw [execAssignNested, rhsValueAlias, rhsToSVal_stackAlias hprim hrv₅]
    simp only [Typed.WrappedExpr.kind, resOk_bind]
    rw [resolveLoc, resolveS_alias path.ty hsp₅]
    simp only [resOk_bind]
    rw [evalInt, indexAlias, evalValue_alias index.ty hidx₅]
    simp only [resOk_bind]
    cases w.asInt with
    | error e => rfl
    | ok i => rfl
  simp only []
  rw [hR]
  refine bindPureResults_agree _ fun i => ?_
  exact saveStorage_agree (hagree₄.setEnv_right idx_mem _) root
    (segs ++ [Seg.at i]) v.toSVal

/-- Tail with a simple index left in place.  Both sides evaluate it after
the path, so ordinary congruence suffices. -/
theorem indexWriteTailPlain_agree {ty : Ty} {path index rhs : WrappedExpr}
    {s₂ t₂ : State} {v : Value} {root : Name} {segs : List Seg}
    (hprim : rhs.ty.isPrimitive = true)
    (hfi : ∀ n ∈ aliasNames, usesVar index n = false)
    (hrv₂ : lookupBy rhsValueAliasName t₂.env = some (Binding.val v))
    (hagree₂ : EnvAgreeExcept aliasNames s₂ t₂) :
    ResultsAgree aliasNames
      ((evalInt s₂ index) >>= fun y =>
        match y with
        | (s₃, i) => s₃.saveStorage root (segs ++ [Seg.at i]) v.toSVal)
      (execBlock (t₂.setEnv storagePathAliasName (Binding.spath root segs))
        [Stmt.assign
          (indexFromAlias Kind.storage storagePathAliasName ty path index)
          (rhsValueAlias rhs)]) := by
  have hrv₃ : lookupBy rhsValueAliasName
      (t₂.setEnv storagePathAliasName (Binding.spath root segs)).env =
        some (Binding.val v) := by
    rw [State.setEnv, lookupBy_setBy_ne (Ne.symm sp_ne_rv)]
    exact hrv₂
  have hsp₃ : lookupBy storagePathAliasName
      (t₂.setEnv storagePathAliasName (Binding.spath root segs)).env =
        some (Binding.spath root segs) := lookupBy_setBy_self ..
  have hagree₃ : EnvAgreeExcept aliasNames s₂
      (t₂.setEnv storagePathAliasName (Binding.spath root segs)) :=
    hagree₂.setEnv_right sp_mem _
  have hR : execBlock (t₂.setEnv storagePathAliasName (Binding.spath root segs))
      [Stmt.assign
        (indexFromAlias Kind.storage storagePathAliasName ty path index)
        (rhsValueAlias rhs)] =
      (evalInt (t₂.setEnv storagePathAliasName (Binding.spath root segs))
        index) >>= fun y =>
        match y with
        | (t₃, i) =>
            t₃.saveStorage root (segs ++ [Seg.at i]) v.toSVal := by
    rw [execBlock_single, execStmt]
    show execAssignNested
      (t₂.setEnv storagePathAliasName (Binding.spath root segs))
      (WrappedExpr.index Kind.storage ty
        (aliasExpr Kind.storage path.ty storagePathAliasName) index)
      (rhsValueAlias rhs) = _
    rw [execAssignNested, rhsValueAlias, rhsToSVal_stackAlias hprim hrv₃]
    simp only [Typed.WrappedExpr.kind, resOk_bind]
    rw [resolveLoc, resolveS_alias path.ty hsp₃]
    simp only [resOk_bind]
    cases evalInt (t₂.setEnv storagePathAliasName (Binding.spath root segs))
        index with
    | error e => rfl
    | ok z => obtain ⟨t₃, i⟩ := z; rfl
  rw [hR]
  refine ResAgree.bindStateWith (evalInt_agree hagree₃ index hfi) ?_
  intro s₃ t₃ i _ _ hagree₄
  exact saveStorage_agree hagree₄ root (segs ++ [Seg.at i]) v.toSVal

/-- Template: the storage index-write unfold (`indexWriteResolveBlock`
at `Kind.storage`) on a **primitive** value operand — and, since
`captureIndexTargetBlock` is this function, the left-snd unfold too.

The residual runs value, path, index, write, which is exactly the order
`execAssignNested` + `resolveLoc` run them in.  So, as for the field
twin, nothing about interference is assumed: no `hev`, no `hstable`, and
crucially no `pureExpr index` — the hypothesis that used to exclude
`values[i++] = i`.  The frozen value and the captured path survive the
index evaluation by `evalValue_keep`, and the path capture by
`resolveS_keep`.

Shared by `storageIndexWriteUnfoldLeftFst`,
`storageIndexWriteUnfoldLeftSndIndex` and
`memoryToStorageUnfoldLeftSndTargetIndex`. -/
theorem indexWriteResolveStorage_sound (s : State) (ty : Ty)
    (path index rhs : WrappedExpr)
    (hprim : rhs.ty.isPrimitive = true)
    (hfp : ∀ n ∈ aliasNames, usesVar path n = false)
    (hfi : ∀ n ∈ aliasNames, usesVar index n = false) :
    ResultsAgree aliasNames
      (execStmt s (Stmt.assign (PlaceExpr.index Kind.storage ty path index) rhs))
      (execBlock s (indexWriteResolveBlock Kind.storage storagePathAliasName
        ty path index rhs)) := by
  show ResultsAgree aliasNames
    (execStmt s (Stmt.assign (PlaceExpr.index Kind.storage ty path index) rhs))
    (execBlock s (freezeRhs rhs fun v =>
      if index.complex then
        [captureStoragePath path, captureIndex index,
          Stmt.assign
            (indexFromAlias Kind.storage storagePathAliasName ty path
              (indexAlias index)) v]
      else
        [captureStoragePath path,
          Stmt.assign
            (indexFromAlias Kind.storage storagePathAliasName ty path index) v]))
  rw [freezeRhs, if_pos hprim, execStmt]
  cases hevR : evalValue s rhs with
  | error err =>
      have hL : execAssign s (PlaceExpr.index Kind.storage ty path index) rhs =
          .error err := by
        show execAssignNested s
          (WrappedExpr.index Kind.storage ty path index) rhs = .error err
        rw [execAssignNested, rhsToSVal, hprim]
        simp only [if_pos, hevR]
        rfl
      have hR : ∀ b : Block,
          execBlock s (captureRhsValue rhs :: b) = .error err := by
        intro b
        rw [execBlock.eq_def, captureRhsValue, capture]
        simp only [execStmt, hevR]
        rfl
      by_cases hc : index.complex
      · rw [if_pos hc, hL, hR]; rfl
      · rw [if_neg hc, hL, hR]; rfl
  | ok x =>
      obtain ⟨s₁, v⟩ := x
      have hrv₁ : lookupBy rhsValueAliasName
          (s₁.setEnv rhsValueAliasName (Binding.val v)).env =
            some (Binding.val v) := lookupBy_setBy_self ..
      have hagree₁ : EnvAgreeExcept aliasNames s₁
          (s₁.setEnv rhsValueAliasName (Binding.val v)) :=
        (EnvAgreeExcept.refl _ s₁).setEnv_right rv_mem _
      have hL : execAssign s (PlaceExpr.index Kind.storage ty path index) rhs =
          (resolveS s₁ path) >>= fun x =>
            match x with
            | (s₂, root, segs) =>
                (evalInt s₂ index) >>= fun y =>
                  match y with
                  | (s₃, i) =>
                      s₃.saveStorage root (segs ++ [Seg.at i]) v.toSVal := by
        show execAssignNested s
          (WrappedExpr.index Kind.storage ty path index) rhs = _
        rw [execAssignNested, rhsToSVal, hprim]
        simp only [if_pos, hevR, resOk_bind, Typed.WrappedExpr.kind]
        rw [resolveLoc]
        cases resolveS s₁ path with
        | error e => rfl
        | ok y =>
            obtain ⟨s₂, root, segs⟩ := y
            simp only [resOk_bind]
            cases evalInt s₂ index with
            | error e => rfl
            | ok z => obtain ⟨s₃, i⟩ := z; rfl
      -- the shared prefix: freeze, then capture the path
      have hRpre : ∀ tail : Block,
          execBlock s (captureRhsValue rhs :: captureStoragePath path :: tail) =
            (resolveS (s₁.setEnv rhsValueAliasName (Binding.val v)) path) >>=
              fun x =>
                match x with
                | (t₂, root, segs) =>
                    execBlock (t₂.setEnv storagePathAliasName
                      (Binding.spath root segs)) tail := by
        intro tail
        rw [execBlock.eq_def, captureRhsValue, capture]
        simp only [execStmt, hevR, resOk_bind]
        rw [execBlock.eq_def, captureStoragePath, capture]
        simp only [execStmt]
        cases resolveS (s₁.setEnv rhsValueAliasName (Binding.val v)) path with
        | error e => rfl
        | ok y => obtain ⟨t₂, root, segs⟩ := y; rfl
      rw [hL]
      by_cases hc : index.complex
      · rw [if_pos hc, hRpre]
        refine ResAgree.bindStateWith (resolveS_agree hagree₁ path hfp) ?_
        intro s₂ t₂ a _ hres₂ hagree₂
        obtain ⟨root, segs⟩ := a
        simp only []
        refine indexWriteTailCapture_agree hprim hfi ?_ hagree₂
        rw [resolveS_keep (s₁.setEnv rhsValueAliasName (Binding.val v)) path hfp
          t₂ (root, segs) hres₂ _ rv_mem]
        exact hrv₁
      · rw [if_neg hc, hRpre]
        refine ResAgree.bindStateWith (resolveS_agree hagree₁ path hfp) ?_
        intro s₂ t₂ a _ hres₂ hagree₂
        obtain ⟨root, segs⟩ := a
        simp only []
        refine indexWriteTailPlain_agree hprim hfi ?_ hagree₂
        rw [resolveS_keep (s₁.setEnv rhsValueAliasName (Binding.val v)) path hfp
          t₂ (root, segs) hres₂ _ rv_mem]
        exact hrv₁

/-- `people[i++].age = i` is in scope now: no `hev`, no `hstable`. -/
theorem storageFieldWriteUnfoldLeftFst_sound
    (s : State) (ty : Ty) (path : WrappedExpr) (fld : Field)
    (rhs : WrappedExpr)
    (hcond : (ruleEffect .storageFieldWriteUnfoldLeftFst).cond
      (Stmt.assign (PlaceExpr.field Kind.storage ty path fld) rhs))
    (hprim : rhs.ty.isPrimitive = true)
    (hfresh : ∀ n ∈ aliasNames,
      stmtUsesVar
        (Stmt.assign (PlaceExpr.field Kind.storage ty path fld) rhs) n =
        false) :
    ResultsAgree aliasNames
      (execStmt s
        (Stmt.assign (PlaceExpr.field Kind.storage ty path fld) rhs))
      (execBlock s
        ((ruleEffect .storageFieldWriteUnfoldLeftFst).block
          (Stmt.assign (PlaceExpr.field Kind.storage ty path fld) rhs)
          hcond)) := by
  exact fieldWriteResolveStorage_sound s ty path fld rhs hprim
    (fun n hn => by
      have := hfresh n hn
      simp [stmtUsesVar] at this
      exact this.1)

/-- `memoryToStorageUnfoldLeftFstTarget` on a **primitive**-typed memory
source.  The rule's condition (`isComplex path ∧ isMemory rhs ∧ isSimple rhs`)
admits one, and `freezeRhs` freezes it, so the residual is the ordinary frozen
template and this is unconditional — no `hev`, no `hstable`.

Stated because the reference-case theorem below requires
`hnp : rhs.ty.isPrimitive = false`, which left this half of the rule's own
condition with no theorem at all. -/
theorem memoryToStorageUnfoldLeftFstTarget_prim_sound
    (s : State) (ty : Ty) (path : WrappedExpr) (fld : Field)
    (rhs : WrappedExpr)
    (hcond : (ruleEffect .memoryToStorageUnfoldLeftFstTarget).cond
      (Stmt.assign (PlaceExpr.field Kind.storage ty path fld) rhs))
    (hprim : rhs.ty.isPrimitive = true)
    (hfresh : ∀ n ∈ aliasNames,
      stmtUsesVar
        (Stmt.assign (PlaceExpr.field Kind.storage ty path fld) rhs) n =
        false) :
    ResultsAgree aliasNames
      (execStmt s
        (Stmt.assign (PlaceExpr.field Kind.storage ty path fld) rhs))
      (execBlock s
        ((ruleEffect .memoryToStorageUnfoldLeftFstTarget).block
          (Stmt.assign (PlaceExpr.field Kind.storage ty path fld) rhs)
          hcond)) := by
  refine fieldWriteResolveStorage_sound s ty path fld rhs hprim ?_
  intro n hn
  have := hfresh n hn
  simp [stmtUsesVar, placeField_expr, usesVar] at this
  exact this.1

/-- The memory source is a reference, so this one keeps its side
condition; see `fieldWriteResolveStorage_ref_sound`. -/
theorem memoryToStorageUnfoldLeftFstTarget_sound
    (s : State) (ty : Ty) (path : WrappedExpr) (fld : Field)
    (rhs : WrappedExpr) {sv : SVal}
    (hcond : (ruleEffect .memoryToStorageUnfoldLeftFstTarget).cond
      (Stmt.assign (PlaceExpr.field Kind.storage ty path fld) rhs))
    (hnp : rhs.ty.isPrimitive = false)
    (hfresh : ∀ n ∈ aliasNames,
      stmtUsesVar
        (Stmt.assign (PlaceExpr.field Kind.storage ty path fld) rhs) n =
        false)
    (hev : rhsToSVal s rhs = .ok (s, sv))
    (hstable : ∀ {t : State} {root : Name} {segs : List Seg},
      resolveS s path = .ok (t, root, segs) ->
        rhsToSVal t rhs = .ok (t, sv)) :
    ResultsAgree aliasNames
      (execStmt s
        (Stmt.assign (PlaceExpr.field Kind.storage ty path fld) rhs))
      (execBlock s
        ((ruleEffect .memoryToStorageUnfoldLeftFstTarget).block
          (Stmt.assign (PlaceExpr.field Kind.storage ty path fld) rhs)
          hcond)) := by
  exact fieldWriteResolveStorage_ref_sound s ty path fld rhs hnp
    (fun n hn => by
      have := hfresh n hn
      simp [stmtUsesVar] at this
      exact this.2)
    (pure_of_simple hcond.2.2) hev hstable

/-- `values[i++] = i` under the left-fst rule: no `hev`, no `hstable`,
no `pureExpr index`. -/
theorem storageIndexWriteUnfoldLeftFst_sound
    (s : State) (ty : Ty) (path index : WrappedExpr)
    (rhs : WrappedExpr)
    (hcond : (ruleEffect .storageIndexWriteUnfoldLeftFst).cond
      (Stmt.assign (PlaceExpr.index Kind.storage ty path index) rhs))
    (hprim : rhs.ty.isPrimitive = true)
    (hfresh : ∀ n ∈ aliasNames,
      stmtUsesVar
        (Stmt.assign (PlaceExpr.index Kind.storage ty path index) rhs) n =
        false) :
    ResultsAgree aliasNames
      (execStmt s
        (Stmt.assign (PlaceExpr.index Kind.storage ty path index) rhs))
      (execBlock s
        ((ruleEffect .storageIndexWriteUnfoldLeftFst).block
          (Stmt.assign (PlaceExpr.index Kind.storage ty path index) rhs)
          hcond)) := by
  refine indexWriteResolveStorage_sound s ty path index rhs hprim ?_ ?_ <;>
    intro n hn <;> have := hfresh n hn <;>
    simp [stmtUsesVar, placeIndex_expr, usesVar] at this
  · exact this.1.1
  · exact this.1.2

/-- **`values[i++] = i` is sound now.**  `captureIndexTargetBlock` is
`indexWriteResolveBlock`, so this is the same template; the hypothesis
`pureExpr index`, which is exactly what excluded the counterexample, is
gone. -/
theorem storageIndexWriteUnfoldLeftSndIndex_sound
    (s : State) (ty : Ty) (path index rhs : WrappedExpr)
    (hcond : (ruleEffect .storageIndexWriteUnfoldLeftSndIndex).cond
      (Stmt.assign (PlaceExpr.index Kind.storage ty path index) rhs))
    (hprim : rhs.ty.isPrimitive = true)
    (hfresh : ∀ n ∈ aliasNames,
      stmtUsesVar
        (Stmt.assign (PlaceExpr.index Kind.storage ty path index) rhs) n =
        false) :
    ResultsAgree aliasNames
      (execStmt s
        (Stmt.assign (PlaceExpr.index Kind.storage ty path index) rhs))
      (execBlock s
        ((ruleEffect .storageIndexWriteUnfoldLeftSndIndex).block
          (Stmt.assign (PlaceExpr.index Kind.storage ty path index) rhs)
          hcond)) := by
  refine indexWriteResolveStorage_sound s ty path index rhs hprim ?_ ?_ <;>
    intro n hn <;> have := hfresh n hn <;>
    simp [stmtUsesVar, placeIndex_expr, usesVar] at this
  · exact this.1.1
  · exact this.1.2

/-- `memoryToStorageUnfoldLeftSndTargetIndex`: a storage index target with a
complex index and a *memory* right-hand side.

The residual is `captureIndexTargetBlock`, which is `indexWriteResolveBlock`, so
on a **primitive**-typed memory source this is the same statement as
`storageIndexWriteUnfoldLeftSndIndex_sound` and dispatches to the same template:
`freezeRhs` binds the value into `rv` before the path and index captures run, so
no non-interference hypothesis is needed.

**`hprim` is a carve-out, and what it carves out is the interpreter.**  The
rule's own condition is `isSimple path ∧ isComplex index ∧ isMemory rhs ∧
isSimple rhs` — it says nothing about primitivity — so the rule also fires on a
*reference*-typed memory source, and on that instance this theorem says
nothing.  It is not merely unproved there: as stated against this interpreter
it is false.  `Counterexamples/RefSourceOrder.lean` refutes it on
`people[carol.age++] = carol`, where the index mutates the very object the
source copies.

**The rule is not what is wrong there.**  That program runs on a real EVM as
solkey's `TestSuite.storageIndexWriteRefSourceImpureIndex`
(`SolidityRuntimeExecutionTest`), and the chain agrees with the *residual*:
solc is right-hand-side-first for a primitive source, but for a struct source
it resolves the target slot first and copies member by member, so the index has
already run.  `Semantics.execAssignNested` is uniformly value-first and is
therefore unfaithful to solc on reference sources.

So `hprim` marks the shapes on which the interpreter — the thing every theorem
in this file is stated against — cannot express the intended claim.  It is
unlike the `hev`/`hstable` it replaced, which assumed away real interference.
The repair is in `Semantics`, not in `cond`: make the assignment target-first
for reference sources, then restate this theorem without `hprim`.  Not done;
`Rules.freezeRhs` correctly stays out of it either way, since a reference
snapshot would have to be a `Stmt.memoryDecl` and that binds `Binding.mref`,
an alias rather than a copy. -/
theorem memoryToStorageUnfoldLeftSndTargetIndex_sound
    (s : State) (ty : Ty) (path index rhs : WrappedExpr)
    (hcond : (ruleEffect .memoryToStorageUnfoldLeftSndTargetIndex).cond
      (Stmt.assign (PlaceExpr.index Kind.storage ty path index) rhs))
    (hprim : rhs.ty.isPrimitive = true)
    (hfresh : ∀ n ∈ aliasNames,
      stmtUsesVar
        (Stmt.assign (PlaceExpr.index Kind.storage ty path index) rhs) n =
        false) :
    ResultsAgree aliasNames
      (execStmt s
        (Stmt.assign (PlaceExpr.index Kind.storage ty path index) rhs))
      (execBlock s
        ((ruleEffect .memoryToStorageUnfoldLeftSndTargetIndex).block
          (Stmt.assign (PlaceExpr.index Kind.storage ty path index) rhs)
          hcond)) := by
  refine indexWriteResolveStorage_sound s ty path index rhs hprim ?_ ?_ <;>
    intro n hn <;> have := hfresh n hn <;>
    simp [stmtUsesVar, placeIndex_expr, usesVar] at this
  · exact this.1.1
  · exact this.1.2

/-- Transport a pure, fresh place resolution along an env-agreement. -/
theorem resolveLoc_transport {ns : List Name} {s t' : State}
    {e : WrappedExpr} {loc : Loc}
    (hagree : EnvAgreeExcept ns s t')
    (hf : ∀ n ∈ ns, usesVar e n = false)
    (hp : pureExpr e = true)
    (hbase : resolveLoc s e = .ok (s, loc)) :
    resolveLoc t' e = .ok (t', loc) := by
  have h := resolveLoc_agree hagree e hf
  rw [hbase] at h
  rcases h.cases with ⟨err, h1, h2⟩ | ⟨u₁, u₂, a, h1, h2, hu⟩
  · exact nomatch h1
  · have ha : a = loc := (congrArg Prod.snd (Except.ok.inj h1)).symm
    have hu2 : u₂ = t' := resolveLoc_pure hp h2
    rw [h2, hu2, ha]

/-! ## Computation lemmas for assignments with primitive right-hand
sides

Under solc's RHS-first order the right-hand side computes first; these
lemmas evaluate `execAssign` given the evaluation's outcome and the
target's (kind-coherent) resolution, expressing the write through
`writeLoc`. -/

/-- Invert a primitive `rhsToSVal`. -/
theorem rhsToSValPrim_inv {s u : State} {rhs : WrappedExpr} {x : SVal}
    (hprim : rhs.ty.isPrimitive = true)
    (h : rhsToSVal s rhs = .ok (u, x)) :
    ∃ v, evalValue s rhs = .ok (u, v) ∧ x = Value.toSVal v := by
  rw [rhsToSVal, if_pos hprim] at h
  obtain ⟨⟨u', v⟩, h1, h2⟩ := bind_ok_inv h
  cases h2
  exact ⟨v, h1, rfl⟩

/-- Invert a primitive `rhsToMVal`. -/
theorem rhsToMValPrim_inv {s u : State} {rhs : WrappedExpr} {x : MVal}
    (hprim : rhs.ty.isPrimitive = true)
    (h : rhsToMVal s rhs = .ok (u, x)) :
    ∃ v, evalValue s rhs = .ok (u, v) ∧ x = Value.toMVal v := by
  rw [rhsToMVal, if_pos hprim] at h
  obtain ⟨⟨u', v⟩, h1, h2⟩ := bind_ok_inv h
  cases h2
  exact ⟨v, h1, rfl⟩

/-- Nested assignment with a primitive right-hand side that fails:
the failure propagates (the reader runs first). -/
theorem execAssignNested_evalErr {s : State} {e rhs : WrappedExpr}
    {loc : Loc} {err : Halt}
    (h₁ : resolveLoc s e = .ok (s, loc))
    (hnv : ∀ kind ty fld, e ≠ WrappedExpr.var kind ty fld)
    (hprim : rhs.ty.isPrimitive = true)
    (hev : evalValue s rhs = .error err) :
    execAssignNested s e rhs = .error err := by
  rw [execAssignNested]
  have hlk := resolveLoc_kind h₁
  cases hk : e.kind with
  | storage =>
      rw [rhsToSVal, if_pos hprim, hev]
      rfl
  | memory =>
      rw [rhsToMVal, if_pos hprim, hev]
      rfl
  | stack =>
      rw [hk] at hlk
      cases loc with
      | stack n =>
          obtain ⟨k', t', f', he⟩ :=
            resolveLoc_rootLoc_var h₁ (Or.inl ⟨n, rfl⟩)
          exact absurd he (hnv _ _ _)
      | storageLocal n => exact nomatch hlk
      | memoryRoot n => exact nomatch hlk
      | storage root segs => exact nomatch hlk
      | memoryField id fld => exact nomatch hlk
      | memoryIndex id i => exact nomatch hlk

/-- Nested assignment with a primitive right-hand side that succeeds:
the assignment is the `writeLoc` at the post-evaluation resolution. -/
theorem execAssignNested_evalOkPrim {s u : State} {e rhs : WrappedExpr}
    {loc : Loc} {v : Value}
    (hloc : resolveLoc u e = .ok (u, loc))
    (hnv : ∀ kind ty fld, e ≠ WrappedExpr.var kind ty fld)
    (hprim : rhs.ty.isPrimitive = true)
    (hev : evalValue s rhs = .ok (u, v)) :
    execAssignNested s e rhs = writeLoc u loc v := by
  rw [execAssignNested]
  have hlk := resolveLoc_kind hloc
  cases hk : e.kind with
  | storage =>
      rw [rhsToSVal, if_pos hprim, hev]
      simp only [resOk_bind]
      rw [hloc]
      simp only [resOk_bind]
      rw [hk] at hlk
      cases loc with
      | storage root segs => rfl
      | stack n => exact nomatch hlk
      | storageLocal n =>
          obtain ⟨k', t', f', he⟩ :=
            resolveLoc_rootLoc_var hloc (Or.inr (Or.inl ⟨n, rfl⟩))
          exact absurd he (hnv _ _ _)
      | memoryRoot n => exact nomatch hlk
      | memoryField id fld => exact nomatch hlk
      | memoryIndex id i => exact nomatch hlk
  | memory =>
      rw [rhsToMVal, if_pos hprim, hev]
      simp only [resOk_bind]
      rw [hloc]
      simp only [resOk_bind]
      rw [hk] at hlk
      cases loc with
      | memoryField id fld => rfl
      | memoryIndex id i => rfl
      | memoryRoot n =>
          obtain ⟨k', t', f', he⟩ :=
            resolveLoc_rootLoc_var hloc (Or.inr (Or.inr ⟨n, rfl⟩))
          exact absurd he (hnv _ _ _)
      | stack n => exact nomatch hlk
      | storageLocal n => exact nomatch hlk
      | storage root segs => exact nomatch hlk
  | stack =>
      rw [hk] at hlk
      cases loc with
      | stack n =>
          obtain ⟨k', t', f', he⟩ :=
            resolveLoc_rootLoc_var hloc (Or.inl ⟨n, rfl⟩)
          exact absurd he (hnv _ _ _)
      | storageLocal n => exact nomatch hlk
      | memoryRoot n => exact nomatch hlk
      | storage root segs => exact nomatch hlk
      | memoryField id fld => exact nomatch hlk
      | memoryIndex id i => exact nomatch hlk

/-- A primitive-RHS assignment whose right-hand side fails: the
failure propagates. Alias-rebinding targets are excluded (ill-typed
for a primitive source). -/
theorem execAssign_evalErr {s : State} {lhs : PlaceExpr}
    {rhs : WrappedExpr} {loc : Loc} {err : Halt}
    (h₁ : resolveLoc s lhs.expr = .ok (s, loc))
    (hprim : rhs.ty.isPrimitive = true)
    (hnsl : ∀ nm, loc ≠ Loc.storageLocal nm)
    (hnmr : ∀ nm, loc ≠ Loc.memoryRoot nm)
    (hev : evalValue s rhs = .error err) :
    execAssign s lhs rhs = .error err := by
  rw [execAssign]
  match hsh : lhs.expr with
  | .var kind ty fld =>
      rw [hsh] at h₁
      cases kind with
      | stack => rw [hev]; rfl
      | storage =>
          by_cases ho : fld.origin = some StorageOrigin.global
          · simp only [if_pos ho]
            rw [rhsToSVal, if_pos hprim, hev]
            rfl
          · rw [resolveLoc, if_neg ho] at h₁
            cases h₁
            exact absurd rfl (hnsl fld.name)
      | memory =>
          rw [resolveLoc] at h₁
          cases h₁
          exact absurd rfl (hnmr fld.name)
  | .field kind ty base fld =>
      rw [hsh] at h₁
      exact execAssignNested_evalErr h₁ (fun _ _ _ h => nomatch h) hprim hev
  | .index kind ty base index =>
      rw [hsh] at h₁
      exact execAssignNested_evalErr h₁ (fun _ _ _ h => nomatch h) hprim hev
  | .pushPlace target =>
      rw [hsh] at h₁
      exact execAssignNested_evalErr h₁ (fun _ _ _ h => nomatch h) hprim hev
  | .bool b =>
      rw [hsh, resolveLoc.eq_def] at h₁
      exact nomatch h₁
  | .intLit ty v =>
      rw [hsh, resolveLoc.eq_def] at h₁
      exact nomatch h₁
  | .mkCall kind ty nm args =>
      rw [hsh, resolveLoc.eq_def] at h₁
      exact nomatch h₁
  | .mkBinop op l r =>
      rw [hsh, resolveLoc.eq_def] at h₁
      exact nomatch h₁
  | .mkUnop op arg =>
      rw [hsh, resolveLoc.eq_def] at h₁
      exact nomatch h₁
  | .mkIncDec op target =>
      rw [hsh, resolveLoc.eq_def] at h₁
      exact nomatch h₁
  | .mkTernary c t el =>
      rw [hsh, resolveLoc.eq_def] at h₁
      exact nomatch h₁

/-- A primitive-RHS assignment whose right-hand side succeeds: the
assignment is the `writeLoc` at the post-evaluation resolution. -/
theorem execAssign_evalOkPrim {s u : State} {lhs : PlaceExpr}
    {rhs : WrappedExpr} {loc : Loc} {v : Value}
    (h₁ : resolveLoc s lhs.expr = .ok (s, loc))
    (hloc : resolveLoc u lhs.expr = .ok (u, loc))
    (hprim : rhs.ty.isPrimitive = true)
    (hnsl : ∀ nm, loc ≠ Loc.storageLocal nm)
    (hnmr : ∀ nm, loc ≠ Loc.memoryRoot nm)
    (hev : evalValue s rhs = .ok (u, v)) :
    execAssign s lhs rhs = writeLoc u loc v := by
  rw [execAssign]
  match hsh : lhs.expr with
  | .var kind ty fld =>
      rw [hsh] at h₁ hloc
      cases kind with
      | stack =>
          rw [resolveLoc] at hloc
          cases hloc
          rw [hev]
          rfl
      | storage =>
          by_cases ho : fld.origin = some StorageOrigin.global
          · simp only [if_pos ho]
            rw [resolveLoc, if_pos ho] at hloc
            cases hloc
            rw [rhsToSVal, if_pos hprim, hev]
            rfl
          · rw [resolveLoc, if_neg ho] at h₁
            cases h₁
            exact absurd rfl (hnsl fld.name)
      | memory =>
          rw [resolveLoc] at h₁
          cases h₁
          exact absurd rfl (hnmr fld.name)
  | .field kind ty base fld =>
      rw [hsh] at hloc
      exact execAssignNested_evalOkPrim hloc (fun _ _ _ h => nomatch h)
        hprim hev
  | .index kind ty base index =>
      rw [hsh] at hloc
      exact execAssignNested_evalOkPrim hloc (fun _ _ _ h => nomatch h)
        hprim hev
  | .pushPlace target =>
      rw [hsh] at hloc
      exact execAssignNested_evalOkPrim hloc (fun _ _ _ h => nomatch h)
        hprim hev
  | .bool b =>
      rw [hsh, resolveLoc.eq_def] at h₁
      exact nomatch h₁
  | .intLit ty v =>
      rw [hsh, resolveLoc.eq_def] at h₁
      exact nomatch h₁
  | .mkCall kind ty nm args =>
      rw [hsh, resolveLoc.eq_def] at h₁
      exact nomatch h₁
  | .mkBinop op l r =>
      rw [hsh, resolveLoc.eq_def] at h₁
      exact nomatch h₁
  | .mkUnop op arg =>
      rw [hsh, resolveLoc.eq_def] at h₁
      exact nomatch h₁
  | .mkIncDec op target =>
      rw [hsh, resolveLoc.eq_def] at h₁
      exact nomatch h₁
  | .mkTernary c t el =>
      rw [hsh, resolveLoc.eq_def] at h₁
      exact nomatch h₁

/-- Assignment to a stack variable: the write is the environment
re-binding after the right-hand side evaluates, whatever the
right-hand side. -/
theorem execAssign_stackVar {s : State} {lhs : PlaceExpr}
    {rhs : WrappedExpr} {name : Name}
    (h : ∀ u : State, resolveLoc u lhs.expr = .ok (u, Loc.stack name)) :
    execAssign s lhs rhs =
      (evalValue s rhs) >>= fun x =>
        match x with
        | (u, v) => Except.ok (u.setEnv name (Binding.val v)) := by
  rw [execAssign]
  match hsh : lhs.expr with
  | .var kind ty fld =>
      have h' := h s
      rw [hsh] at h'
      cases kind with
      | stack =>
          rw [resolveLoc] at h'
          cases h'
          rfl
      | storage =>
          rw [resolveLoc] at h'
          by_cases ho : fld.origin = some StorageOrigin.global
          · rw [if_pos ho] at h'
            exact absurd h' (by simp)
          · rw [if_neg ho] at h'
            exact absurd h' (by simp)
      | memory =>
          rw [resolveLoc] at h'
          exact absurd h' (by simp)
  | .field kindE tyE base fldE =>
      have h' := h s
      rw [hsh] at h'
      obtain ⟨k', t', f', he⟩ := resolveLoc_rootLoc_var h' (Or.inl ⟨name, rfl⟩)
      exact nomatch he
  | .index kindE tyE base index =>
      have h' := h s
      rw [hsh] at h'
      obtain ⟨k', t', f', he⟩ := resolveLoc_rootLoc_var h' (Or.inl ⟨name, rfl⟩)
      exact nomatch he
  | .pushPlace target =>
      have h' := h s
      rw [hsh] at h'
      obtain ⟨k', t', f', he⟩ := resolveLoc_rootLoc_var h' (Or.inl ⟨name, rfl⟩)
      exact nomatch he
  | .bool b =>
      have h' := h s
      rw [hsh, resolveLoc.eq_def] at h'
      exact nomatch h'
  | .intLit tyI v =>
      have h' := h s
      rw [hsh, resolveLoc.eq_def] at h'
      exact nomatch h'
  | .mkCall kindE tyE nm args =>
      have h' := h s
      rw [hsh, resolveLoc.eq_def] at h'
      exact nomatch h'
  | .mkBinop op l r =>
      have h' := h s
      rw [hsh, resolveLoc.eq_def] at h'
      exact nomatch h'
  | .mkUnop op arg =>
      have h' := h s
      rw [hsh, resolveLoc.eq_def] at h'
      exact nomatch h'
  | .mkIncDec op target =>
      have h' := h s
      rw [hsh, resolveLoc.eq_def] at h'
      exact nomatch h'
  | .mkTernary c t el =>
      have h' := h s
      rw [hsh, resolveLoc.eq_def] at h'
      exact nomatch h'

/-- The workhorse for the right-hand-side unfold rules: the assignment
target (the same expression on both sides, fresh for the scratch
names) resolves in the first initial state, the captured right-hand
side has the same type and data location as the original, and it
simulates the original under evaluation, storage resolution, and
memory read. Nested targets need only resolution *congruence*: solc's
RHS-first order runs the readers first, and the simulation hands both
sides agreeing intermediate states. -/
theorem execAssign_pureLocSim {ns : List Name} {s₁ s₂ : State}
    {lhs : PlaceExpr} {rhs₁ rhs₂ : WrappedExpr} {loc : Loc}
    (h₁ : resolveLoc s₁ lhs.expr = .ok (s₁, loc))
    (hfl : ∀ n ∈ ns, usesVar lhs.expr n = false)
    (hty : rhs₂.ty = rhs₁.ty) (hkind : rhs₂.kind = rhs₁.kind)
    (heval : ResAgree ns (evalValue s₁ rhs₁) (evalValue s₂ rhs₂))
    (hres : rhs₁.kind = Kind.storage ∨ (∃ nm, loc = Loc.storageLocal nm) ->
      ResAgree ns (resolveS s₁ rhs₁) (resolveS s₂ rhs₂))
    (hread : rhs₁.kind = Kind.memory ->
      ResAgree ns (readM s₁ rhs₁) (readM s₂ rhs₂)) :
    ResultsAgree ns (execAssign s₁ lhs rhs₁) (execAssign s₂ lhs rhs₂) := by
  have hsimS : ResAgree ns (rhsToSVal s₁ rhs₁) (rhsToSVal s₂ rhs₂) := by
    rw [rhsToSVal, rhsToSVal, hty, hkind]
    cases hp : rhs₁.ty.isPrimitive with
    | true =>
        refine ResAgree.bind heval ?_
        intro u₁ u₂ v hu
        exact ⟨rfl, hu⟩
    | false =>
        match hk : rhs₁.kind with
        | Kind.storage =>
            cases hm : tyHasMapping rhs₁.ty with
            | true => exact rfl
            | false =>
                refine ResAgree.bind (hres (Or.inl hk)) ?_
                intro u₁ u₂ a hu
                obtain ⟨rroot, rsegs⟩ := a
                simp only [findStorage_congr hu]
                exact bindPureRes_agree _ fun v => ⟨rfl, hu⟩
        | Kind.memory =>
            refine ResAgree.bind (hread hk) ?_
            intro u₁ u₂ mv hu
            simp only [copyMem_congr hu]
            exact bindPureRes_agree _ fun sval => ⟨rfl, hu⟩
        | Kind.stack => exact rfl
  have hsimM : ResAgree ns (rhsToMVal s₁ rhs₁) (rhsToMVal s₂ rhs₂) := by
    rw [rhsToMVal, rhsToMVal, hty, hkind]
    cases hp : rhs₁.ty.isPrimitive with
    | true =>
        refine ResAgree.bind heval ?_
        intro u₁ u₂ v hu
        exact ⟨rfl, hu⟩
    | false =>
        match hk : rhs₁.kind with
        | Kind.storage =>
            refine ResAgree.bind (hres (Or.inl hk)) ?_
            intro u₁ u₂ a hu
            obtain ⟨rroot, rsegs⟩ := a
            simp only [findStorage_congr hu]
            refine bindPureRes_agree _ fun sval => ?_
            exact copyStToM_agree hu sval
        | Kind.memory => exact hread hk
        | Kind.stack => exact rfl
  rw [execAssign, execAssign]
  match hsh : lhs.expr with
  | .var kind ty fld =>
      rw [hsh] at h₁
      cases kind with
      | stack =>
          refine ResAgree.bindState heval ?_
          intro u₁ u₂ v hu
          exact hu.setEnv_both fld.name (Binding.val v)
      | storage =>
          by_cases ho : fld.origin = some StorageOrigin.global
          · simp only [if_pos ho]
            refine ResAgree.bindState hsimS ?_
            intro u₁ u₂ sv hu
            exact saveStorage_agree hu fld.name [] sv
          · simp only [if_neg ho]
            rw [resolveLoc, if_neg ho] at h₁
            cases h₁
            refine ResAgree.bindState (hres (Or.inr ⟨fld.name, rfl⟩)) ?_
            intro u₁ u₂ a hu
            obtain ⟨root, segs⟩ := a
            exact hu.setEnv_both fld.name (Binding.spath root segs)
      | memory =>
          rw [hkind]
          match hk : rhs₁.kind with
          | Kind.memory =>
              refine ResAgree.bindState (hread hk) ?_
              intro u₁ u₂ mv hu
              cases mv with
              | ref id => exact hu.setEnv_both fld.name (Binding.mref id)
              | prim p => cases p <;> exact rfl
          | Kind.storage =>
              refine ResAgree.bindState (hres (Or.inl hk)) ?_
              intro u₁ u₂ a hu
              obtain ⟨root, segs⟩ := a
              simp only [findStorage_congr hu]
              refine bindPureResults_agree _ fun sval => ?_
              refine ResAgree.bindState (copyStToM_agree hu sval) ?_
              intro w₁ w₂ mv hw
              cases mv with
              | ref id => exact hw.setEnv_both fld.name (Binding.mref id)
              | prim p => cases p <;> exact rfl
          | Kind.stack => exact rfl
  | .field kindE tyE base fldE =>
      rw [hsh] at hfl
      exact pureLocSimNested hfl hsimS hsimM
  | .index kindE tyE base index =>
      rw [hsh] at hfl
      exact pureLocSimNested hfl hsimS hsimM
  | .pushPlace target =>
      rw [hsh] at hfl
      exact pureLocSimNested hfl hsimS hsimM
  | .bool b => rw [hsh, resolveLoc.eq_def] at h₁; exact nomatch h₁
  | .intLit tyI v => rw [hsh, resolveLoc.eq_def] at h₁; exact nomatch h₁
  | .mkCall kindE tyE nm args =>
      rw [hsh] at hfl
      exact pureLocSimNested hfl hsimS hsimM
  | .mkBinop op l r => rw [hsh, resolveLoc.eq_def] at h₁; exact nomatch h₁
  | .mkUnop op arg => rw [hsh, resolveLoc.eq_def] at h₁; exact nomatch h₁
  | .mkIncDec op target =>
      rw [hsh, resolveLoc.eq_def] at h₁; exact nomatch h₁
  | .mkTernary c t el =>
      rw [hsh, resolveLoc.eq_def] at h₁; exact nomatch h₁
where
  pureLocSimNested {ns : List Name} {s₁ s₂ : State} {e : WrappedExpr}
      {rhs₁ rhs₂ : WrappedExpr}
      (hfl : ∀ n ∈ ns, usesVar e n = false)
      (hsimS : ResAgree ns (rhsToSVal s₁ rhs₁) (rhsToSVal s₂ rhs₂))
      (hsimM : ResAgree ns (rhsToMVal s₁ rhs₁) (rhsToMVal s₂ rhs₂)) :
      ResultsAgree ns (execAssignNested s₁ e rhs₁)
        (execAssignNested s₂ e rhs₂) := by
    rw [execAssignNested, execAssignNested]
    cases hk : e.kind with
    | storage =>
        refine ResAgree.bindState hsimS ?_
        intro u₁ u₂ sv hu
        refine ResAgree.bindState (resolveLoc_agree hu e hfl) ?_
        intro w₁ w₂ loc' hw
        cases loc' with
        | storage root segs => exact saveStorage_agree hw root segs sv
        | stack n => exact rfl
        | storageLocal n => exact rfl
        | memoryRoot n => exact rfl
        | memoryField id fld => exact rfl
        | memoryIndex id i => exact rfl
    | memory =>
        refine ResAgree.bindState hsimM ?_
        intro u₁ u₂ mv hu
        refine ResAgree.bindState (resolveLoc_agree hu e hfl) ?_
        intro w₁ w₂ loc' hw
        cases loc' with
        | memoryField id fld =>
            simp only [getObj_congr hw]
            refine bindPureResults_agree _ fun obj => ?_
            cases obj with
            | array elems => exact rfl
            | struct fields => exact setObj_agree hw id _
        | memoryIndex id i =>
            simp only [getObj_congr hw]
            refine bindPureResults_agree _ fun obj => ?_
            cases obj with
            | struct fields => exact rfl
            | array elems =>
                by_cases hb : 0 ≤ i ∧ i.toNat < elems.length
                · simp only [if_pos hb]
                  exact setObj_agree hw id _
                · simp only [if_neg hb]
                  exact rfl
        | stack n => exact rfl
        | storageLocal n => exact rfl
        | memoryRoot n => exact rfl
        | storage root segs => exact rfl
    | stack => exact rfl

/-- Variant of `execAssign_pureLocSim` for primitive-typed right-hand
sides: only the evaluation simulation is needed, at the price of
excluding the (ill-typed for a primitive source) rebinding targets. -/
theorem execAssign_pureLocSimPrim {ns : List Name} {s₁ s₂ : State}
    {lhs : PlaceExpr} {rhs₁ rhs₂ : WrappedExpr} {loc : Loc}
    (h₁ : resolveLoc s₁ lhs.expr = .ok (s₁, loc))
    (hfl : ∀ n ∈ ns, usesVar lhs.expr n = false)
    (hty : rhs₂.ty = rhs₁.ty) (hprim : rhs₁.ty.isPrimitive = true)
    (heval : ResAgree ns (evalValue s₁ rhs₁) (evalValue s₂ rhs₂))
    (hnsl : ∀ nm, loc ≠ Loc.storageLocal nm)
    (hnmr : ∀ nm, loc ≠ Loc.memoryRoot nm) :
    ResultsAgree ns (execAssign s₁ lhs rhs₁) (execAssign s₂ lhs rhs₂) := by
  have hprim₂ : rhs₂.ty.isPrimitive = true := by rw [hty]; exact hprim
  have hsimS : ResAgree ns (rhsToSVal s₁ rhs₁) (rhsToSVal s₂ rhs₂) := by
    rw [rhsToSVal, rhsToSVal, if_pos hprim, if_pos hprim₂]
    refine ResAgree.bind heval ?_
    intro u₁ u₂ v hu
    exact ⟨rfl, hu⟩
  have hsimM : ResAgree ns (rhsToMVal s₁ rhs₁) (rhsToMVal s₂ rhs₂) := by
    rw [rhsToMVal, rhsToMVal, if_pos hprim, if_pos hprim₂]
    refine ResAgree.bind heval ?_
    intro u₁ u₂ v hu
    exact ⟨rfl, hu⟩
  rw [execAssign, execAssign]
  match hsh : lhs.expr with
  | .var kind ty fld =>
      rw [hsh] at h₁
      cases kind with
      | stack =>
          refine ResAgree.bindState heval ?_
          intro u₁ u₂ v hu
          exact hu.setEnv_both fld.name (Binding.val v)
      | storage =>
          by_cases ho : fld.origin = some StorageOrigin.global
          · simp only [if_pos ho]
            refine ResAgree.bindState hsimS ?_
            intro u₁ u₂ sv hu
            exact saveStorage_agree hu fld.name [] sv
          · rw [resolveLoc, if_neg ho] at h₁
            cases h₁
            exact absurd rfl (hnsl fld.name)
      | memory =>
          rw [resolveLoc] at h₁
          cases h₁
          exact absurd rfl (hnmr fld.name)
  | .field kindE tyE base fldE =>
      rw [hsh] at hfl
      exact execAssign_pureLocSim.pureLocSimNested hfl hsimS hsimM
  | .index kindE tyE base index =>
      rw [hsh] at hfl
      exact execAssign_pureLocSim.pureLocSimNested hfl hsimS hsimM
  | .pushPlace target =>
      rw [hsh] at hfl
      exact execAssign_pureLocSim.pureLocSimNested hfl hsimS hsimM
  | .bool b => rw [hsh, resolveLoc.eq_def] at h₁; exact nomatch h₁
  | .intLit tyI v => rw [hsh, resolveLoc.eq_def] at h₁; exact nomatch h₁
  | .mkCall kindE tyE nm args =>
      rw [hsh] at hfl
      exact execAssign_pureLocSim.pureLocSimNested hfl hsimS hsimM
  | .mkBinop op l r => rw [hsh, resolveLoc.eq_def] at h₁; exact nomatch h₁
  | .mkUnop op arg => rw [hsh, resolveLoc.eq_def] at h₁; exact nomatch h₁
  | .mkIncDec op target =>
      rw [hsh, resolveLoc.eq_def] at h₁; exact nomatch h₁
  | .mkTernary c t el =>
      rw [hsh, resolveLoc.eq_def] at h₁; exact nomatch h₁

/-- A storage-kind right-hand side whose resolution fails makes the
assignment fail: solc's RHS-first order runs the reader before the
target resolves. -/
theorem execAssignNested_storageRhsErr {s : State} {e rhs : WrappedExpr}
    {loc : Loc} {err : Halt}
    (hlhs : resolveLoc s e = .ok (s, loc))
    (hnv : ∀ kind ty fld, e ≠ WrappedExpr.var kind ty fld)
    (hkind : rhs.kind = Kind.storage)
    (hnm : tyHasMapping rhs.ty = false)
    (hevalEq : ∀ u : State, evalValue u rhs =
      (resolveS u rhs) >>= fun x =>
        (x.1.findStorage x.2.1 x.2.2) >>= fun v =>
          v.asValue >>= fun val => Except.ok (x.1, val))
    (hcap : resolveS s rhs = .error err) :
    execAssignNested s e rhs = .error err := by
  rw [execAssignNested]
  have hlk := resolveLoc_kind hlhs
  cases hk : e.kind with
  | storage =>
      rw [rhsToSVal]
      by_cases hp : rhs.ty.isPrimitive = true
      · rw [if_pos hp, hevalEq s, hcap]
        rfl
      · rw [if_neg hp, hkind,
          if_neg (show ¬ tyHasMapping rhs.ty = true by simp [hnm]), hcap]
        rfl
  | memory =>
      rw [rhsToMVal]
      by_cases hp : rhs.ty.isPrimitive = true
      · rw [if_pos hp, hevalEq s, hcap]
        rfl
      · rw [if_neg hp, hkind, hcap]
        rfl
  | stack =>
      rw [hk] at hlk
      cases loc with
      | stack n =>
          obtain ⟨k', t', f', he⟩ :=
            resolveLoc_rootLoc_var hlhs (Or.inl ⟨n, rfl⟩)
          exact absurd he (hnv _ _ _)
      | storageLocal n => exact nomatch hlk
      | memoryRoot n => exact nomatch hlk
      | storage root segs => exact nomatch hlk
      | memoryField id fld => exact nomatch hlk
      | memoryIndex id i => exact nomatch hlk

theorem execAssign_storageRhsErr {s : State} {lhs : PlaceExpr}
    {rhs : WrappedExpr} {loc : Loc} {err : Halt}
    (hlhs : resolveLoc s lhs.expr = .ok (s, loc))
    (hkind : rhs.kind = Kind.storage)
    (hnm : tyHasMapping rhs.ty = false)
    (hevalEq : ∀ u : State, evalValue u rhs =
      (resolveS u rhs) >>= fun x =>
        (x.1.findStorage x.2.1 x.2.2) >>= fun v =>
          v.asValue >>= fun val => Except.ok (x.1, val))
    (hcap : resolveS s rhs = .error err) :
    execAssign s lhs rhs = .error err := by
  rw [execAssign]
  match hsh : lhs.expr with
  | .var kind ty fld =>
      rw [hsh] at hlhs
      cases kind with
      | stack => rw [hevalEq s, hcap]; rfl
      | storage =>
          by_cases ho : fld.origin = some StorageOrigin.global
          · simp only [if_pos ho]
            rw [rhsToSVal]
            by_cases hp : rhs.ty.isPrimitive = true
            · rw [if_pos hp, hevalEq s, hcap]
              rfl
            · rw [if_neg hp, hkind,
                if_neg (show ¬ tyHasMapping rhs.ty = true by simp [hnm]),
                hcap]
              rfl
          · simp only [if_neg ho]
            rw [hcap]
            rfl
      | memory =>
          rw [hkind, hcap]
          rfl
  | .field kindE tyE base fldE =>
      rw [hsh] at hlhs
      exact execAssignNested_storageRhsErr hlhs (fun _ _ _ h => nomatch h)
        hkind hnm hevalEq hcap
  | .index kindE tyE base index =>
      rw [hsh] at hlhs
      exact execAssignNested_storageRhsErr hlhs (fun _ _ _ h => nomatch h)
        hkind hnm hevalEq hcap
  | .pushPlace target =>
      rw [hsh] at hlhs
      exact execAssignNested_storageRhsErr hlhs (fun _ _ _ h => nomatch h)
        hkind hnm hevalEq hcap
  | .bool b => rw [hsh, resolveLoc.eq_def] at hlhs; exact nomatch hlhs
  | .intLit tyI v => rw [hsh, resolveLoc.eq_def] at hlhs; exact nomatch hlhs
  | .mkCall kindE tyE nm args =>
      rw [hsh] at hlhs
      exact execAssignNested_storageRhsErr hlhs (fun _ _ _ h => nomatch h)
        hkind hnm hevalEq hcap
  | .mkBinop op l r => rw [hsh, resolveLoc.eq_def] at hlhs; exact nomatch hlhs
  | .mkUnop op arg => rw [hsh, resolveLoc.eq_def] at hlhs; exact nomatch hlhs
  | .mkIncDec op target =>
      rw [hsh, resolveLoc.eq_def] at hlhs; exact nomatch hlhs
  | .mkTernary c t el =>
      rw [hsh, resolveLoc.eq_def] at hlhs; exact nomatch hlhs

/-- `execAssignNested_storageRhsErr` for a *non-primitive* storage
right-hand side: no `hevalEq` bridge is needed because the
`evalValue` path is only taken at primitive types. Serves right-hand
sides `evalValue` cannot read at all (a `pushPlace`). -/
theorem execAssignNested_storageRhsErrNonPrim {s : State}
    {e : WrappedExpr} {rhs : WrappedExpr} {loc : Loc} {err : Halt}
    (hlhs : resolveLoc s e = .ok (s, loc))
    (hnv : ∀ kind ty fld, e ≠ WrappedExpr.var kind ty fld)
    (hkind : rhs.kind = Kind.storage)
    (hprim : rhs.ty.isPrimitive = false)
    (hnm : tyHasMapping rhs.ty = false)
    (hcap : resolveS s rhs = .error err) :
    execAssignNested s e rhs = .error err := by
  rw [execAssignNested]
  have hlk := resolveLoc_kind hlhs
  have hp : ¬ rhs.ty.isPrimitive = true := by simp [hprim]
  cases hk : e.kind with
  | storage =>
      rw [rhsToSVal, if_neg hp, hkind,
        if_neg (show ¬ tyHasMapping rhs.ty = true by simp [hnm]), hcap]
      rfl
  | memory =>
      rw [rhsToMVal, if_neg hp, hkind, hcap]
      rfl
  | stack =>
      rw [hk] at hlk
      cases loc with
      | stack n =>
          obtain ⟨k', t', f', he⟩ :=
            resolveLoc_rootLoc_var hlhs (Or.inl ⟨n, rfl⟩)
          exact absurd he (hnv _ _ _)
      | storageLocal n => exact nomatch hlk
      | memoryRoot n => exact nomatch hlk
      | storage root segs => exact nomatch hlk
      | memoryField id fld => exact nomatch hlk
      | memoryIndex id i => exact nomatch hlk

/-- `execAssign_storageRhsErr` for a *non-primitive* storage right-hand
side (a `pushPlace`, say, which `evalValue` cannot read): instead of
the `hevalEq` bridge it needs the target not to be a stack variable —
the one arm that reads the right-hand side with `evalValue`
unconditionally. -/
theorem execAssign_storageRhsErrNonPrim {s : State} {lhs : PlaceExpr}
    {rhs : WrappedExpr} {loc : Loc} {err : Halt}
    (hlhs : resolveLoc s lhs.expr = .ok (s, loc))
    (hkind : rhs.kind = Kind.storage)
    (hprim : rhs.ty.isPrimitive = false)
    (hnm : tyHasMapping rhs.ty = false)
    (hnst : ∀ nm, loc ≠ Loc.stack nm)
    (hcap : resolveS s rhs = .error err) :
    execAssign s lhs rhs = .error err := by
  have hp : ¬ rhs.ty.isPrimitive = true := by simp [hprim]
  rw [execAssign]
  match hsh : lhs.expr with
  | .var kind ty fld =>
      rw [hsh] at hlhs
      cases kind with
      | stack =>
          rw [resolveLoc] at hlhs
          cases hlhs
          exact absurd rfl (hnst fld.name)
      | storage =>
          by_cases ho : fld.origin = some StorageOrigin.global
          · simp only [if_pos ho]
            rw [rhsToSVal, if_neg hp, hkind,
              if_neg (show ¬ tyHasMapping rhs.ty = true by simp [hnm]),
              hcap]
            rfl
          · simp only [if_neg ho]
            rw [hcap]
            rfl
      | memory =>
          rw [hkind, hcap]
          rfl
  | .field kindE tyE base fldE =>
      rw [hsh] at hlhs
      exact execAssignNested_storageRhsErrNonPrim hlhs
        (fun _ _ _ h => nomatch h) hkind hprim hnm hcap
  | .index kindE tyE base index =>
      rw [hsh] at hlhs
      exact execAssignNested_storageRhsErrNonPrim hlhs
        (fun _ _ _ h => nomatch h) hkind hprim hnm hcap
  | .pushPlace target =>
      rw [hsh] at hlhs
      exact execAssignNested_storageRhsErrNonPrim hlhs
        (fun _ _ _ h => nomatch h) hkind hprim hnm hcap
  | .bool b => rw [hsh, resolveLoc.eq_def] at hlhs; exact nomatch hlhs
  | .intLit tyI v => rw [hsh, resolveLoc.eq_def] at hlhs; exact nomatch hlhs
  | .mkCall kindE tyE nm args =>
      rw [hsh] at hlhs
      exact execAssignNested_storageRhsErrNonPrim hlhs
        (fun _ _ _ h => nomatch h) hkind hprim hnm hcap
  | .mkBinop op l r => rw [hsh, resolveLoc.eq_def] at hlhs; exact nomatch hlhs
  | .mkUnop op arg => rw [hsh, resolveLoc.eq_def] at hlhs; exact nomatch hlhs
  | .mkIncDec op target =>
      rw [hsh, resolveLoc.eq_def] at hlhs; exact nomatch hlhs
  | .mkTernary c t el =>
      rw [hsh, resolveLoc.eq_def] at hlhs; exact nomatch hlhs

/-- A memory-kind right-hand side whose read fails makes the
assignment fail (rebinding targets excluded via `hnsl`). -/
theorem execAssign_memoryRhsErr {s : State} {lhs : PlaceExpr}
    {rhs : WrappedExpr} {loc : Loc} {err : Halt}
    (hlhs : resolveLoc s lhs.expr = .ok (s, loc))
    (hkind : rhs.kind = Kind.memory)
    (hnsl : ∀ nm, loc ≠ Loc.storageLocal nm)
    (hevalEq : ∀ u : State, evalValue u rhs =
      (readM u rhs) >>= fun x =>
        x.2.asValue >>= fun val => Except.ok (x.1, val))
    (hcap : readM s rhs = .error err) :
    execAssign s lhs rhs = .error err := by
  have hnested : ∀ {e : WrappedExpr},
      resolveLoc s e = .ok (s, loc) ->
      (∀ kind ty fld, e ≠ WrappedExpr.var kind ty fld) ->
      execAssignNested s e rhs = .error err := by
    intro e hl hnv
    rw [execAssignNested]
    have hlk := resolveLoc_kind hl
    cases hk : e.kind with
    | storage =>
        rw [rhsToSVal]
        by_cases hp : rhs.ty.isPrimitive = true
        · rw [if_pos hp, hevalEq s, hcap]
          rfl
        · rw [if_neg hp, hkind, hcap]
          rfl
    | memory =>
        rw [rhsToMVal]
        by_cases hp : rhs.ty.isPrimitive = true
        · rw [if_pos hp, hevalEq s, hcap]
          rfl
        · rw [if_neg hp, hkind, hcap]
          rfl
    | stack =>
        rw [hk] at hlk
        cases loc with
        | stack n =>
            obtain ⟨k', t', f', he⟩ :=
              resolveLoc_rootLoc_var hl (Or.inl ⟨n, rfl⟩)
            exact absurd he (hnv _ _ _)
        | storageLocal n => exact nomatch hlk
        | memoryRoot n => exact nomatch hlk
        | storage root segs => exact nomatch hlk
        | memoryField id fld => exact nomatch hlk
        | memoryIndex id i => exact nomatch hlk
  rw [execAssign]
  match hsh : lhs.expr with
  | .var kind ty fld =>
      rw [hsh] at hlhs
      cases kind with
      | stack => rw [hevalEq s, hcap]; rfl
      | storage =>
          by_cases ho : fld.origin = some StorageOrigin.global
          · simp only [if_pos ho]
            rw [rhsToSVal]
            by_cases hp : rhs.ty.isPrimitive = true
            · rw [if_pos hp, hevalEq s, hcap]
              rfl
            · rw [if_neg hp, hkind, hcap]
              rfl
          · rw [resolveLoc, if_neg ho] at hlhs
            cases hlhs
            exact absurd rfl (hnsl fld.name)
      | memory =>
          rw [hkind, hcap]
          rfl
  | .field kindE tyE base fldE =>
      rw [hsh] at hlhs
      exact hnested hlhs (fun _ _ _ h => nomatch h)
  | .index kindE tyE base index =>
      rw [hsh] at hlhs
      exact hnested hlhs (fun _ _ _ h => nomatch h)
  | .pushPlace target =>
      rw [hsh] at hlhs
      exact hnested hlhs (fun _ _ _ h => nomatch h)
  | .bool b => rw [hsh, resolveLoc.eq_def] at hlhs; exact nomatch hlhs
  | .intLit tyI v => rw [hsh, resolveLoc.eq_def] at hlhs; exact nomatch hlhs
  | .mkCall kindE tyE nm args =>
      rw [hsh] at hlhs
      exact hnested hlhs (fun _ _ _ h => nomatch h)
  | .mkBinop op l r => rw [hsh, resolveLoc.eq_def] at hlhs; exact nomatch hlhs
  | .mkUnop op arg => rw [hsh, resolveLoc.eq_def] at hlhs; exact nomatch hlhs
  | .mkIncDec op target =>
      rw [hsh, resolveLoc.eq_def] at hlhs; exact nomatch hlhs
  | .mkTernary c t el =>
      rw [hsh, resolveLoc.eq_def] at hlhs; exact nomatch hlhs

/-- Template: the `pv` value-capture for a storage-kind right-hand
side (`captureAssignBlock` with `valueCaptureKind rhs = Kind.storage`).
The rule hoists the right-hand side in front of the target; both the
right-hand side and the target are pure, so the two orders coincide.
Shared by `storageFieldReadUnfoldRightSndResult` and
`storageIndexReadUnfoldRightSndResult`. -/
theorem captureAssignStorageRhs_sound (s : State) (lhs : PlaceExpr)
    (rhs : WrappedExpr) {loc : Loc}
    (hlhs : resolveLoc s lhs.expr = .ok (s, loc))
    (hplhs : pureExpr lhs.expr = true)
    (hfl : ∀ n ∈ aliasNames, usesVar lhs.expr n = false)
    (hprhs : pureExpr rhs = true)
    (hkind : rhs.kind = Kind.storage)
    (hnm : tyHasMapping rhs.ty = false)
    (hevalEq : ∀ u : State, evalValue u rhs =
      (resolveS u rhs) >>= fun x =>
        (x.1.findStorage x.2.1 x.2.2) >>= fun v =>
          v.asValue >>= fun val => Except.ok (x.1, val)) :
    ResultsAgree aliasNames
      (execStmt s (Stmt.assign lhs rhs))
      (execBlock s [Stmt.storagePlaceAlias rhs.ty valueAliasName rhs,
        Stmt.assign lhs (aliasExpr Kind.storage rhs.ty valueAliasName)]) := by
  rw [execStmt, execBlock_pair]
  cases hcap : resolveS s rhs with
  | error err =>
      have hL : execAssign s lhs rhs = .error err :=
        execAssign_storageRhsErr hlhs hkind hnm hevalEq hcap
      have hR : execStmt s
          (Stmt.storagePlaceAlias rhs.ty valueAliasName rhs) =
          .error err := by
        rw [execStmt, hcap]
        rfl
      rw [hL, hR]
      exact rfl
  | ok x =>
      obtain ⟨t, rootr, segsr⟩ := x
      have hts : t = s := resolveS_pure hprhs hcap
      subst hts
      have hR : execStmt t
          (Stmt.storagePlaceAlias rhs.ty valueAliasName rhs) =
          .ok (t.setEnv valueAliasName (Binding.spath rootr segsr)) := by
        rw [execStmt, hcap]
        rfl
      rw [hR]
      have ht' : EnvAgreeExcept aliasNames t
          (t.setEnv valueAliasName (Binding.spath rootr segsr)) :=
        (EnvAgreeExcept.refl _ t).setEnv_right pv_mem _
      have halias : resolveS
          (t.setEnv valueAliasName (Binding.spath rootr segsr))
          (aliasExpr Kind.storage rhs.ty valueAliasName) =
          .ok (t.setEnv valueAliasName (Binding.spath rootr segsr),
            rootr, segsr) :=
        resolveS_alias rhs.ty
          (lookupBy_setBy_self valueAliasName (Binding.spath rootr segsr) t.env)
      have hevalAlias : ∀ (u : State),
          evalValue u (aliasExpr Kind.storage rhs.ty valueAliasName) =
          (resolveS u (aliasExpr Kind.storage rhs.ty valueAliasName)) >>=
            fun x => (x.1.findStorage x.2.1 x.2.2) >>= fun v =>
              v.asValue >>= fun val => Except.ok (x.1, val) := fun u => by
        rw [aliasExpr, evalValue]
      show ResultsAgree aliasNames (execAssign t lhs rhs)
        (execStmt (t.setEnv valueAliasName (Binding.spath rootr segsr))
          (Stmt.assign lhs (aliasExpr Kind.storage rhs.ty valueAliasName)))
      rw [execStmt]
      refine execAssign_pureLocSim hlhs hfl rfl ?_ ?_ ?_ ?_
      · rw [hkind]
        rfl
      · rw [hevalEq t, hcap, hevalAlias _, halias]
        simp only [resOk_bind, findStorage_congr ht']
        refine bindPureRes_agree _ fun v => ?_
        exact bindPureRes_agree _ fun val => ⟨rfl, ht'⟩
      · intro _
        rw [hcap, halias]
        exact ⟨rfl, ht'⟩
      · intro hm
        rw [hkind] at hm
        exact nomatch hm

theorem storageFieldReadUnfoldRightSndResult_sound
    (s : State) (lhs : PlaceExpr) (rhs : WrappedExpr) {loc : Loc}
    (hcond : (ruleEffect .storageFieldReadUnfoldRightSndResult).cond
      (Stmt.assign lhs rhs))
    (hfresh : ∀ n ∈ aliasNames,
      stmtUsesVar (Stmt.assign lhs rhs) n = false)
    (hlhs : resolveLoc s lhs.expr = .ok (s, loc))
    (hplhs : pureExpr lhs.expr = true)
    (hnm : tyHasMapping rhs.ty = false) :
    ResultsAgree aliasNames
      (execStmt s (Stmt.assign lhs rhs))
      (execBlock s
        ((ruleEffect .storageFieldReadUnfoldRightSndResult).block
          (Stmt.assign lhs rhs) hcond)) := by
  match rhs, hcond, hfresh, hnm with
  | WrappedExpr.field Kind.storage tyR pathR fldR, hcond, hfresh, hnm =>
      refine captureAssignStorageRhs_sound s lhs
        (WrappedExpr.field Kind.storage tyR pathR fldR) hlhs hplhs ?_
        (pure_of_simple (e := pathR) hcond.2.2) rfl hnm
        (fun u => by rw [evalValue])
      intro n hn
      have := hfresh n hn
      simp [stmtUsesVar] at this
      exact this.1

theorem storageIndexReadUnfoldRightSndResult_sound
    (s : State) (lhs : PlaceExpr) (rhs : WrappedExpr) {loc : Loc}
    (hcond : (ruleEffect .storageIndexReadUnfoldRightSndResult).cond
      (Stmt.assign lhs rhs))
    (hfresh : ∀ n ∈ aliasNames,
      stmtUsesVar (Stmt.assign lhs rhs) n = false)
    (hlhs : resolveLoc s lhs.expr = .ok (s, loc))
    (hplhs : pureExpr lhs.expr = true)
    (hnm : tyHasMapping rhs.ty = false) :
    ResultsAgree aliasNames
      (execStmt s (Stmt.assign lhs rhs))
      (execBlock s
        ((ruleEffect .storageIndexReadUnfoldRightSndResult).block
          (Stmt.assign lhs rhs) hcond)) := by
  match rhs, hcond, hfresh, hnm with
  | WrappedExpr.index Kind.storage tyR pathR idxR, hcond, hfresh, hnm =>
      refine captureAssignStorageRhs_sound s lhs
        (WrappedExpr.index Kind.storage tyR pathR idxR) hlhs hplhs ?_
        (by
          have h1 := pure_of_simple (e := pathR) hcond.2.2.1
          have h2 := pure_of_simple (e := idxR) hcond.2.2.2
          simp [pureExpr, h1, h2])
        rfl hnm (fun u => by rw [evalValue])
      intro n hn
      have := hfresh n hn
      simp [stmtUsesVar] at this
      exact this.1

theorem storageFieldReadUnfoldRightFst_sound
    (s : State) (lhs : PlaceExpr) (rhs : WrappedExpr) {loc : Loc}
    (hcond : (ruleEffect .storageFieldReadUnfoldRightFst).cond
      (Stmt.assign lhs rhs))
    (hfresh : ∀ n ∈ aliasNames,
      stmtUsesVar (Stmt.assign lhs rhs) n = false)
    (hlhs : resolveLoc s lhs.expr = .ok (s, loc))
    (hplhs : pureExpr lhs.expr = true)
    (hppath : ∀ {kind ty path fld},
      rhs = WrappedExpr.field kind ty path fld -> pureExpr path = true)
    (hnm : tyHasMapping rhs.ty = false) :
    ResultsAgree aliasNames
      (execStmt s (Stmt.assign lhs rhs))
      (execBlock s
        ((ruleEffect .storageFieldReadUnfoldRightFst).block
          (Stmt.assign lhs rhs) hcond)) := by
  revert hppath
  match rhs, hcond, hfresh, hnm with
  | WrappedExpr.field Kind.storage tyR path fldR, hcond, hfresh, hnm =>
      intro hppath
      have hpp : pureExpr path = true := hppath rfl
      have hfl : ∀ n ∈ aliasNames, usesVar lhs.expr n = false := fun n hn => by
        have := hfresh n hn
        simp [stmtUsesVar] at this
        exact this.1
      show ResultsAgree aliasNames
        (execStmt s (Stmt.assign lhs
          (WrappedExpr.field Kind.storage tyR path fldR)))
        (execBlock s [captureStoragePath path,
          Stmt.assign lhs (WrappedExpr.field Kind.storage tyR
            (aliasExpr Kind.storage path.ty storagePathAliasName) fldR)])
      rw [execStmt, execBlock_pair, captureStoragePath, capture]
      cases hcap : resolveS s path with
      | error err =>
          have hcap' : resolveS s
              (WrappedExpr.field Kind.storage tyR path fldR) = .error err := by
            rw [resolveS, hcap]
            rfl
          have hL : execAssign s lhs
              (WrappedExpr.field Kind.storage tyR path fldR) = .error err :=
            execAssign_storageRhsErr hlhs rfl hnm
              (fun u => by rw [evalValue]) hcap'
          have hR : execStmt s
              (Stmt.storagePlaceAlias path.ty storagePathAliasName path) =
              .error err := by
            rw [execStmt, hcap]
            rfl
          rw [hL, hR]
          exact rfl
      | ok x =>
          obtain ⟨t, root', segs'⟩ := x
          have hts : t = s := resolveS_pure hpp hcap
          subst hts
          have hR : execStmt t
              (Stmt.storagePlaceAlias path.ty storagePathAliasName path) =
              .ok (t.setEnv storagePathAliasName (Binding.spath root' segs')) := by
            rw [execStmt, hcap]
            rfl
          rw [hR]
          have ht' : EnvAgreeExcept aliasNames t
              (t.setEnv storagePathAliasName (Binding.spath root' segs')) :=
            (EnvAgreeExcept.refl _ t).setEnv_right sp_mem _
          have hresL : resolveS t
              (WrappedExpr.field Kind.storage tyR path fldR) =
              .ok (t, root', segs' ++ [Seg.field fldR.name]) := by
            rw [resolveS, hcap]
            rfl
          have hresR : resolveS
              (t.setEnv storagePathAliasName (Binding.spath root' segs'))
              (WrappedExpr.field Kind.storage tyR
                (aliasExpr Kind.storage path.ty storagePathAliasName) fldR) =
              .ok (t.setEnv storagePathAliasName (Binding.spath root' segs'),
                root', segs' ++ [Seg.field fldR.name]) := by
            rw [resolveS,
              resolveS_alias path.ty
                (lookupBy_setBy_self storagePathAliasName
                  (Binding.spath root' segs') t.env)]
            rfl
          show ResultsAgree aliasNames
            (execAssign t lhs (WrappedExpr.field Kind.storage tyR path fldR))
            (execStmt
              (t.setEnv storagePathAliasName (Binding.spath root' segs'))
              (Stmt.assign lhs (WrappedExpr.field Kind.storage tyR
                (aliasExpr Kind.storage path.ty storagePathAliasName) fldR)))
          rw [execStmt]
          refine execAssign_pureLocSim hlhs hfl rfl rfl ?_ ?_ ?_
          · rw [evalValue, evalValue, hresL, hresR]
            simp only [resOk_bind, findStorage_congr ht']
            refine bindPureRes_agree _ fun v => ?_
            exact bindPureRes_agree _ fun val => ⟨rfl, ht'⟩
          · intro _
            rw [hresL, hresR]
            exact ⟨rfl, ht'⟩
          · intro hm
            exact nomatch hm

theorem storageIndexReadUnfoldRightFst_sound
    (s : State) (lhs : PlaceExpr) (rhs : WrappedExpr) {loc : Loc}
    (hcond : (ruleEffect .storageIndexReadUnfoldRightFst).cond
      (Stmt.assign lhs rhs))
    (hfresh : ∀ n ∈ aliasNames,
      stmtUsesVar (Stmt.assign lhs rhs) n = false)
    (hlhs : resolveLoc s lhs.expr = .ok (s, loc))
    (hplhs : pureExpr lhs.expr = true)
    (hppath : ∀ {kind ty path index},
      rhs = WrappedExpr.index kind ty path index -> pureExpr path = true)
    (hpidx : ∀ {kind ty path index},
      rhs = WrappedExpr.index kind ty path index -> pureExpr index = true)
    (hnm : tyHasMapping rhs.ty = false) :
    ResultsAgree aliasNames
      (execStmt s (Stmt.assign lhs rhs))
      (execBlock s
        ((ruleEffect .storageIndexReadUnfoldRightFst).block
          (Stmt.assign lhs rhs) hcond)) := by
  revert hppath hpidx
  match rhs, hcond, hfresh, hnm with
  | WrappedExpr.index Kind.storage tyR path idxR, hcond, hfresh, hnm =>
      intro hppath hpidx
      have hpp : pureExpr path = true := hppath rfl
      have hpi : pureExpr idxR = true := hpidx rfl
      have hfl : ∀ n ∈ aliasNames, usesVar lhs.expr n = false := fun n hn => by
        have := hfresh n hn
        simp [stmtUsesVar] at this
        exact this.1
      show ResultsAgree aliasNames
        (execStmt s (Stmt.assign lhs
          (WrappedExpr.index Kind.storage tyR path idxR)))
        (execBlock s [captureStoragePath path,
          Stmt.assign lhs (WrappedExpr.index Kind.storage tyR
            (aliasExpr Kind.storage path.ty storagePathAliasName) idxR)])
      rw [execStmt, execBlock_pair, captureStoragePath, capture]
      cases hcap : resolveS s path with
      | error err =>
          have hcap' : resolveS s
              (WrappedExpr.index Kind.storage tyR path idxR) = .error err := by
            rw [resolveS, hcap]
            rfl
          have hL : execAssign s lhs
              (WrappedExpr.index Kind.storage tyR path idxR) = .error err :=
            execAssign_storageRhsErr hlhs rfl hnm
              (fun u => by rw [evalValue]) hcap'
          have hR : execStmt s
              (Stmt.storagePlaceAlias path.ty storagePathAliasName path) =
              .error err := by
            rw [execStmt, hcap]
            rfl
          rw [hL, hR]
          exact rfl
      | ok x =>
          obtain ⟨t, root', segs'⟩ := x
          have hts : t = s := resolveS_pure hpp hcap
          subst hts
          have hR : execStmt t
              (Stmt.storagePlaceAlias path.ty storagePathAliasName path) =
              .ok (t.setEnv storagePathAliasName (Binding.spath root' segs')) := by
            rw [execStmt, hcap]
            rfl
          rw [hR]
          have ht' : EnvAgreeExcept aliasNames t
              (t.setEnv storagePathAliasName (Binding.spath root' segs')) :=
            (EnvAgreeExcept.refl _ t).setEnv_right sp_mem _
          have hfi : ∀ n ∈ aliasNames, usesVar idxR n = false := fun n hn => by
            have := hfresh n hn
            simp [stmtUsesVar, usesVar] at this
            exact this.2.2
          have hres : ResAgree aliasNames
              (resolveS t (WrappedExpr.index Kind.storage tyR path idxR))
              (resolveS
                (t.setEnv storagePathAliasName (Binding.spath root' segs'))
                (WrappedExpr.index Kind.storage tyR
                  (aliasExpr Kind.storage path.ty storagePathAliasName)
                  idxR)) := by
            rw [resolveS, resolveS, hcap,
              resolveS_alias path.ty
                (lookupBy_setBy_self storagePathAliasName
                  (Binding.spath root' segs') t.env)]
            simp only [resOk_bind]
            refine ResAgree.bind (evalInt_agree ht' idxR hfi) ?_
            intro u₁ u₂ i hu
            exact ⟨rfl, hu⟩
          show ResultsAgree aliasNames
            (execAssign t lhs (WrappedExpr.index Kind.storage tyR path idxR))
            (execStmt
              (t.setEnv storagePathAliasName (Binding.spath root' segs'))
              (Stmt.assign lhs (WrappedExpr.index Kind.storage tyR
                (aliasExpr Kind.storage path.ty storagePathAliasName) idxR)))
          rw [execStmt]
          refine execAssign_pureLocSim hlhs hfl rfl rfl ?_ ?_ ?_
          · rw [evalValue, evalValue]
            refine ResAgree.bind hres ?_
            intro u₁ u₂ a hu
            obtain ⟨root, segs⟩ := a
            simp only [findStorage_congr hu]
            refine bindPureRes_agree _ fun v => ?_
            exact bindPureRes_agree _ fun val => ⟨rfl, hu⟩
          · intro _
            exact hres
          · intro hm
            exact nomatch hm

/-! ## Support for the declaration splits and stack captures -/

theorem ResAgree.selfRefl (ns : List Name) (x : Res (State × α)) :
    ResAgree ns x x := by
  cases x with
  | error e => exact rfl
  | ok a => exact ⟨rfl, EnvAgreeExcept.refl ns a.1⟩

theorem ResultsAgree.anyOf {ns : List Name} {x₁ x₂ : Res State}
    (h : ResultsAgree [] x₁ x₂) : ResultsAgree ns x₁ x₂ := by
  rcases h.cases with ⟨e, h1, h2⟩ | ⟨t₁, t₂, h1, h2, ht⟩
  · rw [h1, h2]; exact rfl
  · rw [h1, h2]
    exact ⟨ht.storage, ht.heap, ht.nextId, ht.net,
      fun n _ => ht.env n (by simp), ht.selfBalance⟩

/-- Re-binding the excepted name identically on both sides removes the
exception. -/
theorem EnvAgreeExcept.setEnv_both_shrink {ns : List Name} {n : Name}
    {s₁ s₂ : State} (h : EnvAgreeExcept (n :: ns) s₁ s₂) (b : Binding) :
    EnvAgreeExcept ns (s₁.setEnv n b) (s₂.setEnv n b) :=
  ⟨h.storage, h.heap, h.nextId, h.net, fun m hm => by
    by_cases he : m = n
    · subst he
      simp [State.setEnv, lookupBy_setBy_self]
    · have : m ∉ n :: ns := fun hc => by
        cases hc with
        | head => exact he rfl
        | tail _ h' => exact hm h'
      simp [State.setEnv, lookupBy_setBy_ne he, h.env m this],
    h.selfBalance⟩

theorem ResAgree.bindStateAcross {ns ns' : List Name}
    {x₁ x₂ : Res (State × α)} (hx : ResAgree ns x₁ x₂)
    {f₁ f₂ : State × α -> Res State}
    (hf : ∀ s₁ s₂ a, EnvAgreeExcept ns s₁ s₂ ->
      ResultsAgree ns' (f₁ (s₁, a)) (f₂ (s₂, a))) :
    ResultsAgree ns' (x₁ >>= f₁) (x₂ >>= f₂) := by
  match x₁, x₂, hx with
  | .error e₁, .error e₂, hx =>
      subst hx
      exact rfl
  | .ok (s₁, a₁), .ok (s₂, a₂), ⟨heq, hs⟩ =>
      subst heq
      exact hf s₁ s₂ a₁ hs

theorem fieldFor_name (n : Name) (ty : Ty) (o : Option StorageOrigin) :
    (SoliditySyntax.fieldFor n ty o).name = n := by
  cases ty <;> rfl

theorem fieldFor_origin (n : Name) (ty : Ty) (o : Option StorageOrigin) :
    (SoliditySyntax.fieldFor n ty o).origin = o := by
  cases ty <;> rfl

/-! ## Declaration splits -/

theorem localValueDeclInitDrop_sound
    (s : State) (ty : Ty) (name : Name) (init : Option WrappedExpr)
    (hcond : (ruleEffect .localValueDeclInitDrop).cond
      (Stmt.stackDecl ty name init))
    (hself : ∀ rhs, init = some rhs -> usesVar rhs name = false) :
    ResultsAgree aliasNames
      (execStmt s (Stmt.stackDecl ty name init))
      (execBlock s
        ((ruleEffect .localValueDeclInitDrop).block
          (Stmt.stackDecl ty name init) hcond)) := by
  revert hself
  match init, hcond with
  | some rhs, _ =>
      intro hself
      have hf : usesVar rhs name = false := hself rhs rfl
      show ResultsAgree aliasNames
        (execStmt s (Stmt.stackDecl ty name (some rhs)))
        (execBlock s [Stmt.stackDecl ty name none,
          Stmt.assign (SoliditySyntax.varPlace Kind.stack ty name) rhs])
      rw [execStmt, execBlock_pair]
      have hR1 : ∃ d, execStmt s (Stmt.stackDecl ty name none) =
          .ok (s.setEnv name (Binding.val d)) := by
        cases ty with
        | prim p =>
            cases p with
            | bool => exact ⟨Value.bool false, by rw [execStmt]⟩
            | uint => exact ⟨Value.int 0, by rw [execStmt.eq_def]⟩
            | int => exact ⟨Value.int 0, by rw [execStmt.eq_def]⟩
        | ref r => exact ⟨Value.int 0, by rw [execStmt.eq_def]⟩
      obtain ⟨d, hR1⟩ := hR1
      rw [hR1]
      have h0 : EnvAgreeExcept [name] s (s.setEnv name (Binding.val d)) :=
        (EnvAgreeExcept.refl _ s).setEnv_right (List.mem_cons_self ..) _
      have hrl : resolveLoc (s.setEnv name (Binding.val d))
          (SoliditySyntax.varPlace Kind.stack ty name).expr =
          .ok (s.setEnv name (Binding.val d), Loc.stack name) := by
        rw [SoliditySyntax.varPlace, placeVar_expr, resolveLoc, fieldFor_name]
      show ResultsAgree aliasNames _
        (execStmt (s.setEnv name (Binding.val d))
          (Stmt.assign (SoliditySyntax.varPlace Kind.stack ty name) rhs))
      rw [execStmt, execAssign.eq_def]
      simp only [SoliditySyntax.varPlace, placeVar_expr, fieldFor_name]
      refine ResultsAgree.anyOf ?_
      refine ResAgree.bindStateAcross
        (evalValue_agree h0 rhs (fun n hn => by
          simp at hn
          subst hn
          exact hf)) ?_
      intro u₁ u₂ v hu
      exact hu.setEnv_both_shrink (Binding.val v)

theorem storageLocalDeclInitDrop_sound
    (s : State) (ty : Ty) (name : Name) (init : Option WrappedExpr)
    (hcond : (ruleEffect .storageLocalDeclInitDrop).cond
      (Stmt.storageDecl ty name init))
    (horig : SoliditySyntax.storageOriginFor name ≠
      some StorageOrigin.global) :
    ResultsAgree aliasNames
      (execStmt s (Stmt.storageDecl ty name init))
      (execBlock s
        ((ruleEffect .storageLocalDeclInitDrop).block
          (Stmt.storageDecl ty name init) hcond)) := by
  match init, hcond with
  | some rhs, _ =>
      show ResultsAgree aliasNames
        (execStmt s (Stmt.storageDecl ty name (some rhs)))
        (execBlock s [Stmt.storageDecl ty name none,
          Stmt.assign (SoliditySyntax.varPlace Kind.storage ty name) rhs])
      rw [execStmt, execBlock_pair]
      have hR1 : execStmt s (Stmt.storageDecl ty name none) = .ok s := by
        rw [execStmt]
      rw [hR1]
      have hrl : resolveLoc s
          (SoliditySyntax.varPlace Kind.storage ty name).expr =
          .ok (s, Loc.storageLocal name) := by
        rw [SoliditySyntax.varPlace, placeVar_expr, resolveLoc,
          fieldFor_origin, SoliditySyntax.originFor, if_neg horig,
          fieldFor_name]
      show ResultsAgree aliasNames _
        (execStmt s
          (Stmt.assign (SoliditySyntax.varPlace Kind.storage ty name) rhs))
      rw [execStmt, execAssign.eq_def]
      simp only [SoliditySyntax.varPlace, placeVar_expr, fieldFor_origin,
        SoliditySyntax.originFor, if_neg horig, fieldFor_name]
      exact ResultsAgree.refl _ _

theorem memoryLocalDeclInitDrop_sound
    (s : State) (ty : Ty) (name : Name) (init : Option WrappedExpr)
    (hcond : (ruleEffect .memoryLocalDeclInitDrop).cond
      (Stmt.memoryDecl ty name init)) :
    ResultsAgree aliasNames
      (execStmt s (Stmt.memoryDecl ty name init))
      (execBlock s
        ((ruleEffect .memoryLocalDeclInitDrop).block
          (Stmt.memoryDecl ty name init) hcond)) := by
  match init, hcond with
  | some rhs, _ =>
      show ResultsAgree aliasNames
        (execStmt s (Stmt.memoryDecl ty name (some rhs)))
        (execBlock s
          [Stmt.assign (SoliditySyntax.varPlace Kind.memory ty name) rhs])
      rw [execStmt, execBlock_single]
      have hrl : resolveLoc s
          (SoliditySyntax.varPlace Kind.memory ty name).expr =
          .ok (s, Loc.memoryRoot name) := by
        rw [SoliditySyntax.varPlace, placeVar_expr, resolveLoc, fieldFor_name]
      show ResultsAgree aliasNames _
        (execStmt s
          (Stmt.assign (SoliditySyntax.varPlace Kind.memory ty name) rhs))
      rw [execStmt, execAssign.eq_def]
      simp only [SoliditySyntax.varPlace, placeVar_expr, fieldFor_name]
      exact ResultsAgree.refl _ _

/-! ## If-then-else, assert, transfer -/

theorem ifElseTrue_sound
    (s : State) (c : WrappedExpr) (thn els : List Stmt)
    (hcond : (ruleEffect .ifElseTrue).cond (Stmt.ite c thn els)) :
    ResultsAgree aliasNames
      (execStmt s (Stmt.ite c thn els))
      (execBlock s ((ruleEffect .ifElseTrue).block
        (Stmt.ite c thn els) hcond)) := by
  match c, hcond with
  | WrappedExpr.bool true, _ =>
      show ResultsAgree aliasNames
        (execStmt s (Stmt.ite (WrappedExpr.bool true) thn els))
        (execBlock s thn)
      rw [execStmt, evalValue]
      exact ResultsAgree.refl _ _

theorem ifElseFalse_sound
    (s : State) (c : WrappedExpr) (thn els : List Stmt)
    (hcond : (ruleEffect .ifElseFalse).cond (Stmt.ite c thn els)) :
    ResultsAgree aliasNames
      (execStmt s (Stmt.ite c thn els))
      (execBlock s ((ruleEffect .ifElseFalse).block
        (Stmt.ite c thn els) hcond)) := by
  match c, hcond with
  | WrappedExpr.bool false, _ =>
      show ResultsAgree aliasNames
        (execStmt s (Stmt.ite (WrappedExpr.bool false) thn els))
        (execBlock s els)
      rw [execStmt, evalValue]
      exact ResultsAgree.refl _ _

theorem ifElseNegated_sound
    (s : State) (c : WrappedExpr) (thn els : List Stmt)
    (hcond : (ruleEffect .ifElseNegated).cond (Stmt.ite c thn els)) :
    ResultsAgree aliasNames
      (execStmt s (Stmt.ite c thn els))
      (execBlock s ((ruleEffect .ifElseNegated).block
        (Stmt.ite c thn els) hcond)) := by
  match c, hcond with
  | .mkUnop UnOp.not inner, _ =>
      show ResultsAgree aliasNames
        (execStmt s (Stmt.ite (WrappedExpr.unop UnOp.not inner) thn els))
        (execBlock s [Stmt.ite inner els thn])
      rw [execStmt, execBlock_single, execStmt, evalValue]
      cases hev : evalValue s inner with
      | error err => exact rfl
      | ok x =>
          obtain ⟨t, v⟩ := x
          simp only [resOk_bind]
          cases v with
          | int i => exact rfl
          | bool b =>
              cases b with
              | true => exact ResultsAgree.refl _ _
              | false => exact ResultsAgree.refl _ _

theorem assertConditionCapture_sound
    (s : State) (c : WrappedExpr)
    (hcond : (ruleEffect .assertConditionCapture).cond
      (Stmt.assertStmt c)) :
    ResultsAgree aliasNames
      (execStmt s (Stmt.assertStmt c))
      (execBlock s ((ruleEffect .assertConditionCapture).block
        (Stmt.assertStmt c) hcond)) := by
  show ResultsAgree aliasNames
    (execStmt s (Stmt.assertStmt c))
    (execBlock s [Stmt.stackDecl c.ty valueAliasName (some c),
      Stmt.assertStmt (stackValueAlias c)])
  rw [execStmt, execBlock_pair]
  cases hev : evalValue s c with
  | error err =>
      have hR1 : execStmt s (Stmt.stackDecl c.ty valueAliasName (some c)) =
          .error err := by
        rw [execStmt, hev]
        rfl
      rw [hR1]
      exact rfl
  | ok x =>
      obtain ⟨t, v⟩ := x
      have hR1 : execStmt s (Stmt.stackDecl c.ty valueAliasName (some c)) =
          .ok (t.setEnv valueAliasName (Binding.val v)) := by
        rw [execStmt, hev]
        rfl
      rw [hR1]
      simp only [resOk_bind]
      have ht' : EnvAgreeExcept aliasNames t
          (t.setEnv valueAliasName (Binding.val v)) :=
        (EnvAgreeExcept.refl _ t).setEnv_right pv_mem _
      show ResultsAgree aliasNames _
        (execStmt (t.setEnv valueAliasName (Binding.val v))
          (Stmt.assertStmt (stackValueAlias c)))
      rw [execStmt, stackValueAlias,
        evalValue_alias c.ty
          (lookupBy_setBy_self valueAliasName (Binding.val v) t.env)]
      simp only [resOk_bind]
      cases v with
      | int i => exact rfl
      | bool b =>
          cases b with
          | true => exact ht'
          | false => exact rfl

theorem requireConditionCapture_sound
    (s : State) (c : WrappedExpr)
    (hcond : (ruleEffect .requireConditionCapture).cond
      (Stmt.requireStmt c)) :
    ResultsAgree aliasNames
      (execStmt s (Stmt.requireStmt c))
      (execBlock s ((ruleEffect .requireConditionCapture).block
        (Stmt.requireStmt c) hcond)) := by
  show ResultsAgree aliasNames
    (execStmt s (Stmt.requireStmt c))
    (execBlock s [Stmt.stackDecl c.ty valueAliasName (some c),
      Stmt.requireStmt (stackValueAlias c)])
  rw [execStmt, execBlock_pair]
  cases hev : evalValue s c with
  | error err =>
      have hR1 : execStmt s (Stmt.stackDecl c.ty valueAliasName (some c)) =
          .error err := by
        rw [execStmt, hev]
        rfl
      rw [hR1]
      exact rfl
  | ok x =>
      obtain ⟨t, v⟩ := x
      have hR1 : execStmt s (Stmt.stackDecl c.ty valueAliasName (some c)) =
          .ok (t.setEnv valueAliasName (Binding.val v)) := by
        rw [execStmt, hev]
        rfl
      rw [hR1]
      simp only [resOk_bind]
      have ht' : EnvAgreeExcept aliasNames t
          (t.setEnv valueAliasName (Binding.val v)) :=
        (EnvAgreeExcept.refl _ t).setEnv_right pv_mem _
      show ResultsAgree aliasNames _
        (execStmt (t.setEnv valueAliasName (Binding.val v))
          (Stmt.requireStmt (stackValueAlias c)))
      rw [execStmt, stackValueAlias,
        evalValue_alias c.ty
          (lookupBy_setBy_self valueAliasName (Binding.val v) t.env)]
      simp only [resOk_bind]
      cases v with
      | int i => exact rfl
      | bool b =>
          cases b with
          | true => exact ht'
          | false => exact rfl

theorem ifElseUnfold_sound
    (s : State) (c : WrappedExpr) (thn els : List Stmt)
    (hcond : (ruleEffect .ifElseUnfold).cond
      (Stmt.ite c thn els))
    (hfresh : ∀ n ∈ aliasNames,
      stmtUsesVar (Stmt.ite c thn els) n = false) :
    ResultsAgree aliasNames
      (execStmt s (Stmt.ite c thn els))
      (execBlock s ((ruleEffect .ifElseUnfold).block
        (Stmt.ite c thn els) hcond)) := by
  have hfthn : ∀ n ∈ aliasNames, blockUsesVar thn n = false := fun n hn => by
    have := hfresh n hn
    simp [stmtUsesVar] at this
    exact this.1.2
  have hfels : ∀ n ∈ aliasNames, blockUsesVar els n = false := fun n hn => by
    have := hfresh n hn
    simp [stmtUsesVar] at this
    exact this.2
  show ResultsAgree aliasNames
    (execStmt s (Stmt.ite c thn els))
    (execBlock s [Stmt.stackDecl c.ty valueAliasName (some c),
      Stmt.ite (stackValueAlias c) thn els])
  rw [execStmt, execBlock_pair]
  cases hev : evalValue s c with
  | error err =>
      have hR1 : execStmt s (Stmt.stackDecl c.ty valueAliasName (some c)) =
          .error err := by
        rw [execStmt, hev]
        rfl
      rw [hR1]
      exact rfl
  | ok x =>
      obtain ⟨t, v⟩ := x
      have hR1 : execStmt s (Stmt.stackDecl c.ty valueAliasName (some c)) =
          .ok (t.setEnv valueAliasName (Binding.val v)) := by
        rw [execStmt, hev]
        rfl
      rw [hR1]
      simp only [resOk_bind]
      have ht' : EnvAgreeExcept aliasNames t
          (t.setEnv valueAliasName (Binding.val v)) :=
        (EnvAgreeExcept.refl _ t).setEnv_right pv_mem _
      show ResultsAgree aliasNames _
        (execStmt (t.setEnv valueAliasName (Binding.val v))
          (Stmt.ite (stackValueAlias c) thn els))
      rw [execStmt, stackValueAlias,
        evalValue_alias c.ty
          (lookupBy_setBy_self valueAliasName (Binding.val v) t.env)]
      simp only [resOk_bind]
      cases v with
      | int i => exact rfl
      | bool b =>
          cases b with
          | true => exact execBlock_agree ht' thn hfthn
          | false => exact execBlock_agree ht' els hfels

theorem transferUnfoldLeftFstReceiver_sound
    (s : State) (recipient amount : WrappedExpr)
    (hcond : (ruleEffect .transferUnfoldLeftFstReceiver).cond
      (Stmt.transfer recipient amount))
    (hfresh : ∀ n ∈ aliasNames,
      stmtUsesVar (Stmt.transfer recipient amount) n = false) :
    ResultsAgree aliasNames
      (execStmt s (Stmt.transfer recipient amount))
      (execBlock s ((ruleEffect .transferUnfoldLeftFstReceiver).block
        (Stmt.transfer recipient amount) hcond)) := by
  have hfamt : ∀ n ∈ aliasNames, usesVar amount n = false := fun n hn => by
    have := hfresh n hn
    simp [stmtUsesVar] at this
    exact this.2
  show ResultsAgree aliasNames
    (execStmt s (Stmt.transfer recipient amount))
    (execBlock s [Stmt.stackDecl recipient.ty valueAliasName (some recipient),
      Stmt.transfer (stackValueAlias recipient) amount])
  rw [execStmt, execBlock_pair]
  cases hev : evalValue s recipient with
  | error err =>
      have hR1 : execStmt s
          (Stmt.stackDecl recipient.ty valueAliasName (some recipient)) =
          .error err := by
        rw [execStmt, hev]
        rfl
      rw [hR1, evalInt, hev]
      exact rfl
  | ok x =>
      obtain ⟨t, v⟩ := x
      have hR1 : execStmt s
          (Stmt.stackDecl recipient.ty valueAliasName (some recipient)) =
          .ok (t.setEnv valueAliasName (Binding.val v)) := by
        rw [execStmt, hev]
        rfl
      rw [hR1, evalInt, hev]
      simp only [resOk_bind]
      have ht' : EnvAgreeExcept aliasNames t
          (t.setEnv valueAliasName (Binding.val v)) :=
        (EnvAgreeExcept.refl _ t).setEnv_right pv_mem _
      show ResultsAgree aliasNames _
        (execStmt (t.setEnv valueAliasName (Binding.val v))
          (Stmt.transfer (stackValueAlias recipient) amount))
      rw [execStmt]
      have halias : evalInt (t.setEnv valueAliasName (Binding.val v))
          (stackValueAlias recipient) =
          v.asInt >>= fun i =>
            .ok (t.setEnv valueAliasName (Binding.val v), i) := by
        rw [stackValueAlias, evalInt,
          evalValue_alias recipient.ty
            (lookupBy_setBy_self valueAliasName (Binding.val v) t.env)]
        rfl
      rw [halias]
      cases hi : v.asInt with
      | error err => exact rfl
      | ok addr =>
          simp only [resOk_bind]
          refine ResAgree.bindState (evalInt_agree ht' amount hfamt) ?_
          intro u₁ u₂ amt hu
          by_cases hneg : amt < 0
          · simp only [if_pos hneg]
            exact rfl
          · simp only [if_neg hneg]
            rw [hu.selfBalance]
            by_cases hbal : u₂.selfBalance < amt
            · simp only [if_pos hbal]
              exact rfl
            · simp only [if_neg hbal]
              simp only [getNet_congr hu]
              exact ⟨hu.storage, hu.heap, hu.nextId,
                by simp [State.setNet, hu.net], hu.env, rfl⟩

theorem transferUnfoldRightSndArgument_sound
    (s : State) (recipient amount : WrappedExpr) (addr : Int)
    (hcond : (ruleEffect .transferUnfoldRightSndArgument).cond
      (Stmt.transfer recipient amount))
    (hfresh : ∀ n ∈ aliasNames,
      stmtUsesVar (Stmt.transfer recipient amount) n = false)
    (hrec : evalInt s recipient = .ok (s, addr))
    (hpamt : pureExpr amount = true) :
    ResultsAgree aliasNames
      (execStmt s (Stmt.transfer recipient amount))
      (execBlock s ((ruleEffect .transferUnfoldRightSndArgument).block
        (Stmt.transfer recipient amount) hcond)) := by
  have hfrec : ∀ n ∈ aliasNames, usesVar recipient n = false := fun n hn => by
    have := hfresh n hn
    simp [stmtUsesVar] at this
    exact this.1
  show ResultsAgree aliasNames
    (execStmt s (Stmt.transfer recipient amount))
    (execBlock s [Stmt.stackDecl amount.ty valueAliasName (some amount),
      Stmt.transfer recipient (stackValueAlias amount)])
  rw [execStmt, execBlock_pair]
  cases hev : evalValue s amount with
  | error err =>
      have hR1 : execStmt s
          (Stmt.stackDecl amount.ty valueAliasName (some amount)) =
          .error err := by
        rw [execStmt, hev]
        rfl
      rw [hR1, hrec]
      simp only [resOk_bind]
      rw [evalInt, hev]
      exact rfl
  | ok x =>
      obtain ⟨t, v⟩ := x
      have hts : t = s := evalValue_pure hpamt hev
      subst hts
      have hR1 : execStmt t
          (Stmt.stackDecl amount.ty valueAliasName (some amount)) =
          .ok (t.setEnv valueAliasName (Binding.val v)) := by
        rw [execStmt, hev]
        rfl
      rw [hR1, hrec]
      simp only [resOk_bind]
      have ht' : EnvAgreeExcept aliasNames t
          (t.setEnv valueAliasName (Binding.val v)) :=
        (EnvAgreeExcept.refl _ t).setEnv_right pv_mem _
      have hrec' : evalInt (t.setEnv valueAliasName (Binding.val v))
          recipient =
          .ok (t.setEnv valueAliasName (Binding.val v), addr) := by
        have h := evalInt_agree ht' recipient hfrec
        rw [hrec] at h
        rcases h.cases with ⟨err, h1, h2⟩ | ⟨u₁, u₂, a, h1, h2, hu⟩
        · exact nomatch h1
        · have ha : a = addr := (congrArg Prod.snd (Except.ok.inj h1)).symm
          have hu2 : u₂ = t.setEnv valueAliasName (Binding.val v) :=
            evalInt_pure (pure_of_simple hcond.1) h2
          rw [h2, hu2, ha]
      show ResultsAgree aliasNames _
        (execStmt (t.setEnv valueAliasName (Binding.val v))
          (Stmt.transfer recipient (stackValueAlias amount)))
      rw [execStmt, hrec']
      simp only [resOk_bind]
      have halias : evalInt (t.setEnv valueAliasName (Binding.val v))
          (stackValueAlias amount) =
          v.asInt >>= fun i =>
            .ok (t.setEnv valueAliasName (Binding.val v), i) := by
        rw [stackValueAlias, evalInt,
          evalValue_alias amount.ty
            (lookupBy_setBy_self valueAliasName (Binding.val v) t.env)]
        rfl
      rw [evalInt, hev, halias]
      simp only [resOk_bind]
      cases hi : v.asInt with
      | error err => exact rfl
      | ok amt =>
          simp only [resOk_bind, getNet_congr ht']
          by_cases hneg : amt < 0
          · simp only [if_pos hneg]
            exact rfl
          · simp only [if_neg hneg]
            rw [ht'.selfBalance]
            by_cases hbal : (t.setEnv valueAliasName
                (Binding.val v)).selfBalance < amt
            · simp only [if_pos hbal]
              exact rfl
            · simp only [if_neg hbal]
              exact ⟨ht'.storage, ht'.heap, ht'.nextId,
                by simp [State.setNet, ht'.net], ht'.env, rfl⟩

/-! ## Operator captures -/

/-- A simple stack variable resolves to its stack slot in any state. -/
theorem stackVarLoc (lhs : PlaceExpr)
    (h1 : lhs.expr.isStack = true) (h2 : lhs.expr.simple = true) :
    ∃ name, ∀ (u : State),
      resolveLoc u lhs.expr = .ok (u, Loc.stack name) := by
  obtain ⟨e, hass⟩ := lhs
  match e, hass, h1, h2 with
  | .var kind ty fld, _, h1, _ =>
      cases kind with
      | stack => exact ⟨fld.name, fun u => by rw [resolveLoc]⟩
      | storage => exact nomatch h1
      | memory => exact nomatch h1
  | .field .., _, _, h2 => exact nomatch h2
  | .index .., _, _, h2 => exact nomatch h2
  | .pushPlace .., _, _, h2 => exact nomatch h2
  | .bool _, hass, _, _ => exact nomatch hass
  | .intLit .., hass, _, _ => exact nomatch hass
  | .mkCall .., hass, _, _ => exact nomatch hass
  | .mkBinop .., hass, _, _ => exact nomatch hass
  | .mkUnop .., hass, _, _ => exact nomatch hass
  | .mkIncDec .., hass, _, _ => exact nomatch hass
  | .mkTernary .., hass, _, _ => exact nomatch hass

/-- `ternaryToIf` (KeY): `v = se ? e1 : e2;` on a stack variable rewrites
to the statement `if`. The condition is simple, hence pure, so both
sides evaluate the same branch assignment in the same state — the
results are literally equal. -/
theorem ternaryToIf_sound
    (s : State) (lhs : PlaceExpr) (rhs : WrappedExpr)
    (hcond : (ruleEffect .ternaryToIf).cond (Stmt.assign lhs rhs)) :
    ResultsAgree aliasNames
      (execStmt s (Stmt.assign lhs rhs))
      (execBlock s ((ruleEffect .ternaryToIf).block
        (Stmt.assign lhs rhs) hcond)) := by
  match rhs, hcond with
  | .mkTernary c t e, hcond =>
      obtain ⟨hsc, hs1, hs2⟩ := hcond
      simp only [Rules.isSimple, Rules.isStack] at hsc hs1 hs2
      obtain ⟨name, hloc⟩ := stackVarLoc lhs hs1 hs2
      show ResultsAgree aliasNames
        (execStmt s (Stmt.assign lhs (WrappedExpr.ternary c t e)))
        (execBlock s [Stmt.ite c [Stmt.assign lhs t] [Stmt.assign lhs e]])
      rw [execBlock_single, execStmt, execStmt, execAssign_stackVar hloc,
        evalValue]
      cases hev : evalValue s c with
      | error err => exact rfl
      | ok x =>
          obtain ⟨u, cv⟩ := x
          have hu : u = s := evalValue_pure (pure_of_simple hsc) hev
          subst hu
          simp only [resOk_bind]
          cases cv with
          | int v => exact rfl
          | bool b =>
              cases b with
              | true =>
                  show ResultsAgree aliasNames _
                    (execBlock u [Stmt.assign lhs t])
                  rw [execBlock_single, execStmt, execAssign_stackVar hloc]
                  exact ResultsAgree.refl _ _
              | false =>
                  show ResultsAgree aliasNames _
                    (execBlock u [Stmt.assign lhs e])
                  rw [execBlock_single, execStmt, execAssign_stackVar hloc]
                  exact ResultsAgree.refl _ _

/-- `ternaryToIfStorage` (KeY): the twin of `ternaryToIf` for a
storage-path target. The condition is simple/pure, so the target
resolves identically on both sides; `hprim` pins the interpreter to the
primitive-write dispatch (the branch types agree via `htye`). -/
theorem ternaryToIfStorage_sound
    (s : State) (lhs : PlaceExpr) (rhs : WrappedExpr) {loc : Loc}
    (hcond : (ruleEffect .ternaryToIfStorage).cond
      (Stmt.assign lhs rhs))
    (hlhs : resolveLoc s lhs.expr = .ok (s, loc))
    (hfl : ∀ n ∈ aliasNames, usesVar lhs.expr n = false)
    (hprim : rhs.ty.isPrimitive = true)
    (htye : ∀ {c t e}, rhs = WrappedExpr.ternary c t e -> e.ty = t.ty)
    (hnsl : ∀ nm, loc ≠ Loc.storageLocal nm)
    (hnmr : ∀ nm, loc ≠ Loc.memoryRoot nm) :
    ResultsAgree aliasNames
      (execStmt s (Stmt.assign lhs rhs))
      (execBlock s ((ruleEffect .ternaryToIfStorage).block
        (Stmt.assign lhs rhs) hcond)) := by
  revert hprim htye
  match rhs, hcond with
  | .mkTernary c t e, hcond =>
      intro hprim htye
      obtain ⟨hsc, hst⟩ := hcond
      simp only [Rules.isSimple] at hsc
      show ResultsAgree aliasNames
        (execStmt s (Stmt.assign lhs (WrappedExpr.ternary c t e)))
        (execBlock s [Stmt.ite c [Stmt.assign lhs t] [Stmt.assign lhs e]])
      rw [execBlock_single, execStmt, execStmt]
      cases hev : evalValue s c with
      | error err =>
          have hev' : evalValue s (WrappedExpr.ternary c t e) =
              .error err := by
            rw [evalValue, hev]
            rfl
          rw [execAssign_evalErr hlhs hprim hnsl hnmr hev']
          exact rfl
      | ok x =>
          obtain ⟨u, cv⟩ := x
          have hu : u = s := evalValue_pure (pure_of_simple hsc) hev
          subst hu
          simp only [resOk_bind]
          cases cv with
          | int v =>
              have hev' : evalValue u (WrappedExpr.ternary c t e) =
                  .error .stuck := by
                rw [evalValue, hev]
                rfl
              rw [execAssign_evalErr hlhs hprim hnsl hnmr hev']
              exact rfl
          | bool b =>
              cases b with
              | true =>
                  show ResultsAgree aliasNames _
                    (execBlock u [Stmt.assign lhs t])
                  rw [execBlock_single, execStmt]
                  refine execAssign_pureLocSimPrim hlhs hfl rfl hprim ?_
                    hnsl hnmr
                  rw [evalValue, hev]
                  simp only [resOk_bind]
                  exact ResAgree.refl _ _
              | false =>
                  show ResultsAgree aliasNames _
                    (execBlock u [Stmt.assign lhs e])
                  rw [execBlock_single, execStmt]
                  refine execAssign_pureLocSimPrim hlhs hfl
                    (show e.ty = (WrappedExpr.ternary c t e).ty from
                      @htye c t e rfl) hprim ?_ hnsl hnmr
                  rw [evalValue, hev]
                  simp only [resOk_bind]
                  exact ResAgree.refl _ _

theorem ternaryCaptureCond_sound
    (s : State) (lhs : PlaceExpr) (rhs : WrappedExpr) {loc : Loc}
    (hcond : (ruleEffect .ternaryCaptureCond).cond
      (Stmt.assign lhs rhs))
    (hfresh : ∀ n ∈ aliasNames,
      stmtUsesVar (Stmt.assign lhs rhs) n = false)
    (hlhs : resolveLoc s lhs.expr = .ok (s, loc))
    (hplhs : pureExpr lhs.expr = true)
    (hprim : rhs.ty.isPrimitive = true)
    (hnsl : ∀ nm, loc ≠ Loc.storageLocal nm)
    (hnmr : ∀ nm, loc ≠ Loc.memoryRoot nm)
    (hstable : ∀ {c t e} u cv, rhs = WrappedExpr.ternary c t e ->
      evalValue s c = .ok (u, cv) ->
      resolveLoc u lhs.expr = .ok (u, loc)) :
    ResultsAgree aliasNames
      (execStmt s (Stmt.assign lhs rhs))
      (execBlock s ((ruleEffect .ternaryCaptureCond).block
        (Stmt.assign lhs rhs) hcond)) := by
  revert hprim hstable
  match rhs, hcond, hfresh with
  | .mkTernary c t e, hcond, hfresh =>
      intro hprim hstable
      have hfl : ∀ n ∈ aliasNames, usesVar lhs.expr n = false :=
        fun n hn => by
          have := hfresh n hn
          simp [stmtUsesVar] at this
          exact this.1
      have hfc : ∀ n ∈ aliasNames, usesVar c n = false := fun n hn => by
        have := hfresh n hn
        simp [stmtUsesVar, usesVar] at this
        exact this.2.1.1
      have hft : ∀ n ∈ aliasNames, usesVar t n = false := fun n hn => by
        have := hfresh n hn
        simp [stmtUsesVar, usesVar] at this
        exact this.2.1.2
      have hfe : ∀ n ∈ aliasNames, usesVar e n = false := fun n hn => by
        have := hfresh n hn
        simp [stmtUsesVar, usesVar] at this
        exact this.2.2
      show ResultsAgree aliasNames
        (execStmt s (Stmt.assign lhs (WrappedExpr.ternary c t e)))
        (execBlock s [captureStackValue c,
          Stmt.assign lhs
            (WrappedExpr.ternary (stackValueAlias c) t e)])
      rw [execStmt, execBlock_pair, captureStackValue, capture]
      cases hev : evalValue s c with
      | error err =>
          have hev' : evalValue s (WrappedExpr.ternary c t e) =
              .error err := by
            rw [evalValue, hev]
            rfl
          have hL : execAssign s lhs (WrappedExpr.ternary c t e) =
              .error err := execAssign_evalErr hlhs hprim hnsl hnmr hev'
          have hR : execStmt s (Stmt.stackDecl c.ty valueAliasName (some c)) =
              .error err := by
            rw [execStmt, hev]
            rfl
          rw [hL, hR]
          exact rfl
      | ok x =>
          obtain ⟨u, cv⟩ := x
          have hR : execStmt s (Stmt.stackDecl c.ty valueAliasName (some c)) =
              .ok (u.setEnv valueAliasName (Binding.val cv)) := by
            rw [execStmt, hev]
            rfl
          rw [hR]
          have hu' : EnvAgreeExcept aliasNames u
              (u.setEnv valueAliasName (Binding.val cv)) :=
            (EnvAgreeExcept.refl _ u).setEnv_right pv_mem _
          show ResultsAgree aliasNames _
            (execStmt (u.setEnv valueAliasName (Binding.val cv))
              (Stmt.assign lhs
                (WrappedExpr.ternary (stackValueAlias c) t e)))
          rw [execStmt]
          refine execAssign_pureLocSim hlhs hfl
            rfl rfl ?_ ?_ ?_
          · rw [evalValue, evalValue, hev, stackValueAlias,
              evalValue_alias c.ty
                (lookupBy_setBy_self valueAliasName (Binding.val cv) u.env)]
            simp only [resOk_bind]
            cases cv with
            | int v => exact rfl
            | bool b =>
                cases b with
                | true => exact evalValue_agree hu' t hft
                | false => exact evalValue_agree hu' e hfe
          · intro _
            rw [resolveS.eq_def, resolveS.eq_def]
            exact rfl
          · intro hk
            exact nomatch hk

theorem unopCapture_sound (op : UnOp)
    (s : State) (lhs : PlaceExpr) (rhs : WrappedExpr)
    (hcond : (ruleEffect (.unopCapture op)).cond (Stmt.assign lhs rhs))
    (hfresh : ∀ n ∈ aliasNames,
      stmtUsesVar (Stmt.assign lhs rhs) n = false) :
    ResultsAgree aliasNames
      (execStmt s (Stmt.assign lhs rhs))
      (execBlock s ((ruleEffect (.unopCapture op)).block
        (Stmt.assign lhs rhs) hcond)) := by
  match rhs, hcond, hfresh with
  | .mkUnop op' arg, hcond, hfresh =>
      obtain ⟨name, hloc⟩ := stackVarLoc lhs hcond.2.1.1 hcond.2.1.2
      show ResultsAgree aliasNames
        (execStmt s (Stmt.assign lhs (WrappedExpr.unop op' arg)))
        (execBlock s [Stmt.stackDecl arg.ty valueAliasName (some arg),
          Stmt.assign lhs
            (WrappedExpr.unop op' (stackValueAlias arg))])
      rw [execStmt, execBlock_pair]
      cases hev : evalValue s arg with
      | error err =>
          have hL : execAssign s lhs (WrappedExpr.unop op' arg) =
              .error err := by
            rw [execAssign_stackVar hloc, evalValue, hev]
            rfl
          have hR : execStmt s
              (Stmt.stackDecl arg.ty valueAliasName (some arg)) =
              .error err := by
            rw [execStmt, hev]
            rfl
          rw [hL, hR]
          exact rfl
      | ok x =>
          obtain ⟨t, v⟩ := x
          have hR : execStmt s
              (Stmt.stackDecl arg.ty valueAliasName (some arg)) =
              .ok (t.setEnv valueAliasName (Binding.val v)) := by
            rw [execStmt, hev]
            rfl
          rw [hR]
          have ht' : EnvAgreeExcept aliasNames t
              (t.setEnv valueAliasName (Binding.val v)) :=
            (EnvAgreeExcept.refl _ t).setEnv_right pv_mem _
          show ResultsAgree aliasNames
            (execAssign s lhs (WrappedExpr.unop op' arg))
            (execStmt (t.setEnv valueAliasName (Binding.val v))
              (Stmt.assign lhs (WrappedExpr.unop op' (stackValueAlias arg))))
          rw [execStmt, execAssign_stackVar hloc, execAssign_stackVar hloc]
          rw [evalValue, evalValue, hev, stackValueAlias,
            evalValue_alias arg.ty
              (lookupBy_setBy_self valueAliasName (Binding.val v) t.env)]
          simp only [resOk_bind]
          cases applyUnOp op' v with
          | error e => exact rfl
          | ok w =>
              simp only [resOk_bind, stackValueAlias, aliasExpr,
                Typed.WrappedExpr.ty]
              cases op' with
              | not => exact ht'.setEnv_both name (Binding.val w)
              | neg =>
                  cases arg.ty with
                  | prim p =>
                      cases p with
                      | int =>
                          cases checkArith Ty.int w with
                          | error e => exact rfl
                          | ok w' => exact ht'.setEnv_both name (Binding.val w')
                      | bool => exact ht'.setEnv_both name (Binding.val w)
                      | uint => exact ht'.setEnv_both name (Binding.val w)
                  | ref r => exact ht'.setEnv_both name (Binding.val w)

theorem storageIndexReadUnfoldRightSndIndex_sound
    (s : State) (lhs : PlaceExpr) (rhs : WrappedExpr) {loc : Loc}
    (hcond : (ruleEffect .storageIndexReadUnfoldRightSndIndex).cond
      (Stmt.assign lhs rhs))
    (hfresh : ∀ n ∈ aliasNames,
      stmtUsesVar (Stmt.assign lhs rhs) n = false)
    (hlhs : resolveLoc s lhs.expr = .ok (s, loc))
    (hplhs : pureExpr lhs.expr = true)
    (hpidx : ∀ {kind ty path index},
      rhs = WrappedExpr.index kind ty path index -> pureExpr index = true)
    (hbase : ∀ {kind ty path index},
      rhs = WrappedExpr.index kind ty path index ->
        ∃ root segs, resolveS s path = .ok (s, root, segs))
    (hnm : tyHasMapping rhs.ty = false) :
    ResultsAgree aliasNames
      (execStmt s (Stmt.assign lhs rhs))
      (execBlock s
        ((ruleEffect .storageIndexReadUnfoldRightSndIndex).block
          (Stmt.assign lhs rhs) hcond)) := by
  revert hpidx hbase
  match rhs, hcond, hfresh, hnm with
  | WrappedExpr.index Kind.storage tyR pathR idxR, hcond, hfresh, hnm =>
      intro hpidx hbase
      obtain ⟨root, segs, hb⟩ := hbase rfl
      have hpi : pureExpr idxR = true := hpidx rfl
      have hpp : pureExpr pathR = true := pure_of_simple hcond.1
      have hfl : ∀ n ∈ aliasNames, usesVar lhs.expr n = false := fun n hn => by
        have := hfresh n hn
        simp [stmtUsesVar] at this
        exact this.1
      have hfp : ∀ n ∈ aliasNames, usesVar pathR n = false := fun n hn => by
        have := hfresh n hn
        simp [stmtUsesVar, usesVar] at this
        exact this.2.1
      show ResultsAgree aliasNames
        (execStmt s (Stmt.assign lhs
          (WrappedExpr.index Kind.storage tyR pathR idxR)))
        (execBlock s [Stmt.stackDecl idxR.ty indexAliasName (some idxR),
          Stmt.assign lhs (WrappedExpr.index Kind.storage tyR pathR
            (indexAlias idxR))])
      rw [execStmt, execBlock_pair]
      cases hev : evalValue s idxR with
      | error err =>
          have hcap' : resolveS s
              (WrappedExpr.index Kind.storage tyR pathR idxR) =
              .error err := by
            rw [resolveS, hb]
            simp only [resOk_bind]
            rw [evalInt, hev]
            rfl
          have hL : execAssign s lhs
              (WrappedExpr.index Kind.storage tyR pathR idxR) =
              .error err :=
            execAssign_storageRhsErr hlhs rfl hnm
              (fun u => by rw [evalValue]) hcap'
          have hR : execStmt s
              (Stmt.stackDecl idxR.ty indexAliasName (some idxR)) =
              .error err := by
            rw [execStmt, hev]
            rfl
          rw [hL, hR]
          exact rfl
      | ok x =>
          obtain ⟨t, v⟩ := x
          have hts : t = s := evalValue_pure hpi hev
          subst hts
          have hR : execStmt t
              (Stmt.stackDecl idxR.ty indexAliasName (some idxR)) =
              .ok (t.setEnv indexAliasName (Binding.val v)) := by
            rw [execStmt, hev]
            rfl
          rw [hR]
          have ht' : EnvAgreeExcept aliasNames t
              (t.setEnv indexAliasName (Binding.val v)) :=
            (EnvAgreeExcept.refl _ t).setEnv_right idx_mem _
          have hres : ResAgree aliasNames
              (resolveS t (WrappedExpr.index Kind.storage tyR pathR idxR))
              (resolveS (t.setEnv indexAliasName (Binding.val v))
                (WrappedExpr.index Kind.storage tyR pathR
                  (indexAlias idxR))) := by
            rw [resolveS, resolveS, hb, resolveS_transport ht' hfp hpp hb]
            simp only [resOk_bind]
            rw [evalInt, evalInt, hev, indexAlias,
              evalValue_alias idxR.ty
                (lookupBy_setBy_self indexAliasName (Binding.val v) t.env)]
            simp only [resOk_bind]
            cases v.asInt with
            | error err => exact rfl
            | ok i => exact ⟨rfl, ht'⟩
          show ResultsAgree aliasNames
            (execAssign t lhs
              (WrappedExpr.index Kind.storage tyR pathR idxR))
            (execStmt (t.setEnv indexAliasName (Binding.val v))
              (Stmt.assign lhs (WrappedExpr.index Kind.storage tyR pathR
                (indexAlias idxR))))
          rw [execStmt]
          refine execAssign_pureLocSim hlhs hfl rfl rfl ?_ ?_ ?_
          · rw [evalValue, evalValue]
            refine ResAgree.bind hres ?_
            intro u₁ u₂ a hu
            obtain ⟨root', segs'⟩ := a
            simp only [findStorage_congr hu]
            refine bindPureRes_agree _ fun w => ?_
            exact bindPureRes_agree _ fun val => ⟨rfl, hu⟩
          · intro _
            exact hres
          · intro hm
            exact nomatch hm

theorem binopUnfoldLeft_sound (op : BinOp)
    (s : State) (lhs : PlaceExpr) (rhs : WrappedExpr)
    (hcond : (ruleEffect (.binopUnfoldLeft op)).cond
      (Stmt.assign lhs rhs))
    (hfresh : ∀ n ∈ aliasNames,
      stmtUsesVar (Stmt.assign lhs rhs) n = false) :
    ResultsAgree aliasNames
      (execStmt s (Stmt.assign lhs rhs))
      (execBlock s ((ruleEffect (.binopUnfoldLeft op)).block
        (Stmt.assign lhs rhs) hcond)) := by
  match rhs, hcond, hfresh with
  | .mkBinop op' l r, hcond, hfresh =>
      obtain ⟨name, hloc⟩ := stackVarLoc lhs hcond.2.1.1 hcond.2.1.2
      have hfr : ∀ n ∈ aliasNames, usesVar r n = false := fun n hn => by
        have := hfresh n hn
        simp [stmtUsesVar, usesVar] at this
        exact this.2.2
      show ResultsAgree aliasNames
        (execStmt s (Stmt.assign lhs (WrappedExpr.binop op' l r)))
        (execBlock s [Stmt.stackDecl l.ty valueAliasName (some l),
          Stmt.assign lhs (WrappedExpr.binop op' (stackValueAlias l) r)])
      rw [execStmt, execBlock_pair]
      cases hev : evalValue s l with
      | error err =>
          have hL : execAssign s lhs (WrappedExpr.binop op' l r) =
              .error err := by
            rw [execAssign_stackVar hloc, evalValue, hev]
            rfl
          have hR : execStmt s
              (Stmt.stackDecl l.ty valueAliasName (some l)) = .error err := by
            rw [execStmt, hev]
            rfl
          rw [hL, hR]
          exact rfl
      | ok x =>
          obtain ⟨t, v⟩ := x
          have hR : execStmt s
              (Stmt.stackDecl l.ty valueAliasName (some l)) =
              .ok (t.setEnv valueAliasName (Binding.val v)) := by
            rw [execStmt, hev]
            rfl
          rw [hR]
          have ht' : EnvAgreeExcept aliasNames t
              (t.setEnv valueAliasName (Binding.val v)) :=
            (EnvAgreeExcept.refl _ t).setEnv_right pv_mem _
          show ResultsAgree aliasNames
            (execAssign s lhs (WrappedExpr.binop op' l r))
            (execStmt (t.setEnv valueAliasName (Binding.val v))
              (Stmt.assign lhs
                (WrappedExpr.binop op' (stackValueAlias l) r)))
          rw [execStmt, execAssign_stackVar hloc, execAssign_stackVar hloc]
          rw [evalValue, evalValue, hev, stackValueAlias,
            evalValue_alias l.ty
              (lookupBy_setBy_self valueAliasName (Binding.val v) t.env)]
          simp only [resOk_bind]
          have hrest : ResultsAgree aliasNames
              (((evalValue t r) >>= fun x =>
                  (applyBinOp op' v x.2) >>= fun w =>
                    (checkArith (op'.retTy l.ty) w) >>= fun w' =>
                      Except.ok (x.1, w')) >>=
                fun y => Except.ok (y.1.setEnv name (Binding.val y.2)))
              (((evalValue (t.setEnv valueAliasName (Binding.val v)) r) >>=
                  fun x =>
                    (applyBinOp op' v x.2) >>= fun w =>
                      (checkArith (op'.retTy l.ty) w) >>= fun w' =>
                        Except.ok (x.1, w')) >>=
                fun y => Except.ok (y.1.setEnv name (Binding.val y.2))) := by
            refine ResAgree.bindState ?_ ?_
            · refine ResAgree.bind (evalValue_agree ht' r hfr) ?_
              intro u₁ u₂ rv hu
              refine bindPureRes_agree _ fun w => ?_
              exact bindPureRes_agree _ fun w' => ⟨rfl, hu⟩
            · intro u₁ u₂ w hu
              exact hu.setEnv_both name (Binding.val w)
          cases op' <;>
            first
            | exact hrest
            | (cases v with
                | int i => exact hrest
                | bool b =>
                    cases b <;>
                      first
                      | exact ht'.setEnv_both name _
                      | exact hrest)

theorem binopUnfoldRight_sound (op : BinOp)
    (s : State) (lhs : PlaceExpr) (rhs : WrappedExpr) (lv : Value)
    (hcond : (ruleEffect (.binopUnfoldRight op)).cond
      (Stmt.assign lhs rhs))
    (hfresh : ∀ n ∈ aliasNames,
      stmtUsesVar (Stmt.assign lhs rhs) n = false)
    (hlv : ∀ {op' : BinOp} {l r : WrappedExpr},
      rhs = WrappedExpr.binop op' l r -> evalValue s l = .ok (s, lv))
    (hpr : ∀ {op' : BinOp} {l r : WrappedExpr},
      rhs = WrappedExpr.binop op' l r -> pureExpr r = true) :
    ResultsAgree aliasNames
      (execStmt s (Stmt.assign lhs rhs))
      (execBlock s ((ruleEffect (.binopUnfoldRight op)).block
        (Stmt.assign lhs rhs) hcond)) := by
  revert hlv hpr
  match rhs, hcond, hfresh with
  | .mkBinop op' l r, hcond, hfresh =>
      intro hlv hpr
      obtain ⟨heq, hsc, hsv, hsl, hcr⟩ := hcond
      have hsc' : op'.shortCircuits = false := heq ▸ hsc
      have hlveq : evalValue s l = .ok (s, lv) := hlv rfl
      have hprr : pureExpr r = true := hpr rfl
      obtain ⟨name, hloc⟩ := stackVarLoc lhs hsv.1 hsv.2
      have hfl2 : ∀ n ∈ aliasNames, usesVar l n = false := fun n hn => by
        have := hfresh n hn
        simp [stmtUsesVar, usesVar] at this
        exact this.2.1
      show ResultsAgree aliasNames
        (execStmt s (Stmt.assign lhs (WrappedExpr.binop op' l r)))
        (execBlock s [Stmt.stackDecl r.ty valueAliasName (some r),
          Stmt.assign lhs (WrappedExpr.binop op' l (stackValueAlias r))])
      rw [execStmt, execBlock_pair]
      cases hev : evalValue s r with
      | error err =>
          have hL : execAssign s lhs (WrappedExpr.binop op' l r) =
              .error err := by
            rw [execAssign_stackVar hloc, evalValue, hlveq]
            simp only [resOk_bind]
            cases op' <;>
              first
              | (rw [hev]
                 cases lv with
                 | int i => rfl
                 | bool b => cases b <;> rfl)
              | exact absurd hsc' (by decide)
          have hR : execStmt s
              (Stmt.stackDecl r.ty valueAliasName (some r)) = .error err := by
            rw [execStmt, hev]
            rfl
          rw [hL, hR]
          exact rfl
      | ok x =>
          obtain ⟨t, v⟩ := x
          have hts : t = s := evalValue_pure hprr hev
          subst hts
          have hR : execStmt t
              (Stmt.stackDecl r.ty valueAliasName (some r)) =
              .ok (t.setEnv valueAliasName (Binding.val v)) := by
            rw [execStmt, hev]
            rfl
          rw [hR]
          have ht' : EnvAgreeExcept aliasNames t
              (t.setEnv valueAliasName (Binding.val v)) :=
            (EnvAgreeExcept.refl _ t).setEnv_right pv_mem _
          have hlv' : evalValue (t.setEnv valueAliasName (Binding.val v)) l =
              .ok (t.setEnv valueAliasName (Binding.val v), lv) := by
            have h := evalValue_agree ht' l hfl2
            rw [hlveq] at h
            rcases h.cases with ⟨err, h1, h2⟩ | ⟨u₁, u₂, a, h1, h2, hu⟩
            · exact nomatch h1
            · have ha : a = lv := (congrArg Prod.snd (Except.ok.inj h1)).symm
              have hu2 : u₂ = t.setEnv valueAliasName (Binding.val v) :=
                evalValue_pure (pure_of_simple hsl) h2
              rw [h2, hu2, ha]
          show ResultsAgree aliasNames
            (execAssign t lhs (WrappedExpr.binop op' l r))
            (execStmt (t.setEnv valueAliasName (Binding.val v))
              (Stmt.assign lhs
                (WrappedExpr.binop op' l (stackValueAlias r))))
          rw [execStmt, execAssign_stackVar hloc, execAssign_stackVar hloc]
          rw [evalValue, evalValue, hlveq, hlv']
          simp only [resOk_bind]
          have he' : evalValue (t.setEnv valueAliasName (Binding.val v))
              (stackValueAlias r) =
              .ok (t.setEnv valueAliasName (Binding.val v), v) := by
            rw [stackValueAlias,
              evalValue_alias r.ty
                (lookupBy_setBy_self valueAliasName (Binding.val v) t.env)]
          have hrest : ResultsAgree aliasNames
              (((evalValue t r) >>= fun x =>
                  (applyBinOp op' lv x.2) >>= fun w =>
                    (checkArith (op'.retTy l.ty) w) >>= fun w' =>
                      Except.ok (x.1, w')) >>=
                fun y => Except.ok (y.1.setEnv name (Binding.val y.2)))
              (((evalValue (t.setEnv valueAliasName (Binding.val v))
                  (stackValueAlias r)) >>= fun x =>
                  (applyBinOp op' lv x.2) >>= fun w =>
                    (checkArith (op'.retTy l.ty) w) >>= fun w' =>
                      Except.ok (x.1, w')) >>=
                fun y => Except.ok (y.1.setEnv name (Binding.val y.2))) := by
            rw [hev, he']
            simp only [resOk_bind]
            cases applyBinOp op' lv v with
            | error e => exact rfl
            | ok w =>
                simp only [resOk_bind]
                cases checkArith (op'.retTy l.ty) w with
                | error e => exact rfl
                | ok w' => exact ht'.setEnv_both name (Binding.val w')
          cases op' <;>
            first
            | exact hrest
            | (cases lv with
                | int i => exact hrest
                | bool b =>
                    cases b <;>
                      first
                      | exact ht'.setEnv_both name _
                      | exact hrest)

/-- KeY `logicalAndShortCircuitRhs`: `v = se && nse;` rewrites to
`if (se) { v = nse } else { v = false }` (the Lean image of KeY's ternary
`v = se ? nse : false;`). Sound relative to the operands evaluating to
booleans — the interpreter's `applyBinOp` guard is a typing check the
residual no longer performs, exactly as in KeY, where the program is
well-typed by construction. -/
theorem logicalAndShortCircuitRhs_sound
    (s : State) (lhs : PlaceExpr) (rhs : WrappedExpr) (lb : Bool)
    (hcond : (ruleEffect .logicalAndShortCircuitRhs).cond
      (Stmt.assign lhs rhs))
    (hlv : ∀ {op' : BinOp} {l r : WrappedExpr},
      rhs = WrappedExpr.binop op' l r -> evalValue s l = .ok (s, Value.bool lb))
    (hrb : ∀ {op' : BinOp} {l r : WrappedExpr} {t : State} {v : Value},
      rhs = WrappedExpr.binop op' l r -> evalValue s r = .ok (t, v) ->
        ∃ b, v = Value.bool b) :
    ResultsAgree aliasNames
      (execStmt s (Stmt.assign lhs rhs))
      (execBlock s ((ruleEffect .logicalAndShortCircuitRhs).block
        (Stmt.assign lhs rhs) hcond)) := by
  revert hlv hrb
  match rhs, hcond with
  | .mkBinop op' l r, hcond =>
      intro hlv hrb
      obtain ⟨heq, hsv, hsl, hcr⟩ := hcond
      subst heq
      have hlveq : evalValue s l = .ok (s, Value.bool lb) := hlv rfl
      obtain ⟨name, hloc⟩ := stackVarLoc lhs hsv.1 hsv.2
      show ResultsAgree aliasNames
        (execStmt s (Stmt.assign lhs (WrappedExpr.binop BinOp.and l r)))
        (execBlock s
          [Stmt.ite l [Stmt.assign lhs r]
            [Stmt.assign lhs (WrappedExpr.bool false)]])
      rw [execStmt, execBlock_single, execStmt,
        execAssign_stackVar hloc, evalValue, hlveq]
      simp only [resOk_bind]
      cases lb with
      | false =>
          show ResultsAgree aliasNames
            (.ok (s.setEnv name (Binding.val (Value.bool false))))
            (execBlock s [Stmt.assign lhs (WrappedExpr.bool false)])
          rw [execBlock_single, execStmt, execAssign_stackVar hloc,
            evalValue]
          exact EnvAgreeExcept.refl _ _
      | true =>
          show ResultsAgree aliasNames
            ((evalValue s r >>= fun x =>
                (applyBinOp BinOp.and (Value.bool true) x.2) >>=
                  fun w =>
                    (checkArith (BinOp.and.retTy l.ty) w) >>= fun w' =>
                      Except.ok (x.1, w')) >>=
              fun y => Except.ok (y.1.setEnv name (Binding.val y.2)))
            (execBlock s [Stmt.assign lhs r])
          rw [execBlock_single, execStmt, execAssign_stackVar hloc]
          cases hev : evalValue s r with
          | error err => exact rfl
          | ok x =>
              obtain ⟨t, v⟩ := x
              obtain ⟨b, rfl⟩ := hrb rfl hev
              simp only [resOk_bind, applyBinOp, Value.asBool, resOk_bind,
                Bool.true_and, checkArith, BinOp.retTy, BinOp.isArith]
              exact EnvAgreeExcept.refl _ _

/-- KeY `logicalOrShortCircuitRhs`: `v = se || nse;` rewrites to
`if (se) { v = true } else { v = nse }`. See
`logicalAndShortCircuitRhs_sound` for the typing caveat. -/
theorem logicalOrShortCircuitRhs_sound
    (s : State) (lhs : PlaceExpr) (rhs : WrappedExpr) (lb : Bool)
    (hcond : (ruleEffect .logicalOrShortCircuitRhs).cond
      (Stmt.assign lhs rhs))
    (hlv : ∀ {op' : BinOp} {l r : WrappedExpr},
      rhs = WrappedExpr.binop op' l r -> evalValue s l = .ok (s, Value.bool lb))
    (hrb : ∀ {op' : BinOp} {l r : WrappedExpr} {t : State} {v : Value},
      rhs = WrappedExpr.binop op' l r -> evalValue s r = .ok (t, v) ->
        ∃ b, v = Value.bool b) :
    ResultsAgree aliasNames
      (execStmt s (Stmt.assign lhs rhs))
      (execBlock s ((ruleEffect .logicalOrShortCircuitRhs).block
        (Stmt.assign lhs rhs) hcond)) := by
  revert hlv hrb
  match rhs, hcond with
  | .mkBinop op' l r, hcond =>
      intro hlv hrb
      obtain ⟨heq, hsv, hsl, hcr⟩ := hcond
      subst heq
      have hlveq : evalValue s l = .ok (s, Value.bool lb) := hlv rfl
      obtain ⟨name, hloc⟩ := stackVarLoc lhs hsv.1 hsv.2
      show ResultsAgree aliasNames
        (execStmt s (Stmt.assign lhs (WrappedExpr.binop BinOp.or l r)))
        (execBlock s
          [Stmt.ite l [Stmt.assign lhs (WrappedExpr.bool true)]
            [Stmt.assign lhs r]])
      rw [execStmt, execBlock_single, execStmt,
        execAssign_stackVar hloc, evalValue, hlveq]
      simp only [resOk_bind]
      cases lb with
      | true =>
          show ResultsAgree aliasNames
            (.ok (s.setEnv name (Binding.val (Value.bool true))))
            (execBlock s [Stmt.assign lhs (WrappedExpr.bool true)])
          rw [execBlock_single, execStmt, execAssign_stackVar hloc,
            evalValue]
          exact EnvAgreeExcept.refl _ _
      | false =>
          show ResultsAgree aliasNames
            ((evalValue s r >>= fun x =>
                (applyBinOp BinOp.or (Value.bool false) x.2) >>=
                  fun w =>
                    (checkArith (BinOp.or.retTy l.ty) w) >>= fun w' =>
                      Except.ok (x.1, w')) >>=
              fun y => Except.ok (y.1.setEnv name (Binding.val y.2)))
            (execBlock s [Stmt.assign lhs r])
          rw [execBlock_single, execStmt, execAssign_stackVar hloc]
          cases hev : evalValue s r with
          | error err => exact rfl
          | ok x =>
              obtain ⟨t, v⟩ := x
              obtain ⟨b, rfl⟩ := hrb rfl hev
              simp only [resOk_bind, applyBinOp, Value.asBool, resOk_bind,
                Bool.false_or, checkArith, BinOp.retTy, BinOp.isArith]
              exact EnvAgreeExcept.refl _ _

theorem binopUnfoldResult_sound (op : BinOp)
    (s : State) (lhs : PlaceExpr) (rhs : WrappedExpr) {loc : Loc}
    (hcond : (ruleEffect (.binopUnfoldResult op)).cond
      (Stmt.assign lhs rhs))
    (hfresh : ∀ n ∈ aliasNames,
      stmtUsesVar (Stmt.assign lhs rhs) n = false)
    (hlhs : resolveLoc s lhs.expr = .ok (s, loc))
    (hplhs : pureExpr lhs.expr = true)
    (hprim : rhs.ty.isPrimitive = true)
    (hnsl : ∀ nm, loc ≠ Loc.storageLocal nm)
    (hnmr : ∀ nm, loc ≠ Loc.memoryRoot nm) :
    ResultsAgree aliasNames
      (execStmt s (Stmt.assign lhs rhs))
      (execBlock s ((ruleEffect (.binopUnfoldResult op)).block
        (Stmt.assign lhs rhs) hcond)) := by
  revert hprim
  match rhs, hcond, hfresh with
  | .mkBinop op' l r, hcond, hfresh =>
      intro hprim
      have hpl : pureExpr l = true := pure_of_simple hcond.2.2.2.2.1
      have hpr : pureExpr r = true := pure_of_simple hcond.2.2.2.2.2
      have hpfull : pureExpr (WrappedExpr.binop op' l r) = true := by
        simp [pureExpr, hpl, hpr]
      have hfl : ∀ n ∈ aliasNames, usesVar lhs.expr n = false := fun n hn => by
        have := hfresh n hn
        simp [stmtUsesVar] at this
        exact this.1
      show ResultsAgree aliasNames
        (execStmt s (Stmt.assign lhs (WrappedExpr.binop op' l r)))
        (execBlock s
          [Stmt.stackDecl (WrappedExpr.binop op' l r).ty valueAliasName
            (some (WrappedExpr.binop op' l r)),
          Stmt.assign lhs
            (stackValueAlias (WrappedExpr.binop op' l r))])
      rw [execStmt, execBlock_pair]
      cases hev : evalValue s (WrappedExpr.binop op' l r) with
      | error err =>
          have hL : execAssign s lhs (WrappedExpr.binop op' l r) =
              .error err := execAssign_evalErr hlhs hprim hnsl hnmr hev
          have hR : execStmt s
              (Stmt.stackDecl (WrappedExpr.binop op' l r).ty valueAliasName
                (some (WrappedExpr.binop op' l r))) = .error err := by
            rw [execStmt, hev]
            rfl
          rw [hL, hR]
          exact rfl
      | ok x =>
          obtain ⟨t, v⟩ := x
          have hts : t = s := evalValue_pure hpfull hev
          subst hts
          have hR : execStmt t
              (Stmt.stackDecl (WrappedExpr.binop op' l r).ty valueAliasName
                (some (WrappedExpr.binop op' l r))) =
              .ok (t.setEnv valueAliasName (Binding.val v)) := by
            rw [execStmt, hev]
            rfl
          rw [hR]
          have ht' : EnvAgreeExcept aliasNames t
              (t.setEnv valueAliasName (Binding.val v)) :=
            (EnvAgreeExcept.refl _ t).setEnv_right pv_mem _
          show ResultsAgree aliasNames
            (execAssign t lhs (WrappedExpr.binop op' l r))
            (execStmt (t.setEnv valueAliasName (Binding.val v))
              (Stmt.assign lhs
                (stackValueAlias (WrappedExpr.binop op' l r))))
          rw [execStmt]
          refine execAssign_pureLocSim hlhs hfl rfl rfl ?_ ?_ ?_
          · rw [hev, stackValueAlias,
              evalValue_alias (WrappedExpr.binop op' l r).ty
                (lookupBy_setBy_self valueAliasName (Binding.val v) t.env)]
            exact ⟨rfl, ht'⟩
          · intro _
            have h1 : resolveS t (WrappedExpr.binop op' l r) =
                .error .stuck := by
              rw [resolveS.eq_def]
            have h2 : resolveS (t.setEnv valueAliasName (Binding.val v))
                (stackValueAlias (WrappedExpr.binop op' l r)) =
                .error .stuck := by
              rw [stackValueAlias, aliasExpr, resolveS, aliasField_name]
              simp [State.setEnv, lookupBy_setBy_self]
            rw [h1, h2]
            exact rfl
          · intro hm
            exact nomatch hm

/-! ## Compound-assignment and inc/dec unfolds -/

theorem evalValue_transportErr {ns : List Name} {s t' : State}
    {e : WrappedExpr} {err : Halt}
    (hagree : EnvAgreeExcept ns s t')
    (hf : ∀ n ∈ ns, usesVar e n = false)
    (h : evalValue s e = .error err) : evalValue t' e = .error err := by
  have hh := evalValue_agree hagree e hf
  rw [h] at hh
  rcases hh.cases with ⟨e', h1, h2⟩ | ⟨u₁, u₂, a, h1, h2, hu⟩
  · rw [h2, Except.error.inj h1]
  · exact nomatch h1

theorem evalValue_transportOk {ns : List Name} {s t' : State}
    {e : WrappedExpr} {v : Value}
    (hagree : EnvAgreeExcept ns s t')
    (hf : ∀ n ∈ ns, usesVar e n = false)
    (hp : pureExpr e = true)
    (h : evalValue s e = .ok (s, v)) : evalValue t' e = .ok (t', v) := by
  have hh := evalValue_agree hagree e hf
  rw [h] at hh
  rcases hh.cases with ⟨e', h1, h2⟩ | ⟨u₁, u₂, a, h1, h2, hu⟩
  · exact nomatch h1
  · have ha : a = v := (congrArg Prod.snd (Except.ok.inj h1)).symm
    have hu2 : u₂ = t' := evalValue_pure hp h2
    rw [h2, hu2, ha]

/-- The shared tail of a compound assignment, once both sides have
resolved the same location from agreeing states. -/
theorem compoundTail_agree {ns : List Name} {s₂ t₃ : State} {op' : BinOp}
    {ty : Ty} {loc : Loc} {v : Value}
    (hag : EnvAgreeExcept ns s₂ t₃) (hfr : LocFresh ns loc) :
    ResultsAgree ns
      ((readLoc s₂ loc) >>= fun old => (applyBinOp op' old v) >>= fun new =>
        (checkArith ty new) >>= fun new' => writeLoc s₂ loc new')
      ((readLoc t₃ loc) >>= fun old => (applyBinOp op' old v) >>= fun new =>
        (checkArith ty new) >>= fun new' => writeLoc t₃ loc new') := by
  rw [readLoc_congr hag hfr]
  refine bindPureResults_agree _ fun oldv => ?_
  refine bindPureResults_agree _ fun new => ?_
  refine bindPureResults_agree _ fun new' => ?_
  exact writeLoc_agree hag new'

/-- `compoundAssignValueRhsCapture op` (KeY `addAssignValueRhsCapture`,
...): hoisting a nonsimple compound-assignment RHS into `pv` preserves
the statement's meaning. The interpreter reads the target's old value
*before* the RHS runs while the residual reads it *after* the capture,
so `hstableOld` demands the target's value survive the RHS's effects —
the compound-assignment image of `valueRhsCaptureAssign_sound`'s
non-interference condition. -/
theorem compoundAssignValueRhsCapture_sound (op : BinOp)
    (s : State) (op' : BinOp) (lhs : PlaceExpr) (rhs : WrappedExpr)
    {old : Value}
    (hcond : (ruleEffect (.compoundAssignValueRhsCapture op)).cond
      (Stmt.compoundAssign op' lhs rhs))
    (hfresh : ∀ n ∈ aliasNames,
      stmtUsesVar (Stmt.compoundAssign op' lhs rhs) n = false)
    (hplhs : pureExpr lhs.expr = true)
    (hold : evalValue s lhs.expr = .ok (s, old))
    (hstableOld : ∀ t v, evalValue s rhs = .ok (t, v) ->
      evalValue t lhs.expr = .ok (t, old)) :
    ResultsAgree aliasNames
      (execStmt s (Stmt.compoundAssign op' lhs rhs))
      (execBlock s ((ruleEffect (.compoundAssignValueRhsCapture op)).block
        (Stmt.compoundAssign op' lhs rhs) hcond)) := by
  have hfl : ∀ n ∈ aliasNames, usesVar lhs.expr n = false := fun n hn => by
    have := hfresh n hn
    simp [stmtUsesVar] at this
    exact this.1
  have hfr : ∀ n ∈ aliasNames, usesVar rhs n = false := fun n hn => by
    have := hfresh n hn
    simp [stmtUsesVar] at this
    exact this.2
  show ResultsAgree aliasNames
    (execStmt s (Stmt.compoundAssign op' lhs rhs))
    (execBlock s [captureStackValue rhs,
      Stmt.compoundAssign op' lhs (stackValueAlias rhs)])
  rw [execStmt, execBlock_pair, captureStackValue, capture]
  cases hev : evalValue s rhs with
  | error err =>
      have hR : execStmt s (Stmt.stackDecl rhs.ty valueAliasName (some rhs)) =
          .error err := by
        rw [execStmt, hev]
        rfl
      rw [hR]
      exact rfl
  | ok x =>
      obtain ⟨t, v⟩ := x
      have hR : execStmt s (Stmt.stackDecl rhs.ty valueAliasName (some rhs)) =
          .ok (t.setEnv valueAliasName (Binding.val v)) := by
        rw [execStmt, hev]
        rfl
      rw [hR]
      simp only [resOk_bind]
      have ht' : EnvAgreeExcept aliasNames t
          (t.setEnv valueAliasName (Binding.val v)) :=
        (EnvAgreeExcept.refl _ t).setEnv_right pv_mem _
      show ResultsAgree aliasNames _
        (execStmt (t.setEnv valueAliasName (Binding.val v))
          (Stmt.compoundAssign op' lhs (stackValueAlias rhs)))
      rw [execStmt]
      have hevA : evalValue (t.setEnv valueAliasName (Binding.val v))
          (stackValueAlias rhs) =
          .ok (t.setEnv valueAliasName (Binding.val v), v) := by
        rw [stackValueAlias,
          evalValue_alias rhs.ty
            (lookupBy_setBy_self valueAliasName (Binding.val v) t.env)]
      rw [hevA]
      simp only [resOk_bind]
      refine ResAgree.bindStateWith (resolveLoc_agree ht' lhs.expr hfl) ?_
      intro u₁ u₂ loc' h₁ h₂ hu
      have hfresh' : LocFresh aliasNames loc' := resolveLoc_fresh hfl h₁
      rw [readLoc_congr hu hfresh']
      refine bindPureResults_agree _ fun oldv => ?_
      refine bindPureResults_agree _ fun new => ?_
      refine bindPureResults_agree _ fun new' => ?_
      exact writeLoc_agree hu new'

/-- `a[i++].x += i` is in scope now.  `compoundAssign` is value-first
like plain assignment (`Semantics.execStmt`), and the residual now freezes
the value into `rv` before capturing the path — so the old `hppath` and
`hrsOk` are both gone, and only freshness of the path remains. -/
theorem storageFieldCompoundAssignUnfoldLeftFst_sound (op : BinOp)
    (s : State) (op' : BinOp) (lhs : PlaceExpr) (rhs : WrappedExpr)
    (hcond : (ruleEffect
      (.storageFieldCompoundAssignUnfoldLeftFst op)).cond
      (Stmt.compoundAssign op' lhs rhs))
    (hfresh : ∀ n ∈ aliasNames,
      stmtUsesVar (Stmt.compoundAssign op' lhs rhs) n = false) :
    ResultsAgree aliasNames
      (execStmt s (Stmt.compoundAssign op' lhs rhs))
      (execBlock s
        ((ruleEffect (.storageFieldCompoundAssignUnfoldLeftFst op)).block
          (Stmt.compoundAssign op' lhs rhs) hcond)) := by
  obtain ⟨e, hass⟩ := lhs
  match e, hass, hcond, hfresh with
  | WrappedExpr.field Kind.storage ty path fld, hass, hcond, hfresh =>
      have hfp : ∀ n ∈ aliasNames, usesVar path n = false := fun n hn => by
        have := hfresh n hn
        simp [stmtUsesVar] at this
        exact this.1
      show ResultsAgree aliasNames
        (execStmt s (Stmt.compoundAssign op'
          (PlaceExpr.field Kind.storage ty path fld) rhs))
        (execBlock s [captureRhsValue rhs, captureStoragePath path,
          Stmt.compoundAssign op'
            (fieldFromAlias Kind.storage storagePathAliasName ty path fld)
            (rhsValueAlias rhs)])
      rw [execStmt, execBlock_triple, captureRhsValue, capture, execStmt,
        placeField_expr]
      cases hevR : evalValue s rhs with
      | error err => simp only [hevR]; rfl
      | ok x =>
          obtain ⟨s₁, v⟩ := x
          simp only [hevR, resOk_bind]
          have hrv₁ : lookupBy rhsValueAliasName
              (s₁.setEnv rhsValueAliasName (Binding.val v)).env =
                some (Binding.val v) := lookupBy_setBy_self ..
          have hagree₁ : EnvAgreeExcept aliasNames s₁
              (s₁.setEnv rhsValueAliasName (Binding.val v)) :=
            (EnvAgreeExcept.refl _ s₁).setEnv_right rv_mem _
          have hL : ((resolveLoc s₁ (WrappedExpr.field Kind.storage ty path fld))
                >>= fun d =>
                  (readLoc d.fst d.snd) >>= fun old =>
                    (applyBinOp op' old v) >>= fun new =>
                      (checkArith
                        (WrappedExpr.field Kind.storage ty path fld).ty new)
                        >>= fun new' => writeLoc d.fst d.snd new') =
              (resolveS s₁ path) >>= fun y => match y with
                | (s₂, root, segs) =>
                    (readLoc s₂ (Loc.storage root (segs ++ [Seg.field fld.name])))
                      >>= fun old => (applyBinOp op' old v) >>= fun new =>
                        (checkArith ty new) >>= fun new' =>
                          writeLoc s₂ (Loc.storage root
                            (segs ++ [Seg.field fld.name])) new' := by
            rw [resolveLoc, resolveS]
            cases resolveS s₁ path with
            | error e => rfl
            | ok y => obtain ⟨s₂, root, segs⟩ := y; rfl
          have hR : execBlock (s₁.setEnv rhsValueAliasName (Binding.val v))
              [captureStoragePath path,
                Stmt.compoundAssign op'
                  (fieldFromAlias Kind.storage storagePathAliasName ty path fld)
                  (rhsValueAlias rhs)] =
              (resolveS (s₁.setEnv rhsValueAliasName (Binding.val v)) path) >>=
                fun y => match y with
                  | (t₂, root, segs) =>
                      execStmt (t₂.setEnv storagePathAliasName
                        (Binding.spath root segs))
                        (Stmt.compoundAssign op'
                          (fieldFromAlias Kind.storage storagePathAliasName ty
                            path fld)
                          (rhsValueAlias rhs)) := by
            rw [execBlock_pair, captureStoragePath, capture, execStmt]
            cases resolveS (s₁.setEnv rhsValueAliasName (Binding.val v)) path with
            | error e => rfl
            | ok y => obtain ⟨t₂, root, segs⟩ := y; rfl
          rw [hL, hR]
          refine ResAgree.bindStateWith (resolveS_agree hagree₁ path hfp) ?_
          intro s₂ t₂ a _ hres₂ hagree₂
          obtain ⟨root, segs⟩ := a
          simp only []
          have hrv₃ : lookupBy rhsValueAliasName
              (t₂.setEnv storagePathAliasName (Binding.spath root segs)).env =
                some (Binding.val v) := by
            rw [State.setEnv, lookupBy_setBy_ne (Ne.symm sp_ne_rv),
              resolveS_keep (s₁.setEnv rhsValueAliasName (Binding.val v)) path
                hfp t₂ (root, segs) hres₂ _ rv_mem]
            exact hrv₁
          have hsp₃ : lookupBy storagePathAliasName
              (t₂.setEnv storagePathAliasName (Binding.spath root segs)).env =
                some (Binding.spath root segs) := lookupBy_setBy_self ..
          have hRA : execStmt
              (t₂.setEnv storagePathAliasName (Binding.spath root segs))
              (Stmt.compoundAssign op'
                (fieldFromAlias Kind.storage storagePathAliasName ty path fld)
                (rhsValueAlias rhs)) =
              (readLoc (t₂.setEnv storagePathAliasName (Binding.spath root segs))
                (Loc.storage root (segs ++ [Seg.field fld.name]))) >>= fun old =>
                (applyBinOp op' old v) >>= fun new =>
                  (checkArith ty new) >>= fun new' =>
                    writeLoc (t₂.setEnv storagePathAliasName
                      (Binding.spath root segs))
                      (Loc.storage root (segs ++ [Seg.field fld.name])) new' := by
            rw [execStmt, fieldFromAlias, placeField_expr, rhsValueAlias,
              evalValue_alias rhs.ty hrv₃]
            simp only [resOk_bind]
            rw [resolveLoc, resolveS, resolveS_alias path.ty hsp₃]
            rfl
          rw [hRA]
          exact compoundTail_agree (hagree₂.setEnv_right sp_mem _) trivial

theorem storageFieldIncDecUnfoldLeftFst_sound (op : IncDec)
    (s : State) (expr : WrappedExpr)
    (hcond : (ruleEffect (.storageFieldIncDecUnfoldLeftFst op)).cond
      (Stmt.expr expr))
    (hppath : ∀ {op'' kind ty path fld},
      expr = WrappedExpr.incDec op''
        (WrappedExpr.field kind ty path fld) -> pureExpr path = true) :
    ResultsAgree aliasNames
      (execStmt s (Stmt.expr expr))
      (execBlock s
        ((ruleEffect (.storageFieldIncDecUnfoldLeftFst op)).block
          (Stmt.expr expr) hcond)) := by
  revert hppath
  match expr, hcond with
  | .mkIncDec op'' (WrappedExpr.field Kind.storage ty path fld), hcond =>
      intro hppath
      have hpp : pureExpr path = true := hppath rfl
      show ResultsAgree aliasNames
        (execStmt s (Stmt.expr (WrappedExpr.incDec op''
          (WrappedExpr.field Kind.storage ty path fld))))
        (execBlock s [captureStoragePath path,
          Stmt.expr (WrappedExpr.incDec op''
            (WrappedExpr.field Kind.storage ty
              (aliasExpr Kind.storage path.ty storagePathAliasName) fld))])
      rw [execStmt, execBlock_pair, captureStoragePath, capture]
      cases hres : resolveS s path with
      | error err =>
          have hR : execStmt s
              (Stmt.storagePlaceAlias path.ty storagePathAliasName path) =
              .error err := by
            rw [execStmt, hres]
            rfl
          rw [hR, evalValue, resolveLoc, resolveS, hres]
          exact rfl
      | ok x =>
          obtain ⟨t, root, segs⟩ := x
          have hts : t = s := resolveS_pure hpp hres
          subst hts
          have hR : execStmt t
              (Stmt.storagePlaceAlias path.ty storagePathAliasName path) =
              .ok (t.setEnv storagePathAliasName (Binding.spath root segs)) := by
            rw [execStmt, hres]
            rfl
          rw [hR]
          have ht' : EnvAgreeExcept aliasNames t
              (t.setEnv storagePathAliasName (Binding.spath root segs)) :=
            (EnvAgreeExcept.refl _ t).setEnv_right sp_mem _
          have halias := resolveS_alias (s := t.setEnv storagePathAliasName
              (Binding.spath root segs)) path.ty
            (lookupBy_setBy_self storagePathAliasName
              (Binding.spath root segs) t.env)
          have hwl : resolveLoc t
              (WrappedExpr.field Kind.storage ty path fld) =
              .ok (t, Loc.storage root (segs ++ [Seg.field fld.name])) := by
            rw [resolveLoc, resolveS, hres]
            rfl
          have hwr : resolveLoc
              (t.setEnv storagePathAliasName (Binding.spath root segs))
              (WrappedExpr.field Kind.storage ty
                (aliasExpr Kind.storage path.ty storagePathAliasName) fld) =
              .ok (t.setEnv storagePathAliasName (Binding.spath root segs),
                Loc.storage root (segs ++ [Seg.field fld.name])) := by
            rw [resolveLoc, resolveS, halias]
            rfl
          show ResultsAgree aliasNames _
            (execStmt (t.setEnv storagePathAliasName (Binding.spath root segs))
              (Stmt.expr (WrappedExpr.incDec op''
                (WrappedExpr.field Kind.storage ty
                  (aliasExpr Kind.storage path.ty storagePathAliasName) fld))))
          rw [execStmt, evalValue, hwl, evalValue, hwr]
          simp only [resOk_bind]
          rw [readLoc_congr (loc := Loc.storage root
            (segs ++ [Seg.field fld.name])) ht' trivial]
          refine ResAgree.bindState ?_ ?_
          · refine bindPureRes_agree _ fun old => ?_
            refine bindPureRes_agree _ fun oldInt => ?_
            refine bindPureRes_agree _ fun newVal => ?_
            refine ResultsAgree.bindRes (writeLoc_agree ht' newVal) ?_
            intro u₁ u₂ hu
            exact ⟨rfl, hu⟩
          · intro u₁ u₂ vv hu
            exact hu

theorem evalInt_transportErr {ns : List Name} {s t' : State}
    {e : WrappedExpr} {err : Halt}
    (hagree : EnvAgreeExcept ns s t')
    (hf : ∀ n ∈ ns, usesVar e n = false)
    (h : evalInt s e = .error err) : evalInt t' e = .error err := by
  have hh := evalInt_agree hagree e hf
  rw [h] at hh
  rcases hh.cases with ⟨e', h1, h2⟩ | ⟨u₁, u₂, a, h1, h2, hu⟩
  · rw [h2, Except.error.inj h1]
  · exact nomatch h1

theorem evalInt_transportOk {ns : List Name} {s t' : State}
    {e : WrappedExpr} {i : Int}
    (hagree : EnvAgreeExcept ns s t')
    (hf : ∀ n ∈ ns, usesVar e n = false)
    (hp : pureExpr e = true)
    (h : evalInt s e = .ok (s, i)) : evalInt t' e = .ok (t', i) := by
  have hh := evalInt_agree hagree e hf
  rw [h] at hh
  rcases hh.cases with ⟨e', h1, h2⟩ | ⟨u₁, u₂, a, h1, h2, hu⟩
  · exact nomatch h1
  · have ha : a = i := (congrArg Prod.snd (Except.ok.inj h1)).symm
    have hu2 : u₂ = t' := evalInt_pure hp h2
    rw [h2, hu2, ha]

/-- The index twin.  Same story: the value is frozen before the path
capture, so `hppath`/`hrsOk` are gone. -/
theorem storageIndexCompoundAssignUnfoldLeftFst_sound (op : BinOp)
    (s : State) (op' : BinOp) (lhs : PlaceExpr) (rhs : WrappedExpr)
    (hcond : (ruleEffect
      (.storageIndexCompoundAssignUnfoldLeftFst op)).cond
      (Stmt.compoundAssign op' lhs rhs))
    (hfresh : ∀ n ∈ aliasNames,
      stmtUsesVar (Stmt.compoundAssign op' lhs rhs) n = false) :
    ResultsAgree aliasNames
      (execStmt s (Stmt.compoundAssign op' lhs rhs))
      (execBlock s
        ((ruleEffect (.storageIndexCompoundAssignUnfoldLeftFst op)).block
          (Stmt.compoundAssign op' lhs rhs) hcond)) := by
  obtain ⟨e, hass⟩ := lhs
  match e, hass, hcond, hfresh with
  | WrappedExpr.index Kind.storage ty path idxE, hass, hcond, hfresh =>
      have hfp : ∀ n ∈ aliasNames, usesVar path n = false := fun n hn => by
        have := hfresh n hn
        simp [stmtUsesVar, usesVar] at this
        exact this.1.1
      have hfi : ∀ n ∈ aliasNames, usesVar idxE n = false := fun n hn => by
        have := hfresh n hn
        simp [stmtUsesVar, usesVar] at this
        exact this.1.2
      show ResultsAgree aliasNames
        (execStmt s (Stmt.compoundAssign op'
          (PlaceExpr.index Kind.storage ty path idxE) rhs))
        (execBlock s [captureRhsValue rhs, captureStoragePath path,
          Stmt.compoundAssign op'
            (indexFromAlias Kind.storage storagePathAliasName ty path idxE)
            (rhsValueAlias rhs)])
      rw [execStmt, execBlock_triple, captureRhsValue, capture, execStmt,
        placeIndex_expr]
      cases hevR : evalValue s rhs with
      | error err => simp only [hevR]; rfl
      | ok x =>
          obtain ⟨s₁, v⟩ := x
          simp only [hevR, resOk_bind]
          have hrv₁ : lookupBy rhsValueAliasName
              (s₁.setEnv rhsValueAliasName (Binding.val v)).env =
                some (Binding.val v) := lookupBy_setBy_self ..
          have hagree₁ : EnvAgreeExcept aliasNames s₁
              (s₁.setEnv rhsValueAliasName (Binding.val v)) :=
            (EnvAgreeExcept.refl _ s₁).setEnv_right rv_mem _
          have hL : ((resolveLoc s₁ (WrappedExpr.index Kind.storage ty path idxE))
                >>= fun d =>
                  (readLoc d.fst d.snd) >>= fun old =>
                    (applyBinOp op' old v) >>= fun new =>
                      (checkArith
                        (WrappedExpr.index Kind.storage ty path idxE).ty new)
                        >>= fun new' => writeLoc d.fst d.snd new') =
              (resolveS s₁ path) >>= fun y => match y with
                | (s₂, root, segs) =>
                    (evalInt s₂ idxE) >>= fun z => match z with
                      | (s₃, i) =>
                          (readLoc s₃ (Loc.storage root (segs ++ [Seg.at i])))
                            >>= fun old => (applyBinOp op' old v) >>= fun new =>
                              (checkArith ty new) >>= fun new' =>
                                writeLoc s₃
                                  (Loc.storage root (segs ++ [Seg.at i])) new' := by
            rw [resolveLoc]
            cases resolveS s₁ path with
            | error e => rfl
            | ok y =>
                obtain ⟨s₂, root, segs⟩ := y
                simp only [resOk_bind]
                cases evalInt s₂ idxE with
                | error e => rfl
                | ok z => obtain ⟨s₃, i⟩ := z; rfl
          have hR : execBlock (s₁.setEnv rhsValueAliasName (Binding.val v))
              [captureStoragePath path,
                Stmt.compoundAssign op'
                  (indexFromAlias Kind.storage storagePathAliasName ty path idxE)
                  (rhsValueAlias rhs)] =
              (resolveS (s₁.setEnv rhsValueAliasName (Binding.val v)) path) >>=
                fun y => match y with
                  | (t₂, root, segs) =>
                      execStmt (t₂.setEnv storagePathAliasName
                        (Binding.spath root segs))
                        (Stmt.compoundAssign op'
                          (indexFromAlias Kind.storage storagePathAliasName ty
                            path idxE)
                          (rhsValueAlias rhs)) := by
            rw [execBlock_pair, captureStoragePath, capture, execStmt]
            cases resolveS (s₁.setEnv rhsValueAliasName (Binding.val v)) path with
            | error e => rfl
            | ok y => obtain ⟨t₂, root, segs⟩ := y; rfl
          rw [hL, hR]
          refine ResAgree.bindStateWith (resolveS_agree hagree₁ path hfp) ?_
          intro s₂ t₂ a _ hres₂ hagree₂
          obtain ⟨root, segs⟩ := a
          simp only []
          have hrv₃ : lookupBy rhsValueAliasName
              (t₂.setEnv storagePathAliasName (Binding.spath root segs)).env =
                some (Binding.val v) := by
            rw [State.setEnv, lookupBy_setBy_ne (Ne.symm sp_ne_rv),
              resolveS_keep (s₁.setEnv rhsValueAliasName (Binding.val v)) path
                hfp t₂ (root, segs) hres₂ _ rv_mem]
            exact hrv₁
          have hsp₃ : lookupBy storagePathAliasName
              (t₂.setEnv storagePathAliasName (Binding.spath root segs)).env =
                some (Binding.spath root segs) := lookupBy_setBy_self ..
          have hRA : execStmt
              (t₂.setEnv storagePathAliasName (Binding.spath root segs))
              (Stmt.compoundAssign op'
                (indexFromAlias Kind.storage storagePathAliasName ty path idxE)
                (rhsValueAlias rhs)) =
              (evalInt (t₂.setEnv storagePathAliasName (Binding.spath root segs))
                idxE) >>= fun z => match z with
                | (t₃, i) =>
                    (readLoc t₃ (Loc.storage root (segs ++ [Seg.at i])))
                      >>= fun old => (applyBinOp op' old v) >>= fun new =>
                        (checkArith ty new) >>= fun new' =>
                          writeLoc t₃ (Loc.storage root (segs ++ [Seg.at i]))
                            new' := by
            rw [execStmt, indexFromAlias, placeIndex_expr, rhsValueAlias,
              evalValue_alias rhs.ty hrv₃]
            simp only [resOk_bind]
            rw [resolveLoc, resolveS_alias path.ty hsp₃]
            simp only [resOk_bind]
            cases evalInt (t₂.setEnv storagePathAliasName
                (Binding.spath root segs)) idxE with
            | error e => rfl
            | ok z => obtain ⟨t₃, i⟩ := z; rfl
          rw [hRA]
          refine ResAgree.bindStateWith
            (evalInt_agree (hagree₂.setEnv_right sp_mem _) idxE hfi) ?_
          intro s₃ t₃ i _ _ hagree₄
          exact compoundTail_agree hagree₄ trivial

theorem storageIndexIncDecUnfoldLeftFst_sound (op : IncDec)
    (s : State) (expr : WrappedExpr)
    (hcond : (ruleEffect (.storageIndexIncDecUnfoldLeftFst op)).cond
      (Stmt.expr expr))
    (hfresh : ∀ n ∈ aliasNames, stmtUsesVar (Stmt.expr expr) n = false)
    (hppath : ∀ {op'' kind ty path index},
      expr = WrappedExpr.incDec op''
        (WrappedExpr.index kind ty path index) -> pureExpr path = true) :
    ResultsAgree aliasNames
      (execStmt s (Stmt.expr expr))
      (execBlock s
        ((ruleEffect (.storageIndexIncDecUnfoldLeftFst op)).block
          (Stmt.expr expr) hcond)) := by
  revert hppath
  match expr, hcond, hfresh with
  | .mkIncDec op'' (WrappedExpr.index Kind.storage ty path idxE), hcond,
      hfresh =>
      intro hppath
      have hpp : pureExpr path = true := hppath rfl
      have hpi : pureExpr idxE = true := pure_of_simple hcond.2.2
      have hfi : ∀ n ∈ aliasNames, usesVar idxE n = false := fun n hn => by
        have := hfresh n hn
        simp [stmtUsesVar, usesVar] at this
        exact this.2
      show ResultsAgree aliasNames
        (execStmt s (Stmt.expr (WrappedExpr.incDec op''
          (WrappedExpr.index Kind.storage ty path idxE))))
        (execBlock s [captureStoragePath path,
          Stmt.expr (WrappedExpr.incDec op''
            (WrappedExpr.index Kind.storage ty
              (aliasExpr Kind.storage path.ty storagePathAliasName) idxE))])
      rw [execStmt, execBlock_pair, captureStoragePath, capture]
      cases hres : resolveS s path with
      | error err =>
          have hR : execStmt s
              (Stmt.storagePlaceAlias path.ty storagePathAliasName path) =
              .error err := by
            rw [execStmt, hres]
            rfl
          rw [hR, evalValue, resolveLoc, hres]
          exact rfl
      | ok x =>
          obtain ⟨t, root, segs⟩ := x
          have hts : t = s := resolveS_pure hpp hres
          subst hts
          have hR : execStmt t
              (Stmt.storagePlaceAlias path.ty storagePathAliasName path) =
              .ok (t.setEnv storagePathAliasName
                (Binding.spath root segs)) := by
            rw [execStmt, hres]
            rfl
          rw [hR]
          have ht' : EnvAgreeExcept aliasNames t
              (t.setEnv storagePathAliasName (Binding.spath root segs)) :=
            (EnvAgreeExcept.refl _ t).setEnv_right sp_mem _
          have halias := resolveS_alias (s := t.setEnv storagePathAliasName
              (Binding.spath root segs)) path.ty
            (lookupBy_setBy_self storagePathAliasName
              (Binding.spath root segs) t.env)
          show ResultsAgree aliasNames _
            (execStmt (t.setEnv storagePathAliasName (Binding.spath root segs))
              (Stmt.expr (WrappedExpr.incDec op''
                (WrappedExpr.index Kind.storage ty
                  (aliasExpr Kind.storage path.ty storagePathAliasName)
                  idxE))))
          rw [execStmt, evalValue, evalValue]
          simp only [resOk_bind]
          rw [resolveLoc, resolveLoc, hres, halias]
          simp only [resOk_bind]
          cases hidx : evalInt t idxE with
          | error err =>
              rw [evalInt_transportErr ht' hfi hidx]
              exact rfl
          | ok y =>
              obtain ⟨u, i⟩ := y
              have hu : u = t := evalInt_pure hpi hidx
              subst hu
              rw [evalInt_transportOk ht' hfi hpi hidx]
              simp only [resOk_bind]
              rw [readLoc_congr (loc := Loc.storage root
                (segs ++ [Seg.at i])) ht' trivial]
              refine ResAgree.bindState ?_ ?_
              · refine bindPureRes_agree _ fun old => ?_
                refine bindPureRes_agree _ fun oldInt => ?_
                refine bindPureRes_agree _ fun newVal => ?_
                refine ResultsAgree.bindRes (writeLoc_agree ht' newVal) ?_
                intro u₁ u₂ hu
                exact ⟨rfl, hu⟩
              · intro u₁ u₂ vv hu
                exact hu

theorem storagePushValueUnfoldLeftFstReceiver_sound
    (s : State) (target : PlaceExpr) (value : Option WrappedExpr)
    (hcond : (ruleEffect .storagePushValueUnfoldLeftFstReceiver).cond
      (Stmt.push target value))
    (hfresh : ∀ n ∈ aliasNames,
      stmtUsesVar (Stmt.push target value) n = false) :
    ResultsAgree aliasNames
      (execStmt s (Stmt.push target value))
      (execBlock s
        ((ruleEffect .storagePushValueUnfoldLeftFstReceiver).block
          (Stmt.push target value) hcond)) := by
  match value, hcond, hfresh with
  | none, hcond, _ => exact nomatch hcond.2.2
  | some rhs, hcond, hfresh =>
      have hfr : ∀ n ∈ aliasNames, usesVar rhs n = false := fun n hn => by
        have := hfresh n hn
        simp [stmtUsesVar, optUsesVar] at this
        exact this.2
      show ResultsAgree aliasNames
        (execStmt s (Stmt.push target (some rhs)))
        (execBlock s [captureStoragePath target.expr,
          Stmt.push (aliasPlace Kind.storage target.ty storagePathAliasName)
            (some rhs)])
      rw [execStmt, execBlock_pair, captureStoragePath, capture]
      cases hres : resolveS s target.expr with
      | error err =>
          have hR : execStmt s
              (Stmt.storagePlaceAlias target.expr.ty storagePathAliasName
                target.expr) = .error err := by
            rw [execStmt, hres]
            rfl
          rw [hR]
          exact rfl
      | ok x =>
          obtain ⟨t, root, segs⟩ := x
          have hR : execStmt s
              (Stmt.storagePlaceAlias target.expr.ty storagePathAliasName
                target.expr) =
              .ok (t.setEnv storagePathAliasName (Binding.spath root segs)) := by
            rw [execStmt, hres]
            rfl
          rw [hR]
          have ht' : EnvAgreeExcept aliasNames t
              (t.setEnv storagePathAliasName (Binding.spath root segs)) :=
            (EnvAgreeExcept.refl _ t).setEnv_right sp_mem _
          show ResultsAgree aliasNames _
            (execStmt (t.setEnv storagePathAliasName (Binding.spath root segs))
              (Stmt.push
                (aliasPlace Kind.storage target.ty storagePathAliasName)
                (some rhs)))
          rw [execStmt]
          have haP : (aliasPlace Kind.storage target.ty
              storagePathAliasName).expr =
              aliasExpr Kind.storage target.ty storagePathAliasName := rfl
          rw [haP,
            resolveS_alias target.ty
              (lookupBy_setBy_self storagePathAliasName
                (Binding.spath root segs) t.env)]
          simp only [resOk_bind, findStorage_congr ht']
          refine bindPureResults_agree _ fun arr => ?_
          cases arr with
      | array elems =>
          have htyP : (aliasExpr Kind.storage target.ty
              storagePathAliasName).ty = target.expr.ty := rfl
          rw [htyP]
          match hty : target.expr.ty with
          | Ty.ref (RefTy.array elemTy) =>
              simp only []
              refine ResAgree.bindState (rhsToSVal_agree ht' rhs hfr) ?_
              intro u₁ u₂ sv hu
              exact saveStorage_agree hu root segs _
          | Ty.bool => exact rfl
          | Ty.uint => exact rfl
          | Ty.int => exact rfl
          | Ty.ref (RefTy.struct nm) => exact rfl
          | Ty.ref (RefTy.mapping k v) => exact rfl
      | prim p => cases p <;> exact rfl
      | struct fields => exact rfl
      | map entries dflt => exact rfl

theorem storagePushUnfoldLeftFstReceiver_sound
    (s : State) (target : PlaceExpr) (value : Option WrappedExpr)
    (hcond : (ruleEffect .storagePushUnfoldLeftFstReceiver).cond
      (Stmt.push target value)) :
    ResultsAgree aliasNames
      (execStmt s (Stmt.push target value))
      (execBlock s
        ((ruleEffect .storagePushUnfoldLeftFstReceiver).block
          (Stmt.push target value) hcond)) := by
  have hvn : value = none := hcond.2.2
  subst hvn
  show ResultsAgree aliasNames
    (execStmt s (Stmt.push target none))
    (execBlock s [captureStoragePath target.expr,
      Stmt.push (aliasPlace Kind.storage target.ty storagePathAliasName)
        none])
  rw [execStmt, execBlock_pair, captureStoragePath, capture]
  cases hres : resolveS s target.expr with
  | error err =>
      have hR : execStmt s
          (Stmt.storagePlaceAlias target.expr.ty storagePathAliasName
            target.expr) = .error err := by
        rw [execStmt, hres]
        rfl
      rw [hR]
      exact rfl
  | ok x =>
      obtain ⟨t, root, segs⟩ := x
      have hR : execStmt s
          (Stmt.storagePlaceAlias target.expr.ty storagePathAliasName
            target.expr) =
          .ok (t.setEnv storagePathAliasName (Binding.spath root segs)) := by
        rw [execStmt, hres]
        rfl
      rw [hR]
      have ht' : EnvAgreeExcept aliasNames t
          (t.setEnv storagePathAliasName (Binding.spath root segs)) :=
        (EnvAgreeExcept.refl _ t).setEnv_right sp_mem _
      show ResultsAgree aliasNames _
        (execStmt (t.setEnv storagePathAliasName (Binding.spath root segs))
          (Stmt.push
            (aliasPlace Kind.storage target.ty storagePathAliasName) none))
      rw [execStmt]
      have haP : (aliasPlace Kind.storage target.ty
          storagePathAliasName).expr =
          aliasExpr Kind.storage target.ty storagePathAliasName := rfl
      rw [haP,
        resolveS_alias target.ty
          (lookupBy_setBy_self storagePathAliasName
            (Binding.spath root segs) t.env)]
      simp only [resOk_bind, findStorage_congr ht']
      refine bindPureResults_agree _ fun arr => ?_
      cases arr with
      | array elems =>
          have htyP : (aliasExpr Kind.storage target.ty
              storagePathAliasName).ty = target.expr.ty := rfl
          rw [htyP]
          match hty : target.expr.ty with
          | Ty.ref (RefTy.array elemTy) =>
              exact saveStorage_agree ht' root segs _
          | Ty.bool => exact rfl
          | Ty.uint => exact rfl
          | Ty.int => exact rfl
          | Ty.ref (RefTy.struct nm) => exact rfl
          | Ty.ref (RefTy.mapping k v) => exact rfl
      | prim p => cases p <;> exact rfl
      | struct fields => exact rfl
      | map entries dflt => exact rfl

theorem storagePopUnfoldLeftFstReceiver_sound
    (s : State) (target : PlaceExpr)
    (hcond : (ruleEffect .storagePopUnfoldLeftFstReceiver).cond
      (Stmt.pop target)) :
    ResultsAgree aliasNames
      (execStmt s (Stmt.pop target))
      (execBlock s
        ((ruleEffect .storagePopUnfoldLeftFstReceiver).block
          (Stmt.pop target) hcond)) := by
  show ResultsAgree aliasNames
    (execStmt s (Stmt.pop target))
    (execBlock s [captureStoragePath target.expr,
      Stmt.pop (aliasPlace Kind.storage target.ty storagePathAliasName)])
  rw [execStmt, execBlock_pair, captureStoragePath, capture]
  cases hres : resolveS s target.expr with
  | error err =>
      have hR : execStmt s
          (Stmt.storagePlaceAlias target.expr.ty storagePathAliasName
            target.expr) = .error err := by
        rw [execStmt, hres]
        rfl
      rw [hR]
      exact rfl
  | ok x =>
      obtain ⟨t, root, segs⟩ := x
      have hR : execStmt s
          (Stmt.storagePlaceAlias target.expr.ty storagePathAliasName
            target.expr) =
          .ok (t.setEnv storagePathAliasName (Binding.spath root segs)) := by
        rw [execStmt, hres]
        rfl
      rw [hR]
      have ht' : EnvAgreeExcept aliasNames t
          (t.setEnv storagePathAliasName (Binding.spath root segs)) :=
        (EnvAgreeExcept.refl _ t).setEnv_right sp_mem _
      show ResultsAgree aliasNames _
        (execStmt (t.setEnv storagePathAliasName (Binding.spath root segs))
          (Stmt.pop
            (aliasPlace Kind.storage target.ty storagePathAliasName)))
      rw [execStmt]
      have haP : (aliasPlace Kind.storage target.ty
          storagePathAliasName).expr =
          aliasExpr Kind.storage target.ty storagePathAliasName := rfl
      rw [haP,
        resolveS_alias target.ty
          (lookupBy_setBy_self storagePathAliasName
            (Binding.spath root segs) t.env)]
      simp only [resOk_bind, findStorage_congr ht']
      refine bindPureResults_agree _ fun arr => ?_
      cases arr with
      | array elems =>
          simp only []
          cases elems.reverse with
          | nil => exact rfl
          | cons hd restRev => exact saveStorage_agree ht' root segs _
      | prim p => cases p <;> exact rfl
      | struct fields => exact rfl
      | map entries dflt => exact rfl

/-! ## Storage delete unfold -/

theorem storageDeleteComplexTarget_sound
    (s : State) (target : PlaceExpr)
    (hcond : (ruleEffect .storageDeleteComplexTarget).cond
      (Stmt.delete target))
    (hfresh : ∀ n ∈ aliasNames,
      stmtUsesVar (Stmt.delete target) n = false)
    (hbase : ∀ {kind ty path index},
      target.expr = WrappedExpr.index kind ty path index ->
        path.complex = false ->
        (pureExpr index = true ∧
          ∃ root segs, resolveS s path = .ok (s, root, segs))) :
    ResultsAgree aliasNames
      (execStmt s (Stmt.delete target))
      (execBlock s
        ((ruleEffect .storageDeleteComplexTarget).block
          (Stmt.delete target) hcond)) := by
  obtain ⟨e, hass⟩ := target
  revert hbase
  match e, hass, hcond, hfresh with
  | WrappedExpr.field Kind.storage ty path fld, hass, hcond, hfresh =>
      intro _
      show ResultsAgree aliasNames
        (execStmt s (Stmt.delete (PlaceExpr.field Kind.storage ty path fld)))
        (execBlock s [captureStoragePath path,
          Stmt.delete
            (fieldFromAlias Kind.storage storagePathAliasName ty path fld)])
      have hLeq : execStmt s
          (Stmt.delete (PlaceExpr.field Kind.storage ty path fld)) =
          (resolveS s (WrappedExpr.field Kind.storage ty path fld)) >>=
            fun x => (x.1.findStorage x.2.1 x.2.2) >>= fun cur =>
              x.1.saveStorage x.2.1 x.2.2 cur.defaultOf := by
        rw [execStmt]
        rfl
      rw [hLeq, execBlock_pair, captureStoragePath, capture, resolveS]
      cases hres : resolveS s path with
      | error err =>
          have hR : execStmt s
              (Stmt.storagePlaceAlias path.ty storagePathAliasName path) =
              .error err := by
            rw [execStmt, hres]
            rfl
          rw [hR]
          exact rfl
      | ok x =>
          obtain ⟨t, root, segs⟩ := x
          have hR : execStmt s
              (Stmt.storagePlaceAlias path.ty storagePathAliasName path) =
              .ok (t.setEnv storagePathAliasName (Binding.spath root segs)) := by
            rw [execStmt, hres]
            rfl
          rw [hR]
          have ht' : EnvAgreeExcept aliasNames t
              (t.setEnv storagePathAliasName (Binding.spath root segs)) :=
            (EnvAgreeExcept.refl _ t).setEnv_right sp_mem _
          have hReq : execStmt
              (t.setEnv storagePathAliasName (Binding.spath root segs))
              (Stmt.delete (fieldFromAlias Kind.storage storagePathAliasName
                ty path fld)) =
              ((t.setEnv storagePathAliasName
                  (Binding.spath root segs)).findStorage root
                (segs ++ [Seg.field fld.name])) >>= fun cur =>
                (t.setEnv storagePathAliasName
                  (Binding.spath root segs)).saveStorage root
                  (segs ++ [Seg.field fld.name]) cur.defaultOf := by
            rw [execStmt, fieldFromAlias, placeField_expr, resolveS,
              resolveS_alias (s := t.setEnv storagePathAliasName
                  (Binding.spath root segs)) path.ty
                (lookupBy_setBy_self storagePathAliasName
                  (Binding.spath root segs) t.env)]
            rfl
          show ResultsAgree aliasNames _
            (execStmt (t.setEnv storagePathAliasName (Binding.spath root segs))
              (Stmt.delete (fieldFromAlias Kind.storage storagePathAliasName
                ty path fld)))
          rw [hReq]
          simp only [resOk_bind, findStorage_congr ht']
          refine bindPureResults_agree _ fun cur => ?_
          exact saveStorage_agree ht' root (segs ++ [Seg.field fld.name])
            cur.defaultOf
  | WrappedExpr.index Kind.storage ty path idxE, hass, hcond, hfresh =>
      intro hbase
      have hfi : ∀ n ∈ aliasNames, usesVar idxE n = false := fun n hn => by
        have := hfresh n hn
        simp [stmtUsesVar, usesVar] at this
        exact this.2
      show ResultsAgree aliasNames
        (execStmt s (Stmt.delete (PlaceExpr.index Kind.storage ty path idxE)))
        (execBlock s (storageDeleteComplexTargetBlock
          (WrappedExpr.index Kind.storage ty path idxE) hcond))
      cases hpc : path.complex with
      | true =>
          have hbl : storageDeleteComplexTargetBlock
              (WrappedExpr.index Kind.storage ty path idxE) hcond =
              [captureStoragePath path,
                Stmt.delete (indexFromAlias Kind.storage storagePathAliasName
                  ty path idxE)] := by
            rw [storageDeleteComplexTargetBlock]
            simp [hpc]
          rw [hbl, execBlock_pair, captureStoragePath, capture]
          cases hres : resolveS s path with
          | error err =>
              have hL : execStmt s
                  (Stmt.delete (PlaceExpr.index Kind.storage ty path idxE)) =
                  .error err := by
                rw [execStmt, placeIndex_expr, resolveS, hres]
                rfl
              have hR : execStmt s
                  (Stmt.storagePlaceAlias path.ty storagePathAliasName path) =
                  .error err := by
                rw [execStmt, hres]
                rfl
              rw [hL, hR]
              exact rfl
          | ok x =>
              obtain ⟨t, root, segs⟩ := x
              have hR : execStmt s
                  (Stmt.storagePlaceAlias path.ty storagePathAliasName path) =
                  .ok (t.setEnv storagePathAliasName
                    (Binding.spath root segs)) := by
                rw [execStmt, hres]
                rfl
              rw [hR]
              have ht' : EnvAgreeExcept aliasNames t
                  (t.setEnv storagePathAliasName (Binding.spath root segs)) :=
                (EnvAgreeExcept.refl _ t).setEnv_right sp_mem _
              have hLeq : execStmt s
                  (Stmt.delete (PlaceExpr.index Kind.storage ty path idxE)) =
                  ((evalInt t idxE) >>= fun y =>
                    Except.ok (y.1, root, segs ++ [Seg.at y.2])) >>= fun x =>
                    (x.1.findStorage x.2.1 x.2.2) >>= fun cur =>
                      x.1.saveStorage x.2.1 x.2.2 cur.defaultOf := by
                rw [execStmt, placeIndex_expr, resolveS, hres]
                rfl
              have hReq : execStmt
                  (t.setEnv storagePathAliasName (Binding.spath root segs))
                  (Stmt.delete (indexFromAlias Kind.storage
                    storagePathAliasName ty path idxE)) =
                  ((evalInt (t.setEnv storagePathAliasName
                      (Binding.spath root segs)) idxE) >>= fun y =>
                    Except.ok (y.1, root, segs ++ [Seg.at y.2])) >>= fun x =>
                    (x.1.findStorage x.2.1 x.2.2) >>= fun cur =>
                      x.1.saveStorage x.2.1 x.2.2 cur.defaultOf := by
                rw [execStmt, indexFromAlias, placeIndex_expr, resolveS,
                  resolveS_alias (s := t.setEnv storagePathAliasName
                      (Binding.spath root segs)) path.ty
                    (lookupBy_setBy_self storagePathAliasName
                      (Binding.spath root segs) t.env)]
                rfl
              show ResultsAgree aliasNames _
                (execStmt (t.setEnv storagePathAliasName
                    (Binding.spath root segs))
                  (Stmt.delete (indexFromAlias Kind.storage
                    storagePathAliasName ty path idxE)))
              rw [hLeq, hReq]
              refine ResAgree.bindState ?_ ?_
              · refine ResAgree.bind (evalInt_agree ht' idxE hfi) ?_
                intro u₁ u₂ i hu
                exact ⟨rfl, hu⟩
              · intro u₁ u₂ a hu
                obtain ⟨r2, s2⟩ := a
                simp only [findStorage_congr hu]
                refine bindPureResults_agree _ fun cur => ?_
                exact saveStorage_agree hu r2 s2 cur.defaultOf
      | false =>
          obtain ⟨hpi, root, segs, hb⟩ := hbase rfl hpc
          have hps : path.simple = true := by
            rcases hcond with hc | hc
            · have hcc : path.complex = true := hc
              rw [hpc] at hcc
              exact nomatch hcc
            · exact hc.1
          have hbl : storageDeleteComplexTargetBlock
              (WrappedExpr.index Kind.storage ty path idxE) hcond =
              [captureIndex idxE,
                Stmt.delete (PlaceExpr.index Kind.storage ty path
                  (indexAlias idxE))] := by
            rw [storageDeleteComplexTargetBlock]
            simp [hpc]
          rw [hbl, execBlock_pair, captureIndex, capture]
          cases hev : evalValue s idxE with
          | error err =>
              have hL : execStmt s
                  (Stmt.delete (PlaceExpr.index Kind.storage ty path idxE)) =
                  .error err := by
                rw [execStmt, placeIndex_expr, resolveS, hb]
                simp only [resOk_bind]
                rw [evalInt, hev]
                rfl
              have hR : execStmt s
                  (Stmt.stackDecl idxE.ty indexAliasName (some idxE)) =
                  .error err := by
                rw [execStmt, hev]
                rfl
              rw [hL, hR]
              exact rfl
          | ok y =>
              obtain ⟨t, v⟩ := y
              have hts : t = s := evalValue_pure hpi hev
              subst hts
              have hR : execStmt t
                  (Stmt.stackDecl idxE.ty indexAliasName (some idxE)) =
                  .ok (t.setEnv indexAliasName (Binding.val v)) := by
                rw [execStmt, hev]
                rfl
              rw [hR]
              have ht' : EnvAgreeExcept aliasNames t
                  (t.setEnv indexAliasName (Binding.val v)) :=
                (EnvAgreeExcept.refl _ t).setEnv_right idx_mem _
              have hLeq : execStmt t
                  (Stmt.delete (PlaceExpr.index Kind.storage ty path idxE)) =
                  (((v.asInt) >>= fun i => Except.ok (t, i)) >>= fun y =>
                    Except.ok (y.1, root, segs ++ [Seg.at y.2])) >>= fun x =>
                    (x.1.findStorage x.2.1 x.2.2) >>= fun cur =>
                      x.1.saveStorage x.2.1 x.2.2 cur.defaultOf := by
                rw [execStmt, placeIndex_expr, resolveS, hb]
                simp only [resOk_bind]
                rw [evalInt, hev]
                rfl
              have hReq : execStmt (t.setEnv indexAliasName (Binding.val v))
                  (Stmt.delete (PlaceExpr.index Kind.storage ty path
                    (indexAlias idxE))) =
                  (((v.asInt) >>= fun i =>
                      Except.ok (t.setEnv indexAliasName (Binding.val v),
                        i)) >>= fun y =>
                    Except.ok (y.1, root, segs ++ [Seg.at y.2])) >>= fun x =>
                    (x.1.findStorage x.2.1 x.2.2) >>= fun cur =>
                      x.1.saveStorage x.2.1 x.2.2 cur.defaultOf := by
                rw [execStmt, placeIndex_expr, resolveS,
                  resolveS_transport ht'
                    (fun n hn => by
                      have := hfresh n hn
                      simp [stmtUsesVar, usesVar] at this
                      exact this.1) (pure_of_simple hps) hb]
                simp only [resOk_bind]
                rw [evalInt, indexAlias,
                  evalValue_alias idxE.ty
                    (lookupBy_setBy_self indexAliasName (Binding.val v)
                      t.env)]
                rfl
              show ResultsAgree aliasNames _
                (execStmt (t.setEnv indexAliasName (Binding.val v))
                  (Stmt.delete (PlaceExpr.index Kind.storage ty path
                    (indexAlias idxE))))
              rw [hLeq, hReq]
              cases hi : v.asInt with
              | error err => exact rfl
              | ok i =>
                  simp only [resOk_bind, findStorage_congr ht']
                  refine bindPureResults_agree _ fun cur => ?_
                  exact saveStorage_agree ht' root (segs ++ [Seg.at i])
                    cur.defaultOf
  | WrappedExpr.pushPlace tgt, hass, hcond, hfresh =>
      intro _
      show ResultsAgree aliasNames
        (execStmt s (Stmt.delete ⟨WrappedExpr.pushPlace tgt, hass⟩))
        (execBlock s [captureStoragePath tgt,
          Stmt.delete (PlaceExpr.pushPlace
            (aliasPlace Kind.storage tgt.ty storagePathAliasName))])
      have hLeq : execStmt s (Stmt.delete ⟨WrappedExpr.pushPlace tgt, hass⟩) =
          (resolveS s (WrappedExpr.pushPlace tgt)) >>= fun x =>
            (x.1.findStorage x.2.1 x.2.2) >>= fun cur =>
              x.1.saveStorage x.2.1 x.2.2 cur.defaultOf := by
        rw [execStmt]
        rfl
      rw [hLeq, execBlock_pair, captureStoragePath, capture, resolveS]
      cases hres : resolveS s tgt with
      | error err =>
          have hR : execStmt s
              (Stmt.storagePlaceAlias tgt.ty storagePathAliasName tgt) =
              .error err := by
            rw [execStmt, hres]
            rfl
          rw [hR]
          exact rfl
      | ok x =>
          obtain ⟨t, root, segs⟩ := x
          have hR : execStmt s
              (Stmt.storagePlaceAlias tgt.ty storagePathAliasName tgt) =
              .ok (t.setEnv storagePathAliasName (Binding.spath root segs)) := by
            rw [execStmt, hres]
            rfl
          rw [hR]
          have ht' : EnvAgreeExcept aliasNames t
              (t.setEnv storagePathAliasName (Binding.spath root segs)) :=
            (EnvAgreeExcept.refl _ t).setEnv_right sp_mem _
          have hReq : execStmt
              (t.setEnv storagePathAliasName (Binding.spath root segs))
              (Stmt.delete (PlaceExpr.pushPlace
                (aliasPlace Kind.storage tgt.ty storagePathAliasName))) =
              (resolveS (t.setEnv storagePathAliasName
                  (Binding.spath root segs))
                (WrappedExpr.pushPlace
                  (aliasExpr Kind.storage tgt.ty storagePathAliasName))) >>=
                fun x => (x.1.findStorage x.2.1 x.2.2) >>= fun cur =>
                  x.1.saveStorage x.2.1 x.2.2 cur.defaultOf := by
            rw [execStmt]
            rfl
          show ResultsAgree aliasNames _
            (execStmt (t.setEnv storagePathAliasName (Binding.spath root segs))
              (Stmt.delete (PlaceExpr.pushPlace
                (aliasPlace Kind.storage tgt.ty storagePathAliasName))))
          rw [hReq, resolveS,
            resolveS_alias (s := t.setEnv storagePathAliasName
                (Binding.spath root segs)) tgt.ty
              (lookupBy_setBy_self storagePathAliasName
                (Binding.spath root segs) t.env)]
          simp only [resOk_bind, findStorage_congr ht']
          refine ResAgree.bindState ?_ ?_
          · refine bindPureRes_agree _ fun arr => ?_
            cases arr with
            | array elems =>
                have htyP : (aliasExpr Kind.storage tgt.ty
                    storagePathAliasName).ty = tgt.ty := rfl
                rw [htyP]
                match hty : tgt.ty with
                | Ty.ref (RefTy.array elemTy) =>
                    refine ResultsAgree.bindRes
                      (saveStorage_agree ht' root segs
                        (SVal.array (elems ++ [defaultForTy elemTy]))) ?_
                    intro u₁ u₂ hu
                    exact ⟨rfl, hu⟩
                | Ty.bool => exact rfl
                | Ty.uint => exact rfl
                | Ty.int => exact rfl
                | Ty.ref (RefTy.struct nm) => exact rfl
                | Ty.ref (RefTy.mapping k v) => exact rfl
            | prim p => cases p <;> exact rfl
            | struct fields => exact rfl
            | map entries dflt => exact rfl
          · intro u₁ u₂ a hu
            obtain ⟨r2, s2⟩ := a
            simp only [findStorage_congr hu]
            refine bindPureResults_agree _ fun cur => ?_
            exact saveStorage_agree hu r2 s2 cur.defaultOf

/-! ## Memory unfolds

The memory captures bind the alias with `readM`, while the interpreter
resolves memory targets with `resolveMBase`; the two agree up to the
ref-filter below (no induction needed — both share the `resolveMBase`
prefix on the sub-path). -/

theorem resBind_assoc (x : Res α) (f : α -> Res β) (g : β -> Res γ) :
    (x >>= f) >>= g = x >>= fun a => f a >>= g := by
  cases x <;> rfl

theorem resBind_congr {x : Res α} {f g : α -> Res β}
    (h : ∀ a, f a = g a) : x >>= f = x >>= g := by
  cases x with
  | error e => rfl
  | ok a => exact h a

theorem resolveMBase_eq_readM (s : State) (e : WrappedExpr) :
    resolveMBase s e = (readM s e) >>= fun x =>
      match x.2 with
      | MVal.ref id => .ok (x.1, id)
      | MVal.prim _ => .error .stuck := by
  match e with
  | .var kind ty fld =>
      rw [resolveMBase, readM, resBind_assoc]
      refine resBind_congr fun b => ?_
      cases b with
      | val v => rfl
      | spath root segs => rfl
      | mref id => rfl
  | .field kind ty base fld =>
      rw [resolveMBase, readM, resBind_assoc]
      refine resBind_congr fun x => ?_
      obtain ⟨t, baseId⟩ := x
      show (t.getObj baseId) >>= _ = ((t.getObj baseId) >>= _) >>= _
      rw [resBind_assoc]
      refine resBind_congr fun obj => ?_
      cases obj with
      | array elems => rfl
      | struct fields =>
          simp only []
          cases lookupBy fld.name fields with
          | none => rfl
          | some v => cases v <;> rfl
  | .index kind ty base index =>
      rw [resolveMBase, readM, resBind_assoc]
      refine resBind_congr fun x => ?_
      obtain ⟨t, baseId⟩ := x
      show (evalInt t index) >>= _ = ((evalInt t index) >>= _) >>= _
      rw [resBind_assoc]
      refine resBind_congr fun y => ?_
      obtain ⟨u, i⟩ := y
      show (u.getObj baseId) >>= _ = ((u.getObj baseId) >>= _) >>= _
      rw [resBind_assoc]
      refine resBind_congr fun obj => ?_
      cases obj with
      | struct fields => rfl
      | array elems =>
          simp only []
          by_cases hb : 0 ≤ i ∧ i.toNat < elems.length
          · simp only [dif_pos hb]
            cases elems.get ⟨i.toNat, hb.2⟩ <;> rfl
          · simp only [dif_neg hb]
            rfl
  | .bool b => rw [resolveMBase.eq_def, readM.eq_def]; rfl
  | .intLit ty v => rw [resolveMBase.eq_def, readM.eq_def]; rfl
  | .pushPlace target => rw [resolveMBase.eq_def, readM.eq_def]; rfl
  | .mkCall kind ty nm args => rw [resolveMBase.eq_def, readM.eq_def]; rfl
  | .mkBinop op l r => rw [resolveMBase.eq_def, readM.eq_def]; rfl
  | .mkUnop op arg => rw [resolveMBase.eq_def, readM.eq_def]; rfl
  | .mkIncDec op target => rw [resolveMBase.eq_def, readM.eq_def]; rfl
  | .mkTernary c t el => rw [resolveMBase.eq_def, readM.eq_def]; rfl

/-- Template: the memory field-write unfold (`fieldWriteResolveBlock` at
`Kind.memory`) on a **primitive** value operand — the memory twin of
`fieldWriteResolveStorage_sound`.

`Rules.freezeRhs` binds the value into `rv` before the path capture runs, so
the two sides agree with nothing assumed about interference: the old
`hev`/`hstable` hypotheses are gone, and so is purity of the right-hand side.
All that is left is that the path does not mention the reserved alias names.

The frozen binding survives the path capture by `readM_keep`; that is the fact
the old side conditions were standing in for. -/
theorem fieldWriteResolveMemory_sound (s : State) (ty : Ty)
    (path : WrappedExpr) (fld : Field) (rhs : WrappedExpr)
    (hprim : rhs.ty.isPrimitive = true)
    (hkpm : path.kind = Kind.memory)
    (hfp : ∀ n ∈ aliasNames, usesVar path n = false) :
    ResultsAgree aliasNames
      (execStmt s (Stmt.assign (PlaceExpr.field Kind.memory ty path fld) rhs))
      (execBlock s (fieldWriteResolveBlock Kind.memory memoryPathAliasName
        ty path fld rhs)) := by
  show ResultsAgree aliasNames
    (execStmt s (Stmt.assign (PlaceExpr.field Kind.memory ty path fld) rhs))
    (execBlock s (freezeRhs rhs fun v =>
      [captureMemoryPath path,
        Stmt.assign
          (fieldFromAlias Kind.memory memoryPathAliasName ty path fld) v]))
  rw [freezeRhs, if_pos hprim, execStmt, execBlock_triple, captureRhsValue,
    capture, execStmt]
  cases hevR : evalValue s rhs with
  | error err =>
      have hL : execAssign s (PlaceExpr.field Kind.memory ty path fld) rhs =
          .error err := by
        show execAssignNested s
          (WrappedExpr.field Kind.memory ty path fld) rhs = .error err
        rw [execAssignNested, rhsToMVal, hprim]
        simp only [if_pos, hevR]
        rfl
      rw [hL]
      rfl
  | ok x =>
      obtain ⟨s₁, v⟩ := x
      simp only [hevR, resOk_bind]
      have hrv₁ : lookupBy rhsValueAliasName
          (s₁.setEnv rhsValueAliasName (Binding.val v)).env =
            some (Binding.val v) := lookupBy_setBy_self ..
      have hagree₁ : EnvAgreeExcept aliasNames s₁
          (s₁.setEnv rhsValueAliasName (Binding.val v)) :=
        (EnvAgreeExcept.refl _ s₁).setEnv_right rv_mem _
      have hL : execAssign s (PlaceExpr.field Kind.memory ty path fld) rhs =
          (readM s₁ path) >>= fun y =>
            match y.2 with
            | MVal.ref id =>
                writeMSlot y.1 (Loc.memoryField id fld.name) v.toMVal
            | _ => .error .stuck := by
        show execAssignNested s
          (WrappedExpr.field Kind.memory ty path fld) rhs = _
        rw [execAssignNested, rhsToMVal, hprim]
        simp only [if_pos, hevR, resOk_bind, Typed.WrappedExpr.kind]
        rw [resolveLoc, resolveMBase_eq_readM]
        cases readM s₁ path with
        | error e => rfl
        | ok y =>
            obtain ⟨t, mv⟩ := y
            cases mv with
            | prim p => cases p <;> rfl
            | ref id => rfl
      have hR : execBlock (s₁.setEnv rhsValueAliasName (Binding.val v))
          [captureMemoryPath path,
            Stmt.assign
              (fieldFromAlias Kind.memory memoryPathAliasName ty path fld)
              (rhsValueAlias rhs)] =
          (readM (s₁.setEnv rhsValueAliasName (Binding.val v)) path) >>=
            fun y =>
              match y.2 with
              | MVal.ref id =>
                  execStmt (y.1.setEnv memoryPathAliasName (Binding.mref id))
                    (Stmt.assign
                      (fieldFromAlias Kind.memory memoryPathAliasName ty path
                        fld)
                      (rhsValueAlias rhs))
              | _ => .error .stuck := by
        have hRdecl : ∀ w : State, execStmt w
            (Stmt.memoryDecl path.ty memoryPathAliasName (some path)) =
            (readM w path) >>= fun y =>
              match y.2 with
              | MVal.ref id =>
                  .ok (y.1.setEnv memoryPathAliasName (Binding.mref id))
              | MVal.prim _ => .error .stuck := by
          intro w
          rw [execStmt]
          rw [hkpm]
          rfl
        rw [execBlock_pair, captureMemoryPath, capture, hRdecl]
        cases readM (s₁.setEnv rhsValueAliasName (Binding.val v)) path with
        | error e => rfl
        | ok y =>
            obtain ⟨t, mv⟩ := y
            cases mv with
            | prim p => cases p <;> rfl
            | ref id => rfl
      rw [hL, hR]
      refine ResAgree.bindStateWith (readM_agree hagree₁ path hfp) ?_
      intro t₁ t₂ mv _ hres₂ hagree₂
      cases mv with
      | prim p => cases p <;> exact rfl
      | ref id =>
          show ResultsAgree aliasNames
            (writeMSlot t₁ (Loc.memoryField id fld.name) v.toMVal)
            (execStmt (t₂.setEnv memoryPathAliasName (Binding.mref id))
              (Stmt.assign
                (fieldFromAlias Kind.memory memoryPathAliasName ty path fld)
                (rhsValueAlias rhs)))
          have hrv₃ : lookupBy rhsValueAliasName
              (t₂.setEnv memoryPathAliasName (Binding.mref id)).env =
                some (Binding.val v) := by
            rw [State.setEnv, lookupBy_setBy_ne (Ne.symm mp_ne_rv)]
            rw [readM_keep (s₁.setEnv rhsValueAliasName (Binding.val v)) path
              hfp t₂ (MVal.ref id) hres₂ _ rv_mem]
            exact hrv₁
          have hmp₃ : lookupBy memoryPathAliasName
              (t₂.setEnv memoryPathAliasName (Binding.mref id)).env =
                some (Binding.mref id) := lookupBy_setBy_self ..
          have hevAlias : rhsToMVal
              (t₂.setEnv memoryPathAliasName (Binding.mref id))
              (rhsValueAlias rhs) =
              .ok (t₂.setEnv memoryPathAliasName (Binding.mref id), v.toMVal) :=
            rhsToMVal_stackAlias hprim hrv₃
          have hRA : execStmt
              (t₂.setEnv memoryPathAliasName (Binding.mref id))
              (Stmt.assign
                (fieldFromAlias Kind.memory memoryPathAliasName ty path fld)
                (rhsValueAlias rhs)) =
              writeMSlot (t₂.setEnv memoryPathAliasName (Binding.mref id))
                (Loc.memoryField id fld.name) v.toMVal := by
            rw [execStmt]
            show execAssignNested
              (t₂.setEnv memoryPathAliasName (Binding.mref id))
              (WrappedExpr.field Kind.memory ty
                (aliasExpr Kind.memory path.ty memoryPathAliasName) fld)
              (rhsValueAlias rhs) = _
            rw [execAssignNested, hevAlias]
            simp only [Typed.WrappedExpr.kind, resOk_bind]
            rw [resolveLoc, resolveMBase_alias path.ty hmp₃]
            simp only [resOk_bind]
            rfl
          rw [hRA]
          exact writeMSlot_agree (hagree₂.setEnv_right mp_mem _) _ v.toMVal
/-- Tail of the memory index-write unfold with a **captured** complex index,
the memory twin of `indexWriteTailCapture_agree`. -/
theorem indexWriteTailCaptureMemory_agree {ty : Ty}
    {path index rhs : WrappedExpr} {s₂ t₂ : State} {v : Value} {id : Nat}
    (hprim : rhs.ty.isPrimitive = true)
    (hfi : ∀ n ∈ aliasNames, usesVar index n = false)
    (hrv₂ : lookupBy rhsValueAliasName t₂.env = some (Binding.val v))
    (hagree₂ : EnvAgreeExcept aliasNames s₂ t₂) :
    ResultsAgree aliasNames
      ((evalInt s₂ index) >>= fun y =>
        match y with
        | (s₃, i) => writeMSlot s₃ (Loc.memoryIndex id i) v.toMVal)
      (execBlock (t₂.setEnv memoryPathAliasName (Binding.mref id))
        [captureIndex index,
          Stmt.assign
            (indexFromAlias Kind.memory memoryPathAliasName ty path
              (indexAlias index))
            (rhsValueAlias rhs)]) := by
  have hrv₃ : lookupBy rhsValueAliasName
      (t₂.setEnv memoryPathAliasName (Binding.mref id)).env =
        some (Binding.val v) := by
    rw [State.setEnv, lookupBy_setBy_ne (Ne.symm mp_ne_rv)]
    exact hrv₂
  have hmp₃ : lookupBy memoryPathAliasName
      (t₂.setEnv memoryPathAliasName (Binding.mref id)).env =
        some (Binding.mref id) := lookupBy_setBy_self ..
  have hagree₃ : EnvAgreeExcept aliasNames s₂
      (t₂.setEnv memoryPathAliasName (Binding.mref id)) :=
    hagree₂.setEnv_right mp_mem _
  have hLn : ((evalInt s₂ index) >>= fun y =>
        match y with
        | (s₃, i) => writeMSlot s₃ (Loc.memoryIndex id i) v.toMVal) =
      (evalValue s₂ index) >>= fun y =>
        match y with
        | (s₃, w) => w.asInt >>= fun i =>
            writeMSlot s₃ (Loc.memoryIndex id i) v.toMVal := by
    rw [evalInt]
    cases evalValue s₂ index with
    | error e => rfl
    | ok z =>
        obtain ⟨s₃, w⟩ := z
        simp only [resOk_bind]
        cases w.asInt with
        | error e => rfl
        | ok i => rfl
  have hRn : execBlock (t₂.setEnv memoryPathAliasName (Binding.mref id))
        [captureIndex index,
          Stmt.assign
            (indexFromAlias Kind.memory memoryPathAliasName ty path
              (indexAlias index))
            (rhsValueAlias rhs)] =
      (evalValue (t₂.setEnv memoryPathAliasName (Binding.mref id))
        index) >>= fun y =>
        match y with
        | (t₄, w) =>
            execStmt (t₄.setEnv indexAliasName (Binding.val w))
              (Stmt.assign
                (indexFromAlias Kind.memory memoryPathAliasName ty path
                  (indexAlias index))
                (rhsValueAlias rhs)) := by
    rw [execBlock_pair, captureIndex, capture, execStmt]
    cases evalValue (t₂.setEnv memoryPathAliasName (Binding.mref id))
        index with
    | error e => rfl
    | ok z => obtain ⟨t₄, w⟩ := z; rfl
  rw [hLn, hRn]
  refine ResAgree.bindStateWith (evalValue_agree hagree₃ index hfi) ?_
  intro s₃ t₄ w _ hev₄ hagree₄
  have hkeep := evalValue_keep
    (t₂.setEnv memoryPathAliasName (Binding.mref id)) index hfi t₄ w hev₄
  have hrv₅ : lookupBy rhsValueAliasName
      (t₄.setEnv indexAliasName (Binding.val w)).env =
        some (Binding.val v) := by
    rw [State.setEnv, lookupBy_setBy_ne (Ne.symm idx_ne_rv),
      hkeep rhsValueAliasName rv_mem]
    exact hrv₃
  have hmp₅ : lookupBy memoryPathAliasName
      (t₄.setEnv indexAliasName (Binding.val w)).env =
        some (Binding.mref id) := by
    rw [State.setEnv, lookupBy_setBy_ne (Ne.symm idx_ne_mp),
      hkeep memoryPathAliasName mp_mem]
    exact hmp₃
  have hidx₅ : lookupBy indexAliasName
      (t₄.setEnv indexAliasName (Binding.val w)).env = some (Binding.val w) :=
    lookupBy_setBy_self ..
  have hevAlias : rhsToMVal (t₄.setEnv indexAliasName (Binding.val w))
      (rhsValueAlias rhs) =
      .ok (t₄.setEnv indexAliasName (Binding.val w), v.toMVal) :=
    rhsToMVal_stackAlias hprim hrv₅
  have hR : execStmt (t₄.setEnv indexAliasName (Binding.val w))
      (Stmt.assign
        (indexFromAlias Kind.memory memoryPathAliasName ty path
          (indexAlias index))
        (rhsValueAlias rhs)) =
      w.asInt >>= fun i =>
        writeMSlot (t₄.setEnv indexAliasName (Binding.val w))
          (Loc.memoryIndex id i) v.toMVal := by
    rw [execStmt]
    show execAssignNested (t₄.setEnv indexAliasName (Binding.val w))
      (WrappedExpr.index Kind.memory ty
        (aliasExpr Kind.memory path.ty memoryPathAliasName)
        (indexAlias index))
      (rhsValueAlias rhs) = _
    rw [execAssignNested, hevAlias]
    simp only [Typed.WrappedExpr.kind, resOk_bind]
    rw [resolveLoc, resolveMBase_alias path.ty hmp₅]
    simp only [resOk_bind]
    rw [evalInt, indexAlias, evalValue_alias index.ty hidx₅]
    simp only [resOk_bind]
    cases w.asInt with
    | error e => rfl
    | ok i => rfl
  simp only []
  rw [hR]
  refine bindPureResults_agree _ fun i => ?_
  exact writeMSlot_agree (hagree₄.setEnv_right idx_mem _) _ v.toMVal

/-- Tail of the memory index-write unfold with a simple index left in place,
the memory twin of `indexWriteTailPlain_agree`. -/
theorem indexWriteTailPlainMemory_agree {ty : Ty}
    {path index rhs : WrappedExpr} {s₂ t₂ : State} {v : Value} {id : Nat}
    (hprim : rhs.ty.isPrimitive = true)
    (hfi : ∀ n ∈ aliasNames, usesVar index n = false)
    (hrv₂ : lookupBy rhsValueAliasName t₂.env = some (Binding.val v))
    (hagree₂ : EnvAgreeExcept aliasNames s₂ t₂) :
    ResultsAgree aliasNames
      ((evalInt s₂ index) >>= fun y =>
        match y with
        | (s₃, i) => writeMSlot s₃ (Loc.memoryIndex id i) v.toMVal)
      (execBlock (t₂.setEnv memoryPathAliasName (Binding.mref id))
        [Stmt.assign
          (indexFromAlias Kind.memory memoryPathAliasName ty path index)
          (rhsValueAlias rhs)]) := by
  have hrv₃ : lookupBy rhsValueAliasName
      (t₂.setEnv memoryPathAliasName (Binding.mref id)).env =
        some (Binding.val v) := by
    rw [State.setEnv, lookupBy_setBy_ne (Ne.symm mp_ne_rv)]
    exact hrv₂
  have hmp₃ : lookupBy memoryPathAliasName
      (t₂.setEnv memoryPathAliasName (Binding.mref id)).env =
        some (Binding.mref id) := lookupBy_setBy_self ..
  have hagree₃ : EnvAgreeExcept aliasNames s₂
      (t₂.setEnv memoryPathAliasName (Binding.mref id)) :=
    hagree₂.setEnv_right mp_mem _
  have hevAlias : rhsToMVal (t₂.setEnv memoryPathAliasName (Binding.mref id))
      (rhsValueAlias rhs) =
      .ok (t₂.setEnv memoryPathAliasName (Binding.mref id), v.toMVal) :=
    rhsToMVal_stackAlias hprim hrv₃
  have hR : execBlock (t₂.setEnv memoryPathAliasName (Binding.mref id))
      [Stmt.assign
        (indexFromAlias Kind.memory memoryPathAliasName ty path index)
        (rhsValueAlias rhs)] =
      (evalInt (t₂.setEnv memoryPathAliasName (Binding.mref id))
        index) >>= fun y =>
        match y with
        | (t₃, i) => writeMSlot t₃ (Loc.memoryIndex id i) v.toMVal := by
    rw [execBlock_single, execStmt]
    show execAssignNested
      (t₂.setEnv memoryPathAliasName (Binding.mref id))
      (WrappedExpr.index Kind.memory ty
        (aliasExpr Kind.memory path.ty memoryPathAliasName) index)
      (rhsValueAlias rhs) = _
    rw [execAssignNested, hevAlias]
    simp only [Typed.WrappedExpr.kind, resOk_bind]
    rw [resolveLoc, resolveMBase_alias path.ty hmp₃]
    simp only [resOk_bind]
    cases evalInt (t₂.setEnv memoryPathAliasName (Binding.mref id))
        index with
    | error e => rfl
    | ok z => obtain ⟨t₃, i⟩ := z; rfl
  rw [hR]
  refine ResAgree.bindStateWith (evalInt_agree hagree₃ index hfi) ?_
  intro s₃ t₃ i _ _ hagree₄
  exact writeMSlot_agree hagree₄ _ v.toMVal

/-- Template: the memory index-write unfold (`indexWriteResolveBlock` at
`Kind.memory`) on a **primitive** value operand — and, since
`captureIndexTargetBlock` is this function, the left-snd unfold too.

The memory twin of `indexWriteResolveStorage_sound`: the residual runs value,
path, index, write, exactly the order `execAssignNested` + `resolveLoc` run
them in, so no `hev`, no `hstable`, and no `pureExpr index`.  The frozen value
and the captured path survive the index evaluation by `evalValue_keep`, and the
path capture by `readM_keep`. -/
theorem indexWriteResolveMemory_sound (s : State) (ty : Ty)
    (path index rhs : WrappedExpr)
    (hprim : rhs.ty.isPrimitive = true)
    (hkpm : path.kind = Kind.memory)
    (hfp : ∀ n ∈ aliasNames, usesVar path n = false)
    (hfi : ∀ n ∈ aliasNames, usesVar index n = false) :
    ResultsAgree aliasNames
      (execStmt s (Stmt.assign (PlaceExpr.index Kind.memory ty path index) rhs))
      (execBlock s (indexWriteResolveBlock Kind.memory memoryPathAliasName
        ty path index rhs)) := by
  show ResultsAgree aliasNames
    (execStmt s (Stmt.assign (PlaceExpr.index Kind.memory ty path index) rhs))
    (execBlock s (freezeRhs rhs fun v =>
      if index.complex then
        [captureMemoryPath path, captureIndex index,
          Stmt.assign
            (indexFromAlias Kind.memory memoryPathAliasName ty path
              (indexAlias index)) v]
      else
        [captureMemoryPath path,
          Stmt.assign
            (indexFromAlias Kind.memory memoryPathAliasName ty path index) v]))
  rw [freezeRhs, if_pos hprim, execStmt]
  cases hevR : evalValue s rhs with
  | error err =>
      have hL : execAssign s (PlaceExpr.index Kind.memory ty path index) rhs =
          .error err := by
        show execAssignNested s
          (WrappedExpr.index Kind.memory ty path index) rhs = .error err
        rw [execAssignNested, rhsToMVal, hprim]
        simp only [if_pos, hevR]
        rfl
      have hR : ∀ b : Block,
          execBlock s (captureRhsValue rhs :: b) = .error err := by
        intro b
        rw [execBlock.eq_def, captureRhsValue, capture]
        simp only [execStmt, hevR]
        rfl
      by_cases hc : index.complex
      · rw [if_pos hc, hL, hR]; rfl
      · rw [if_neg hc, hL, hR]; rfl
  | ok x =>
      obtain ⟨s₁, v⟩ := x
      have hrv₁ : lookupBy rhsValueAliasName
          (s₁.setEnv rhsValueAliasName (Binding.val v)).env =
            some (Binding.val v) := lookupBy_setBy_self ..
      have hagree₁ : EnvAgreeExcept aliasNames s₁
          (s₁.setEnv rhsValueAliasName (Binding.val v)) :=
        (EnvAgreeExcept.refl _ s₁).setEnv_right rv_mem _
      have hL : execAssign s (PlaceExpr.index Kind.memory ty path index) rhs =
          (readM s₁ path) >>= fun y =>
            match y.2 with
            | MVal.ref id =>
                (evalInt y.1 index) >>= fun z =>
                  match z with
                  | (s₃, i) => writeMSlot s₃ (Loc.memoryIndex id i) v.toMVal
            | _ => .error .stuck := by
        show execAssignNested s
          (WrappedExpr.index Kind.memory ty path index) rhs = _
        rw [execAssignNested, rhsToMVal, hprim]
        simp only [if_pos, hevR, resOk_bind, Typed.WrappedExpr.kind]
        rw [resolveLoc, resolveMBase_eq_readM]
        cases readM s₁ path with
        | error e => rfl
        | ok y =>
            obtain ⟨t, mv⟩ := y
            cases mv with
            | prim p => cases p <;> rfl
            | ref id =>
                simp only [resOk_bind]
                cases evalInt t index with
                | error e => rfl
                | ok z => obtain ⟨s₃, i⟩ := z; rfl
      have hRpre : ∀ tail : Block,
          execBlock s (captureRhsValue rhs :: captureMemoryPath path :: tail) =
            (readM (s₁.setEnv rhsValueAliasName (Binding.val v)) path) >>=
              fun y =>
                match y.2 with
                | MVal.ref id =>
                    execBlock (y.1.setEnv memoryPathAliasName
                      (Binding.mref id)) tail
                | MVal.prim _ => .error .stuck := by
        intro tail
        rw [execBlock.eq_def, captureRhsValue, capture]
        simp only [execStmt, hevR, resOk_bind]
        rw [execBlock.eq_def, captureMemoryPath, capture]
        simp only [execStmt, hkpm]
        cases readM (s₁.setEnv rhsValueAliasName (Binding.val v)) path with
        | error e => rfl
        | ok y =>
            obtain ⟨t, mv⟩ := y
            cases mv with
            | prim p => cases p <;> rfl
            | ref id => rfl
      rw [hL]
      by_cases hc : index.complex
      · rw [if_pos hc, hRpre]
        refine ResAgree.bindStateWith (readM_agree hagree₁ path hfp) ?_
        intro t₁ t₂ mv _ hres₂ hagree₂
        cases mv with
        | prim p => cases p <;> exact rfl
        | ref id =>
            show ResultsAgree aliasNames
              ((evalInt t₁ index) >>= fun z =>
                match z with
                | (s₃, i) => writeMSlot s₃ (Loc.memoryIndex id i) v.toMVal)
              (execBlock (t₂.setEnv memoryPathAliasName (Binding.mref id))
                [captureIndex index,
                  Stmt.assign
                    (indexFromAlias Kind.memory memoryPathAliasName ty path
                      (indexAlias index))
                    (rhsValueAlias rhs)])
            refine indexWriteTailCaptureMemory_agree hprim hfi ?_ hagree₂
            rw [readM_keep (s₁.setEnv rhsValueAliasName (Binding.val v)) path
              hfp t₂ (MVal.ref id) hres₂ _ rv_mem]
            exact hrv₁
      · rw [if_neg hc, hRpre]
        refine ResAgree.bindStateWith (readM_agree hagree₁ path hfp) ?_
        intro t₁ t₂ mv _ hres₂ hagree₂
        cases mv with
        | prim p => cases p <;> exact rfl
        | ref id =>
            show ResultsAgree aliasNames
              ((evalInt t₁ index) >>= fun z =>
                match z with
                | (s₃, i) => writeMSlot s₃ (Loc.memoryIndex id i) v.toMVal)
              (execBlock (t₂.setEnv memoryPathAliasName (Binding.mref id))
                [Stmt.assign
                  (indexFromAlias Kind.memory memoryPathAliasName ty path index)
                  (rhsValueAlias rhs)])
            refine indexWriteTailPlainMemory_agree hprim hfi ?_ hagree₂
            rw [readM_keep (s₁.setEnv rhsValueAliasName (Binding.val v)) path
              hfp t₂ (MVal.ref id) hres₂ _ rv_mem]
            exact hrv₁
/-- `memoryFieldWriteUnfoldLeftFst` on a **primitive** value operand.

Dispatches to `fieldWriteResolveMemory_sound`.  The reference-typed case is not
covered: `Stmt.memoryDecl` from a memory source aliases rather than copying,
while `rhsToMVal` reads the reference out, so no residual can snapshot it — the
combination is excluded by the rule's condition, not by a hypothesis here. -/
theorem memoryFieldWriteUnfoldLeftFst_sound
    (s : State) (lhs : PlaceExpr) (rhs : WrappedExpr)
    (hcond : (ruleEffect .memoryFieldWriteUnfoldLeftFst).cond
      (Stmt.assign lhs rhs))
    (hprim : rhs.ty.isPrimitive = true)
    (hfresh : ∀ n ∈ aliasNames,
      stmtUsesVar (Stmt.assign lhs rhs) n = false)
    (hkp : ∀ {kind ty path fld},
      lhs.expr = WrappedExpr.field kind ty path fld ->
        path.kind = Kind.memory) :
    ResultsAgree aliasNames
      (execStmt s (Stmt.assign lhs rhs))
      (execBlock s
        ((ruleEffect .memoryFieldWriteUnfoldLeftFst).block
          (Stmt.assign lhs rhs) hcond)) := by
  obtain ⟨e, hass⟩ := lhs
  revert hkp
  match e, hass, hcond, hfresh with
  | WrappedExpr.field Kind.memory ty path fld, hass, hcond, hfresh =>
      intro hkp
      refine fieldWriteResolveMemory_sound s ty path fld rhs hprim (hkp rfl) ?_
      intro n hn
      have := hfresh n hn
      simp [stmtUsesVar, placeField_expr, usesVar] at this
      exact this.1

/-- `memoryIndexWriteUnfoldLeftFst` on a **primitive** value operand.

Dispatches to `indexWriteResolveMemory_sound`.  `hkp` is the AST
well-formedness fact that a memory index node has a memory-kinded base — not a
non-interference assumption; the reference-typed value case is excluded by the
rule's condition, not by a hypothesis here. -/
theorem memoryIndexWriteUnfoldLeftFst_sound
    (s : State) (lhs : PlaceExpr) (rhs : WrappedExpr)
    (hcond : (ruleEffect .memoryIndexWriteUnfoldLeftFst).cond
      (Stmt.assign lhs rhs))
    (hprim : rhs.ty.isPrimitive = true)
    (hfresh : ∀ n ∈ aliasNames,
      stmtUsesVar (Stmt.assign lhs rhs) n = false)
    (hkp : ∀ {kind ty path index},
      lhs.expr = WrappedExpr.index kind ty path index ->
        path.kind = Kind.memory) :
    ResultsAgree aliasNames
      (execStmt s (Stmt.assign lhs rhs))
      (execBlock s
        ((ruleEffect .memoryIndexWriteUnfoldLeftFst).block
          (Stmt.assign lhs rhs) hcond)) := by
  obtain ⟨e, hass⟩ := lhs
  revert hkp
  match e, hass, hcond, hfresh with
  | WrappedExpr.index Kind.memory ty path idxE, hass, hcond, hfresh =>
      intro hkp
      refine indexWriteResolveMemory_sound s ty path idxE rhs hprim (hkp rfl)
        ?_ ?_ <;>
        intro n hn <;> have := hfresh n hn <;>
        simp [stmtUsesVar, placeIndex_expr, usesVar] at this
      · exact this.1.1
      · exact this.1.2

theorem memoryFieldReadUnfoldRightFst_sound
    (s : State) (lhs : PlaceExpr) (rhs : WrappedExpr) {loc : Loc}
    (hcond : (ruleEffect .memoryFieldReadUnfoldRightFst).cond
      (Stmt.assign lhs rhs))
    (hfresh : ∀ n ∈ aliasNames,
      stmtUsesVar (Stmt.assign lhs rhs) n = false)
    (hlhs : resolveLoc s lhs.expr = .ok (s, loc))
    (hplhs : pureExpr lhs.expr = true)
    (hnsl : ∀ nm, loc ≠ Loc.storageLocal nm)
    (hkp : ∀ {kind ty path fld},
      rhs = WrappedExpr.field kind ty path fld -> path.kind = Kind.memory)
    (hppath : ∀ {kind ty path fld},
      rhs = WrappedExpr.field kind ty path fld -> pureExpr path = true) :
    ResultsAgree aliasNames
      (execStmt s (Stmt.assign lhs rhs))
      (execBlock s
        ((ruleEffect .memoryFieldReadUnfoldRightFst).block
          (Stmt.assign lhs rhs) hcond)) := by
  revert hkp hppath
  match rhs, hcond, hfresh with
  | WrappedExpr.field Kind.memory tyR path fldR, hcond, hfresh =>
      intro hkp hppath
      have hkpm : path.kind = Kind.memory := hkp rfl
      have hpp : pureExpr path = true := hppath rfl
      have hfl : ∀ n ∈ aliasNames, usesVar lhs.expr n = false := fun n hn => by
        have := hfresh n hn
        simp [stmtUsesVar] at this
        exact this.1
      show ResultsAgree aliasNames
        (execStmt s (Stmt.assign lhs
          (WrappedExpr.field Kind.memory tyR path fldR)))
        (execBlock s [Stmt.memoryDecl path.ty memoryPathAliasName (some path),
          Stmt.assign lhs (WrappedExpr.field Kind.memory tyR
            (aliasExpr Kind.memory path.ty memoryPathAliasName) fldR)])
      rw [execStmt, execBlock_pair]
      have hRdecl : execStmt s
          (Stmt.memoryDecl path.ty memoryPathAliasName (some path)) =
          (readM s path) >>= fun x =>
            match x.2 with
            | MVal.ref id =>
                .ok (x.1.setEnv memoryPathAliasName (Binding.mref id))
            | MVal.prim _ => .error .stuck := by
        rw [execStmt]
        rw [hkpm]
        rfl
      have hLerr : ∀ (err : Halt), readM s path = .error err ->
          execAssign s lhs (WrappedExpr.field Kind.memory tyR path fldR) =
            .error err := by
        intro err hcap
        have hcap' : readM s (WrappedExpr.field Kind.memory tyR path fldR) =
            .error err := by
          rw [readM, resolveMBase_eq_readM, hcap]
          rfl
        exact execAssign_memoryRhsErr hlhs rfl hnsl
          (fun u => by rw [evalValue]) hcap'
      cases hcap : readM s path with
      | error err =>
          rw [hLerr err hcap, hRdecl, hcap]
          exact rfl
      | ok x =>
          obtain ⟨t, mv⟩ := x
          have hts : t = s := readM_pure hpp hcap
          subst hts
          cases mv with
          | prim p =>
              cases p
              all_goals {
                have hL : execAssign t lhs
                    (WrappedExpr.field Kind.memory tyR path fldR) =
                    .error .stuck := by
                  have hcap' : readM t
                      (WrappedExpr.field Kind.memory tyR path fldR) =
                      .error .stuck := by
                    rw [readM, resolveMBase_eq_readM, hcap]
                    rfl
                  exact execAssign_memoryRhsErr hlhs rfl hnsl
                    (fun u => by rw [evalValue]) hcap'
                rw [hL, hRdecl, hcap]
                exact rfl
              }
          | ref id =>
              rw [hRdecl, hcap]
              have ht' : EnvAgreeExcept aliasNames t
                  (t.setEnv memoryPathAliasName (Binding.mref id)) :=
                (EnvAgreeExcept.refl _ t).setEnv_right mp_mem _
              have hreadL : readM t
                  (WrappedExpr.field Kind.memory tyR path fldR) =
                  (t.getObj id) >>= fun obj =>
                    match obj with
                    | MObj.struct fields =>
                        match lookupBy fldR.name fields with
                        | some v => Except.ok (t, v)
                        | none => Except.error Halt.stuck
                    | MObj.array _ => Except.error Halt.stuck := by
                rw [readM, resolveMBase_eq_readM, hcap]
                rfl
              have hreadR : readM
                  (t.setEnv memoryPathAliasName (Binding.mref id))
                  (WrappedExpr.field Kind.memory tyR
                    (aliasExpr Kind.memory path.ty memoryPathAliasName)
                    fldR) =
                  ((t.setEnv memoryPathAliasName
                      (Binding.mref id)).getObj id) >>= fun obj =>
                    match obj with
                    | MObj.struct fields =>
                        match lookupBy fldR.name fields with
                        | some v =>
                            Except.ok (t.setEnv memoryPathAliasName
                              (Binding.mref id), v)
                        | none => Except.error Halt.stuck
                    | MObj.array _ => Except.error Halt.stuck := by
                rw [readM,
                  resolveMBase_alias (s := t.setEnv memoryPathAliasName
                      (Binding.mref id)) path.ty
                    (lookupBy_setBy_self memoryPathAliasName
                      (Binding.mref id) t.env)]
                rfl
              have hreadSim : ResAgree aliasNames
                  (readM t (WrappedExpr.field Kind.memory tyR path fldR))
                  (readM (t.setEnv memoryPathAliasName (Binding.mref id))
                    (WrappedExpr.field Kind.memory tyR
                      (aliasExpr Kind.memory path.ty memoryPathAliasName)
                      fldR)) := by
                rw [hreadL, hreadR, getObj_congr ht']
                refine bindPureRes_agree _ fun obj => ?_
                cases obj with
                | array elems => exact rfl
                | struct fields =>
                    simp only []
                    cases lookupBy fldR.name fields with
                    | none => exact rfl
                    | some v => exact ⟨rfl, ht'⟩
              show ResultsAgree aliasNames
                (execAssign t lhs
                  (WrappedExpr.field Kind.memory tyR path fldR))
                (execStmt (t.setEnv memoryPathAliasName (Binding.mref id))
                  (Stmt.assign lhs (WrappedExpr.field Kind.memory tyR
                    (aliasExpr Kind.memory path.ty memoryPathAliasName)
                    fldR)))
              rw [execStmt]
              refine execAssign_pureLocSim hlhs hfl rfl rfl ?_ ?_ ?_
              · rw [evalValue, evalValue]
                refine ResAgree.bind hreadSim ?_
                intro u₁ u₂ v hu
                exact bindPureRes_agree _ fun val => ⟨rfl, hu⟩
              · intro h
                rcases h with hk | ⟨nm, hl⟩
                · exact nomatch hk
                · exact absurd hl (hnsl nm)
              · intro _
                exact hreadSim

theorem memoryIndexReadUnfoldRightFst_sound
    (s : State) (lhs : PlaceExpr) (rhs : WrappedExpr) {loc : Loc}
    (hcond : (ruleEffect .memoryIndexReadUnfoldRightFst).cond
      (Stmt.assign lhs rhs))
    (hfresh : ∀ n ∈ aliasNames,
      stmtUsesVar (Stmt.assign lhs rhs) n = false)
    (hlhs : resolveLoc s lhs.expr = .ok (s, loc))
    (hplhs : pureExpr lhs.expr = true)
    (hnsl : ∀ nm, loc ≠ Loc.storageLocal nm)
    (hkp : ∀ {kind ty path index},
      rhs = WrappedExpr.index kind ty path index -> path.kind = Kind.memory)
    (hppath : ∀ {kind ty path index},
      rhs = WrappedExpr.index kind ty path index -> pureExpr path = true) :
    ResultsAgree aliasNames
      (execStmt s (Stmt.assign lhs rhs))
      (execBlock s
        ((ruleEffect .memoryIndexReadUnfoldRightFst).block
          (Stmt.assign lhs rhs) hcond)) := by
  revert hkp hppath
  match rhs, hcond, hfresh with
  | WrappedExpr.index Kind.memory tyR path idxE, hcond, hfresh =>
      intro hkp hppath
      have hkpm : path.kind = Kind.memory := hkp rfl
      have hpp : pureExpr path = true := hppath rfl
      have hfl : ∀ n ∈ aliasNames, usesVar lhs.expr n = false := fun n hn => by
        have := hfresh n hn
        simp [stmtUsesVar] at this
        exact this.1
      have hfi : ∀ n ∈ aliasNames, usesVar idxE n = false := fun n hn => by
        have := hfresh n hn
        simp [stmtUsesVar, usesVar] at this
        exact this.2.2
      show ResultsAgree aliasNames
        (execStmt s (Stmt.assign lhs
          (WrappedExpr.index Kind.memory tyR path idxE)))
        (execBlock s [Stmt.memoryDecl path.ty memoryPathAliasName (some path),
          Stmt.assign lhs (WrappedExpr.index Kind.memory tyR
            (aliasExpr Kind.memory path.ty memoryPathAliasName) idxE)])
      rw [execStmt, execBlock_pair]
      have hRdecl : execStmt s
          (Stmt.memoryDecl path.ty memoryPathAliasName (some path)) =
          (readM s path) >>= fun x =>
            match x.2 with
            | MVal.ref id =>
                .ok (x.1.setEnv memoryPathAliasName (Binding.mref id))
            | MVal.prim _ => .error .stuck := by
        rw [execStmt]
        rw [hkpm]
        rfl
      have hLany : ∀ (err : Halt),
          ((resolveMBase s path : Res (State × Nat)) = .error err) ->
          execAssign s lhs (WrappedExpr.index Kind.memory tyR path idxE) =
            .error err := by
        intro err hmb
        have hcap' : readM s (WrappedExpr.index Kind.memory tyR path idxE) =
            .error err := by
          rw [readM, hmb]
          rfl
        exact execAssign_memoryRhsErr hlhs rfl hnsl
          (fun u => by rw [evalValue]) hcap' 
      cases hcap : readM s path with
      | error err =>
          have hmb : (resolveMBase s path : Res (State × Nat)) =
              .error err := by
            rw [resolveMBase_eq_readM, hcap]
            rfl
          rw [hLany err hmb, hRdecl, hcap]
          exact rfl
      | ok x =>
          obtain ⟨t, mv⟩ := x
          have hts : t = s := readM_pure hpp hcap
          subst hts
          cases mv with
          | prim p =>
              cases p
              all_goals {
                have hmb : (resolveMBase t path : Res (State × Nat)) =
                    .error .stuck := by
                  rw [resolveMBase_eq_readM, hcap]
                  rfl
                rw [hLany .stuck hmb, hRdecl, hcap]
                exact rfl
              }
          | ref id =>
              rw [hRdecl, hcap]
              have ht' : EnvAgreeExcept aliasNames t
                  (t.setEnv memoryPathAliasName (Binding.mref id)) :=
                (EnvAgreeExcept.refl _ t).setEnv_right mp_mem _
              have hmb : (resolveMBase t path : Res (State × Nat)) =
                  .ok (t, id) := by
                rw [resolveMBase_eq_readM, hcap]
                rfl
              have hreadL : readM t
                  (WrappedExpr.index Kind.memory tyR path idxE) =
                  (evalInt t idxE) >>= fun y =>
                    (y.1.getObj id) >>= fun obj =>
                      match obj with
                      | MObj.array elems =>
                          if h : 0 ≤ y.2 ∧ y.2.toNat < elems.length then
                            Except.ok (y.1, elems.get ⟨y.2.toNat, h.2⟩)
                          else Except.error Halt.revert
                      | MObj.struct _ => Except.error Halt.stuck := by
                rw [readM, hmb]
                rfl
              have hreadR : readM
                  (t.setEnv memoryPathAliasName (Binding.mref id))
                  (WrappedExpr.index Kind.memory tyR
                    (aliasExpr Kind.memory path.ty memoryPathAliasName)
                    idxE) =
                  (evalInt (t.setEnv memoryPathAliasName (Binding.mref id))
                      idxE) >>= fun y =>
                    (y.1.getObj id) >>= fun obj =>
                      match obj with
                      | MObj.array elems =>
                          if h : 0 ≤ y.2 ∧ y.2.toNat < elems.length then
                            Except.ok (y.1, elems.get ⟨y.2.toNat, h.2⟩)
                          else Except.error Halt.revert
                      | MObj.struct _ => Except.error Halt.stuck := by
                rw [readM,
                  resolveMBase_alias (s := t.setEnv memoryPathAliasName
                      (Binding.mref id)) path.ty
                    (lookupBy_setBy_self memoryPathAliasName
                      (Binding.mref id) t.env)]
                rfl
              have hreadSim : ResAgree aliasNames
                  (readM t (WrappedExpr.index Kind.memory tyR path idxE))
                  (readM (t.setEnv memoryPathAliasName (Binding.mref id))
                    (WrappedExpr.index Kind.memory tyR
                      (aliasExpr Kind.memory path.ty memoryPathAliasName)
                      idxE)) := by
                rw [hreadL, hreadR]
                refine ResAgree.bind (evalInt_agree ht' idxE hfi) ?_
                intro u₁ u₂ i hu
                simp only [getObj_congr hu]
                refine bindPureRes_agree _ fun obj => ?_
                cases obj with
                | struct fields => exact rfl
                | array elems =>
                    by_cases hb : 0 ≤ i ∧ i.toNat < elems.length
                    · simp only [dif_pos hb]
                      exact ⟨rfl, hu⟩
                    · simp only [dif_neg hb]
                      exact rfl
              show ResultsAgree aliasNames
                (execAssign t lhs
                  (WrappedExpr.index Kind.memory tyR path idxE))
                (execStmt (t.setEnv memoryPathAliasName (Binding.mref id))
                  (Stmt.assign lhs (WrappedExpr.index Kind.memory tyR
                    (aliasExpr Kind.memory path.ty memoryPathAliasName)
                    idxE)))
              rw [execStmt]
              refine execAssign_pureLocSim hlhs hfl rfl rfl ?_ ?_ ?_
              · rw [evalValue, evalValue]
                refine ResAgree.bind hreadSim ?_
                intro u₁ u₂ v hu
                exact bindPureRes_agree _ fun val => ⟨rfl, hu⟩
              · intro h
                rcases h with hk | ⟨nm, hl⟩
                · exact nomatch hk
                · exact absurd hl (hnsl nm)
              · intro _
                exact hreadSim

theorem storageToMemoryDeclUnfoldRightFst_sound
    (s : State) (ty : Ty) (name : Name) (init : Option WrappedExpr)
    (hcond : (ruleEffect .storageToMemoryDeclUnfoldRightFst).cond
      (Stmt.memoryDecl ty name init))
    (hfresh : ∀ n ∈ aliasNames,
      stmtUsesVar (Stmt.memoryDecl ty name init) n = false) :
    ResultsAgree aliasNames
      (execStmt s (Stmt.memoryDecl ty name init))
      (execBlock s
        ((ruleEffect .storageToMemoryDeclUnfoldRightFst).block
          (Stmt.memoryDecl ty name init) hcond)) := by
  match init, hcond, hfresh with
  | some (WrappedExpr.field Kind.storage tyR path fld), hcond, hfresh =>
      show ResultsAgree aliasNames
        (execStmt s (Stmt.memoryDecl ty name
          (some (WrappedExpr.field Kind.storage tyR path fld))))
        (execBlock s [captureStoragePath path,
          Stmt.memoryDecl ty name
            (some (WrappedExpr.field Kind.storage tyR
              (aliasExpr Kind.storage path.ty storagePathAliasName) fld))])
      have hLeq : execStmt s (Stmt.memoryDecl ty name
          (some (WrappedExpr.field Kind.storage tyR path fld))) =
          (resolveS s (WrappedExpr.field Kind.storage tyR path fld)) >>=
            fun x => (x.1.findStorage x.2.1 x.2.2) >>= fun sval =>
              (copyStToM x.1 sval) >>= fun y =>
                match y.2 with
                | MVal.ref id => .ok (y.1.setEnv name (Binding.mref id))
                | MVal.prim _ => .error .stuck := by
        rw [execStmt]
        rfl
      rw [hLeq, execBlock_pair, captureStoragePath, capture, resolveS]
      cases hres : resolveS s path with
      | error err =>
          have hR : execStmt s
              (Stmt.storagePlaceAlias path.ty storagePathAliasName path) =
              .error err := by
            rw [execStmt, hres]
            rfl
          rw [hR]
          exact rfl
      | ok x =>
          obtain ⟨t, root, segs⟩ := x
          have hR : execStmt s
              (Stmt.storagePlaceAlias path.ty storagePathAliasName path) =
              .ok (t.setEnv storagePathAliasName (Binding.spath root segs)) := by
            rw [execStmt, hres]
            rfl
          rw [hR]
          have ht' : EnvAgreeExcept aliasNames t
              (t.setEnv storagePathAliasName (Binding.spath root segs)) :=
            (EnvAgreeExcept.refl _ t).setEnv_right sp_mem _
          have hReq : execStmt
              (t.setEnv storagePathAliasName (Binding.spath root segs))
              (Stmt.memoryDecl ty name
                (some (WrappedExpr.field Kind.storage tyR
                  (aliasExpr Kind.storage path.ty storagePathAliasName)
                  fld))) =
              ((t.setEnv storagePathAliasName
                  (Binding.spath root segs)).findStorage root
                (segs ++ [Seg.field fld.name])) >>= fun sval =>
                (copyStToM (t.setEnv storagePathAliasName
                  (Binding.spath root segs)) sval) >>= fun y =>
                  match y.2 with
                  | MVal.ref id => .ok (y.1.setEnv name (Binding.mref id))
                  | MVal.prim _ => .error .stuck := by
            rw [execStmt, resolveS,
              resolveS_alias (s := t.setEnv storagePathAliasName
                  (Binding.spath root segs)) path.ty
                (lookupBy_setBy_self storagePathAliasName
                  (Binding.spath root segs) t.env)]
            rfl
          show ResultsAgree aliasNames _
            (execStmt (t.setEnv storagePathAliasName (Binding.spath root segs))
              (Stmt.memoryDecl ty name
                (some (WrappedExpr.field Kind.storage tyR
                  (aliasExpr Kind.storage path.ty storagePathAliasName)
                  fld))))
          rw [hReq]
          simp only [resOk_bind, findStorage_congr ht']
          refine bindPureResults_agree _ fun sval => ?_
          refine ResAgree.bindState (copyStToM_agree ht' sval) ?_
          intro w₁ w₂ mv hw
          cases mv with
          | ref id => exact hw.setEnv_both name (Binding.mref id)
          | prim p => cases p <;> exact rfl

/-- KeY `memoryStorageCopyUnfold`: `m = nsp;` captures the complex
storage path into the storage alias `sp` first; the deep copy then
happens through the alias (`memoryStorageCopy` / `execAssign`). -/
theorem memoryStorageCopyUnfold_sound
    (s : State) (lhs : PlaceExpr) (rhs : WrappedExpr)
    (hcond : (ruleEffect .memoryStorageCopyUnfold).cond
      (Stmt.assign lhs rhs))
    (hfresh : ∀ n ∈ aliasNames,
      stmtUsesVar (Stmt.assign lhs rhs) n = false) :
    ResultsAgree aliasNames
      (execStmt s (Stmt.assign lhs rhs))
      (execBlock s ((ruleEffect .memoryStorageCopyUnfold).block
        (Stmt.assign lhs rhs) hcond)) := by
  obtain ⟨h1, h2, h3⟩ := hcond
  simp only [Rules.isSimple, PlaceExpr.kind] at h1 h2
  have hk : rhs.kind = Kind.storage := by
    cases rhs <;> first
      | exact h3.elim
      | (rename_i kind _ _ _
         cases kind <;> first | rfl | exact h3.elim)
  obtain ⟨lexpr, hassign⟩ := lhs
  simp only [PlaceExpr.expr] at h1 h2
  cases lexpr <;>
    simp only [Typed.WrappedExpr.kind] at h1 <;>
    first
      | exact Kind.noConfusion h1
      | (simp only [PlaceExpr.expr, WrappedExpr.simple,
           Typed.WrappedExpr.simple] at h2
         exact Bool.noConfusion h2)
      | skip
  next kindL tyL fldL =>
    subst h1
    show ResultsAgree aliasNames
      (execStmt s (Stmt.assign ⟨WrappedExpr.var Kind.memory tyL fldL, hassign⟩
        rhs))
      (execBlock s [captureStoragePath rhs,
        Stmt.assign ⟨WrappedExpr.var Kind.memory tyL fldL, hassign⟩
          (storageAlias rhs)])
    rw [execStmt, execBlock_pair, execAssign, hk, captureStoragePath,
      capture]
    cases hres : resolveS s rhs with
    | error err =>
        have hR : execStmt s
            (Stmt.storagePlaceAlias rhs.ty storagePathAliasName rhs) =
            .error err := by
          rw [execStmt, hres]
          rfl
        rw [hR]
        exact rfl
    | ok x =>
        obtain ⟨t, root, segs⟩ := x
        have hR : execStmt s
            (Stmt.storagePlaceAlias rhs.ty storagePathAliasName rhs) =
            .ok (t.setEnv storagePathAliasName (Binding.spath root segs)) := by
          rw [execStmt, hres]
          rfl
        rw [hR]
        simp only [resOk_bind]
        have ht' : EnvAgreeExcept aliasNames t
            (t.setEnv storagePathAliasName (Binding.spath root segs)) :=
          (EnvAgreeExcept.refl _ t).setEnv_right sp_mem _
        have hReq : execStmt
            (t.setEnv storagePathAliasName (Binding.spath root segs))
            (Stmt.assign ⟨WrappedExpr.var Kind.memory tyL fldL, hassign⟩
              (storageAlias rhs)) =
            ((t.setEnv storagePathAliasName
                (Binding.spath root segs)).findStorage root segs) >>=
              fun sval =>
                (copyStToM (t.setEnv storagePathAliasName
                  (Binding.spath root segs)) sval) >>= fun y =>
                  match y.2 with
                  | MVal.ref id =>
                      .ok (y.1.setEnv fldL.name (Binding.mref id))
                  | MVal.prim _ => .error .stuck := by
          rw [execStmt, execAssign]
          simp only [storageAlias]
          rw [show (aliasExpr Kind.storage rhs.ty
              storagePathAliasName).kind = Kind.storage from rfl]
          rw [resolveS_alias (s := t.setEnv storagePathAliasName
                (Binding.spath root segs)) rhs.ty
              (lookupBy_setBy_self storagePathAliasName
                (Binding.spath root segs) t.env)]
          rfl
        show ResultsAgree aliasNames _
          (execStmt (t.setEnv storagePathAliasName (Binding.spath root segs))
            (Stmt.assign ⟨WrappedExpr.var Kind.memory tyL fldL, hassign⟩
              (storageAlias rhs)))
        rw [hReq]
        simp only [resOk_bind, findStorage_congr ht']
        refine bindPureResults_agree _ fun sval => ?_
        refine ResAgree.bindState (copyStToM_agree ht' sval) ?_
        intro w₁ w₂ mv hw
        cases mv with
        | ref id => exact hw.setEnv_both fldL.name (Binding.mref id)
        | prim p => cases p <;> exact rfl

/-- **`m[i++] = i` on a memory target is sound now.**
`captureIndexTargetBlock` is `indexWriteResolveBlock`, so this dispatches to
`indexWriteResolveMemory_sound` exactly as the left-fst twin does: no `hpi`, no
`hbase`, no `hrsOk`.  `hkp` is the AST well-formedness fact that a memory index
node has a memory-kinded base. -/
theorem memoryIndexWriteUnfoldLeftSndIndex_sound
    (s : State) (lhs : PlaceExpr) (rhs : WrappedExpr)
    (hcond : (ruleEffect .memoryIndexWriteUnfoldLeftSndIndex).cond
      (Stmt.assign lhs rhs))
    (hprim : rhs.ty.isPrimitive = true)
    (hfresh : ∀ n ∈ aliasNames,
      stmtUsesVar (Stmt.assign lhs rhs) n = false)
    (hkp : ∀ {kind ty path index},
      lhs.expr = WrappedExpr.index kind ty path index ->
        path.kind = Kind.memory) :
    ResultsAgree aliasNames
      (execStmt s (Stmt.assign lhs rhs))
      (execBlock s
        ((ruleEffect .memoryIndexWriteUnfoldLeftSndIndex).block
          (Stmt.assign lhs rhs) hcond)) := by
  obtain ⟨e, hass⟩ := lhs
  revert hkp
  match e, hass, hcond, hfresh with
  | WrappedExpr.index Kind.memory ty path idxE, hass, hcond, hfresh =>
      intro hkp
      refine indexWriteResolveMemory_sound s ty path idxE rhs hprim (hkp rfl)
        ?_ ?_ <;>
        intro n hn <;> have := hfresh n hn <;>
        simp [stmtUsesVar, placeIndex_expr, usesVar] at this
      · exact this.1.1
      · exact this.1.2

theorem memoryIndexReadUnfoldRightSndIndex_sound
    (s : State) (lhs : PlaceExpr) (rhs : WrappedExpr) {loc : Loc} (id : Nat)
    (hcond : (ruleEffect .memoryIndexReadUnfoldRightSndIndex).cond
      (Stmt.assign lhs rhs))
    (hfresh : ∀ n ∈ aliasNames,
      stmtUsesVar (Stmt.assign lhs rhs) n = false)
    (hlhs : resolveLoc s lhs.expr = .ok (s, loc))
    (hplhs : pureExpr lhs.expr = true)
    (hnsl : ∀ nm, loc ≠ Loc.storageLocal nm)
    (hpi : ∀ {kind ty path index},
      rhs = WrappedExpr.index kind ty path index -> pureExpr index = true)
    (hbase : ∀ {kind ty path index},
      rhs = WrappedExpr.index kind ty path index ->
        resolveMBase s path = .ok (s, id)) :
    ResultsAgree aliasNames
      (execStmt s (Stmt.assign lhs rhs))
      (execBlock s
        ((ruleEffect .memoryIndexReadUnfoldRightSndIndex).block
          (Stmt.assign lhs rhs) hcond)) := by
  revert hpi hbase
  match rhs, hcond, hfresh with
  | WrappedExpr.index Kind.memory tyR path idxE, hcond, hfresh =>
      intro hpi hbase
      have hb : resolveMBase s path = .ok (s, id) := hbase rfl
      have hpix : pureExpr idxE = true := hpi rfl
      have hpp : pureExpr path = true := pure_of_simple hcond.1
      have hfl : ∀ n ∈ aliasNames, usesVar lhs.expr n = false := fun n hn => by
        have := hfresh n hn
        simp [stmtUsesVar] at this
        exact this.1
      have hfp : ∀ n ∈ aliasNames, usesVar path n = false := fun n hn => by
        have := hfresh n hn
        simp [stmtUsesVar, usesVar] at this
        exact this.2.1
      show ResultsAgree aliasNames
        (execStmt s (Stmt.assign lhs
          (WrappedExpr.index Kind.memory tyR path idxE)))
        (execBlock s [Stmt.stackDecl idxE.ty indexAliasName (some idxE),
          Stmt.assign lhs (WrappedExpr.index Kind.memory tyR path
            (indexAlias idxE))])
      rw [execStmt, execBlock_pair]
      cases hev : evalValue s idxE with
      | error err =>
          have hL : execAssign s lhs
              (WrappedExpr.index Kind.memory tyR path idxE) = .error err := by
            have hcap' : readM s
                (WrappedExpr.index Kind.memory tyR path idxE) =
                .error err := by
              rw [readM, hb]
              simp only [resOk_bind]
              rw [evalInt, hev]
              rfl
            exact execAssign_memoryRhsErr hlhs rfl hnsl
              (fun u => by rw [evalValue]) hcap'
          have hR : execStmt s
              (Stmt.stackDecl idxE.ty indexAliasName (some idxE)) =
              .error err := by
            rw [execStmt, hev]
            rfl
          rw [hL, hR]
          exact rfl
      | ok y =>
          obtain ⟨t, v⟩ := y
          have hts : t = s := evalValue_pure hpix hev
          subst hts
          have hR : execStmt t
              (Stmt.stackDecl idxE.ty indexAliasName (some idxE)) =
              .ok (t.setEnv indexAliasName (Binding.val v)) := by
            rw [execStmt, hev]
            rfl
          rw [hR]
          have ht' : EnvAgreeExcept aliasNames t
              (t.setEnv indexAliasName (Binding.val v)) :=
            (EnvAgreeExcept.refl _ t).setEnv_right idx_mem _
          have hb' : resolveMBase (t.setEnv indexAliasName (Binding.val v))
              path = .ok (t.setEnv indexAliasName (Binding.val v), id) := by
            have h := resolveMBase_agree ht' path hfp
            rw [hb] at h
            rcases h.cases with ⟨err, h1, h2⟩ | ⟨u₁, u₂, a, h1, h2, hu⟩
            · exact nomatch h1
            · have ha : a = id := (congrArg Prod.snd (Except.ok.inj h1)).symm
              have hu2 : u₂ = t.setEnv indexAliasName (Binding.val v) :=
                resolveMBase_pure hpp h2
              rw [h2, hu2, ha]
          have hreadL : readM t
              (WrappedExpr.index Kind.memory tyR path idxE) =
              (((v.asInt) >>= fun i => Except.ok (t, i)) >>= fun y =>
                (y.1.getObj id) >>= fun obj =>
                  match obj with
                  | MObj.array elems =>
                      if h : 0 ≤ y.2 ∧ y.2.toNat < elems.length then
                        Except.ok (y.1, elems.get ⟨y.2.toNat, h.2⟩)
                      else Except.error Halt.revert
                  | MObj.struct _ => Except.error Halt.stuck) := by
            rw [readM, hb]
            simp only [resOk_bind]
            rw [evalInt, hev]
            rfl
          have hreadR : readM (t.setEnv indexAliasName (Binding.val v))
              (WrappedExpr.index Kind.memory tyR path (indexAlias idxE)) =
              (((v.asInt) >>= fun i =>
                  Except.ok (t.setEnv indexAliasName (Binding.val v),
                    i)) >>= fun y =>
                (y.1.getObj id) >>= fun obj =>
                  match obj with
                  | MObj.array elems =>
                      if h : 0 ≤ y.2 ∧ y.2.toNat < elems.length then
                        Except.ok (y.1, elems.get ⟨y.2.toNat, h.2⟩)
                      else Except.error Halt.revert
                  | MObj.struct _ => Except.error Halt.stuck) := by
            rw [readM, hb']
            simp only [resOk_bind]
            rw [evalInt, indexAlias,
              evalValue_alias idxE.ty
                (lookupBy_setBy_self indexAliasName (Binding.val v) t.env)]
            rfl
          have hreadSim : ResAgree aliasNames
              (readM t (WrappedExpr.index Kind.memory tyR path idxE))
              (readM (t.setEnv indexAliasName (Binding.val v))
                (WrappedExpr.index Kind.memory tyR path
                  (indexAlias idxE))) := by
            rw [hreadL, hreadR]
            refine ResAgree.bind ?_ ?_
            · exact bindPureRes_agree _ fun i => ⟨rfl, ht'⟩
            · intro u₁ u₂ i hu
              simp only [getObj_congr hu]
              refine bindPureRes_agree _ fun obj => ?_
              cases obj with
              | struct fields => exact rfl
              | array elems =>
                  by_cases hbnd : 0 ≤ i ∧ i.toNat < elems.length
                  · simp only [dif_pos hbnd]
                    exact ⟨rfl, hu⟩
                  · simp only [dif_neg hbnd]
                    exact rfl
          show ResultsAgree aliasNames
            (execAssign t lhs
              (WrappedExpr.index Kind.memory tyR path idxE))
            (execStmt (t.setEnv indexAliasName (Binding.val v))
              (Stmt.assign lhs (WrappedExpr.index Kind.memory tyR path
                (indexAlias idxE))))
          rw [execStmt]
          refine execAssign_pureLocSim hlhs hfl rfl rfl ?_ ?_ ?_
          · rw [evalValue, evalValue]
            refine ResAgree.bind hreadSim ?_
            intro u₁ u₂ w hu
            exact bindPureRes_agree _ fun val => ⟨rfl, hu⟩
          · intro h
            rcases h with hk | ⟨nm, hl⟩
            · exact nomatch hk
            · exact absurd hl (hnsl nm)
          · intro _
            exact hreadSim

theorem storageLocalRootPushUnfoldLeftFstReceiver_sound
    (s : State) (lhs : PlaceExpr) (rhs : WrappedExpr) {loc : Loc}
    (hcond : (ruleEffect
      .storageLocalRootPushUnfoldLeftFstReceiver).cond
      (Stmt.assign lhs rhs))
    (hfresh : ∀ n ∈ aliasNames,
      stmtUsesVar (Stmt.assign lhs rhs) n = false)
    (hlhs : resolveLoc s lhs.expr = .ok (s, loc))
    (hplhs : pureExpr lhs.expr = true)
    (hnst : ∀ nm, loc ≠ Loc.stack nm)
    (hasgn : ∀ {target}, rhs = WrappedExpr.pushPlace target ->
      target.assignable = true)
    (hptgt : ∀ {target}, rhs = WrappedExpr.pushPlace target ->
      pureExpr target = true)
    (hprimF : ∀ {target}, rhs = WrappedExpr.pushPlace target ->
      (WrappedExpr.pushPlace target).ty.isPrimitive = false)
    (hnm : ∀ {target}, rhs = WrappedExpr.pushPlace target ->
      tyHasMapping (WrappedExpr.pushPlace target).ty = false) :
    ResultsAgree aliasNames
      (execStmt s (Stmt.assign lhs rhs))
      (execBlock s
        ((ruleEffect .storageLocalRootPushUnfoldLeftFstReceiver).block
          (Stmt.assign lhs rhs) hcond)) := by
  revert hasgn hptgt hprimF hnm
  match rhs, hcond, hfresh with
  | WrappedExpr.pushPlace target, hcond, hfresh =>
      intro hasgn hptgt hprimF hnm
      have ha : target.assignable = true := hasgn rfl
      have hpt : pureExpr target = true := hptgt rfl
      have hpF : (WrappedExpr.pushPlace target).ty.isPrimitive = false :=
        hprimF rfl
      have hnmP : tyHasMapping (WrappedExpr.pushPlace target).ty = false :=
        hnm rfl
      have hks : target.kind = Kind.storage := hcond.1
      have hkpp : (WrappedExpr.pushPlace target).kind = Kind.storage := rfl
      have hfl : ∀ n ∈ aliasNames, usesVar lhs.expr n = false := fun n hn => by
        have := hfresh n hn
        simp [stmtUsesVar] at this
        exact this.1
      have hft : ∀ n ∈ aliasNames, usesVar target n = false := fun n hn => by
        have := hfresh n hn
        simp [stmtUsesVar, usesVar] at this
        exact this.2
      show ResultsAgree aliasNames
        (execStmt s (Stmt.assign lhs (WrappedExpr.pushPlace target)))
        (execBlock s
          (match asPlace? target with
            | some _ =>
                [captureStoragePath target,
                  Stmt.assign lhs (WrappedExpr.pushPlace
                    (aliasExpr Kind.storage target.ty storagePathAliasName))]
            | none => []))
      rw [asPlace?, dif_pos ha]
      rw [execStmt, execBlock_pair, captureStoragePath, capture]
      cases hcap : resolveS s target with
      | error err =>
          have hL : execAssign s lhs (WrappedExpr.pushPlace target) =
              .error err := by
            have hcapP : resolveS s (WrappedExpr.pushPlace target) =
                .error err := by
              rw [resolveS, hcap]
              rfl
            exact execAssign_storageRhsErrNonPrim hlhs hkpp hpF hnmP hnst
              hcapP
          have hR : execStmt s
              (Stmt.storagePlaceAlias target.ty storagePathAliasName
                target) = .error err := by
            rw [execStmt, hcap]
            rfl
          rw [hL, hR]
          exact rfl
      | ok x =>
          obtain ⟨t, root, segs⟩ := x
          have hts : t = s := resolveS_pure hpt hcap
          subst hts
          have hR : execStmt t
              (Stmt.storagePlaceAlias target.ty storagePathAliasName
                target) =
              .ok (t.setEnv storagePathAliasName (Binding.spath root segs)) := by
            rw [execStmt, hcap]
            rfl
          rw [hR]
          have ht' : EnvAgreeExcept aliasNames t
              (t.setEnv storagePathAliasName (Binding.spath root segs)) :=
            (EnvAgreeExcept.refl _ t).setEnv_right sp_mem _
          have hresSim : ResAgree aliasNames
              (resolveS t (WrappedExpr.pushPlace target))
              (resolveS
                (t.setEnv storagePathAliasName (Binding.spath root segs))
                (WrappedExpr.pushPlace
                  (aliasExpr Kind.storage target.ty
                    storagePathAliasName))) := by
            rw [resolveS, resolveS, hcap,
              resolveS_alias (s := t.setEnv storagePathAliasName
                  (Binding.spath root segs)) target.ty
                (lookupBy_setBy_self storagePathAliasName
                  (Binding.spath root segs) t.env)]
            simp only [resOk_bind, findStorage_congr ht']
            refine bindPureRes_agree _ fun arr => ?_
            cases arr with
            | array elems =>
                have htyP : (aliasExpr Kind.storage target.ty
                    storagePathAliasName).ty = target.ty := rfl
                rw [htyP]
                match hty : target.ty with
                | Ty.ref (RefTy.array elemTy) =>
                    refine ResultsAgree.bindRes
                      (saveStorage_agree ht' root segs
                        (SVal.array (elems ++ [defaultForTy elemTy]))) ?_
                    intro u₁ u₂ hu
                    exact ⟨rfl, hu⟩
                | Ty.bool => exact rfl
                | Ty.uint => exact rfl
                | Ty.int => exact rfl
                | Ty.ref (RefTy.struct nm) => exact rfl
                | Ty.ref (RefTy.mapping k v) => exact rfl
            | prim p => cases p <;> exact rfl
            | struct fields => exact rfl
            | map entries dflt => exact rfl
          show ResultsAgree aliasNames
            (execAssign t lhs (WrappedExpr.pushPlace target))
            (execStmt (t.setEnv storagePathAliasName (Binding.spath root segs))
              (Stmt.assign lhs (WrappedExpr.pushPlace
                (aliasExpr Kind.storage target.ty storagePathAliasName))))
          rw [execStmt]
          refine execAssign_pureLocSim hlhs hfl rfl ?_ ?_ ?_ ?_
          · have h1 : (WrappedExpr.pushPlace
                (aliasExpr Kind.storage target.ty
                  storagePathAliasName)).kind = Kind.storage := rfl
            rw [h1, hkpp]
          · rw [evalValue.eq_def, evalValue.eq_def]
            exact rfl
          · intro _
            exact hresSim
          · intro hm
            have hm' : Kind.storage = Kind.memory := hkpp ▸ hm
            exact nomatch hm'

theorem valueRhsCaptureAssign_sound
    (s : State) (lhs : PlaceExpr) (rhs : WrappedExpr) {loc : Loc}
    (hfresh : ∀ n ∈ aliasNames,
      stmtUsesVar (Stmt.assign lhs rhs) n = false)
    (hlhs : resolveLoc s lhs.expr = .ok (s, loc))
    (hplhs : pureExpr lhs.expr = true)
    (hprim : rhs.ty.isPrimitive = true)
    (hnsl : ∀ nm, loc ≠ Loc.storageLocal nm)
    (hnmr : ∀ nm, loc ≠ Loc.memoryRoot nm)
    (hstable : ∀ t v, evalValue s rhs = .ok (t, v) ->
      resolveLoc t lhs.expr = .ok (t, loc)) :
    ResultsAgree aliasNames
      (execStmt s (Stmt.assign lhs rhs))
      (execBlock s [captureStackValue rhs,
        Stmt.assign lhs (stackValueAlias rhs)]) := by
  have hfl : ∀ n ∈ aliasNames, usesVar lhs.expr n = false := fun n hn => by
    have := hfresh n hn
    simp [stmtUsesVar] at this
    exact this.1
  rw [execStmt, execBlock_pair]
  cases hev : evalValue s rhs with
  | error err =>
      have hL : execAssign s lhs rhs = .error err :=
        execAssign_evalErr hlhs hprim hnsl hnmr hev
      have hR : execStmt s (captureStackValue rhs) = .error err := by
        rw [captureStackValue, capture, execStmt, hev]
        rfl
      rw [hL, hR]
      exact rfl
  | ok x =>
      obtain ⟨t, v⟩ := x
      have hR : execStmt s (captureStackValue rhs) =
          .ok (t.setEnv valueAliasName (Binding.val v)) := by
        rw [captureStackValue, capture, execStmt, hev]
        rfl
      rw [hR]
      have ht' : EnvAgreeExcept aliasNames t
          (t.setEnv valueAliasName (Binding.val v)) :=
        (EnvAgreeExcept.refl _ t).setEnv_right pv_mem _
      have hstab := hstable t v hev
      have htrans : resolveLoc (t.setEnv valueAliasName (Binding.val v))
          lhs.expr =
          .ok (t.setEnv valueAliasName (Binding.val v), loc) :=
        resolveLoc_transport ht' hfl hplhs hstab
      have hevAlias : evalValue (t.setEnv valueAliasName (Binding.val v))
          (stackValueAlias rhs) =
          .ok (t.setEnv valueAliasName (Binding.val v), v) := by
        rw [stackValueAlias,
          evalValue_alias rhs.ty
            (lookupBy_setBy_self valueAliasName (Binding.val v) t.env)]
      show ResultsAgree aliasNames
        (execAssign s lhs rhs)
        (execStmt (t.setEnv valueAliasName (Binding.val v))
          (Stmt.assign lhs (stackValueAlias rhs)))
      have hprimA : (stackValueAlias rhs).ty.isPrimitive = true := hprim
      rw [execStmt,
        execAssign_evalOkPrim hlhs hstab hprim hnsl hnmr hev,
        execAssign_evalOkPrim htrans htrans hprimA hnsl hnmr hevAlias]
      exact writeLoc_agree ht' v

theorem storageRootWriteValueRhsCapture_sound
    (s : State) (lhs : PlaceExpr) (rhs : WrappedExpr) {loc : Loc}
    (hcond : (ruleEffect .storageRootWriteValueRhsCapture).cond
      (Stmt.assign lhs rhs))
    (hfresh : ∀ n ∈ aliasNames,
      stmtUsesVar (Stmt.assign lhs rhs) n = false)
    (hlhs : resolveLoc s lhs.expr = .ok (s, loc))
    (hplhs : pureExpr lhs.expr = true)
    (hprim : rhs.ty.isPrimitive = true)
    (hnsl : ∀ nm, loc ≠ Loc.storageLocal nm)
    (hnmr : ∀ nm, loc ≠ Loc.memoryRoot nm)
    (hstable : ∀ t v, evalValue s rhs = .ok (t, v) ->
      resolveLoc t lhs.expr = .ok (t, loc)) :
    ResultsAgree aliasNames
      (execStmt s (Stmt.assign lhs rhs))
      (execBlock s ((ruleEffect .storageRootWriteValueRhsCapture).block
        (Stmt.assign lhs rhs) hcond)) :=
  valueRhsCaptureAssign_sound s lhs rhs hfresh hlhs hplhs hprim hnsl hnmr
    hstable

theorem fieldWriteValueRhsCapture_sound
    (s : State) (lhs : PlaceExpr) (rhs : WrappedExpr) {loc : Loc}
    (hcond : (ruleEffect .fieldWriteValueRhsCapture).cond
      (Stmt.assign lhs rhs))
    (hfresh : ∀ n ∈ aliasNames,
      stmtUsesVar (Stmt.assign lhs rhs) n = false)
    (hlhs : resolveLoc s lhs.expr = .ok (s, loc))
    (hplhs : pureExpr lhs.expr = true)
    (hprim : rhs.ty.isPrimitive = true)
    (hnsl : ∀ nm, loc ≠ Loc.storageLocal nm)
    (hnmr : ∀ nm, loc ≠ Loc.memoryRoot nm)
    (hstable : ∀ t v, evalValue s rhs = .ok (t, v) ->
      resolveLoc t lhs.expr = .ok (t, loc)) :
    ResultsAgree aliasNames
      (execStmt s (Stmt.assign lhs rhs))
      (execBlock s ((ruleEffect .fieldWriteValueRhsCapture).block
        (Stmt.assign lhs rhs) hcond)) :=
  valueRhsCaptureAssign_sound s lhs rhs hfresh hlhs hplhs hprim hnsl hnmr
    hstable

theorem indexWriteValueRhsCapture_sound
    (s : State) (lhs : PlaceExpr) (rhs : WrappedExpr) {loc : Loc}
    (hcond : (ruleEffect .indexWriteValueRhsCapture).cond
      (Stmt.assign lhs rhs))
    (hfresh : ∀ n ∈ aliasNames,
      stmtUsesVar (Stmt.assign lhs rhs) n = false)
    (hlhs : resolveLoc s lhs.expr = .ok (s, loc))
    (hplhs : pureExpr lhs.expr = true)
    (hprim : rhs.ty.isPrimitive = true)
    (hnsl : ∀ nm, loc ≠ Loc.storageLocal nm)
    (hnmr : ∀ nm, loc ≠ Loc.memoryRoot nm)
    (hstable : ∀ t v, evalValue s rhs = .ok (t, v) ->
      resolveLoc t lhs.expr = .ok (t, loc)) :
    ResultsAgree aliasNames
      (execStmt s (Stmt.assign lhs rhs))
      (execBlock s ((ruleEffect .indexWriteValueRhsCapture).block
        (Stmt.assign lhs rhs) hcond)) :=
  valueRhsCaptureAssign_sound s lhs rhs hfresh hlhs hplhs hprim hnsl hnmr
    hstable

theorem memoryFieldReadUnfoldRightSndResult_sound
    (s : State) (lhs : PlaceExpr) (rhs : WrappedExpr) {loc : Loc}
    (hcond : (ruleEffect .memoryFieldReadUnfoldRightSndResult).cond
      (Stmt.assign lhs rhs))
    (hfresh : ∀ n ∈ aliasNames,
      stmtUsesVar (Stmt.assign lhs rhs) n = false)
    (hlhs : resolveLoc s lhs.expr = .ok (s, loc))
    (hplhs : pureExpr lhs.expr = true)
    (hml : (∃ id fld, loc = Loc.memoryField id fld) ∨
      (∃ id i, loc = Loc.memoryIndex id i))
    (hwf : rhs.ty.isPrimitive = false -> ∀ t mv,
      readM s rhs = .ok (t, mv) -> ∃ id, mv = MVal.ref id) :
    ResultsAgree aliasNames
      (execStmt s (Stmt.assign lhs rhs))
      (execBlock s
        ((ruleEffect .memoryFieldReadUnfoldRightSndResult).block
          (Stmt.assign lhs rhs) hcond)) := by
  have hnsl : ∀ nm, loc ≠ Loc.storageLocal nm := fun nm h => by
    rcases hml with ⟨_, _, h2⟩ | ⟨_, _, h2⟩ <;> rw [h2] at h <;>
      exact nomatch h
  have hnmr : ∀ nm, loc ≠ Loc.memoryRoot nm := fun nm h => by
    rcases hml with ⟨_, _, h2⟩ | ⟨_, _, h2⟩ <;> rw [h2] at h <;>
      exact nomatch h
  have hnst : ∀ nm, loc ≠ Loc.stack nm := fun nm h => by
    rcases hml with ⟨_, _, h2⟩ | ⟨_, _, h2⟩ <;> rw [h2] at h <;>
      exact nomatch h
  have hnsg : ∀ root segs, loc ≠ Loc.storage root segs := fun r sg h => by
    rcases hml with ⟨_, _, h2⟩ | ⟨_, _, h2⟩ <;> rw [h2] at h <;>
      exact nomatch h
  revert hwf
  match rhs, hcond, hfresh with
  | WrappedExpr.field Kind.memory tyR path fldR, hcond, hfresh =>
      intro hwf
      have hpr : pureExpr (WrappedExpr.field Kind.memory tyR path fldR) =
          true := pure_of_simple (e := path) hcond.2.2
      have hfl : ∀ n ∈ aliasNames, usesVar lhs.expr n = false := fun n hn => by
        have := hfresh n hn
        simp [stmtUsesVar] at this
        exact this.1
      show ResultsAgree aliasNames
        (execStmt s (Stmt.assign lhs
          (WrappedExpr.field Kind.memory tyR path fldR)))
        (execBlock s
          [captureValue (WrappedExpr.field Kind.memory tyR path fldR),
          Stmt.assign lhs
            (valueAlias (WrappedExpr.field Kind.memory tyR path fldR))])
      rw [execStmt, execBlock_pair]
      cases hprim : (WrappedExpr.field Kind.memory tyR path
          fldR).ty.isPrimitive with
      | true =>
          have hvck : valueCaptureKind
              (WrappedExpr.field Kind.memory tyR path fldR) = Kind.stack := by
            rw [valueCaptureKind]
            simp [hprim]
            intro h
            exact nomatch h
          rw [captureValue, valueAlias, hvck, capture]
          cases hev : evalValue s
              (WrappedExpr.field Kind.memory tyR path fldR) with
          | error err =>
              have hL : execAssign s lhs
                  (WrappedExpr.field Kind.memory tyR path fldR) =
                  .error err :=
                execAssign_evalErr hlhs hprim hnsl hnmr hev
              have hR : execStmt s
                  (Stmt.stackDecl (WrappedExpr.field Kind.memory tyR path
                    fldR).ty valueAliasName
                    (some (WrappedExpr.field Kind.memory tyR path fldR))) =
                  .error err := by
                rw [execStmt, hev]
                rfl
              rw [hL, hR]
              exact rfl
          | ok x =>
              obtain ⟨t, v⟩ := x
              have hts : t = s := evalValue_pure hpr hev
              subst hts
              have hR : execStmt t
                  (Stmt.stackDecl (WrappedExpr.field Kind.memory tyR path
                    fldR).ty valueAliasName
                    (some (WrappedExpr.field Kind.memory tyR path fldR))) =
                  .ok (t.setEnv valueAliasName (Binding.val v)) := by
                rw [execStmt, hev]
                rfl
              rw [hR]
              have ht' : EnvAgreeExcept aliasNames t
                  (t.setEnv valueAliasName (Binding.val v)) :=
                (EnvAgreeExcept.refl _ t).setEnv_right pv_mem _
              show ResultsAgree aliasNames
                (execAssign t lhs
                  (WrappedExpr.field Kind.memory tyR path fldR))
                (execStmt (t.setEnv valueAliasName (Binding.val v))
                  (Stmt.assign lhs (aliasExpr Kind.stack
                    (WrappedExpr.field Kind.memory tyR path fldR).ty
                    valueAliasName)))
              rw [execStmt]
              refine execAssign_pureLocSimPrim hlhs hfl rfl hprim ?_
                hnsl hnmr
              rw [hev,
                evalValue_alias (WrappedExpr.field Kind.memory tyR path
                    fldR).ty
                  (lookupBy_setBy_self valueAliasName (Binding.val v) t.env)]
              exact ⟨rfl, ht'⟩
      | false =>
          have hvck : valueCaptureKind
              (WrappedExpr.field Kind.memory tyR path fldR) =
              Kind.memory := by
            rw [valueCaptureKind]
            simp [hprim]
            rfl
          rw [captureValue, valueAlias, hvck, capture]
          cases hcap : readM s
              (WrappedExpr.field Kind.memory tyR path fldR) with
          | error err =>
              have hL : execAssign s lhs
                  (WrappedExpr.field Kind.memory tyR path fldR) =
                  .error err :=
                execAssign_memoryRhsErr hlhs rfl hnsl
                  (fun u => by rw [evalValue]) hcap
              have hR : execStmt s
                  (Stmt.memoryDecl (WrappedExpr.field Kind.memory tyR path
                    fldR).ty valueAliasName
                    (some (WrappedExpr.field Kind.memory tyR path fldR))) =
                  .error err := by
                rw [execStmt, hcap]
                rfl
              rw [hL, hR]
              exact rfl
          | ok x =>
              obtain ⟨t, mv⟩ := x
              have hts : t = s := readM_pure hpr hcap
              subst hts
              obtain ⟨id, hmv⟩ := hwf hprim t mv hcap
              subst hmv
              have hR : execStmt t
                  (Stmt.memoryDecl (WrappedExpr.field Kind.memory tyR path
                    fldR).ty valueAliasName
                    (some (WrappedExpr.field Kind.memory tyR path fldR))) =
                  .ok (t.setEnv valueAliasName (Binding.mref id)) := by
                rw [execStmt, hcap]
                rfl
              rw [hR]
              have ht' : EnvAgreeExcept aliasNames t
                  (t.setEnv valueAliasName (Binding.mref id)) :=
                (EnvAgreeExcept.refl _ t).setEnv_right pv_mem _
              have hevL : evalValue t
                  (WrappedExpr.field Kind.memory tyR path fldR) =
                  .error .stuck := by
                rw [evalValue, hcap]
                rfl
              have hevR : evalValue
                  (t.setEnv valueAliasName (Binding.mref id))
                  (aliasExpr Kind.memory (WrappedExpr.field Kind.memory tyR
                    path fldR).ty valueAliasName) = .error .stuck := by
                rw [aliasExpr, evalValue]
              have hrdR : readM (t.setEnv valueAliasName (Binding.mref id))
                  (aliasExpr Kind.memory (WrappedExpr.field Kind.memory tyR
                    path fldR).ty valueAliasName) =
                  .ok (t.setEnv valueAliasName (Binding.mref id),
                    MVal.ref id) :=
                readM_alias _
                  (lookupBy_setBy_self valueAliasName (Binding.mref id)
                    t.env)
              show ResultsAgree aliasNames
                (execAssign t lhs
                  (WrappedExpr.field Kind.memory tyR path fldR))
                (execStmt (t.setEnv valueAliasName (Binding.mref id))
                  (Stmt.assign lhs (aliasExpr Kind.memory
                    (WrappedExpr.field Kind.memory tyR path fldR).ty
                    valueAliasName)))
              rw [execStmt]
              refine execAssign_pureLocSim hlhs hfl rfl rfl ?_ ?_ ?_
              · rw [hevL, hevR]
                exact rfl
              · intro h
                rcases h with hk | ⟨nm, hl⟩
                · exact nomatch hk
                · exact absurd hl (hnsl nm)
              · intro _
                rw [hcap, hrdR]
                exact ⟨rfl, ht'⟩

theorem memoryIndexReadUnfoldRightSndResult_sound
    (s : State) (lhs : PlaceExpr) (rhs : WrappedExpr) {loc : Loc}
    (hcond : (ruleEffect .memoryIndexReadUnfoldRightSndResult).cond
      (Stmt.assign lhs rhs))
    (hfresh : ∀ n ∈ aliasNames,
      stmtUsesVar (Stmt.assign lhs rhs) n = false)
    (hlhs : resolveLoc s lhs.expr = .ok (s, loc))
    (hplhs : pureExpr lhs.expr = true)
    (hml : (∃ id fld, loc = Loc.memoryField id fld) ∨
      (∃ id i, loc = Loc.memoryIndex id i))
    (hwf : rhs.ty.isPrimitive = false -> ∀ t mv,
      readM s rhs = .ok (t, mv) -> ∃ id, mv = MVal.ref id) :
    ResultsAgree aliasNames
      (execStmt s (Stmt.assign lhs rhs))
      (execBlock s
        ((ruleEffect .memoryIndexReadUnfoldRightSndResult).block
          (Stmt.assign lhs rhs) hcond)) := by
  have hnsl : ∀ nm, loc ≠ Loc.storageLocal nm := fun nm h => by
    rcases hml with ⟨_, _, h2⟩ | ⟨_, _, h2⟩ <;> rw [h2] at h <;>
      exact nomatch h
  have hnmr : ∀ nm, loc ≠ Loc.memoryRoot nm := fun nm h => by
    rcases hml with ⟨_, _, h2⟩ | ⟨_, _, h2⟩ <;> rw [h2] at h <;>
      exact nomatch h
  have hnst : ∀ nm, loc ≠ Loc.stack nm := fun nm h => by
    rcases hml with ⟨_, _, h2⟩ | ⟨_, _, h2⟩ <;> rw [h2] at h <;>
      exact nomatch h
  have hnsg : ∀ root segs, loc ≠ Loc.storage root segs := fun r sg h => by
    rcases hml with ⟨_, _, h2⟩ | ⟨_, _, h2⟩ <;> rw [h2] at h <;>
      exact nomatch h
  revert hwf
  match rhs, hcond, hfresh with
  | WrappedExpr.index Kind.memory tyR path idxE, hcond, hfresh =>
      intro hwf
      have hpr : pureExpr (WrappedExpr.index Kind.memory tyR path idxE) =
          true := by
        have h1 := pure_of_simple (e := path) hcond.2.2.1
        have h2 := pure_of_simple (e := idxE) hcond.2.2.2
        simp [pureExpr, h1, h2]
      have hfl : ∀ n ∈ aliasNames, usesVar lhs.expr n = false := fun n hn => by
        have := hfresh n hn
        simp [stmtUsesVar] at this
        exact this.1
      show ResultsAgree aliasNames
        (execStmt s (Stmt.assign lhs
          (WrappedExpr.index Kind.memory tyR path idxE)))
        (execBlock s
          [captureValue (WrappedExpr.index Kind.memory tyR path idxE),
          Stmt.assign lhs
            (valueAlias (WrappedExpr.index Kind.memory tyR path idxE))])
      rw [execStmt, execBlock_pair]
      cases hprim : (WrappedExpr.index Kind.memory tyR path
          idxE).ty.isPrimitive with
      | true =>
          have hvck : valueCaptureKind
              (WrappedExpr.index Kind.memory tyR path idxE) = Kind.stack := by
            rw [valueCaptureKind]
            simp [hprim]
            intro h
            exact nomatch h
          rw [captureValue, valueAlias, hvck, capture]
          cases hev : evalValue s
              (WrappedExpr.index Kind.memory tyR path idxE) with
          | error err =>
              have hL : execAssign s lhs
                  (WrappedExpr.index Kind.memory tyR path idxE) =
                  .error err :=
                execAssign_evalErr hlhs hprim hnsl hnmr hev
              have hR : execStmt s
                  (Stmt.stackDecl (WrappedExpr.index Kind.memory tyR path
                    idxE).ty valueAliasName
                    (some (WrappedExpr.index Kind.memory tyR path idxE))) =
                  .error err := by
                rw [execStmt, hev]
                rfl
              rw [hL, hR]
              exact rfl
          | ok x =>
              obtain ⟨t, v⟩ := x
              have hts : t = s := evalValue_pure hpr hev
              subst hts
              have hR : execStmt t
                  (Stmt.stackDecl (WrappedExpr.index Kind.memory tyR path
                    idxE).ty valueAliasName
                    (some (WrappedExpr.index Kind.memory tyR path idxE))) =
                  .ok (t.setEnv valueAliasName (Binding.val v)) := by
                rw [execStmt, hev]
                rfl
              rw [hR]
              have ht' : EnvAgreeExcept aliasNames t
                  (t.setEnv valueAliasName (Binding.val v)) :=
                (EnvAgreeExcept.refl _ t).setEnv_right pv_mem _
              show ResultsAgree aliasNames
                (execAssign t lhs
                  (WrappedExpr.index Kind.memory tyR path idxE))
                (execStmt (t.setEnv valueAliasName (Binding.val v))
                  (Stmt.assign lhs (aliasExpr Kind.stack
                    (WrappedExpr.index Kind.memory tyR path idxE).ty
                    valueAliasName)))
              rw [execStmt]
              refine execAssign_pureLocSimPrim hlhs hfl rfl hprim ?_
                hnsl hnmr
              rw [hev,
                evalValue_alias (WrappedExpr.index Kind.memory tyR path
                    idxE).ty
                  (lookupBy_setBy_self valueAliasName (Binding.val v) t.env)]
              exact ⟨rfl, ht'⟩
      | false =>
          have hvck : valueCaptureKind
              (WrappedExpr.index Kind.memory tyR path idxE) =
              Kind.memory := by
            rw [valueCaptureKind]
            simp [hprim]
            rfl
          rw [captureValue, valueAlias, hvck, capture]
          cases hcap : readM s
              (WrappedExpr.index Kind.memory tyR path idxE) with
          | error err =>
              have hL : execAssign s lhs
                  (WrappedExpr.index Kind.memory tyR path idxE) =
                  .error err :=
                execAssign_memoryRhsErr hlhs rfl hnsl
                  (fun u => by rw [evalValue]) hcap
              have hR : execStmt s
                  (Stmt.memoryDecl (WrappedExpr.index Kind.memory tyR path
                    idxE).ty valueAliasName
                    (some (WrappedExpr.index Kind.memory tyR path idxE))) =
                  .error err := by
                rw [execStmt, hcap]
                rfl
              rw [hL, hR]
              exact rfl
          | ok x =>
              obtain ⟨t, mv⟩ := x
              have hts : t = s := readM_pure hpr hcap
              subst hts
              obtain ⟨id, hmv⟩ := hwf hprim t mv hcap
              subst hmv
              have hR : execStmt t
                  (Stmt.memoryDecl (WrappedExpr.index Kind.memory tyR path
                    idxE).ty valueAliasName
                    (some (WrappedExpr.index Kind.memory tyR path idxE))) =
                  .ok (t.setEnv valueAliasName (Binding.mref id)) := by
                rw [execStmt, hcap]
                rfl
              rw [hR]
              have ht' : EnvAgreeExcept aliasNames t
                  (t.setEnv valueAliasName (Binding.mref id)) :=
                (EnvAgreeExcept.refl _ t).setEnv_right pv_mem _
              have hevL : evalValue t
                  (WrappedExpr.index Kind.memory tyR path idxE) =
                  .error .stuck := by
                rw [evalValue, hcap]
                rfl
              have hevR : evalValue
                  (t.setEnv valueAliasName (Binding.mref id))
                  (aliasExpr Kind.memory (WrappedExpr.index Kind.memory tyR
                    path idxE).ty valueAliasName) = .error .stuck := by
                rw [aliasExpr, evalValue]
              have hrdR : readM (t.setEnv valueAliasName (Binding.mref id))
                  (aliasExpr Kind.memory (WrappedExpr.index Kind.memory tyR
                    path idxE).ty valueAliasName) =
                  .ok (t.setEnv valueAliasName (Binding.mref id),
                    MVal.ref id) :=
                readM_alias _
                  (lookupBy_setBy_self valueAliasName (Binding.mref id)
                    t.env)
              show ResultsAgree aliasNames
                (execAssign t lhs
                  (WrappedExpr.index Kind.memory tyR path idxE))
                (execStmt (t.setEnv valueAliasName (Binding.mref id))
                  (Stmt.assign lhs (aliasExpr Kind.memory
                    (WrappedExpr.index Kind.memory tyR path idxE).ty
                    valueAliasName)))
              rw [execStmt]
              refine execAssign_pureLocSim hlhs hfl rfl rfl ?_ ?_ ?_
              · rw [hevL, hevR]
                exact rfl
              · intro h
                rcases h with hk | ⟨nm, hl⟩
                · exact nomatch hk
                · exact absurd hl (hnsl nm)
              · intro _
                rw [hcap, hrdR]
                exact ⟨rfl, ht'⟩

theorem memoryToStorageUnfoldRightFstSource_sound
    (s : State) (lhs : PlaceExpr) (rhs : WrappedExpr) {loc : Loc}
    (hcond : (ruleEffect .memoryToStorageUnfoldRightFstSource).cond
      (Stmt.assign lhs rhs))
    (hfresh : ∀ n ∈ aliasNames,
      stmtUsesVar (Stmt.assign lhs rhs) n = false)
    (hlhs : resolveLoc s lhs.expr = .ok (s, loc))
    (hplhs : pureExpr lhs.expr = true)
    (hnsl : ∀ nm, loc ≠ Loc.storageLocal nm)
    (hnmr : ∀ nm, loc ≠ Loc.memoryRoot nm)
    (hkm : rhs.kind = Kind.memory)
    (hprhs : pureExpr rhs = true)
    (hevalEq : ∀ u : State, evalValue u rhs =
      (readM u rhs) >>= fun x =>
        x.2.asValue >>= fun val => Except.ok (x.1, val))
    (hwf : rhs.ty.isPrimitive = false -> ∀ t mv,
      readM s rhs = .ok (t, mv) -> ∃ id, mv = MVal.ref id) :
    ResultsAgree aliasNames
      (execStmt s (Stmt.assign lhs rhs))
      (execBlock s
        ((ruleEffect .memoryToStorageUnfoldRightFstSource).block
          (Stmt.assign lhs rhs) hcond)) := by
  have hfl : ∀ n ∈ aliasNames, usesVar lhs.expr n = false := fun n hn => by
    have := hfresh n hn
    simp [stmtUsesVar] at this
    exact this.1
  have hmem : rhs.isMemory = true := by
    simp [Typed.WrappedExpr.isMemory, hkm]
  show ResultsAgree aliasNames
    (execStmt s (Stmt.assign lhs rhs))
    (execBlock s [captureValue rhs, Stmt.assign lhs (valueAlias rhs)])
  rw [execStmt, execBlock_pair]
  cases hprim : rhs.ty.isPrimitive with
  | true =>
      have hvck : valueCaptureKind rhs = Kind.stack := by
        rw [valueCaptureKind]
        simp [hprim, hmem]
      rw [captureValue, valueAlias, hvck, capture]
      cases hev : evalValue s rhs with
      | error err =>
          have hL : execAssign s lhs rhs = .error err :=
            execAssign_evalErr hlhs hprim hnsl hnmr hev
          have hR : execStmt s
              (Stmt.stackDecl rhs.ty valueAliasName (some rhs)) =
              .error err := by
            rw [execStmt, hev]
            rfl
          rw [hL, hR]
          exact rfl
      | ok x =>
          obtain ⟨t, v⟩ := x
          have hts : t = s := evalValue_pure hprhs hev
          subst hts
          have hR : execStmt t
              (Stmt.stackDecl rhs.ty valueAliasName (some rhs)) =
              .ok (t.setEnv valueAliasName (Binding.val v)) := by
            rw [execStmt, hev]
            rfl
          rw [hR]
          have ht' : EnvAgreeExcept aliasNames t
              (t.setEnv valueAliasName (Binding.val v)) :=
            (EnvAgreeExcept.refl _ t).setEnv_right pv_mem _
          show ResultsAgree aliasNames
            (execAssign t lhs rhs)
            (execStmt (t.setEnv valueAliasName (Binding.val v))
              (Stmt.assign lhs
                (aliasExpr Kind.stack rhs.ty valueAliasName)))
          rw [execStmt]
          refine execAssign_pureLocSimPrim hlhs hfl rfl hprim ?_
            hnsl hnmr
          rw [hev,
            evalValue_alias rhs.ty
              (lookupBy_setBy_self valueAliasName (Binding.val v) t.env)]
          exact ⟨rfl, ht'⟩
  | false =>
      have hvck : valueCaptureKind rhs = Kind.memory := by
        rw [valueCaptureKind]
        simp [hprim, hmem, hkm]
      rw [captureValue, valueAlias, hvck, capture]
      cases hcap : readM s rhs with
      | error err =>
          have hL : execAssign s lhs rhs = .error err :=
            execAssign_memoryRhsErr hlhs hkm hnsl hevalEq hcap
          have hR : execStmt s
              (Stmt.memoryDecl rhs.ty valueAliasName (some rhs)) =
              .error err := by
            rw [execStmt]
            rw [hkm, hcap]
            rfl
          rw [hL, hR]
          exact rfl
      | ok x =>
          obtain ⟨t, mv⟩ := x
          have hts : t = s := readM_pure hprhs hcap
          subst hts
          obtain ⟨id, hmv⟩ := hwf hprim t mv hcap
          subst hmv
          have hR : execStmt t
              (Stmt.memoryDecl rhs.ty valueAliasName (some rhs)) =
              .ok (t.setEnv valueAliasName (Binding.mref id)) := by
            rw [execStmt]
            rw [hkm, hcap]
            rfl
          rw [hR]
          have ht' : EnvAgreeExcept aliasNames t
              (t.setEnv valueAliasName (Binding.mref id)) :=
            (EnvAgreeExcept.refl _ t).setEnv_right pv_mem _
          have hevL : evalValue t rhs = .error .stuck := by
            rw [hevalEq t, hcap]
            rfl
          have hevR : evalValue (t.setEnv valueAliasName (Binding.mref id))
              (aliasExpr Kind.memory rhs.ty valueAliasName) =
              .error .stuck := by
            rw [aliasExpr, evalValue]
          have hrdR : readM (t.setEnv valueAliasName (Binding.mref id))
              (aliasExpr Kind.memory rhs.ty valueAliasName) =
              .ok (t.setEnv valueAliasName (Binding.mref id),
                MVal.ref id) :=
            readM_alias _
              (lookupBy_setBy_self valueAliasName (Binding.mref id) t.env)
          show ResultsAgree aliasNames
            (execAssign t lhs rhs)
            (execStmt (t.setEnv valueAliasName (Binding.mref id))
              (Stmt.assign lhs
                (aliasExpr Kind.memory rhs.ty valueAliasName)))
          rw [execStmt]
          refine execAssign_pureLocSim hlhs hfl rfl ?_ ?_ ?_ ?_
          · rw [hkm]
            rfl
          · rw [hevL, hevR]
            exact rfl
          · intro h
            rcases h with hk | ⟨nm, hl⟩
            · rw [hkm] at hk
              exact nomatch hk
            · exact absurd hl (hnsl nm)
          · intro _
            rw [hcap, hrdR]
            exact ⟨rfl, ht'⟩

/-- `memoryWriteUnfoldRightSndResult`, storage-kind right-hand side:
the capture is a storage-path alias, so the storage `pv`-capture
template applies. -/
theorem memoryWriteUnfoldRightSndResult_storage_sound
    (s : State) (lhs : PlaceExpr) (rhs : WrappedExpr) {loc : Loc}
    (hcond : (ruleEffect .memoryWriteUnfoldRightSndResult).cond
      (Stmt.assign lhs rhs))
    (hfresh : ∀ n ∈ aliasNames,
      stmtUsesVar (Stmt.assign lhs rhs) n = false)
    (hlhs : resolveLoc s lhs.expr = .ok (s, loc))
    (hplhs : pureExpr lhs.expr = true)
    (hkS : rhs.kind = Kind.storage)
    (hprhs : pureExpr rhs = true)
    (hnm : tyHasMapping rhs.ty = false)
    (hevalEq : ∀ u : State, evalValue u rhs =
      (resolveS u rhs) >>= fun x =>
        (x.1.findStorage x.2.1 x.2.2) >>= fun v =>
          v.asValue >>= fun val => Except.ok (x.1, val)) :
    ResultsAgree aliasNames
      (execStmt s (Stmt.assign lhs rhs))
      (execBlock s
        ((ruleEffect .memoryWriteUnfoldRightSndResult).block
          (Stmt.assign lhs rhs) hcond)) := by
  have hfl : ∀ n ∈ aliasNames, usesVar lhs.expr n = false := fun n hn => by
    have := hfresh n hn
    simp [stmtUsesVar] at this
    exact this.1
  have hmem : rhs.isMemory = false := by
    simp [Typed.WrappedExpr.isMemory, hkS]
  have hvck : valueCaptureKind rhs = Kind.storage := by
    rw [valueCaptureKind]
    simp [hmem, hkS]
  show ResultsAgree aliasNames
    (execStmt s (Stmt.assign lhs rhs))
    (execBlock s [captureValue rhs, Stmt.assign lhs (valueAlias rhs)])
  rw [captureValue, valueAlias, hvck, capture]
  exact captureAssignStorageRhs_sound s lhs rhs hlhs hplhs hfl hprhs hkS
    hnm hevalEq

/-- `memoryWriteUnfoldRightSndResult`, stack-kind right-hand side
(operators): the capture is a typed value temporary. -/
theorem memoryWriteUnfoldRightSndResult_stack_sound
    (s : State) (lhs : PlaceExpr) (rhs : WrappedExpr) {loc : Loc}
    (hcond : (ruleEffect .memoryWriteUnfoldRightSndResult).cond
      (Stmt.assign lhs rhs))
    (hfresh : ∀ n ∈ aliasNames,
      stmtUsesVar (Stmt.assign lhs rhs) n = false)
    (hlhs : resolveLoc s lhs.expr = .ok (s, loc))
    (hplhs : pureExpr lhs.expr = true)
    (hml : (∃ id fld, loc = Loc.memoryField id fld) ∨
      (∃ id i, loc = Loc.memoryIndex id i))
    (hkS : rhs.kind = Kind.stack)
    (hprhs : pureExpr rhs = true)
    (hprim : rhs.ty.isPrimitive = true) :
    ResultsAgree aliasNames
      (execStmt s (Stmt.assign lhs rhs))
      (execBlock s
        ((ruleEffect .memoryWriteUnfoldRightSndResult).block
          (Stmt.assign lhs rhs) hcond)) := by
  have hnsl : ∀ nm, loc ≠ Loc.storageLocal nm := fun nm h => by
    rcases hml with ⟨_, _, h2⟩ | ⟨_, _, h2⟩ <;> rw [h2] at h <;>
      exact nomatch h
  have hnmr : ∀ nm, loc ≠ Loc.memoryRoot nm := fun nm h => by
    rcases hml with ⟨_, _, h2⟩ | ⟨_, _, h2⟩ <;> rw [h2] at h <;>
      exact nomatch h
  have hnst : ∀ nm, loc ≠ Loc.stack nm := fun nm h => by
    rcases hml with ⟨_, _, h2⟩ | ⟨_, _, h2⟩ <;> rw [h2] at h <;>
      exact nomatch h
  have hnsg : ∀ root segs, loc ≠ Loc.storage root segs := fun r sg h => by
    rcases hml with ⟨_, _, h2⟩ | ⟨_, _, h2⟩ <;> rw [h2] at h <;>
      exact nomatch h
  have hfl : ∀ n ∈ aliasNames, usesVar lhs.expr n = false := fun n hn => by
    have := hfresh n hn
    simp [stmtUsesVar] at this
    exact this.1
  have hmem : rhs.isMemory = false := by
    simp [Typed.WrappedExpr.isMemory, hkS]
  have hvck : valueCaptureKind rhs = Kind.stack := by
    rw [valueCaptureKind]
    simp [hmem, hkS]
  show ResultsAgree aliasNames
    (execStmt s (Stmt.assign lhs rhs))
    (execBlock s [captureValue rhs, Stmt.assign lhs (valueAlias rhs)])
  rw [execStmt, execBlock_pair, captureValue, valueAlias, hvck, capture]
  cases hev : evalValue s rhs with
  | error err =>
      have hL : execAssign s lhs rhs = .error err :=
        execAssign_evalErr hlhs hprim hnsl hnmr hev
      have hR : execStmt s
          (Stmt.stackDecl rhs.ty valueAliasName (some rhs)) =
          .error err := by
        rw [execStmt, hev]
        rfl
      rw [hL, hR]
      exact rfl
  | ok x =>
      obtain ⟨t, v⟩ := x
      have hts : t = s := evalValue_pure hprhs hev
      subst hts
      have hR : execStmt t
          (Stmt.stackDecl rhs.ty valueAliasName (some rhs)) =
          .ok (t.setEnv valueAliasName (Binding.val v)) := by
        rw [execStmt, hev]
        rfl
      rw [hR]
      have ht' : EnvAgreeExcept aliasNames t
          (t.setEnv valueAliasName (Binding.val v)) :=
        (EnvAgreeExcept.refl _ t).setEnv_right pv_mem _
      show ResultsAgree aliasNames
        (execAssign t lhs rhs)
        (execStmt (t.setEnv valueAliasName (Binding.val v))
          (Stmt.assign lhs (aliasExpr Kind.stack rhs.ty valueAliasName)))
      rw [execStmt]
      refine execAssign_pureLocSimPrim hlhs hfl rfl hprim ?_ hnsl hnmr
      rw [hev,
        evalValue_alias rhs.ty
          (lookupBy_setBy_self valueAliasName (Binding.val v) t.env)]
      exact ⟨rfl, ht'⟩

/-- `storagePushValueUnfoldRightSndArgument` for arguments whose value
capture is a stack temporary (`valueCaptureKind rhs = Kind.stack`:
operators and primitive-typed memory reads). -/
theorem storagePushValueUnfoldRightSndArgument_stack_sound
    (s : State) (target : PlaceExpr) (value : Option WrappedExpr)
    (root : Name) (segs : List Seg) (elems : List SVal) (elemTy : Ty)
    (hcond : (ruleEffect .storagePushValueUnfoldRightSndArgument).cond
      (Stmt.push target value))
    (hfresh : ∀ n ∈ aliasNames,
      stmtUsesVar (Stmt.push target value) n = false)
    (hbase : resolveS s target.expr = .ok (s, root, segs))
    (harr : s.findStorage root segs = .ok (SVal.array elems))
    (htyE : target.expr.ty = Ty.ref (RefTy.array elemTy))
    (hvck : ∀ {rhs}, value = some rhs -> valueCaptureKind rhs = Kind.stack)
    (hprim : ∀ {rhs}, value = some rhs -> rhs.ty.isPrimitive = true)
    (hprhs : ∀ {rhs}, value = some rhs -> pureExpr rhs = true) :
    ResultsAgree aliasNames
      (execStmt s (Stmt.push target value))
      (execBlock s
        ((ruleEffect .storagePushValueUnfoldRightSndArgument).block
          (Stmt.push target value) hcond)) := by
  revert hvck hprim hprhs
  match value, hcond, hfresh with
  | some rhs, hcond, hfresh =>
      intro hvck hprim hprhs
      have hvckr : valueCaptureKind rhs = Kind.stack := hvck rfl
      have hprimr : rhs.ty.isPrimitive = true := hprim rfl
      have hpr : pureExpr rhs = true := hprhs rfl
      have hpt : pureExpr target.expr = true := pure_of_simple hcond.2.1
      have hft : ∀ n ∈ aliasNames, usesVar target.expr n = false :=
        fun n hn => by
          have := hfresh n hn
          simp [stmtUsesVar] at this
          exact this.1
      have hLeq : execStmt s (Stmt.push target (some rhs)) =
          (evalValue s rhs) >>= fun x =>
            ((Except.ok (x.1, x.2.toSVal) : Res (State × SVal)) >>= fun y =>
              y.1.saveStorage root segs
                (SVal.array (elems ++ [y.2]))) := by
        rw [execStmt, hbase]
        simp only [resOk_bind]
        rw [harr]
        simp only [resOk_bind]
        rw [htyE]
        simp only []
        rw [rhsToSVal, if_pos hprimr, resBind_assoc]
        rfl
      show ResultsAgree aliasNames
        (execStmt s (Stmt.push target (some rhs)))
        (execBlock s [captureValue rhs,
          Stmt.push target (some (valueAlias rhs))])
      rw [hLeq, execBlock_pair, captureValue, valueAlias, hvckr, capture]
      cases hev : evalValue s rhs with
      | error err =>
          have hR : execStmt s
              (Stmt.stackDecl rhs.ty valueAliasName (some rhs)) =
              .error err := by
            rw [execStmt, hev]
            rfl
          rw [hR]
          exact rfl
      | ok x =>
          obtain ⟨t, v⟩ := x
          have hts : t = s := evalValue_pure hpr hev
          subst hts
          have hR : execStmt t
              (Stmt.stackDecl rhs.ty valueAliasName (some rhs)) =
              .ok (t.setEnv valueAliasName (Binding.val v)) := by
            rw [execStmt, hev]
            rfl
          rw [hR]
          have ht' : EnvAgreeExcept aliasNames t
              (t.setEnv valueAliasName (Binding.val v)) :=
            (EnvAgreeExcept.refl _ t).setEnv_right pv_mem _
          have hbase' : resolveS
              (t.setEnv valueAliasName (Binding.val v)) target.expr =
              .ok (t.setEnv valueAliasName (Binding.val v), root, segs) :=
            resolveS_transport ht' hft hpt hbase
          have harr' : (t.setEnv valueAliasName
              (Binding.val v)).findStorage root segs =
              .ok (SVal.array elems) := by
            rw [← findStorage_congr ht']
            exact harr
          have hReq : execStmt (t.setEnv valueAliasName (Binding.val v))
              (Stmt.push target
                (some (aliasExpr Kind.stack rhs.ty valueAliasName))) =
              (evalValue (t.setEnv valueAliasName (Binding.val v))
                  (aliasExpr Kind.stack rhs.ty valueAliasName)) >>= fun x =>
                ((Except.ok (x.1, x.2.toSVal) : Res (State × SVal)) >>=
                  fun y => y.1.saveStorage root segs
                    (SVal.array (elems ++ [y.2]))) := by
            rw [execStmt, hbase']
            simp only [resOk_bind]
            rw [harr']
            simp only [resOk_bind]
            rw [htyE]
            simp only []
            have htyA : (aliasExpr Kind.stack rhs.ty
                valueAliasName).ty.isPrimitive = true := hprimr
            rw [rhsToSVal, if_pos htyA, resBind_assoc]
            rfl
          show ResultsAgree aliasNames _
            (execStmt (t.setEnv valueAliasName (Binding.val v))
              (Stmt.push target
                (some (aliasExpr Kind.stack rhs.ty valueAliasName))))
          rw [hReq,
            evalValue_alias rhs.ty
              (lookupBy_setBy_self valueAliasName (Binding.val v) t.env)]
          simp only [resOk_bind]
          exact saveStorage_agree ht' root segs
            (SVal.array (elems ++ [v.toSVal]))

theorem memoryDeleteComplexTarget_sound
    (s : State) (target : PlaceExpr) (mid : Nat)
    (hcond : (ruleEffect .memoryDeleteComplexTarget).cond
      (Stmt.delete target))
    (hfresh : ∀ n ∈ aliasNames,
      stmtUsesVar (Stmt.delete target) n = false)
    (hkp : ∀ {kind ty path fld},
      target.expr = WrappedExpr.field kind ty path fld ->
        path.kind = Kind.memory ∧ pureExpr path = true)
    (hkpi : ∀ {kind ty path index},
      target.expr = WrappedExpr.index kind ty path index ->
        path.complex = true ->
        path.kind = Kind.memory ∧ pureExpr path = true)
    (hbase : ∀ {kind ty path index},
      target.expr = WrappedExpr.index kind ty path index ->
        path.complex = false ->
        (pureExpr index = true ∧
          resolveMBase s path = .ok (s, mid))) :
    ResultsAgree aliasNames
      (execStmt s (Stmt.delete target))
      (execBlock s
        ((ruleEffect .memoryDeleteComplexTarget).block
          (Stmt.delete target) hcond)) := by
  obtain ⟨e, hass⟩ := target
  revert hkp hkpi hbase
  match e, hass, hcond, hfresh with
  | WrappedExpr.field Kind.memory ty path fld, hass, hcond, hfresh =>
      intro hkp _ _
      obtain ⟨hkpm, hpp⟩ := hkp rfl
      show ResultsAgree aliasNames
        (execStmt s (Stmt.delete (PlaceExpr.field Kind.memory ty path fld)))
        (execBlock s [Stmt.memoryDecl path.ty memoryPathAliasName (some path),
          Stmt.delete
            (fieldFromAlias Kind.memory memoryPathAliasName ty path fld)])
      have hLeq : execStmt s
          (Stmt.delete (PlaceExpr.field Kind.memory ty path fld)) =
          (resolveLoc s (WrappedExpr.field Kind.memory ty path fld)) >>=
            fun x =>
              match ty with
              | Ty.bool => writeMSlot x.1 x.2 (MVal.bool false)
              | Ty.uint => writeMSlot x.1 x.2 (MVal.int 0)
              | Ty.int => writeMSlot x.1 x.2 (MVal.int 0)
              | Ty.ref r =>
                  (allocDefault x.1 r) >>= fun y =>
                    writeMSlot y.1 x.2 (MVal.ref y.2) := by
        rw [execStmt]
        rfl
      have hReq : ∀ (u : State), execStmt u
          (Stmt.delete
            (fieldFromAlias Kind.memory memoryPathAliasName ty path fld)) =
          (resolveLoc u (WrappedExpr.field Kind.memory ty
            (aliasExpr Kind.memory path.ty memoryPathAliasName) fld)) >>=
            fun x =>
              match ty with
              | Ty.bool => writeMSlot x.1 x.2 (MVal.bool false)
              | Ty.uint => writeMSlot x.1 x.2 (MVal.int 0)
              | Ty.int => writeMSlot x.1 x.2 (MVal.int 0)
              | Ty.ref r =>
                  (allocDefault x.1 r) >>= fun y =>
                    writeMSlot y.1 x.2 (MVal.ref y.2) := fun u => by
        rw [execStmt]
        rfl
      rw [hLeq, execBlock_pair]
      have hRdecl : execStmt s
          (Stmt.memoryDecl path.ty memoryPathAliasName (some path)) =
          (readM s path) >>= fun x =>
            match x.2 with
            | MVal.ref id =>
                .ok (x.1.setEnv memoryPathAliasName (Binding.mref id))
            | MVal.prim _ => .error .stuck := by
        rw [execStmt]
        rw [hkpm]
        rfl
      cases hcap : readM s path with
      | error err =>
          rw [hRdecl, hcap, resolveLoc, resolveMBase_eq_readM, hcap]
          exact rfl
      | ok x =>
          obtain ⟨t, mv⟩ := x
          have hts : t = s := readM_pure hpp hcap
          subst hts
          cases mv with
          | prim p =>
              cases p <;>
                (rw [hRdecl, hcap, resolveLoc, resolveMBase_eq_readM, hcap]
                 exact rfl)
          | ref id =>
              rw [hRdecl, hcap]
              have ht' : EnvAgreeExcept aliasNames t
                  (t.setEnv memoryPathAliasName (Binding.mref id)) :=
                (EnvAgreeExcept.refl _ t).setEnv_right mp_mem _
              have hLloc : resolveLoc t
                  (WrappedExpr.field Kind.memory ty path fld) =
                  .ok (t, Loc.memoryField id fld.name) := by
                rw [resolveLoc, resolveMBase_eq_readM, hcap]
                rfl
              have hRloc : resolveLoc
                  (t.setEnv memoryPathAliasName (Binding.mref id))
                  (WrappedExpr.field Kind.memory ty
                    (aliasExpr Kind.memory path.ty memoryPathAliasName)
                    fld) =
                  .ok (t.setEnv memoryPathAliasName (Binding.mref id),
                    Loc.memoryField id fld.name) := by
                rw [resolveLoc,
                  resolveMBase_alias (s := t.setEnv memoryPathAliasName
                      (Binding.mref id)) path.ty
                    (lookupBy_setBy_self memoryPathAliasName
                      (Binding.mref id) t.env)]
                rfl
              show ResultsAgree aliasNames _
                (execStmt (t.setEnv memoryPathAliasName (Binding.mref id))
                  (Stmt.delete (fieldFromAlias Kind.memory
                    memoryPathAliasName ty path fld)))
              rw [hReq, hLloc, hRloc]
              simp only [resOk_bind]
              match hty : ty with
              | Ty.bool => exact writeMSlot_agree ht' _ (MVal.bool false)
              | Ty.uint => exact writeMSlot_agree ht' _ (MVal.int 0)
              | Ty.int => exact writeMSlot_agree ht' _ (MVal.int 0)
              | Ty.ref r =>
                  refine ResAgree.bindState (allocDefault_agree ht' r) ?_
                  intro w₁ w₂ id2 hw
                  exact writeMSlot_agree hw _ (MVal.ref id2)
  | WrappedExpr.index Kind.memory ty path idxE, hass, hcond, hfresh =>
      intro _ hkpi hbase
      have hfi : ∀ n ∈ aliasNames, usesVar idxE n = false := fun n hn => by
        have := hfresh n hn
        simp [stmtUsesVar, usesVar] at this
        exact this.2
      have hLeq : execStmt s
          (Stmt.delete (PlaceExpr.index Kind.memory ty path idxE)) =
          (resolveLoc s (WrappedExpr.index Kind.memory ty path idxE)) >>=
            fun x =>
              match ty with
              | Ty.bool => writeMSlot x.1 x.2 (MVal.bool false)
              | Ty.uint => writeMSlot x.1 x.2 (MVal.int 0)
              | Ty.int => writeMSlot x.1 x.2 (MVal.int 0)
              | Ty.ref r =>
                  (allocDefault x.1 r) >>= fun y =>
                    writeMSlot y.1 x.2 (MVal.ref y.2) := by
        rw [execStmt]
        rfl
      show ResultsAgree aliasNames
        (execStmt s (Stmt.delete (PlaceExpr.index Kind.memory ty path idxE)))
        (execBlock s (memoryDeleteComplexTargetBlock
          (WrappedExpr.index Kind.memory ty path idxE) hcond))
      cases hpc : path.complex with
      | true =>
          obtain ⟨hkpm, hpp⟩ := hkpi rfl hpc
          have hbl : memoryDeleteComplexTargetBlock
              (WrappedExpr.index Kind.memory ty path idxE) hcond =
              [Stmt.memoryDecl path.ty memoryPathAliasName (some path),
                Stmt.delete (indexFromAlias Kind.memory memoryPathAliasName
                  ty path idxE)] := by
            rw [memoryDeleteComplexTargetBlock]
            simp [hpc, captureMemoryPath, capture]
          rw [hbl, hLeq, execBlock_pair]
          have hRdecl : execStmt s
              (Stmt.memoryDecl path.ty memoryPathAliasName (some path)) =
              (readM s path) >>= fun x =>
                match x.2 with
                | MVal.ref id =>
                    .ok (x.1.setEnv memoryPathAliasName (Binding.mref id))
                | MVal.prim _ => .error .stuck := by
            rw [execStmt]
            rw [hkpm]
            rfl
          have hReq : ∀ (u : State), execStmt u
              (Stmt.delete (indexFromAlias Kind.memory memoryPathAliasName
                ty path idxE)) =
              (resolveLoc u (WrappedExpr.index Kind.memory ty
                (aliasExpr Kind.memory path.ty memoryPathAliasName)
                idxE)) >>= fun x =>
                match ty with
                | Ty.bool => writeMSlot x.1 x.2 (MVal.bool false)
                | Ty.uint => writeMSlot x.1 x.2 (MVal.int 0)
                | Ty.int => writeMSlot x.1 x.2 (MVal.int 0)
                | Ty.ref r =>
                    (allocDefault x.1 r) >>= fun y =>
                      writeMSlot y.1 x.2 (MVal.ref y.2) := fun u => by
            rw [execStmt]
            rfl
          cases hcap : readM s path with
          | error err =>
              rw [hRdecl, hcap, resolveLoc, resolveMBase_eq_readM, hcap]
              exact rfl
          | ok x =>
              obtain ⟨t, mv⟩ := x
              have hts : t = s := readM_pure hpp hcap
              subst hts
              cases mv with
              | prim p =>
                  cases p <;>
                    (rw [hRdecl, hcap, resolveLoc, resolveMBase_eq_readM,
                       hcap]
                     exact rfl)
              | ref id =>
                  rw [hRdecl, hcap]
                  have ht' : EnvAgreeExcept aliasNames t
                      (t.setEnv memoryPathAliasName (Binding.mref id)) :=
                    (EnvAgreeExcept.refl _ t).setEnv_right mp_mem _
                  have hlocSim : ResAgree aliasNames
                      (resolveLoc t
                        (WrappedExpr.index Kind.memory ty path idxE))
                      (resolveLoc
                        (t.setEnv memoryPathAliasName (Binding.mref id))
                        (WrappedExpr.index Kind.memory ty
                          (aliasExpr Kind.memory path.ty
                            memoryPathAliasName) idxE)) := by
                    rw [resolveLoc, resolveLoc, resolveMBase_eq_readM, hcap,
                      resolveMBase_alias (s := t.setEnv memoryPathAliasName
                          (Binding.mref id)) path.ty
                        (lookupBy_setBy_self memoryPathAliasName
                          (Binding.mref id) t.env)]
                    simp only [resOk_bind]
                    refine ResAgree.bind (evalInt_agree ht' idxE hfi) ?_
                    intro u₁ u₂ i hu
                    exact ⟨rfl, hu⟩
                  show ResultsAgree aliasNames _
                    (execStmt (t.setEnv memoryPathAliasName (Binding.mref id))
                      (Stmt.delete (indexFromAlias Kind.memory
                        memoryPathAliasName ty path idxE)))
                  rw [hReq]
                  refine ResAgree.bindState hlocSim ?_
                  intro u₁ u₂ loc2 hu
                  match hty : ty with
                  | Ty.bool => exact writeMSlot_agree hu _ (MVal.bool false)
                  | Ty.uint => exact writeMSlot_agree hu _ (MVal.int 0)
                  | Ty.int => exact writeMSlot_agree hu _ (MVal.int 0)
                  | Ty.ref r =>
                      refine ResAgree.bindState (allocDefault_agree hu r) ?_
                      intro w₁ w₂ id2 hw
                      exact writeMSlot_agree hw _ (MVal.ref id2)
      | false =>
          obtain ⟨hpi, hb⟩ := hbase rfl hpc
          have hps : path.simple = true := by
            rcases hcond with hc | hc
            · have hcc : path.complex = true := hc
              rw [hpc] at hcc
              exact nomatch hcc
            · exact hc.1
          have hpp : pureExpr path = true := pure_of_simple hps
          have hfp : ∀ n ∈ aliasNames, usesVar path n = false := fun n hn => by
            have := hfresh n hn
            simp [stmtUsesVar, usesVar] at this
            exact this.1
          have hbl : memoryDeleteComplexTargetBlock
              (WrappedExpr.index Kind.memory ty path idxE) hcond =
              [Stmt.stackDecl idxE.ty indexAliasName (some idxE),
                Stmt.delete (PlaceExpr.index Kind.memory ty path
                  (indexAlias idxE))] := by
            rw [memoryDeleteComplexTargetBlock]
            simp [hpc, captureIndex, capture]
          rw [hbl, hLeq, execBlock_pair]
          cases hev : evalValue s idxE with
          | error err =>
              have hL2 : (resolveLoc s
                  (WrappedExpr.index Kind.memory ty path idxE)) =
                  .error err := by
                rw [resolveLoc, hb]
                simp only [resOk_bind]
                rw [evalInt, hev]
                rfl
              have hR : execStmt s
                  (Stmt.stackDecl idxE.ty indexAliasName (some idxE)) =
                  .error err := by
                rw [execStmt, hev]
                rfl
              rw [hL2, hR]
              exact rfl
          | ok y =>
              obtain ⟨t, v⟩ := y
              have hts : t = s := evalValue_pure hpi hev
              subst hts
              have hR : execStmt t
                  (Stmt.stackDecl idxE.ty indexAliasName (some idxE)) =
                  .ok (t.setEnv indexAliasName (Binding.val v)) := by
                rw [execStmt, hev]
                rfl
              rw [hR]
              have ht' : EnvAgreeExcept aliasNames t
                  (t.setEnv indexAliasName (Binding.val v)) :=
                (EnvAgreeExcept.refl _ t).setEnv_right idx_mem _
              have hb' : resolveMBase
                  (t.setEnv indexAliasName (Binding.val v)) path =
                  .ok (t.setEnv indexAliasName (Binding.val v), mid) := by
                have h := resolveMBase_agree ht' path hfp
                rw [hb] at h
                rcases h.cases with ⟨err, h1, h2⟩ | ⟨u₁, u₂, a, h1, h2, hu⟩
                · exact nomatch h1
                · have ha : a = mid :=
                    (congrArg Prod.snd (Except.ok.inj h1)).symm
                  have hu2 : u₂ = t.setEnv indexAliasName (Binding.val v) :=
                    resolveMBase_pure hpp h2
                  rw [h2, hu2, ha]
              have hReq : ∀ (u : State), execStmt u
                  (Stmt.delete (PlaceExpr.index Kind.memory ty path
                    (indexAlias idxE))) =
                  (resolveLoc u (WrappedExpr.index Kind.memory ty path
                    (indexAlias idxE))) >>= fun x =>
                    match ty with
                    | Ty.bool => writeMSlot x.1 x.2 (MVal.bool false)
                    | Ty.uint => writeMSlot x.1 x.2 (MVal.int 0)
                    | Ty.int => writeMSlot x.1 x.2 (MVal.int 0)
                    | Ty.ref r =>
                        (allocDefault x.1 r) >>= fun y =>
                          writeMSlot y.1 x.2 (MVal.ref y.2) := fun u => by
                rw [execStmt]
                rfl
              have hlocSim : ResAgree aliasNames
                  (resolveLoc t (WrappedExpr.index Kind.memory ty path idxE))
                  (resolveLoc (t.setEnv indexAliasName (Binding.val v))
                    (WrappedExpr.index Kind.memory ty path
                      (indexAlias idxE))) := by
                rw [resolveLoc, resolveLoc, hb, hb']
                simp only [resOk_bind]
                rw [evalInt, evalInt, hev, indexAlias,
                  evalValue_alias idxE.ty
                    (lookupBy_setBy_self indexAliasName (Binding.val v)
                      t.env)]
                simp only [resOk_bind]
                cases v.asInt with
                | error err => exact rfl
                | ok i => exact ⟨rfl, ht'⟩
              show ResultsAgree aliasNames _
                (execStmt (t.setEnv indexAliasName (Binding.val v))
                  (Stmt.delete (PlaceExpr.index Kind.memory ty path
                    (indexAlias idxE))))
              rw [hReq]
              refine ResAgree.bindState hlocSim ?_
              intro u₁ u₂ loc2 hu
              match hty : ty with
              | Ty.bool => exact writeMSlot_agree hu _ (MVal.bool false)
              | Ty.uint => exact writeMSlot_agree hu _ (MVal.int 0)
              | Ty.int => exact writeMSlot_agree hu _ (MVal.int 0)
              | Ty.ref r =>
                  refine ResAgree.bindState (allocDefault_agree hu r) ?_
                  intro w₁ w₂ id2 hw
                  exact writeMSlot_agree hw _ (MVal.ref id2)

/-! ## `push`-lvalue assignment

`a.push() = e` extends the array with a default element and then
overwrites it; `a.push(e)` appends the value directly. The storage-tree
lemma below shows the two compositions coincide. -/

theorem setBy_setBy [DecidableEq κ] (k : κ) (a b : α)
    (l : List (κ × α)) : setBy k b (setBy k a l) = setBy k b l := by
  induction l with
  | nil => simp [setBy]
  | cons hd tl ih =>
      obtain ⟨k', v'⟩ := hd
      by_cases h : k = k'
      · simp [setBy, h]
      · simp [setBy, h, ih]

theorem list_set_append_last (elems : List α) (d v : α) :
    (elems ++ [d]).set elems.length v = elems ++ [v] := by
  induction elems with
  | nil => rfl
  | cons hd tl ih => simp [List.set, ih]

theorem list_set_set (elems : List α) (i : Nat) (a b : α) :
    (elems.set i a).set i b = elems.set i b := by
  induction elems generalizing i with
  | nil => rfl
  | cons hd tl ih =>
      cases i with
      | zero => rfl
      | succ n => simp [List.set, ih]

theorem list_get_set_self (elems : List α) (i : Nat) (a : α)
    (h : i < (elems.set i a).length) : (elems.set i a).get ⟨i, h⟩ = a := by
  induction elems generalizing i with
  | nil => simp [List.set] at h
  | cons hd tl ih =>
      cases i with
      | zero => rfl
      | succ n => exact ih n (by simpa using h)

/-- Extending an array with a default and then saving into the new slot
is the same as appending the value directly. -/
theorem save_extend_then_set (sv : SVal) (segs : List Seg)
    (elems : List SVal) (d v : SVal) :
    ((sv.save segs (SVal.array (elems ++ [d]))) >>= fun sv' =>
      sv'.save (segs ++ [Seg.at (elems.length : Int)]) v) =
    sv.save segs (SVal.array (elems ++ [v])) := by
  induction segs generalizing sv with
  | nil =>
      have hnil : ∀ x y : SVal, SVal.save x [] y = .ok y := by
        intro x y; simp [SVal.save]
      simp only [List.nil_append]
      rw [hnil, hnil]
      show (SVal.array (elems ++ [d])).save [Seg.at (elems.length : Int)] v =
        Except.ok (SVal.array (elems ++ [v]))
      rw [SVal.save]
      have hb : 0 ≤ (elems.length : Int) ∧
          (elems.length : Int).toNat < (elems ++ [d]).length := by
        constructor
        · exact Int.ofNat_nonneg _
        · simp
      rw [dif_pos hb]
      have hget : (elems ++ [d]).get
          ⟨(elems.length : Int).toNat, hb.2⟩ = d := by
        have : (elems.length : Int).toNat = elems.length := by simp
        simp [List.get_eq_getElem, this]
      rw [hget, hnil]
      show Except.ok (SVal.array ((elems ++ [d]).set
        (elems.length : Int).toNat v)) = _
      have : (elems.length : Int).toNat = elems.length := by simp
      rw [this, list_set_append_last]
  | cons seg rest ih =>
      cases sv with
      | prim p =>
          cases p <;> (rw [SVal.save.eq_def]; cases seg <;> rfl)
      | struct fields =>
          cases seg with
          | field name =>
              rw [SVal.save, SVal.save]
              cases hlk : lookupBy name fields with
              | none => rfl
              | some old =>
                  simp only []
                  rw [← ih old]
                  cases hs1 : old.save rest (SVal.array (elems ++ [d])) with
                  | error err => rfl
                  | ok mid =>
                      show (SVal.struct (setBy name mid fields)).save
                          (Seg.field name ::
                            (rest ++ [Seg.at (elems.length : Int)])) v = _
                      rw [SVal.save]
                      simp only [lookupBy_setBy_self]
                      simp only [resOk_bind]
                      cases hs2 : mid.save
                          (rest ++ [Seg.at (elems.length : Int)]) v with
                      | error err => rfl
                      | ok fin =>
                          show Except.ok (SVal.struct (setBy name fin
                            (setBy name mid fields))) = _
                          rw [setBy_setBy]
                          rfl
          | «at» i => rw [SVal.save.eq_def]; rfl
      | array arr =>
          cases seg with
          | field name => rw [SVal.save.eq_def]; rfl
          | «at» i =>
              rw [SVal.save, SVal.save]
              by_cases hb : 0 ≤ i ∧ i.toNat < arr.length
              · rw [dif_pos hb, dif_pos hb]
                rw [← ih (arr.get ⟨i.toNat, hb.2⟩)]
                cases hs1 : (arr.get ⟨i.toNat, hb.2⟩).save rest
                    (SVal.array (elems ++ [d])) with
                | error err => rfl
                | ok mid =>
                    show (SVal.array (arr.set i.toNat mid)).save
                        (Seg.at i ::
                          (rest ++ [Seg.at (elems.length : Int)])) v = _
                    rw [SVal.save]
                    have hb2 : 0 ≤ i ∧ i.toNat < (arr.set i.toNat
                        mid).length := by
                      simpa using hb
                    rw [dif_pos hb2]
                    have hget2 : (arr.set i.toNat mid).get
                        ⟨i.toNat, hb2.2⟩ = mid :=
                      list_get_set_self arr i.toNat mid hb2.2
                    rw [hget2]
                    simp only [resOk_bind]
                    cases hs2 : mid.save
                        (rest ++ [Seg.at (elems.length : Int)]) v with
                    | error err => rfl
                    | ok fin =>
                        show Except.ok (SVal.array ((arr.set i.toNat
                          mid).set i.toNat fin)) = _
                        rw [list_set_set]
                        rfl
              · rw [dif_neg hb, dif_neg hb]
                rfl
      | map entries dflt =>
          cases seg with
          | field name => rw [SVal.save.eq_def]; rfl
          | «at» i =>
              rw [SVal.save, SVal.save]
              cases hlk : lookupBy i entries with
              | none =>
                  simp only []
                  rw [← ih dflt]
                  cases hs1 : dflt.save rest (SVal.array (elems ++ [d])) with
                  | error err => rfl
                  | ok mid =>
                      show (SVal.map (setBy i mid entries) dflt).save
                          (Seg.at i ::
                            (rest ++ [Seg.at (elems.length : Int)])) v = _
                      rw [SVal.save]
                      simp only [lookupBy_setBy_self]
                      simp only [resOk_bind]
                      cases hs2 : mid.save
                          (rest ++ [Seg.at (elems.length : Int)]) v with
                      | error err => rfl
                      | ok fin =>
                          show Except.ok (SVal.map (setBy i fin
                            (setBy i mid entries)) dflt) = _
                          rw [setBy_setBy]
                          rfl
              | some old =>
                  simp only []
                  rw [← ih old]
                  cases hs1 : old.save rest (SVal.array (elems ++ [d])) with
                  | error err => rfl
                  | ok mid =>
                      show (SVal.map (setBy i mid entries) dflt).save
                          (Seg.at i ::
                            (rest ++ [Seg.at (elems.length : Int)])) v = _
                      rw [SVal.save]
                      simp only [lookupBy_setBy_self]
                      simp only [resOk_bind]
                      cases hs2 : mid.save
                          (rest ++ [Seg.at (elems.length : Int)]) v with
                      | error err => rfl
                      | ok fin =>
                          show Except.ok (SVal.map (setBy i fin
                            (setBy i mid entries)) dflt) = _
                          rw [setBy_setBy]
                          rfl

/-- State-level composition: extending an array and then writing the
new slot equals appending the value. -/
theorem stateSave_extend_then_set (t : State) (root : Name)
    (segs : List Seg) (elems : List SVal) (d w : SVal) :
    ((t.saveStorage root segs (SVal.array (elems ++ [d]))) >>= fun t' =>
      t'.saveStorage root (segs ++ [Seg.at (elems.length : Int)]) w) =
    t.saveStorage root segs (SVal.array (elems ++ [w])) := by
  unfold State.saveStorage
  cases hlk : lookupBy root t.storage with
  | none => rfl
  | some sv =>
      simp only []
      rw [← save_extend_then_set sv segs elems d w]
      cases hs1 : sv.save segs (SVal.array (elems ++ [d])) with
      | error err => rfl
      | ok mid =>
          simp only [resOk_bind, lookupBy_setBy_self]
          cases hs2 : mid.save (segs ++ [Seg.at (elems.length : Int)])
              w with
          | error err => rfl
          | ok fin =>
              simp only [setBy_setBy]

theorem storagePushLhsToPushValue_sound
    (s : State) (lhs : PlaceExpr) (rhs : WrappedExpr) (v : Value)
    (hcond : (ruleEffect .storagePushLhsToPushValue).cond
      (Stmt.assign lhs rhs))
    (hpt : ∀ {tgt}, lhs.expr = WrappedExpr.pushPlace tgt ->
      pureExpr tgt = true)
    (hprim : rhs.ty.isPrimitive = true)
    (hev : evalValue s rhs = .ok (s, v)) :
    ResultsAgree aliasNames
      (execStmt s (Stmt.assign lhs rhs))
      (execBlock s
        ((ruleEffect .storagePushLhsToPushValue).block
          (Stmt.assign lhs rhs) hcond)) := by
  obtain ⟨e, hass⟩ := lhs
  revert hpt
  match e, hass, hcond with
  | WrappedExpr.pushPlace tgt, hass, hcond =>
      intro hpt
      have hptx : pureExpr tgt = true := hpt rfl
      have hasgn : tgt.assignable = true := hass
      show ResultsAgree aliasNames
        (execStmt s (Stmt.assign ⟨WrappedExpr.pushPlace tgt, hass⟩ rhs))
        (execBlock s [Stmt.push ⟨tgt, hasgn⟩ (some rhs)])
      rw [execStmt, execBlock_single, execStmt]
      have hrs : rhsToSVal s rhs = .ok (s, v.toSVal) := by
        rw [rhsToSVal, if_pos hprim, hev]
        rfl
      -- The assignment reads the right-hand side first (solc order), so
      -- with the pure `hev` capture it collapses to: resolve the push
      -- place (extending the array), then store the value at the new
      -- slot.
      have hL0 : execAssign s ⟨WrappedExpr.pushPlace tgt, hass⟩ rhs =
          (resolveLoc s (WrappedExpr.pushPlace tgt)) >>= fun y =>
            match y.2 with
            | Loc.storage root segs => y.1.saveStorage root segs v.toSVal
            | Loc.stack _ => .error .stuck
            | Loc.storageLocal _ => .error .stuck
            | Loc.memoryRoot _ => .error .stuck
            | Loc.memoryField _ _ => .error .stuck
            | Loc.memoryIndex _ _ => .error .stuck := by
        show execAssignNested s (WrappedExpr.pushPlace tgt) rhs = _
        rw [execAssignNested,
          show (WrappedExpr.pushPlace tgt).kind = Kind.storage from rfl,
          hrs]
        rfl
      rw [hL0, resolveLoc, resBind_assoc, resolveS]
      cases hres : resolveS s tgt with
      | error err => exact rfl
      | ok x =>
          obtain ⟨t, root, segs⟩ := x
          have hts : t = s := resolveS_pure hptx hres
          subst hts
          simp only [resOk_bind]
          cases harr : t.findStorage root segs with
          | error err => exact rfl
          | ok arr =>
              simp only [resOk_bind]
              cases arr with
              | prim p => cases p <;> exact rfl
              | struct fields => exact rfl
              | map entries dflt => exact rfl
              | array elems =>
                  match hty : tgt.ty with
                  | Ty.bool => exact rfl
                  | Ty.uint => exact rfl
                  | Ty.int => exact rfl
                  | Ty.ref (RefTy.struct nm) => exact rfl
                  | Ty.ref (RefTy.mapping k vv) => exact rfl
                  | Ty.ref (RefTy.array elemTy) =>
                      simp only []
                      have hrs' : rhsToSVal t rhs = .ok (t, v.toSVal) := by
                        rw [rhsToSVal, if_pos hprim, hev]
                        rfl
                      rw [hrs']
                      simp only [resOk_bind]
                      rw [resBind_assoc]
                      simp only [resOk_bind]
                      rw [stateSave_extend_then_set t root segs elems
                        (defaultForTy elemTy) v.toSVal]
                      exact ResultsAgree.refl _ _

/-! ## Coverage rules: `exprStmtCapture`, `pushAssignLower`,
`pushFieldAssignLower`

The three Lean-only coverage rules (Rules.lean, `RuleName` docstring).
All three are unconditional: the residual performs the very evaluation
the original performs, differing only in the scratch `pv` binding
(`exprStmtCapture`) or not at all (the two lowerings, whose residual is
literally the `Stmt.assign` form `execStmt` delegates to). -/

/-- `e;` ⟶ `pv = e;`: same evaluation, same aborts, same effects; the
final states differ only at the scratch name. -/
theorem exprStmtCapture_sound (s : State) (e : WrappedExpr)
    (hcond : (ruleEffect .exprStmtCapture).cond (Stmt.expr e)) :
    ResultsAgree aliasNames
      (execStmt s (Stmt.expr e))
      (execBlock s ((ruleEffect .exprStmtCapture).block
        (Stmt.expr e) hcond)) := by
  show ResultsAgree aliasNames
    (execStmt s (Stmt.expr e)) (execBlock s [captureStackValue e])
  rw [execBlock_single, captureStackValue, capture, execStmt, execStmt]
  cases hev : evalValue s e with
  | error err => exact rfl
  | ok p =>
      obtain ⟨t, v⟩ := p
      simp only [resOk_bind]
      exact EnvAgreeExcept.setEnv_right (EnvAgreeExcept.refl _ _)
        (by simp [aliasNames]) _

/-- `arr.push() = v;` (sugar) ⟶ `assign (pushPlace arr) v`: definitionally
the same interpreter call. -/
theorem pushAssignLower_sound (s : State) (target : PlaceExpr) (value : WrappedExpr)
    (hcond : (ruleEffect .pushAssignLower).cond
      (Stmt.pushAssign target value)) :
    ResultsAgree aliasNames
      (execStmt s (Stmt.pushAssign target value))
      (execBlock s ((ruleEffect .pushAssignLower).block
        (Stmt.pushAssign target value) hcond)) := by
  show ResultsAgree aliasNames
    (execStmt s (Stmt.pushAssign target value))
    (execBlock s [Stmt.assign (PlaceExpr.pushPlace target) value])
  rw [execBlock_single]
  exact ResultsAgree.refl _ _

/-- `arr.push().f = v;` (sugar) ⟶ the field assignment through the push
place: definitionally the same interpreter call. -/
theorem pushFieldAssignLower_sound (s : State) (target : PlaceExpr)
    (fld : Field) (value : WrappedExpr)
    (hcond : (ruleEffect .pushFieldAssignLower).cond
      (Stmt.pushFieldAssign target fld value)) :
    ResultsAgree aliasNames
      (execStmt s (Stmt.pushFieldAssign target fld value))
      (execBlock s ((ruleEffect .pushFieldAssignLower).block
        (Stmt.pushFieldAssign target fld value) hcond)) := by
  show ResultsAgree aliasNames
    (execStmt s (Stmt.pushFieldAssign target fld value))
    (execBlock s
      [Stmt.assign
        (PlaceExpr.field Kind.storage fld.ty (WrappedExpr.pushPlace target) fld)
        value])
  rw [execBlock_single]
  exact ResultsAgree.refl _ _

/-! ## Call rules, relative to inlining

`execStmt` is stuck on a `callStmt` by design (calls are given meaning by
`SolidityJudgment.checkInlined`, i.e. by `inlineBlock`), so the two call
rules cannot agree with `execStmt` on the un-inlined statement — no
`ResultsAgree (execStmt s (callStmt …)) …` theorem is true.  Their honest
soundness statement is relative to the inlined reading: the original and
the residual *inline to blocks that agree*. -/

/-- `functionBodyExpand` is sound relative to inlining: inlining the call
with fuel `d + 1` is exactly inlining the rule's residual (the expanded
body) with fuel `d`. -/
theorem functionBodyExpand_sound_inlined (d : Nat) (s : State)
    (res : Option PlaceExpr) (fn : Name) (args : List WrappedExpr)
    (hcond : (ruleEffect .functionBodyExpand).cond
      (Stmt.callStmt res fn args)) :
    ResultsAgree aliasNames
      (execBlock s (SoliditySyntax.inlineBlock (d + 1)
        [Stmt.callStmt res fn args]))
      (execBlock s (SoliditySyntax.inlineBlock d
        ((ruleEffect .functionBodyExpand).block
          (Stmt.callStmt res fn args) hcond))) := by
  have hc : args.all (·.simple) = true ∧
      (SoliditySyntax.expandCall res fn args).isSome = true := hcond
  obtain ⟨blk, hblk⟩ := Option.isSome_iff_exists.mp hc.2
  show ResultsAgree aliasNames _
    (execBlock s (SoliditySyntax.inlineBlock d
      ((SoliditySyntax.expandCall res fn args).getD [])))
  rw [hblk, Option.getD_some, SoliditySyntax.inlineBlock_cons,
    SoliditySyntax.inlineBlock_nil, List.append_nil,
    SoliditySyntax.inlineStmt_callStmt d res fn args blk hblk]
  exact ResultsAgree.refl _ _

/-- `functionCallArgCapture`, relative to inlining, **open**.

The residual hoists the leftmost complex argument `c` into `pv` ahead of
the (simple) arguments before it and ahead of the callee's parameter
declarations.  Agreement therefore needs, beyond alias freshness for the
statement: `c` pure (an impure `c` — `f(i, i++)` — is evaluated before
the earlier simple argument `i` in the residual but after it in the
inlined original, so the rule is unsound on that program, exactly as the
`*WriteUnfoldLeft*` family on `a[i++].x = i`); the callee body, result
place and remaining arguments free of the scratch name (the inlined
body runs after the capture and must not read `pv`); and `c` free of the
callee's parameter names (the residual evaluates `c` before the
parameter declarations shadow them).  With those hypotheses the proof is
a congruence argument through `paramDecls` using `evalValue_agree`
and `execBlock_agree`, plus an `inlineBlock_append` lemma that does not
exist yet.  Left as `sorry` rather than weakened. -/
theorem functionCallArgCapture_sound_inlined (d : Nat) (s : State)
    (res : Option PlaceExpr) (fn : Name) (args : List WrappedExpr)
    (c : WrappedExpr) (args' : List WrappedExpr)
    (hcond : (ruleEffect .functionCallArgCapture).cond
      (Stmt.callStmt res fn args))
    (hcap : captureFirstComplexArg args = some (c, args'))
    (hfresh : ∀ n ∈ aliasNames,
      stmtUsesVar (Stmt.callStmt res fn args) n = false)
    (hpure : pureExpr c = true)
    (hcallee : ∀ dfn, SoliditySyntax.funDef fn = some dfn ->
      (∀ n ∈ aliasNames, blockUsesVar dfn.body n = false) ∧
        ∀ p ∈ dfn.params, usesVar c p.2 = false) :
    ResultsAgree aliasNames
      (execBlock s (SoliditySyntax.inlineBlock (d + 1)
        [Stmt.callStmt res fn args]))
      (execBlock s (SoliditySyntax.inlineBlock (d + 1)
        ((ruleEffect .functionCallArgCapture).block
          (Stmt.callStmt res fn args) hcond))) := by
  sorry

/-! ## Full-coverage statements for the two split rules -/

/-- `storagePushValueUnfoldRightSndArgument`, all argument shapes,
**open beyond the stack case**.  The rule's condition admits any complex
argument; `storagePushValueUnfoldRightSndArgument_stack_sound` proves the
arguments whose capture is a stack temporary (operators, primitive-typed
memory reads).  The remaining shapes — a storage-typed argument
(`arr.push(s.inner)`, captured as a storage-path alias) and a memory
identity argument (captured as a memory alias) — need the storage- and
memory-alias read-back kits threaded through the array extension, which
is not done.  Stated here at full generality with the same hypotheses as
the stack case minus the capture-kind restriction; `sorry` rather than a
narrower claim under the rule's name. -/
theorem storagePushValueUnfoldRightSndArgument_sound
    (s : State) (target : PlaceExpr) (value : Option WrappedExpr)
    (root : Name) (segs : List Seg) (elems : List SVal) (elemTy : Ty)
    (hcond : (ruleEffect .storagePushValueUnfoldRightSndArgument).cond
      (Stmt.push target value))
    (hfresh : ∀ n ∈ aliasNames,
      stmtUsesVar (Stmt.push target value) n = false)
    (hbase : resolveS s target.expr = .ok (s, root, segs))
    (harr : s.findStorage root segs = .ok (SVal.array elems))
    (htyE : target.expr.ty = Ty.ref (RefTy.array elemTy))
    (hprhs : ∀ {rhs}, value = some rhs -> pureExpr rhs = true) :
    ResultsAgree aliasNames
      (execStmt s (Stmt.push target value))
      (execBlock s
        ((ruleEffect .storagePushValueUnfoldRightSndArgument).block
          (Stmt.push target value) hcond)) := by
  by_cases hstack : ∀ {rhs}, value = some rhs ->
      valueCaptureKind rhs = Kind.stack ∧ rhs.ty.isPrimitive = true
  · exact storagePushValueUnfoldRightSndArgument_stack_sound s target value
      root segs elems elemTy hcond hfresh hbase harr htyE
      (fun h => (hstack h).1) (fun h => (hstack h).2) hprhs
  · sorry

/-- `memoryWriteUnfoldRightSndResult`, all right-hand-side kinds.  The
storage and stack kinds dispatch to the two proved lemmas above (each
with the side conditions that kind needs).  The rule's condition also
admits a *memory*-kind complex right-hand side that is not a memory
field/index read (a memory-typed call or ternary), whose capture is a
memory alias declaration; that case is **open** — `sorry` rather than a
statement restricted to two of the three kinds under the rule's name. -/
theorem memoryWriteUnfoldRightSndResult_sound
    (s : State) (lhs : PlaceExpr) (rhs : WrappedExpr) {loc : Loc}
    (hcond : (ruleEffect .memoryWriteUnfoldRightSndResult).cond
      (Stmt.assign lhs rhs))
    (hfresh : ∀ n ∈ aliasNames,
      stmtUsesVar (Stmt.assign lhs rhs) n = false)
    (hlhs : resolveLoc s lhs.expr = .ok (s, loc))
    (hplhs : pureExpr lhs.expr = true)
    (hprhs : pureExpr rhs = true)
    (hS : rhs.kind = Kind.storage ->
      tyHasMapping rhs.ty = false ∧
        ∀ u : State, evalValue u rhs =
          (resolveS u rhs) >>= fun x =>
            (x.1.findStorage x.2.1 x.2.2) >>= fun v =>
              v.asValue >>= fun val => Except.ok (x.1, val))
    (hK : rhs.kind = Kind.stack ->
      ((∃ id fld, loc = Loc.memoryField id fld) ∨
        (∃ id i, loc = Loc.memoryIndex id i)) ∧
        rhs.ty.isPrimitive = true) :
    ResultsAgree aliasNames
      (execStmt s (Stmt.assign lhs rhs))
      (execBlock s
        ((ruleEffect .memoryWriteUnfoldRightSndResult).block
          (Stmt.assign lhs rhs) hcond)) := by
  cases hk : rhs.kind with
  | storage =>
      exact memoryWriteUnfoldRightSndResult_storage_sound s lhs rhs hcond
        hfresh hlhs hplhs hk hprhs (hS hk).1 (hS hk).2
  | stack =>
      exact memoryWriteUnfoldRightSndResult_stack_sound s lhs rhs hcond
        hfresh hlhs hplhs (hK hk).1 hk hprhs (hK hk).2
  | memory =>
      sorry

end RuleSoundness

end Solidity
