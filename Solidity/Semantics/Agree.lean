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
  tx : s₁.tx = s₂.tx

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

namespace EnvAgreeExcept

theorem refl (ns : List Var) (s : State) : EnvAgreeExcept ns s s :=
  ⟨rfl, rfl, rfl, rfl, fun _ _ => rfl, rfl, rfl⟩

end EnvAgreeExcept

/-- Agreeing states have one environment: `msg.sender` reads alike. -/
theorem State.envVal_congr {ns : List Var} {s₁ s₂ : State} (h : EnvAgreeExcept ns s₁ s₂)
    (k : EnvKey) : s₁.envVal k = s₂.envVal k := by
  cases k <;> simp [State.envVal, h.tx, h.selfBalance]

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

/-- Inserting a scratch binding moves a state within its
`EnvAgreeExcept` class. -/
theorem EnvAgreeExcept.setEnv_right {ns : List Var} {s₁ s₂ : State}
    (h : EnvAgreeExcept ns s₁ s₂) {n : Var} (hn : n ∈ ns) (b : Binding) :
    EnvAgreeExcept ns s₁ (s₂.setEnv n b) :=
  ⟨h.storage, h.heap, h.nextId, h.net, fun m hm => by
    have hne : m ≠ n := fun heq => hm (heq ▸ hn)
    simpa [State.setEnv, lookupBy_setBy_ne hne] using h.env m hm,
    h.selfBalance, h.tx⟩

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
    h.selfBalance, h.tx⟩

/-! ## Relational lemmas for the storage primitives -/

theorem findStorage_congr {ns : List Var} {s₁ s₂ : State}
    (h : EnvAgreeExcept ns s₁ s₂) (root : Name) (segs : List Seg) :
    s₁.findStorage root segs = s₂.findStorage root segs := by
  unfold State.findStorage
  rw [h.storage]

/-- A bounds check reads the storage only. -/
theorem checkIndex_congr {ns : List Var} {s₁ s₂ : State}
    (h : EnvAgreeExcept ns s₁ s₂) (root : Name) (segs : List Seg) (i : Int) :
    s₁.checkIndex root segs i = s₂.checkIndex root segs i := by
  unfold State.checkIndex
  rw [findStorage_congr h]

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
        h.selfBalance, h.tx⟩
  unfold State.saveStorage
  rw [h.storage]
  cases lookupBy root s₂.storage with
  | none => exact rfl
  | some v => exact hsave (v.save segs new)


/-- A copy writes over what is there: it agrees as the write does. -/
theorem writeStorage_agree {ns : List Var} {s₁ s₂ : State}
    (h : EnvAgreeExcept ns s₁ s₂) (root : Name) (segs : List Seg) (new : SVal) :
    ResultsAgree ns (s₁.writeStorage root segs new) (s₂.writeStorage root segs new) := by
  unfold State.writeStorage
  split
  · exact saveStorage_agree h _ _ _
  all_goals
    rw [findStorage_congr h]
    cases s₂.findStorage root segs with
    | error e => exact rfl
    | ok cur => exact saveStorage_agree h _ _ _

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
    h.selfBalance, h.tx⟩

theorem getNet_congr {ns : List Var} {s₁ s₂ : State}
    (h : EnvAgreeExcept ns s₁ s₂) (addr : Int) :
    s₁.getNet addr = s₂.getNet addr := by
  unfold State.getNet
  rw [h.net]

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
        by simp [ht.nextId], ht.net, ht.env, ht.selfBalance, ht.tx⟩
  | .array elems _ _ =>
      rw [copyStToM, copyStToM]
      refine ResAgree.bind (copyStElems_agree h elems) ?_
      intro t₁ t₂ melems ht
      exact ⟨by simp [ht.nextId],
        ht.storage, by simp [ht.heap, ht.nextId],
        by simp [ht.nextId], ht.net, ht.env, ht.selfBalance, ht.tx⟩
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

/-! ## What a program mentions

The variables a piece of syntax mentions, declared ones included: a rule's
fresh names are fresh when the statement avoids them (`Avoids`). -/

namespace Solidity

open Semantics

variable {C : Contract}

/-- `vs` avoids `ns`: no variable of `vs` is among `ns`.  `alice.age = x;`
avoids `[se1, sp1]`. -/
def Avoids (vs ns : List Var) : Prop := ∀ x ∈ vs, x ∉ ns

theorem Avoids.left {vs ws ns : List Var} (h : Avoids (vs ++ ws) ns) : Avoids vs ns :=
  fun x hx => h x (List.mem_append_left _ hx)

theorem Avoids.right {vs ws ns : List Var} (h : Avoids (vs ++ ws) ns) : Avoids ws ns :=
  fun x hx => h x (List.mem_append_right _ hx)

theorem Avoids.tail {x : Var} {vs ns : List Var} (h : Avoids (x :: vs) ns) : Avoids vs ns :=
  fun y hy => h y (List.mem_cons_of_mem _ hy)

theorem Avoids.head {x : Var} {vs ns : List Var} (h : Avoids (x :: vs) ns) : x ∉ ns :=
  h x List.mem_cons_self

def Src.vars {T : Ty} : Src C T → List Var
  | .val v => v.vars
  | .copy p _ => p.vars

def ARhs.vars {R : RefTy} : ARhs C R → List Var
  | .path p => p.vars
  | .push b _ => b.vars

def MRhs.vars {R : RefTy} : MRhs C R → List Var
  | .alias p => p.vars
  | .copy p _ => p.vars
  | .newArr n _ => n.vars

def NewLhs.vars {R : RefTy} : NewLhs C R → List Var
  | .store l => l.vars
  | .mem l => l.vars

def MSrc.vars {T : Ty} : MSrc C T → List Var
  | .val v => v.vars
  | .ref p => p.vars

def OpLoc.vars {p : PrimTy} : OpLoc C p → List Var
  | .local x => [x]
  | .root .. => []
  | .field b _ _ => b.vars
  | .index _ b i => b.vars ++ i.vars
  | .mfield b _ _ => b.vars
  | .mindex _ b i => b.vars ++ i.vars

/-- The variables of an optional part. -/
def optVars {α : Type} (f : α → List Var) : Option α → List Var
  | none => []
  | some a => f a

/-- The variables of a call's arguments: each parameter and what its
argument reads. -/
def Arg.vars : List (Arg C) → List Var
  | [] => []
  | a :: as => a.x :: a.e.vars ++ Arg.vars as

/-- The variables an external call reads. -/
def ExtCall.vars (c : ExtCall C) : List Var :=
  c.addr.vars ++ c.args.flatMap fun a => a.2.vars

/-- The return variable of a call, and the local it lands in. -/
def CallRet.vars : CallRet → List Var
  | .none => []
  | .val _ r res => r :: res.toList
  | .rets rs => rs.map (·.2)

/-- The variables a loop's annotation reads. -/
def LoopAnn.vars : LoopAnn C → List Var
  | .unwind _ => []
  | .inv I dec => I.vars ++ optVars Val.vars dec

mutual

/-- The variables a statement mentions: `uint x = y + 1;` mentions `x` and
`y`. -/
def Stmt.vars : Stmt C → List Var
  | .assign l r => l.vars ++ r.vars
  | .rebind x r => x :: r.vars
  | .assignLocal x r => x :: r.vars
  | .declLocal _ x init => x :: optVars Val.vars init
  | .declStorage _ x init => x :: optVars ARhs.vars init
  | .opAssign _ _ _ l r => l.vars ++ r.vars
  | .incDec _ _ l => l.vars
  | .assignIncDec x _ _ l _ => x :: l.vars
  | .push b v _ => b.vars ++ optVars Src.vars v
  | .pop b => b.vars
  | .transfer r a => r.vars ++ a.vars
  | .send pv r a => pv :: (r.vars ++ a.vars)
  | .declMem _ x init _ => x :: optVars MRhs.vars init
  | .rebindMem x r => x :: r.vars
  | .assignFromMem l p => l.vars ++ p.vars
  | .assignMem l r => l.vars ++ r.vars
  | .delete l => l.vars
  | .deleteMem p _ => p.vars
  | .assignNew l n _ => l.vars ++ n.vars
  | .ite c thn els => c.vars ++ Prog.vars thn ++ Prog.vars els
  | .require c => c.vars
  | .assert c => c.vars
  | .revert => []
  | .call _ args _ ret body => Arg.vars args ++ ret.vars ++ Prog.vars body
  | .tryCall c rets ok err code pnc other =>
    c.vars ++ rets.map (·.2) ++ Prog.vars ok ++ Prog.vars err ++ code.toList ++ Prog.vars pnc ++
      Prog.vars other
  | .loop a c body => a.vars ++ c.vars ++ Prog.vars body

def Prog.vars : List (Stmt C) → List Var
  | [] => []
  | s :: P => s.vars ++ Prog.vars P

end

/-! ## Frames

What a piece of syntax does not mention, it does not see: two states that
agree off `ns` evaluate a part that avoids `ns` alike, and run a statement
that avoids `ns` to states that agree off `ns` again.  Binding a scratch
`sp1` changes nothing `alice.age = 10;` reads or writes. -/

section Frame

variable {ns : List Var} {σ τ : State}

theorem aliasPath_frame (hag : EnvAgreeExcept ns σ τ) {x : Var} (hx : x ∉ ns) :
    aliasPath σ x = aliasPath τ x := by
  unfold aliasPath; rw [getEnv_congr hag hx]

theorem Simple.eval_frame (hag : EnvAgreeExcept ns σ τ) {p : PrimTy} :
    (s : Simple C p) → Avoids s.vars ns → s.eval σ = s.eval τ
  | .lit .., _ | .bool _, _ => rfl
  | .local x, h => by simp only [Simple.eval, getEnv_congr hag (h x (by simp [Simple.vars]))]
  | .env k _, _ => by simp only [Simple.eval, State.envVal_congr hag]

mutual

theorem SPath.resolve_frame (hag : EnvAgreeExcept ns σ τ) :
    {T : Ty} → (p : SPath C T) → Avoids p.vars ns → p.resolve σ = p.resolve τ
  | _, .alias x, h => aliasPath_frame hag (h x (by simp [SPath.vars]))
  | _, .loc l, h => l.resolve_frame hag h

theorem Loc.resolve_frame (hag : EnvAgreeExcept ns σ τ) :
    {T : Ty} → (l : Loc C T) → Avoids l.vars ns → l.resolve σ = l.resolve τ
  | _, .root .., _ => rfl
  | _, .field b _ _, h => by simp only [Loc.resolve, b.resolve_frame hag h]
  | _, .index _ b i, h => by
    simp only [Loc.resolve, b.resolve_frame hag h.left, i.eval_frame hag h.right,
      checkIndex_congr hag]

theorem MPath.mval_frame (hag : EnvAgreeExcept ns σ τ) :
    {T : Ty} → (p : MPath C T) → Avoids p.vars ns → p.mval σ = p.mval τ
  | _, .var x, h => by simp only [MPath.mval, getEnv_congr hag (h x (by simp [MPath.vars]))]
  | _, .loc l, h => l.read_frame hag h

theorem MLoc.read_frame (hag : EnvAgreeExcept ns σ τ) :
    {T : Ty} → (l : MLoc C T) → Avoids l.vars ns → l.read σ = l.read τ
  | _, .field b _ _, h => by simp only [MLoc.read, b.mval_frame hag h, getObj_congr hag]
  | _, .index _ b i, h => by
    simp only [MLoc.read, b.mval_frame hag h.left, i.eval_frame hag h.right, getObj_congr hag]

theorem Val.eval_frame (hag : EnvAgreeExcept ns σ τ) :
    {p : PrimTy} → (v : Val C p) → Avoids v.vars ns → v.eval σ = v.eval τ
  | _, .simple s, h => s.eval_frame hag h
  | _, .read l, h => by simp only [Val.eval, l.resolve_frame hag h, findStorage_congr hag]
  | _, .binop _ _ _ a b, h => by
    simp only [Val.eval, a.eval_frame hag h.left, b.eval_frame hag h.right]
  | _, .unop _ _ _ a, h => by simp only [Val.eval, a.eval_frame hag h]
  | _, .ternary c a b, h => by
    simp only [Val.eval, c.eval_frame hag h.left.left, a.eval_frame hag h.left.right,
      b.eval_frame hag h.right]
  | _, .readMem l, h => by simp only [Val.eval, l.read_frame hag h]
  | _, .len b _, h => by simp only [Val.eval, b.resolve_frame hag h, arrayLen, findStorage_congr hag]
  | _, .mlen b _, h => by simp only [Val.eval, b.mval_frame hag h, memArrayLen, getObj_congr hag]

end

theorem Src.value_frame (hag : EnvAgreeExcept ns σ τ) {T : Ty} :
    (r : Src C T) → Avoids r.vars ns → r.value σ = r.value τ
  | .val v, h => by simp only [Src.value, v.eval_frame hag h]
  | .copy p _, h => by simp only [Src.value, p.resolve_frame hag h, findStorage_congr hag]

theorem MSrc.mval_frame (hag : EnvAgreeExcept ns σ τ) {T : Ty} :
    (r : MSrc C T) → Avoids r.vars ns → r.mval σ = r.mval τ
  | .val v, h => by simp only [MSrc.mval, v.eval_frame hag h]
  | .ref p, h => by simp only [MSrc.mval, p.mval_frame hag h]

/-! ### The state operations respect agreement -/

theorem ResultsAgree.ok {s₁ s₂ : State} (h : EnvAgreeExcept ns s₁ s₂) :
    ResultsAgree ns (.ok s₁) (.ok s₂) := h

theorem memWriteField_agree (hag : EnvAgreeExcept ns σ τ) (id : Nat) (f : Name) (mv : MVal) :
    ResultsAgree ns (memWriteField σ id f mv) (memWriteField τ id f mv) := by
  unfold memWriteField; rw [getObj_congr hag]
  cases τ.getObj id with
  | error _ => rfl
  | ok o => cases o <;> first | rfl | exact setObj_agree hag _ _

theorem memWriteIndex_agree (hag : EnvAgreeExcept ns σ τ) (id : Nat) (i : Int) (mv : MVal) :
    ResultsAgree ns (memWriteIndex σ id i mv) (memWriteIndex τ id i mv) := by
  unfold memWriteIndex; rw [getObj_congr hag]
  cases τ.getObj id with
  | error _ => rfl
  | ok o =>
    cases o with
    | struct _ => rfl
    | array elems =>
      simp only [bind, Except.bind]
      split
      · exact setObj_agree hag _ _
      · rfl

theorem readLoc_congr (hag : EnvAgreeExcept ns σ τ) (a : Addr) : readLoc σ a = readLoc τ a := by
  cases a <;> simp only [readLoc, getObj_congr hag]

theorem writeLoc_agree (hag : EnvAgreeExcept ns σ τ) (a : Addr) (v : Value) :
    ResultsAgree ns (writeLoc σ a v) (writeLoc τ a v) := by
  cases a with
  | memoryField id f =>
    simp only [writeLoc, getObj_congr hag]
    cases τ.getObj id with
    | error _ => rfl
    | ok o => cases o <;> first | rfl | exact setObj_agree hag _ _
  | memoryIndex id i =>
    simp only [writeLoc, getObj_congr hag]
    cases τ.getObj id with
    | error _ => rfl
    | ok o =>
      cases o with
      | struct _ => rfl
      | array elems =>
        simp only [bind, Except.bind]
        split
        · exact setObj_agree hag _ _
        · rfl

theorem ResAgree.of_results {α : Type} {x₁ x₂ : Res State} (h : ResultsAgree ns x₁ x₂) (a : α) :
    ResAgree ns (x₁ >>= fun s => pure (s, a)) (x₂ >>= fun s => pure (s, a)) := by
  match x₁, x₂, h with
  | .error _, .error _, h => subst h; rfl
  | .ok _, .ok _, h => exact ⟨rfl, h⟩

set_option hygiene false in
/-- Two runs of one computation from agreeing states: peel the shared pure
prefix, then close with the operation's agreement lemma. -/
macro "agree_run" h:term : tactic => `(tactic| repeat (first
  | exact ResultsAgree.refl _ _
  | exact EnvAgreeExcept.setEnv_both $h _ _
  | exact ResAgree.ok (EnvAgreeExcept.setEnv_both $h _ _)
  | exact $h
  | exact saveStorage_agree $h _ _ _
  | exact writeStorage_agree $h _ _ _
  | exact memWriteField_agree $h _ _ _
  | exact memWriteIndex_agree $h _ _ _
  | exact writeLoc_agree $h _ _
  | exact ResAgree.of_results (saveStorage_agree $h _ _ _) _
  | exact ResAgree.of_results (writeLoc_agree $h _ _) _
  | exact opStore_agree $h _ _ _ _ _
  | exact opMem_agree $h _ _ _ _
  | exact bumpStore_agree $h _ _ _ _
  | exact bumpMem_agree $h _ _ _
  | exact transferAt_agree $h _ _
  | exact sendAt_agree $h _ _ _
  | exact popAt_agree $h _ _ _
  | refine bindPureResults_agree _ fun _ => ?_
  | refine bindPureRes_agree _ fun _ => ?_
  | split))

theorem MLoc.write_frame (hag : EnvAgreeExcept ns σ τ) (mv : MVal) {T : Ty} :
    (l : MLoc C T) → Avoids l.vars ns → ResultsAgree ns (l.write σ mv) (l.write τ mv)
  | .field b f _, h => by
    simp only [MLoc.write, b.mval_frame hag h]
    agree_run hag
  | .index _ b i, h => by
    simp only [MLoc.write, b.mval_frame hag h.left, i.eval_frame hag h.right]
    agree_run hag

theorem opStore_agree (hag : EnvAgreeExcept ns σ τ) (op : BinOp) (p : PrimTy) (r : Name)
    (segs : List Seg) (v : Value) :
    ResultsAgree ns (opStore σ op p r segs v) (opStore τ op p r segs v) := by
  simp only [opStore, findStorage_congr hag]
  agree_run hag

theorem opMem_agree (hag : EnvAgreeExcept ns σ τ) (op : BinOp) (p : PrimTy) (a : Addr)
    (v : Value) : ResultsAgree ns (opMem σ op p a v) (opMem τ op p a v) := by
  simp only [opMem, readLoc_congr hag]
  agree_run hag

theorem OpLoc.store_frame (hag : EnvAgreeExcept ns σ τ) (op : BinOp) {p : PrimTy} :
    (l : OpLoc C p) → Avoids l.vars ns → (v : Value) →
      ResultsAgree ns (l.store σ op v) (l.store τ op v)
  | .local x, h, v => by
    simp only [OpLoc.store, opLocal, getEnv_congr hag (h.head)]
    agree_run hag
  | .root .., _, v => opStore_agree hag _ _ _ _ _
  | .field b f hf, h, v => by
    simp only [OpLoc.store, (Loc.field b f hf).resolve_frame hag h]
    agree_run hag
  | .index it b i, h, v => by
    simp only [OpLoc.store, (Loc.index it b (.simple i)).resolve_frame hag h]
    agree_run hag
  | .mfield b f _, h, v => by
    simp only [OpLoc.store, b.mval_frame hag h]
    agree_run hag
  | .mindex _ b i, h, v => by
    simp only [OpLoc.store, b.mval_frame hag h.left, i.eval_frame hag h.right]
    agree_run hag

theorem bumpStore_agree (hag : EnvAgreeExcept ns σ τ) (op : IncDec) (p : PrimTy) (r : Name)
    (segs : List Seg) : ResAgree ns (bumpStore σ op p r segs) (bumpStore τ op p r segs) := by
  simp only [bumpStore, findStorage_congr hag]
  agree_run hag

theorem bumpMem_agree (hag : EnvAgreeExcept ns σ τ) (op : IncDec) (p : PrimTy) (a : Addr) :
    ResAgree ns (bumpMem σ op p a) (bumpMem τ op p a) := by
  simp only [bumpMem, readLoc_congr hag]
  agree_run hag

theorem OpLoc.bump_frame (hag : EnvAgreeExcept ns σ τ) (op : IncDec) {p : PrimTy} :
    (l : OpLoc C p) → Avoids l.vars ns → ResAgree ns (l.bump σ op) (l.bump τ op)
  | .local x, h => by
    simp only [OpLoc.bump, bumpLocal, getEnv_congr hag (h.head)]
    agree_run hag
  | .root .., _ => bumpStore_agree hag _ _ _ _
  | .field b f hf, h => by
    simp only [OpLoc.bump, (Loc.field b f hf).resolve_frame hag h]
    agree_run hag
  | .index it b i, h => by
    simp only [OpLoc.bump, (Loc.index it b (.simple i)).resolve_frame hag h]
    agree_run hag
  | .mfield b f _, h => by
    simp only [OpLoc.bump, b.mval_frame hag h]
    agree_run hag
  | .mindex _ b i, h => by
    simp only [OpLoc.bump, b.mval_frame hag h.left, i.eval_frame hag h.right]
    agree_run hag

theorem pushAt_agree (hag : EnvAgreeExcept ns σ τ) (E : Ty) (r : Name) (segs : List Seg)
    {f g : SVal → Res SVal} (hfg : ∀ x, f x = g x) :
    ResultsAgree ns (pushAt σ E r segs f) (pushAt τ E r segs g) := by
  simp only [pushAt, findStorage_congr hag, hfg]
  refine bindPureResults_agree _ fun v => ?_
  cases v <;> first | rfl | agree_run hag

theorem pushPlaceAt_agree (hag : EnvAgreeExcept ns σ τ) (E : Ty) (r : Name) (segs : List Seg) :
    ResAgree ns (pushPlaceAt σ E r segs) (pushPlaceAt τ E r segs) := by
  simp only [pushPlaceAt, findStorage_congr hag]
  refine bindPureRes_agree _ fun v => ?_
  cases v <;> first | rfl | exact ResAgree.of_results (saveStorage_agree hag _ _ _) _

theorem popAt_agree (hag : EnvAgreeExcept ns σ τ) (keep : Bool) (r : Name) (segs : List Seg) :
    ResultsAgree ns (popAt σ keep r segs) (popAt τ keep r segs) := by
  simp only [popAt, findStorage_congr hag]
  refine bindPureResults_agree _ fun v => ?_
  cases v with
  | array elems shadow =>
    dsimp only
    split
    · rfl
    · exact saveStorage_agree hag _ _ _
  | _ => rfl

theorem transferAt_agree (hag : EnvAgreeExcept ns σ τ) (addr amt : Int) :
    ResultsAgree ns (transferAt σ addr amt) (transferAt τ addr amt) := by
  simp only [transferAt]
  split
  · rfl
  rw [State.pay_eq, State.pay_eq]
  exact ⟨hag.storage, hag.heap, hag.nextId,
    by simp only [State.getNet, hag.net, hag.tx], hag.env, hag.selfBalance, hag.tx⟩

theorem pay_agree (hag : EnvAgreeExcept ns σ τ) (addr amt : Int) :
    EnvAgreeExcept ns (σ.pay addr amt) (τ.pay addr amt) := by
  rw [State.pay_eq, State.pay_eq]
  exact ⟨hag.storage, hag.heap, hag.nextId,
    by simp only [State.getNet, hag.net, hag.tx], hag.env, hag.selfBalance, hag.tx⟩

theorem sendAt_agree (hag : EnvAgreeExcept ns σ τ) (pv : Var) (addr amt : Int) :
    ResultsAgree ns (sendAt σ pv addr amt) (sendAt τ pv addr amt) := by
  simp only [sendAt, hag.tx]
  split
  · rfl
  split
  · exact EnvAgreeExcept.setEnv_both (pay_agree hag addr amt) _ _
  · exact EnvAgreeExcept.setEnv_both (pay_agree hag addr amt) _ _
  · exact EnvAgreeExcept.setEnv_both hag _ _

theorem ARhs.bind_frame (hag : EnvAgreeExcept ns σ τ) (x : Var) {R : RefTy} :
    (r : ARhs C R) → Avoids r.vars ns → ResultsAgree ns (r.bind σ x) (r.bind τ x)
  | .path p, h => by
    simp only [ARhs.bind, p.resolve_frame hag h]
    agree_run hag
  | .push b _, h => by
    simp only [ARhs.bind, b.resolve_frame hag h]
    refine bindPureResults_agree _ fun _ => ?_
    refine ResAgree.bindState (pushPlaceAt_agree hag _ _ _) fun _ _ _ h' => ?_
    exact EnvAgreeExcept.setEnv_both h' _ _

theorem MRhs.bind_frame (hag : EnvAgreeExcept ns σ τ) (x : Var) {R : RefTy} :
    (r : MRhs C R) → Avoids r.vars ns → ResultsAgree ns (r.bind σ x) (r.bind τ x)
  | .alias p, h => by
    simp only [MRhs.bind, p.mval_frame hag h]
    agree_run hag
  | .copy p _, h => by
    simp only [MRhs.bind, p.resolve_frame hag h, findStorage_congr hag]
    refine bindPureResults_agree _ fun _ => bindPureResults_agree _ fun sv => ?_
    refine ResAgree.bindState (copyStToM_agree hag sv) fun _ _ _ h' => ?_
    agree_run h'
  | .newArr n _, h => by
    simp only [MRhs.bind, n.eval_frame hag h]
    refine bindPureResults_agree _ fun _ => bindPureResults_agree _ fun _ => ?_
    refine ResAgree.bindState (copyStToM_agree hag _) fun _ _ _ h' => ?_
    agree_run h'

theorem writeAddr_agree (hag : EnvAgreeExcept ns σ τ) (mv : MVal) (a : Addr) :
    ResultsAgree ns (writeAddr σ mv a) (writeAddr τ mv a) := by
  cases a
  · exact memWriteField_agree hag _ _ _
  · exact memWriteIndex_agree hag _ _ _

theorem MLoc.addr_frame (hag : EnvAgreeExcept ns σ τ) {T : Ty} :
    (l : MLoc C T) → Avoids l.vars ns → l.addr σ = l.addr τ
  | .field b _ _, h => by simp only [MLoc.addr, b.mval_frame hag h]
  | .index _ b i, h => by simp only [MLoc.addr, b.mval_frame hag h.left, i.eval_frame hag h.right]

theorem memClear_agree (hag : EnvAgreeExcept ns σ τ) (a : Addr) :
    (T : Ty) → ResultsAgree ns (memClear σ a T) (memClear τ a T)
  | .prim _ => writeAddr_agree hag _ _
  | .ref R => ResAgree.bindState (allocDefault_agree hag R) fun _ _ _ h' => writeAddr_agree h' _ _

theorem allocDefault_bind_agree (hag : EnvAgreeExcept ns σ τ) (R : RefTy) (x : Var) :
    ResultsAgree ns (do let (σ', id) ← allocDefault σ R; pure (σ'.setEnv x (.mref id)))
      (do let (σ', id) ← allocDefault τ R; pure (σ'.setEnv x (.mref id))) :=
  ResAgree.bindState (allocDefault_agree hag R) fun _ _ _ h' => EnvAgreeExcept.setEnv_both h' _ _

/-- A call's arguments, read from two states that agree off `ns`, bind alike
into two states that agree off `ns`. -/
theorem Arg.bindSeq_frame :
    (args : List (Arg C)) → Avoids (Arg.vars args) ns → ∀ {σ τ : State}, EnvAgreeExcept ns σ τ →
      ResultsAgree ns (Arg.bindSeq args σ) (Arg.bindSeq args τ)
  | [], _, _, _, hag => hag
  | a :: as, h, _, _, hag => by
    simp only [Arg.bindSeq, a.e.eval_frame hag (fun x hx => h x (by simp [Arg.vars, hx]))]
    refine bindPureResults_agree _ fun v => ?_
    exact Arg.bindSeq_frame as (fun x hx => h x (by simp [Arg.vars, hx]))
      (EnvAgreeExcept.setEnv_both hag _ _)

/-- An external call is made alike from two states that agree off what it
reads. -/
theorem ExtCall.key_frame {σ τ : State} (hag : EnvAgreeExcept ns σ τ) (c : ExtCall C)
    (h : Avoids c.vars ns) : c.key σ = c.key τ := by
  have hargs : ∀ as : List (ExtArg C), Avoids (as.flatMap fun a => a.2.vars) ns →
      as.mapM (fun a => a.2.eval σ) = as.mapM (fun a => a.2.eval τ) := by
    intro as
    induction as with
    | nil => intro _; rfl
    | cons a as ih =>
      intro h
      simp only [List.mapM_cons, a.2.eval_frame hag (h.left (ws := _) |> fun h' => by
        simpa [List.flatMap_cons] using fun x hx => h x (by simp [List.flatMap_cons, hx])),
        ih (fun x hx => h x (by simp only [List.flatMap_cons]; exact List.mem_append_right _ hx))]
  simp only [ExtCall.key, c.addr.eval_frame hag h.left, hargs c.args h.right]

/-- The locals an outcome binds, bound alike in two states that agree. -/
theorem bindData_frame :
    (xs : List (PrimTy × Var)) → (vs : List Value) → ∀ {σ τ : State}, EnvAgreeExcept ns σ τ →
      ResultsAgree ns (bindData xs vs σ) (bindData xs vs τ)
  | [], _, _, _, hag => hag
  | _ :: _, [], _, _, _ => rfl
  | (p, x) :: xs, v :: vs, _, _, hag => by
    simp only [bindData]
    split
    · exact bindData_frame xs vs (EnvAgreeExcept.setEnv_both hag _ _)
    · rfl

theorem CallRet.enter_frame {σ τ : State} (hag : EnvAgreeExcept ns σ τ) (ret : CallRet) :
    EnvAgreeExcept ns (ret.enter σ) (ret.enter τ) := by
  exact CallRet.enter_induct₂ (R := EnvAgreeExcept ns)
    (fun _ _ _ _ h => EnvAgreeExcept.setEnv_both h _ _) ret hag

theorem CallRet.leave_frame {σ τ : State} (hag : EnvAgreeExcept ns σ τ) :
    (ret : CallRet) → Avoids ret.vars ns →
      ResultsAgree ns (CallRet.leave (C := C) σ ret) (CallRet.leave (C := C) τ ret)
  | .none, _ => hag
  | .val _ _ Option.none, _ => hag
  | .rets _, _ => hag
  | .val p r (some y), h => by
    simp only [CallRet.leave,
      (Simple.local r : Simple C p).eval_frame hag (fun x hx => h x (by simp_all [Simple.vars, CallRet.vars]))]
    agree_run hag

mutual

/-- **Frame, for statements**: a statement that avoids `ns` runs alike from
two states that agree off `ns`, and they end agreeing off `ns`.  Binding a
scratch `sp1` changes nothing `alice.age = 10;` reads or writes. -/
theorem Stmt.run_frame {σ τ : State} (hag : EnvAgreeExcept ns σ τ) :
    (s : Stmt C) → Avoids s.vars ns → ResultsAgree ns (s.run σ) (s.run τ)
  | .assign l r, h => by
    simp only [Stmt.run, r.value_frame hag h.right, l.resolve_frame hag h.left]
    agree_run hag
  | .rebind x r, h => r.bind_frame hag x h.tail
  | .assignLocal x r, h => by
    simp only [Stmt.run, r.eval_frame hag h.tail]
    agree_run hag
  | .declLocal p x init, h => by
    cases init with
    | none => exact EnvAgreeExcept.setEnv_both hag _ _
    | some e =>
      simp only [Stmt.run, e.eval_frame hag h.tail]
      agree_run hag
  | .declStorage _ x init, h => by
    cases init with
    | none => exact hag
    | some r => exact r.bind_frame hag x h.tail
  | .opAssign op _ _ l r, h => by
    simp only [Stmt.run, r.eval_frame hag h.right]
    exact bindPureResults_agree _ fun v => l.store_frame hag op h.left v
  | .incDec op _ l, h => by
    simp only [Stmt.run]
    exact ResAgree.bindState (l.bump_frame hag op h) fun _ _ _ h' => h'
  | .assignIncDec x op _ l _, h => by
    simp only [Stmt.run]
    exact ResAgree.bindState (l.bump_frame hag op h.tail) fun _ _ _ h' =>
      EnvAgreeExcept.setEnv_both h' _ _
  | .push (E := E) b v _, h => by
    simp only [Stmt.run, b.resolve_frame hag h.left]
    refine bindPureResults_agree _ fun _ => pushAt_agree hag _ _ _ fun sv => ?_
    cases v with
    | none => rfl
    | some r => simp only [Src.pushVal, r.value_frame hag h.right]
  | .pop b, h => by
    simp only [Stmt.run, b.resolve_frame hag h]
    agree_run hag
  | .transfer r a, h => by
    simp only [Stmt.run, r.eval_frame hag h.left, a.eval_frame hag h.right]
    agree_run hag
  | .send pv r a, h => by
    simp only [Stmt.run, r.eval_frame hag h.tail.left, a.eval_frame hag h.tail.right]
    agree_run hag
  | .declMem R x init _, h => by
    cases init with
    | none => exact allocDefault_bind_agree hag R x
    | some r => exact r.bind_frame hag x h.tail
  | .rebindMem x r, h => r.bind_frame hag x h.tail
  | .assignFromMem l p, h => by
    simp only [Stmt.run, p.mval_frame hag h.right, l.resolve_frame hag h.left, copyMem_congr hag]
    agree_run hag
  | .assignMem l r, h => by
    simp only [Stmt.run, r.mval_frame hag h.right]
    exact bindPureResults_agree _ fun mv => l.write_frame hag mv h.left
  | .delete l, h => by
    simp only [Stmt.run, l.resolve_frame hag h, findStorage_congr hag]
    agree_run hag
  | .deleteMem p _, h => by
    cases p with
    | var x => exact allocDefault_bind_agree hag _ x
    | loc l =>
      simp only [Stmt.run, l.addr_frame hag h]
      exact bindPureResults_agree _ fun a => memClear_agree hag a _
  | .assignNew l n _, h => by
    simp only [Stmt.run, n.eval_frame hag h.right]
    refine bindPureResults_agree _ fun _ => bindPureResults_agree _ fun _ => ?_
    refine ResAgree.bindState (copyStToM_agree hag _) fun _ _ _ h' => ?_
    refine bindPureResults_agree _ fun id => ?_
    cases l with
    | store l =>
      simp only [copyMem_congr h', l.resolve_frame h' h.left]
      agree_run h'
    | mem l => exact l.write_frame h' _ h.left
  | .ite c thn els, h => by
    simp only [Stmt.run, c.eval_frame hag h.left.left]
    refine bindPureResults_agree _ fun v => ?_
    cases v with
    | bool b =>
      cases b
      · exact Prog.run_frame hag els h.right
      · exact Prog.run_frame hag thn h.left.right
    | int _ => rfl
  | .require c, h | .assert c, h => by
    simp only [Stmt.run, c.eval_frame hag h]
    refine bindPureResults_agree _ fun v => ?_
    cases v with
    | bool b => cases b <;> first | rfl | exact hag
    | int _ => rfl
  | .revert, _ => rfl
  | .call _ args _ ret body, h => by
    simp only [Stmt.run]
    refine ResultsAgree.bind (Arg.bindSeq_frame args h.left.left hag) fun _ _ h₁ => ?_
    refine ResultsAgree.bind (Prog.run_frame (CallRet.enter_frame h₁ ret) body h.right)
      fun _ _ h₂ => ?_
    exact CallRet.leave_frame h₂ ret h.left.right
  | .tryCall c rets ok err code pnc other, h => by
    simp only [Stmt.run, c.key_frame hag h.left.left.left.left.left.left, hag.tx]
    refine bindPureResults_agree _ fun k => ?_
    rcases lookupBy k τ.tx.ext with _ | (vs | _ | v | _)
    · rfl
    · exact ResultsAgree.bind (bindData_frame rets vs hag) fun _ _ h' =>
        Prog.run_frame h' ok h.left.left.left.left.right
    · exact Prog.run_frame hag err h.left.left.left.right
    · exact ResultsAgree.bind (bindData_frame _ [v] hag) fun _ _ h' =>
        Prog.run_frame h' pnc h.left.right
    · exact Prog.run_frame hag other h.right
  | .loop _ c body, h => by
    simp only [Stmt.run]
    refine Loop.run_rel (R := EnvAgreeExcept ns) (Q := ResultsAgree ns) hag
      (fun τ₁ τ₂ hτ => ?_) rfl
    simp only [Loop.step, c.eval_frame hτ h.left.right]
    rcases c.eval τ₂ with e | (_ | b)
    · exact (rfl : e = e)
    · exact (rfl : Halt.stuck = Halt.stuck)
    · cases b
      · exact hτ
      · rcases (Prog.run_frame hτ body h.right).cases with ⟨e, h₁, h₂⟩ | ⟨s₁, s₂, h₁, h₂, hs⟩
        · simp only [h₁, h₂]
          exact (rfl : e = e)
        · simp only [h₁, h₂]
          exact hs

theorem Prog.run_frame {σ τ : State} (hag : EnvAgreeExcept ns σ τ) :
    (P : List (Stmt C)) → Avoids (Prog.vars P) ns → ResultsAgree ns (Prog.run σ P) (Prog.run τ P)
  | [], _ => hag
  | s :: P, h => by
    simp only [Prog.run]
    exact ResultsAgree.bind (Stmt.run_frame hag s h.left) fun _ _ h' => Prog.run_frame h' P h.right

end

end Frame

end Solidity
