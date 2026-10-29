import Solidity.Source.Semantics

/-!
# Horizons: the interpreter is monotone in its fuel (S05 item 2)

`Below m m'`: on every state, `m` times out or runs exactly as `m'`.  Every
function of the interpreter at horizon `n` is `Below` itself at `n + 1`
(`belowAt`, by induction on `n`, one step theorem per function so each stays
within the default heartbeats), and so are deployments and transactions
(`deploy_below`, `runTx_below`).  Hence **horizon independence**: a result
that completes at some horizon is the result at every larger one
(`runTx_stable`, `deploy_stable`), what `firstDone` finds is not a choice
(`firstDone_runTx`), and a `stuck` run stays stuck (`runTx_stuck_stable`),
so it is not a lack of horizon.

`Approx`/`Grow` additionally track that events only grow; they are the
start of the events of non-completing transactions, not yet used.

The tactic `below_go` walks two copies of a body that differ only in the
horizon: through binds, `attempt`s, `match`es and `if`s, closing calls by the
given lemmas and the rest by reflexivity.  `below_unfold f n` unfolds one
level of `f` on each side without unfolding the right side's inner calls.
-/

namespace Solidity.Source

open EM
open Solidity.Roadmap (Address Word Bytes Request Outcome Event)

variable {E : Env}

/-- A computation only appends events. -/
def Grow {Γ : RCtx} {α : Type} (m : EM E Γ α) : Prop :=
  ∀ x, x.2.events <+: (m.run x).2.2.events

/-- **`m` approximates `m'`**: both grow, and on every state `m` either
times out with events `m'` extends, or agrees with `m'`. -/
def Approx {Γ : RCtx} {α : Type} (m m' : EM E Γ α) : Prop :=
  Grow m ∧ Grow m' ∧ ∀ x, ((m.run x).1 = .error .timeout ∧ (m.run x).2.2.events <+: (m'.run x).2.2.events) ∨
    m.run x = m'.run x

theorem run_bind {Γ : RCtx} {α β : Type} (m : EM E Γ α) (k : α → EM E Γ β) (x) :
    (m >>= k).run x = match m.run x with
      | (.ok a, y) => (k a).run y
      | (.error e, y) => (.error e, y) := by
  rw [ExceptT.run_bind]
  show StateT.bind (ExceptT.run m) _ x = _
  simp only [StateT.bind]
  show (match ExceptT.run m x with | (r, y) => _) = _
  rcases ExceptT.run m x with ⟨r, y⟩
  cases r <;> rfl

theorem Grow.pure {Γ : RCtx} {α : Type} (a : α) : Grow (pure a : EM E Γ α) := fun _ => List.prefix_refl _

theorem Grow.halt {Γ : RCtx} {α : Type} (h : Halt) : Grow (halt h : EM E Γ α) := fun _ => List.prefix_refl _

theorem Grow.bind {Γ : RCtx} {α β : Type} {m : EM E Γ α} {k : α → EM E Γ β} (hm : Grow m)
    (hk : ∀ a, Grow (k a)) : Grow (m >>= k) := by
  intro x
  rw [run_bind]
  have h1 := hm x
  rcases hr : m.run x with ⟨r, y⟩
  rw [hr] at h1
  cases r with
  | ok a => exact h1.trans (hk a y)
  | error e => exact h1

theorem Approx.refl {Γ : RCtx} {α : Type} {m : EM E Γ α} (h : Grow m) : Approx m m :=
  ⟨h, h, fun _ => .inr rfl⟩

theorem Approx.timeout {Γ : RCtx} {α : Type} {m' : EM E Γ α} (h : Grow m') : Approx (halt .timeout) m' :=
  ⟨Grow.halt _, h, fun x => .inl ⟨rfl, h x⟩⟩

theorem Approx.bind {Γ : RCtx} {α β : Type} {m m' : EM E Γ α} {k k' : α → EM E Γ β}
    (hm : Approx m m') (hk : ∀ a, Approx (k a) (k' a)) : Approx (m >>= k) (m' >>= k') := by
  refine ⟨Grow.bind hm.1 fun a => (hk a).1, Grow.bind hm.2.1 fun a => (hk a).2.1, fun x => ?_⟩
  rw [run_bind, run_bind]
  rcases hm.2.2 x with ⟨ht, he⟩ | he
  · left
    rcases hr : m.run x with ⟨r, y⟩
    rw [hr] at ht he
    cases ht
    refine ⟨rfl, he.trans ?_⟩
    rcases hr' : m'.run x with ⟨r', y'⟩
    cases r' with
    | ok a => exact (hk a).2.1 y'
    | error e => exact List.prefix_refl _
  · rw [← he]
    rcases m.run x with ⟨r, y⟩
    cases r with
    | ok a => exact (hk a).2.2 y
    | error e => exact .inr rfl

/-! ## Completion is stable under more fuel -/

/-- **`m` is `m'` or times out**: on every state, `m` times out or agrees
with `m'`. -/
def Below {Γ : RCtx} {α : Type} (m m' : EM E Γ α) : Prop :=
  ∀ x, (m.run x).1 = .error .timeout ∨ m.run x = m'.run x

theorem Below.refl {Γ : RCtx} {α : Type} (m : EM E Γ α) : Below m m := fun _ => .inr rfl

theorem Below.timeout {Γ : RCtx} {α : Type} (m' : EM E Γ α) : Below (halt .timeout) m' := fun _ => .inl rfl

theorem Below.bind {Γ : RCtx} {α β : Type} {m m' : EM E Γ α} {k k' : α → EM E Γ β}
    (hm : Below m m') (hk : ∀ a, Below (k a) (k' a)) : Below (m >>= k) (m' >>= k') := by
  intro x
  rw [run_bind, run_bind]
  rcases hm x with ht | he
  · left
    rcases hr : m.run x with ⟨r, y⟩
    rw [hr] at ht
    cases ht
    rfl
  · rw [← he]
    rcases m.run x with ⟨r, y⟩
    cases r with
    | ok a => exact hk a y
    | error e => exact .inr rfl

theorem Below.bind_left {Γ : RCtx} {α β : Type} {m m' : EM E Γ α} {k : α → EM E Γ β}
    (hm : Below m m') : Below (m >>= k) (m' >>= k) := Below.bind hm fun a => Below.refl (k a)

theorem Below.bind_right {Γ : RCtx} {α β : Type} (m : EM E Γ α) {k k' : α → EM E Γ β}
    (hk : ∀ a, Below (k a) (k' a)) : Below (m >>= k) (m >>= k') := Below.bind (Below.refl m) hk

/-- Close `Below (body at n) (body at n + 1)`: through binds, `match`es and
`if`s, by the given fuel lemmas at the calls, and by reflexivity where no
fuel is read. -/
syntax "below_go" "[" ident,* "]" : tactic
macro_rules
  | `(tactic| below_go [$ls,*]) => `(tactic| repeat' (first
      | (with_reducible exact Below.timeout _)
      | (with_reducible exact Below.refl _)
      | (first $[| with_reducible apply $ls:ident]*)
      | (apply Below.attempt_bind)
      | (refine Below.bind ?_ ?_)
      | (with_reducible intro _)
      | (with_reducible rfl)
      | split
      | (dsimp only)))

mutual
theorem zeroData_below {Γ : RCtx} : ∀ (n : Nat) (τ : STy), Below (zeroData (E := E) (Γ := Γ) n τ) (zeroData (n + 1) τ)
  | 0, _ => Below.timeout _
  | n + 1, τ => by
    simp only [zeroData]
    split
    all_goals first
      | exact Below.refl _
      | exact Below.bind (zeroElems_below n _ _) fun _ => Below.refl _
      | exact Below.bind (zeroFields_below n _) fun _ => Below.refl _
      | exact Below.bind (zeroVal_below n _) fun _ => Below.refl _
theorem zeroVal_below {Γ : RCtx} : ∀ (n : Nat) (τ : STy), Below (zeroVal (E := E) (Γ := Γ) n τ) (zeroVal (n + 1) τ)
  | 0, _ => Below.timeout _
  | n + 1, τ => by
    simp only [zeroVal]
    split
    · exact Below.refl _
    · split
      · exact Below.bind (zeroData_below n _) fun _ => Below.refl _
      · exact Below.refl _
theorem zeroElems_below {Γ : RCtx} : ∀ (n : Nat) (σ : STy) (m : Nat),
    Below (zeroElems (E := E) (Γ := Γ) n σ m) (zeroElems (n + 1) σ m)
  | 0, _, m => by cases m <;> simp only [zeroElems] <;> exact Below.timeout _
  | n + 1, _, 0 => by simp only [zeroElems]; exact Below.refl _
  | n + 1, σ, m + 1 => by
    simp only [zeroElems]
    exact Below.bind (zeroVal_below n _) fun _ => Below.bind (zeroElems_below n _ _) fun _ => Below.refl _
theorem zeroFields_below {Γ : RCtx} : ∀ (n : Nat) (τs : List STy),
    Below (zeroFields (E := E) (Γ := Γ) n τs) (zeroFields (n + 1) τs)
  | 0, τs => by cases τs <;> simp only [zeroFields] <;> exact Below.timeout _
  | n + 1, [] => by simp only [zeroFields]; exact Below.refl _
  | n + 1, τ :: τs => by
    simp only [zeroFields]
    exact Below.bind (zeroVal_below n _) fun _ => Below.bind (zeroFields_below n _) fun _ => Below.refl _
end


mutual
theorem loadMem_below {Γ : RCtx} (F : Fr) : ∀ (n : Nat) (τ : STy) (p : SPath),
    Below (loadMem (E := E) (Γ := Γ) F n τ p) (loadMem F (n + 1) τ p)
  | 0, _, _ => Below.timeout _
  | n + 1, τ, p => by
    simp only [loadMem]
    below_go [loadBytes_below, loadElems_below, loadFields_below]
theorem loadElem_below {Γ : RCtx} (F : Fr) : ∀ (n : Nat) (τ : STy) (p : SPath),
    Below (loadElem (E := E) (Γ := Γ) F n τ p) (loadElem F (n + 1) τ p)
  | 0, _, _ => Below.timeout _
  | n + 1, τ, p => by
    simp only [loadElem]
    below_go [loadMem_below]
theorem loadElems_below {Γ : RCtx} (F : Fr) : ∀ (n : Nat) (σ : STy) (p : SPath) (i m : Nat),
    Below (loadElems (E := E) (Γ := Γ) F n σ p i m) (loadElems F (n + 1) σ p i m)
  | 0, _, _, _, m => by cases m <;> simp only [loadElems] <;> exact Below.timeout _
  | n + 1, _, _, _, 0 => by simp only [loadElems]; exact Below.refl _
  | n + 1, σ, p, i, m + 1 => by
    simp only [loadElems]
    below_go [loadElem_below, loadElems_below]
theorem loadFields_below {Γ : RCtx} (F : Fr) : ∀ (n : Nat) (τs : List STy) (p : SPath) (i : Nat),
    Below (loadFields (E := E) (Γ := Γ) F n τs p i) (loadFields F (n + 1) τs p i)
  | 0, τs, _, _ => by cases τs <;> simp only [loadFields] <;> exact Below.timeout _
  | n + 1, [], _, _ => by simp only [loadFields]; exact Below.refl _
  | n + 1, τ :: τs, p, i => by
    simp only [loadFields]
    below_go [loadElem_below, loadFields_below]
theorem loadBytes_below {Γ : RCtx} (F : Fr) : ∀ (n : Nat) (p : SPath) (i k : Nat),
    Below (loadBytes (E := E) (Γ := Γ) F n p i k) (loadBytes F (n + 1) p i k)
  | 0, _, _, k => by cases k <;> exact Below.timeout _
  | n + 1, _, _, 0 => Below.refl _
  | n + 1, p, i, k + 1 => by
    refine Below.bind (Below.refl _) fun v => ?_
    cases v <;> first
      | exact Below.bind (loadBytes_below F n p (i + 1) k) fun _ => Below.refl _
      | (rename_i h; cases h)
end


mutual
theorem deleteStor_below {Γ : RCtx} (F : Fr) : ∀ (n : Nat) (τ : STy) (p : SPath),
    Below (deleteStor (E := E) (Γ := Γ) F n τ p) (deleteStor F (n + 1) τ p)
  | 0, _, _ => Below.timeout _
  | n + 1, τ, p => by
    simp only [deleteStor]
    below_go [deleteRange_below, deleteFields_below]
theorem deleteRange_below {Γ : RCtx} (F : Fr) : ∀ (n : Nat) (σ : STy) (p : SPath) (i k : Nat),
    Below (deleteRange (E := E) (Γ := Γ) F n σ p i k) (deleteRange F (n + 1) σ p i k)
  | 0, _, _, _, k => by cases k <;> exact Below.timeout _
  | n + 1, _, _, _, 0 => Below.refl _
  | n + 1, σ, p, i, k + 1 =>
    Below.bind (deleteStor_below F n σ _) fun _ => deleteRange_below F n σ p (i + 1) k
theorem deleteFields_below {Γ : RCtx} (F : Fr) : ∀ (n : Nat) (τs : List STy) (p : SPath) (i : Nat),
    Below (deleteFields (E := E) (Γ := Γ) F n τs p i) (deleteFields F (n + 1) τs p i)
  | 0, τs, _, _ => by cases τs <;> exact Below.timeout _
  | n + 1, [], _, _ => Below.refl _
  | n + 1, τ :: τs, p, i =>
    Below.bind (deleteStor_below F n τ _) fun _ => deleteFields_below F n τs p (i + 1)
end

mutual
theorem storeData_below {Γ : RCtx} (F : Fr) : ∀ (n : Nat) (τ : STy) (p : SPath) {σ : STy} (x : Data E.layout σ),
    Below (storeData (Γ := Γ) F n τ p x) (storeData F (n + 1) τ p x)
  | 0, _, _, _, _ => Below.timeout _
  | n + 1, τ, p, _, x => by
    simp only [storeData]
    below_go [storeBytes_below, deleteRange_below, storeElems_below, storeFields_below, storeVal_below]
theorem storeVal_below {Γ : RCtx} (F : Fr) : ∀ (n : Nat) (τ : STy) (p : SPath) {σ : STy} (v : Val E.layout σ),
    Below (storeVal (Γ := Γ) F n τ p v) (storeVal F (n + 1) τ p v)
  | 0, _, _, _, _ => Below.timeout _
  | n + 1, τ, p, _, v => by
    simp only [storeVal]
    below_go [storeData_below, loadMem_below]
theorem storeElems_below {Γ : RCtx} (F : Fr) : ∀ (n : Nat) (τ : STy) (p : SPath) (i len : Nat) {σ : STy}
    (xs : Fin len → Data E.layout σ),
    Below (storeElems (Γ := Γ) F n τ p i len xs) (storeElems F (n + 1) τ p i len xs)
  | 0, _, _, _, len, _, _ => by cases len <;> exact Below.timeout _
  | n + 1, _, _, _, 0, _, _ => Below.refl _
  | n + 1, τ, p, i, len + 1, _, xs =>
    Below.bind (storeData_below F n τ _ _) fun _ => storeElems_below F n τ p (i + 1) len _
theorem storeFields_below {Γ : RCtx} (F : Fr) : ∀ (n : Nat) (τs : List STy) (p : SPath) (i : Nat) {σs : List STy}
    (xs : DataList E.layout σs),
    Below (storeFields (Γ := Γ) F n τs p i xs) (storeFields F (n + 1) τs p i xs)
  | 0, τs, _, _, _, xs => by cases τs <;> cases xs <;> exact Below.timeout _
  | n + 1, [], _, _, _, _ => Below.refl _
  | n + 1, _ :: _, _, _, _, .nil => Below.refl _
  | n + 1, τ :: τs, p, i, _, .cons x xs =>
    Below.bind (storeData_below F n τ _ x) fun _ => storeFields_below F n τs p (i + 1) xs
theorem storeBytes_below {Γ : RCtx} (F : Fr) : ∀ (n : Nat) (p : SPath) (i : Nat) (bs : List UInt8),
    Below (storeBytes (E := E) (Γ := Γ) F n p i bs) (storeBytes F (n + 1) p i bs)
  | 0, _, _, bs => by cases bs <;> exact Below.timeout _
  | n + 1, _, _, [] => Below.refl _
  | n + 1, p, i, b :: bs => Below.bind (Below.refl _) fun _ => storeBytes_below F n p (i + 1) bs
end


/-! ### The interpreter's helpers -/

theorem bytesOfRV_below {Γ : RCtx} (F : Fr) (n : Nat) {τ : STy} (v : RVal E.layout τ) :
    Below (bytesOfRV (Γ := Γ) F n v) (bytesOfRV F (n + 1) v) := by
  unfold bytesOfRV
  below_go [loadMem_below]

theorem encodeOne_below {Γ : RCtx} (F : Fr) (n : Nat) (packed : Bool) {τ : STy} (v : RVal E.layout τ) :
    Below (encodeOne (Γ := Γ) F n packed v) (encodeOne F (n + 1) packed v) := by
  unfold encodeOne
  below_go [bytesOfRV_below]

theorem encodeParts_below {Γ : RCtx} (F : Fr) (n : Nat) (packed : Bool) :
    ∀ {τs : List STy} (vs : RVals E.layout τs),
      Below (encodeParts (Γ := Γ) F n packed vs) (encodeParts F (n + 1) packed vs)
  | _, .nil => Below.refl _
  | _, .cons v vs => Below.bind (encodeOne_below F n packed v) fun _ =>
      Below.bind (encodeParts_below F n packed vs) fun _ => Below.refl _

theorem encodeVals_below {Γ : RCtx} (F : Fr) (n : Nat) (packed : Bool) {τs : List STy} (vs : RVals E.layout τs) :
    Below (encodeVals (Γ := Γ) F n packed vs) (encodeVals F (n + 1) packed vs) :=
  Below.bind (encodeParts_below F n packed vs) fun _ => Below.refl _

theorem convRV_below {Γ : RCtx} (F : Fr) (n : Nat) {σ : STy} (τ : STy) (v : RVal E.layout σ) :
    Below (convRV (Γ := Γ) F n τ v) (convRV F (n + 1) τ v) := by
  unfold convRV
  below_go [loadMem_below]

theorem convExplicitRV_below {Γ : RCtx} (F : Fr) (n : Nat) {σ : STy} (τ : STy) (v : RVal E.layout σ) :
    Below (convExplicitRV (Γ := Γ) F n τ v) (convExplicitRV F (n + 1) τ v) := by
  unfold convExplicitRV
  below_go [convRV_below, bytesOfRV_below]

theorem writeLoc_below {Γ : RCtx} (F : Fr) (n : Nat) {τ : STy} (loc : Loc E.layout Γ τ) (v : Val E.layout τ) :
    Below (writeLoc F n loc v) (writeLoc F (n + 1) loc v) := by
  unfold writeLoc
  below_go [storeVal_below]

theorem deleteLoc_below {Γ : RCtx} (F : Fr) (n : Nat) {τ : STy} (loc : Loc E.layout Γ τ) :
    Below (deleteLoc F n loc) (deleteLoc F (n + 1) loc) := by
  unfold deleteLoc
  below_go [deleteStor_below, writeLoc_below, zeroVal_below]

theorem keyStep_below {Γ : RCtx} (F : Fr) (n : Nat) {τ : STy} (k : RVal E.layout τ) :
    Below (keyStep (Γ := Γ) F n k) (keyStep F (n + 1) k) := by
  unfold keyStep
  below_go [bytesOfRV_below]

theorem zeroVals_below {Γ : RCtx} (n : Nat) : ∀ (τs : List STy),
    Below (zeroVals (E := E) (Γ := Γ) n τs) (zeroVals (n + 1) τs)
  | [] => Below.refl _
  | τ :: τs => Below.bind (zeroVal_below n τ) fun _ => Below.bind (zeroVals_below n τs) fun _ => Below.refl _

theorem zeroInner_below {Γ' : RCtx} (n : Nat) : ∀ (k : Nat) {Γ : RCtx} (l : Locals E.layout Γ),
    Below (zeroInner (Γ' := Γ') n k l) (zeroInner (n + 1) k l)
  | 0, _, _ => Below.refl _
  | _ + 1, _, .nil => Below.refl _
  | k + 1, _, .cons _ r => Below.bind (zeroVal_below n _) fun _ =>
      Below.bind (zeroInner_below n k r) fun _ => Below.refl _

theorem copyInto_below {Γ : RCtx} (F : Fr) (n : Nat) (τ : STy) (p : SPath) {σ : STy} (v : RVal E.layout σ) :
    Below (copyInto (Γ := Γ) F n τ p v) (copyInto F (n + 1) τ p v) := by
  unfold copyInto
  below_go [storeData_below, storeVal_below]

theorem getterPath_below {Γ : RCtx} (F : Fr) (n : Nat) (data : Solidity.Roadmap.Bytes) : ∀ (τ : STy) (p : SPath) (i : Nat),
    Below (getterPath (E := E) (Γ := Γ) F n data τ p i) (getterPath F (n + 1) data τ p i)
  | .mapping k v, p, i => by
    simp only [getterPath]
    below_go [keyStep_below, getterPath_below]
  | .array _ τ len, p, i => by
    simp only [getterPath]
    below_go [getterPath_below]
  | .int _, _, _ | .bool, _, _ | .address _, _, _ | .fixedBytes _ _, _, _ | .fixed _, _, _ | .enum _, _, _
  | .udvt _, _, _ | .contract _, _, _ | .bytes _, _, _ | .string _, _, _ | .struct _ _, _, _
  | .fn _ _ _ _, _, _ | .rational _, _, _ | .hexConst _ _, _, _ | .stringLit _, _, _ | .tuple _, _, _ =>
    Below.refl _


/-! ### Frames and caught halts -/

theorem run_attempt {Γ : RCtx} {α : Type} (m : EM E Γ α) (x) :
    (EM.attempt m).run x = (.ok (m.run x).1, (m.run x).2) := by
  show (match m.run x with | (r, x') => ((.ok r, x') : Except Halt _ × _)) = _
  rcases m.run x with ⟨r, y⟩
  rfl

theorem run_sub {Γ Γ' : RCtx} {α : Type} (l' : Locals E.layout Γ') (m : EM E Γ' α) (l : Locals E.layout Γ)
    (s : St E) : (EM.sub l' m).run (l, s) = match m.run (l', s) with
      | (.ok a, (l'', s')) => (.ok (a, l''), (l, s'))
      | (.error h, (_, s')) => (.error h, (l, s')) := rfl

theorem Below.sub {Γ Γ' : RCtx} {α : Type} (l' : Locals E.layout Γ') {m m' : EM E Γ' α}
    (h : Below m m') : Below (EM.sub (Γ := Γ) l' m) (EM.sub l' m') := by
  intro x
  rcases x with ⟨l, s⟩
  rw [run_sub, run_sub]
  rcases h (l', s) with ht | he
  · left
    rcases hr : m.run (l', s) with ⟨r, l'', s'⟩
    rw [hr] at ht
    cases ht
    rfl
  · right
    rw [he]

/-- A halt caught by `attempt`: the continuation re-raises a timeout. -/
theorem Below.attempt_bind {Γ : RCtx} {α β : Type} {m m' : EM E Γ α} {k k' : Except Halt α → EM E Γ β}
    (hm : Below m m') (hk : ∀ r, Below (k r) (k' r))
    (h0 : ∀ x, ((k (.error .timeout)).run x).1 = .error .timeout) :
    Below (EM.attempt m >>= k) (EM.attempt m' >>= k') := by
  intro x
  rw [run_bind, run_bind, run_attempt, run_attempt]
  rcases hm x with ht | he
  · left
    rw [ht]
    exact h0 _
  · rw [he]
    exact hk _ _


/-! ### The interpreter -/

/-- Unfold one level of `f` on each side of `Below (f (n + 1) …) (f (n + 2) …)`
without unfolding the right side's inner calls at `n + 1`. -/
syntax "below_unfold" ident ident : tactic
macro_rules
  | `(tactic| below_unfold $f $n) => `(tactic| (
      conv => lhs; simp only [$f:ident]
      generalize hm : $n + 1 = m
      conv => rhs; simp only [$f:ident]
      subst hm))


section
variable (G : Glob E)

/-- **The induction hypothesis**: every interpreter function at horizon `n`
is below itself at `n + 1`. -/
structure BelowAt (n : Nat) : Prop where
  evalE : ∀ (F : Fr) {Γ : RCtx} {τ : STy} (e : RExpr E Γ τ), Below (evalE G F n e) (evalE G F (n + 1) e)
  evalPair : ∀ (F : Fr) {Γ : RCtx} {σ τ : STy} (a : RExpr E Γ σ) (b : RExpr E Γ τ),
    Below (evalPair G F n a b) (evalPair G F (n + 1) a b)
  evalArgs : ∀ (F : Fr) {Γ : RCtx} {τs : List STy} (es : RArgs E Γ τs),
    Below (evalArgs G F n es) (evalArgs G F (n + 1) es)
  evalConvArgs : ∀ (F : Fr) {Γ : RCtx} {τs : List STy} (es : RConvArgs E Γ τs),
    Below (evalConvArgs G F n es) (evalConvArgs G F (n + 1) es)
  evalLoc : ∀ (F : Fr) {Γ : RCtx} {τ : STy} (l : RLVal E Γ τ), Below (evalLoc G F n l) (evalLoc G F (n + 1) l)
  evalBuiltin : ∀ (F : Fr) {Γ : RCtx} {σs : List STy} (b : Builtin) (args : RArgs E Γ σs) (τ : STy),
    Below (evalBuiltin G F n b args τ) (evalBuiltin G F (n + 1) b args τ)
  evalArgsRev : ∀ (F : Fr) {Γ : RCtx} {τs : List STy} (es : RArgs E Γ τs),
    Below (evalArgsRev G F n es) (evalArgsRev G F (n + 1) es)
  pay : ∀ (F : Fr) {Γ : RCtx} (a : RExpr E Γ (.address true)) (v : RExpr E Γ (.int IntTy.u256)),
    Below (pay G F n a v) (pay G F (n + 1) a v)
  execS : ∀ (F : Fr) (nps : Nat) (ph : Option (Ph E)) {R : List STy} {M : Bool} {k : SCtx} {Γ Γ' : RCtx}
    (s : RStmt E R M k Γ Γ') (l : Locals E.layout Γ),
    Below (execS G F n nps ph s l) (execS G F (n + 1) nps ph s l)
  forIter : ∀ (F : Fr) (nps : Nat) (ph : Option (Ph E)) {R : List STy} {M u : Bool} {Γ₁ Γ₂ : RCtx}
    (c : ROptBool E Γ₁) (post : ROptExpr E Γ₁) (body : RStmt E R M ⟨true, u⟩ Γ₁ Γ₂) (l : Locals E.layout Γ₁),
    Below (forIter G F n nps ph c post body l) (forIter G F (n + 1) nps ph c post body l)
  execItems : ∀ (F : Fr) (nps : Nat) (ph : Option (Ph E)) {R : List STy} {M : Bool} {k : SCtx} {Γ Γ' : RCtx}
    (b : RItems E R M k Γ Γ') (l : Locals E.layout Γ),
    Below (execItems G F n nps ph b l) (execItems G F (n + 1) nps ph b l)
  runMods : ∀ (F : Fr) (b : RBody E) (mods : List (RModInv E b.locals)) (l : Locals E.layout b.locals),
    Below (runMods G F n b mods l) (runMods G F (n + 1) b mods l)
  callInternal : ∀ (F : Fr) (d : Decl) {ps : List STy} (vs : Vals E.layout ps) (rs : List STy),
    Below (callInternal G F n d vs rs) (callInternal G F (n + 1) d vs rs)
  callAddr : ∀ (F : Fr) (a : Solidity.Roadmap.Address) (v : Solidity.Roadmap.Word) (input : Solidity.Roadmap.Bytes)
    (static : Bool), Below (callAddr G F n a v input static) (callAddr G F (n + 1) a v input static)
  enterInstance : ∀ (a sender : Solidity.Roadmap.Address) (v : Solidity.Roadmap.Word) (input : Solidity.Roadmap.Bytes)
    (static : Bool) (c : String) (depth : Nat) (m : Nat × Nat × Heap E.layout),
    Below (enterInstance G n a sender v input static c depth m)
      (enterInstance G (n + 1) a sender v input static c depth m)
  envLoop : ∀ (depth : Nat) (pstatic : Bool), Below (envLoop G n depth pstatic) (envLoop G (n + 1) depth pstatic)
  dispatch : ∀ (F : Fr) (input : Solidity.Roadmap.Bytes), Below (dispatch G F n input) (dispatch G F (n + 1) input)

theorem belowAt_zero : BelowAt G 0 where
  evalE _ _ _ _ := by rw [evalE.eq_1]; exact Below.timeout _
  evalPair _ _ _ _ _ _ := by rw [evalPair.eq_1]; exact Below.timeout _
  evalArgs _ _ _ _ := by rw [evalArgs.eq_1]; exact Below.timeout _
  evalConvArgs _ _ _ _ := by rw [evalConvArgs.eq_1]; exact Below.timeout _
  evalLoc _ _ _ _ := by rw [evalLoc.eq_1]; exact Below.timeout _
  evalBuiltin _ _ _ _ _ _ := by rw [evalBuiltin.eq_1]; exact Below.timeout _
  evalArgsRev _ _ _ _ := by rw [evalArgsRev.eq_1]; exact Below.timeout _
  pay _ _ _ _ := by rw [pay.eq_1]; exact Below.timeout _
  execS _ _ _ _ _ _ _ _ _ _ := by rw [execS.eq_1]; exact Below.timeout _
  forIter _ _ _ _ _ _ _ _ _ _ _ _ := by rw [forIter.eq_1]; exact Below.timeout _
  execItems _ _ _ _ _ _ _ _ _ _ := by rw [execItems.eq_1]; exact Below.timeout _
  runMods _ _ _ _ := by rw [runMods.eq_1]; exact Below.timeout _
  callInternal _ _ _ _ _ := by rw [callInternal.eq_1]; exact Below.timeout _
  callAddr _ _ _ _ _ := by rw [callAddr.eq_1]; exact Below.timeout _
  enterInstance _ _ _ _ _ _ _ _ := by rw [enterInstance.eq_1]; exact Below.timeout _
  envLoop _ _ := by rw [envLoop.eq_1]; exact Below.timeout _
  dispatch _ _ := by rw [dispatch.eq_1]; exact Below.timeout _

variable {G} {n : Nat}

theorem evalE_step (ih : BelowAt G n) (F : Fr) {Γ : RCtx} {τ : STy} (e : RExpr E Γ τ) :
    Below (evalE G F (n + 1) e) (evalE G F (n + 1 + 1) e) := by
  cases e <;> below_unfold evalE n <;> below_go [ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, convRV_below, convExplicitRV_below, bytesOfRV_below, encodeVals_below, writeLoc_below, deleteLoc_below, keyStep_below, zeroVals_below, zeroInner_below, zeroVal_below, getterPath_below, copyInto_below, Below.sub]
theorem evalPair_step (ih : BelowAt G n) (F : Fr) {Γ : RCtx} {σ τ : STy} (a : RExpr E Γ σ) (b : RExpr E Γ τ) :
    Below (evalPair G F (n + 1) a b) (evalPair G F (n + 1 + 1) a b) := by
  below_unfold evalPair n
  below_go [ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, convRV_below, convExplicitRV_below, bytesOfRV_below, encodeVals_below, writeLoc_below, deleteLoc_below, keyStep_below, zeroVals_below, zeroInner_below, zeroVal_below, getterPath_below, copyInto_below, Below.sub]
theorem evalArgs_step (ih : BelowAt G n) (F : Fr) {Γ : RCtx} {τs : List STy} (es : RArgs E Γ τs) :
    Below (evalArgs G F (n + 1) es) (evalArgs G F (n + 1 + 1) es) := by
  cases es <;> below_unfold evalArgs n <;> below_go [ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, convRV_below, convExplicitRV_below, bytesOfRV_below, encodeVals_below, writeLoc_below, deleteLoc_below, keyStep_below, zeroVals_below, zeroInner_below, zeroVal_below, getterPath_below, copyInto_below, Below.sub]
theorem evalConvArgs_step (ih : BelowAt G n) (F : Fr) {Γ : RCtx} {τs : List STy} (es : RConvArgs E Γ τs) :
    Below (evalConvArgs G F (n + 1) es) (evalConvArgs G F (n + 1 + 1) es) := by
  cases es <;> below_unfold evalConvArgs n <;> below_go [ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, convRV_below, convExplicitRV_below, bytesOfRV_below, encodeVals_below, writeLoc_below, deleteLoc_below, keyStep_below, zeroVals_below, zeroInner_below, zeroVal_below, getterPath_below, copyInto_below, Below.sub]
theorem evalLoc_step (ih : BelowAt G n) (F : Fr) {Γ : RCtx} {τ : STy} (l : RLVal E Γ τ) :
    Below (evalLoc G F (n + 1) l) (evalLoc G F (n + 1 + 1) l) := by
  cases l <;> below_unfold evalLoc n <;> below_go [ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, convRV_below, convExplicitRV_below, bytesOfRV_below, encodeVals_below, writeLoc_below, deleteLoc_below, keyStep_below, zeroVals_below, zeroInner_below, zeroVal_below, getterPath_below, copyInto_below, Below.sub]
theorem evalBuiltin_step (ih : BelowAt G n) (F : Fr) {Γ : RCtx} {σs : List STy} (b : Builtin)
    (args : RArgs E Γ σs) (τ : STy) :
    Below (evalBuiltin G F (n + 1) b args τ) (evalBuiltin G F (n + 1 + 1) b args τ) := by
  below_unfold evalBuiltin n
  below_go [ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, convRV_below, convExplicitRV_below, bytesOfRV_below, encodeVals_below, writeLoc_below, deleteLoc_below, keyStep_below, zeroVals_below, zeroInner_below, zeroVal_below, getterPath_below, copyInto_below, Below.sub]
theorem evalArgsRev_step (ih : BelowAt G n) (F : Fr) {Γ : RCtx} {τs : List STy} (es : RArgs E Γ τs) :
    Below (evalArgsRev G F (n + 1) es) (evalArgsRev G F (n + 1 + 1) es) := by
  cases es <;> below_unfold evalArgsRev n <;> below_go [ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, convRV_below, convExplicitRV_below, bytesOfRV_below, encodeVals_below, writeLoc_below, deleteLoc_below, keyStep_below, zeroVals_below, zeroInner_below, zeroVal_below, getterPath_below, copyInto_below, Below.sub]
theorem pay_step (ih : BelowAt G n) (F : Fr) {Γ : RCtx} (a : RExpr E Γ (.address true))
    (v : RExpr E Γ (.int IntTy.u256)) : Below (pay G F (n + 1) a v) (pay G F (n + 1 + 1) a v) := by
  below_unfold pay n
  below_go [ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, convRV_below, convExplicitRV_below, bytesOfRV_below, encodeVals_below, writeLoc_below, deleteLoc_below, keyStep_below, zeroVals_below, zeroInner_below, zeroVal_below, getterPath_below, copyInto_below, Below.sub]
theorem execS_step (ih : BelowAt G n) (F : Fr) (nps : Nat) (ph : Option (Ph E)) {R : List STy} {M : Bool}
    {k : SCtx} {Γ Γ' : RCtx} (s : RStmt E R M k Γ Γ') (l : Locals E.layout Γ) :
    Below (execS G F (n + 1) nps ph s l) (execS G F (n + 1 + 1) nps ph s l) := by
  cases s <;> below_unfold execS n <;> below_go [ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, convRV_below, convExplicitRV_below, bytesOfRV_below, encodeVals_below, writeLoc_below, deleteLoc_below, keyStep_below, zeroVals_below, zeroInner_below, zeroVal_below, getterPath_below, copyInto_below, Below.sub]
theorem forIter_step (ih : BelowAt G n) (F : Fr) (nps : Nat) (ph : Option (Ph E)) {R : List STy} {M u : Bool}
    {Γ₁ Γ₂ : RCtx} (c : ROptBool E Γ₁) (post : ROptExpr E Γ₁) (body : RStmt E R M ⟨true, u⟩ Γ₁ Γ₂)
    (l : Locals E.layout Γ₁) :
    Below (forIter G F (n + 1) nps ph c post body l) (forIter G F (n + 1 + 1) nps ph c post body l) := by
  cases c <;> below_unfold forIter n <;> below_go [ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, convRV_below, convExplicitRV_below, bytesOfRV_below, encodeVals_below, writeLoc_below, deleteLoc_below, keyStep_below, zeroVals_below, zeroInner_below, zeroVal_below, getterPath_below, copyInto_below, Below.sub]
theorem execItems_step (ih : BelowAt G n) (F : Fr) (nps : Nat) (ph : Option (Ph E)) {R : List STy} {M : Bool}
    {k : SCtx} {Γ Γ' : RCtx} (b : RItems E R M k Γ Γ') (l : Locals E.layout Γ) :
    Below (execItems G F (n + 1) nps ph b l) (execItems G F (n + 1 + 1) nps ph b l) := by
  cases b <;> below_unfold execItems n <;> below_go [ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, convRV_below, convExplicitRV_below, bytesOfRV_below, encodeVals_below, writeLoc_below, deleteLoc_below, keyStep_below, zeroVals_below, zeroInner_below, zeroVal_below, getterPath_below, copyInto_below, Below.sub]
theorem runMods_step (ih : BelowAt G n) (F : Fr) (b : RBody E) (mods : List (RModInv E b.locals))
    (l : Locals E.layout b.locals) : Below (runMods G F (n + 1) b mods l) (runMods G F (n + 1 + 1) b mods l) := by
  cases mods with
  | nil => below_unfold runMods n; below_go [ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, convRV_below, convExplicitRV_below, bytesOfRV_below, encodeVals_below, writeLoc_below, deleteLoc_below, keyStep_below, zeroVals_below, zeroInner_below, zeroVal_below, getterPath_below, copyInto_below, Below.sub]
  | cons md rest =>
    below_unfold runMods n
    refine Below.bind (Below.sub _ (ih.evalConvArgs _ _)) fun p => ?_
    split
    · exact Below.refl _
    · split
      · refine Below.bind (Below.refl _) fun s => ?_
        refine Below.bind (Below.refl _) fun _ => ?_
        refine Below.attempt_bind (ih.execItems _ _ _ _ _) (fun r => ?_) (fun x => ?_)
        · below_go [ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, convRV_below, convExplicitRV_below, bytesOfRV_below, encodeVals_below, writeLoc_below, deleteLoc_below, keyStep_below, zeroVals_below, zeroInner_below, zeroVal_below, getterPath_below, copyInto_below, Below.sub]
        · rfl
      · exact Below.refl _
theorem callInternal_step (ih : BelowAt G n) (F : Fr) (d : Decl) {ps : List STy} (vs : Vals E.layout ps)
    (rs : List STy) : Below (callInternal G F (n + 1) d vs rs) (callInternal G F (n + 1 + 1) d vs rs) := by
  below_unfold callInternal n
  below_go [ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, convRV_below, convExplicitRV_below, bytesOfRV_below, encodeVals_below, writeLoc_below, deleteLoc_below, keyStep_below, zeroVals_below, zeroInner_below, zeroVal_below, getterPath_below, copyInto_below, Below.sub]
theorem callAddr_step (ih : BelowAt G n) (F : Fr) (a : Solidity.Roadmap.Address) (v : Solidity.Roadmap.Word)
    (input : Solidity.Roadmap.Bytes) (static : Bool) :
    Below (callAddr G F (n + 1) a v input static) (callAddr G F (n + 1 + 1) a v input static) := by
  below_unfold callAddr n
  below_go [ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, convRV_below, convExplicitRV_below, bytesOfRV_below, encodeVals_below, writeLoc_below, deleteLoc_below, keyStep_below, zeroVals_below, zeroInner_below, zeroVal_below, getterPath_below, copyInto_below, Below.sub]
theorem enterInstance_step (ih : BelowAt G n) (a sender : Solidity.Roadmap.Address) (v : Solidity.Roadmap.Word)
    (input : Solidity.Roadmap.Bytes) (static : Bool) (c : String) (depth : Nat) (m : Nat × Nat × Heap E.layout) :
    Below (enterInstance G (n + 1) a sender v input static c depth m)
      (enterInstance G (n + 1 + 1) a sender v input static c depth m) := by
  below_unfold enterInstance n
  refine Below.bind (Below.refl _) fun _ => ?_
  refine Below.attempt_bind (ih.dispatch _ _) (fun r => ?_) (fun x => ?_)
  · exact Below.refl _
  · rfl
theorem envLoop_step (ih : BelowAt G n) (depth : Nat) (pstatic : Bool) :
    Below (envLoop G (n + 1) depth pstatic) (envLoop G (n + 1 + 1) depth pstatic) := by
  below_unfold envLoop n
  below_go [ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, convRV_below, convExplicitRV_below, bytesOfRV_below, encodeVals_below, writeLoc_below, deleteLoc_below, keyStep_below, zeroVals_below, zeroInner_below, zeroVal_below, getterPath_below, copyInto_below, Below.sub]
theorem dispatch_step (ih : BelowAt G n) (F : Fr) (input : Solidity.Roadmap.Bytes) :
    Below (dispatch G F (n + 1) input) (dispatch G F (n + 1 + 1) input) := by
  below_unfold dispatch n
  below_go [ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, convRV_below, convExplicitRV_below, bytesOfRV_below, encodeVals_below, writeLoc_below, deleteLoc_below, keyStep_below, zeroVals_below, zeroInner_below, zeroVal_below, getterPath_below, copyInto_below, Below.sub]

/-- **Every interpreter function is monotone in its horizon.** -/
theorem belowAt (G : Glob E) : ∀ n, BelowAt G n
  | 0 => belowAt_zero G
  | n + 1 =>
    have ih := belowAt G n
    ⟨evalE_step ih, evalPair_step ih, evalArgs_step ih, evalConvArgs_step ih, evalLoc_step ih,
      evalBuiltin_step ih, evalArgsRev_step ih, pay_step ih, execS_step ih, forIter_step ih,
      execItems_step ih, runMods_step ih, callInternal_step ih, callAddr_step ih, enterInstance_step ih,
      envLoop_step ih, dispatch_step ih⟩

end


/-! ### Transactions -/

theorem Below.forIn {Γ : RCtx} {α β : Type} (l : List α) (b : β) {f f' : α → β → EM E Γ (ForInStep β)}
    (h : ∀ a b, Below (f a b) (f' a b)) : Below (forIn l b f) (forIn l b f') := by
  induction l generalizing b with
  | nil => exact Below.refl _
  | cons a as ih =>
    simp only [List.forIn_cons]
    refine Below.bind (h a b) fun r => ?_
    cases r with
    | done _ => exact Below.refl _
    | yield b' => exact ih b'

theorem storeRV_below {Γ : RCtx} (F : Fr) (n : Nat) (τ : STy) (p : SPath) {σ : STy} (v : RVal E.layout σ) :
    Below (storeRV (Γ := Γ) F n τ p v) (storeRV F (n + 1) τ p v) := by
  unfold storeRV
  below_go [storeVal_below, storeData_below]

theorem runInits_below (G : Glob E) (F : Fr) (n : Nat) : ∀ (l : List (RInit E)),
    Below (runInits G F n l) (runInits G F (n + 1) l)
  | [] => Below.refl _
  | ri :: rest => Below.bind (Below.sub _ ((belowAt G n).evalE F _)) fun _ =>
      Below.bind (storeRV_below F n _ _ _) fun _ => runInits_below G F n rest

theorem giveArgs_below (G : Glob E) (F : Fr) (n : Nat) (X : String) (lX : Locals E.layout (G.prog.ctorLocals X)) :
    ∀ (bs : List (RBaseArg E (G.prog.ctorLocals X))) (acc : CtorLocals G),
      Below (giveArgs G F n X lX bs acc) (giveArgs G F (n + 1) X lX bs acc)
  | [], _ => Below.refl _
  | ba :: rest, acc => by
    simp only [giveArgs]
    split
    · exact giveArgs_below G F n X lX rest acc
    · refine Below.bind (Below.sub _ ((belowAt G n).evalConvArgs F _)) fun _ => ?_
      split
      · exact giveArgs_below G F n X lX rest _
      · exact Below.refl _

theorem collectArgs_below (G : Glob E) (F : Fr) (n : Nat) : ∀ (Xs : List String) (acc : CtorLocals G),
    Below (collectArgs G F n Xs acc) (collectArgs G F (n + 1) Xs acc)
  | [], _ => Below.refl _
  | X :: Xs, acc => Below.bind (Below.refl _) fun lX =>
      Below.bind (giveArgs_below G F n X lX _ acc) fun acc' => collectArgs_below G F n Xs acc'

theorem runCtorBody_below (G : Glob E) (F : Fr) (n : Nat) (acc : CtorLocals G) (X : String) :
    Below (runCtorBody G F n acc X) (runCtorBody G F (n + 1) acc X) := by
  have ih := belowAt G n
  unfold runCtorBody
  below_go [ih.evalE, ih.evalConvArgs, ih.runMods, ih.dispatch, storeRV_below, runInits_below, giveArgs_below, collectArgs_below, runCtorBody_below, construct_below, Below.sub]

theorem construct_below (G : Glob E) (F : Fr) (n : Nat) (c : String) (lc : Locals E.layout (G.prog.ctorLocals c)) :
    Below (construct G F n c lc) (construct G F (n + 1) c lc) := by
  unfold construct
  split
  · refine Below.bind (Below.forIn _ _ fun X _ => Below.bind (runInits_below G F n _) fun _ => Below.refl _)
      fun _ => ?_
    refine Below.bind (collectArgs_below G F n _ _) fun acc => ?_
    exact Below.bind (Below.forIn _ _ fun X _ => Below.bind (runCtorBody_below G F n acc X) fun _ => Below.refl _)
      fun _ => Below.refl _
  · refine Below.bind (collectArgs_below G F n _ _) fun acc => ?_
    exact Below.bind (Below.forIn _ _ fun X _ => Below.bind (runInits_below G F n _) fun _ =>
      Below.bind (runCtorBody_below G F n acc X) fun _ => Below.refl _) fun _ => Below.refl _

theorem deploy_below (G : Glob E) (n : Nat) (c : String) (addr sender : Address) (value : Word) (args : Bytes) :
    Below (deploy G n c addr sender value args) (deploy G (n + 1) c addr sender value args) := by
  unfold deploy
  dsimp only
  refine Below.bind (Below.refl _) fun m => ?_
  refine Below.bind (Below.refl _) fun s => ?_
  split <;> refine Below.bind (Below.refl _) fun _ => ?_ <;>
    refine Below.attempt_bind ?_ (fun _ => Below.refl _) (fun _ => rfl) <;>
    split <;> refine Below.bind (Below.refl _) fun _ => ?_ <;> refine Below.bind (Below.refl _) fun _ => ?_ <;>
    split <;> first | exact construct_below G _ n c _ | exact Below.refl _

theorem runTx_below (G : Glob E) (n : Nat) (q : Request) :
    Below (runTx G n q) (runTx G (n + 1) q) := by
  have ih := belowAt { G with timestamp := q.timestamp } n
  unfold runTx
  dsimp only
  refine Below.bind (Below.refl _) fun m => ?_
  refine Below.bind (Below.refl _) fun oc => ?_
  split
  · exact Below.refl _
  · refine Below.attempt_bind ?_ (fun _ => Below.refl _) (fun _ => rfl)
    exact Below.bind (Below.refl _) fun _ => ih.dispatch _ _

/-! ## Horizon independence -/

theorem Below.trans {Γ : RCtx} {α : Type} {a b c : EM E Γ α} (h₁ : Below a b) (h₂ : Below b c) : Below a c := by
  intro x
  rcases h₁ x with ht | he
  · exact .inl ht
  · rw [he]
    rcases h₂ x with ht | he'
    · exact .inl (he ▸ ht)
    · exact .inr he'

/-- A family monotone at each step is monotone. -/
theorem Below.mono {Γ : RCtx} {α : Type} {f : Nat → EM E Γ α} (h : ∀ n, Below (f n) (f (n + 1)))
    {n m : Nat} (hnm : n ≤ m) : Below (f n) (f m) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hnm
  induction d with
  | zero => exact Below.refl _
  | succ d ih => exact (ih (by omega)).trans (h _)

/-- A run that does not time out is the run at every larger horizon. -/
theorem Below.eq_of_done {Γ : RCtx} {α : Type} {m m' : EM E Γ α} (h : Below m m') (x)
    (hd : (m.run x).1 ≠ .error .timeout) : m'.run x = m.run x :=
  match h x with
  | .inl ht => absurd ht hd
  | .inr he => he.symm

theorem done_iff {α σ : Type} (r : Except Halt α × σ) : Done r = true ↔ r.1 ≠ .error .timeout := by
  rcases r with ⟨r, s⟩
  cases r with
  | ok a => exact ⟨(fun _ h => nomatch h), (fun _ => rfl)⟩
  | error h =>
    cases h with
    | timeout => exact ⟨(fun h => nomatch h), (fun h => absurd rfl h)⟩
    | revert _ => exact ⟨(fun _ h => nomatch h), (fun _ => rfl)⟩
    | stuck _ => exact ⟨(fun _ h => nomatch h), (fun _ => rfl)⟩

/-- **Horizon independence** of a monotone family: a result that
completes at horizon `k` is the result at every horizon `k' ≥ k`. -/
theorem runAt_stable {α : Type} {m : Nat → EM E [] α} (hm : ∀ n, Below (m n) (m (n + 1))) (s : St E)
    {k k' : Nat} (hk : k ≤ k') (hd : Done (runAt m s k) = true) : runAt m s k' = runAt m s k := by
  have hb := Below.mono hm hk
  have hd' : ((m k).run (L0 E, s)).1 ≠ .error .timeout := by
    have := (done_iff _).mp hd
    simp only [runAt] at this
    rcases hr : (m k).run (L0 E, s) with ⟨r, l, s'⟩
    rw [hr] at this
    exact this
  simp only [runAt]
  rw [hb.eq_of_done _ hd']

/-- **A transaction's result does not depend on its horizon** once it
completes. -/
theorem runTx_stable (G : Glob E) (q : Request) (s : St E) {k k' : Nat} (hk : k ≤ k')
    (hd : Done (runAt (fun f => runTx G f q) s k) = true) :
    runAt (fun f => runTx G f q) s k' = runAt (fun f => runTx G f q) s k :=
  runAt_stable (fun n => runTx_below G n q) s hk hd

/-- So does a deployment's. -/
theorem deploy_stable (G : Glob E) (c : String) (addr sender : Address) (value : Word) (args : Bytes)
    (s : St E) {k k' : Nat} (hk : k ≤ k')
    (hd : Done (runAt (fun f => deploy G f c addr sender value args) s k) = true) :
    runAt (fun f => deploy G f c addr sender value args) s k' =
      runAt (fun f => deploy G f c addr sender value args) s k :=
  runAt_stable (fun n => deploy_below G n c addr sender value args) s hk hd

/-- **The least completing horizon is not a choice**: what `firstDone`
finds is the run at every horizon from there on, so a transaction's
meaning in a session is its result at any completing horizon. -/
theorem firstDone_runTx (G : Glob E) (q : Request) (s : St E) {n k k' : Nat}
    {r : Except Halt Outcome × St E} (h : firstDone (runAt (fun f => runTx G f q) s) n = some (k, r))
    (hk : k ≤ k') : runAt (fun f => runTx G f q) s k' = r := by
  obtain ⟨_, rfl, hd⟩ := firstDone_spec h
  exact runTx_stable G q s hk hd

/-- A stuck transaction is stuck at every larger horizon: being stuck is
not a lack of horizon. -/
theorem runTx_stuck_stable (G : Glob E) (q : Request) (s : St E) {k k' : Nat} (hk : k ≤ k') {msg : String}
    (h : (runAt (fun f => runTx G f q) s k).1 = .error (.stuck msg)) :
    (runAt (fun f => runTx G f q) s k').1 = .error (.stuck msg) := by
  have hd : Done (runAt (fun f => runTx G f q) s k) = true := by
    rw [done_iff, h]; exact fun h' => nomatch h'
  rw [runTx_stable G q s hk hd, h]

/-! ## Events only grow -/

theorem run_st {Γ : RCtx} (x : Locals E.layout Γ × St E) : (st : EM E Γ (St E)).run x = (.ok x.2, x) := rfl

theorem Grow.get {Γ : RCtx} : Grow (get : EM E Γ (Locals E.layout Γ × St E)) := fun _ => List.prefix_refl _
theorem Grow.st {Γ : RCtx} : Grow (st : EM E Γ (St E)) := fun _ => List.prefix_refl _
theorem Grow.locals {Γ : RCtx} : Grow (locals : EM E Γ (Locals E.layout Γ)) := fun _ => List.prefix_refl _
theorem Grow.setLocals {Γ : RCtx} (l : Locals E.layout Γ) : Grow (setLocals l : EM E Γ Unit) :=
  fun _ => List.prefix_refl _
theorem Grow.modSt {Γ : RCtx} (f : St E → St E) (hf : ∀ s, s.events <+: (f s).events) :
    Grow (modSt f : EM E Γ Unit) := fun x => hf x.2
theorem Grow.lift {Γ : RCtx} {α : Type} (r : R α) : Grow (lift r : EM E Γ α) := by
  cases r <;> exact fun _ => List.prefix_refl _
theorem Grow.sub {Γ Γ' : RCtx} {α : Type} (l' : Locals E.layout Γ') {m : EM E Γ' α} (h : Grow m) :
    Grow (EM.sub (Γ := Γ) l' m) := by
  intro x
  rcases x with ⟨l, s⟩
  rw [run_sub]
  have := h (l', s)
  rcases hr : m.run (l', s) with ⟨r, l'', s'⟩
  rw [hr] at this
  cases r <;> exact this
theorem Grow.attempt {Γ : RCtx} {α : Type} {m : EM E Γ α} (h : Grow m) : Grow (EM.attempt m) := by
  intro x
  rw [run_attempt]
  exact h x

theorem heapPut_grow {Γ : RCtx} (a : Nat) (x : Σ τ, Data E.layout τ) : Grow (heapPut (Γ := Γ) a x) := by
  intro y
  unfold heapPut
  rw [run_bind, run_st]
  dsimp only
  split
  · exact List.prefix_refl _
  · exact List.prefix_refl _

theorem alloc_grow {Γ : RCtx} {τ : STy} (x : Data E.layout τ) : Grow (alloc (Γ := Γ) x) := by
  intro y
  unfold alloc
  rw [run_bind, run_st]
  exact List.prefix_refl _

/-- Close `Grow body`: through binds, `match`es and `if`s, by the given
lemmas at the calls; a `modSt` keeps or appends events. -/
syntax "grow_go" "[" ident,* "]" : tactic
macro_rules
  | `(tactic| grow_go [$ls,*]) => `(tactic| repeat' (first
      | (with_reducible exact Grow.pure _)
      | (with_reducible exact Grow.halt _)
      | (with_reducible exact Grow.st)
      | (with_reducible exact Grow.get)
      | (with_reducible exact Grow.locals)
      | (with_reducible exact Grow.setLocals _)
      | (with_reducible exact Grow.lift _)
      | (with_reducible apply Grow.modSt; intro _; first | exact List.prefix_refl _ | exact List.prefix_append _ _)
      | (first $[| with_reducible apply $ls:ident]*)
      | (with_reducible apply Grow.sub)
      | (with_reducible apply Grow.attempt)
      | (with_reducible apply Grow.map)
      | (refine Grow.bind ?_ ?_)
      | (with_reducible intro _)
      | split
      | (intro _; exact List.prefix_refl _)
      | (dsimp only)))

section
variable {Γ : RCtx}

theorem getV_grow {τ : STy} (v : RVal E.layout τ) : Grow (getV (Γ := Γ) v) := Grow.lift _
theorem readCell_grow (F : Fr) (p : SPath) : Grow (readCell (E := E) (Γ := Γ) F p) := by
  unfold readCell; grow_go []
theorem readAt_grow (F : Fr) (p : SPath) (τ : STy) : Grow (readAt (E := E) (Γ := Γ) F p τ) := by
  unfold readAt; grow_go [readCell_grow]
theorem applyOp_grow (F : Fr) (o : Op E.layout E.lay E.lay) : Grow (applyOp (Γ := Γ) F o) := by
  unfold applyOp; grow_go []
theorem setCell_grow (F : Fr) (p : SPath) (o : Option (Val E.layout (E.cellTy p))) :
    Grow (setCell (Γ := Γ) F p o) := by
  unfold setCell; grow_go [applyOp_grow]
theorem writeAt_grow {τ : STy} (F : Fr) (p : SPath) (v : Val E.layout τ) : Grow (writeAt (Γ := Γ) F p v) := by
  unfold writeAt; grow_go [setCell_grow]
theorem readLen_grow (F : Fr) (p : SPath) : Grow (readLen (E := E) (Γ := Γ) F p) := by
  unfold readLen; grow_go [readAt_grow]
theorem writeLen_grow (F : Fr) (p : SPath) (k : Nat) : Grow (writeLen (E := E) (Γ := Γ) F p k) := by
  unfold writeLen; grow_go [writeAt_grow]
theorem heapObj_grow (a : Nat) : Grow (heapObj (E := E) (Γ := Γ) a) := by
  unfold heapObj; grow_go []
theorem heapAt_grow (a : Nat) (τ : STy) : Grow (heapAt (E := E) (Γ := Γ) a τ) := by
  unfold heapAt; grow_go [heapObj_grow]
theorem heapBytes_grow (a : Nat) : Grow (heapBytes (E := E) (Γ := Γ) a) := by
  unfold heapBytes; grow_go [heapObj_grow]
theorem allocRef_grow {τ : STy} (x : Data E.layout τ) : Grow (allocRef (Γ := Γ) x) := by
  unfold allocRef; grow_go [alloc_grow]
theorem storRef_grow (τ : STy) (p : SPath) : Grow (storRef (E := E) (Γ := Γ) τ p) := by
  unfold storRef; grow_go []

end

section
variable {Γ : RCtx}

mutual
theorem zeroData_grow : ∀ (n : Nat) (τ : STy), Grow (zeroData (E := E) (Γ := Γ) n τ)
  | 0, _ => Grow.halt _
  | n + 1, τ => by
    simp only [zeroData]
    grow_go [zeroElems_grow, zeroFields_grow, zeroVal_grow, heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow]
theorem zeroVal_grow : ∀ (n : Nat) (τ : STy), Grow (zeroVal (E := E) (Γ := Γ) n τ)
  | 0, _ => Grow.halt _
  | n + 1, τ => by
    simp only [zeroVal]
    grow_go [zeroData_grow, heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow]
theorem zeroElems_grow : ∀ (n : Nat) (σ : STy) (m : Nat), Grow (zeroElems (E := E) (Γ := Γ) n σ m)
  | 0, _, m => by cases m <;> exact Grow.halt _
  | n + 1, _, 0 => Grow.pure _
  | n + 1, σ, m + 1 => Grow.bind (zeroVal_grow n σ) fun _ => Grow.bind (zeroElems_grow n σ m) fun _ => Grow.pure _
theorem zeroFields_grow : ∀ (n : Nat) (τs : List STy), Grow (zeroFields (E := E) (Γ := Γ) n τs)
  | 0, τs => by cases τs <;> exact Grow.halt _
  | n + 1, [] => Grow.pure _
  | n + 1, τ :: τs => Grow.bind (zeroVal_grow n τ) fun _ => Grow.bind (zeroFields_grow n τs) fun _ => Grow.pure _
end

mutual
theorem loadMem_grow (F : Fr) : ∀ (n : Nat) (τ : STy) (p : SPath), Grow (loadMem (E := E) (Γ := Γ) F n τ p)
  | 0, _, _ => Grow.halt _
  | n + 1, τ, p => by
    simp only [loadMem]
    grow_go [loadBytes_grow, loadElems_grow, loadFields_grow, heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow]
theorem loadElem_grow (F : Fr) : ∀ (n : Nat) (τ : STy) (p : SPath), Grow (loadElem (E := E) (Γ := Γ) F n τ p)
  | 0, _, _ => Grow.halt _
  | n + 1, τ, p => by
    simp only [loadElem]
    grow_go [loadMem_grow, heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow]
theorem loadElems_grow (F : Fr) : ∀ (n : Nat) (σ : STy) (p : SPath) (i m : Nat),
    Grow (loadElems (E := E) (Γ := Γ) F n σ p i m)
  | 0, _, _, _, m => by cases m <;> exact Grow.halt _
  | n + 1, _, _, _, 0 => Grow.pure _
  | n + 1, σ, p, i, m + 1 => Grow.bind (loadElem_grow F n σ _) fun _ =>
      Grow.bind (loadElems_grow F n σ p (i + 1) m) fun _ => Grow.pure _
theorem loadFields_grow (F : Fr) : ∀ (n : Nat) (τs : List STy) (p : SPath) (i : Nat),
    Grow (loadFields (E := E) (Γ := Γ) F n τs p i)
  | 0, τs, _, _ => by cases τs <;> exact Grow.halt _
  | n + 1, [], _, _ => Grow.pure _
  | n + 1, τ :: τs, p, i => Grow.bind (loadElem_grow F n τ _) fun _ =>
      Grow.bind (loadFields_grow F n τs p (i + 1)) fun _ => Grow.pure _
theorem loadBytes_grow (F : Fr) : ∀ (n : Nat) (p : SPath) (i k : Nat), Grow (loadBytes (E := E) (Γ := Γ) F n p i k)
  | 0, _, _, k => by cases k <;> exact Grow.halt _
  | n + 1, _, _, 0 => Grow.pure _
  | n + 1, p, i, k + 1 => by
    refine Grow.bind (readAt_grow F _ _) fun v => ?_
    cases v <;> first
      | exact Grow.bind (loadBytes_grow F n p (i + 1) k) fun _ => Grow.pure _
      | (rename_i h; cases h)
end

mutual
theorem deleteStor_grow (F : Fr) : ∀ (n : Nat) (τ : STy) (p : SPath), Grow (deleteStor (E := E) (Γ := Γ) F n τ p)
  | 0, _, _ => Grow.halt _
  | n + 1, τ, p => by
    simp only [deleteStor]
    grow_go [deleteRange_grow, deleteFields_grow, heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow]
theorem deleteRange_grow (F : Fr) : ∀ (n : Nat) (σ : STy) (p : SPath) (i k : Nat),
    Grow (deleteRange (E := E) (Γ := Γ) F n σ p i k)
  | 0, _, _, _, k => by cases k <;> exact Grow.halt _
  | n + 1, _, _, _, 0 => Grow.pure _
  | n + 1, σ, p, i, k + 1 => Grow.bind (deleteStor_grow F n σ _) fun _ => deleteRange_grow F n σ p (i + 1) k
theorem deleteFields_grow (F : Fr) : ∀ (n : Nat) (τs : List STy) (p : SPath) (i : Nat),
    Grow (deleteFields (E := E) (Γ := Γ) F n τs p i)
  | 0, τs, _, _ => by cases τs <;> exact Grow.halt _
  | n + 1, [], _, _ => Grow.pure _
  | n + 1, τ :: τs, p, i => Grow.bind (deleteStor_grow F n τ _) fun _ => deleteFields_grow F n τs p (i + 1)
end

mutual
theorem storeData_grow (F : Fr) : ∀ (n : Nat) (τ : STy) (p : SPath) {σ : STy} (x : Data E.layout σ),
    Grow (storeData (Γ := Γ) F n τ p x)
  | 0, _, _, _, _ => Grow.halt _
  | n + 1, τ, p, _, x => by
    simp only [storeData]
    grow_go [storeBytes_grow, deleteRange_grow, storeElems_grow, storeFields_grow, storeVal_grow, heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow]
theorem storeVal_grow (F : Fr) : ∀ (n : Nat) (τ : STy) (p : SPath) {σ : STy} (v : Val E.layout σ),
    Grow (storeVal (Γ := Γ) F n τ p v)
  | 0, _, _, _, _ => Grow.halt _
  | n + 1, τ, p, _, v => by
    simp only [storeVal]
    grow_go [storeData_grow, loadMem_grow, heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow]
theorem storeElems_grow (F : Fr) : ∀ (n : Nat) (τ : STy) (p : SPath) (i len : Nat) {σ : STy}
    (xs : Fin len → Data E.layout σ), Grow (storeElems (Γ := Γ) F n τ p i len xs)
  | 0, _, _, _, len, _, _ => by cases len <;> exact Grow.halt _
  | n + 1, _, _, _, 0, _, _ => Grow.pure _
  | n + 1, τ, p, i, len + 1, _, xs =>
    Grow.bind (storeData_grow F n τ _ _) fun _ => storeElems_grow F n τ p (i + 1) len _
theorem storeFields_grow (F : Fr) : ∀ (n : Nat) (τs : List STy) (p : SPath) (i : Nat) {σs : List STy}
    (xs : DataList E.layout σs), Grow (storeFields (Γ := Γ) F n τs p i xs)
  | 0, τs, _, _, _, xs => by cases τs <;> cases xs <;> exact Grow.halt _
  | n + 1, [], _, _, _, _ => Grow.pure _
  | n + 1, _ :: _, _, _, _, .nil => Grow.pure _
  | n + 1, τ :: τs, p, i, _, .cons x xs =>
    Grow.bind (storeData_grow F n τ _ x) fun _ => storeFields_grow F n τs p (i + 1) xs
theorem storeBytes_grow (F : Fr) : ∀ (n : Nat) (p : SPath) (i : Nat) (bs : List UInt8),
    Grow (storeBytes (E := E) (Γ := Γ) F n p i bs)
  | 0, _, _, bs => by cases bs <;> exact Grow.halt _
  | n + 1, _, _, [] => Grow.pure _
  | n + 1, p, i, b :: bs => Grow.bind (writeAt_grow F _ _) fun _ => storeBytes_grow F n p (i + 1) bs
end

end

section
variable {Γ : RCtx}

theorem List.mapM_grow {Γ : RCtx} {α β : Type} (f : α → EM E Γ β) (hf : ∀ a, Grow (f a)) :
    ∀ (l : List α), Grow (l.mapM f) := by
  intro l
  suffices h : ∀ (acc : List β), Grow (List.mapM.loop f l acc) from h []
  induction l with
  | nil => intro acc; exact Grow.pure _
  | cons a as ih => intro acc; exact Grow.bind (hf a) fun b => ih (b :: acc)

theorem panicM_grow {α : Type} : Grow (memElem.panicM (E := E) (Γ := Γ) (α := α)) := Grow.lift _
theorem memElem_grow (a i : Nat) (τ : STy) : Grow (memElem (E := E) (Γ := Γ) a i τ) := by
  unfold memElem; grow_go [panicM_grow, heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow]
theorem readLoc_grow (F : Fr) {τ : STy} (loc : Loc E.layout Γ τ) : Grow (readLoc F loc) := by
  cases loc <;> simp only [readLoc] <;> grow_go [memElem_grow, heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow]
theorem memSet_grow (a i : Nat) {τ : STy} (v : Val E.layout τ) : Grow (memSet (Γ := Γ) a i v) := by
  unfold memSet; grow_go [heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow]
theorem lengthOf_grow (F : Fr) {τ : STy} (v : Val E.layout τ) : Grow (lengthOf (Γ := Γ) F v) := by
  unfold lengthOf; grow_go [heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow]
theorem indexLoc_grow (F : Fr) {l : DataLoc} {σ : STy} {k : Option Nat} (a : Val E.layout (.array l σ k))
    (i : Nat) : Grow (indexLoc (Γ := Γ) F a i) := by
  unfold indexLoc; grow_go [lengthOf_grow, heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow]
theorem indexNat_grow {σ : STy} (v : RVal E.layout σ) : Grow (indexNat (Γ := Γ) v) := Grow.lift _
theorem instanceAt_grow (G : Glob E) (a : Address) : Grow (instanceAt (Γ := Γ) G a) := by
  unfold instanceAt; grow_go []
theorem emitEvent_grow (e : Event) : Grow (emitEvent (E := E) (Γ := Γ) e) := by
  unfold emitEvent; grow_go []
theorem credit_grow (a : Address) (v : Word) : Grow (credit (E := E) (Γ := Γ) a v) := by
  unfold credit; grow_go []
theorem debit_grow (a : Address) (v : Word) : Grow (debit (E := E) (Γ := Γ) a v) := by
  unfold debit; grow_go []
theorem mark_grow : Grow (mark (E := E) (Γ := Γ)) := by
  unfold mark; grow_go []
theorem rollbackTo_grow (m : Nat × Nat × Heap E.layout) : Grow (rollbackTo (Γ := Γ) m) := by
  unfold rollbackTo; grow_go []
theorem reraise_grow (o : Outcome) : Grow (reraise (E := E) (Γ := Γ) o) := by
  unfold reraise; grow_go []
theorem fieldsOf_grow : ∀ {ps : List STy} (vs : Vals E.layout ps) (τs : List STy),
    Grow (fieldsOf (E := E) (Γ := Γ) vs τs)
  | _, .nil, [] => Grow.pure _
  | _, .nil, _ :: _ => Grow.halt _
  | _, .cons _ _, [] => Grow.halt _
  | _, .cons (τ := σ) v vs, τ :: τs => by
    simp only [fieldsOf]
    split
    · exact Grow.bind (fieldsOf_grow vs τs) fun _ => Grow.pure _
    · exact Grow.halt _
theorem ret32_grow (τ : STy) (bs : Bytes) : Grow (ret32 (E := E) (Γ := Γ) τ bs) := by
  unfold ret32; grow_go []
theorem tailBytes_grow (data : Bytes) (i : Nat) : Grow (tailBytes (E := E) (Γ := Γ) data i) := by
  unfold tailBytes
  dsimp only
  split
  · exact Grow.pure _
  · exact Grow.halt _
theorem decodeArg_grow (data : Bytes) (i : Nat) (τ : STy) : Grow (decodeArg (E := E) (Γ := Γ) data i τ) := by
  unfold decodeArg
  split
  · split
    · exact Grow.bind (tailBytes_grow data i) fun _ => allocRef_grow _
    · exact Grow.lift _
  · split
    · exact Grow.bind (tailBytes_grow data i) fun _ => allocRef_grow _
    · exact Grow.lift _
  · split
    · split
      · dsimp only
        split
        · exact Grow.bind (List.mapM_grow _ (fun _ => Grow.lift _) _) fun _ => allocRef_grow _
        · exact Grow.halt _
      · exact Grow.halt _
    · exact Grow.lift _
  · exact Grow.lift _
theorem decodeArgs_grow (data : Bytes) : ∀ (τs : List STy) (i : Nat), Grow (decodeArgs (E := E) (Γ := Γ) data τs i)
  | [], _ => Grow.pure _
  | τ :: τs, i => Grow.bind (decodeArg_grow data i τ) fun _ =>
      Grow.bind (decodeArgs_grow data τs (i + 1)) fun _ => Grow.pure _

end

section
variable {Γ : RCtx}

theorem bytesOfRV_grow (F : Fr) (n : Nat) {τ : STy} (v : RVal E.layout τ) : Grow (bytesOfRV (Γ := Γ) F n v) := by
  unfold bytesOfRV; grow_go [heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow]
theorem encodeOne_grow (F : Fr) (n : Nat) (packed : Bool) {τ : STy} (v : RVal E.layout τ) :
    Grow (encodeOne (Γ := Γ) F n packed v) := by
  unfold encodeOne; grow_go [bytesOfRV_grow, heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow]
theorem encodeParts_grow (F : Fr) (n : Nat) (packed : Bool) :
    ∀ {τs : List STy} (vs : RVals E.layout τs), Grow (encodeParts (Γ := Γ) F n packed vs)
  | _, .nil => Grow.pure _
  | _, .cons v vs => Grow.bind (encodeOne_grow F n packed v) fun _ =>
      Grow.bind (encodeParts_grow F n packed vs) fun _ => Grow.pure _
theorem encodeVals_grow (F : Fr) (n : Nat) (packed : Bool) {τs : List STy} (vs : RVals E.layout τs) :
    Grow (encodeVals (Γ := Γ) F n packed vs) := by
  unfold encodeVals; grow_go [encodeParts_grow]
theorem convRV_grow (F : Fr) (n : Nat) {σ : STy} (τ : STy) (v : RVal E.layout σ) :
    Grow (convRV (Γ := Γ) F n τ v) := by
  unfold convRV; grow_go [heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow]
theorem convExplicitRV_grow (F : Fr) (n : Nat) {σ : STy} (τ : STy) (v : RVal E.layout σ) :
    Grow (convExplicitRV (Γ := Γ) F n τ v) := by
  unfold convExplicitRV; grow_go [convRV_grow, bytesOfRV_grow, heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow]
theorem writeLoc_grow (F : Fr) (n : Nat) {τ : STy} (loc : Loc E.layout Γ τ) (v : Val E.layout τ) :
    Grow (writeLoc F n loc v) := by
  unfold writeLoc; grow_go [heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow]
theorem deleteLoc_grow (F : Fr) (n : Nat) {τ : STy} (loc : Loc E.layout Γ τ) : Grow (deleteLoc F n loc) := by
  unfold deleteLoc; grow_go [writeLoc_grow, heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow]
theorem keyStep_grow (F : Fr) (n : Nat) {τ : STy} (k : RVal E.layout τ) : Grow (keyStep (Γ := Γ) F n k) := by
  unfold keyStep; grow_go [bytesOfRV_grow, heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow]
theorem zeroVals_grow (n : Nat) : ∀ (τs : List STy), Grow (zeroVals (E := E) (Γ := Γ) n τs)
  | [] => Grow.pure _
  | τ :: τs => Grow.bind (zeroVal_grow n τ) fun _ => Grow.bind (zeroVals_grow n τs) fun _ => Grow.pure _
theorem zeroInner_grow (n : Nat) : ∀ (k : Nat) {Γ' : RCtx} (l : Locals E.layout Γ'),
    Grow (zeroInner (Γ' := Γ) n k l)
  | 0, _, _ => Grow.pure _
  | _ + 1, _, .nil => Grow.pure _
  | k + 1, _, .cons _ r => Grow.bind (zeroVal_grow n _) fun _ => Grow.bind (zeroInner_grow n k r) fun _ => Grow.pure _
theorem copyInto_grow (F : Fr) (n : Nat) (τ : STy) (p : SPath) {σ : STy} (v : RVal E.layout σ) :
    Grow (copyInto (Γ := Γ) F n τ p v) := by
  unfold copyInto; grow_go [heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow]
theorem extReturn_grow (rs : List STy) (o : Outcome) : Grow (extReturn (E := E) (Γ := Γ) rs o) := by
  unfold extReturn; grow_go [reraise_grow]
theorem getterPath_grow (F : Fr) (n : Nat) (data : Solidity.Roadmap.Bytes) : ∀ (τ : STy) (p : SPath) (i : Nat),
    Grow (getterPath (E := E) (Γ := Γ) F n data τ p i)
  | .mapping k v, p, i => by
    simp only [getterPath]
    grow_go [keyStep_grow, getterPath_grow, extReturn_grow, heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow]
  | .array _ τ len, p, i => by
    simp only [getterPath]
    grow_go [getterPath_grow, extReturn_grow, heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow]
  | .int _, _, _ | .bool, _, _ | .address _, _, _ | .fixedBytes _ _, _, _ | .fixed _, _, _ | .enum _, _, _
  | .udvt _, _, _ | .contract _, _, _ | .bytes _, _, _ | .string _, _, _ | .struct _ _, _, _
  | .fn _ _ _ _, _, _ | .rational _, _, _ | .hexConst _ _, _, _ | .stringLit _, _, _ | .tuple _, _, _ =>
    Grow.pure _

end

theorem Grow.map {Γ : RCtx} {α β : Type} (f : α → β) {m : EM E Γ α} (h : Grow m) : Grow (f <$> m) := by
  intro x
  show x.2.events <+: ((m >>= fun a => (Pure.pure (f a) : EM E Γ β)).run x).2.2.events
  exact Grow.bind h (fun _ => Grow.pure _) x

/-! ### Every interpreter function only appends events -/

structure GrowAt (G : Glob E) (n : Nat) : Prop where
  evalE : ∀ (F : Fr) ⦃Γ : RCtx⦄ ⦃τ : STy⦄ (e : RExpr E Γ τ), Grow (evalE G F n e)
  evalPair : ∀ (F : Fr) ⦃Γ : RCtx⦄ ⦃σ τ : STy⦄ (a : RExpr E Γ σ) (b : RExpr E Γ τ), Grow (evalPair G F n a b)
  evalArgs : ∀ (F : Fr) ⦃Γ : RCtx⦄ ⦃τs : List STy⦄ (es : RArgs E Γ τs), Grow (evalArgs G F n es)
  evalConvArgs : ∀ (F : Fr) ⦃Γ : RCtx⦄ ⦃τs : List STy⦄ (es : RConvArgs E Γ τs), Grow (evalConvArgs G F n es)
  evalLoc : ∀ (F : Fr) ⦃Γ : RCtx⦄ ⦃τ : STy⦄ (l : RLVal E Γ τ), Grow (evalLoc G F n l)
  evalBuiltin : ∀ (F : Fr) ⦃Γ : RCtx⦄ ⦃σs : List STy⦄ (b : Builtin) (args : RArgs E Γ σs) (τ : STy), Grow (evalBuiltin G F n b args τ)
  evalArgsRev : ∀ (F : Fr) ⦃Γ : RCtx⦄ ⦃τs : List STy⦄ (es : RArgs E Γ τs), Grow (evalArgsRev G F n es)
  pay : ∀ (F : Fr) ⦃Γ : RCtx⦄ (a : RExpr E Γ (.address true)) (v : RExpr E Γ (.int IntTy.u256)), Grow (pay G F n a v)
  execS : ∀ (F : Fr) (nps : Nat) (ph : Option (Ph E)) ⦃R : List STy⦄ ⦃M : Bool⦄ ⦃k : SCtx⦄ ⦃Γ Γ' : RCtx⦄ (s : RStmt E R M k Γ Γ') (l : Locals E.layout Γ), Grow (execS G F n nps ph s l)
  forIter : ∀ (F : Fr) (nps : Nat) (ph : Option (Ph E)) ⦃R : List STy⦄ ⦃M u : Bool⦄ ⦃Γ₁ Γ₂ : RCtx⦄ (c : ROptBool E Γ₁) (post : ROptExpr E Γ₁) (body : RStmt E R M ⟨true, u⟩ Γ₁ Γ₂) (l : Locals E.layout Γ₁), Grow (forIter G F n nps ph c post body l)
  execItems : ∀ (F : Fr) (nps : Nat) (ph : Option (Ph E)) ⦃R : List STy⦄ ⦃M : Bool⦄ ⦃k : SCtx⦄ ⦃Γ Γ' : RCtx⦄ (b : RItems E R M k Γ Γ') (l : Locals E.layout Γ), Grow (execItems G F n nps ph b l)
  runMods : ∀ (F : Fr) (b : RBody E) (mods : List (RModInv E b.locals)) (l : Locals E.layout b.locals), Grow (runMods G F n b mods l)
  callInternal : ∀ (F : Fr) (d : Decl) ⦃ps : List STy⦄ (vs : Vals E.layout ps) (rs : List STy), Grow (callInternal G F n d vs rs)
  callAddr : ∀ (F : Fr) (a : Address) (v : Word) (input : Bytes) (static : Bool), Grow (callAddr G F n a v input static)
  enterInstance : ∀ (a sender : Address) (v : Word) (input : Bytes) (static : Bool) (c : String) (depth : Nat) (m : Nat × Nat × Heap E.layout), Grow (enterInstance G n a sender v input static c depth m)
  envLoop : ∀ (depth : Nat) (pstatic : Bool), Grow (envLoop G n depth pstatic)
  dispatch : ∀ (F : Fr) (input : Bytes), Grow (dispatch G F n input)

theorem growAt_zero (G : Glob E) : GrowAt G 0 where
  evalE := by intros; rw [evalE.eq_1]; exact Grow.halt _
  evalPair := by intros; rw [evalPair.eq_1]; exact Grow.halt _
  evalArgs := by intros; rw [evalArgs.eq_1]; exact Grow.halt _
  evalConvArgs := by intros; rw [evalConvArgs.eq_1]; exact Grow.halt _
  evalLoc := by intros; rw [evalLoc.eq_1]; exact Grow.halt _
  evalBuiltin := by intros; rw [evalBuiltin.eq_1]; exact Grow.halt _
  evalArgsRev := by intros; rw [evalArgsRev.eq_1]; exact Grow.halt _
  pay := by intros; rw [pay.eq_1]; exact Grow.halt _
  execS := by intros; rw [execS.eq_1]; exact Grow.halt _
  forIter := by intros; rw [forIter.eq_1]; exact Grow.halt _
  execItems := by intros; rw [execItems.eq_1]; exact Grow.halt _
  runMods := by intros; rw [runMods.eq_1]; exact Grow.halt _
  callInternal := by intros; rw [callInternal.eq_1]; exact Grow.halt _
  callAddr := by intros; rw [callAddr.eq_1]; exact Grow.halt _
  enterInstance := by intros; rw [enterInstance.eq_1]; exact Grow.halt _
  envLoop := by intros; rw [envLoop.eq_1]; exact Grow.halt _
  dispatch := by intros; rw [dispatch.eq_1]; exact Grow.halt _

theorem evalE_grow_0 {G : Glob E} {n : Nat} (ih : GrowAt G n) (F : Fr) {Γ : RCtx} {τ : STy} (e : RExpr E Γ τ)
    (h : 0 ≤ e.ctorIdx ∧ e.ctorIdx < 12) : Grow (evalE G F (n + 1) e) := by
  cases e <;> first | (exfalso; simp only [RExpr.ctorIdx] at h; omega) | (simp only [evalE]; grow_go [ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow, memElem_grow, readLoc_grow, lengthOf_grow, indexLoc_grow, indexNat_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow, fieldsOf_grow, ret32_grow, decodeArgs_grow, bytesOfRV_grow, encodeVals_grow, convRV_grow, convExplicitRV_grow, writeLoc_grow, deleteLoc_grow, keyStep_grow, zeroVals_grow, zeroInner_grow, copyInto_grow, getterPath_grow, extReturn_grow])
theorem evalE_grow_1 {G : Glob E} {n : Nat} (ih : GrowAt G n) (F : Fr) {Γ : RCtx} {τ : STy} (e : RExpr E Γ τ)
    (h : 12 ≤ e.ctorIdx ∧ e.ctorIdx < 24) : Grow (evalE G F (n + 1) e) := by
  cases e <;> first | (exfalso; simp only [RExpr.ctorIdx] at h; omega) | (simp only [evalE]; grow_go [ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow, memElem_grow, readLoc_grow, lengthOf_grow, indexLoc_grow, indexNat_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow, fieldsOf_grow, ret32_grow, decodeArgs_grow, bytesOfRV_grow, encodeVals_grow, convRV_grow, convExplicitRV_grow, writeLoc_grow, deleteLoc_grow, keyStep_grow, zeroVals_grow, zeroInner_grow, copyInto_grow, getterPath_grow, extReturn_grow])
theorem evalE_grow_2 {G : Glob E} {n : Nat} (ih : GrowAt G n) (F : Fr) {Γ : RCtx} {τ : STy} (e : RExpr E Γ τ)
    (h : 24 ≤ e.ctorIdx ∧ e.ctorIdx < 36) : Grow (evalE G F (n + 1) e) := by
  cases e <;> first | (exfalso; simp only [RExpr.ctorIdx] at h; omega) | (simp only [evalE]; grow_go [ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow, memElem_grow, readLoc_grow, lengthOf_grow, indexLoc_grow, indexNat_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow, fieldsOf_grow, ret32_grow, decodeArgs_grow, bytesOfRV_grow, encodeVals_grow, convRV_grow, convExplicitRV_grow, writeLoc_grow, deleteLoc_grow, keyStep_grow, zeroVals_grow, zeroInner_grow, copyInto_grow, getterPath_grow, extReturn_grow])
theorem evalE_grow_3 {G : Glob E} {n : Nat} (ih : GrowAt G n) (F : Fr) {Γ : RCtx} {τ : STy} (e : RExpr E Γ τ)
    (h : 36 ≤ e.ctorIdx ∧ e.ctorIdx < 60) : Grow (evalE G F (n + 1) e) := by
  cases e <;> first | (exfalso; simp only [RExpr.ctorIdx] at h; omega) | (simp only [evalE]; grow_go [ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow, memElem_grow, readLoc_grow, lengthOf_grow, indexLoc_grow, indexNat_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow, fieldsOf_grow, ret32_grow, decodeArgs_grow, bytesOfRV_grow, encodeVals_grow, convRV_grow, convExplicitRV_grow, writeLoc_grow, deleteLoc_grow, keyStep_grow, zeroVals_grow, zeroInner_grow, copyInto_grow, getterPath_grow, extReturn_grow])
theorem evalE_grow_step {G : Glob E} {n : Nat} (ih : GrowAt G n) (F : Fr) {Γ : RCtx} {τ : STy} (e : RExpr E Γ τ) :
    Grow (evalE G F (n + 1) e) := by
  by_cases h0 : e.ctorIdx < 12
  · exact evalE_grow_0 ih F e ⟨Nat.zero_le _, h0⟩
  by_cases h1 : e.ctorIdx < 24
  · exact evalE_grow_1 ih F e ⟨by omega, h1⟩
  by_cases h2 : e.ctorIdx < 36
  · exact evalE_grow_2 ih F e ⟨by omega, h2⟩
  have h3 : e.ctorIdx < 60 := by cases e <;> simp only [RExpr.ctorIdx] <;> omega
  exact evalE_grow_3 ih F e ⟨by omega, h3⟩
theorem evalPair_grow_step {G : Glob E} {n : Nat} (ih : GrowAt G n) (F : Fr) {Γ : RCtx} {σ τ : STy} (a : RExpr E Γ σ) (b : RExpr E Γ τ) :
    Grow (evalPair G F (n + 1) a b) := by
  simp only [evalPair]; grow_go [ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow, memElem_grow, readLoc_grow, lengthOf_grow, indexLoc_grow, indexNat_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow, fieldsOf_grow, ret32_grow, decodeArgs_grow, bytesOfRV_grow, encodeVals_grow, convRV_grow, convExplicitRV_grow, writeLoc_grow, deleteLoc_grow, keyStep_grow, zeroVals_grow, zeroInner_grow, copyInto_grow, getterPath_grow, extReturn_grow]
theorem evalArgs_grow_step {G : Glob E} {n : Nat} (ih : GrowAt G n) (F : Fr) {Γ : RCtx} {τs : List STy} (es : RArgs E Γ τs) :
    Grow (evalArgs G F (n + 1) es) := by
  cases es <;> simp only [evalArgs] <;> grow_go [ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow, memElem_grow, readLoc_grow, lengthOf_grow, indexLoc_grow, indexNat_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow, fieldsOf_grow, ret32_grow, decodeArgs_grow, bytesOfRV_grow, encodeVals_grow, convRV_grow, convExplicitRV_grow, writeLoc_grow, deleteLoc_grow, keyStep_grow, zeroVals_grow, zeroInner_grow, copyInto_grow, getterPath_grow, extReturn_grow]
theorem evalConvArgs_grow_step {G : Glob E} {n : Nat} (ih : GrowAt G n) (F : Fr) {Γ : RCtx} {τs : List STy} (es : RConvArgs E Γ τs) :
    Grow (evalConvArgs G F (n + 1) es) := by
  cases es <;> simp only [evalConvArgs] <;> grow_go [ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow, memElem_grow, readLoc_grow, lengthOf_grow, indexLoc_grow, indexNat_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow, fieldsOf_grow, ret32_grow, decodeArgs_grow, bytesOfRV_grow, encodeVals_grow, convRV_grow, convExplicitRV_grow, writeLoc_grow, deleteLoc_grow, keyStep_grow, zeroVals_grow, zeroInner_grow, copyInto_grow, getterPath_grow, extReturn_grow]
theorem evalLoc_grow_step {G : Glob E} {n : Nat} (ih : GrowAt G n) (F : Fr) {Γ : RCtx} {τ : STy} (l : RLVal E Γ τ) :
    Grow (evalLoc G F (n + 1) l) := by
  cases l <;> simp only [evalLoc] <;> grow_go [ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow, memElem_grow, readLoc_grow, lengthOf_grow, indexLoc_grow, indexNat_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow, fieldsOf_grow, ret32_grow, decodeArgs_grow, bytesOfRV_grow, encodeVals_grow, convRV_grow, convExplicitRV_grow, writeLoc_grow, deleteLoc_grow, keyStep_grow, zeroVals_grow, zeroInner_grow, copyInto_grow, getterPath_grow, extReturn_grow]
theorem evalBuiltin_grow_0 {G : Glob E} {n : Nat} (ih : GrowAt G n) (F : Fr) {Γ : RCtx} {σs : List STy}
    (b : Builtin) (args : RArgs E Γ σs) (τ : STy) (hb : b = .require ∨ b = .assert ∨ b = .revert) :
    Grow (evalBuiltin G F (n + 1) b args τ) := by
  rcases hb with rfl | rfl | rfl <;> simp only [evalBuiltin] <;> grow_go [ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow, memElem_grow, readLoc_grow, lengthOf_grow, indexLoc_grow, indexNat_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow, fieldsOf_grow, ret32_grow, decodeArgs_grow, bytesOfRV_grow, encodeVals_grow, convRV_grow, convExplicitRV_grow, writeLoc_grow, deleteLoc_grow, keyStep_grow, zeroVals_grow, zeroInner_grow, copyInto_grow, getterPath_grow, extReturn_grow]
theorem evalBuiltin_grow_1 {G : Glob E} {n : Nat} (ih : GrowAt G n) (F : Fr) {Γ : RCtx} {σs : List STy}
    (b : Builtin) (args : RArgs E Γ σs) (τ : STy) (hb : b = .keccak256 ∨ b = .sha256 ∨ b = .ripemd160) :
    Grow (evalBuiltin G F (n + 1) b args τ) := by
  rcases hb with rfl | rfl | rfl <;> simp only [evalBuiltin] <;> grow_go [ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow, memElem_grow, readLoc_grow, lengthOf_grow, indexLoc_grow, indexNat_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow, fieldsOf_grow, ret32_grow, decodeArgs_grow, bytesOfRV_grow, encodeVals_grow, convRV_grow, convExplicitRV_grow, writeLoc_grow, deleteLoc_grow, keyStep_grow, zeroVals_grow, zeroInner_grow, copyInto_grow, getterPath_grow, extReturn_grow]
theorem evalBuiltin_grow_2 {G : Glob E} {n : Nat} (ih : GrowAt G n) (F : Fr) {Γ : RCtx} {σs : List STy}
    (b : Builtin) (args : RArgs E Γ σs) (τ : STy) (hb : b = .addmod) :
    Grow (evalBuiltin G F (n + 1) b args τ) := by
  rcases hb with rfl <;> simp only [evalBuiltin] <;> grow_go [ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow, memElem_grow, readLoc_grow, lengthOf_grow, indexLoc_grow, indexNat_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow, fieldsOf_grow, ret32_grow, decodeArgs_grow, bytesOfRV_grow, encodeVals_grow, convRV_grow, convExplicitRV_grow, writeLoc_grow, deleteLoc_grow, keyStep_grow, zeroVals_grow, zeroInner_grow, copyInto_grow, getterPath_grow, extReturn_grow]
theorem evalBuiltin_grow_3 {G : Glob E} {n : Nat} (ih : GrowAt G n) (F : Fr) {Γ : RCtx} {σs : List STy}
    (b : Builtin) (args : RArgs E Γ σs) (τ : STy) (hb : b = .mulmod) :
    Grow (evalBuiltin G F (n + 1) b args τ) := by
  rcases hb with rfl <;> simp only [evalBuiltin] <;> grow_go [ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow, memElem_grow, readLoc_grow, lengthOf_grow, indexLoc_grow, indexNat_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow, fieldsOf_grow, ret32_grow, decodeArgs_grow, bytesOfRV_grow, encodeVals_grow, convRV_grow, convExplicitRV_grow, writeLoc_grow, deleteLoc_grow, keyStep_grow, zeroVals_grow, zeroInner_grow, copyInto_grow, getterPath_grow, extReturn_grow]
theorem evalBuiltin_grow_4 {G : Glob E} {n : Nat} (ih : GrowAt G n) (F : Fr) {Γ : RCtx} {σs : List STy}
    (b : Builtin) (args : RArgs E Γ σs) (τ : STy) (hb : b = .ecrecover) :
    Grow (evalBuiltin G F (n + 1) b args τ) := by
  rcases hb with rfl <;> simp only [evalBuiltin] <;> grow_go [ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow, memElem_grow, readLoc_grow, lengthOf_grow, indexLoc_grow, indexNat_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow, fieldsOf_grow, ret32_grow, decodeArgs_grow, bytesOfRV_grow, encodeVals_grow, convRV_grow, convExplicitRV_grow, writeLoc_grow, deleteLoc_grow, keyStep_grow, zeroVals_grow, zeroInner_grow, copyInto_grow, getterPath_grow, extReturn_grow]
theorem evalBuiltin_grow_step {G : Glob E} {n : Nat} (ih : GrowAt G n) (F : Fr) {Γ : RCtx} {σs : List STy}
    (b : Builtin) (args : RArgs E Γ σs) (τ : STy) : Grow (evalBuiltin G F (n + 1) b args τ) := by
  cases b
  all_goals first
    | exact evalBuiltin_grow_0 ih F _ args τ (by decide)
    | exact evalBuiltin_grow_1 ih F _ args τ (by decide)
    | exact evalBuiltin_grow_2 ih F _ args τ (by decide)
    | exact evalBuiltin_grow_3 ih F _ args τ (by decide)
    | exact evalBuiltin_grow_4 ih F _ args τ (by decide)
    | (simp only [evalBuiltin]; grow_go [ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow, memElem_grow, readLoc_grow, lengthOf_grow, indexLoc_grow, indexNat_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow, fieldsOf_grow, ret32_grow, decodeArgs_grow, bytesOfRV_grow, encodeVals_grow, convRV_grow, convExplicitRV_grow, writeLoc_grow, deleteLoc_grow, keyStep_grow, zeroVals_grow, zeroInner_grow, copyInto_grow, getterPath_grow, extReturn_grow])
theorem evalArgsRev_grow_step {G : Glob E} {n : Nat} (ih : GrowAt G n) (F : Fr) {Γ : RCtx} {τs : List STy} (es : RArgs E Γ τs) :
    Grow (evalArgsRev G F (n + 1) es) := by
  cases es <;> simp only [evalArgsRev] <;> grow_go [ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow, memElem_grow, readLoc_grow, lengthOf_grow, indexLoc_grow, indexNat_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow, fieldsOf_grow, ret32_grow, decodeArgs_grow, bytesOfRV_grow, encodeVals_grow, convRV_grow, convExplicitRV_grow, writeLoc_grow, deleteLoc_grow, keyStep_grow, zeroVals_grow, zeroInner_grow, copyInto_grow, getterPath_grow, extReturn_grow]
theorem pay_grow_step {G : Glob E} {n : Nat} (ih : GrowAt G n) (F : Fr) {Γ : RCtx} (a : RExpr E Γ (.address true)) (v : RExpr E Γ (.int IntTy.u256)) :
    Grow (pay G F (n + 1) a v) := by
  simp only [pay]; grow_go [ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow, memElem_grow, readLoc_grow, lengthOf_grow, indexLoc_grow, indexNat_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow, fieldsOf_grow, ret32_grow, decodeArgs_grow, bytesOfRV_grow, encodeVals_grow, convRV_grow, convExplicitRV_grow, writeLoc_grow, deleteLoc_grow, keyStep_grow, zeroVals_grow, zeroInner_grow, copyInto_grow, getterPath_grow, extReturn_grow]
theorem execS_grow_step {G : Glob E} {n : Nat} (ih : GrowAt G n) (F : Fr) (nps : Nat) (ph : Option (Ph E)) {R : List STy} {M : Bool} {k : SCtx} {Γ Γ' : RCtx} (s : RStmt E R M k Γ Γ') (l : Locals E.layout Γ) :
    Grow (execS G F (n + 1) nps ph s l) := by
  cases s <;> simp only [execS] <;> grow_go [ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow, memElem_grow, readLoc_grow, lengthOf_grow, indexLoc_grow, indexNat_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow, fieldsOf_grow, ret32_grow, decodeArgs_grow, bytesOfRV_grow, encodeVals_grow, convRV_grow, convExplicitRV_grow, writeLoc_grow, deleteLoc_grow, keyStep_grow, zeroVals_grow, zeroInner_grow, copyInto_grow, getterPath_grow, extReturn_grow]
theorem forIter_grow_step {G : Glob E} {n : Nat} (ih : GrowAt G n) (F : Fr) (nps : Nat) (ph : Option (Ph E)) {R : List STy} {M u : Bool} {Γ₁ Γ₂ : RCtx} (c : ROptBool E Γ₁) (post : ROptExpr E Γ₁) (body : RStmt E R M ⟨true, u⟩ Γ₁ Γ₂) (l : Locals E.layout Γ₁) :
    Grow (forIter G F (n + 1) nps ph c post body l) := by
  cases c <;> simp only [forIter] <;> grow_go [ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow, memElem_grow, readLoc_grow, lengthOf_grow, indexLoc_grow, indexNat_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow, fieldsOf_grow, ret32_grow, decodeArgs_grow, bytesOfRV_grow, encodeVals_grow, convRV_grow, convExplicitRV_grow, writeLoc_grow, deleteLoc_grow, keyStep_grow, zeroVals_grow, zeroInner_grow, copyInto_grow, getterPath_grow, extReturn_grow]
theorem execItems_grow_step {G : Glob E} {n : Nat} (ih : GrowAt G n) (F : Fr) (nps : Nat) (ph : Option (Ph E)) {R : List STy} {M : Bool} {k : SCtx} {Γ Γ' : RCtx} (b : RItems E R M k Γ Γ') (l : Locals E.layout Γ) :
    Grow (execItems G F (n + 1) nps ph b l) := by
  cases b <;> simp only [execItems] <;> grow_go [ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow, memElem_grow, readLoc_grow, lengthOf_grow, indexLoc_grow, indexNat_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow, fieldsOf_grow, ret32_grow, decodeArgs_grow, bytesOfRV_grow, encodeVals_grow, convRV_grow, convExplicitRV_grow, writeLoc_grow, deleteLoc_grow, keyStep_grow, zeroVals_grow, zeroInner_grow, copyInto_grow, getterPath_grow, extReturn_grow]
theorem runMods_grow_step {G : Glob E} {n : Nat} (ih : GrowAt G n) (F : Fr) (b : RBody E) (mods : List (RModInv E b.locals)) (l : Locals E.layout b.locals) :
    Grow (runMods G F (n + 1) b mods l) := by
  cases mods <;> simp only [runMods] <;> grow_go [ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow, memElem_grow, readLoc_grow, lengthOf_grow, indexLoc_grow, indexNat_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow, fieldsOf_grow, ret32_grow, decodeArgs_grow, bytesOfRV_grow, encodeVals_grow, convRV_grow, convExplicitRV_grow, writeLoc_grow, deleteLoc_grow, keyStep_grow, zeroVals_grow, zeroInner_grow, copyInto_grow, getterPath_grow, extReturn_grow]
theorem callInternal_grow_step {G : Glob E} {n : Nat} (ih : GrowAt G n) (F : Fr) (d : Decl) {ps : List STy} (vs : Vals E.layout ps) (rs : List STy) :
    Grow (callInternal G F (n + 1) d vs rs) := by
  simp only [callInternal]; grow_go [ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow, memElem_grow, readLoc_grow, lengthOf_grow, indexLoc_grow, indexNat_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow, fieldsOf_grow, ret32_grow, decodeArgs_grow, bytesOfRV_grow, encodeVals_grow, convRV_grow, convExplicitRV_grow, writeLoc_grow, deleteLoc_grow, keyStep_grow, zeroVals_grow, zeroInner_grow, copyInto_grow, getterPath_grow, extReturn_grow]
theorem callAddr_grow_step {G : Glob E} {n : Nat} (ih : GrowAt G n) (F : Fr) (a : Address) (v : Word) (input : Bytes) (static : Bool) :
    Grow (callAddr G F (n + 1) a v input static) := by
  simp only [callAddr]; grow_go [ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow, memElem_grow, readLoc_grow, lengthOf_grow, indexLoc_grow, indexNat_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow, fieldsOf_grow, ret32_grow, decodeArgs_grow, bytesOfRV_grow, encodeVals_grow, convRV_grow, convExplicitRV_grow, writeLoc_grow, deleteLoc_grow, keyStep_grow, zeroVals_grow, zeroInner_grow, copyInto_grow, getterPath_grow, extReturn_grow]
theorem enterInstance_grow_step {G : Glob E} {n : Nat} (ih : GrowAt G n) (a sender : Address) (v : Word) (input : Bytes) (static : Bool) (c : String) (depth : Nat) (m : Nat × Nat × Heap E.layout) :
    Grow (enterInstance G (n + 1) a sender v input static c depth m) := by
  simp only [enterInstance]; grow_go [ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow, memElem_grow, readLoc_grow, lengthOf_grow, indexLoc_grow, indexNat_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow, fieldsOf_grow, ret32_grow, decodeArgs_grow, bytesOfRV_grow, encodeVals_grow, convRV_grow, convExplicitRV_grow, writeLoc_grow, deleteLoc_grow, keyStep_grow, zeroVals_grow, zeroInner_grow, copyInto_grow, getterPath_grow, extReturn_grow]
theorem envLoop_grow_step {G : Glob E} {n : Nat} (ih : GrowAt G n) (depth : Nat) (pstatic : Bool) :
    Grow (envLoop G (n + 1) depth pstatic) := by
  rw [envLoop.eq_2 G depth pstatic n]; grow_go [ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow, memElem_grow, readLoc_grow, lengthOf_grow, indexLoc_grow, indexNat_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow, fieldsOf_grow, ret32_grow, decodeArgs_grow, bytesOfRV_grow, encodeVals_grow, convRV_grow, convExplicitRV_grow, writeLoc_grow, deleteLoc_grow, keyStep_grow, zeroVals_grow, zeroInner_grow, copyInto_grow, getterPath_grow, extReturn_grow]
theorem dispatch_grow_fn {G : Glob E} {n : Nat} (ih : GrowAt G n) (F : Fr) (input : Bytes) {d : Decl}
    (hp : G.pickFn F input = some d) (he : input.isEmpty = false) : Grow (dispatch G F (n + 1) input) := by
  simp only [dispatch, hp, he]; grow_go [ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow, memElem_grow, readLoc_grow, lengthOf_grow, indexLoc_grow, indexNat_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow, fieldsOf_grow, ret32_grow, decodeArgs_grow, bytesOfRV_grow, encodeVals_grow, convRV_grow, convExplicitRV_grow, writeLoc_grow, deleteLoc_grow, keyStep_grow, zeroVals_grow, zeroInner_grow, copyInto_grow, getterPath_grow, extReturn_grow]
theorem dispatch_grow_getter_none {G : Glob E} {n : Nat} (ih : GrowAt G n) (F : Fr) (input : Bytes) {r : Decl × List STy × STy}
    (hp : G.pickFn F input = none) (hg : G.pickGetter F input = some r) : Grow (dispatch G F (n + 1) input) := by
  simp only [dispatch, hp, hg]; grow_go [ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow, memElem_grow, readLoc_grow, lengthOf_grow, indexLoc_grow, indexNat_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow, fieldsOf_grow, ret32_grow, decodeArgs_grow, bytesOfRV_grow, encodeVals_grow, convRV_grow, convExplicitRV_grow, writeLoc_grow, deleteLoc_grow, keyStep_grow, zeroVals_grow, zeroInner_grow, copyInto_grow, getterPath_grow, extReturn_grow]
theorem dispatch_grow_getter_some {G : Glob E} {n : Nat} (ih : GrowAt G n) (F : Fr) (input : Bytes) {d : Decl} {r : Decl × List STy × STy}
    (hp : G.pickFn F input = some d) (he : input.isEmpty = true) (hg : G.pickGetter F input = some r) :
    Grow (dispatch G F (n + 1) input) := by
  simp only [dispatch, hp, he, hg]; grow_go [ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow, memElem_grow, readLoc_grow, lengthOf_grow, indexLoc_grow, indexNat_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow, fieldsOf_grow, ret32_grow, decodeArgs_grow, bytesOfRV_grow, encodeVals_grow, convRV_grow, convExplicitRV_grow, writeLoc_grow, deleteLoc_grow, keyStep_grow, zeroVals_grow, zeroInner_grow, copyInto_grow, getterPath_grow, extReturn_grow]
theorem dispatch_grow_getter {G : Glob E} {n : Nat} (ih : GrowAt G n) (F : Fr) (input : Bytes) (b : Bool) {r : Decl × List STy × STy}
    (hm : (G.pickFn F input, input.isEmpty) = (none, b) ∨ ∃ d, (G.pickFn F input, input.isEmpty) = (some d, true))
    (hg : G.pickGetter F input = some r) : Grow (dispatch G F (n + 1) input) := by
  rcases hm with hm | ⟨d, hm⟩ <;> simp only [Prod.mk.injEq] at hm
  · exact dispatch_grow_getter_none ih F input hm.1 hg
  · exact dispatch_grow_getter_some ih F input hm.1 hm.2 hg
theorem dispatch_grow_special {G : Glob E} {n : Nat} (ih : GrowAt G n) (F : Fr) (input : Bytes) (b : Bool)
    (hm : (G.pickFn F input, input.isEmpty) = (none, b) ∨ ∃ d, (G.pickFn F input, input.isEmpty) = (some d, true))
    (hg : G.pickGetter F input = none) : Grow (dispatch G F (n + 1) input) := by
  rcases hm with hm | ⟨d, hm⟩ <;> simp only [Prod.mk.injEq] at hm <;> simp only [dispatch, hm.1, hm.2, hg] <;>
    grow_go [ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow, memElem_grow, readLoc_grow, lengthOf_grow, indexLoc_grow, indexNat_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow, fieldsOf_grow, ret32_grow, decodeArgs_grow, bytesOfRV_grow, encodeVals_grow, convRV_grow, convExplicitRV_grow, writeLoc_grow, deleteLoc_grow, keyStep_grow, zeroVals_grow, zeroInner_grow, copyInto_grow, getterPath_grow, extReturn_grow]
theorem dispatch_grow_step {G : Glob E} {n : Nat} (ih : GrowAt G n) (F : Fr) (input : Bytes) : Grow (dispatch G F (n + 1) input) := by
  cases hp : G.pickFn F input with
  | some d =>
    cases he : input.isEmpty with
    | false => exact dispatch_grow_fn ih F input hp he
    | true =>
      cases hg : G.pickGetter F input with
      | some r => exact dispatch_grow_getter ih F input true (.inr ⟨d, by rw [hp, he]⟩) hg
      | none => exact dispatch_grow_special ih F input true (.inr ⟨d, by rw [hp, he]⟩) hg
  | none =>
    cases hg : G.pickGetter F input with
    | some r => exact dispatch_grow_getter ih F input _ (.inl (by rw [hp])) hg
    | none => exact dispatch_grow_special ih F input _ (.inl (by rw [hp])) hg

theorem growAt (G : Glob E) : ∀ n, GrowAt G n
  | 0 => growAt_zero G
  | n + 1 =>
    have ih := growAt G n
    ⟨evalE_grow_step ih, evalPair_grow_step ih, evalArgs_grow_step ih, evalConvArgs_grow_step ih, evalLoc_grow_step ih, evalBuiltin_grow_step ih, evalArgsRev_grow_step ih, pay_grow_step ih, execS_grow_step ih, forIter_grow_step ih, execItems_grow_step ih, runMods_grow_step ih, callInternal_grow_step ih, callAddr_grow_step ih, enterInstance_grow_step ih, envLoop_grow_step ih, dispatch_grow_step ih⟩

/-! ## Helpers keep the events -/

/-- A computation leaves the events as they are. -/
def Const {Γ : RCtx} {α : Type} (m : EM E Γ α) : Prop :=
  ∀ x, (m.run x).2.2.events = x.2.events

theorem Const.pure {Γ : RCtx} {α : Type} (a : α) : Const (pure a : EM E Γ α) := fun _ => rfl
theorem Const.halt {Γ : RCtx} {α : Type} (h : Halt) : Const (halt h : EM E Γ α) := fun _ => rfl
theorem Const.bind {Γ : RCtx} {α β : Type} {m : EM E Γ α} {k : α → EM E Γ β} (hm : Const m)
    (hk : ∀ a, Const (k a)) : Const (m >>= k) := by
  intro x
  rw [run_bind]
  have h1 := hm x
  rcases hr : m.run x with ⟨r, y⟩
  rw [hr] at h1
  cases r with
  | ok a => exact (hk a y).trans h1
  | error e => exact h1

/-- A computation that keeps the events approximates itself at a larger
horizon exactly when it is below it. -/
theorem Approx.of_below {Γ : RCtx} {α : Type} {m m' : EM E Γ α} (hb : Below m m') (hc : Const m)
    (hc' : Const m') : Approx m m' := by
  refine ⟨fun x => (hc x).symm ▸ List.prefix_refl _, fun x => (hc' x).symm ▸ List.prefix_refl _, fun x => ?_⟩
  rcases hb x with ht | he
  · exact .inl ⟨ht, by rw [hc, hc']; exact List.prefix_refl _⟩
  · exact .inr he


theorem Const.st {Γ : RCtx} : Const (st : EM E Γ (St E)) := fun _ => rfl
theorem Const.locals {Γ : RCtx} : Const (locals : EM E Γ (Locals E.layout Γ)) := fun _ => rfl
theorem Const.setLocals {Γ : RCtx} (l : Locals E.layout Γ) : Const (setLocals l : EM E Γ Unit) :=
  fun _ => rfl
theorem Const.modSt {Γ : RCtx} (f : St E → St E) (hf : ∀ s, (f s).events = s.events) :
    Const (modSt f : EM E Γ Unit) := fun x => hf x.2
theorem Const.lift {Γ : RCtx} {α : Type} (r : R α) : Const (lift r : EM E Γ α) := by
  cases r <;> exact fun _ => rfl
theorem Const.sub {Γ Γ' : RCtx} {α : Type} (l' : Locals E.layout Γ') {m : EM E Γ' α} (h : Const m) :
    Const (EM.sub (Γ := Γ) l' m) := by
  intro x
  rcases x with ⟨l, s⟩
  rw [run_sub]
  have := h (l', s)
  rcases hr : m.run (l', s) with ⟨r, l'', s'⟩
  rw [hr] at this
  cases r <;> exact this
theorem Const.attempt {Γ : RCtx} {α : Type} {m : EM E Γ α} (h : Const m) : Const (EM.attempt m) := by
  intro x
  rw [run_attempt]
  exact h x

theorem heapPut_const {Γ : RCtx} (a : Nat) (x : Σ τ, Data E.layout τ) : Const (heapPut (Γ := Γ) a x) := by
  intro y
  unfold heapPut
  rw [run_bind, run_st]
  dsimp only
  split
  · exact rfl
  · exact rfl

theorem alloc_const {Γ : RCtx} {τ : STy} (x : Data E.layout τ) : Const (alloc (Γ := Γ) x) := by
  intro y
  unfold alloc
  rw [run_bind, run_st]
  exact rfl

/-- Close `Const body`: through binds, `match`es and `if`s, by the given
lemmas at the calls; a `modSt` keeps or appends events. -/
syntax "const_go" "[" ident,* "]" : tactic
macro_rules
  | `(tactic| const_go [$ls,*]) => `(tactic| repeat' (first
      | (with_reducible exact Const.pure _)
      | (with_reducible exact Const.halt _)
      | (with_reducible exact Const.st)
      | (with_reducible exact Const.locals)
      | (with_reducible exact Const.setLocals _)
      | (with_reducible exact Const.lift _)
      | (with_reducible apply Const.modSt; intro _; rfl)
      | (first $[| with_reducible apply $ls:ident]*)
      | (with_reducible apply Const.sub)
      | (with_reducible apply Const.attempt)
      | (with_reducible apply Const.map)
      | (refine Const.bind ?_ ?_)
      | (with_reducible intro _)
      | split
      | (intro _; exact rfl)
      | (dsimp only)))

section
variable {Γ : RCtx}

theorem getV_const {τ : STy} (v : RVal E.layout τ) : Const (getV (Γ := Γ) v) := Const.lift _
theorem readCell_const (F : Fr) (p : SPath) : Const (readCell (E := E) (Γ := Γ) F p) := by
  unfold readCell; const_go []
theorem readAt_const (F : Fr) (p : SPath) (τ : STy) : Const (readAt (E := E) (Γ := Γ) F p τ) := by
  unfold readAt; const_go [readCell_const]
theorem applyOp_const (F : Fr) (o : Op E.layout E.lay E.lay) : Const (applyOp (Γ := Γ) F o) := by
  unfold applyOp; const_go []
theorem setCell_const (F : Fr) (p : SPath) (o : Option (Val E.layout (E.cellTy p))) :
    Const (setCell (Γ := Γ) F p o) := by
  unfold setCell; const_go [applyOp_const]
theorem writeAt_const {τ : STy} (F : Fr) (p : SPath) (v : Val E.layout τ) : Const (writeAt (Γ := Γ) F p v) := by
  unfold writeAt; const_go [setCell_const]
theorem readLen_const (F : Fr) (p : SPath) : Const (readLen (E := E) (Γ := Γ) F p) := by
  unfold readLen; const_go [readAt_const]
theorem writeLen_const (F : Fr) (p : SPath) (k : Nat) : Const (writeLen (E := E) (Γ := Γ) F p k) := by
  unfold writeLen; const_go [writeAt_const]
theorem heapObj_const (a : Nat) : Const (heapObj (E := E) (Γ := Γ) a) := by
  unfold heapObj; const_go []
theorem heapAt_const (a : Nat) (τ : STy) : Const (heapAt (E := E) (Γ := Γ) a τ) := by
  unfold heapAt; const_go [heapObj_const]
theorem heapBytes_const (a : Nat) : Const (heapBytes (E := E) (Γ := Γ) a) := by
  unfold heapBytes; const_go [heapObj_const]
theorem allocRef_const {τ : STy} (x : Data E.layout τ) : Const (allocRef (Γ := Γ) x) := by
  unfold allocRef; const_go [alloc_const]
theorem storRef_const (τ : STy) (p : SPath) : Const (storRef (E := E) (Γ := Γ) τ p) := by
  unfold storRef; const_go []

end

section
variable {Γ : RCtx}

mutual
theorem zeroData_const : ∀ (n : Nat) (τ : STy), Const (zeroData (E := E) (Γ := Γ) n τ)
  | 0, _ => Const.halt _
  | n + 1, τ => by
    simp only [zeroData]
    const_go [zeroElems_const, zeroFields_const, zeroVal_const, heapPut_const, alloc_const, readCell_const, readAt_const, applyOp_const, setCell_const, writeAt_const, readLen_const, writeLen_const, heapObj_const, heapAt_const, heapBytes_const, allocRef_const, storRef_const, getV_const]
theorem zeroVal_const : ∀ (n : Nat) (τ : STy), Const (zeroVal (E := E) (Γ := Γ) n τ)
  | 0, _ => Const.halt _
  | n + 1, τ => by
    simp only [zeroVal]
    const_go [zeroData_const, heapPut_const, alloc_const, readCell_const, readAt_const, applyOp_const, setCell_const, writeAt_const, readLen_const, writeLen_const, heapObj_const, heapAt_const, heapBytes_const, allocRef_const, storRef_const, getV_const]
theorem zeroElems_const : ∀ (n : Nat) (σ : STy) (m : Nat), Const (zeroElems (E := E) (Γ := Γ) n σ m)
  | 0, _, m => by cases m <;> exact Const.halt _
  | n + 1, _, 0 => Const.pure _
  | n + 1, σ, m + 1 => Const.bind (zeroVal_const n σ) fun _ => Const.bind (zeroElems_const n σ m) fun _ => Const.pure _
theorem zeroFields_const : ∀ (n : Nat) (τs : List STy), Const (zeroFields (E := E) (Γ := Γ) n τs)
  | 0, τs => by cases τs <;> exact Const.halt _
  | n + 1, [] => Const.pure _
  | n + 1, τ :: τs => Const.bind (zeroVal_const n τ) fun _ => Const.bind (zeroFields_const n τs) fun _ => Const.pure _
end

mutual
theorem loadMem_const (F : Fr) : ∀ (n : Nat) (τ : STy) (p : SPath), Const (loadMem (E := E) (Γ := Γ) F n τ p)
  | 0, _, _ => Const.halt _
  | n + 1, τ, p => by
    simp only [loadMem]
    const_go [loadBytes_const, loadElems_const, loadFields_const, heapPut_const, alloc_const, readCell_const, readAt_const, applyOp_const, setCell_const, writeAt_const, readLen_const, writeLen_const, heapObj_const, heapAt_const, heapBytes_const, allocRef_const, storRef_const, getV_const]
theorem loadElem_const (F : Fr) : ∀ (n : Nat) (τ : STy) (p : SPath), Const (loadElem (E := E) (Γ := Γ) F n τ p)
  | 0, _, _ => Const.halt _
  | n + 1, τ, p => by
    simp only [loadElem]
    const_go [loadMem_const, heapPut_const, alloc_const, readCell_const, readAt_const, applyOp_const, setCell_const, writeAt_const, readLen_const, writeLen_const, heapObj_const, heapAt_const, heapBytes_const, allocRef_const, storRef_const, getV_const]
theorem loadElems_const (F : Fr) : ∀ (n : Nat) (σ : STy) (p : SPath) (i m : Nat),
    Const (loadElems (E := E) (Γ := Γ) F n σ p i m)
  | 0, _, _, _, m => by cases m <;> exact Const.halt _
  | n + 1, _, _, _, 0 => Const.pure _
  | n + 1, σ, p, i, m + 1 => Const.bind (loadElem_const F n σ _) fun _ =>
      Const.bind (loadElems_const F n σ p (i + 1) m) fun _ => Const.pure _
theorem loadFields_const (F : Fr) : ∀ (n : Nat) (τs : List STy) (p : SPath) (i : Nat),
    Const (loadFields (E := E) (Γ := Γ) F n τs p i)
  | 0, τs, _, _ => by cases τs <;> exact Const.halt _
  | n + 1, [], _, _ => Const.pure _
  | n + 1, τ :: τs, p, i => Const.bind (loadElem_const F n τ _) fun _ =>
      Const.bind (loadFields_const F n τs p (i + 1)) fun _ => Const.pure _
theorem loadBytes_const (F : Fr) : ∀ (n : Nat) (p : SPath) (i k : Nat), Const (loadBytes (E := E) (Γ := Γ) F n p i k)
  | 0, _, _, k => by cases k <;> exact Const.halt _
  | n + 1, _, _, 0 => Const.pure _
  | n + 1, p, i, k + 1 => by
    refine Const.bind (readAt_const F _ _) fun v => ?_
    cases v <;> first
      | exact Const.bind (loadBytes_const F n p (i + 1) k) fun _ => Const.pure _
      | (rename_i h; cases h)
end

mutual
theorem deleteStor_const (F : Fr) : ∀ (n : Nat) (τ : STy) (p : SPath), Const (deleteStor (E := E) (Γ := Γ) F n τ p)
  | 0, _, _ => Const.halt _
  | n + 1, τ, p => by
    simp only [deleteStor]
    const_go [deleteRange_const, deleteFields_const, heapPut_const, alloc_const, readCell_const, readAt_const, applyOp_const, setCell_const, writeAt_const, readLen_const, writeLen_const, heapObj_const, heapAt_const, heapBytes_const, allocRef_const, storRef_const, getV_const]
theorem deleteRange_const (F : Fr) : ∀ (n : Nat) (σ : STy) (p : SPath) (i k : Nat),
    Const (deleteRange (E := E) (Γ := Γ) F n σ p i k)
  | 0, _, _, _, k => by cases k <;> exact Const.halt _
  | n + 1, _, _, _, 0 => Const.pure _
  | n + 1, σ, p, i, k + 1 => Const.bind (deleteStor_const F n σ _) fun _ => deleteRange_const F n σ p (i + 1) k
theorem deleteFields_const (F : Fr) : ∀ (n : Nat) (τs : List STy) (p : SPath) (i : Nat),
    Const (deleteFields (E := E) (Γ := Γ) F n τs p i)
  | 0, τs, _, _ => by cases τs <;> exact Const.halt _
  | n + 1, [], _, _ => Const.pure _
  | n + 1, τ :: τs, p, i => Const.bind (deleteStor_const F n τ _) fun _ => deleteFields_const F n τs p (i + 1)
end

mutual
theorem storeData_const (F : Fr) : ∀ (n : Nat) (τ : STy) (p : SPath) {σ : STy} (x : Data E.layout σ),
    Const (storeData (Γ := Γ) F n τ p x)
  | 0, _, _, _, _ => Const.halt _
  | n + 1, τ, p, _, x => by
    simp only [storeData]
    const_go [storeBytes_const, deleteRange_const, storeElems_const, storeFields_const, storeVal_const, heapPut_const, alloc_const, readCell_const, readAt_const, applyOp_const, setCell_const, writeAt_const, readLen_const, writeLen_const, heapObj_const, heapAt_const, heapBytes_const, allocRef_const, storRef_const, getV_const]
theorem storeVal_const (F : Fr) : ∀ (n : Nat) (τ : STy) (p : SPath) {σ : STy} (v : Val E.layout σ),
    Const (storeVal (Γ := Γ) F n τ p v)
  | 0, _, _, _, _ => Const.halt _
  | n + 1, τ, p, _, v => by
    simp only [storeVal]
    const_go [storeData_const, loadMem_const, heapPut_const, alloc_const, readCell_const, readAt_const, applyOp_const, setCell_const, writeAt_const, readLen_const, writeLen_const, heapObj_const, heapAt_const, heapBytes_const, allocRef_const, storRef_const, getV_const]
theorem storeElems_const (F : Fr) : ∀ (n : Nat) (τ : STy) (p : SPath) (i len : Nat) {σ : STy}
    (xs : Fin len → Data E.layout σ), Const (storeElems (Γ := Γ) F n τ p i len xs)
  | 0, _, _, _, len, _, _ => by cases len <;> exact Const.halt _
  | n + 1, _, _, _, 0, _, _ => Const.pure _
  | n + 1, τ, p, i, len + 1, _, xs =>
    Const.bind (storeData_const F n τ _ _) fun _ => storeElems_const F n τ p (i + 1) len _
theorem storeFields_const (F : Fr) : ∀ (n : Nat) (τs : List STy) (p : SPath) (i : Nat) {σs : List STy}
    (xs : DataList E.layout σs), Const (storeFields (Γ := Γ) F n τs p i xs)
  | 0, τs, _, _, _, xs => by cases τs <;> cases xs <;> exact Const.halt _
  | n + 1, [], _, _, _, _ => Const.pure _
  | n + 1, _ :: _, _, _, _, .nil => Const.pure _
  | n + 1, τ :: τs, p, i, _, .cons x xs =>
    Const.bind (storeData_const F n τ _ x) fun _ => storeFields_const F n τs p (i + 1) xs
theorem storeBytes_const (F : Fr) : ∀ (n : Nat) (p : SPath) (i : Nat) (bs : List UInt8),
    Const (storeBytes (E := E) (Γ := Γ) F n p i bs)
  | 0, _, _, bs => by cases bs <;> exact Const.halt _
  | n + 1, _, _, [] => Const.pure _
  | n + 1, p, i, b :: bs => Const.bind (writeAt_const F _ _) fun _ => storeBytes_const F n p (i + 1) bs
end

end

section
variable {Γ : RCtx}

theorem List.mapM_const {Γ : RCtx} {α β : Type} (f : α → EM E Γ β) (hf : ∀ a, Const (f a)) :
    ∀ (l : List α), Const (l.mapM f) := by
  intro l
  suffices h : ∀ (acc : List β), Const (List.mapM.loop f l acc) from h []
  induction l with
  | nil => intro acc; exact Const.pure _
  | cons a as ih => intro acc; exact Const.bind (hf a) fun b => ih (b :: acc)

theorem panicM_const {α : Type} : Const (memElem.panicM (E := E) (Γ := Γ) (α := α)) := Const.lift _
theorem memElem_const (a i : Nat) (τ : STy) : Const (memElem (E := E) (Γ := Γ) a i τ) := by
  unfold memElem; const_go [panicM_const, heapPut_const, alloc_const, readCell_const, readAt_const, applyOp_const, setCell_const, writeAt_const, readLen_const, writeLen_const, heapObj_const, heapAt_const, heapBytes_const, allocRef_const, storRef_const, getV_const, zeroVal_const, zeroData_const, loadMem_const, deleteStor_const, storeData_const, storeVal_const]
theorem readLoc_const (F : Fr) {τ : STy} (loc : Loc E.layout Γ τ) : Const (readLoc F loc) := by
  cases loc <;> simp only [readLoc] <;> const_go [memElem_const, heapPut_const, alloc_const, readCell_const, readAt_const, applyOp_const, setCell_const, writeAt_const, readLen_const, writeLen_const, heapObj_const, heapAt_const, heapBytes_const, allocRef_const, storRef_const, getV_const, zeroVal_const, zeroData_const, loadMem_const, deleteStor_const, storeData_const, storeVal_const]
theorem memSet_const (a i : Nat) {τ : STy} (v : Val E.layout τ) : Const (memSet (Γ := Γ) a i v) := by
  unfold memSet; const_go [heapPut_const, alloc_const, readCell_const, readAt_const, applyOp_const, setCell_const, writeAt_const, readLen_const, writeLen_const, heapObj_const, heapAt_const, heapBytes_const, allocRef_const, storRef_const, getV_const, zeroVal_const, zeroData_const, loadMem_const, deleteStor_const, storeData_const, storeVal_const]
theorem lengthOf_const (F : Fr) {τ : STy} (v : Val E.layout τ) : Const (lengthOf (Γ := Γ) F v) := by
  unfold lengthOf; const_go [heapPut_const, alloc_const, readCell_const, readAt_const, applyOp_const, setCell_const, writeAt_const, readLen_const, writeLen_const, heapObj_const, heapAt_const, heapBytes_const, allocRef_const, storRef_const, getV_const, zeroVal_const, zeroData_const, loadMem_const, deleteStor_const, storeData_const, storeVal_const]
theorem indexLoc_const (F : Fr) {l : DataLoc} {σ : STy} {k : Option Nat} (a : Val E.layout (.array l σ k))
    (i : Nat) : Const (indexLoc (Γ := Γ) F a i) := by
  unfold indexLoc; const_go [lengthOf_const, heapPut_const, alloc_const, readCell_const, readAt_const, applyOp_const, setCell_const, writeAt_const, readLen_const, writeLen_const, heapObj_const, heapAt_const, heapBytes_const, allocRef_const, storRef_const, getV_const, zeroVal_const, zeroData_const, loadMem_const, deleteStor_const, storeData_const, storeVal_const]
theorem indexNat_const {σ : STy} (v : RVal E.layout σ) : Const (indexNat (Γ := Γ) v) := Const.lift _
theorem instanceAt_const (G : Glob E) (a : Address) : Const (instanceAt (Γ := Γ) G a) := by
  unfold instanceAt; const_go []
theorem credit_const (a : Address) (v : Word) : Const (credit (E := E) (Γ := Γ) a v) := by
  unfold credit; const_go []
theorem debit_const (a : Address) (v : Word) : Const (debit (E := E) (Γ := Γ) a v) := by
  unfold debit; const_go []
theorem mark_const : Const (mark (E := E) (Γ := Γ)) := by
  unfold mark; const_go []
theorem rollbackTo_const (m : Nat × Nat × Heap E.layout) : Const (rollbackTo (Γ := Γ) m) := by
  unfold rollbackTo; const_go []
theorem reraise_const (o : Outcome) : Const (reraise (E := E) (Γ := Γ) o) := by
  unfold reraise; const_go []
theorem fieldsOf_const : ∀ {ps : List STy} (vs : Vals E.layout ps) (τs : List STy),
    Const (fieldsOf (E := E) (Γ := Γ) vs τs)
  | _, .nil, [] => Const.pure _
  | _, .nil, _ :: _ => Const.halt _
  | _, .cons _ _, [] => Const.halt _
  | _, .cons (τ := σ) v vs, τ :: τs => by
    simp only [fieldsOf]
    split
    · exact Const.bind (fieldsOf_const vs τs) fun _ => Const.pure _
    · exact Const.halt _
theorem ret32_const (τ : STy) (bs : Bytes) : Const (ret32 (E := E) (Γ := Γ) τ bs) := by
  unfold ret32; const_go []
theorem tailBytes_const (data : Bytes) (i : Nat) : Const (tailBytes (E := E) (Γ := Γ) data i) := by
  unfold tailBytes
  dsimp only
  split
  · exact Const.pure _
  · exact Const.halt _
theorem decodeArg_const (data : Bytes) (i : Nat) (τ : STy) : Const (decodeArg (E := E) (Γ := Γ) data i τ) := by
  unfold decodeArg
  split
  · split
    · exact Const.bind (tailBytes_const data i) fun _ => allocRef_const _
    · exact Const.lift _
  · split
    · exact Const.bind (tailBytes_const data i) fun _ => allocRef_const _
    · exact Const.lift _
  · split
    · split
      · dsimp only
        split
        · exact Const.bind (List.mapM_const _ (fun _ => Const.lift _) _) fun _ => allocRef_const _
        · exact Const.halt _
      · exact Const.halt _
    · exact Const.lift _
  · exact Const.lift _
theorem decodeArgs_const (data : Bytes) : ∀ (τs : List STy) (i : Nat), Const (decodeArgs (E := E) (Γ := Γ) data τs i)
  | [], _ => Const.pure _
  | τ :: τs, i => Const.bind (decodeArg_const data i τ) fun _ =>
      Const.bind (decodeArgs_const data τs (i + 1)) fun _ => Const.pure _

end

section
variable {Γ : RCtx}

theorem bytesOfRV_const (F : Fr) (n : Nat) {τ : STy} (v : RVal E.layout τ) : Const (bytesOfRV (Γ := Γ) F n v) := by
  unfold bytesOfRV; const_go [heapPut_const, alloc_const, readCell_const, readAt_const, applyOp_const, setCell_const, writeAt_const, readLen_const, writeLen_const, heapObj_const, heapAt_const, heapBytes_const, allocRef_const, storRef_const, getV_const, zeroVal_const, zeroData_const, loadMem_const, deleteStor_const, storeData_const, storeVal_const, memSet_const]
theorem encodeOne_const (F : Fr) (n : Nat) (packed : Bool) {τ : STy} (v : RVal E.layout τ) :
    Const (encodeOne (Γ := Γ) F n packed v) := by
  unfold encodeOne; const_go [bytesOfRV_const, heapPut_const, alloc_const, readCell_const, readAt_const, applyOp_const, setCell_const, writeAt_const, readLen_const, writeLen_const, heapObj_const, heapAt_const, heapBytes_const, allocRef_const, storRef_const, getV_const, zeroVal_const, zeroData_const, loadMem_const, deleteStor_const, storeData_const, storeVal_const, memSet_const]
theorem encodeParts_const (F : Fr) (n : Nat) (packed : Bool) :
    ∀ {τs : List STy} (vs : RVals E.layout τs), Const (encodeParts (Γ := Γ) F n packed vs)
  | _, .nil => Const.pure _
  | _, .cons v vs => Const.bind (encodeOne_const F n packed v) fun _ =>
      Const.bind (encodeParts_const F n packed vs) fun _ => Const.pure _
theorem encodeVals_const (F : Fr) (n : Nat) (packed : Bool) {τs : List STy} (vs : RVals E.layout τs) :
    Const (encodeVals (Γ := Γ) F n packed vs) := by
  unfold encodeVals; const_go [encodeParts_const]
theorem convRV_const (F : Fr) (n : Nat) {σ : STy} (τ : STy) (v : RVal E.layout σ) :
    Const (convRV (Γ := Γ) F n τ v) := by
  unfold convRV; const_go [heapPut_const, alloc_const, readCell_const, readAt_const, applyOp_const, setCell_const, writeAt_const, readLen_const, writeLen_const, heapObj_const, heapAt_const, heapBytes_const, allocRef_const, storRef_const, getV_const, zeroVal_const, zeroData_const, loadMem_const, deleteStor_const, storeData_const, storeVal_const, memSet_const]
theorem convExplicitRV_const (F : Fr) (n : Nat) {σ : STy} (τ : STy) (v : RVal E.layout σ) :
    Const (convExplicitRV (Γ := Γ) F n τ v) := by
  unfold convExplicitRV; const_go [convRV_const, bytesOfRV_const, heapPut_const, alloc_const, readCell_const, readAt_const, applyOp_const, setCell_const, writeAt_const, readLen_const, writeLen_const, heapObj_const, heapAt_const, heapBytes_const, allocRef_const, storRef_const, getV_const, zeroVal_const, zeroData_const, loadMem_const, deleteStor_const, storeData_const, storeVal_const, memSet_const]
theorem writeLoc_const (F : Fr) (n : Nat) {τ : STy} (loc : Loc E.layout Γ τ) (v : Val E.layout τ) :
    Const (writeLoc F n loc v) := by
  unfold writeLoc; const_go [heapPut_const, alloc_const, readCell_const, readAt_const, applyOp_const, setCell_const, writeAt_const, readLen_const, writeLen_const, heapObj_const, heapAt_const, heapBytes_const, allocRef_const, storRef_const, getV_const, zeroVal_const, zeroData_const, loadMem_const, deleteStor_const, storeData_const, storeVal_const, memSet_const]
theorem deleteLoc_const (F : Fr) (n : Nat) {τ : STy} (loc : Loc E.layout Γ τ) : Const (deleteLoc F n loc) := by
  unfold deleteLoc; const_go [writeLoc_const, heapPut_const, alloc_const, readCell_const, readAt_const, applyOp_const, setCell_const, writeAt_const, readLen_const, writeLen_const, heapObj_const, heapAt_const, heapBytes_const, allocRef_const, storRef_const, getV_const, zeroVal_const, zeroData_const, loadMem_const, deleteStor_const, storeData_const, storeVal_const, memSet_const]
theorem keyStep_const (F : Fr) (n : Nat) {τ : STy} (k : RVal E.layout τ) : Const (keyStep (Γ := Γ) F n k) := by
  unfold keyStep; const_go [bytesOfRV_const, heapPut_const, alloc_const, readCell_const, readAt_const, applyOp_const, setCell_const, writeAt_const, readLen_const, writeLen_const, heapObj_const, heapAt_const, heapBytes_const, allocRef_const, storRef_const, getV_const, zeroVal_const, zeroData_const, loadMem_const, deleteStor_const, storeData_const, storeVal_const, memSet_const]
theorem zeroVals_const (n : Nat) : ∀ (τs : List STy), Const (zeroVals (E := E) (Γ := Γ) n τs)
  | [] => Const.pure _
  | τ :: τs => Const.bind (zeroVal_const n τ) fun _ => Const.bind (zeroVals_const n τs) fun _ => Const.pure _
theorem zeroInner_const (n : Nat) : ∀ (k : Nat) {Γ' : RCtx} (l : Locals E.layout Γ'),
    Const (zeroInner (Γ' := Γ) n k l)
  | 0, _, _ => Const.pure _
  | _ + 1, _, .nil => Const.pure _
  | k + 1, _, .cons _ r => Const.bind (zeroVal_const n _) fun _ => Const.bind (zeroInner_const n k r) fun _ => Const.pure _
theorem copyInto_const (F : Fr) (n : Nat) (τ : STy) (p : SPath) {σ : STy} (v : RVal E.layout σ) :
    Const (copyInto (Γ := Γ) F n τ p v) := by
  unfold copyInto; const_go [heapPut_const, alloc_const, readCell_const, readAt_const, applyOp_const, setCell_const, writeAt_const, readLen_const, writeLen_const, heapObj_const, heapAt_const, heapBytes_const, allocRef_const, storRef_const, getV_const, zeroVal_const, zeroData_const, loadMem_const, deleteStor_const, storeData_const, storeVal_const, memSet_const]
theorem extReturn_const (rs : List STy) (o : Outcome) : Const (extReturn (E := E) (Γ := Γ) rs o) := by
  unfold extReturn; const_go [reraise_const]
theorem getterPath_const (F : Fr) (n : Nat) (data : Solidity.Roadmap.Bytes) : ∀ (τ : STy) (p : SPath) (i : Nat),
    Const (getterPath (E := E) (Γ := Γ) F n data τ p i)
  | .mapping k v, p, i => by
    simp only [getterPath]
    const_go [keyStep_const, getterPath_const, heapPut_const, alloc_const, readCell_const, readAt_const, applyOp_const, setCell_const, writeAt_const, readLen_const, writeLen_const, heapObj_const, heapAt_const, heapBytes_const, allocRef_const, storRef_const, getV_const, zeroVal_const, zeroData_const, loadMem_const, deleteStor_const, storeData_const, storeVal_const, memSet_const]
  | .array _ τ len, p, i => by
    simp only [getterPath]
    const_go [getterPath_const, heapPut_const, alloc_const, readCell_const, readAt_const, applyOp_const, setCell_const, writeAt_const, readLen_const, writeLen_const, heapObj_const, heapAt_const, heapBytes_const, allocRef_const, storRef_const, getV_const, zeroVal_const, zeroData_const, loadMem_const, deleteStor_const, storeData_const, storeVal_const, memSet_const]
  | .int _, _, _ | .bool, _, _ | .address _, _, _ | .fixedBytes _ _, _, _ | .fixed _, _, _ | .enum _, _, _
  | .udvt _, _, _ | .contract _, _, _ | .bytes _, _, _ | .string _, _, _ | .struct _ _, _, _
  | .fn _ _ _ _, _, _ | .rational _, _, _ | .hexConst _ _, _, _ | .stringLit _, _, _ | .tuple _, _, _ =>
    Const.pure _

end

theorem Const.map {Γ : RCtx} {α β : Type} (f : α → β) {m : EM E Γ α} (h : Const m) : Const (f <$> m) := by
  intro x
  show ((m >>= fun a => (Pure.pure (f a) : EM E Γ β)).run x).2.2.events = x.2.events
  exact Const.bind h (fun _ => Const.pure _) x


/-! ## Timed-out runs show a prefix of the events -/

theorem Approx.trans {Γ : RCtx} {α : Type} {a b c : EM E Γ α} (h₁ : Approx a b) (h₂ : Approx b c) :
    Approx a c := by
  refine ⟨h₁.1, h₂.2.1, fun x => ?_⟩
  rcases h₁.2.2 x with ⟨ht, he⟩ | he
  · rcases h₂.2.2 x with ⟨_, he'⟩ | he'
    · exact .inl ⟨ht, he.trans he'⟩
    · exact .inl ⟨ht, he'.symm ▸ he⟩
  · rw [he]; exact h₂.2.2 x

theorem Approx.sub {Γ Γ' : RCtx} {α : Type} (l' : Locals E.layout Γ') {m m' : EM E Γ' α}
    (h : Approx m m') : Approx (EM.sub (Γ := Γ) l' m) (EM.sub l' m') := by
  refine ⟨Grow.sub l' h.1, Grow.sub l' h.2.1, fun x => ?_⟩
  rcases x with ⟨l, s⟩
  rw [run_sub, run_sub]
  rcases h.2.2 (l', s) with ⟨ht, he⟩ | he
  · left
    rcases hr : m.run (l', s) with ⟨r, l₁, s₁⟩
    rw [hr] at ht he
    cases ht
    refine ⟨rfl, ?_⟩
    rcases hr' : m'.run (l', s) with ⟨r', l₂, s₂⟩
    rw [hr'] at he
    cases r' <;> exact he
  · right
    rw [he]

/-- A halt caught by `attempt`: the continuation re-raises a timeout
without adding events. -/
theorem Approx.attempt_bind {Γ : RCtx} {α β : Type} {m m' : EM E Γ α} {k k' : Except Halt α → EM E Γ β}
    (hm : Approx m m') (hk : ∀ r, Approx (k r) (k' r))
    (h0 : ∀ x, ((k (.error .timeout)).run x).1 = .error .timeout ∧
      ((k (.error .timeout)).run x).2.2.events = x.2.events) :
    Approx (EM.attempt m >>= k) (EM.attempt m' >>= k') := by
  refine ⟨Grow.bind (Grow.attempt hm.1) fun r => (hk r).1, Grow.bind (Grow.attempt hm.2.1) fun r => (hk r).2.1,
    fun x => ?_⟩
  rw [run_bind, run_bind, run_attempt, run_attempt]
  rcases hm.2.2 x with ⟨ht, he⟩ | he
  · left
    rw [ht]
    refine ⟨(h0 _).1, ?_⟩
    rw [(h0 _).2]
    exact he.trans ((hk _).2.1 _)
  · rw [he]
    exact (hk _).2.2 _

theorem Approx.forIn {Γ : RCtx} {α β : Type} (l : List α) (b : β) {f f' : α → β → EM E Γ (ForInStep β)}
    (h : ∀ a b, Approx (f a b) (f' a b)) : Approx (forIn l b f) (forIn l b f') := by
  induction l generalizing b with
  | nil => exact Approx.refl (Grow.pure _)
  | cons a as ih =>
    simp only [List.forIn_cons]
    refine Approx.bind (h a b) fun r => ?_
    cases r with
    | done _ => exact Approx.refl (Grow.pure _)
    | yield b' => exact ih b'

/-- Close `Approx (body at n) (body at n + 1)` as `below_go` does; where the
two sides agree, by `Grow` (`grow_go` with the second list). -/
syntax "approx_go" "[" ident,* "]" "[" ident,* "]" "[" ident,* "]" "[" ident,* "]" : tactic
macro_rules
  | `(tactic| approx_go [$ls,*] [$gs,*] [$bs,*] [$cs,*]) => `(tactic| repeat' (first
      | (with_reducible refine Approx.bind ?_ ?_)
      | (with_reducible exact Approx.refl (by grow_go [$gs,*]))
      | (first $[| with_reducible apply $ls:ident]*)
      | (with_reducible apply Approx.sub)
      | (refine Approx.attempt_bind ?_ ?_ ?_)
      | (with_reducible intro _)
      | (exact ⟨rfl, rfl⟩)
      | split
      | ((refine Approx.of_below ?_ ?_ ?_) <;> (first | (first $[| with_reducible apply $bs:ident]*) | (const_go [$cs,*])) <;> done)
      | (dsimp only)))

section
variable (G : Glob E)

/-- **The induction hypothesis**: every interpreter function at horizon `n`
approximates itself at `n + 1`. -/
structure ApproxAt (n : Nat) : Prop where
  evalE : ∀ (F : Fr) {Γ : RCtx} {τ : STy} (e : RExpr E Γ τ), Approx (evalE G F n e) (evalE G F (n + 1) e)
  evalPair : ∀ (F : Fr) {Γ : RCtx} {σ τ : STy} (a : RExpr E Γ σ) (b : RExpr E Γ τ),
    Approx (evalPair G F n a b) (evalPair G F (n + 1) a b)
  evalArgs : ∀ (F : Fr) {Γ : RCtx} {τs : List STy} (es : RArgs E Γ τs),
    Approx (evalArgs G F n es) (evalArgs G F (n + 1) es)
  evalConvArgs : ∀ (F : Fr) {Γ : RCtx} {τs : List STy} (es : RConvArgs E Γ τs),
    Approx (evalConvArgs G F n es) (evalConvArgs G F (n + 1) es)
  evalLoc : ∀ (F : Fr) {Γ : RCtx} {τ : STy} (l : RLVal E Γ τ), Approx (evalLoc G F n l) (evalLoc G F (n + 1) l)
  evalBuiltin : ∀ (F : Fr) {Γ : RCtx} {σs : List STy} (b : Builtin) (args : RArgs E Γ σs) (τ : STy),
    Approx (evalBuiltin G F n b args τ) (evalBuiltin G F (n + 1) b args τ)
  evalArgsRev : ∀ (F : Fr) {Γ : RCtx} {τs : List STy} (es : RArgs E Γ τs),
    Approx (evalArgsRev G F n es) (evalArgsRev G F (n + 1) es)
  pay : ∀ (F : Fr) {Γ : RCtx} (a : RExpr E Γ (.address true)) (v : RExpr E Γ (.int IntTy.u256)),
    Approx (pay G F n a v) (pay G F (n + 1) a v)
  execS : ∀ (F : Fr) (nps : Nat) (ph : Option (Ph E)) {R : List STy} {M : Bool} {k : SCtx} {Γ Γ' : RCtx}
    (s : RStmt E R M k Γ Γ') (l : Locals E.layout Γ),
    Approx (execS G F n nps ph s l) (execS G F (n + 1) nps ph s l)
  forIter : ∀ (F : Fr) (nps : Nat) (ph : Option (Ph E)) {R : List STy} {M u : Bool} {Γ₁ Γ₂ : RCtx}
    (c : ROptBool E Γ₁) (post : ROptExpr E Γ₁) (body : RStmt E R M ⟨true, u⟩ Γ₁ Γ₂) (l : Locals E.layout Γ₁),
    Approx (forIter G F n nps ph c post body l) (forIter G F (n + 1) nps ph c post body l)
  execItems : ∀ (F : Fr) (nps : Nat) (ph : Option (Ph E)) {R : List STy} {M : Bool} {k : SCtx} {Γ Γ' : RCtx}
    (b : RItems E R M k Γ Γ') (l : Locals E.layout Γ),
    Approx (execItems G F n nps ph b l) (execItems G F (n + 1) nps ph b l)
  runMods : ∀ (F : Fr) (b : RBody E) (mods : List (RModInv E b.locals)) (l : Locals E.layout b.locals),
    Approx (runMods G F n b mods l) (runMods G F (n + 1) b mods l)
  callInternal : ∀ (F : Fr) (d : Decl) {ps : List STy} (vs : Vals E.layout ps) (rs : List STy),
    Approx (callInternal G F n d vs rs) (callInternal G F (n + 1) d vs rs)
  callAddr : ∀ (F : Fr) (a : Solidity.Roadmap.Address) (v : Solidity.Roadmap.Word) (input : Solidity.Roadmap.Bytes)
    (static : Bool), Approx (callAddr G F n a v input static) (callAddr G F (n + 1) a v input static)
  enterInstance : ∀ (a sender : Solidity.Roadmap.Address) (v : Solidity.Roadmap.Word) (input : Solidity.Roadmap.Bytes)
    (static : Bool) (c : String) (depth : Nat) (m : Nat × Nat × Heap E.layout),
    Approx (enterInstance G n a sender v input static c depth m)
      (enterInstance G (n + 1) a sender v input static c depth m)
  envLoop : ∀ (depth : Nat) (pstatic : Bool), Approx (envLoop G n depth pstatic) (envLoop G (n + 1) depth pstatic)
  dispatch : ∀ (F : Fr) (input : Solidity.Roadmap.Bytes), Approx (dispatch G F n input) (dispatch G F (n + 1) input)

theorem approxAt_zero : ApproxAt G 0 where
  evalE := by intros; rw [evalE.eq_1]; apply Approx.timeout; apply (growAt G (0 + 1)).evalE
  evalPair := by intros; rw [evalPair.eq_1]; apply Approx.timeout; apply (growAt G (0 + 1)).evalPair
  evalArgs := by intros; rw [evalArgs.eq_1]; apply Approx.timeout; apply (growAt G (0 + 1)).evalArgs
  evalConvArgs := by intros; rw [evalConvArgs.eq_1]; apply Approx.timeout; apply (growAt G (0 + 1)).evalConvArgs
  evalLoc := by intros; rw [evalLoc.eq_1]; apply Approx.timeout; apply (growAt G (0 + 1)).evalLoc
  evalBuiltin := by intros; rw [evalBuiltin.eq_1]; apply Approx.timeout; apply (growAt G (0 + 1)).evalBuiltin
  evalArgsRev := by intros; rw [evalArgsRev.eq_1]; apply Approx.timeout; apply (growAt G (0 + 1)).evalArgsRev
  pay := by intros; rw [pay.eq_1]; apply Approx.timeout; apply (growAt G (0 + 1)).pay
  execS := by intros; rw [execS.eq_1]; apply Approx.timeout; apply (growAt G (0 + 1)).execS
  forIter := by intros; rw [forIter.eq_1]; apply Approx.timeout; apply (growAt G (0 + 1)).forIter
  execItems := by intros; rw [execItems.eq_1]; apply Approx.timeout; apply (growAt G (0 + 1)).execItems
  runMods := by intros; rw [runMods.eq_1]; apply Approx.timeout; apply (growAt G (0 + 1)).runMods
  callInternal := by intros; rw [callInternal.eq_1]; apply Approx.timeout; apply (growAt G (0 + 1)).callInternal
  callAddr := by intros; rw [callAddr.eq_1]; apply Approx.timeout; apply (growAt G (0 + 1)).callAddr
  enterInstance := by intros; rw [enterInstance.eq_1]; apply Approx.timeout; apply (growAt G (0 + 1)).enterInstance
  envLoop := by intros; rw [envLoop.eq_1]; apply Approx.timeout; apply (growAt G (0 + 1)).envLoop
  dispatch := by intros; rw [dispatch.eq_1]; apply Approx.timeout; apply (growAt G (0 + 1)).dispatch

variable {G} {n : Nat}

theorem evalE_apart_0 {G : Glob E} {n : Nat} (ih : ApproxAt G n) (F : Fr) {Γ : RCtx} {τ : STy} (e : RExpr E Γ τ)
    (h : 0 ≤ e.ctorIdx ∧ e.ctorIdx < 12) : Approx (evalE G F (n + 1) e) (evalE G F (n + 1 + 1) e) := by
  have gn := growAt G n
  have gs := growAt G (n + 1)
  cases e <;> first | (exfalso; simp only [RExpr.ctorIdx] at h; omega) | (below_unfold evalE n; approx_go [ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, Approx.sub] [heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow, memElem_grow, readLoc_grow, lengthOf_grow, indexLoc_grow, indexNat_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow, fieldsOf_grow, ret32_grow, decodeArgs_grow, bytesOfRV_grow, encodeVals_grow, convRV_grow, convExplicitRV_grow, writeLoc_grow, deleteLoc_grow, keyStep_grow, zeroVals_grow, zeroInner_grow, copyInto_grow, getterPath_grow, extReturn_grow, gn.evalE, gn.evalPair, gn.evalArgs, gn.evalConvArgs, gn.evalLoc, gn.evalBuiltin, gn.evalArgsRev, gn.pay, gn.execS, gn.forIter, gn.execItems, gn.runMods, gn.callInternal, gn.callAddr, gn.enterInstance, gn.envLoop, gn.dispatch, gs.evalE, gs.evalPair, gs.evalArgs, gs.evalConvArgs, gs.evalLoc, gs.evalBuiltin, gs.evalArgsRev, gs.pay, gs.execS, gs.forIter, gs.execItems, gs.runMods, gs.callInternal, gs.callAddr, gs.enterInstance, gs.envLoop, gs.dispatch] [convRV_below, convExplicitRV_below, bytesOfRV_below, encodeVals_below, writeLoc_below, deleteLoc_below, keyStep_below, zeroVals_below, zeroInner_below, zeroVal_below, getterPath_below, copyInto_below, storeData_below, storeVal_below, loadMem_below, deleteStor_below] [heapPut_const, alloc_const, readCell_const, readAt_const, applyOp_const, setCell_const, writeAt_const, readLen_const, writeLen_const, heapObj_const, heapAt_const, heapBytes_const, allocRef_const, storRef_const, getV_const, zeroVal_const, zeroData_const, loadMem_const, deleteStor_const, storeData_const, storeVal_const, memSet_const, memElem_const, readLoc_const, lengthOf_const, indexLoc_const, indexNat_const, instanceAt_const, credit_const, debit_const, mark_const, rollbackTo_const, reraise_const, fieldsOf_const, ret32_const, decodeArgs_const, bytesOfRV_const, encodeVals_const, convRV_const, convExplicitRV_const, writeLoc_const, deleteLoc_const, keyStep_const, zeroVals_const, zeroInner_const, copyInto_const, getterPath_const, extReturn_const])
theorem evalE_apart_1 {G : Glob E} {n : Nat} (ih : ApproxAt G n) (F : Fr) {Γ : RCtx} {τ : STy} (e : RExpr E Γ τ)
    (h : 12 ≤ e.ctorIdx ∧ e.ctorIdx < 24) : Approx (evalE G F (n + 1) e) (evalE G F (n + 1 + 1) e) := by
  have gn := growAt G n
  have gs := growAt G (n + 1)
  cases e <;> first | (exfalso; simp only [RExpr.ctorIdx] at h; omega) | (below_unfold evalE n; approx_go [ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, Approx.sub] [heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow, memElem_grow, readLoc_grow, lengthOf_grow, indexLoc_grow, indexNat_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow, fieldsOf_grow, ret32_grow, decodeArgs_grow, bytesOfRV_grow, encodeVals_grow, convRV_grow, convExplicitRV_grow, writeLoc_grow, deleteLoc_grow, keyStep_grow, zeroVals_grow, zeroInner_grow, copyInto_grow, getterPath_grow, extReturn_grow, gn.evalE, gn.evalPair, gn.evalArgs, gn.evalConvArgs, gn.evalLoc, gn.evalBuiltin, gn.evalArgsRev, gn.pay, gn.execS, gn.forIter, gn.execItems, gn.runMods, gn.callInternal, gn.callAddr, gn.enterInstance, gn.envLoop, gn.dispatch, gs.evalE, gs.evalPair, gs.evalArgs, gs.evalConvArgs, gs.evalLoc, gs.evalBuiltin, gs.evalArgsRev, gs.pay, gs.execS, gs.forIter, gs.execItems, gs.runMods, gs.callInternal, gs.callAddr, gs.enterInstance, gs.envLoop, gs.dispatch] [convRV_below, convExplicitRV_below, bytesOfRV_below, encodeVals_below, writeLoc_below, deleteLoc_below, keyStep_below, zeroVals_below, zeroInner_below, zeroVal_below, getterPath_below, copyInto_below, storeData_below, storeVal_below, loadMem_below, deleteStor_below] [heapPut_const, alloc_const, readCell_const, readAt_const, applyOp_const, setCell_const, writeAt_const, readLen_const, writeLen_const, heapObj_const, heapAt_const, heapBytes_const, allocRef_const, storRef_const, getV_const, zeroVal_const, zeroData_const, loadMem_const, deleteStor_const, storeData_const, storeVal_const, memSet_const, memElem_const, readLoc_const, lengthOf_const, indexLoc_const, indexNat_const, instanceAt_const, credit_const, debit_const, mark_const, rollbackTo_const, reraise_const, fieldsOf_const, ret32_const, decodeArgs_const, bytesOfRV_const, encodeVals_const, convRV_const, convExplicitRV_const, writeLoc_const, deleteLoc_const, keyStep_const, zeroVals_const, zeroInner_const, copyInto_const, getterPath_const, extReturn_const])
theorem evalE_apart_2 {G : Glob E} {n : Nat} (ih : ApproxAt G n) (F : Fr) {Γ : RCtx} {τ : STy} (e : RExpr E Γ τ)
    (h : 24 ≤ e.ctorIdx ∧ e.ctorIdx < 28) : Approx (evalE G F (n + 1) e) (evalE G F (n + 1 + 1) e) := by
  have gn := growAt G n
  have gs := growAt G (n + 1)
  cases e <;> first | (exfalso; simp only [RExpr.ctorIdx] at h; omega) | (below_unfold evalE n; approx_go [ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, Approx.sub] [heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow, memElem_grow, readLoc_grow, lengthOf_grow, indexLoc_grow, indexNat_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow, fieldsOf_grow, ret32_grow, decodeArgs_grow, bytesOfRV_grow, encodeVals_grow, convRV_grow, convExplicitRV_grow, writeLoc_grow, deleteLoc_grow, keyStep_grow, zeroVals_grow, zeroInner_grow, copyInto_grow, getterPath_grow, extReturn_grow, gn.evalE, gn.evalPair, gn.evalArgs, gn.evalConvArgs, gn.evalLoc, gn.evalBuiltin, gn.evalArgsRev, gn.pay, gn.execS, gn.forIter, gn.execItems, gn.runMods, gn.callInternal, gn.callAddr, gn.enterInstance, gn.envLoop, gn.dispatch, gs.evalE, gs.evalPair, gs.evalArgs, gs.evalConvArgs, gs.evalLoc, gs.evalBuiltin, gs.evalArgsRev, gs.pay, gs.execS, gs.forIter, gs.execItems, gs.runMods, gs.callInternal, gs.callAddr, gs.enterInstance, gs.envLoop, gs.dispatch] [convRV_below, convExplicitRV_below, bytesOfRV_below, encodeVals_below, writeLoc_below, deleteLoc_below, keyStep_below, zeroVals_below, zeroInner_below, zeroVal_below, getterPath_below, copyInto_below, storeData_below, storeVal_below, loadMem_below, deleteStor_below] [heapPut_const, alloc_const, readCell_const, readAt_const, applyOp_const, setCell_const, writeAt_const, readLen_const, writeLen_const, heapObj_const, heapAt_const, heapBytes_const, allocRef_const, storRef_const, getV_const, zeroVal_const, zeroData_const, loadMem_const, deleteStor_const, storeData_const, storeVal_const, memSet_const, memElem_const, readLoc_const, lengthOf_const, indexLoc_const, indexNat_const, instanceAt_const, credit_const, debit_const, mark_const, rollbackTo_const, reraise_const, fieldsOf_const, ret32_const, decodeArgs_const, bytesOfRV_const, encodeVals_const, convRV_const, convExplicitRV_const, writeLoc_const, deleteLoc_const, keyStep_const, zeroVals_const, zeroInner_const, copyInto_const, getterPath_const, extReturn_const])
theorem evalE_apart_3 {G : Glob E} {n : Nat} (ih : ApproxAt G n) (F : Fr) {Γ : RCtx} {τ : STy} (e : RExpr E Γ τ)
    (h : 28 ≤ e.ctorIdx ∧ e.ctorIdx < 32) : Approx (evalE G F (n + 1) e) (evalE G F (n + 1 + 1) e) := by
  have gn := growAt G n
  have gs := growAt G (n + 1)
  cases e <;> first | (exfalso; simp only [RExpr.ctorIdx] at h; omega) | (below_unfold evalE n; approx_go [ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, Approx.sub] [heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow, memElem_grow, readLoc_grow, lengthOf_grow, indexLoc_grow, indexNat_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow, fieldsOf_grow, ret32_grow, decodeArgs_grow, bytesOfRV_grow, encodeVals_grow, convRV_grow, convExplicitRV_grow, writeLoc_grow, deleteLoc_grow, keyStep_grow, zeroVals_grow, zeroInner_grow, copyInto_grow, getterPath_grow, extReturn_grow, gn.evalE, gn.evalPair, gn.evalArgs, gn.evalConvArgs, gn.evalLoc, gn.evalBuiltin, gn.evalArgsRev, gn.pay, gn.execS, gn.forIter, gn.execItems, gn.runMods, gn.callInternal, gn.callAddr, gn.enterInstance, gn.envLoop, gn.dispatch, gs.evalE, gs.evalPair, gs.evalArgs, gs.evalConvArgs, gs.evalLoc, gs.evalBuiltin, gs.evalArgsRev, gs.pay, gs.execS, gs.forIter, gs.execItems, gs.runMods, gs.callInternal, gs.callAddr, gs.enterInstance, gs.envLoop, gs.dispatch] [convRV_below, convExplicitRV_below, bytesOfRV_below, encodeVals_below, writeLoc_below, deleteLoc_below, keyStep_below, zeroVals_below, zeroInner_below, zeroVal_below, getterPath_below, copyInto_below, storeData_below, storeVal_below, loadMem_below, deleteStor_below] [heapPut_const, alloc_const, readCell_const, readAt_const, applyOp_const, setCell_const, writeAt_const, readLen_const, writeLen_const, heapObj_const, heapAt_const, heapBytes_const, allocRef_const, storRef_const, getV_const, zeroVal_const, zeroData_const, loadMem_const, deleteStor_const, storeData_const, storeVal_const, memSet_const, memElem_const, readLoc_const, lengthOf_const, indexLoc_const, indexNat_const, instanceAt_const, credit_const, debit_const, mark_const, rollbackTo_const, reraise_const, fieldsOf_const, ret32_const, decodeArgs_const, bytesOfRV_const, encodeVals_const, convRV_const, convExplicitRV_const, writeLoc_const, deleteLoc_const, keyStep_const, zeroVals_const, zeroInner_const, copyInto_const, getterPath_const, extReturn_const])
theorem evalE_apart_4 {G : Glob E} {n : Nat} (ih : ApproxAt G n) (F : Fr) {Γ : RCtx} {τ : STy} (e : RExpr E Γ τ)
    (h : 32 ≤ e.ctorIdx ∧ e.ctorIdx < 33) : Approx (evalE G F (n + 1) e) (evalE G F (n + 1 + 1) e) := by
  have gn := growAt G n
  have gs := growAt G (n + 1)
  cases e <;> first | (exfalso; simp only [RExpr.ctorIdx] at h; omega) | (below_unfold evalE n; approx_go [ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, Approx.sub] [heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow, memElem_grow, readLoc_grow, lengthOf_grow, indexLoc_grow, indexNat_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow, fieldsOf_grow, ret32_grow, decodeArgs_grow, bytesOfRV_grow, encodeVals_grow, convRV_grow, convExplicitRV_grow, writeLoc_grow, deleteLoc_grow, keyStep_grow, zeroVals_grow, zeroInner_grow, copyInto_grow, getterPath_grow, extReturn_grow, gn.evalE, gn.evalPair, gn.evalArgs, gn.evalConvArgs, gn.evalLoc, gn.evalBuiltin, gn.evalArgsRev, gn.pay, gn.execS, gn.forIter, gn.execItems, gn.runMods, gn.callInternal, gn.callAddr, gn.enterInstance, gn.envLoop, gn.dispatch, gs.evalE, gs.evalPair, gs.evalArgs, gs.evalConvArgs, gs.evalLoc, gs.evalBuiltin, gs.evalArgsRev, gs.pay, gs.execS, gs.forIter, gs.execItems, gs.runMods, gs.callInternal, gs.callAddr, gs.enterInstance, gs.envLoop, gs.dispatch] [convRV_below, convExplicitRV_below, bytesOfRV_below, encodeVals_below, writeLoc_below, deleteLoc_below, keyStep_below, zeroVals_below, zeroInner_below, zeroVal_below, getterPath_below, copyInto_below, storeData_below, storeVal_below, loadMem_below, deleteStor_below] [heapPut_const, alloc_const, readCell_const, readAt_const, applyOp_const, setCell_const, writeAt_const, readLen_const, writeLen_const, heapObj_const, heapAt_const, heapBytes_const, allocRef_const, storRef_const, getV_const, zeroVal_const, zeroData_const, loadMem_const, deleteStor_const, storeData_const, storeVal_const, memSet_const, memElem_const, readLoc_const, lengthOf_const, indexLoc_const, indexNat_const, instanceAt_const, credit_const, debit_const, mark_const, rollbackTo_const, reraise_const, fieldsOf_const, ret32_const, decodeArgs_const, bytesOfRV_const, encodeVals_const, convRV_const, convExplicitRV_const, writeLoc_const, deleteLoc_const, keyStep_const, zeroVals_const, zeroInner_const, copyInto_const, getterPath_const, extReturn_const])
theorem evalE_apart_5 {G : Glob E} {n : Nat} (ih : ApproxAt G n) (F : Fr) {Γ : RCtx} {τ : STy} (e : RExpr E Γ τ)
    (h : 33 ≤ e.ctorIdx ∧ e.ctorIdx < 34) : Approx (evalE G F (n + 1) e) (evalE G F (n + 1 + 1) e) := by
  have gn := growAt G n
  have gs := growAt G (n + 1)
  cases e <;> first | (exfalso; simp only [RExpr.ctorIdx] at h; omega) | (below_unfold evalE n; approx_go [ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, Approx.sub] [heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow, memElem_grow, readLoc_grow, lengthOf_grow, indexLoc_grow, indexNat_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow, fieldsOf_grow, ret32_grow, decodeArgs_grow, bytesOfRV_grow, encodeVals_grow, convRV_grow, convExplicitRV_grow, writeLoc_grow, deleteLoc_grow, keyStep_grow, zeroVals_grow, zeroInner_grow, copyInto_grow, getterPath_grow, extReturn_grow, gn.evalE, gn.evalPair, gn.evalArgs, gn.evalConvArgs, gn.evalLoc, gn.evalBuiltin, gn.evalArgsRev, gn.pay, gn.execS, gn.forIter, gn.execItems, gn.runMods, gn.callInternal, gn.callAddr, gn.enterInstance, gn.envLoop, gn.dispatch, gs.evalE, gs.evalPair, gs.evalArgs, gs.evalConvArgs, gs.evalLoc, gs.evalBuiltin, gs.evalArgsRev, gs.pay, gs.execS, gs.forIter, gs.execItems, gs.runMods, gs.callInternal, gs.callAddr, gs.enterInstance, gs.envLoop, gs.dispatch] [convRV_below, convExplicitRV_below, bytesOfRV_below, encodeVals_below, writeLoc_below, deleteLoc_below, keyStep_below, zeroVals_below, zeroInner_below, zeroVal_below, getterPath_below, copyInto_below, storeData_below, storeVal_below, loadMem_below, deleteStor_below] [heapPut_const, alloc_const, readCell_const, readAt_const, applyOp_const, setCell_const, writeAt_const, readLen_const, writeLen_const, heapObj_const, heapAt_const, heapBytes_const, allocRef_const, storRef_const, getV_const, zeroVal_const, zeroData_const, loadMem_const, deleteStor_const, storeData_const, storeVal_const, memSet_const, memElem_const, readLoc_const, lengthOf_const, indexLoc_const, indexNat_const, instanceAt_const, credit_const, debit_const, mark_const, rollbackTo_const, reraise_const, fieldsOf_const, ret32_const, decodeArgs_const, bytesOfRV_const, encodeVals_const, convRV_const, convExplicitRV_const, writeLoc_const, deleteLoc_const, keyStep_const, zeroVals_const, zeroInner_const, copyInto_const, getterPath_const, extReturn_const])
theorem evalE_apart_6 {G : Glob E} {n : Nat} (ih : ApproxAt G n) (F : Fr) {Γ : RCtx} {τ : STy} (e : RExpr E Γ τ)
    (h : 34 ≤ e.ctorIdx ∧ e.ctorIdx < 35) : Approx (evalE G F (n + 1) e) (evalE G F (n + 1 + 1) e) := by
  have gn := growAt G n
  have gs := growAt G (n + 1)
  cases e <;> first | (exfalso; simp only [RExpr.ctorIdx] at h; omega) | (below_unfold evalE n; approx_go [ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, Approx.sub] [heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow, memElem_grow, readLoc_grow, lengthOf_grow, indexLoc_grow, indexNat_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow, fieldsOf_grow, ret32_grow, decodeArgs_grow, bytesOfRV_grow, encodeVals_grow, convRV_grow, convExplicitRV_grow, writeLoc_grow, deleteLoc_grow, keyStep_grow, zeroVals_grow, zeroInner_grow, copyInto_grow, getterPath_grow, extReturn_grow, gn.evalE, gn.evalPair, gn.evalArgs, gn.evalConvArgs, gn.evalLoc, gn.evalBuiltin, gn.evalArgsRev, gn.pay, gn.execS, gn.forIter, gn.execItems, gn.runMods, gn.callInternal, gn.callAddr, gn.enterInstance, gn.envLoop, gn.dispatch, gs.evalE, gs.evalPair, gs.evalArgs, gs.evalConvArgs, gs.evalLoc, gs.evalBuiltin, gs.evalArgsRev, gs.pay, gs.execS, gs.forIter, gs.execItems, gs.runMods, gs.callInternal, gs.callAddr, gs.enterInstance, gs.envLoop, gs.dispatch] [convRV_below, convExplicitRV_below, bytesOfRV_below, encodeVals_below, writeLoc_below, deleteLoc_below, keyStep_below, zeroVals_below, zeroInner_below, zeroVal_below, getterPath_below, copyInto_below, storeData_below, storeVal_below, loadMem_below, deleteStor_below] [heapPut_const, alloc_const, readCell_const, readAt_const, applyOp_const, setCell_const, writeAt_const, readLen_const, writeLen_const, heapObj_const, heapAt_const, heapBytes_const, allocRef_const, storRef_const, getV_const, zeroVal_const, zeroData_const, loadMem_const, deleteStor_const, storeData_const, storeVal_const, memSet_const, memElem_const, readLoc_const, lengthOf_const, indexLoc_const, indexNat_const, instanceAt_const, credit_const, debit_const, mark_const, rollbackTo_const, reraise_const, fieldsOf_const, ret32_const, decodeArgs_const, bytesOfRV_const, encodeVals_const, convRV_const, convExplicitRV_const, writeLoc_const, deleteLoc_const, keyStep_const, zeroVals_const, zeroInner_const, copyInto_const, getterPath_const, extReturn_const])
theorem evalE_apart_7 {G : Glob E} {n : Nat} (ih : ApproxAt G n) (F : Fr) {Γ : RCtx} {τ : STy} (e : RExpr E Γ τ)
    (h : 35 ≤ e.ctorIdx ∧ e.ctorIdx < 36) : Approx (evalE G F (n + 1) e) (evalE G F (n + 1 + 1) e) := by
  have gn := growAt G n
  have gs := growAt G (n + 1)
  cases e <;> first | (exfalso; simp only [RExpr.ctorIdx] at h; omega) | (below_unfold evalE n; approx_go [ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, Approx.sub] [heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow, memElem_grow, readLoc_grow, lengthOf_grow, indexLoc_grow, indexNat_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow, fieldsOf_grow, ret32_grow, decodeArgs_grow, bytesOfRV_grow, encodeVals_grow, convRV_grow, convExplicitRV_grow, writeLoc_grow, deleteLoc_grow, keyStep_grow, zeroVals_grow, zeroInner_grow, copyInto_grow, getterPath_grow, extReturn_grow, gn.evalE, gn.evalPair, gn.evalArgs, gn.evalConvArgs, gn.evalLoc, gn.evalBuiltin, gn.evalArgsRev, gn.pay, gn.execS, gn.forIter, gn.execItems, gn.runMods, gn.callInternal, gn.callAddr, gn.enterInstance, gn.envLoop, gn.dispatch, gs.evalE, gs.evalPair, gs.evalArgs, gs.evalConvArgs, gs.evalLoc, gs.evalBuiltin, gs.evalArgsRev, gs.pay, gs.execS, gs.forIter, gs.execItems, gs.runMods, gs.callInternal, gs.callAddr, gs.enterInstance, gs.envLoop, gs.dispatch] [convRV_below, convExplicitRV_below, bytesOfRV_below, encodeVals_below, writeLoc_below, deleteLoc_below, keyStep_below, zeroVals_below, zeroInner_below, zeroVal_below, getterPath_below, copyInto_below, storeData_below, storeVal_below, loadMem_below, deleteStor_below] [heapPut_const, alloc_const, readCell_const, readAt_const, applyOp_const, setCell_const, writeAt_const, readLen_const, writeLen_const, heapObj_const, heapAt_const, heapBytes_const, allocRef_const, storRef_const, getV_const, zeroVal_const, zeroData_const, loadMem_const, deleteStor_const, storeData_const, storeVal_const, memSet_const, memElem_const, readLoc_const, lengthOf_const, indexLoc_const, indexNat_const, instanceAt_const, credit_const, debit_const, mark_const, rollbackTo_const, reraise_const, fieldsOf_const, ret32_const, decodeArgs_const, bytesOfRV_const, encodeVals_const, convRV_const, convExplicitRV_const, writeLoc_const, deleteLoc_const, keyStep_const, zeroVals_const, zeroInner_const, copyInto_const, getterPath_const, extReturn_const])
theorem evalE_apart_8 {G : Glob E} {n : Nat} (ih : ApproxAt G n) (F : Fr) {Γ : RCtx} {τ : STy} (e : RExpr E Γ τ)
    (h : 36 ≤ e.ctorIdx ∧ e.ctorIdx < 60) : Approx (evalE G F (n + 1) e) (evalE G F (n + 1 + 1) e) := by
  have gn := growAt G n
  have gs := growAt G (n + 1)
  cases e <;> first | (exfalso; simp only [RExpr.ctorIdx] at h; omega) | (below_unfold evalE n; approx_go [ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, Approx.sub] [heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow, memElem_grow, readLoc_grow, lengthOf_grow, indexLoc_grow, indexNat_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow, fieldsOf_grow, ret32_grow, decodeArgs_grow, bytesOfRV_grow, encodeVals_grow, convRV_grow, convExplicitRV_grow, writeLoc_grow, deleteLoc_grow, keyStep_grow, zeroVals_grow, zeroInner_grow, copyInto_grow, getterPath_grow, extReturn_grow, gn.evalE, gn.evalPair, gn.evalArgs, gn.evalConvArgs, gn.evalLoc, gn.evalBuiltin, gn.evalArgsRev, gn.pay, gn.execS, gn.forIter, gn.execItems, gn.runMods, gn.callInternal, gn.callAddr, gn.enterInstance, gn.envLoop, gn.dispatch, gs.evalE, gs.evalPair, gs.evalArgs, gs.evalConvArgs, gs.evalLoc, gs.evalBuiltin, gs.evalArgsRev, gs.pay, gs.execS, gs.forIter, gs.execItems, gs.runMods, gs.callInternal, gs.callAddr, gs.enterInstance, gs.envLoop, gs.dispatch] [convRV_below, convExplicitRV_below, bytesOfRV_below, encodeVals_below, writeLoc_below, deleteLoc_below, keyStep_below, zeroVals_below, zeroInner_below, zeroVal_below, getterPath_below, copyInto_below, storeData_below, storeVal_below, loadMem_below, deleteStor_below] [heapPut_const, alloc_const, readCell_const, readAt_const, applyOp_const, setCell_const, writeAt_const, readLen_const, writeLen_const, heapObj_const, heapAt_const, heapBytes_const, allocRef_const, storRef_const, getV_const, zeroVal_const, zeroData_const, loadMem_const, deleteStor_const, storeData_const, storeVal_const, memSet_const, memElem_const, readLoc_const, lengthOf_const, indexLoc_const, indexNat_const, instanceAt_const, credit_const, debit_const, mark_const, rollbackTo_const, reraise_const, fieldsOf_const, ret32_const, decodeArgs_const, bytesOfRV_const, encodeVals_const, convRV_const, convExplicitRV_const, writeLoc_const, deleteLoc_const, keyStep_const, zeroVals_const, zeroInner_const, copyInto_const, getterPath_const, extReturn_const])
theorem evalE_astep (ih : ApproxAt G n) (F : Fr) {Γ : RCtx} {τ : STy} (e : RExpr E Γ τ) :
    Approx (evalE G F (n + 1) e) (evalE G F (n + 1 + 1) e) := by
  by_cases h0 : e.ctorIdx < 12
  · exact evalE_apart_0 ih F e ⟨by omega, h0⟩
  by_cases h1 : e.ctorIdx < 24
  · exact evalE_apart_1 ih F e ⟨by omega, h1⟩
  by_cases h2 : e.ctorIdx < 28
  · exact evalE_apart_2 ih F e ⟨by omega, h2⟩
  by_cases h3 : e.ctorIdx < 32
  · exact evalE_apart_3 ih F e ⟨by omega, h3⟩
  by_cases h4 : e.ctorIdx < 33
  · exact evalE_apart_4 ih F e ⟨by omega, h4⟩
  by_cases h5 : e.ctorIdx < 34
  · exact evalE_apart_5 ih F e ⟨by omega, h5⟩
  by_cases h6 : e.ctorIdx < 35
  · exact evalE_apart_6 ih F e ⟨by omega, h6⟩
  by_cases h7 : e.ctorIdx < 36
  · exact evalE_apart_7 ih F e ⟨by omega, h7⟩
  have hl : e.ctorIdx < 60 := by cases e <;> simp only [RExpr.ctorIdx] <;> omega
  exact evalE_apart_8 ih F e ⟨by omega, hl⟩
theorem evalPair_astep (ih : ApproxAt G n) (F : Fr) {Γ : RCtx} {σ τ : STy} (a : RExpr E Γ σ) (b : RExpr E Γ τ) :
    Approx (evalPair G F (n + 1) a b) (evalPair G F (n + 1 + 1) a b) := by
  have gn := growAt G n
  have gs := growAt G (n + 1)
  below_unfold evalPair n
  approx_go [ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, Approx.sub] [heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow, memElem_grow, readLoc_grow, lengthOf_grow, indexLoc_grow, indexNat_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow, fieldsOf_grow, ret32_grow, decodeArgs_grow, bytesOfRV_grow, encodeVals_grow, convRV_grow, convExplicitRV_grow, writeLoc_grow, deleteLoc_grow, keyStep_grow, zeroVals_grow, zeroInner_grow, copyInto_grow, getterPath_grow, extReturn_grow, gn.evalE, gn.evalPair, gn.evalArgs, gn.evalConvArgs, gn.evalLoc, gn.evalBuiltin, gn.evalArgsRev, gn.pay, gn.execS, gn.forIter, gn.execItems, gn.runMods, gn.callInternal, gn.callAddr, gn.enterInstance, gn.envLoop, gn.dispatch, gs.evalE, gs.evalPair, gs.evalArgs, gs.evalConvArgs, gs.evalLoc, gs.evalBuiltin, gs.evalArgsRev, gs.pay, gs.execS, gs.forIter, gs.execItems, gs.runMods, gs.callInternal, gs.callAddr, gs.enterInstance, gs.envLoop, gs.dispatch] [convRV_below, convExplicitRV_below, bytesOfRV_below, encodeVals_below, writeLoc_below, deleteLoc_below, keyStep_below, zeroVals_below, zeroInner_below, zeroVal_below, getterPath_below, copyInto_below, storeData_below, storeVal_below, loadMem_below, deleteStor_below] [heapPut_const, alloc_const, readCell_const, readAt_const, applyOp_const, setCell_const, writeAt_const, readLen_const, writeLen_const, heapObj_const, heapAt_const, heapBytes_const, allocRef_const, storRef_const, getV_const, zeroVal_const, zeroData_const, loadMem_const, deleteStor_const, storeData_const, storeVal_const, memSet_const, memElem_const, readLoc_const, lengthOf_const, indexLoc_const, indexNat_const, instanceAt_const, credit_const, debit_const, mark_const, rollbackTo_const, reraise_const, fieldsOf_const, ret32_const, decodeArgs_const, bytesOfRV_const, encodeVals_const, convRV_const, convExplicitRV_const, writeLoc_const, deleteLoc_const, keyStep_const, zeroVals_const, zeroInner_const, copyInto_const, getterPath_const, extReturn_const]
theorem evalArgs_astep (ih : ApproxAt G n) (F : Fr) {Γ : RCtx} {τs : List STy} (es : RArgs E Γ τs) :
    Approx (evalArgs G F (n + 1) es) (evalArgs G F (n + 1 + 1) es) := by
  have gn := growAt G n
  have gs := growAt G (n + 1)
  cases es <;> below_unfold evalArgs n <;> approx_go [ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, Approx.sub] [heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow, memElem_grow, readLoc_grow, lengthOf_grow, indexLoc_grow, indexNat_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow, fieldsOf_grow, ret32_grow, decodeArgs_grow, bytesOfRV_grow, encodeVals_grow, convRV_grow, convExplicitRV_grow, writeLoc_grow, deleteLoc_grow, keyStep_grow, zeroVals_grow, zeroInner_grow, copyInto_grow, getterPath_grow, extReturn_grow, gn.evalE, gn.evalPair, gn.evalArgs, gn.evalConvArgs, gn.evalLoc, gn.evalBuiltin, gn.evalArgsRev, gn.pay, gn.execS, gn.forIter, gn.execItems, gn.runMods, gn.callInternal, gn.callAddr, gn.enterInstance, gn.envLoop, gn.dispatch, gs.evalE, gs.evalPair, gs.evalArgs, gs.evalConvArgs, gs.evalLoc, gs.evalBuiltin, gs.evalArgsRev, gs.pay, gs.execS, gs.forIter, gs.execItems, gs.runMods, gs.callInternal, gs.callAddr, gs.enterInstance, gs.envLoop, gs.dispatch] [convRV_below, convExplicitRV_below, bytesOfRV_below, encodeVals_below, writeLoc_below, deleteLoc_below, keyStep_below, zeroVals_below, zeroInner_below, zeroVal_below, getterPath_below, copyInto_below, storeData_below, storeVal_below, loadMem_below, deleteStor_below] [heapPut_const, alloc_const, readCell_const, readAt_const, applyOp_const, setCell_const, writeAt_const, readLen_const, writeLen_const, heapObj_const, heapAt_const, heapBytes_const, allocRef_const, storRef_const, getV_const, zeroVal_const, zeroData_const, loadMem_const, deleteStor_const, storeData_const, storeVal_const, memSet_const, memElem_const, readLoc_const, lengthOf_const, indexLoc_const, indexNat_const, instanceAt_const, credit_const, debit_const, mark_const, rollbackTo_const, reraise_const, fieldsOf_const, ret32_const, decodeArgs_const, bytesOfRV_const, encodeVals_const, convRV_const, convExplicitRV_const, writeLoc_const, deleteLoc_const, keyStep_const, zeroVals_const, zeroInner_const, copyInto_const, getterPath_const, extReturn_const]
theorem evalConvArgs_astep (ih : ApproxAt G n) (F : Fr) {Γ : RCtx} {τs : List STy} (es : RConvArgs E Γ τs) :
    Approx (evalConvArgs G F (n + 1) es) (evalConvArgs G F (n + 1 + 1) es) := by
  have gn := growAt G n
  have gs := growAt G (n + 1)
  cases es <;> below_unfold evalConvArgs n <;> approx_go [ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, Approx.sub] [heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow, memElem_grow, readLoc_grow, lengthOf_grow, indexLoc_grow, indexNat_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow, fieldsOf_grow, ret32_grow, decodeArgs_grow, bytesOfRV_grow, encodeVals_grow, convRV_grow, convExplicitRV_grow, writeLoc_grow, deleteLoc_grow, keyStep_grow, zeroVals_grow, zeroInner_grow, copyInto_grow, getterPath_grow, extReturn_grow, gn.evalE, gn.evalPair, gn.evalArgs, gn.evalConvArgs, gn.evalLoc, gn.evalBuiltin, gn.evalArgsRev, gn.pay, gn.execS, gn.forIter, gn.execItems, gn.runMods, gn.callInternal, gn.callAddr, gn.enterInstance, gn.envLoop, gn.dispatch, gs.evalE, gs.evalPair, gs.evalArgs, gs.evalConvArgs, gs.evalLoc, gs.evalBuiltin, gs.evalArgsRev, gs.pay, gs.execS, gs.forIter, gs.execItems, gs.runMods, gs.callInternal, gs.callAddr, gs.enterInstance, gs.envLoop, gs.dispatch] [convRV_below, convExplicitRV_below, bytesOfRV_below, encodeVals_below, writeLoc_below, deleteLoc_below, keyStep_below, zeroVals_below, zeroInner_below, zeroVal_below, getterPath_below, copyInto_below, storeData_below, storeVal_below, loadMem_below, deleteStor_below] [heapPut_const, alloc_const, readCell_const, readAt_const, applyOp_const, setCell_const, writeAt_const, readLen_const, writeLen_const, heapObj_const, heapAt_const, heapBytes_const, allocRef_const, storRef_const, getV_const, zeroVal_const, zeroData_const, loadMem_const, deleteStor_const, storeData_const, storeVal_const, memSet_const, memElem_const, readLoc_const, lengthOf_const, indexLoc_const, indexNat_const, instanceAt_const, credit_const, debit_const, mark_const, rollbackTo_const, reraise_const, fieldsOf_const, ret32_const, decodeArgs_const, bytesOfRV_const, encodeVals_const, convRV_const, convExplicitRV_const, writeLoc_const, deleteLoc_const, keyStep_const, zeroVals_const, zeroInner_const, copyInto_const, getterPath_const, extReturn_const]
theorem evalLoc_astep (ih : ApproxAt G n) (F : Fr) {Γ : RCtx} {τ : STy} (l : RLVal E Γ τ) :
    Approx (evalLoc G F (n + 1) l) (evalLoc G F (n + 1 + 1) l) := by
  have gn := growAt G n
  have gs := growAt G (n + 1)
  cases l <;> below_unfold evalLoc n <;> approx_go [ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, Approx.sub] [heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow, memElem_grow, readLoc_grow, lengthOf_grow, indexLoc_grow, indexNat_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow, fieldsOf_grow, ret32_grow, decodeArgs_grow, bytesOfRV_grow, encodeVals_grow, convRV_grow, convExplicitRV_grow, writeLoc_grow, deleteLoc_grow, keyStep_grow, zeroVals_grow, zeroInner_grow, copyInto_grow, getterPath_grow, extReturn_grow, gn.evalE, gn.evalPair, gn.evalArgs, gn.evalConvArgs, gn.evalLoc, gn.evalBuiltin, gn.evalArgsRev, gn.pay, gn.execS, gn.forIter, gn.execItems, gn.runMods, gn.callInternal, gn.callAddr, gn.enterInstance, gn.envLoop, gn.dispatch, gs.evalE, gs.evalPair, gs.evalArgs, gs.evalConvArgs, gs.evalLoc, gs.evalBuiltin, gs.evalArgsRev, gs.pay, gs.execS, gs.forIter, gs.execItems, gs.runMods, gs.callInternal, gs.callAddr, gs.enterInstance, gs.envLoop, gs.dispatch] [convRV_below, convExplicitRV_below, bytesOfRV_below, encodeVals_below, writeLoc_below, deleteLoc_below, keyStep_below, zeroVals_below, zeroInner_below, zeroVal_below, getterPath_below, copyInto_below, storeData_below, storeVal_below, loadMem_below, deleteStor_below] [heapPut_const, alloc_const, readCell_const, readAt_const, applyOp_const, setCell_const, writeAt_const, readLen_const, writeLen_const, heapObj_const, heapAt_const, heapBytes_const, allocRef_const, storRef_const, getV_const, zeroVal_const, zeroData_const, loadMem_const, deleteStor_const, storeData_const, storeVal_const, memSet_const, memElem_const, readLoc_const, lengthOf_const, indexLoc_const, indexNat_const, instanceAt_const, credit_const, debit_const, mark_const, rollbackTo_const, reraise_const, fieldsOf_const, ret32_const, decodeArgs_const, bytesOfRV_const, encodeVals_const, convRV_const, convExplicitRV_const, writeLoc_const, deleteLoc_const, keyStep_const, zeroVals_const, zeroInner_const, copyInto_const, getterPath_const, extReturn_const]
theorem evalBuiltin_apart_0 {G : Glob E} {n : Nat} (ih : ApproxAt G n) (F : Fr) {Γ : RCtx} {σs : List STy}
    (b : Builtin) (args : RArgs E Γ σs) (τ : STy) (hb : b = .require ∨ b = .assert ∨ b = .revert) :
    Approx (evalBuiltin G F (n + 1) b args τ) (evalBuiltin G F (n + 1 + 1) b args τ) := by
  have gn := growAt G n
  have gs := growAt G (n + 1)
  rcases hb with rfl | rfl | rfl <;> below_unfold evalBuiltin n <;> approx_go [ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, Approx.sub] [heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow, memElem_grow, readLoc_grow, lengthOf_grow, indexLoc_grow, indexNat_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow, fieldsOf_grow, ret32_grow, decodeArgs_grow, bytesOfRV_grow, encodeVals_grow, convRV_grow, convExplicitRV_grow, writeLoc_grow, deleteLoc_grow, keyStep_grow, zeroVals_grow, zeroInner_grow, copyInto_grow, getterPath_grow, extReturn_grow, gn.evalE, gn.evalPair, gn.evalArgs, gn.evalConvArgs, gn.evalLoc, gn.evalBuiltin, gn.evalArgsRev, gn.pay, gn.execS, gn.forIter, gn.execItems, gn.runMods, gn.callInternal, gn.callAddr, gn.enterInstance, gn.envLoop, gn.dispatch, gs.evalE, gs.evalPair, gs.evalArgs, gs.evalConvArgs, gs.evalLoc, gs.evalBuiltin, gs.evalArgsRev, gs.pay, gs.execS, gs.forIter, gs.execItems, gs.runMods, gs.callInternal, gs.callAddr, gs.enterInstance, gs.envLoop, gs.dispatch] [convRV_below, convExplicitRV_below, bytesOfRV_below, encodeVals_below, writeLoc_below, deleteLoc_below, keyStep_below, zeroVals_below, zeroInner_below, zeroVal_below, getterPath_below, copyInto_below, storeData_below, storeVal_below, loadMem_below, deleteStor_below] [heapPut_const, alloc_const, readCell_const, readAt_const, applyOp_const, setCell_const, writeAt_const, readLen_const, writeLen_const, heapObj_const, heapAt_const, heapBytes_const, allocRef_const, storRef_const, getV_const, zeroVal_const, zeroData_const, loadMem_const, deleteStor_const, storeData_const, storeVal_const, memSet_const, memElem_const, readLoc_const, lengthOf_const, indexLoc_const, indexNat_const, instanceAt_const, credit_const, debit_const, mark_const, rollbackTo_const, reraise_const, fieldsOf_const, ret32_const, decodeArgs_const, bytesOfRV_const, encodeVals_const, convRV_const, convExplicitRV_const, writeLoc_const, deleteLoc_const, keyStep_const, zeroVals_const, zeroInner_const, copyInto_const, getterPath_const, extReturn_const]
theorem evalBuiltin_apart_1 {G : Glob E} {n : Nat} (ih : ApproxAt G n) (F : Fr) {Γ : RCtx} {σs : List STy}
    (b : Builtin) (args : RArgs E Γ σs) (τ : STy) (hb : b = .keccak256 ∨ b = .sha256 ∨ b = .ripemd160) :
    Approx (evalBuiltin G F (n + 1) b args τ) (evalBuiltin G F (n + 1 + 1) b args τ) := by
  have gn := growAt G n
  have gs := growAt G (n + 1)
  rcases hb with rfl | rfl | rfl <;> below_unfold evalBuiltin n <;> approx_go [ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, Approx.sub] [heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow, memElem_grow, readLoc_grow, lengthOf_grow, indexLoc_grow, indexNat_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow, fieldsOf_grow, ret32_grow, decodeArgs_grow, bytesOfRV_grow, encodeVals_grow, convRV_grow, convExplicitRV_grow, writeLoc_grow, deleteLoc_grow, keyStep_grow, zeroVals_grow, zeroInner_grow, copyInto_grow, getterPath_grow, extReturn_grow, gn.evalE, gn.evalPair, gn.evalArgs, gn.evalConvArgs, gn.evalLoc, gn.evalBuiltin, gn.evalArgsRev, gn.pay, gn.execS, gn.forIter, gn.execItems, gn.runMods, gn.callInternal, gn.callAddr, gn.enterInstance, gn.envLoop, gn.dispatch, gs.evalE, gs.evalPair, gs.evalArgs, gs.evalConvArgs, gs.evalLoc, gs.evalBuiltin, gs.evalArgsRev, gs.pay, gs.execS, gs.forIter, gs.execItems, gs.runMods, gs.callInternal, gs.callAddr, gs.enterInstance, gs.envLoop, gs.dispatch] [convRV_below, convExplicitRV_below, bytesOfRV_below, encodeVals_below, writeLoc_below, deleteLoc_below, keyStep_below, zeroVals_below, zeroInner_below, zeroVal_below, getterPath_below, copyInto_below, storeData_below, storeVal_below, loadMem_below, deleteStor_below] [heapPut_const, alloc_const, readCell_const, readAt_const, applyOp_const, setCell_const, writeAt_const, readLen_const, writeLen_const, heapObj_const, heapAt_const, heapBytes_const, allocRef_const, storRef_const, getV_const, zeroVal_const, zeroData_const, loadMem_const, deleteStor_const, storeData_const, storeVal_const, memSet_const, memElem_const, readLoc_const, lengthOf_const, indexLoc_const, indexNat_const, instanceAt_const, credit_const, debit_const, mark_const, rollbackTo_const, reraise_const, fieldsOf_const, ret32_const, decodeArgs_const, bytesOfRV_const, encodeVals_const, convRV_const, convExplicitRV_const, writeLoc_const, deleteLoc_const, keyStep_const, zeroVals_const, zeroInner_const, copyInto_const, getterPath_const, extReturn_const]
theorem evalBuiltin_apart_2 {G : Glob E} {n : Nat} (ih : ApproxAt G n) (F : Fr) {Γ : RCtx} {σs : List STy}
    (b : Builtin) (args : RArgs E Γ σs) (τ : STy) (hb : b = .addmod) :
    Approx (evalBuiltin G F (n + 1) b args τ) (evalBuiltin G F (n + 1 + 1) b args τ) := by
  have gn := growAt G n
  have gs := growAt G (n + 1)
  rcases hb with rfl <;> below_unfold evalBuiltin n <;> approx_go [ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, Approx.sub] [heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow, memElem_grow, readLoc_grow, lengthOf_grow, indexLoc_grow, indexNat_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow, fieldsOf_grow, ret32_grow, decodeArgs_grow, bytesOfRV_grow, encodeVals_grow, convRV_grow, convExplicitRV_grow, writeLoc_grow, deleteLoc_grow, keyStep_grow, zeroVals_grow, zeroInner_grow, copyInto_grow, getterPath_grow, extReturn_grow, gn.evalE, gn.evalPair, gn.evalArgs, gn.evalConvArgs, gn.evalLoc, gn.evalBuiltin, gn.evalArgsRev, gn.pay, gn.execS, gn.forIter, gn.execItems, gn.runMods, gn.callInternal, gn.callAddr, gn.enterInstance, gn.envLoop, gn.dispatch, gs.evalE, gs.evalPair, gs.evalArgs, gs.evalConvArgs, gs.evalLoc, gs.evalBuiltin, gs.evalArgsRev, gs.pay, gs.execS, gs.forIter, gs.execItems, gs.runMods, gs.callInternal, gs.callAddr, gs.enterInstance, gs.envLoop, gs.dispatch] [convRV_below, convExplicitRV_below, bytesOfRV_below, encodeVals_below, writeLoc_below, deleteLoc_below, keyStep_below, zeroVals_below, zeroInner_below, zeroVal_below, getterPath_below, copyInto_below, storeData_below, storeVal_below, loadMem_below, deleteStor_below] [heapPut_const, alloc_const, readCell_const, readAt_const, applyOp_const, setCell_const, writeAt_const, readLen_const, writeLen_const, heapObj_const, heapAt_const, heapBytes_const, allocRef_const, storRef_const, getV_const, zeroVal_const, zeroData_const, loadMem_const, deleteStor_const, storeData_const, storeVal_const, memSet_const, memElem_const, readLoc_const, lengthOf_const, indexLoc_const, indexNat_const, instanceAt_const, credit_const, debit_const, mark_const, rollbackTo_const, reraise_const, fieldsOf_const, ret32_const, decodeArgs_const, bytesOfRV_const, encodeVals_const, convRV_const, convExplicitRV_const, writeLoc_const, deleteLoc_const, keyStep_const, zeroVals_const, zeroInner_const, copyInto_const, getterPath_const, extReturn_const]
theorem evalBuiltin_apart_3 {G : Glob E} {n : Nat} (ih : ApproxAt G n) (F : Fr) {Γ : RCtx} {σs : List STy}
    (b : Builtin) (args : RArgs E Γ σs) (τ : STy) (hb : b = .mulmod) :
    Approx (evalBuiltin G F (n + 1) b args τ) (evalBuiltin G F (n + 1 + 1) b args τ) := by
  have gn := growAt G n
  have gs := growAt G (n + 1)
  rcases hb with rfl <;> below_unfold evalBuiltin n <;> approx_go [ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, Approx.sub] [heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow, memElem_grow, readLoc_grow, lengthOf_grow, indexLoc_grow, indexNat_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow, fieldsOf_grow, ret32_grow, decodeArgs_grow, bytesOfRV_grow, encodeVals_grow, convRV_grow, convExplicitRV_grow, writeLoc_grow, deleteLoc_grow, keyStep_grow, zeroVals_grow, zeroInner_grow, copyInto_grow, getterPath_grow, extReturn_grow, gn.evalE, gn.evalPair, gn.evalArgs, gn.evalConvArgs, gn.evalLoc, gn.evalBuiltin, gn.evalArgsRev, gn.pay, gn.execS, gn.forIter, gn.execItems, gn.runMods, gn.callInternal, gn.callAddr, gn.enterInstance, gn.envLoop, gn.dispatch, gs.evalE, gs.evalPair, gs.evalArgs, gs.evalConvArgs, gs.evalLoc, gs.evalBuiltin, gs.evalArgsRev, gs.pay, gs.execS, gs.forIter, gs.execItems, gs.runMods, gs.callInternal, gs.callAddr, gs.enterInstance, gs.envLoop, gs.dispatch] [convRV_below, convExplicitRV_below, bytesOfRV_below, encodeVals_below, writeLoc_below, deleteLoc_below, keyStep_below, zeroVals_below, zeroInner_below, zeroVal_below, getterPath_below, copyInto_below, storeData_below, storeVal_below, loadMem_below, deleteStor_below] [heapPut_const, alloc_const, readCell_const, readAt_const, applyOp_const, setCell_const, writeAt_const, readLen_const, writeLen_const, heapObj_const, heapAt_const, heapBytes_const, allocRef_const, storRef_const, getV_const, zeroVal_const, zeroData_const, loadMem_const, deleteStor_const, storeData_const, storeVal_const, memSet_const, memElem_const, readLoc_const, lengthOf_const, indexLoc_const, indexNat_const, instanceAt_const, credit_const, debit_const, mark_const, rollbackTo_const, reraise_const, fieldsOf_const, ret32_const, decodeArgs_const, bytesOfRV_const, encodeVals_const, convRV_const, convExplicitRV_const, writeLoc_const, deleteLoc_const, keyStep_const, zeroVals_const, zeroInner_const, copyInto_const, getterPath_const, extReturn_const]
theorem evalBuiltin_apart_4 {G : Glob E} {n : Nat} (ih : ApproxAt G n) (F : Fr) {Γ : RCtx} {σs : List STy}
    (b : Builtin) (args : RArgs E Γ σs) (τ : STy) (hb : b = .ecrecover) :
    Approx (evalBuiltin G F (n + 1) b args τ) (evalBuiltin G F (n + 1 + 1) b args τ) := by
  have gn := growAt G n
  have gs := growAt G (n + 1)
  rcases hb with rfl <;> below_unfold evalBuiltin n <;> approx_go [ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, Approx.sub] [heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow, memElem_grow, readLoc_grow, lengthOf_grow, indexLoc_grow, indexNat_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow, fieldsOf_grow, ret32_grow, decodeArgs_grow, bytesOfRV_grow, encodeVals_grow, convRV_grow, convExplicitRV_grow, writeLoc_grow, deleteLoc_grow, keyStep_grow, zeroVals_grow, zeroInner_grow, copyInto_grow, getterPath_grow, extReturn_grow, gn.evalE, gn.evalPair, gn.evalArgs, gn.evalConvArgs, gn.evalLoc, gn.evalBuiltin, gn.evalArgsRev, gn.pay, gn.execS, gn.forIter, gn.execItems, gn.runMods, gn.callInternal, gn.callAddr, gn.enterInstance, gn.envLoop, gn.dispatch, gs.evalE, gs.evalPair, gs.evalArgs, gs.evalConvArgs, gs.evalLoc, gs.evalBuiltin, gs.evalArgsRev, gs.pay, gs.execS, gs.forIter, gs.execItems, gs.runMods, gs.callInternal, gs.callAddr, gs.enterInstance, gs.envLoop, gs.dispatch] [convRV_below, convExplicitRV_below, bytesOfRV_below, encodeVals_below, writeLoc_below, deleteLoc_below, keyStep_below, zeroVals_below, zeroInner_below, zeroVal_below, getterPath_below, copyInto_below, storeData_below, storeVal_below, loadMem_below, deleteStor_below] [heapPut_const, alloc_const, readCell_const, readAt_const, applyOp_const, setCell_const, writeAt_const, readLen_const, writeLen_const, heapObj_const, heapAt_const, heapBytes_const, allocRef_const, storRef_const, getV_const, zeroVal_const, zeroData_const, loadMem_const, deleteStor_const, storeData_const, storeVal_const, memSet_const, memElem_const, readLoc_const, lengthOf_const, indexLoc_const, indexNat_const, instanceAt_const, credit_const, debit_const, mark_const, rollbackTo_const, reraise_const, fieldsOf_const, ret32_const, decodeArgs_const, bytesOfRV_const, encodeVals_const, convRV_const, convExplicitRV_const, writeLoc_const, deleteLoc_const, keyStep_const, zeroVals_const, zeroInner_const, copyInto_const, getterPath_const, extReturn_const]
theorem evalBuiltin_astep (ih : ApproxAt G n) (F : Fr) {Γ : RCtx} {σs : List STy} (b : Builtin)
    (args : RArgs E Γ σs) (τ : STy) :
    Approx (evalBuiltin G F (n + 1) b args τ) (evalBuiltin G F (n + 1 + 1) b args τ) := by
  have gn := growAt G n
  have gs := growAt G (n + 1)
  cases b
  all_goals first
    | exact evalBuiltin_apart_0 ih F _ args τ (by decide)
    | exact evalBuiltin_apart_1 ih F _ args τ (by decide)
    | exact evalBuiltin_apart_2 ih F _ args τ (by decide)
    | exact evalBuiltin_apart_3 ih F _ args τ (by decide)
    | exact evalBuiltin_apart_4 ih F _ args τ (by decide)
    | (below_unfold evalBuiltin n; approx_go [ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, Approx.sub] [heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow, memElem_grow, readLoc_grow, lengthOf_grow, indexLoc_grow, indexNat_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow, fieldsOf_grow, ret32_grow, decodeArgs_grow, bytesOfRV_grow, encodeVals_grow, convRV_grow, convExplicitRV_grow, writeLoc_grow, deleteLoc_grow, keyStep_grow, zeroVals_grow, zeroInner_grow, copyInto_grow, getterPath_grow, extReturn_grow, gn.evalE, gn.evalPair, gn.evalArgs, gn.evalConvArgs, gn.evalLoc, gn.evalBuiltin, gn.evalArgsRev, gn.pay, gn.execS, gn.forIter, gn.execItems, gn.runMods, gn.callInternal, gn.callAddr, gn.enterInstance, gn.envLoop, gn.dispatch, gs.evalE, gs.evalPair, gs.evalArgs, gs.evalConvArgs, gs.evalLoc, gs.evalBuiltin, gs.evalArgsRev, gs.pay, gs.execS, gs.forIter, gs.execItems, gs.runMods, gs.callInternal, gs.callAddr, gs.enterInstance, gs.envLoop, gs.dispatch] [convRV_below, convExplicitRV_below, bytesOfRV_below, encodeVals_below, writeLoc_below, deleteLoc_below, keyStep_below, zeroVals_below, zeroInner_below, zeroVal_below, getterPath_below, copyInto_below, storeData_below, storeVal_below, loadMem_below, deleteStor_below] [heapPut_const, alloc_const, readCell_const, readAt_const, applyOp_const, setCell_const, writeAt_const, readLen_const, writeLen_const, heapObj_const, heapAt_const, heapBytes_const, allocRef_const, storRef_const, getV_const, zeroVal_const, zeroData_const, loadMem_const, deleteStor_const, storeData_const, storeVal_const, memSet_const, memElem_const, readLoc_const, lengthOf_const, indexLoc_const, indexNat_const, instanceAt_const, credit_const, debit_const, mark_const, rollbackTo_const, reraise_const, fieldsOf_const, ret32_const, decodeArgs_const, bytesOfRV_const, encodeVals_const, convRV_const, convExplicitRV_const, writeLoc_const, deleteLoc_const, keyStep_const, zeroVals_const, zeroInner_const, copyInto_const, getterPath_const, extReturn_const])
theorem evalArgsRev_astep (ih : ApproxAt G n) (F : Fr) {Γ : RCtx} {τs : List STy} (es : RArgs E Γ τs) :
    Approx (evalArgsRev G F (n + 1) es) (evalArgsRev G F (n + 1 + 1) es) := by
  have gn := growAt G n
  have gs := growAt G (n + 1)
  cases es <;> below_unfold evalArgsRev n <;> approx_go [ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, Approx.sub] [heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow, memElem_grow, readLoc_grow, lengthOf_grow, indexLoc_grow, indexNat_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow, fieldsOf_grow, ret32_grow, decodeArgs_grow, bytesOfRV_grow, encodeVals_grow, convRV_grow, convExplicitRV_grow, writeLoc_grow, deleteLoc_grow, keyStep_grow, zeroVals_grow, zeroInner_grow, copyInto_grow, getterPath_grow, extReturn_grow, gn.evalE, gn.evalPair, gn.evalArgs, gn.evalConvArgs, gn.evalLoc, gn.evalBuiltin, gn.evalArgsRev, gn.pay, gn.execS, gn.forIter, gn.execItems, gn.runMods, gn.callInternal, gn.callAddr, gn.enterInstance, gn.envLoop, gn.dispatch, gs.evalE, gs.evalPair, gs.evalArgs, gs.evalConvArgs, gs.evalLoc, gs.evalBuiltin, gs.evalArgsRev, gs.pay, gs.execS, gs.forIter, gs.execItems, gs.runMods, gs.callInternal, gs.callAddr, gs.enterInstance, gs.envLoop, gs.dispatch] [convRV_below, convExplicitRV_below, bytesOfRV_below, encodeVals_below, writeLoc_below, deleteLoc_below, keyStep_below, zeroVals_below, zeroInner_below, zeroVal_below, getterPath_below, copyInto_below, storeData_below, storeVal_below, loadMem_below, deleteStor_below] [heapPut_const, alloc_const, readCell_const, readAt_const, applyOp_const, setCell_const, writeAt_const, readLen_const, writeLen_const, heapObj_const, heapAt_const, heapBytes_const, allocRef_const, storRef_const, getV_const, zeroVal_const, zeroData_const, loadMem_const, deleteStor_const, storeData_const, storeVal_const, memSet_const, memElem_const, readLoc_const, lengthOf_const, indexLoc_const, indexNat_const, instanceAt_const, credit_const, debit_const, mark_const, rollbackTo_const, reraise_const, fieldsOf_const, ret32_const, decodeArgs_const, bytesOfRV_const, encodeVals_const, convRV_const, convExplicitRV_const, writeLoc_const, deleteLoc_const, keyStep_const, zeroVals_const, zeroInner_const, copyInto_const, getterPath_const, extReturn_const]
theorem pay_astep (ih : ApproxAt G n) (F : Fr) {Γ : RCtx} (a : RExpr E Γ (.address true))
    (v : RExpr E Γ (.int IntTy.u256)) : Approx (pay G F (n + 1) a v) (pay G F (n + 1 + 1) a v) := by
  have gn := growAt G n
  have gs := growAt G (n + 1)
  below_unfold pay n
  approx_go [ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, Approx.sub] [heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow, memElem_grow, readLoc_grow, lengthOf_grow, indexLoc_grow, indexNat_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow, fieldsOf_grow, ret32_grow, decodeArgs_grow, bytesOfRV_grow, encodeVals_grow, convRV_grow, convExplicitRV_grow, writeLoc_grow, deleteLoc_grow, keyStep_grow, zeroVals_grow, zeroInner_grow, copyInto_grow, getterPath_grow, extReturn_grow, gn.evalE, gn.evalPair, gn.evalArgs, gn.evalConvArgs, gn.evalLoc, gn.evalBuiltin, gn.evalArgsRev, gn.pay, gn.execS, gn.forIter, gn.execItems, gn.runMods, gn.callInternal, gn.callAddr, gn.enterInstance, gn.envLoop, gn.dispatch, gs.evalE, gs.evalPair, gs.evalArgs, gs.evalConvArgs, gs.evalLoc, gs.evalBuiltin, gs.evalArgsRev, gs.pay, gs.execS, gs.forIter, gs.execItems, gs.runMods, gs.callInternal, gs.callAddr, gs.enterInstance, gs.envLoop, gs.dispatch] [convRV_below, convExplicitRV_below, bytesOfRV_below, encodeVals_below, writeLoc_below, deleteLoc_below, keyStep_below, zeroVals_below, zeroInner_below, zeroVal_below, getterPath_below, copyInto_below, storeData_below, storeVal_below, loadMem_below, deleteStor_below] [heapPut_const, alloc_const, readCell_const, readAt_const, applyOp_const, setCell_const, writeAt_const, readLen_const, writeLen_const, heapObj_const, heapAt_const, heapBytes_const, allocRef_const, storRef_const, getV_const, zeroVal_const, zeroData_const, loadMem_const, deleteStor_const, storeData_const, storeVal_const, memSet_const, memElem_const, readLoc_const, lengthOf_const, indexLoc_const, indexNat_const, instanceAt_const, credit_const, debit_const, mark_const, rollbackTo_const, reraise_const, fieldsOf_const, ret32_const, decodeArgs_const, bytesOfRV_const, encodeVals_const, convRV_const, convExplicitRV_const, writeLoc_const, deleteLoc_const, keyStep_const, zeroVals_const, zeroInner_const, copyInto_const, getterPath_const, extReturn_const]
theorem execS_apart_0 {G : Glob E} {n : Nat} (ih : ApproxAt G n) (F : Fr) (nps : Nat) (ph : Option (Ph E)) {R : List STy} {M : Bool}
    {k : SCtx} {Γ Γ' : RCtx} (s : RStmt E R M k Γ Γ') (l : Locals E.layout Γ)
    (h : 0 ≤ s.ctorIdx ∧ s.ctorIdx < 8) :
    Approx (execS G F (n + 1) nps ph s l) (execS G F (n + 1 + 1) nps ph s l) := by
  have gn := growAt G n
  have gs := growAt G (n + 1)
  cases s <;> first | (exfalso; simp only [RStmt.ctorIdx] at h; omega) | (below_unfold execS n; approx_go [ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, Approx.sub] [heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow, memElem_grow, readLoc_grow, lengthOf_grow, indexLoc_grow, indexNat_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow, fieldsOf_grow, ret32_grow, decodeArgs_grow, bytesOfRV_grow, encodeVals_grow, convRV_grow, convExplicitRV_grow, writeLoc_grow, deleteLoc_grow, keyStep_grow, zeroVals_grow, zeroInner_grow, copyInto_grow, getterPath_grow, extReturn_grow, gn.evalE, gn.evalPair, gn.evalArgs, gn.evalConvArgs, gn.evalLoc, gn.evalBuiltin, gn.evalArgsRev, gn.pay, gn.execS, gn.forIter, gn.execItems, gn.runMods, gn.callInternal, gn.callAddr, gn.enterInstance, gn.envLoop, gn.dispatch, gs.evalE, gs.evalPair, gs.evalArgs, gs.evalConvArgs, gs.evalLoc, gs.evalBuiltin, gs.evalArgsRev, gs.pay, gs.execS, gs.forIter, gs.execItems, gs.runMods, gs.callInternal, gs.callAddr, gs.enterInstance, gs.envLoop, gs.dispatch] [convRV_below, convExplicitRV_below, bytesOfRV_below, encodeVals_below, writeLoc_below, deleteLoc_below, keyStep_below, zeroVals_below, zeroInner_below, zeroVal_below, getterPath_below, copyInto_below, storeData_below, storeVal_below, loadMem_below, deleteStor_below] [heapPut_const, alloc_const, readCell_const, readAt_const, applyOp_const, setCell_const, writeAt_const, readLen_const, writeLen_const, heapObj_const, heapAt_const, heapBytes_const, allocRef_const, storRef_const, getV_const, zeroVal_const, zeroData_const, loadMem_const, deleteStor_const, storeData_const, storeVal_const, memSet_const, memElem_const, readLoc_const, lengthOf_const, indexLoc_const, indexNat_const, instanceAt_const, credit_const, debit_const, mark_const, rollbackTo_const, reraise_const, fieldsOf_const, ret32_const, decodeArgs_const, bytesOfRV_const, encodeVals_const, convRV_const, convExplicitRV_const, writeLoc_const, deleteLoc_const, keyStep_const, zeroVals_const, zeroInner_const, copyInto_const, getterPath_const, extReturn_const])
theorem execS_apart_1 {G : Glob E} {n : Nat} (ih : ApproxAt G n) (F : Fr) (nps : Nat) (ph : Option (Ph E)) {R : List STy} {M : Bool}
    {k : SCtx} {Γ Γ' : RCtx} (s : RStmt E R M k Γ Γ') (l : Locals E.layout Γ)
    (h : 8 ≤ s.ctorIdx ∧ s.ctorIdx < 16) :
    Approx (execS G F (n + 1) nps ph s l) (execS G F (n + 1 + 1) nps ph s l) := by
  have gn := growAt G n
  have gs := growAt G (n + 1)
  cases s <;> first | (exfalso; simp only [RStmt.ctorIdx] at h; omega) | (below_unfold execS n; approx_go [ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, Approx.sub] [heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow, memElem_grow, readLoc_grow, lengthOf_grow, indexLoc_grow, indexNat_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow, fieldsOf_grow, ret32_grow, decodeArgs_grow, bytesOfRV_grow, encodeVals_grow, convRV_grow, convExplicitRV_grow, writeLoc_grow, deleteLoc_grow, keyStep_grow, zeroVals_grow, zeroInner_grow, copyInto_grow, getterPath_grow, extReturn_grow, gn.evalE, gn.evalPair, gn.evalArgs, gn.evalConvArgs, gn.evalLoc, gn.evalBuiltin, gn.evalArgsRev, gn.pay, gn.execS, gn.forIter, gn.execItems, gn.runMods, gn.callInternal, gn.callAddr, gn.enterInstance, gn.envLoop, gn.dispatch, gs.evalE, gs.evalPair, gs.evalArgs, gs.evalConvArgs, gs.evalLoc, gs.evalBuiltin, gs.evalArgsRev, gs.pay, gs.execS, gs.forIter, gs.execItems, gs.runMods, gs.callInternal, gs.callAddr, gs.enterInstance, gs.envLoop, gs.dispatch] [convRV_below, convExplicitRV_below, bytesOfRV_below, encodeVals_below, writeLoc_below, deleteLoc_below, keyStep_below, zeroVals_below, zeroInner_below, zeroVal_below, getterPath_below, copyInto_below, storeData_below, storeVal_below, loadMem_below, deleteStor_below] [heapPut_const, alloc_const, readCell_const, readAt_const, applyOp_const, setCell_const, writeAt_const, readLen_const, writeLen_const, heapObj_const, heapAt_const, heapBytes_const, allocRef_const, storRef_const, getV_const, zeroVal_const, zeroData_const, loadMem_const, deleteStor_const, storeData_const, storeVal_const, memSet_const, memElem_const, readLoc_const, lengthOf_const, indexLoc_const, indexNat_const, instanceAt_const, credit_const, debit_const, mark_const, rollbackTo_const, reraise_const, fieldsOf_const, ret32_const, decodeArgs_const, bytesOfRV_const, encodeVals_const, convRV_const, convExplicitRV_const, writeLoc_const, deleteLoc_const, keyStep_const, zeroVals_const, zeroInner_const, copyInto_const, getterPath_const, extReturn_const])
theorem execS_apart_2 {G : Glob E} {n : Nat} (ih : ApproxAt G n) (F : Fr) (nps : Nat) (ph : Option (Ph E)) {R : List STy} {M : Bool}
    {k : SCtx} {Γ Γ' : RCtx} (s : RStmt E R M k Γ Γ') (l : Locals E.layout Γ)
    (h : 16 ≤ s.ctorIdx ∧ s.ctorIdx < 40) :
    Approx (execS G F (n + 1) nps ph s l) (execS G F (n + 1 + 1) nps ph s l) := by
  have gn := growAt G n
  have gs := growAt G (n + 1)
  cases s <;> first | (exfalso; simp only [RStmt.ctorIdx] at h; omega) | (below_unfold execS n; approx_go [ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, Approx.sub] [heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow, memElem_grow, readLoc_grow, lengthOf_grow, indexLoc_grow, indexNat_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow, fieldsOf_grow, ret32_grow, decodeArgs_grow, bytesOfRV_grow, encodeVals_grow, convRV_grow, convExplicitRV_grow, writeLoc_grow, deleteLoc_grow, keyStep_grow, zeroVals_grow, zeroInner_grow, copyInto_grow, getterPath_grow, extReturn_grow, gn.evalE, gn.evalPair, gn.evalArgs, gn.evalConvArgs, gn.evalLoc, gn.evalBuiltin, gn.evalArgsRev, gn.pay, gn.execS, gn.forIter, gn.execItems, gn.runMods, gn.callInternal, gn.callAddr, gn.enterInstance, gn.envLoop, gn.dispatch, gs.evalE, gs.evalPair, gs.evalArgs, gs.evalConvArgs, gs.evalLoc, gs.evalBuiltin, gs.evalArgsRev, gs.pay, gs.execS, gs.forIter, gs.execItems, gs.runMods, gs.callInternal, gs.callAddr, gs.enterInstance, gs.envLoop, gs.dispatch] [convRV_below, convExplicitRV_below, bytesOfRV_below, encodeVals_below, writeLoc_below, deleteLoc_below, keyStep_below, zeroVals_below, zeroInner_below, zeroVal_below, getterPath_below, copyInto_below, storeData_below, storeVal_below, loadMem_below, deleteStor_below] [heapPut_const, alloc_const, readCell_const, readAt_const, applyOp_const, setCell_const, writeAt_const, readLen_const, writeLen_const, heapObj_const, heapAt_const, heapBytes_const, allocRef_const, storRef_const, getV_const, zeroVal_const, zeroData_const, loadMem_const, deleteStor_const, storeData_const, storeVal_const, memSet_const, memElem_const, readLoc_const, lengthOf_const, indexLoc_const, indexNat_const, instanceAt_const, credit_const, debit_const, mark_const, rollbackTo_const, reraise_const, fieldsOf_const, ret32_const, decodeArgs_const, bytesOfRV_const, encodeVals_const, convRV_const, convExplicitRV_const, writeLoc_const, deleteLoc_const, keyStep_const, zeroVals_const, zeroInner_const, copyInto_const, getterPath_const, extReturn_const])
theorem execS_astep (ih : ApproxAt G n) (F : Fr) (nps : Nat) (ph : Option (Ph E)) {R : List STy} {M : Bool}
    {k : SCtx} {Γ Γ' : RCtx} (s : RStmt E R M k Γ Γ') (l : Locals E.layout Γ) :
    Approx (execS G F (n + 1) nps ph s l) (execS G F (n + 1 + 1) nps ph s l) := by
  by_cases h0 : s.ctorIdx < 8
  · exact execS_apart_0 ih F nps ph s l ⟨Nat.zero_le _, h0⟩
  by_cases h1 : s.ctorIdx < 16
  · exact execS_apart_1 ih F nps ph s l ⟨by omega, h1⟩
  have h2 : s.ctorIdx < 40 := by cases s <;> simp only [RStmt.ctorIdx] <;> omega
  exact execS_apart_2 ih F nps ph s l ⟨by omega, h2⟩
theorem forIter_astep (ih : ApproxAt G n) (F : Fr) (nps : Nat) (ph : Option (Ph E)) {R : List STy} {M u : Bool}
    {Γ₁ Γ₂ : RCtx} (c : ROptBool E Γ₁) (post : ROptExpr E Γ₁) (body : RStmt E R M ⟨true, u⟩ Γ₁ Γ₂)
    (l : Locals E.layout Γ₁) :
    Approx (forIter G F (n + 1) nps ph c post body l) (forIter G F (n + 1 + 1) nps ph c post body l) := by
  have gn := growAt G n
  have gs := growAt G (n + 1)
  cases c <;> below_unfold forIter n <;> approx_go [ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, Approx.sub] [heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow, memElem_grow, readLoc_grow, lengthOf_grow, indexLoc_grow, indexNat_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow, fieldsOf_grow, ret32_grow, decodeArgs_grow, bytesOfRV_grow, encodeVals_grow, convRV_grow, convExplicitRV_grow, writeLoc_grow, deleteLoc_grow, keyStep_grow, zeroVals_grow, zeroInner_grow, copyInto_grow, getterPath_grow, extReturn_grow, gn.evalE, gn.evalPair, gn.evalArgs, gn.evalConvArgs, gn.evalLoc, gn.evalBuiltin, gn.evalArgsRev, gn.pay, gn.execS, gn.forIter, gn.execItems, gn.runMods, gn.callInternal, gn.callAddr, gn.enterInstance, gn.envLoop, gn.dispatch, gs.evalE, gs.evalPair, gs.evalArgs, gs.evalConvArgs, gs.evalLoc, gs.evalBuiltin, gs.evalArgsRev, gs.pay, gs.execS, gs.forIter, gs.execItems, gs.runMods, gs.callInternal, gs.callAddr, gs.enterInstance, gs.envLoop, gs.dispatch] [convRV_below, convExplicitRV_below, bytesOfRV_below, encodeVals_below, writeLoc_below, deleteLoc_below, keyStep_below, zeroVals_below, zeroInner_below, zeroVal_below, getterPath_below, copyInto_below, storeData_below, storeVal_below, loadMem_below, deleteStor_below] [heapPut_const, alloc_const, readCell_const, readAt_const, applyOp_const, setCell_const, writeAt_const, readLen_const, writeLen_const, heapObj_const, heapAt_const, heapBytes_const, allocRef_const, storRef_const, getV_const, zeroVal_const, zeroData_const, loadMem_const, deleteStor_const, storeData_const, storeVal_const, memSet_const, memElem_const, readLoc_const, lengthOf_const, indexLoc_const, indexNat_const, instanceAt_const, credit_const, debit_const, mark_const, rollbackTo_const, reraise_const, fieldsOf_const, ret32_const, decodeArgs_const, bytesOfRV_const, encodeVals_const, convRV_const, convExplicitRV_const, writeLoc_const, deleteLoc_const, keyStep_const, zeroVals_const, zeroInner_const, copyInto_const, getterPath_const, extReturn_const]
theorem execItems_astep (ih : ApproxAt G n) (F : Fr) (nps : Nat) (ph : Option (Ph E)) {R : List STy} {M : Bool}
    {k : SCtx} {Γ Γ' : RCtx} (b : RItems E R M k Γ Γ') (l : Locals E.layout Γ) :
    Approx (execItems G F (n + 1) nps ph b l) (execItems G F (n + 1 + 1) nps ph b l) := by
  have gn := growAt G n
  have gs := growAt G (n + 1)
  cases b <;> below_unfold execItems n <;> approx_go [ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, Approx.sub] [heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow, memElem_grow, readLoc_grow, lengthOf_grow, indexLoc_grow, indexNat_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow, fieldsOf_grow, ret32_grow, decodeArgs_grow, bytesOfRV_grow, encodeVals_grow, convRV_grow, convExplicitRV_grow, writeLoc_grow, deleteLoc_grow, keyStep_grow, zeroVals_grow, zeroInner_grow, copyInto_grow, getterPath_grow, extReturn_grow, gn.evalE, gn.evalPair, gn.evalArgs, gn.evalConvArgs, gn.evalLoc, gn.evalBuiltin, gn.evalArgsRev, gn.pay, gn.execS, gn.forIter, gn.execItems, gn.runMods, gn.callInternal, gn.callAddr, gn.enterInstance, gn.envLoop, gn.dispatch, gs.evalE, gs.evalPair, gs.evalArgs, gs.evalConvArgs, gs.evalLoc, gs.evalBuiltin, gs.evalArgsRev, gs.pay, gs.execS, gs.forIter, gs.execItems, gs.runMods, gs.callInternal, gs.callAddr, gs.enterInstance, gs.envLoop, gs.dispatch] [convRV_below, convExplicitRV_below, bytesOfRV_below, encodeVals_below, writeLoc_below, deleteLoc_below, keyStep_below, zeroVals_below, zeroInner_below, zeroVal_below, getterPath_below, copyInto_below, storeData_below, storeVal_below, loadMem_below, deleteStor_below] [heapPut_const, alloc_const, readCell_const, readAt_const, applyOp_const, setCell_const, writeAt_const, readLen_const, writeLen_const, heapObj_const, heapAt_const, heapBytes_const, allocRef_const, storRef_const, getV_const, zeroVal_const, zeroData_const, loadMem_const, deleteStor_const, storeData_const, storeVal_const, memSet_const, memElem_const, readLoc_const, lengthOf_const, indexLoc_const, indexNat_const, instanceAt_const, credit_const, debit_const, mark_const, rollbackTo_const, reraise_const, fieldsOf_const, ret32_const, decodeArgs_const, bytesOfRV_const, encodeVals_const, convRV_const, convExplicitRV_const, writeLoc_const, deleteLoc_const, keyStep_const, zeroVals_const, zeroInner_const, copyInto_const, getterPath_const, extReturn_const]
theorem runMods_astep (ih : ApproxAt G n) (F : Fr) (b : RBody E) (mods : List (RModInv E b.locals))
    (l : Locals E.layout b.locals) : Approx (runMods G F (n + 1) b mods l) (runMods G F (n + 1 + 1) b mods l) := by
  have gn := growAt G n
  have gs := growAt G (n + 1)
  cases mods with
  | nil => below_unfold runMods n; approx_go [ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, Approx.sub] [heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow, memElem_grow, readLoc_grow, lengthOf_grow, indexLoc_grow, indexNat_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow, fieldsOf_grow, ret32_grow, decodeArgs_grow, bytesOfRV_grow, encodeVals_grow, convRV_grow, convExplicitRV_grow, writeLoc_grow, deleteLoc_grow, keyStep_grow, zeroVals_grow, zeroInner_grow, copyInto_grow, getterPath_grow, extReturn_grow, gn.evalE, gn.evalPair, gn.evalArgs, gn.evalConvArgs, gn.evalLoc, gn.evalBuiltin, gn.evalArgsRev, gn.pay, gn.execS, gn.forIter, gn.execItems, gn.runMods, gn.callInternal, gn.callAddr, gn.enterInstance, gn.envLoop, gn.dispatch, gs.evalE, gs.evalPair, gs.evalArgs, gs.evalConvArgs, gs.evalLoc, gs.evalBuiltin, gs.evalArgsRev, gs.pay, gs.execS, gs.forIter, gs.execItems, gs.runMods, gs.callInternal, gs.callAddr, gs.enterInstance, gs.envLoop, gs.dispatch] [convRV_below, convExplicitRV_below, bytesOfRV_below, encodeVals_below, writeLoc_below, deleteLoc_below, keyStep_below, zeroVals_below, zeroInner_below, zeroVal_below, getterPath_below, copyInto_below, storeData_below, storeVal_below, loadMem_below, deleteStor_below] [heapPut_const, alloc_const, readCell_const, readAt_const, applyOp_const, setCell_const, writeAt_const, readLen_const, writeLen_const, heapObj_const, heapAt_const, heapBytes_const, allocRef_const, storRef_const, getV_const, zeroVal_const, zeroData_const, loadMem_const, deleteStor_const, storeData_const, storeVal_const, memSet_const, memElem_const, readLoc_const, lengthOf_const, indexLoc_const, indexNat_const, instanceAt_const, credit_const, debit_const, mark_const, rollbackTo_const, reraise_const, fieldsOf_const, ret32_const, decodeArgs_const, bytesOfRV_const, encodeVals_const, convRV_const, convExplicitRV_const, writeLoc_const, deleteLoc_const, keyStep_const, zeroVals_const, zeroInner_const, copyInto_const, getterPath_const, extReturn_const]
  | cons md rest =>
    below_unfold runMods n
    refine Approx.bind (Approx.sub _ (ih.evalConvArgs _ _)) fun p => ?_
    split
    · exact Approx.refl (by grow_go [heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow, memElem_grow, readLoc_grow, lengthOf_grow, indexLoc_grow, indexNat_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow, fieldsOf_grow, ret32_grow, decodeArgs_grow, bytesOfRV_grow, encodeVals_grow, convRV_grow, convExplicitRV_grow, writeLoc_grow, deleteLoc_grow, keyStep_grow, zeroVals_grow, zeroInner_grow, copyInto_grow, getterPath_grow, extReturn_grow, gn.evalE, gn.evalPair, gn.evalArgs, gn.evalConvArgs, gn.evalLoc, gn.evalBuiltin, gn.evalArgsRev, gn.pay, gn.execS, gn.forIter, gn.execItems, gn.runMods, gn.callInternal, gn.callAddr, gn.enterInstance, gn.envLoop, gn.dispatch, gs.evalE, gs.evalPair, gs.evalArgs, gs.evalConvArgs, gs.evalLoc, gs.evalBuiltin, gs.evalArgsRev, gs.pay, gs.execS, gs.forIter, gs.execItems, gs.runMods, gs.callInternal, gs.callAddr, gs.enterInstance, gs.envLoop, gs.dispatch])
    · split
      · refine Approx.bind (Approx.refl (by grow_go [heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow, memElem_grow, readLoc_grow, lengthOf_grow, indexLoc_grow, indexNat_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow, fieldsOf_grow, ret32_grow, decodeArgs_grow, bytesOfRV_grow, encodeVals_grow, convRV_grow, convExplicitRV_grow, writeLoc_grow, deleteLoc_grow, keyStep_grow, zeroVals_grow, zeroInner_grow, copyInto_grow, getterPath_grow, extReturn_grow, gn.evalE, gn.evalPair, gn.evalArgs, gn.evalConvArgs, gn.evalLoc, gn.evalBuiltin, gn.evalArgsRev, gn.pay, gn.execS, gn.forIter, gn.execItems, gn.runMods, gn.callInternal, gn.callAddr, gn.enterInstance, gn.envLoop, gn.dispatch, gs.evalE, gs.evalPair, gs.evalArgs, gs.evalConvArgs, gs.evalLoc, gs.evalBuiltin, gs.evalArgsRev, gs.pay, gs.execS, gs.forIter, gs.execItems, gs.runMods, gs.callInternal, gs.callAddr, gs.enterInstance, gs.envLoop, gs.dispatch])) fun s => ?_
        refine Approx.bind (Approx.refl (by grow_go [heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow, memElem_grow, readLoc_grow, lengthOf_grow, indexLoc_grow, indexNat_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow, fieldsOf_grow, ret32_grow, decodeArgs_grow, bytesOfRV_grow, encodeVals_grow, convRV_grow, convExplicitRV_grow, writeLoc_grow, deleteLoc_grow, keyStep_grow, zeroVals_grow, zeroInner_grow, copyInto_grow, getterPath_grow, extReturn_grow, gn.evalE, gn.evalPair, gn.evalArgs, gn.evalConvArgs, gn.evalLoc, gn.evalBuiltin, gn.evalArgsRev, gn.pay, gn.execS, gn.forIter, gn.execItems, gn.runMods, gn.callInternal, gn.callAddr, gn.enterInstance, gn.envLoop, gn.dispatch, gs.evalE, gs.evalPair, gs.evalArgs, gs.evalConvArgs, gs.evalLoc, gs.evalBuiltin, gs.evalArgsRev, gs.pay, gs.execS, gs.forIter, gs.execItems, gs.runMods, gs.callInternal, gs.callAddr, gs.enterInstance, gs.envLoop, gs.dispatch])) fun _ => ?_
        refine Approx.attempt_bind (ih.execItems _ _ _ _ _) (fun r => ?_) (fun x => ?_)
        · approx_go [ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, Approx.sub] [heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow, memElem_grow, readLoc_grow, lengthOf_grow, indexLoc_grow, indexNat_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow, fieldsOf_grow, ret32_grow, decodeArgs_grow, bytesOfRV_grow, encodeVals_grow, convRV_grow, convExplicitRV_grow, writeLoc_grow, deleteLoc_grow, keyStep_grow, zeroVals_grow, zeroInner_grow, copyInto_grow, getterPath_grow, extReturn_grow, gn.evalE, gn.evalPair, gn.evalArgs, gn.evalConvArgs, gn.evalLoc, gn.evalBuiltin, gn.evalArgsRev, gn.pay, gn.execS, gn.forIter, gn.execItems, gn.runMods, gn.callInternal, gn.callAddr, gn.enterInstance, gn.envLoop, gn.dispatch, gs.evalE, gs.evalPair, gs.evalArgs, gs.evalConvArgs, gs.evalLoc, gs.evalBuiltin, gs.evalArgsRev, gs.pay, gs.execS, gs.forIter, gs.execItems, gs.runMods, gs.callInternal, gs.callAddr, gs.enterInstance, gs.envLoop, gs.dispatch] [convRV_below, convExplicitRV_below, bytesOfRV_below, encodeVals_below, writeLoc_below, deleteLoc_below, keyStep_below, zeroVals_below, zeroInner_below, zeroVal_below, getterPath_below, copyInto_below, storeData_below, storeVal_below, loadMem_below, deleteStor_below] [heapPut_const, alloc_const, readCell_const, readAt_const, applyOp_const, setCell_const, writeAt_const, readLen_const, writeLen_const, heapObj_const, heapAt_const, heapBytes_const, allocRef_const, storRef_const, getV_const, zeroVal_const, zeroData_const, loadMem_const, deleteStor_const, storeData_const, storeVal_const, memSet_const, memElem_const, readLoc_const, lengthOf_const, indexLoc_const, indexNat_const, instanceAt_const, credit_const, debit_const, mark_const, rollbackTo_const, reraise_const, fieldsOf_const, ret32_const, decodeArgs_const, bytesOfRV_const, encodeVals_const, convRV_const, convExplicitRV_const, writeLoc_const, deleteLoc_const, keyStep_const, zeroVals_const, zeroInner_const, copyInto_const, getterPath_const, extReturn_const]
        · exact ⟨rfl, rfl⟩
      · exact Approx.refl (by grow_go [heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow, memElem_grow, readLoc_grow, lengthOf_grow, indexLoc_grow, indexNat_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow, fieldsOf_grow, ret32_grow, decodeArgs_grow, bytesOfRV_grow, encodeVals_grow, convRV_grow, convExplicitRV_grow, writeLoc_grow, deleteLoc_grow, keyStep_grow, zeroVals_grow, zeroInner_grow, copyInto_grow, getterPath_grow, extReturn_grow, gn.evalE, gn.evalPair, gn.evalArgs, gn.evalConvArgs, gn.evalLoc, gn.evalBuiltin, gn.evalArgsRev, gn.pay, gn.execS, gn.forIter, gn.execItems, gn.runMods, gn.callInternal, gn.callAddr, gn.enterInstance, gn.envLoop, gn.dispatch, gs.evalE, gs.evalPair, gs.evalArgs, gs.evalConvArgs, gs.evalLoc, gs.evalBuiltin, gs.evalArgsRev, gs.pay, gs.execS, gs.forIter, gs.execItems, gs.runMods, gs.callInternal, gs.callAddr, gs.enterInstance, gs.envLoop, gs.dispatch])
theorem callInternal_astep (ih : ApproxAt G n) (F : Fr) (d : Decl) {ps : List STy} (vs : Vals E.layout ps)
    (rs : List STy) : Approx (callInternal G F (n + 1) d vs rs) (callInternal G F (n + 1 + 1) d vs rs) := by
  have gn := growAt G n
  have gs := growAt G (n + 1)
  below_unfold callInternal n
  approx_go [ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, Approx.sub] [heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow, memElem_grow, readLoc_grow, lengthOf_grow, indexLoc_grow, indexNat_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow, fieldsOf_grow, ret32_grow, decodeArgs_grow, bytesOfRV_grow, encodeVals_grow, convRV_grow, convExplicitRV_grow, writeLoc_grow, deleteLoc_grow, keyStep_grow, zeroVals_grow, zeroInner_grow, copyInto_grow, getterPath_grow, extReturn_grow, gn.evalE, gn.evalPair, gn.evalArgs, gn.evalConvArgs, gn.evalLoc, gn.evalBuiltin, gn.evalArgsRev, gn.pay, gn.execS, gn.forIter, gn.execItems, gn.runMods, gn.callInternal, gn.callAddr, gn.enterInstance, gn.envLoop, gn.dispatch, gs.evalE, gs.evalPair, gs.evalArgs, gs.evalConvArgs, gs.evalLoc, gs.evalBuiltin, gs.evalArgsRev, gs.pay, gs.execS, gs.forIter, gs.execItems, gs.runMods, gs.callInternal, gs.callAddr, gs.enterInstance, gs.envLoop, gs.dispatch] [convRV_below, convExplicitRV_below, bytesOfRV_below, encodeVals_below, writeLoc_below, deleteLoc_below, keyStep_below, zeroVals_below, zeroInner_below, zeroVal_below, getterPath_below, copyInto_below, storeData_below, storeVal_below, loadMem_below, deleteStor_below] [heapPut_const, alloc_const, readCell_const, readAt_const, applyOp_const, setCell_const, writeAt_const, readLen_const, writeLen_const, heapObj_const, heapAt_const, heapBytes_const, allocRef_const, storRef_const, getV_const, zeroVal_const, zeroData_const, loadMem_const, deleteStor_const, storeData_const, storeVal_const, memSet_const, memElem_const, readLoc_const, lengthOf_const, indexLoc_const, indexNat_const, instanceAt_const, credit_const, debit_const, mark_const, rollbackTo_const, reraise_const, fieldsOf_const, ret32_const, decodeArgs_const, bytesOfRV_const, encodeVals_const, convRV_const, convExplicitRV_const, writeLoc_const, deleteLoc_const, keyStep_const, zeroVals_const, zeroInner_const, copyInto_const, getterPath_const, extReturn_const]
theorem callAddr_astep (ih : ApproxAt G n) (F : Fr) (a : Solidity.Roadmap.Address) (v : Solidity.Roadmap.Word)
    (input : Solidity.Roadmap.Bytes) (static : Bool) :
    Approx (callAddr G F (n + 1) a v input static) (callAddr G F (n + 1 + 1) a v input static) := by
  have gn := growAt G n
  have gs := growAt G (n + 1)
  below_unfold callAddr n
  approx_go [ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, Approx.sub] [heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow, memElem_grow, readLoc_grow, lengthOf_grow, indexLoc_grow, indexNat_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow, fieldsOf_grow, ret32_grow, decodeArgs_grow, bytesOfRV_grow, encodeVals_grow, convRV_grow, convExplicitRV_grow, writeLoc_grow, deleteLoc_grow, keyStep_grow, zeroVals_grow, zeroInner_grow, copyInto_grow, getterPath_grow, extReturn_grow, gn.evalE, gn.evalPair, gn.evalArgs, gn.evalConvArgs, gn.evalLoc, gn.evalBuiltin, gn.evalArgsRev, gn.pay, gn.execS, gn.forIter, gn.execItems, gn.runMods, gn.callInternal, gn.callAddr, gn.enterInstance, gn.envLoop, gn.dispatch, gs.evalE, gs.evalPair, gs.evalArgs, gs.evalConvArgs, gs.evalLoc, gs.evalBuiltin, gs.evalArgsRev, gs.pay, gs.execS, gs.forIter, gs.execItems, gs.runMods, gs.callInternal, gs.callAddr, gs.enterInstance, gs.envLoop, gs.dispatch] [convRV_below, convExplicitRV_below, bytesOfRV_below, encodeVals_below, writeLoc_below, deleteLoc_below, keyStep_below, zeroVals_below, zeroInner_below, zeroVal_below, getterPath_below, copyInto_below, storeData_below, storeVal_below, loadMem_below, deleteStor_below] [heapPut_const, alloc_const, readCell_const, readAt_const, applyOp_const, setCell_const, writeAt_const, readLen_const, writeLen_const, heapObj_const, heapAt_const, heapBytes_const, allocRef_const, storRef_const, getV_const, zeroVal_const, zeroData_const, loadMem_const, deleteStor_const, storeData_const, storeVal_const, memSet_const, memElem_const, readLoc_const, lengthOf_const, indexLoc_const, indexNat_const, instanceAt_const, credit_const, debit_const, mark_const, rollbackTo_const, reraise_const, fieldsOf_const, ret32_const, decodeArgs_const, bytesOfRV_const, encodeVals_const, convRV_const, convExplicitRV_const, writeLoc_const, deleteLoc_const, keyStep_const, zeroVals_const, zeroInner_const, copyInto_const, getterPath_const, extReturn_const]
theorem enterInstance_astep (ih : ApproxAt G n) (a sender : Solidity.Roadmap.Address) (v : Solidity.Roadmap.Word)
    (input : Solidity.Roadmap.Bytes) (static : Bool) (c : String) (depth : Nat) (m : Nat × Nat × Heap E.layout) :
    Approx (enterInstance G (n + 1) a sender v input static c depth m)
      (enterInstance G (n + 1 + 1) a sender v input static c depth m) := by
  have gn := growAt G n
  have gs := growAt G (n + 1)
  below_unfold enterInstance n
  refine Approx.bind (Approx.refl (by grow_go [heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow, memElem_grow, readLoc_grow, lengthOf_grow, indexLoc_grow, indexNat_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow, fieldsOf_grow, ret32_grow, decodeArgs_grow, bytesOfRV_grow, encodeVals_grow, convRV_grow, convExplicitRV_grow, writeLoc_grow, deleteLoc_grow, keyStep_grow, zeroVals_grow, zeroInner_grow, copyInto_grow, getterPath_grow, extReturn_grow, gn.evalE, gn.evalPair, gn.evalArgs, gn.evalConvArgs, gn.evalLoc, gn.evalBuiltin, gn.evalArgsRev, gn.pay, gn.execS, gn.forIter, gn.execItems, gn.runMods, gn.callInternal, gn.callAddr, gn.enterInstance, gn.envLoop, gn.dispatch, gs.evalE, gs.evalPair, gs.evalArgs, gs.evalConvArgs, gs.evalLoc, gs.evalBuiltin, gs.evalArgsRev, gs.pay, gs.execS, gs.forIter, gs.execItems, gs.runMods, gs.callInternal, gs.callAddr, gs.enterInstance, gs.envLoop, gs.dispatch])) fun _ => ?_
  refine Approx.attempt_bind (ih.dispatch _ _) (fun r => ?_) (fun x => ?_)
  · exact Approx.refl (by grow_go [heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow, memElem_grow, readLoc_grow, lengthOf_grow, indexLoc_grow, indexNat_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow, fieldsOf_grow, ret32_grow, decodeArgs_grow, bytesOfRV_grow, encodeVals_grow, convRV_grow, convExplicitRV_grow, writeLoc_grow, deleteLoc_grow, keyStep_grow, zeroVals_grow, zeroInner_grow, copyInto_grow, getterPath_grow, extReturn_grow, gn.evalE, gn.evalPair, gn.evalArgs, gn.evalConvArgs, gn.evalLoc, gn.evalBuiltin, gn.evalArgsRev, gn.pay, gn.execS, gn.forIter, gn.execItems, gn.runMods, gn.callInternal, gn.callAddr, gn.enterInstance, gn.envLoop, gn.dispatch, gs.evalE, gs.evalPair, gs.evalArgs, gs.evalConvArgs, gs.evalLoc, gs.evalBuiltin, gs.evalArgsRev, gs.pay, gs.execS, gs.forIter, gs.execItems, gs.runMods, gs.callInternal, gs.callAddr, gs.enterInstance, gs.envLoop, gs.dispatch])
  · exact ⟨rfl, rfl⟩
theorem envLoop_astep (ih : ApproxAt G n) (depth : Nat) (pstatic : Bool) :
    Approx (envLoop G (n + 1) depth pstatic) (envLoop G (n + 1 + 1) depth pstatic) := by
  have gn := growAt G n
  have gs := growAt G (n + 1)
  below_unfold envLoop n
  approx_go [ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, Approx.sub] [heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow, memElem_grow, readLoc_grow, lengthOf_grow, indexLoc_grow, indexNat_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow, fieldsOf_grow, ret32_grow, decodeArgs_grow, bytesOfRV_grow, encodeVals_grow, convRV_grow, convExplicitRV_grow, writeLoc_grow, deleteLoc_grow, keyStep_grow, zeroVals_grow, zeroInner_grow, copyInto_grow, getterPath_grow, extReturn_grow, gn.evalE, gn.evalPair, gn.evalArgs, gn.evalConvArgs, gn.evalLoc, gn.evalBuiltin, gn.evalArgsRev, gn.pay, gn.execS, gn.forIter, gn.execItems, gn.runMods, gn.callInternal, gn.callAddr, gn.enterInstance, gn.envLoop, gn.dispatch, gs.evalE, gs.evalPair, gs.evalArgs, gs.evalConvArgs, gs.evalLoc, gs.evalBuiltin, gs.evalArgsRev, gs.pay, gs.execS, gs.forIter, gs.execItems, gs.runMods, gs.callInternal, gs.callAddr, gs.enterInstance, gs.envLoop, gs.dispatch] [convRV_below, convExplicitRV_below, bytesOfRV_below, encodeVals_below, writeLoc_below, deleteLoc_below, keyStep_below, zeroVals_below, zeroInner_below, zeroVal_below, getterPath_below, copyInto_below, storeData_below, storeVal_below, loadMem_below, deleteStor_below] [heapPut_const, alloc_const, readCell_const, readAt_const, applyOp_const, setCell_const, writeAt_const, readLen_const, writeLen_const, heapObj_const, heapAt_const, heapBytes_const, allocRef_const, storRef_const, getV_const, zeroVal_const, zeroData_const, loadMem_const, deleteStor_const, storeData_const, storeVal_const, memSet_const, memElem_const, readLoc_const, lengthOf_const, indexLoc_const, indexNat_const, instanceAt_const, credit_const, debit_const, mark_const, rollbackTo_const, reraise_const, fieldsOf_const, ret32_const, decodeArgs_const, bytesOfRV_const, encodeVals_const, convRV_const, convExplicitRV_const, writeLoc_const, deleteLoc_const, keyStep_const, zeroVals_const, zeroInner_const, copyInto_const, getterPath_const, extReturn_const]
theorem dispatch_apart_fn {G : Glob E} {n : Nat} (ih : ApproxAt G n) (F : Fr) (input : Bytes) {d : Decl}
    (hp : G.pickFn F input = some d) (he : input.isEmpty = false) :
    Approx (dispatch G F (n + 1) input) (dispatch G F (n + 1 + 1) input) := by
  have gn := growAt G n
  have gs := growAt G (n + 1)
  simp only [dispatch, hp, he]; approx_go [ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, Approx.sub] [heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow, memElem_grow, readLoc_grow, lengthOf_grow, indexLoc_grow, indexNat_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow, fieldsOf_grow, ret32_grow, decodeArgs_grow, bytesOfRV_grow, encodeVals_grow, convRV_grow, convExplicitRV_grow, writeLoc_grow, deleteLoc_grow, keyStep_grow, zeroVals_grow, zeroInner_grow, copyInto_grow, getterPath_grow, extReturn_grow, gn.evalE, gn.evalPair, gn.evalArgs, gn.evalConvArgs, gn.evalLoc, gn.evalBuiltin, gn.evalArgsRev, gn.pay, gn.execS, gn.forIter, gn.execItems, gn.runMods, gn.callInternal, gn.callAddr, gn.enterInstance, gn.envLoop, gn.dispatch, gs.evalE, gs.evalPair, gs.evalArgs, gs.evalConvArgs, gs.evalLoc, gs.evalBuiltin, gs.evalArgsRev, gs.pay, gs.execS, gs.forIter, gs.execItems, gs.runMods, gs.callInternal, gs.callAddr, gs.enterInstance, gs.envLoop, gs.dispatch] [convRV_below, convExplicitRV_below, bytesOfRV_below, encodeVals_below, writeLoc_below, deleteLoc_below, keyStep_below, zeroVals_below, zeroInner_below, zeroVal_below, getterPath_below, copyInto_below, storeData_below, storeVal_below, loadMem_below, deleteStor_below] [heapPut_const, alloc_const, readCell_const, readAt_const, applyOp_const, setCell_const, writeAt_const, readLen_const, writeLen_const, heapObj_const, heapAt_const, heapBytes_const, allocRef_const, storRef_const, getV_const, zeroVal_const, zeroData_const, loadMem_const, deleteStor_const, storeData_const, storeVal_const, memSet_const, memElem_const, readLoc_const, lengthOf_const, indexLoc_const, indexNat_const, instanceAt_const, credit_const, debit_const, mark_const, rollbackTo_const, reraise_const, fieldsOf_const, ret32_const, decodeArgs_const, bytesOfRV_const, encodeVals_const, convRV_const, convExplicitRV_const, writeLoc_const, deleteLoc_const, keyStep_const, zeroVals_const, zeroInner_const, copyInto_const, getterPath_const, extReturn_const]
theorem dispatch_apart_gn_c {G : Glob E} {n : Nat} (ih : ApproxAt G n) (F : Fr) (input : Bytes) (hp : G.pickFn F input = none) {d : Decl} {ps : List STy} {ρ : STy} {ri : RInit E}
    (hg : G.pickGetter F input = some (d, ps, ρ)) (hc : G.prog.consts d = some ri) :
    Approx (dispatch G F (n + 1) input) (dispatch G F (n + 1 + 1) input) := by
  have gn := growAt G n
  have gs := growAt G (n + 1)
  simp only [dispatch, hp, hc, hg]; approx_go [ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, Approx.sub] [heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow, memElem_grow, readLoc_grow, lengthOf_grow, indexLoc_grow, indexNat_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow, fieldsOf_grow, ret32_grow, decodeArgs_grow, bytesOfRV_grow, encodeVals_grow, convRV_grow, convExplicitRV_grow, writeLoc_grow, deleteLoc_grow, keyStep_grow, zeroVals_grow, zeroInner_grow, copyInto_grow, getterPath_grow, extReturn_grow, gn.evalE, gn.evalPair, gn.evalArgs, gn.evalConvArgs, gn.evalLoc, gn.evalBuiltin, gn.evalArgsRev, gn.pay, gn.execS, gn.forIter, gn.execItems, gn.runMods, gn.callInternal, gn.callAddr, gn.enterInstance, gn.envLoop, gn.dispatch, gs.evalE, gs.evalPair, gs.evalArgs, gs.evalConvArgs, gs.evalLoc, gs.evalBuiltin, gs.evalArgsRev, gs.pay, gs.execS, gs.forIter, gs.execItems, gs.runMods, gs.callInternal, gs.callAddr, gs.enterInstance, gs.envLoop, gs.dispatch] [convRV_below, convExplicitRV_below, bytesOfRV_below, encodeVals_below, writeLoc_below, deleteLoc_below, keyStep_below, zeroVals_below, zeroInner_below, zeroVal_below, getterPath_below, copyInto_below, storeData_below, storeVal_below, loadMem_below, deleteStor_below] [heapPut_const, alloc_const, readCell_const, readAt_const, applyOp_const, setCell_const, writeAt_const, readLen_const, writeLen_const, heapObj_const, heapAt_const, heapBytes_const, allocRef_const, storRef_const, getV_const, zeroVal_const, zeroData_const, loadMem_const, deleteStor_const, storeData_const, storeVal_const, memSet_const, memElem_const, readLoc_const, lengthOf_const, indexLoc_const, indexNat_const, instanceAt_const, credit_const, debit_const, mark_const, rollbackTo_const, reraise_const, fieldsOf_const, ret32_const, decodeArgs_const, bytesOfRV_const, encodeVals_const, convRV_const, convExplicitRV_const, writeLoc_const, deleteLoc_const, keyStep_const, zeroVals_const, zeroInner_const, copyInto_const, getterPath_const, extReturn_const]
theorem dispatch_apart_gn_v {G : Glob E} {n : Nat} (ih : ApproxAt G n) (F : Fr) (input : Bytes) (hp : G.pickFn F input = none) {d : Decl} {ps : List STy} {ρ : STy} {τ : STy}
    (hg : G.pickGetter F input = some (d, ps, ρ)) (hc : G.prog.consts d = none) (hv : d.varTy E = some τ) :
    Approx (dispatch G F (n + 1) input) (dispatch G F (n + 1 + 1) input) := by
  have gn := growAt G n
  have gs := growAt G (n + 1)
  simp only [dispatch, hp, hc, hv, hg]; approx_go [ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, Approx.sub] [heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow, memElem_grow, readLoc_grow, lengthOf_grow, indexLoc_grow, indexNat_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow, fieldsOf_grow, ret32_grow, decodeArgs_grow, bytesOfRV_grow, encodeVals_grow, convRV_grow, convExplicitRV_grow, writeLoc_grow, deleteLoc_grow, keyStep_grow, zeroVals_grow, zeroInner_grow, copyInto_grow, getterPath_grow, extReturn_grow, gn.evalE, gn.evalPair, gn.evalArgs, gn.evalConvArgs, gn.evalLoc, gn.evalBuiltin, gn.evalArgsRev, gn.pay, gn.execS, gn.forIter, gn.execItems, gn.runMods, gn.callInternal, gn.callAddr, gn.enterInstance, gn.envLoop, gn.dispatch, gs.evalE, gs.evalPair, gs.evalArgs, gs.evalConvArgs, gs.evalLoc, gs.evalBuiltin, gs.evalArgsRev, gs.pay, gs.execS, gs.forIter, gs.execItems, gs.runMods, gs.callInternal, gs.callAddr, gs.enterInstance, gs.envLoop, gs.dispatch] [convRV_below, convExplicitRV_below, bytesOfRV_below, encodeVals_below, writeLoc_below, deleteLoc_below, keyStep_below, zeroVals_below, zeroInner_below, zeroVal_below, getterPath_below, copyInto_below, storeData_below, storeVal_below, loadMem_below, deleteStor_below] [heapPut_const, alloc_const, readCell_const, readAt_const, applyOp_const, setCell_const, writeAt_const, readLen_const, writeLen_const, heapObj_const, heapAt_const, heapBytes_const, allocRef_const, storRef_const, getV_const, zeroVal_const, zeroData_const, loadMem_const, deleteStor_const, storeData_const, storeVal_const, memSet_const, memElem_const, readLoc_const, lengthOf_const, indexLoc_const, indexNat_const, instanceAt_const, credit_const, debit_const, mark_const, rollbackTo_const, reraise_const, fieldsOf_const, ret32_const, decodeArgs_const, bytesOfRV_const, encodeVals_const, convRV_const, convExplicitRV_const, writeLoc_const, deleteLoc_const, keyStep_const, zeroVals_const, zeroInner_const, copyInto_const, getterPath_const, extReturn_const]
theorem dispatch_apart_gn_x {G : Glob E} {n : Nat} (ih : ApproxAt G n) (F : Fr) (input : Bytes) (hp : G.pickFn F input = none) {d : Decl} {ps : List STy} {ρ : STy} 
    (hg : G.pickGetter F input = some (d, ps, ρ)) (hc : G.prog.consts d = none) (hv : d.varTy E = none) :
    Approx (dispatch G F (n + 1) input) (dispatch G F (n + 1 + 1) input) := by
  have gn := growAt G n
  have gs := growAt G (n + 1)
  simp only [dispatch, hp, hc, hv, hg]; approx_go [ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, Approx.sub] [heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow, memElem_grow, readLoc_grow, lengthOf_grow, indexLoc_grow, indexNat_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow, fieldsOf_grow, ret32_grow, decodeArgs_grow, bytesOfRV_grow, encodeVals_grow, convRV_grow, convExplicitRV_grow, writeLoc_grow, deleteLoc_grow, keyStep_grow, zeroVals_grow, zeroInner_grow, copyInto_grow, getterPath_grow, extReturn_grow, gn.evalE, gn.evalPair, gn.evalArgs, gn.evalConvArgs, gn.evalLoc, gn.evalBuiltin, gn.evalArgsRev, gn.pay, gn.execS, gn.forIter, gn.execItems, gn.runMods, gn.callInternal, gn.callAddr, gn.enterInstance, gn.envLoop, gn.dispatch, gs.evalE, gs.evalPair, gs.evalArgs, gs.evalConvArgs, gs.evalLoc, gs.evalBuiltin, gs.evalArgsRev, gs.pay, gs.execS, gs.forIter, gs.execItems, gs.runMods, gs.callInternal, gs.callAddr, gs.enterInstance, gs.envLoop, gs.dispatch] [convRV_below, convExplicitRV_below, bytesOfRV_below, encodeVals_below, writeLoc_below, deleteLoc_below, keyStep_below, zeroVals_below, zeroInner_below, zeroVal_below, getterPath_below, copyInto_below, storeData_below, storeVal_below, loadMem_below, deleteStor_below] [heapPut_const, alloc_const, readCell_const, readAt_const, applyOp_const, setCell_const, writeAt_const, readLen_const, writeLen_const, heapObj_const, heapAt_const, heapBytes_const, allocRef_const, storRef_const, getV_const, zeroVal_const, zeroData_const, loadMem_const, deleteStor_const, storeData_const, storeVal_const, memSet_const, memElem_const, readLoc_const, lengthOf_const, indexLoc_const, indexNat_const, instanceAt_const, credit_const, debit_const, mark_const, rollbackTo_const, reraise_const, fieldsOf_const, ret32_const, decodeArgs_const, bytesOfRV_const, encodeVals_const, convRV_const, convExplicitRV_const, writeLoc_const, deleteLoc_const, keyStep_const, zeroVals_const, zeroInner_const, copyInto_const, getterPath_const, extReturn_const]
theorem dispatch_apart_gn {G : Glob E} {n : Nat} (ih : ApproxAt G n) (F : Fr) (input : Bytes) (hp : G.pickFn F input = none) {r : Decl × List STy × STy} (hg : G.pickGetter F input = some r) :
    Approx (dispatch G F (n + 1) input) (dispatch G F (n + 1 + 1) input) := by
  obtain ⟨d, ps, ρ⟩ := r
  cases hc : G.prog.consts d with
  | some ri => exact dispatch_apart_gn_c ih F input hp hg hc
  | none =>
    cases hv : d.varTy E with
    | some τ => exact dispatch_apart_gn_v ih F input hp hg hc hv
    | none => exact dispatch_apart_gn_x ih F input hp hg hc hv
theorem dispatch_apart_gs_c {G : Glob E} {n : Nat} (ih : ApproxAt G n) (F : Fr) (input : Bytes) {d0 : Decl} (hp : G.pickFn F input = some d0) (he : input.isEmpty = true) {d : Decl} {ps : List STy} {ρ : STy} {ri : RInit E}
    (hg : G.pickGetter F input = some (d, ps, ρ)) (hc : G.prog.consts d = some ri) :
    Approx (dispatch G F (n + 1) input) (dispatch G F (n + 1 + 1) input) := by
  have gn := growAt G n
  have gs := growAt G (n + 1)
  simp only [dispatch, hp, he, hc, hg]; approx_go [ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, Approx.sub] [heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow, memElem_grow, readLoc_grow, lengthOf_grow, indexLoc_grow, indexNat_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow, fieldsOf_grow, ret32_grow, decodeArgs_grow, bytesOfRV_grow, encodeVals_grow, convRV_grow, convExplicitRV_grow, writeLoc_grow, deleteLoc_grow, keyStep_grow, zeroVals_grow, zeroInner_grow, copyInto_grow, getterPath_grow, extReturn_grow, gn.evalE, gn.evalPair, gn.evalArgs, gn.evalConvArgs, gn.evalLoc, gn.evalBuiltin, gn.evalArgsRev, gn.pay, gn.execS, gn.forIter, gn.execItems, gn.runMods, gn.callInternal, gn.callAddr, gn.enterInstance, gn.envLoop, gn.dispatch, gs.evalE, gs.evalPair, gs.evalArgs, gs.evalConvArgs, gs.evalLoc, gs.evalBuiltin, gs.evalArgsRev, gs.pay, gs.execS, gs.forIter, gs.execItems, gs.runMods, gs.callInternal, gs.callAddr, gs.enterInstance, gs.envLoop, gs.dispatch] [convRV_below, convExplicitRV_below, bytesOfRV_below, encodeVals_below, writeLoc_below, deleteLoc_below, keyStep_below, zeroVals_below, zeroInner_below, zeroVal_below, getterPath_below, copyInto_below, storeData_below, storeVal_below, loadMem_below, deleteStor_below] [heapPut_const, alloc_const, readCell_const, readAt_const, applyOp_const, setCell_const, writeAt_const, readLen_const, writeLen_const, heapObj_const, heapAt_const, heapBytes_const, allocRef_const, storRef_const, getV_const, zeroVal_const, zeroData_const, loadMem_const, deleteStor_const, storeData_const, storeVal_const, memSet_const, memElem_const, readLoc_const, lengthOf_const, indexLoc_const, indexNat_const, instanceAt_const, credit_const, debit_const, mark_const, rollbackTo_const, reraise_const, fieldsOf_const, ret32_const, decodeArgs_const, bytesOfRV_const, encodeVals_const, convRV_const, convExplicitRV_const, writeLoc_const, deleteLoc_const, keyStep_const, zeroVals_const, zeroInner_const, copyInto_const, getterPath_const, extReturn_const]
theorem dispatch_apart_gs_v {G : Glob E} {n : Nat} (ih : ApproxAt G n) (F : Fr) (input : Bytes) {d0 : Decl} (hp : G.pickFn F input = some d0) (he : input.isEmpty = true) {d : Decl} {ps : List STy} {ρ : STy} {τ : STy}
    (hg : G.pickGetter F input = some (d, ps, ρ)) (hc : G.prog.consts d = none) (hv : d.varTy E = some τ) :
    Approx (dispatch G F (n + 1) input) (dispatch G F (n + 1 + 1) input) := by
  have gn := growAt G n
  have gs := growAt G (n + 1)
  simp only [dispatch, hp, he, hc, hv, hg]; approx_go [ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, Approx.sub] [heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow, memElem_grow, readLoc_grow, lengthOf_grow, indexLoc_grow, indexNat_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow, fieldsOf_grow, ret32_grow, decodeArgs_grow, bytesOfRV_grow, encodeVals_grow, convRV_grow, convExplicitRV_grow, writeLoc_grow, deleteLoc_grow, keyStep_grow, zeroVals_grow, zeroInner_grow, copyInto_grow, getterPath_grow, extReturn_grow, gn.evalE, gn.evalPair, gn.evalArgs, gn.evalConvArgs, gn.evalLoc, gn.evalBuiltin, gn.evalArgsRev, gn.pay, gn.execS, gn.forIter, gn.execItems, gn.runMods, gn.callInternal, gn.callAddr, gn.enterInstance, gn.envLoop, gn.dispatch, gs.evalE, gs.evalPair, gs.evalArgs, gs.evalConvArgs, gs.evalLoc, gs.evalBuiltin, gs.evalArgsRev, gs.pay, gs.execS, gs.forIter, gs.execItems, gs.runMods, gs.callInternal, gs.callAddr, gs.enterInstance, gs.envLoop, gs.dispatch] [convRV_below, convExplicitRV_below, bytesOfRV_below, encodeVals_below, writeLoc_below, deleteLoc_below, keyStep_below, zeroVals_below, zeroInner_below, zeroVal_below, getterPath_below, copyInto_below, storeData_below, storeVal_below, loadMem_below, deleteStor_below] [heapPut_const, alloc_const, readCell_const, readAt_const, applyOp_const, setCell_const, writeAt_const, readLen_const, writeLen_const, heapObj_const, heapAt_const, heapBytes_const, allocRef_const, storRef_const, getV_const, zeroVal_const, zeroData_const, loadMem_const, deleteStor_const, storeData_const, storeVal_const, memSet_const, memElem_const, readLoc_const, lengthOf_const, indexLoc_const, indexNat_const, instanceAt_const, credit_const, debit_const, mark_const, rollbackTo_const, reraise_const, fieldsOf_const, ret32_const, decodeArgs_const, bytesOfRV_const, encodeVals_const, convRV_const, convExplicitRV_const, writeLoc_const, deleteLoc_const, keyStep_const, zeroVals_const, zeroInner_const, copyInto_const, getterPath_const, extReturn_const]
theorem dispatch_apart_gs_x {G : Glob E} {n : Nat} (ih : ApproxAt G n) (F : Fr) (input : Bytes) {d0 : Decl} (hp : G.pickFn F input = some d0) (he : input.isEmpty = true) {d : Decl} {ps : List STy} {ρ : STy} 
    (hg : G.pickGetter F input = some (d, ps, ρ)) (hc : G.prog.consts d = none) (hv : d.varTy E = none) :
    Approx (dispatch G F (n + 1) input) (dispatch G F (n + 1 + 1) input) := by
  have gn := growAt G n
  have gs := growAt G (n + 1)
  simp only [dispatch, hp, he, hc, hv, hg]; approx_go [ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, Approx.sub] [heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow, memElem_grow, readLoc_grow, lengthOf_grow, indexLoc_grow, indexNat_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow, fieldsOf_grow, ret32_grow, decodeArgs_grow, bytesOfRV_grow, encodeVals_grow, convRV_grow, convExplicitRV_grow, writeLoc_grow, deleteLoc_grow, keyStep_grow, zeroVals_grow, zeroInner_grow, copyInto_grow, getterPath_grow, extReturn_grow, gn.evalE, gn.evalPair, gn.evalArgs, gn.evalConvArgs, gn.evalLoc, gn.evalBuiltin, gn.evalArgsRev, gn.pay, gn.execS, gn.forIter, gn.execItems, gn.runMods, gn.callInternal, gn.callAddr, gn.enterInstance, gn.envLoop, gn.dispatch, gs.evalE, gs.evalPair, gs.evalArgs, gs.evalConvArgs, gs.evalLoc, gs.evalBuiltin, gs.evalArgsRev, gs.pay, gs.execS, gs.forIter, gs.execItems, gs.runMods, gs.callInternal, gs.callAddr, gs.enterInstance, gs.envLoop, gs.dispatch] [convRV_below, convExplicitRV_below, bytesOfRV_below, encodeVals_below, writeLoc_below, deleteLoc_below, keyStep_below, zeroVals_below, zeroInner_below, zeroVal_below, getterPath_below, copyInto_below, storeData_below, storeVal_below, loadMem_below, deleteStor_below] [heapPut_const, alloc_const, readCell_const, readAt_const, applyOp_const, setCell_const, writeAt_const, readLen_const, writeLen_const, heapObj_const, heapAt_const, heapBytes_const, allocRef_const, storRef_const, getV_const, zeroVal_const, zeroData_const, loadMem_const, deleteStor_const, storeData_const, storeVal_const, memSet_const, memElem_const, readLoc_const, lengthOf_const, indexLoc_const, indexNat_const, instanceAt_const, credit_const, debit_const, mark_const, rollbackTo_const, reraise_const, fieldsOf_const, ret32_const, decodeArgs_const, bytesOfRV_const, encodeVals_const, convRV_const, convExplicitRV_const, writeLoc_const, deleteLoc_const, keyStep_const, zeroVals_const, zeroInner_const, copyInto_const, getterPath_const, extReturn_const]
theorem dispatch_apart_gs {G : Glob E} {n : Nat} (ih : ApproxAt G n) (F : Fr) (input : Bytes) {d0 : Decl} (hp : G.pickFn F input = some d0) (he : input.isEmpty = true) {r : Decl × List STy × STy} (hg : G.pickGetter F input = some r) :
    Approx (dispatch G F (n + 1) input) (dispatch G F (n + 1 + 1) input) := by
  obtain ⟨d, ps, ρ⟩ := r
  cases hc : G.prog.consts d with
  | some ri => exact dispatch_apart_gs_c ih F input hp he hg hc
  | none =>
    cases hv : d.varTy E with
    | some τ => exact dispatch_apart_gs_v ih F input hp he hg hc hv
    | none => exact dispatch_apart_gs_x ih F input hp he hg hc hv
theorem dispatch_apart_sn {G : Glob E} {n : Nat} (ih : ApproxAt G n) (F : Fr) (input : Bytes)
    (hp : G.pickFn F input = none) (hg : G.pickGetter F input = none) :
    Approx (dispatch G F (n + 1) input) (dispatch G F (n + 1 + 1) input) := by
  have gn := growAt G n
  have gs := growAt G (n + 1)
  simp only [dispatch, hp, hg]; approx_go [ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, Approx.sub] [heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow, memElem_grow, readLoc_grow, lengthOf_grow, indexLoc_grow, indexNat_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow, fieldsOf_grow, ret32_grow, decodeArgs_grow, bytesOfRV_grow, encodeVals_grow, convRV_grow, convExplicitRV_grow, writeLoc_grow, deleteLoc_grow, keyStep_grow, zeroVals_grow, zeroInner_grow, copyInto_grow, getterPath_grow, extReturn_grow, gn.evalE, gn.evalPair, gn.evalArgs, gn.evalConvArgs, gn.evalLoc, gn.evalBuiltin, gn.evalArgsRev, gn.pay, gn.execS, gn.forIter, gn.execItems, gn.runMods, gn.callInternal, gn.callAddr, gn.enterInstance, gn.envLoop, gn.dispatch, gs.evalE, gs.evalPair, gs.evalArgs, gs.evalConvArgs, gs.evalLoc, gs.evalBuiltin, gs.evalArgsRev, gs.pay, gs.execS, gs.forIter, gs.execItems, gs.runMods, gs.callInternal, gs.callAddr, gs.enterInstance, gs.envLoop, gs.dispatch] [convRV_below, convExplicitRV_below, bytesOfRV_below, encodeVals_below, writeLoc_below, deleteLoc_below, keyStep_below, zeroVals_below, zeroInner_below, zeroVal_below, getterPath_below, copyInto_below, storeData_below, storeVal_below, loadMem_below, deleteStor_below] [heapPut_const, alloc_const, readCell_const, readAt_const, applyOp_const, setCell_const, writeAt_const, readLen_const, writeLen_const, heapObj_const, heapAt_const, heapBytes_const, allocRef_const, storRef_const, getV_const, zeroVal_const, zeroData_const, loadMem_const, deleteStor_const, storeData_const, storeVal_const, memSet_const, memElem_const, readLoc_const, lengthOf_const, indexLoc_const, indexNat_const, instanceAt_const, credit_const, debit_const, mark_const, rollbackTo_const, reraise_const, fieldsOf_const, ret32_const, decodeArgs_const, bytesOfRV_const, encodeVals_const, convRV_const, convExplicitRV_const, writeLoc_const, deleteLoc_const, keyStep_const, zeroVals_const, zeroInner_const, copyInto_const, getterPath_const, extReturn_const]
theorem dispatch_apart_ss {G : Glob E} {n : Nat} (ih : ApproxAt G n) (F : Fr) (input : Bytes) {d : Decl}
    (hp : G.pickFn F input = some d) (he : input.isEmpty = true) (hg : G.pickGetter F input = none) :
    Approx (dispatch G F (n + 1) input) (dispatch G F (n + 1 + 1) input) := by
  have gn := growAt G n
  have gs := growAt G (n + 1)
  simp only [dispatch, hp, he, hg]; approx_go [ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, Approx.sub] [heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, zeroVal_grow, zeroData_grow, loadMem_grow, deleteStor_grow, storeData_grow, storeVal_grow, memSet_grow, memElem_grow, readLoc_grow, lengthOf_grow, indexLoc_grow, indexNat_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow, fieldsOf_grow, ret32_grow, decodeArgs_grow, bytesOfRV_grow, encodeVals_grow, convRV_grow, convExplicitRV_grow, writeLoc_grow, deleteLoc_grow, keyStep_grow, zeroVals_grow, zeroInner_grow, copyInto_grow, getterPath_grow, extReturn_grow, gn.evalE, gn.evalPair, gn.evalArgs, gn.evalConvArgs, gn.evalLoc, gn.evalBuiltin, gn.evalArgsRev, gn.pay, gn.execS, gn.forIter, gn.execItems, gn.runMods, gn.callInternal, gn.callAddr, gn.enterInstance, gn.envLoop, gn.dispatch, gs.evalE, gs.evalPair, gs.evalArgs, gs.evalConvArgs, gs.evalLoc, gs.evalBuiltin, gs.evalArgsRev, gs.pay, gs.execS, gs.forIter, gs.execItems, gs.runMods, gs.callInternal, gs.callAddr, gs.enterInstance, gs.envLoop, gs.dispatch] [convRV_below, convExplicitRV_below, bytesOfRV_below, encodeVals_below, writeLoc_below, deleteLoc_below, keyStep_below, zeroVals_below, zeroInner_below, zeroVal_below, getterPath_below, copyInto_below, storeData_below, storeVal_below, loadMem_below, deleteStor_below] [heapPut_const, alloc_const, readCell_const, readAt_const, applyOp_const, setCell_const, writeAt_const, readLen_const, writeLen_const, heapObj_const, heapAt_const, heapBytes_const, allocRef_const, storRef_const, getV_const, zeroVal_const, zeroData_const, loadMem_const, deleteStor_const, storeData_const, storeVal_const, memSet_const, memElem_const, readLoc_const, lengthOf_const, indexLoc_const, indexNat_const, instanceAt_const, credit_const, debit_const, mark_const, rollbackTo_const, reraise_const, fieldsOf_const, ret32_const, decodeArgs_const, bytesOfRV_const, encodeVals_const, convRV_const, convExplicitRV_const, writeLoc_const, deleteLoc_const, keyStep_const, zeroVals_const, zeroInner_const, copyInto_const, getterPath_const, extReturn_const]
theorem dispatch_astep (ih : ApproxAt G n) (F : Fr) (input : Solidity.Roadmap.Bytes) :
    Approx (dispatch G F (n + 1) input) (dispatch G F (n + 1 + 1) input) := by
  cases hp : G.pickFn F input with
  | some d =>
    cases he : input.isEmpty with
    | false => exact dispatch_apart_fn ih F input hp he
    | true =>
      cases hg : G.pickGetter F input with
      | some r => exact dispatch_apart_gs ih F input hp he hg
      | none => exact dispatch_apart_ss ih F input hp he hg
  | none =>
    cases hg : G.pickGetter F input with
    | some r => exact dispatch_apart_gn ih F input hp hg
    | none => exact dispatch_apart_sn ih F input hp hg

/-- **Every interpreter function is monotone in its horizon.** -/
theorem approxAt (G : Glob E) : ∀ n, ApproxAt G n
  | 0 => approxAt_zero G
  | n + 1 =>
    have ih := approxAt G n
    ⟨evalE_astep ih, evalPair_astep ih, evalArgs_astep ih, evalConvArgs_astep ih, evalLoc_astep ih,
      evalBuiltin_astep ih, evalArgsRev_astep ih, pay_astep ih, execS_astep ih, forIter_astep ih,
      execItems_astep ih, runMods_astep ih, callInternal_astep ih, callAddr_astep ih, enterInstance_astep ih,
      envLoop_astep ih, dispatch_astep ih⟩

end

/-! ### Transactions show a prefix of their events -/

theorem runTx_grow (G : Glob E) (n : Nat) (q : Request) : Grow (runTx G n q) := by
  have gn := growAt { G with timestamp := q.timestamp } n
  unfold runTx
  dsimp only
  grow_go [gn.dispatch, heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow]

theorem runTx_approx (G : Glob E) (n : Nat) (q : Request) : Approx (runTx G n q) (runTx G (n + 1) q) := by
  have ih := approxAt { G with timestamp := q.timestamp } n
  unfold runTx
  dsimp only
  refine Approx.bind (Approx.refl (mark_grow)) fun m => ?_
  refine Approx.bind (Approx.refl (instanceAt_grow _ _)) fun oc => ?_
  split
  · exact Approx.refl (by grow_go [heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow])
  · refine Approx.attempt_bind ?_ (fun _ => Approx.refl (by grow_go [heapPut_grow, alloc_grow, readCell_grow, readAt_grow, applyOp_grow, setCell_grow, writeAt_grow, readLen_grow, writeLen_grow, heapObj_grow, heapAt_grow, heapBytes_grow, allocRef_grow, storRef_grow, getV_grow, instanceAt_grow, emitEvent_grow, credit_grow, debit_grow, mark_grow, rollbackTo_grow, reraise_grow])) (fun _ => ⟨rfl, rfl⟩)
    exact Approx.bind (Approx.refl (credit_grow _ _)) fun _ => ih.dispatch _ _

theorem Approx.mono {Γ : RCtx} {α : Type} {f : Nat → EM E Γ α} (h : ∀ n, Approx (f n) (f (n + 1)))
    (hg : ∀ n, Grow (f n)) {n m : Nat} (hnm : n ≤ m) : Approx (f n) (f m) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hnm
  induction d with
  | zero => exact Approx.refl (hg n)
  | succ d ih => exact (ih (by omega)).trans (h _)

/-- **A transaction's events grow with its horizon**: a run that has not
completed at horizon `k` shows a prefix of the events of the run at every
`k' ≥ k`. -/
theorem runTx_events_mono (G : Glob E) (q : Request) (s : St E) {k k' : Nat} (hk : k ≤ k')
    (hd : Done (runAt (fun f => runTx G f q) s k) = false) :
    (runAt (fun f => runTx G f q) s k).2.events <+: (runAt (fun f => runTx G f q) s k').2.events := by
  have ha := Approx.mono (f := fun f => runTx G f q) (fun n => runTx_approx G n q) (fun n => runTx_grow G n q) hk
  simp only [runAt]
  rcases ha.2.2 (L0 E, s) with ⟨_, he⟩ | he
  · exact he
  · rw [he]; exact List.prefix_refl _

/-- A transaction's events extend the events before it. -/
theorem runTx_extends (G : Glob E) (q : Request) (s : St E) (k : Nat) :
    s.events <+: (runAt (fun f => runTx G f q) s k).2.events := runTx_grow G k q (L0 E, s)

/-- info: 'Solidity.Source.belowAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms belowAt

/-- info: 'Solidity.Source.runTx_stable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms runTx_stable

/-- info: 'Solidity.Source.deploy_stable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms deploy_stable

/-- info: 'Solidity.Source.firstDone_runTx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms firstDone_runTx

/-- info: 'Solidity.Source.runTx_stuck_stable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms runTx_stuck_stable

end Solidity.Source