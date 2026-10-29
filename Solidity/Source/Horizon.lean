import Solidity.Source.Semantics

/-!
# Horizons: the interpreter is monotone in its fuel (S05 item 2)

`Approx m m'`: `m` is `m'` at a smaller horizon.  Both only append events
(`Grow`), and on every state either `m` times out with events that `m'`
extends, or the two runs are equal.
-/

namespace Solidity.Source

open EM

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
      | (refine Below.attempt_bind ?_ ?_ ?_)
      | (refine Below.bind ?_ ?_)
      | (with_reducible intro _)
      | (with_reducible rfl)
      | split))

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

end Solidity.Source
