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
      | exact Below.timeout _
      | (with_reducible exact Below.refl _)
      | (first $[| apply $ls:ident]*)
      | (refine Below.bind ?_ fun _ => ?_)
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

end Solidity.Source
