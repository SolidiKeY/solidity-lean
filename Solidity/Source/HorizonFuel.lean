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

Every interpreter function also only appends events (`growAt`), and a run
that times out shows a prefix of the events of the run at every larger
horizon (`approxAt`, `runTx_events_mono`); `Solidity/Source/Session.lean`
uses this to show the events of unfinished transactions. For checking cost
those results live in `HorizonGrow`, `HorizonConst` and `Horizon` (which
imports the others, so its importers see all of them).

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

theorem halt_bind {Γ : RCtx} {α β : Type} (h : Halt) (k : α → EM E Γ β) :
    (halt h >>= k : EM E Γ β) = halt h := rfl

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

theorem pushVals_below {Γ' : RCtx} (F : Fr) (n : Nat) : ∀ (slots : List (Option STy)) {σs : List STy}
    (vs : RVals E.layout σs) {Γ : RCtx} (l : Locals E.layout Γ),
    Below (pushVals (Γ' := Γ') F n slots vs l) (pushVals F (n + 1) slots vs l)
  | [], _, .nil, _, _ => Below.refl _
  | [], _, .cons _ _, _, _ => Below.refl _
  | Option.none :: _, _, .nil, _, _ => Below.refl _
  | Option.none :: ss, _, .cons _ vs, _, l => pushVals_below F n ss vs l
  | Option.some _ :: _, _, .nil, _, _ => Below.refl _
  | Option.some τ :: ss, _, .cons v vs, _, l =>
    Below.bind (convRV_below F n τ v) fun _ => Below.bind (Below.refl _) fun _ => pushVals_below F n ss vs _

theorem convExplicitRV_below {Γ : RCtx} (F : Fr) (n : Nat) {σ : STy} (τ : STy) (v : RVal E.layout σ) :
    Below (convExplicitRV (Γ := Γ) F n τ v) (convExplicitRV F (n + 1) τ v) := by
  unfold convExplicitRV
  below_go [convRV_below, pushVals_below, bytesOfRV_below]

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



/-! The shared horizon family below covers both calldata modes and the new
delegated library entry. The shared schema also accepts the existing failure plan; ordinary-mode records and statements stay unchanged. -/

theorem Below.withLibraryCalldata {Γ : RCtx} {α : Type}
    (known : Bool) (ty : STy) {a b : EM E Γ α} (h : Below a b) :
    Below (Solidity.Source.withLibraryCalldata known ty a)
      (Solidity.Source.withLibraryCalldata known ty b) := by
  cases known <;> cases ht : ty.containsCalldata <;> simp only [Solidity.Source.withLibraryCalldata, ht, Bool.false_eq_true, if_false, if_true] <;> first | exact h | exact Below.refl _

section
structure HorizonAt (Rel : ∀ {Γ : RCtx} {α : Type}, EM E Γ α → EM E Γ α → Prop) (G : Glob E) (n : Nat) (plan : FailureExecution.RuntimePlan := none) : Prop where
  evalE : ∀ (known : Bool) (F : Fr) {Γ : RCtx} {τ : STy} (e : RExpr E Γ τ), Rel (evalE G F n e (calldataKnown := known) (plan := plan)) (evalE G F (n + 1) e (calldataKnown := known) (plan := plan))
  evalPair : ∀ (known : Bool) (F : Fr) {Γ : RCtx} {σ τ : STy} (a : RExpr E Γ σ) (b : RExpr E Γ τ),
    Rel (evalPair G F n a b (calldataKnown := known) (plan := plan)) (evalPair G F (n + 1) a b (calldataKnown := known) (plan := plan))
  evalArgs : ∀ (known : Bool) (F : Fr) {Γ : RCtx} {τs : List STy} (es : RArgs E Γ τs),
    Rel (evalArgs G F n es (calldataKnown := known) (plan := plan)) (evalArgs G F (n + 1) es (calldataKnown := known) (plan := plan))
  evalConvArgs : ∀ (known : Bool) (F : Fr) {Γ : RCtx} {τs : List STy} (es : RConvArgs E Γ τs),
    Rel (evalConvArgs G F n es (calldataKnown := known) (plan := plan)) (evalConvArgs G F (n + 1) es (calldataKnown := known) (plan := plan))
  evalLoc : ∀ (known : Bool) (F : Fr) {Γ : RCtx} {τ : STy} (l : RLVal E Γ τ), Rel (evalLoc G F n l (calldataKnown := known) (plan := plan)) (evalLoc G F (n + 1) l (calldataKnown := known) (plan := plan))
  evalBuiltin : ∀ (known : Bool) (F : Fr) {Γ : RCtx} {σs : List STy} (b : Builtin) (args : RArgs E Γ σs) (τ : STy),
    Rel (evalBuiltin G F n b args τ (calldataKnown := known) (plan := plan)) (evalBuiltin G F (n + 1) b args τ (calldataKnown := known) (plan := plan))
  evalArgsRev : ∀ (known : Bool) (F : Fr) {Γ : RCtx} {τs : List STy} (es : RArgs E Γ τs),
    Rel (evalArgsRev G F n es (calldataKnown := known) (plan := plan)) (evalArgsRev G F (n + 1) es (calldataKnown := known) (plan := plan))
  pay : ∀ (known : Bool) (F : Fr) {Γ : RCtx} (a : RExpr E Γ (.address true)) (v : RExpr E Γ (.int IntTy.u256)),
    Rel (pay G F n a v (calldataKnown := known) (plan := plan)) (pay G F (n + 1) a v (calldataKnown := known) (plan := plan))
  execS : ∀ (known : Bool) (F : Fr) (nps : Nat) (ph : Option (Ph E)) {R : List STy} {M : Bool} {k : SCtx} {Γ Γ' : RCtx}
    (s : RStmt E R M k Γ Γ') (l : Locals E.layout Γ),
    Rel (execS G F n nps ph s l (calldataKnown := known) (plan := plan)) (execS G F (n + 1) nps ph s l (calldataKnown := known) (plan := plan))
  forIter : ∀ (known : Bool) (F : Fr) (nps : Nat) (ph : Option (Ph E)) {R : List STy} {M u : Bool} {Γ₁ Γ₂ : RCtx}
    (c : ROptBool E Γ₁) (post : ROptExpr E Γ₁) (body : RStmt E R M ⟨true, u⟩ Γ₁ Γ₂) (l : Locals E.layout Γ₁),
    Rel (forIter G F n nps ph c post body l (calldataKnown := known) (plan := plan)) (forIter G F (n + 1) nps ph c post body l (calldataKnown := known) (plan := plan))
  execItems : ∀ (known : Bool) (F : Fr) (nps : Nat) (ph : Option (Ph E)) {R : List STy} {M : Bool} {k : SCtx} {Γ Γ' : RCtx}
    (b : RItems E R M k Γ Γ') (l : Locals E.layout Γ),
    Rel (execItems G F n nps ph b l (calldataKnown := known) (plan := plan)) (execItems G F (n + 1) nps ph b l (calldataKnown := known) (plan := plan))
  runMods : ∀ (known : Bool) (F : Fr) (b : RBody E) (mods : List (RModInv E b.locals)) (l : Locals E.layout b.locals),
    Rel (runMods G F n b mods l (calldataKnown := known) (plan := plan)) (runMods G F (n + 1) b mods l (calldataKnown := known) (plan := plan))
  callInternal : ∀ (known : Bool) (F : Fr) (d : Decl) {ps : List STy} (vs : Vals E.layout ps) (rs : List STy),
    Rel (callInternal G F n d vs rs (calldataKnown := known) (plan := plan)) (callInternal G F (n + 1) d vs rs (calldataKnown := known) (plan := plan))
  callLibrary : ∀ (F : Fr) (d : Decl) {ps : List STy} (vs : Vals E.layout ps) (rs : List STy),
    Rel (callLibrary G F n d vs rs (plan := plan)) (callLibrary G F (n + 1) d vs rs (plan := plan))
  callAddr : ∀ (F : Fr) (a : Solidity.Roadmap.Address) (v : Solidity.Roadmap.Word) (input : Solidity.Roadmap.Bytes)
    (static : Bool), Rel (callAddr G F n a v input static (plan := plan)) (callAddr G F (n + 1) a v input static (plan := plan))
  enterInstance : ∀ (a sender : Solidity.Roadmap.Address) (v : Solidity.Roadmap.Word) (input : Solidity.Roadmap.Bytes)
    (static : Bool) (c : String) (depth : Nat) (m : Nat × Nat × Heap E.layout),
    Rel (enterInstance G n a sender v input static c depth m (plan := plan))
      (enterInstance G (n + 1) a sender v input static c depth m (plan := plan))
  envLoop : ∀ (depth : Nat) (pstatic : Bool), Rel (envLoop G n depth pstatic (plan := plan)) (envLoop G (n + 1) depth pstatic (plan := plan))
  dispatch : ∀ (F : Fr) (input : Solidity.Roadmap.Bytes), Rel (dispatch G F n input (plan := plan)) (dispatch G F (n + 1) input (plan := plan))

abbrev BelowAtKnown (G : Glob E) (n : Nat) : Prop := HorizonAt (@Below E) G n

theorem belowAtKnown_zero (G : Glob E) : BelowAtKnown G 0 := by
  exact {evalE := by intro known a0 a1 a2 a3; rw [evalE.eq_1]; exact Below.timeout _, evalPair := by intro known a0 a1 a2 a3 a4 a5; rw [evalPair.eq_1]; exact Below.timeout _, evalArgs := by intro known a0 a1 a2 a3; rw [evalArgs.eq_1]; exact Below.timeout _, evalConvArgs := by intro known a0 a1 a2 a3; rw [evalConvArgs.eq_1]; exact Below.timeout _, evalLoc := by intro known a0 a1 a2 a3; rw [evalLoc.eq_1]; exact Below.timeout _, evalBuiltin := by intro known a0 a1 a2 a3 a4 a5; rw [evalBuiltin.eq_1]; exact Below.timeout _, evalArgsRev := by intro known a0 a1 a2 a3; rw [evalArgsRev.eq_1]; exact Below.timeout _, pay := by intro known a0 a1 a2 a3; rw [pay.eq_1]; exact Below.timeout _, execS := by intro known a0 a1 a2 a3 a4 a5 a6 a7 a8 a9; rw [execS.eq_1]; exact Below.timeout _, forIter := by intro known a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11; rw [forIter.eq_1]; exact Below.timeout _, execItems := by intro known a0 a1 a2 a3 a4 a5 a6 a7 a8 a9; rw [execItems.eq_1]; exact Below.timeout _, runMods := by intro known a0 a1 a2 a3; rw [runMods.eq_1]; exact Below.timeout _, callInternal := by intro known a0 a1 a2 a3 a4; rw [callInternal.eq_1]; exact Below.timeout _, callLibrary := by intro F d ps vs rs; rw [callLibrary.eq_1]; exact Below.timeout _, callAddr := by intro a0 a1 a2 a3 a4; rw [callAddr.eq_1]; exact Below.timeout _, enterInstance := by intro a0 a1 a2 a3 a4 a5 a6 a7; rw [enterInstance.eq_1]; exact Below.timeout _, envLoop := by intro a0 a1; rw [envLoop.eq_1]; exact Below.timeout _, dispatch := by intro a0 a1; rw [dispatch.eq_1]; exact Below.timeout _}

variable {G : Glob E} {n : Nat}

theorem evalE_known_step (ih : BelowAtKnown G n) (known : Bool) (F : Fr) {Γ : RCtx} {τ : STy} (e : RExpr E Γ τ) :
    Below (evalE G F (n + 1) e (calldataKnown := known)) (evalE G F (n + 1 + 1) e (calldataKnown := known)) := by
  cases e <;> below_unfold evalE n <;> apply Below.withLibraryCalldata <;> below_go [ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callLibrary, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, convRV_below, pushVals_below, convExplicitRV_below, bytesOfRV_below, encodeVals_below, writeLoc_below, deleteLoc_below, keyStep_below, zeroVals_below, zeroInner_below, zeroVal_below, getterPath_below, copyInto_below, Below.sub]

theorem evalPair_known_step (ih : BelowAtKnown G n) (known : Bool) (F : Fr) {Γ : RCtx} {σ τ : STy} (a : RExpr E Γ σ) (b : RExpr E Γ τ) :
    Below (evalPair G F (n + 1) a b (calldataKnown := known)) (evalPair G F (n + 1 + 1) a b (calldataKnown := known)) := by
  below_unfold evalPair n
  below_go [ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callLibrary, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, convRV_below, pushVals_below, convExplicitRV_below, bytesOfRV_below, encodeVals_below, writeLoc_below, deleteLoc_below, keyStep_below, zeroVals_below, zeroInner_below, zeroVal_below, getterPath_below, copyInto_below, Below.sub]

theorem evalArgs_known_step (ih : BelowAtKnown G n) (known : Bool) (F : Fr) {Γ : RCtx} {τs : List STy} (es : RArgs E Γ τs) :
    Below (evalArgs G F (n + 1) es (calldataKnown := known)) (evalArgs G F (n + 1 + 1) es (calldataKnown := known)) := by
  cases es <;> below_unfold evalArgs n <;> below_go [ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callLibrary, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, convRV_below, pushVals_below, convExplicitRV_below, bytesOfRV_below, encodeVals_below, writeLoc_below, deleteLoc_below, keyStep_below, zeroVals_below, zeroInner_below, zeroVal_below, getterPath_below, copyInto_below, Below.sub]

theorem evalConvArgs_known_step (ih : BelowAtKnown G n) (known : Bool) (F : Fr) {Γ : RCtx} {τs : List STy} (es : RConvArgs E Γ τs) :
    Below (evalConvArgs G F (n + 1) es (calldataKnown := known)) (evalConvArgs G F (n + 1 + 1) es (calldataKnown := known)) := by
  cases es <;> below_unfold evalConvArgs n <;> below_go [ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callLibrary, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, convRV_below, pushVals_below, convExplicitRV_below, bytesOfRV_below, encodeVals_below, writeLoc_below, deleteLoc_below, keyStep_below, zeroVals_below, zeroInner_below, zeroVal_below, getterPath_below, copyInto_below, Below.sub]

theorem evalLoc_known_step (ih : BelowAtKnown G n) (known : Bool) (F : Fr) {Γ : RCtx} {τ : STy} (l : RLVal E Γ τ) :
    Below (evalLoc G F (n + 1) l (calldataKnown := known)) (evalLoc G F (n + 1 + 1) l (calldataKnown := known)) := by
  cases l <;> below_unfold evalLoc n <;> below_go [ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callLibrary, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, convRV_below, pushVals_below, convExplicitRV_below, bytesOfRV_below, encodeVals_below, writeLoc_below, deleteLoc_below, keyStep_below, zeroVals_below, zeroInner_below, zeroVal_below, getterPath_below, copyInto_below, Below.sub]

theorem evalBuiltin_known_step (ih : BelowAtKnown G n) (known : Bool) (F : Fr) {Γ : RCtx} {σs : List STy} (b : Builtin)
    (args : RArgs E Γ σs) (τ : STy) :
    Below (evalBuiltin G F (n + 1) b args τ (calldataKnown := known)) (evalBuiltin G F (n + 1 + 1) b args τ (calldataKnown := known)) := by
  below_unfold evalBuiltin n
  below_go [ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callLibrary, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, convRV_below, pushVals_below, convExplicitRV_below, bytesOfRV_below, encodeVals_below, writeLoc_below, deleteLoc_below, keyStep_below, zeroVals_below, zeroInner_below, zeroVal_below, getterPath_below, copyInto_below, Below.sub]

theorem evalArgsRev_known_step (ih : BelowAtKnown G n) (known : Bool) (F : Fr) {Γ : RCtx} {τs : List STy} (es : RArgs E Γ τs) :
    Below (evalArgsRev G F (n + 1) es (calldataKnown := known)) (evalArgsRev G F (n + 1 + 1) es (calldataKnown := known)) := by
  cases es <;> below_unfold evalArgsRev n <;> below_go [ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callLibrary, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, convRV_below, pushVals_below, convExplicitRV_below, bytesOfRV_below, encodeVals_below, writeLoc_below, deleteLoc_below, keyStep_below, zeroVals_below, zeroInner_below, zeroVal_below, getterPath_below, copyInto_below, Below.sub]

theorem pay_known_step (ih : BelowAtKnown G n) (known : Bool) (F : Fr) {Γ : RCtx} (a : RExpr E Γ (.address true))
    (v : RExpr E Γ (.int IntTy.u256)) : Below (pay G F (n + 1) a v (calldataKnown := known)) (pay G F (n + 1 + 1) a v (calldataKnown := known)) := by
  below_unfold pay n
  below_go [ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callLibrary, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, convRV_below, pushVals_below, convExplicitRV_below, bytesOfRV_below, encodeVals_below, writeLoc_below, deleteLoc_below, keyStep_below, zeroVals_below, zeroInner_below, zeroVal_below, getterPath_below, copyInto_below, Below.sub]

theorem execS_known_step (ih : BelowAtKnown G n) (known : Bool) (F : Fr) (nps : Nat) (ph : Option (Ph E)) {R : List STy} {M : Bool}
    {k : SCtx} {Γ Γ' : RCtx} (s : RStmt E R M k Γ Γ') (l : Locals E.layout Γ) :
    Below (execS G F (n + 1) nps ph s l (calldataKnown := known)) (execS G F (n + 1 + 1) nps ph s l (calldataKnown := known)) := by
  cases s <;> below_unfold execS n <;> below_go [ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callLibrary, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, convRV_below, pushVals_below, convExplicitRV_below, bytesOfRV_below, encodeVals_below, writeLoc_below, deleteLoc_below, keyStep_below, zeroVals_below, zeroInner_below, zeroVal_below, getterPath_below, copyInto_below, Below.sub]

theorem forIter_known_step (ih : BelowAtKnown G n) (known : Bool) (F : Fr) (nps : Nat) (ph : Option (Ph E)) {R : List STy} {M u : Bool}
    {Γ₁ Γ₂ : RCtx} (c : ROptBool E Γ₁) (post : ROptExpr E Γ₁) (body : RStmt E R M ⟨true, u⟩ Γ₁ Γ₂)
    (l : Locals E.layout Γ₁) :
    Below (forIter G F (n + 1) nps ph c post body l (calldataKnown := known)) (forIter G F (n + 1 + 1) nps ph c post body l (calldataKnown := known)) := by
  cases c <;> below_unfold forIter n <;> below_go [ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callLibrary, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, convRV_below, pushVals_below, convExplicitRV_below, bytesOfRV_below, encodeVals_below, writeLoc_below, deleteLoc_below, keyStep_below, zeroVals_below, zeroInner_below, zeroVal_below, getterPath_below, copyInto_below, Below.sub]

theorem execItems_known_step (ih : BelowAtKnown G n) (known : Bool) (F : Fr) (nps : Nat) (ph : Option (Ph E)) {R : List STy} {M : Bool}
    {k : SCtx} {Γ Γ' : RCtx} (b : RItems E R M k Γ Γ') (l : Locals E.layout Γ) :
    Below (execItems G F (n + 1) nps ph b l (calldataKnown := known)) (execItems G F (n + 1 + 1) nps ph b l (calldataKnown := known)) := by
  cases b <;> below_unfold execItems n <;> below_go [ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callLibrary, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, convRV_below, pushVals_below, convExplicitRV_below, bytesOfRV_below, encodeVals_below, writeLoc_below, deleteLoc_below, keyStep_below, zeroVals_below, zeroInner_below, zeroVal_below, getterPath_below, copyInto_below, Below.sub]

theorem runMods_known_step (ih : BelowAtKnown G n) (known : Bool) (F : Fr) (b : RBody E) (mods : List (RModInv E b.locals))
    (l : Locals E.layout b.locals) : Below (runMods G F (n + 1) b mods l (calldataKnown := known)) (runMods G F (n + 1 + 1) b mods l (calldataKnown := known)) := by
  cases mods with
  | nil => below_unfold runMods n; below_go [ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callLibrary, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, convRV_below, pushVals_below, convExplicitRV_below, bytesOfRV_below, encodeVals_below, writeLoc_below, deleteLoc_below, keyStep_below, zeroVals_below, zeroInner_below, zeroVal_below, getterPath_below, copyInto_below, Below.sub]
  | cons md rest =>
    below_unfold runMods n
    refine Below.bind (Below.sub _ (ih.evalConvArgs known _ _)) fun p => ?_
    split
    · exact Below.refl _
    · split
      · refine Below.bind (Below.refl _) fun s => ?_
        refine Below.bind (Below.refl _) fun _ => ?_
        refine Below.attempt_bind (ih.execItems known _ _ _ _ _) (fun r => ?_) (fun x => ?_)
        · below_go [ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callLibrary, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, convRV_below, pushVals_below, convExplicitRV_below, bytesOfRV_below, encodeVals_below, writeLoc_below, deleteLoc_below, keyStep_below, zeroVals_below, zeroInner_below, zeroVal_below, getterPath_below, copyInto_below, Below.sub]
        · rfl
      · exact Below.refl _

theorem callInternal_known_step (ih : BelowAtKnown G n) (known : Bool) (F : Fr) (d : Decl) {ps : List STy} (vs : Vals E.layout ps)
    (rs : List STy) : Below (callInternal G F (n + 1) d vs rs (calldataKnown := known)) (callInternal G F (n + 1 + 1) d vs rs (calldataKnown := known)) := by
  below_unfold callInternal n
  below_go [ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callLibrary, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, convRV_below, pushVals_below, convExplicitRV_below, bytesOfRV_below, encodeVals_below, writeLoc_below, deleteLoc_below, keyStep_below, zeroVals_below, zeroInner_below, zeroVal_below, getterPath_below, copyInto_below, Below.sub]

end

section
variable {G : Glob E} {n : Nat}

theorem callLibrary_known_step (ih : BelowAtKnown G n) (F : Fr) (d : Decl)
    {ps : List STy} (vs : Vals E.layout ps) (rs : List STy) :
    Below (callLibrary G F (n + 1) d vs rs) (callLibrary G F (n + 1 + 1) d vs rs) := by
  below_unfold callLibrary n
  below_go [Below.attempt_bind, ih.callInternal, encodeVals_below]
  all_goals simp_all only [Except.error.injEq, reduceCtorEq] <;> rfl


theorem callAddr_known_step (ih : BelowAtKnown G n) (F : Fr) (a : Solidity.Roadmap.Address) (v : Solidity.Roadmap.Word)
    (input : Solidity.Roadmap.Bytes) (static : Bool) :
    Below (callAddr G F (n + 1) a v input static) (callAddr G F (n + 1 + 1) a v input static) := by
  below_unfold callAddr n
  below_go [ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callLibrary, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, convRV_below, pushVals_below, convExplicitRV_below, bytesOfRV_below, encodeVals_below, writeLoc_below, deleteLoc_below, keyStep_below, zeroVals_below, zeroInner_below, zeroVal_below, getterPath_below, copyInto_below, Below.sub]

theorem enterInstance_known_step (ih : BelowAtKnown G n) (a sender : Solidity.Roadmap.Address) (v : Solidity.Roadmap.Word)
    (input : Solidity.Roadmap.Bytes) (static : Bool) (c : String) (depth : Nat) (m : Nat × Nat × Heap E.layout) :
    Below (enterInstance G (n + 1) a sender v input static c depth m)
      (enterInstance G (n + 1 + 1) a sender v input static c depth m) := by
  below_unfold enterInstance n
  refine Below.bind (Below.refl _) fun _ => ?_
  refine Below.attempt_bind (ih.dispatch _ _) (fun r => ?_) (fun x => ?_)
  · exact Below.refl _
  · rfl

theorem envLoop_known_step (ih : BelowAtKnown G n) (depth : Nat) (pstatic : Bool) :
    Below (envLoop G (n + 1) depth pstatic) (envLoop G (n + 1 + 1) depth pstatic) := by
  below_unfold envLoop n
  below_go [ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callLibrary, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, convRV_below, pushVals_below, convExplicitRV_below, bytesOfRV_below, encodeVals_below, writeLoc_below, deleteLoc_below, keyStep_below, zeroVals_below, zeroInner_below, zeroVal_below, getterPath_below, copyInto_below, Below.sub]

theorem dispatch_known_step (ih : BelowAtKnown G n) (F : Fr) (input : Solidity.Roadmap.Bytes) :
    Below (dispatch G F (n + 1) input) (dispatch G F (n + 1 + 1) input) := by
  below_unfold dispatch n
  below_go [ih.evalE, ih.evalPair, ih.evalArgs, ih.evalConvArgs, ih.evalLoc, ih.evalBuiltin, ih.evalArgsRev, ih.pay, ih.execS, ih.forIter, ih.execItems, ih.runMods, ih.callInternal, ih.callLibrary, ih.callAddr, ih.enterInstance, ih.envLoop, ih.dispatch, convRV_below, pushVals_below, convExplicitRV_below, bytesOfRV_below, encodeVals_below, writeLoc_below, deleteLoc_below, keyStep_below, zeroVals_below, zeroInner_below, zeroVal_below, getterPath_below, copyInto_below, Below.sub]

theorem belowAtKnown (G : Glob E) : ∀ n, BelowAtKnown G n := by
  intro n
  induction n with
  | zero => exact belowAtKnown_zero G
  | succ n ih => exact ⟨evalE_known_step ih, evalPair_known_step ih, evalArgs_known_step ih, evalConvArgs_known_step ih, evalLoc_known_step ih, evalBuiltin_known_step ih, evalArgsRev_known_step ih, pay_known_step ih, execS_known_step ih, forIter_known_step ih, execItems_known_step ih, runMods_known_step ih, callInternal_known_step ih, callLibrary_known_step ih, callAddr_known_step ih, enterInstance_known_step ih, envLoop_known_step ih, dispatch_known_step ih⟩

end

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
  exact (belowAtKnown G (n + 1)).evalE true F e

theorem evalPair_step (ih : BelowAt G n) (F : Fr) {Γ : RCtx} {σ τ : STy} (a : RExpr E Γ σ) (b : RExpr E Γ τ) :
    Below (evalPair G F (n + 1) a b) (evalPair G F (n + 1 + 1) a b) := by
  exact (belowAtKnown G (n + 1)).evalPair true F a b

theorem evalArgs_step (ih : BelowAt G n) (F : Fr) {Γ : RCtx} {τs : List STy} (es : RArgs E Γ τs) :
    Below (evalArgs G F (n + 1) es) (evalArgs G F (n + 1 + 1) es) := by
  exact (belowAtKnown G (n + 1)).evalArgs true F es

theorem evalConvArgs_step (ih : BelowAt G n) (F : Fr) {Γ : RCtx} {τs : List STy} (es : RConvArgs E Γ τs) :
    Below (evalConvArgs G F (n + 1) es) (evalConvArgs G F (n + 1 + 1) es) := by
  exact (belowAtKnown G (n + 1)).evalConvArgs true F es

theorem evalLoc_step (ih : BelowAt G n) (F : Fr) {Γ : RCtx} {τ : STy} (l : RLVal E Γ τ) :
    Below (evalLoc G F (n + 1) l) (evalLoc G F (n + 1 + 1) l) := by
  exact (belowAtKnown G (n + 1)).evalLoc true F l

theorem evalBuiltin_step (ih : BelowAt G n) (F : Fr) {Γ : RCtx} {σs : List STy} (b : Builtin)
    (args : RArgs E Γ σs) (τ : STy) :
    Below (evalBuiltin G F (n + 1) b args τ) (evalBuiltin G F (n + 1 + 1) b args τ) := by
  exact (belowAtKnown G (n + 1)).evalBuiltin true F b args τ

theorem evalArgsRev_step (ih : BelowAt G n) (F : Fr) {Γ : RCtx} {τs : List STy} (es : RArgs E Γ τs) :
    Below (evalArgsRev G F (n + 1) es) (evalArgsRev G F (n + 1 + 1) es) := by
  exact (belowAtKnown G (n + 1)).evalArgsRev true F es

theorem pay_step (ih : BelowAt G n) (F : Fr) {Γ : RCtx} (a : RExpr E Γ (.address true))
    (v : RExpr E Γ (.int IntTy.u256)) : Below (pay G F (n + 1) a v) (pay G F (n + 1 + 1) a v) := by
  exact (belowAtKnown G (n + 1)).pay true F a v

theorem execS_step (ih : BelowAt G n) (F : Fr) (nps : Nat) (ph : Option (Ph E)) {R : List STy} {M : Bool}
    {k : SCtx} {Γ Γ' : RCtx} (s : RStmt E R M k Γ Γ') (l : Locals E.layout Γ) :
    Below (execS G F (n + 1) nps ph s l) (execS G F (n + 1 + 1) nps ph s l) := by
  exact (belowAtKnown G (n + 1)).execS true F nps ph s l

theorem forIter_step (ih : BelowAt G n) (F : Fr) (nps : Nat) (ph : Option (Ph E)) {R : List STy} {M u : Bool}
    {Γ₁ Γ₂ : RCtx} (c : ROptBool E Γ₁) (post : ROptExpr E Γ₁) (body : RStmt E R M ⟨true, u⟩ Γ₁ Γ₂)
    (l : Locals E.layout Γ₁) :
    Below (forIter G F (n + 1) nps ph c post body l) (forIter G F (n + 1 + 1) nps ph c post body l) := by
  exact (belowAtKnown G (n + 1)).forIter true F nps ph c post body l

theorem execItems_step (ih : BelowAt G n) (F : Fr) (nps : Nat) (ph : Option (Ph E)) {R : List STy} {M : Bool}
    {k : SCtx} {Γ Γ' : RCtx} (b : RItems E R M k Γ Γ') (l : Locals E.layout Γ) :
    Below (execItems G F (n + 1) nps ph b l) (execItems G F (n + 1 + 1) nps ph b l) := by
  exact (belowAtKnown G (n + 1)).execItems true F nps ph b l

theorem runMods_step (ih : BelowAt G n) (F : Fr) (b : RBody E) (mods : List (RModInv E b.locals))
    (l : Locals E.layout b.locals) : Below (runMods G F (n + 1) b mods l) (runMods G F (n + 1 + 1) b mods l) := by
  exact (belowAtKnown G (n + 1)).runMods true F b mods l

theorem callInternal_step (ih : BelowAt G n) (F : Fr) (d : Decl) {ps : List STy} (vs : Vals E.layout ps)
    (rs : List STy) : Below (callInternal G F (n + 1) d vs rs) (callInternal G F (n + 1 + 1) d vs rs) := by
  exact (belowAtKnown G (n + 1)).callInternal true F d vs rs

theorem callAddr_step (ih : BelowAt G n) (F : Fr) (a : Solidity.Roadmap.Address) (v : Solidity.Roadmap.Word)
    (input : Solidity.Roadmap.Bytes) (static : Bool) :
    Below (callAddr G F (n + 1) a v input static) (callAddr G F (n + 1 + 1) a v input static) := by
  exact (belowAtKnown G (n + 1)).callAddr F a v input static

theorem enterInstance_step (ih : BelowAt G n) (a sender : Solidity.Roadmap.Address) (v : Solidity.Roadmap.Word)
    (input : Solidity.Roadmap.Bytes) (static : Bool) (c : String) (depth : Nat) (m : Nat × Nat × Heap E.layout) :
    Below (enterInstance G (n + 1) a sender v input static c depth m)
      (enterInstance G (n + 1 + 1) a sender v input static c depth m) := by
  exact (belowAtKnown G (n + 1)).enterInstance a sender v input static c depth m

theorem envLoop_step (ih : BelowAt G n) (depth : Nat) (pstatic : Bool) :
    Below (envLoop G (n + 1) depth pstatic) (envLoop G (n + 1 + 1) depth pstatic) := by
  exact (belowAtKnown G (n + 1)).envLoop depth pstatic

theorem dispatch_step (ih : BelowAt G n) (F : Fr) (input : Solidity.Roadmap.Bytes) :
    Below (dispatch G F (n + 1) input) (dispatch G F (n + 1 + 1) input) := by
  exact (belowAtKnown G (n + 1)).dispatch F input

/-- **Every interpreter function is monotone in its horizon.** -/
theorem belowAt (G : Glob E) : ∀ n, BelowAt G n
  | 0 => belowAt_zero G
  | n + 1 =>
    have h : BelowAtKnown G (n + 1) := belowAtKnown G (n + 1)
    ⟨h.evalE true, h.evalPair true, h.evalArgs true, h.evalConvArgs true,
      h.evalLoc true, h.evalBuiltin true, h.evalArgsRev true, h.pay true,
      h.execS true, h.forIter true, h.execItems true, h.runMods true,
      h.callInternal true, h.callAddr, h.enterInstance, h.envLoop,
      h.dispatch⟩

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
    split <;> refine Below.bind (Below.refl _) fun _ => ?_ <;>
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

end Solidity.Source
