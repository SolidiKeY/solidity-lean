import Solidity.Evm.SimLemmas
import Solidity.Evm.Compile
import Solidity.Semantics.Run

/-!
# The simulation over the scoped syntax

The simulation relation for `Evm/Compile.lean`'s compiler
(`docs/intrinsic.md`, M5, W10.5.3): `Sim C L b F σ m`, the machine `m`
represents the typed state `σ`, is `SimL` of the state's global part
(`State.glob`: its typed storage, by `Evm/Repr.lean`'s `ReprStore`; its
ledger; its transaction, `EnvSim`) and of its locals, each read at its level
(`lvl b i`).

**The locals by position.**  `Look C Γ` is what each local of `Γ` holds, as
the simulation reads it (`Seen`: a value of its type, the storage reference
an alias holds): the typed run's `TEnv` instantiates it (`Look.ofTEnv`),
forgetting the heap typing, so a call that grows the heap leaves the
caller's locals read as they were.  Declaring a local is `Look.cons`
(`TEnv`'s pair), a scope end `Look.drop` along an `Ext`, an assignment
`Look.set` (by recursion on the position, as `TEnv.set`).  A value local's
cell represents its value outright (`ReprV p v`).  A declaration is
`SimL.consVal`/`consAlias`/`consFragile`/`consDead`, a scope's end
`SimL.drop` (its locals popped), and the end of a branch `SimL.flags` (the
branches met, the fragile aliases forgotten).

**A frame's cells.**  Code compiled at base `b` over `Γ` writes only cells
at levels `b` and above (`Stmt.storesFrom`), and a call's body, compiled at
`b + Γ.length`, only above the caller's locals; code that does not store to
a cell leaves it (`exec_mem`), so the caller's `SimL` survives the call:
`SimL.enter` starts the callee's frame from the caller's state, and
`SimL.return` (`returnDrop` after a callee that may shrink an array) puts the
caller's locals back over the machine the callee left.

What needs the typed run (`Stmt.run`) is not here: the expression and
statement lemmas (`val_sim` … `stmt_sim`) and `compile_correct` over the
typed run (`Evm/Expr.lean`, `Evm/Stmt.lean`, `Evm/Correct.lean`).
-/

namespace Solidity.Evm

open Solidity (Ctx Idx Ext)

variable {C : Contract}

/-! ## Levels -/

theorem lvl_here (b : Nat) {Γ : Ctx} {t : LTy} : lvl b (Idx.here : Idx (t :: Γ) t) = b + Γ.length := by
  simp only [lvl, Idx.toNat, List.length_cons]; omega

theorem lvl_there (b : Nat) {Γ : Ctx} {t u : LTy} (i : Idx Γ t) :
    lvl b (Idx.there (u := u) i) = lvl b i := by
  have := i.toNat_lt
  simp only [lvl, Idx.toNat, List.length_cons]; omega

theorem lvl_lt (b : Nat) {Γ : Ctx} {t : LTy} (i : Idx Γ t) : lvl b i < b + Γ.length := by
  have := i.toNat_lt
  simp only [lvl]; omega

theorem le_lvl (b : Nat) {Γ : Ctx} {t : LTy} (i : Idx Γ t) : b ≤ lvl b i := by
  simp only [lvl]; omega

theorem lvl_eq_iff (b : Nat) {Γ : Ctx} {t t' : LTy} (i : Idx Γ t) (j : Idx Γ t') :
    lvl b i = lvl b j ↔ i.toNat = j.toNat := by
  have := i.toNat_lt; have := j.toNat_lt
  simp only [lvl]; omega

theorem lvl_ext (b : Nat) {Γ Δ : Ctx} {t : LTy} (h : Ext Γ Δ) (i : Idx Γ t) :
    lvl b (i.ext h) = lvl b i := by
  have := i.toNat_lt; have := h.length_eq
  simp only [lvl, Ext.toNat_idx]; omega

/-- Two locals at one position have one type. -/
theorem Idx.ty_eq {Γ : Ctx} {t t' : LTy} (i : Idx Γ t) (j : Idx Γ t') (h : i.toNat = j.toNat) :
    t = t' := by
  have h1 := i.getElem?_toNat; have h2 := j.getElem?_toNat
  rw [h, h2] at h1; exact (Option.some.inj h1).symm

theorem memAt_upd (m : Machine) (l l' : Nat) (w : Word) :
    ({ m with mem := upd m.mem (cell l) w } : Machine).memAt l' = if l' = l then w else m.memAt l' := by
  simp only [Machine.memAt, upd]

/-! ## The locals by position -/

/-- What the simulation reads of a local of type `t`: a value of its type,
the storage reference an alias holds (`none` while unset); nothing of a
memory reference, a whole storage or a ledger, which the fragment has
none of. -/
@[reducible] def Seen (C : Contract) : LTy → Type
  | .val p => p.Denote
  | .alias R => Option (Solidity.SRef C (.ref R))
  | .mem _ | .old | .oldNet | .kint => Unit

/-- What each local of `Γ` holds, by position, as the simulation reads it:
`TEnv.get` of the typed run's locals, seen (`Look.ofTEnv`). -/
abbrev Look (C : Contract) (Γ : Ctx) := ∀ {t : LTy}, Idx Γ t → Seen C t

/-- A local declared: `TEnv`'s pair. -/
def Look.cons {Γ : Ctx} {u : LTy} (v : Seen C u) (ρ : Look C Γ) : Look C (u :: Γ) :=
  fun {t} i => match t, i with
    | _, .here => v
    | _, .there j => ρ j

/-- The locals below the innermost. -/
def Look.tail {Γ : Ctx} {u : LTy} (ρ : Look C (u :: Γ)) : Look C Γ := fun j => ρ (.there j)

/-- A local assigned: `TEnv.set`, by recursion on the position. -/
def Look.set : {Γ : Ctx} → {t : LTy} → Look C Γ → Idx Γ t → Seen C t → Look C Γ
  | _ :: _, _, ρ, .here, v => Look.cons v ρ.tail
  | _ :: _, _, ρ, .there i, v => Look.cons (ρ .here) (Look.set ρ.tail i v)

/-- A scope's locals popped. -/
def Look.drop {Γ Δ : Ctx} (h : Ext Γ Δ) (ρ : Look C Δ) : Look C Γ := fun i => ρ (i.ext h)

@[simp] theorem Look.cons_here {Γ : Ctx} {u : LTy} (v : Seen C u) (ρ : Look C Γ) :
    Look.cons (u := u) v ρ .here = v := rfl

@[simp] theorem Look.cons_there {Γ : Ctx} {u t : LTy} (v : Seen C u) (ρ : Look C Γ)
    (j : Idx Γ t) : Look.cons (u := u) v ρ (.there j) = ρ j := rfl

theorem Look.set_same : {Γ : Ctx} → {t : LTy} → (ρ : Look C Γ) → (i : Idx Γ t) →
    (v : Seen C t) → Look.set ρ i v i = v
  | _ :: _, _, _, .here, _ => rfl
  | _ :: _, _, ρ, .there i, v => Look.set_same ρ.tail i v

theorem Look.set_other : {Γ : Ctx} → {t t' : LTy} → (ρ : Look C Γ) → (i : Idx Γ t) →
    (v : Seen C t) → (j : Idx Γ t') → j.toNat ≠ i.toNat → Look.set ρ i v j = ρ j
  | _ :: _, _, _, _, .here, _, .here, h => absurd rfl h
  | _ :: _, _, _, _, .here, _, .there _, _ => rfl
  | _ :: _, _, _, _, .there _, _, .here, _ => rfl
  | _ :: _, _, _, _, .there i, v, .there j, h =>
    Look.set_other _ i v j (fun h' => h (by simp only [Idx.toNat, h']))

/-! ## What the fragment knows, by position -/

namespace Frag

theorem get_push_here {Γ : Ctx} (t : LTy) (F : Frag Γ) (f : Fl) :
    (F.push t f).get .here = f := rfl

theorem get_push_there {Γ : Ctx} {t u : LTy} (F : Frag Γ) (f : Fl) (i : Idx Γ t) :
    (F.push u f).get (.there i) = F.get i := rfl

theorem get_set {Γ : Ctx} {t t' : LTy} (F : Frag Γ) (i : Idx Γ t) (f : Fl) (j : Idx Γ t') :
    (F.set i f).get j = if j.toNat = i.toNat ∧ i.toNat < F.fl.length then f else F.get j := by
  simp only [get, set, List.getD_eq_getElem?_getD, List.getElem?_set]
  by_cases h1 : i.toNat = j.toNat
  · by_cases h2 : i.toNat < F.fl.length
    · simp only [h1, ↓reduceIte] at h2 ⊢; simp only [h2, ↓reduceIte, Option.getD_some, and_self]
    · have : F.fl.length ≤ j.toNat := by omega
      simp only [h1, ↓reduceIte] at h2 ⊢
      simp only [h2, ↓reduceIte, Option.getD_none, and_false, not_false_eq_true, getElem?_neg]
  · simp only [h1, ↓reduceIte, Ne.symm h1, false_and]

theorem get_eq_dead {Γ : Ctx} {t : LTy} (F : Frag Γ) (i : Idx Γ t) (h : F.fl.length ≤ i.toNat) :
    F.get i = .dead := by
  simp only [get, List.getD_eq_getElem?_getD, List.getElem?_eq_none h, Option.getD_none]

theorem get_restrict {Γ Δ : Ctx} (h : Ext Γ Δ) (F : Frag Δ) {t : LTy} (i : Idx Γ t) :
    (F.restrict Γ).get i = F.get (i.ext h) := by
  have := h.length_eq
  simp only [get, restrict, List.getD_eq_getElem?_getD, List.getElem?_drop, Ext.toNat_idx]
  congr 2; omega

theorem get_meet {Γ : Ctx} (F G : Frag Γ) {t : LTy} (i : Idx Γ t) {g : Fl}
    (h : (F.meet G).get i = g) (hg : g ≠ .dead) : F.get i = g := by
  simp only [get, meet, List.getD_eq_getElem?_getD, List.getElem?_zipWith] at h ⊢
  cases h1 : F.fl[i.toNat]? <;> cases h2 : G.fl[i.toNat]? <;>
    simp_all only [ne_eq, Option.getD_none, getElem?_eq_none_iff, Nat.not_lt, Option.getD_some,
    not_true_eq_false]
  split at h <;> simp_all only [not_true_eq_false]

theorem meet_comm {Γ : Ctx} (F G : Frag Γ) : F.meet G = G.meet F := by
  simp only [meet, mk.injEq]
  rw [List.zipWith_comm]
  congr; funext f g
  split <;> split <;> simp_all only [not_true_eq_false]

theorem get_meet_right {Γ : Ctx} (F G : Frag Γ) {t : LTy} (i : Idx Γ t) {g : Fl}
    (h : (F.meet G).get i = g) (hg : g ≠ .dead) : G.get i = g :=
  get_meet G F i (meet_comm F G ▸ h) hg

theorem get_dropFragile {Γ : Ctx} (F : Frag Γ) {t : LTy} (i : Idx Γ t) {g : Fl}
    (h : F.dropFragile.get i = g) (hg : g ≠ .dead) : F.get i = g ∧ g ≠ .fragile := by
  simp only [get, dropFragile, List.getD_eq_getElem?_getD, List.getElem?_map] at h ⊢
  cases h1 : F.fl[i.toNat]? <;>
    simp_all only [ne_eq, Option.map_none, Option.map_some, Option.getD_none, Option.getD_some,
      getElem?_eq_none_iff, Nat.not_lt, true_and, not_true_eq_false]
  split at h <;> simp_all only [not_true_eq_false, not_false_eq_true, and_self]

end Frag

/-! ## The simulation relation -/

/-- The machine `m` represents the global state `σ` (its storage, ledger and
transaction; `σ.env` is not read) and the locals `ρ` of `Γ`, which a frame
based at `b` keeps at their levels, and of whose aliases the fragment knows
`F`.  A value local is represented by its cell outright (`ReprV` of the
value it holds), an alias by the slot of the path its reference names. -/
structure SimL (C : Contract) (L b : Nat) {Γ : Ctx} (F : Frag Γ) (σ : State C []) (ρ : Look C Γ)
    (m : Machine) : Prop where
  store : ReprStore C L m.store σ.storage
  vals : ∀ {p : PrimTy} (i : Idx Γ (.val p)), ReprV p (ρ i) (m.memAt (lvl b i))
  aliases : ∀ {R : RefTy} (i : Idx Γ (.alias R)), F.get i = .ok →
    ∃ r s, ρ i = some r ∧ m.memAt (lvl b i) = .slot s ∧
      PathSlot C true r s
  /-- `net(a)` is what `a`'s account lost, at every address but the
  contract's own. -/
  net : ∀ a : Fin W, a ≠ m.self → netAt σ.net a.1 = (m.bal₀ a : Int) - m.bal a
  /-- The contract's own entry is never moved. -/
  netSelf : netAt σ.net m.self = 0
  /-- The bound on the arrays is at most solc's. -/
  bound : L ≤ Lmax
  /-- A fragile alias: its cell holds the slot of a path that indexes an
  array, and that path is in bounds. -/
  fragile : ∀ {R : RefTy} (i : Idx Γ (.alias R)), F.get i = .fragile →
    ∃ r s, ρ i = some r ∧ m.memAt (lvl b i) = .slot s ∧
      PathSlot C false r s ∧
      ∃ sv, σ.storage.findLive r = some sv
  /-- `msg.sender`, `msg.value`, `block.timestamp`, `address(this)`. -/
  env : EnvSim σ.tx m

variable {L b : Nat} {Γ : Ctx} {F : Frag Γ} {σ : State C []} {ρ : Look C Γ}

namespace SimL

/-- `SimL` does not look at the stack. -/
theorem stack {m : Machine} (h : SimL C L b F σ ρ m) (st : List Word) :
    SimL C L b F σ ρ { m with stack := st } :=
  ⟨h.store, h.vals, h.aliases, h.net, h.netSelf, h.bound, h.fragile, h.env⟩

theorem push {m : Machine} (h : SimL C L b F σ ρ m) (w : Word) : SimL C L b F σ ρ (m.push w) :=
  h.stack _

/-- A payment booked: the ledger down at `x`, and the balances moved to match. -/
theorem book {m : Machine} (h : SimL C L b F σ ρ m) (x : PrimTy.uint.Denote) (y : Int) (bl bl₀ : Fin W → Nat)
    (hn : ∀ a : Fin W, a ≠ m.self → netAt (σ.pay x y).net a.1 = (bl₀ a : Int) - bl a)
    (hself : netAt (σ.pay x y).net m.self = 0) :
    SimL C L b F (σ.pay x y) ρ { m with bal := bl, bal₀ := bl₀ } :=
  ⟨h.store, h.vals, h.aliases, hn, hself, h.bound, h.fragile, h.env⟩

/-- Under a looser bound on the arrays. -/
theorem mono {m : Machine} {L' : Nat} (h : SimL C L b F σ ρ m) (hL : L ≤ L') (hL' : L' ≤ Lmax) :
    SimL C L' b F σ ρ m :=
  ⟨h.store.mono hL, h.vals, h.aliases, h.net, h.netSelf, hL', h.fragile, h.env⟩

/-- A storage write that lowers no array's length. -/
theorem store' {m : Machine} (h : SimL C L b F σ ρ m) {st' : WordStore}
    {stor : Solidity.Storage C} (hs : ReprStore C L st' stor)
    (hlen : ∀ x, LenSlot C x → m.store x ≤ st' x) :
    SimL C L b F { σ with storage := stor } ρ { m with store := st' } :=
  ⟨hs, h.vals, h.aliases, h.net, h.netSelf, h.bound, fun i hi => by
    obtain ⟨r, s, h1, h2, h3, h4⟩ := h.fragile i hi
    exact ⟨r, s, h1, h2, h3, live_mono h.store hs hlen h3 h4⟩,
    h.env⟩

/-- Forgetting what the fragment knew: every alias it still reads, it read
before, as the same kind.  The branches met (`Frag.meet`), the fragile
aliases forgotten (`Frag.dropFragile`). -/
theorem flags {m : Machine} {G : Frag Γ} (h : SimL C L b F σ ρ m)
    (hG : ∀ {R : RefTy} (i : Idx Γ (.alias R)) (g : Fl), G.get i = g → g ≠ .dead → F.get i = g) :
    SimL C L b G σ ρ m :=
  ⟨h.store, h.vals, fun i hi => h.aliases i (hG i _ hi (by decide)), h.net, h.netSelf, h.bound,
    fun i hi => h.fragile i (hG i _ hi (by decide)), h.env⟩

theorem meet {m : Machine} (G : Frag Γ) (h : SimL C L b F σ ρ m) :
    SimL C L b (F.meet G) σ ρ m :=
  h.flags fun i _ hg hd => Frag.get_meet F G i hg hd

/-- A storage write that may shrink an array (`pop`, `delete`): the fragile
aliases forgotten. -/
theorem storeDrop {m : Machine} (h : SimL C L b F σ ρ m) {st' : WordStore}
    {stor : Solidity.Storage C} (hs : ReprStore C L st' stor) :
    SimL C L b F.dropFragile { σ with storage := stor } ρ { m with store := st' } := by
  refine ⟨hs, h.vals, fun i hi => h.aliases i (Frag.get_dropFragile F i hi (by decide)).1,
    h.net, h.netSelf, h.bound, fun i hi => ?_, h.env⟩
  exact absurd rfl (Frag.get_dropFragile F i hi (by decide)).2

/-- A scope's end: its locals popped, the enclosing ones where they were. -/
theorem drop {Δ : Ctx} {G : Frag Δ} {ρ' : Look C Δ} {m : Machine} (hΓ : Ext Γ Δ)
    (h : SimL C L b G σ ρ' m) : SimL C L b (G.restrict Γ) σ (ρ'.drop hΓ) m := by
  refine ⟨h.store, fun i => ?_, fun i hi => ?_, h.net, h.netSelf, h.bound, fun i hi => ?_, h.env⟩
  · rw [← lvl_ext b hΓ]; exact h.vals (i.ext hΓ)
  · rw [Frag.get_restrict hΓ] at hi; rw [← lvl_ext b hΓ]; exact h.aliases (i.ext hΓ) hi
  · rw [Frag.get_restrict hΓ] at hi; rw [← lvl_ext b hΓ]; exact h.fragile (i.ext hΓ) hi

/-- The machine's memory changed above the frame's locals only. -/
theorem congrMem {m : Machine} {mem : Nat → Word} (h : SimL C L b F σ ρ m)
    (hm : ∀ l, b ≤ l → l < b + Γ.length → mem (cell l) = m.mem (cell l)) :
    SimL C L b F σ ρ { m with mem := mem } := by
  have e : ∀ {t : LTy} (i : Idx Γ t), ({ m with mem := mem } : Machine).memAt (lvl b i) =
      m.memAt (lvl b i) := fun i => hm _ (le_lvl b i) (lvl_lt b i)
  refine ⟨h.store, fun i => ?_, fun i hi => ?_, h.net, h.netSelf, h.bound, fun i hi => ?_, h.env⟩
  · rw [e]; exact h.vals i
  · rw [e]; exact h.aliases i hi
  · rw [e]; exact h.fragile i hi

/-- `SimL` reads the locals pointwise. -/
theorem congrLook {ρ' : Look C Γ} {m : Machine} (h : SimL C L b F σ ρ m)
    (hρ : ∀ {t : LTy} (i : Idx Γ t), ρ' i = ρ i) : SimL C L b F σ ρ' m := by
  refine ⟨h.store, fun i => ?_, fun i hi => ?_, h.net, h.netSelf, h.bound, fun i hi => ?_, h.env⟩
  · rw [hρ]; exact h.vals i
  · rw [hρ]; exact h.aliases i hi
  · rw [hρ]; exact h.fragile i hi

/-! ### Declarations: `TEnv`'s pair -/

/-- `uint x = e;`: the local pushed, its value in the cell of the next level. -/
theorem consVal {m : Machine} (h : SimL C L b F σ ρ m) {p : PrimTy} {v : p.Denote} {w : Word}
    (hv : ReprV p v w) :
    SimL C L b (F.push (.val p) .ok) σ (ρ.cons (u := .val p) v)
      { m with mem := upd m.mem (cell (b + Γ.length)) w } := by
  have e : ∀ {t : LTy} (i : Idx Γ t),
      ({ m with mem := upd m.mem (cell (b + Γ.length)) w } : Machine).memAt (lvl b i) =
        m.memAt (lvl b i) := fun i => by
    rw [memAt_upd, if_neg (Nat.ne_of_lt (lvl_lt b i))]
  refine ⟨h.store, fun i => ?_, fun i hi => ?_, h.net, h.netSelf, h.bound, fun i hi => ?_, h.env⟩
  · cases i with
    | here => rw [lvl_here, memAt_upd, if_pos rfl]; exact hv
    | there j => rw [lvl_there, e]; exact h.vals j
  · cases i with
    | there j => rw [lvl_there, e]; exact h.aliases j hi
  · cases i with
    | there j => rw [lvl_there, e]; exact h.fragile j hi

/-- `Person storage p = alice;`: the local pushed, the slot in its cell. -/
theorem consAlias {m : Machine} (h : SimL C L b F σ ρ m) {R : RefTy}
    {r : Solidity.SRef C (.ref R)} {s : Slot}
    (hp : PathSlot C true r s) :
    SimL C L b (F.push (.alias R) .ok) σ (ρ.cons (u := .alias R) (some r))
      { m with mem := upd m.mem (cell (b + Γ.length)) (.slot s) } := by
  have e : ∀ {t : LTy} (i : Idx Γ t),
      ({ m with mem := upd m.mem (cell (b + Γ.length)) (.slot s) } : Machine).memAt (lvl b i) =
        m.memAt (lvl b i) := fun i => by
    rw [memAt_upd, if_neg (Nat.ne_of_lt (lvl_lt b i))]
  refine ⟨h.store, fun i => ?_, fun i hi => ?_, h.net, h.netSelf, h.bound, fun i hi => ?_, h.env⟩
  · cases i with
    | there j => rw [lvl_there, e]; exact h.vals j
  · cases i with
    | here => exact ⟨r, s, rfl, by rw [lvl_here, memAt_upd, if_pos rfl], hp⟩
    | there j => rw [lvl_there, e]; exact h.aliases j hi
  · cases i with
    | here => cases hi
    | there j => rw [lvl_there, e]; exact h.fragile j hi

/-- `Person storage p = persons[i];`: a fragile alias pushed. -/
theorem consFragile {m : Machine} (h : SimL C L b F σ ρ m) {R : RefTy}
    {r : Solidity.SRef C (.ref R)} {s : Slot}
    (hp : PathSlot C false r s)
    (hlive : ∃ sv, σ.storage.findLive r = some sv) :
    SimL C L b (F.push (.alias R) .fragile) σ (ρ.cons (u := .alias R) (some r))
      { m with mem := upd m.mem (cell (b + Γ.length)) (.slot s) } := by
  have e : ∀ {t : LTy} (i : Idx Γ t),
      ({ m with mem := upd m.mem (cell (b + Γ.length)) (.slot s) } : Machine).memAt (lvl b i) =
        m.memAt (lvl b i) := fun i => by
    rw [memAt_upd, if_neg (Nat.ne_of_lt (lvl_lt b i))]
  refine ⟨h.store, fun i => ?_, fun i hi => ?_, h.net, h.netSelf, h.bound, fun i hi => ?_, h.env⟩
  · cases i with
    | there j => rw [lvl_there, e]; exact h.vals j
  · cases i with
    | here => cases hi
    | there j => rw [lvl_there, e]; exact h.aliases j hi
  · cases i with
    | here => exact ⟨r, s, rfl, by rw [lvl_here, memAt_upd, if_pos rfl], hp, hlive⟩
    | there j => rw [lvl_there, e]; exact h.fragile j hi

/-- `Person storage p;`: an alias pushed that the fragment may not read
(`unset`), its cell left. -/
theorem consDead {m : Machine} (h : SimL C L b F σ ρ m) (R : RefTy) (v : Seen C (.alias R)) :
    SimL C L b (F.push (.alias R) .dead) σ (ρ.cons (u := .alias R) v) m := by
  refine ⟨h.store, fun i => ?_, fun i hi => ?_, h.net, h.netSelf, h.bound, fun i hi => ?_, h.env⟩
  · cases i with
    | there j => rw [lvl_there]; exact h.vals j
  · cases i with
    | here => cases hi
    | there j => rw [lvl_there]; exact h.aliases j hi
  · cases i with
    | here => cases hi
    | there j => rw [lvl_there]; exact h.fragile j hi

/-! ### Assignments -/

/-- `x = e;`: the local's value and its cell change together. -/
theorem setVal {m : Machine} (h : SimL C L b F σ ρ m) {p : PrimTy} (i : Idx Γ (.val p))
    {v : p.Denote} {w : Word} (hv : ReprV p v w) :
    SimL C L b F σ (ρ.set i v) { m with mem := upd m.mem (cellOf b i) w } := by
  have e : ∀ {t : LTy} (j : Idx Γ t),
      ({ m with mem := upd m.mem (cellOf b i) w } : Machine).memAt (lvl b j) =
        if j.toNat = i.toNat then w else m.memAt (lvl b j) := fun j => by
    simp only [memAt_upd, lvl_eq_iff]
  refine ⟨h.store, fun j => ?_, fun j hj => ?_, h.net, h.netSelf, h.bound, fun j hj => ?_, h.env⟩
  · rw [e]
    by_cases hji : j.toNat = i.toNat
    · cases Idx.ty_eq j i hji
      cases Idx.toNat_inj j i hji
      rw [if_pos rfl, Look.set_same]; exact hv
    · rw [if_neg hji, Look.set_other ρ i v j hji]; exact h.vals j
  · have hji : ¬ j.toNat = i.toNat := fun hh => by cases Idx.ty_eq j i hh
    rw [e, if_neg hji, Look.set_other ρ i v j hji]; exact h.aliases j hj
  · have hji : ¬ j.toNat = i.toNat := fun hh => by cases Idx.ty_eq j i hh
    rw [e, if_neg hji, Look.set_other ρ i v j hji]; exact h.fragile j hj

/-- `p = alice;`: an alias rebound to a path that indexes no array. -/
theorem setAlias {m : Machine} (h : SimL C L b F σ ρ m) {R : RefTy} (i : Idx Γ (.alias R))
    {r : Solidity.SRef C (.ref R)} {s : Slot}
    (hp : PathSlot C true r s) :
    SimL C L b (F.set i .ok) σ (ρ.set i (some r))
      { m with mem := upd m.mem (cellOf b i) (.slot s) } := by
  have e : ∀ {t : LTy} (j : Idx Γ t),
      ({ m with mem := upd m.mem (cellOf b i) (.slot s) } : Machine).memAt (lvl b j) =
        if j.toNat = i.toNat then .slot s else m.memAt (lvl b j) := fun j => by
    simp only [memAt_upd, lvl_eq_iff]
  refine ⟨h.store, fun j => ?_, fun j hj => ?_, h.net, h.netSelf, h.bound, fun j hj => ?_, h.env⟩
  · have hji : ¬ j.toNat = i.toNat := fun hh => by cases Idx.ty_eq j i hh
    rw [e, if_neg hji, Look.set_other ρ i _ j hji]; exact h.vals j
  · rw [Frag.get_set] at hj
    by_cases hji : j.toNat = i.toNat
    · cases Idx.ty_eq j i hji
      cases Idx.toNat_inj j i hji
      split at hj
      · rw [e, if_pos rfl, Look.set_same]; exact ⟨r, s, rfl, rfl, hp⟩
      · rw [Frag.get_eq_dead F _ (by omega)] at hj; cases hj
    · simp only [hji, false_and, ↓reduceIte] at hj
      rw [e, if_neg hji, Look.set_other ρ i _ j hji]; exact h.aliases j hj
  · rw [Frag.get_set] at hj
    by_cases hji : j.toNat = i.toNat
    · simp only [hji, true_and] at hj
      split at hj
      · cases hj
      · rw [Frag.get_eq_dead F j (by omega)] at hj; cases hj
    · simp only [hji, false_and, ↓reduceIte] at hj
      rw [e, if_neg hji, Look.set_other ρ i _ j hji]; exact h.fragile j hj

/-- `p = persons[i];`: an alias rebound through an index, fragile. -/
theorem setFragile {m : Machine} (h : SimL C L b F σ ρ m) {R : RefTy} (i : Idx Γ (.alias R))
    {r : Solidity.SRef C (.ref R)} {s : Slot}
    (hp : PathSlot C false r s)
    (hlive : ∃ sv, σ.storage.findLive r = some sv) :
    SimL C L b (F.set i .fragile) σ (ρ.set i (some r))
      { m with mem := upd m.mem (cellOf b i) (.slot s) } := by
  have e : ∀ {t : LTy} (j : Idx Γ t),
      ({ m with mem := upd m.mem (cellOf b i) (.slot s) } : Machine).memAt (lvl b j) =
        if j.toNat = i.toNat then .slot s else m.memAt (lvl b j) := fun j => by
    simp only [memAt_upd, lvl_eq_iff]
  refine ⟨h.store, fun j => ?_, fun j hj => ?_, h.net, h.netSelf, h.bound, fun j hj => ?_, h.env⟩
  · have hji : ¬ j.toNat = i.toNat := fun hh => by cases Idx.ty_eq j i hh
    rw [e, if_neg hji, Look.set_other ρ i _ j hji]; exact h.vals j
  · rw [Frag.get_set] at hj
    by_cases hji : j.toNat = i.toNat
    · simp only [hji, true_and] at hj
      split at hj
      · cases hj
      · rw [Frag.get_eq_dead F j (by omega)] at hj; cases hj
    · simp only [hji, false_and, ↓reduceIte] at hj
      rw [e, if_neg hji, Look.set_other ρ i _ j hji]; exact h.aliases j hj
  · rw [Frag.get_set] at hj
    by_cases hji : j.toNat = i.toNat
    · cases Idx.ty_eq j i hji
      cases Idx.toNat_inj j i hji
      split at hj
      · rw [e, if_pos rfl, Look.set_same]; exact ⟨r, s, rfl, rfl, hp, hlive⟩
      · rw [Frag.get_eq_dead F _ (by omega)] at hj; cases hj
    · simp only [hji, false_and, ↓reduceIte] at hj
      rw [e, if_neg hji, Look.set_other ρ i _ j hji]; exact h.fragile j hj

/-! ### A call's frame -/

/-- **Entering a call**: the callee's frame `Δ` (its parameters, then its
return variable: values only) at base `b'`, every local readable, its
values in their cells; the caller's storage, ledger and transaction. -/
theorem enter {m : Machine} {Δ : Ctx} (b' : Nat) (h : SimL C L b F σ ρ m) (ρ' : Look C Δ)
    (hv : ∀ {p : PrimTy} (i : Idx Δ (.val p)), ReprV p (ρ' i) (m.memAt (lvl b' i)))
    (hal : ∀ {R : RefTy}, Idx Δ (.alias R) → False) :
    SimL C L b' (Frag.init Δ) σ ρ' m :=
  ⟨h.store, hv, fun i _ => (hal i).elim, h.net, h.netSelf, h.bound, fun i _ => (hal i).elim, h.env⟩

/-- **Back from a call**: the machine and state the callee left (`h'`), the
caller's locals where they were (the callee stored above them,
`storesFrom_callFrame`), and its fragile aliases still in bounds, the callee
having lowered no array's length.  A callee that may (`Stmt.shrinks`) is
`returnDrop`. -/
theorem «return» {m m' : Machine} {Δ : Ctx} {b' : Nat} {G : Frag Δ} {σ' : State C []}
    {ρ' : Look C Δ} (h : SimL C L b F σ ρ m) (h' : SimL C L b' G σ' ρ' m')
    (hmem : ∀ l, l < b + Γ.length → m'.memAt l = m.memAt l)
    (hlen : ∀ x, LenSlot C x → m.store x ≤ m'.store x) :
    SimL C L b F σ' ρ m' := by
  have e : ∀ {t : LTy} (i : Idx Γ t), m'.memAt (lvl b i) = m.memAt (lvl b i) :=
    fun i => hmem _ (lvl_lt b i)
  refine ⟨h'.store, fun i => ?_, fun i hi => ?_, h'.net, h'.netSelf, h'.bound, fun i hi => ?_,
    h'.env⟩
  · rw [e]; exact h.vals i
  · rw [e]; exact h.aliases i hi
  · obtain ⟨r, s, h1, h2, h3, h4⟩ := h.fragile i hi
    rw [e]
    exact ⟨r, s, h1, h2, h3, live_mono h.store h'.store hlen h3 h4⟩

/-- Back from a call that may have shrunk an array: the caller's fragile
aliases forgotten. -/
theorem returnDrop {m m' : Machine} {Δ : Ctx} {b' : Nat} {G : Frag Δ} {σ' : State C []}
    {ρ' : Look C Δ} (h : SimL C L b F σ ρ m) (h' : SimL C L b' G σ' ρ' m')
    (hmem : ∀ l, l < b + Γ.length → m'.memAt l = m.memAt l) :
    SimL C L b F.dropFragile σ' ρ m' := by
  have e : ∀ {t : LTy} (i : Idx Γ t), m'.memAt (lvl b i) = m.memAt (lvl b i) :=
    fun i => hmem _ (lvl_lt b i)
  refine ⟨h'.store, fun i => ?_, fun i hi => ?_, h'.net, h'.netSelf, h'.bound, fun i hi => ?_,
    h'.env⟩
  · rw [e]; exact h.vals i
  · rw [e]; exact h.aliases i (Frag.get_dropFragile F i hi (by decide)).1
  · exact absurd rfl (Frag.get_dropFragile F i hi (by decide)).2

end SimL

/-! ## The locals of a typed state -/

/-- A typed local, as the simulation reads it. -/
def see {H : HTy} : (t : LTy) → t.TDenote C H → Seen C t
  | .val _, v => v
  | .alias _, a => a
  | .mem _, _ | .old, _ | .oldNet, _ | .kint, _ => ()

/-- The locals of a typed state, as the simulation reads them. -/
def Look.ofTEnv {H : HTy} {Γ : Ctx} (e : TEnv C H Γ) : Look C Γ :=
  fun {t} i => see t (TEnv.get i e)

theorem Look.ofTEnv_alias {H : HTy} {Γ : Ctx} {R : RefTy} (e : TEnv C H Γ)
    (i : Idx Γ (.alias R)) : Look.ofTEnv e i = TEnv.get i e := rfl

/-- A local declared: the pair's head. -/
theorem Look.ofTEnv_cons {H : HTy} {Γ : Ctx} {u : LTy} (v : u.TDenote C H) (e : TEnv C H Γ)
    {t : LTy} (i : Idx (u :: Γ) t) :
    Look.ofTEnv (Γ := u :: Γ) (v, e) i = Look.cons (see u v) (Look.ofTEnv e) i := by
  cases i <;> rfl

/-- A local set. -/
theorem Look.ofTEnv_set {H : HTy} {Γ : Ctx} {u : LTy} (i : Idx Γ u) (v : u.TDenote C H)
    (e : TEnv C H Γ) {t : LTy} (j : Idx Γ t) :
    Look.ofTEnv (TEnv.set i v e) j = Look.set (Look.ofTEnv e) i (see u v) j := by
  induction i with
  | here => cases j <;> rfl
  | there i ih =>
    cases j with
    | here => rfl
    | there j => exact ih v e.2 j

/-- A scope's locals popped. -/
theorem Look.ofTEnv_drop {H : HTy} {Γ Δ : Ctx} (h : Ext Γ Δ) (e : TEnv C H Δ) {t : LTy}
    (i : Idx Γ t) : Look.ofTEnv (TEnv.drop h e) i = Look.drop h (Look.ofTEnv e) i := by
  induction h with
  | refl => rfl
  | push h ih => exact ih e.2

theorem see_wk {H H' : HTy} (x : H <+: H') :
    (t : LTy) → (v : t.TDenote C H) → see t (Solidity.LTy.TDenote.wk x t v) = see t v
  | .val _, _ | .alias _, _ | .mem _, _ | .old, _ | .oldNet, _ | .kint, _ => rfl

/-- The locals over a grown heap read as they did. -/
theorem Look.ofTEnv_wk {H H' : HTy} {Γ : Ctx} (x : H <+: H') (e : TEnv C H Γ) {t : LTy}
    (i : Idx Γ t) : Look.ofTEnv (TEnv.wk x Γ e) i = Look.ofTEnv e i := by
  simp only [Look.ofTEnv, TEnv.get_wk, see_wk]

/-! ## The simulation of a typed state -/

/-- **The machine represents the typed state**: `SimL` of its global part
(`State.glob`: its storage, ledger and transaction) and of its locals as
the simulation reads them (`Look.ofTEnv`). -/
abbrev Sim (C : Contract) (L b : Nat) {Γ : Ctx} (F : Frag Γ) (σ : State C Γ) (m : Machine) :
    Prop :=
  SimL C L b F σ.glob (Look.ofTEnv σ.env) m


/-! ## A frame's cells -/

/-- One instruction other than a store to `x` leaves `x`'s cell. -/
theorem step_mem {i : Instr} {m m' : Machine} {k : Nat} {x : Nat} (hi : i ≠ .mstore x)
    (h : i.step m = .ok m' k) : m'.mem x = m.mem x := by
  cases i <;> simp only [Instr.step, Machine.next] at h <;>
    (try split at h) <;> (try split at h) <;> (try split at h) <;>
    (try simp only [Out.ok.injEq, reduceCtorEq] at h) <;>
    (try obtain ⟨rfl, -⟩ := h) <;> try rfl
  exact upd_other _ _ fun e => hi (e ▸ rfl)

/-- Code with no store to `x` leaves `x`'s cell. -/
theorem exec_mem {x : Nat} : ∀ {c : List Instr} {k k' : Nat} {m m' : Machine},
    Instr.mstore x ∉ c → exec c k m = .ok m' k' → m'.mem x = m.mem x
  | [], _, _, _, _, _, h => by simp only [exec_nil, Out.ok.injEq] at h; rw [h.1]
  | i :: c, k + 1, _, _, _, hx, h => exec_mem (fun hc => hx (List.mem_cons_of_mem _ hc)) h
  | i :: c, 0, _, m, _, hx, h => by
    rw [exec_cons_zero] at h
    cases hs : i.step m with
    | ok m₁ k₁ =>
      rw [hs, Out.ok_bind] at h
      rw [exec_mem (fun hc => hx (List.mem_cons_of_mem _ hc)) h,
        step_mem (fun he => hx (he ▸ List.mem_cons_self ..)) hs]
    | revert => rw [hs] at h; cases h
    | fault => rw [hs] at h; cases h

/-! ### Which cells the compiled code stores to -/

/-- Whether an instruction stores to a memory cell. -/
def _root_.Solidity.Evm.Instr.isStore : Instr → Bool
  | .mstore _ => true
  | _ => false

/-- Code that stores to no cell: an expression's, the guards'. -/
abbrev NoStore (c : List Instr) : Prop := c.all (fun i => !i.isStore) = true

theorem noStore_append {c₁ c₂ : List Instr} : NoStore (c₁ ++ c₂) ↔ NoStore c₁ ∧ NoStore c₂ := by
  simp only [NoStore, List.all_append, Bool.and_eq_true]

theorem NoStore.not_mem {c : List Instr} (h : NoStore c) (x : Nat) : Instr.mstore x ∉ c := by
  intro hx
  have := List.all_eq_true.1 h _ hx
  simp only [Instr.isStore, Bool.not_true, Bool.false_eq_true] at this

set_option hygiene false in
/-- One piece of code that stores nowhere: a hypothesis, a guard, or a
literal list (by `rfl`, last: it would unfold `expLoop 255`). -/
local macro "no_store_piece" : tactic =>
  `(tactic| first
    | assumption
    | exact (noStore_leaves _).1
    | exact (noStore_leaves _).2.1
    | exact (noStore_leaves _).2.2
    | exact noStore_pushSlotCode _
    | exact noStore_elemSlot _
    | exact noStore_fixedSlot _
    | exact noStore_binTail _ _
    | exact noStore_bumpCode _ _
    | rfl)

set_option hygiene false in
/-- Split code at its `++` and close each piece. -/
local macro "no_store" : tactic =>
  `(tactic| (simp only [noStore_append]; and_intros <;> no_store_piece))

theorem noStore_flatMap {α : Type} {f : α → List Instr} (h : ∀ a, NoStore (f a)) :
    ∀ os : List α, NoStore (os.flatMap f)
  | [] => rfl
  | o :: os => by
    have := h o; have := noStore_flatMap h os
    rw [List.flatMap_cons]; no_store

theorem noStore_addRep : ∀ z, NoStore (addRep z)
  | 0 => rfl
  | z + 1 => by have := noStore_addRep z; rw [addRep]; no_store

theorem noStore_expLoop : ∀ k, NoStore (expLoop k)
  | 0 => rfl
  | k + 1 => by have := noStore_expLoop k; rw [expLoop]; no_store

theorem noStore_expCode : NoStore expCode := by
  -- `expLoop 255` held opaque: unfolding it unfolds all 255 rounds
  have := noStore_expLoop 255
  unfold expCode expNonzero expGeneral
  generalize expLoop 255 = E at this ⊢
  no_store

theorem noStore_binTail (p : PrimTy) (op : BinOp) : NoStore (binTail p op) := by
  cases p <;> cases op <;> simp only [binTail, uTail, sTail] <;>
    first | (guard_target =ₛ NoStore expCode; exact noStore_expCode) | rfl

theorem noStore_elemSlot (z : Nat) : NoStore (elemSlot z) := by
  have := noStore_addRep z; simp only [elemSlot]; no_store

theorem noStore_fixedSlot (z : Nat) : NoStore (fixedSlot z) := by
  have := noStore_addRep z; simp only [fixedSlot]; no_store

theorem noStore_bumpCode (p : PrimTy) (op : IncDec) : NoStore (bumpCode p op) := by
  have := noStore_binTail p op.binOp
  unfold bumpCode; split <;> no_store

theorem noStore_pushSlotCode (z : Nat) : NoStore (pushSlotCode z) := by
  have := noStore_elemSlot z; simp only [pushSlotCode, assertTop]; no_store

theorem noStore_leaves (os : List Nat) :
    NoStore (zeroCode os) ∧ NoStore (loadLeaves os) ∧ NoStore (storeLeaves os) :=
  ⟨noStore_flatMap (fun _ => rfl) os, noStore_flatMap (fun _ => rfl) os,
    noStore_flatMap (fun _ => rfl) os⟩

theorem noStore_compileSimple (b : Nat) {Γ : Ctx} {p : PrimTy} (s : Solidity.Simple C Γ p) :
    NoStore (compileSimple b s) := by
  cases s with
  | env k _ => cases k <;> rfl
  | _ => rfl

mutual
theorem noStore_compileSPath (b : Nat) {Γ : Ctx} : {T : Ty} →
    (q : Solidity.SPath C Γ T) → NoStore (compileSPath b q)
  | _, .alias _ => rfl
  | _, .loc l => by simp only [compileSPath]; exact noStore_compileLoc b l
theorem noStore_compileLoc (b : Nat) {Γ : Ctx} : {T : Ty} →
    (l : Solidity.Loc C Γ T) → NoStore (compileLoc b l)
  | _, .root _ _ => rfl
  | _, .field q _ _ => by
    have := noStore_compileSPath b q
    simp only [compileLoc]; no_store
  | _, .index .map q i => by
    have := noStore_compileSPath b q; have := noStore_compileVal b i
    simp only [compileLoc]; no_store
  | _, @Solidity.Loc.index _ _ _ _ E (.arr .dyn) q i => by
    have := noStore_compileSPath b q; have := noStore_compileVal b i
    simp only [compileLoc, boundsCheck, assertTop]; no_store
  | _, @Solidity.Loc.index _ _ _ _ E (@IndexTy.arr _ _ (@ArrTy.fixed _ n)) q i => by
    have := noStore_compileSPath b q; have := noStore_compileVal b i
    simp only [compileLoc, fixedCheck, assertTop]; no_store
theorem noStore_compileVal (b : Nat) {Γ : Ctx} : {p : PrimTy} →
    (v : Solidity.Val C Γ p) → NoStore (compileVal b v)
  | _, .simple s => by simp only [compileVal]; exact noStore_compileSimple b s
  | _, .read l => by
    have := noStore_compileLoc b l
    simp only [compileVal]; no_store
  | _, @Solidity.Val.binop _ _ p _ op _ _ x y => by
    have := noStore_compileVal b x
    have := noStore_compileVal b y
    have := noStore_binTail p op
    cases op <;> simp only [compileVal] <;> no_store
  | _, .unop op _ _ x => by
    have := noStore_compileVal b x
    cases op <;> simp only [compileVal, negCode, assertTop] <;> no_store
  | _, .ternary c x y => by
    have := noStore_compileVal b c; have := noStore_compileVal b x
    have := noStore_compileVal b y
    simp only [compileVal]; no_store
  | _, .len q _ => by
    have := noStore_compileSPath b q
    simp only [compileVal]; no_store
  | _, .readMem _ => rfl
  | _, .mlen .. => rfl
  | _, .modular .. => rfl
  | _, .hash .. => rfl
end

/-- Code that stores to no level below `n`. -/
def StoresFrom (n : Nat) (c : List Instr) : Prop := ∀ l, l < n → Instr.mstore (cell l) ∉ c

theorem storesFrom_append {n : Nat} {c₁ c₂ : List Instr} :
    StoresFrom n (c₁ ++ c₂) ↔ StoresFrom n c₁ ∧ StoresFrom n c₂ := by
  simp only [StoresFrom, List.mem_append, not_or]
  exact ⟨fun h => ⟨fun l hl => (h l hl).1, fun l hl => (h l hl).2⟩,
    fun h l hl => ⟨h.1 l hl, h.2 l hl⟩⟩

theorem StoresFrom.mono {n n' : Nat} {c : List Instr} (h : StoresFrom n c) (hn : n' ≤ n) :
    StoresFrom n' c := fun l hl => h l (Nat.lt_of_lt_of_le hl hn)

theorem NoStore.storesFrom {c : List Instr} (h : NoStore c) (n : Nat) : StoresFrom n c :=
  fun l _ => h.not_mem (cell l)

theorem storesFrom_store {n l : Nat} (h : n ≤ l) : StoresFrom n [.mstore (cell l)] := by
  intro l' hl' hm
  simp only [List.mem_singleton, Instr.mstore.injEq] at hm
  have := cell_inj hm; omega

/-- A run of such code keeps every cell below `n`. -/
theorem StoresFrom.exec {n : Nat} {c : List Instr} (h : StoresFrom n c) {k k' : Nat}
    {m m' : Machine} (hr : exec c k m = .ok m' k') : ∀ l, l < n → m'.memAt l = m.memAt l :=
  fun l hl => exec_mem (h l hl) hr

set_option hygiene false in
/-- Split code at its `++` and close each piece: storing nowhere, a store
at a level the hypotheses or `omega` bound, or a hypothesis. -/
local macro "stores_from" : tactic =>
  `(tactic| (simp only [storesFrom_append]; and_intros <;>
    first
    | assumption
    | exact NoStore.storesFrom (by no_store_piece) _
    | exact storesFrom_store (by first | omega | exact le_lvl _ _)))

theorem storesFrom_argsCode (b : Nat) {Γ : Ctx} : {ps : Ctx} →
    (args : Solidity.Args C Γ ps) → StoresFrom (b + Γ.length) (argsCode b args)
  | _, .nil => fun _ _ h => nomatch h
  | _, .snoc as _ _ e => by
    have := storesFrom_argsCode b as; have := noStore_compileVal b e
    simp only [argsCode]; stores_from
  | _, .snocStorage .. | _, .snocMemory .. => fun _ _ h => nomatch h

theorem storesFrom_retEnterCode (b : Nat) {Γ : Ctx} (ps : Ctx) {rs Γ' : Ctx}
    (ret : Solidity.CallRet Γ rs Γ') :
    StoresFrom (b + Γ.length) (retEnterCode b ps ret) := by
  cases ret with
  | val =>
    show StoresFrom _ ([.push w[0]] ++ [.mstore _])
    stores_from
  | _ => exact fun _ _ h => nomatch h

theorem storesFrom_retLeaveCode (b : Nat) {Γ : Ctx} (ps : Ctx) {rs Γ' : Ctx}
    (ret : Solidity.CallRet Γ rs Γ') : StoresFrom b (retLeaveCode b ps ret) := by
  cases ret with
  | val _ _ res =>
    cases res with
    | some y =>
      show StoresFrom _ ([.mload _] ++ [.mstore _])
      stores_from
    | none => exact fun _ _ h => nomatch h
  | _ => exact fun _ _ h => nomatch h

theorem noStore_pushCode (b : Nat) {Γ : Ctx} {E : Ty} (v : Option (Solidity.Src C Γ E))
    (q : Solidity.SPath C Γ (.array E)) : NoStore (pushCode b v q) := by
  have := noStore_compileSPath b q
  have := noStore_pushSlotCode 1
  rcases v with _ | (v | q' | mp | shape)
  · simp only [pushCode]; no_store
  · have := noStore_compileVal b v
    simp only [pushCode]; no_store
  · have := noStore_compileSPath b q'
    simp only [pushCode]; no_store
  · rfl
  · rfl

theorem storesFrom_opLocCode (b n : Nat) {Γ : Ctx} {p : PrimTy} (l : Solidity.OpLoc C Γ p)
    (onLocal : Nat → List Instr) (onLoc : Solidity.Loc C Γ (.prim p) → List Instr)
    (h₁ : ∀ {t : LTy} (i : Idx Γ t), StoresFrom n (onLocal (cellOf b i)))
    (h₂ : ∀ l, StoresFrom n (onLoc l)) : StoresFrom n (opLocCode b l onLocal onLoc) := by
  cases l <;> simp only [opLocCode] <;> first | exact h₁ _ | exact h₂ _ | exact fun _ _ h => nomatch h

mutual
/-- Code compiled at base `b` stores to no level below `b`. -/
theorem storesFrom_compileStmt (b : Nat) {Γ Γ' : Ctx} :
    (s : Solidity.Stmt C Γ Γ') → StoresFrom b (compileStmt b s)
  | .assign l (.val v) => by
    have := noStore_compileVal b v; have := noStore_compileLoc b l
    simp only [compileStmt, assignCode]; stores_from
  | .assign l (.copy q _) => by
    have := noStore_compileSPath b q; have := noStore_compileLoc b l
    simp only [compileStmt, assignCode]; stores_from
  | .assign _ (.copyMem _) | .assign _ (.fixedCopy ..) => fun _ _ h => nomatch h
  | .rebind i (.path q) => by
    have := noStore_compileSPath b q
    simp only [compileStmt]; stores_from
  | .rebind _ (.push ..) => fun _ _ h => nomatch h
  | .assignLocal i r => by
    have := noStore_compileVal b r
    simp only [compileStmt]; stores_from
  | .declLocal _ _ none => by
    show StoresFrom _ ([.push w[0]] ++ [.mstore _])
    stores_from
  | .declLocal _ _ (some e) => by
    have := noStore_compileVal b e
    simp only [compileStmt]; stores_from
  | .declStorage _ _ none => fun _ _ h => nomatch h
  | .declStorage _ _ (some (.path q)) => by
    have := noStore_compileSPath b q
    simp only [compileStmt]; stores_from
  | .declStorage _ _ (some (.push ..)) => fun _ _ h => nomatch h
  | @Solidity.Stmt.opAssign _ _ p op _ _ l r => by
    have := noStore_compileVal b r; have := noStore_binTail p op
    simp only [compileStmt]
    apply storesFrom_opLocCode
    · intro _ i; stores_from
    · intro l; have := noStore_compileLoc b l; stores_from
  | @Solidity.Stmt.incDec _ _ p op _ l => by
    have := noStore_binTail p op.binOp
    simp only [compileStmt]
    apply storesFrom_opLocCode
    · intro _ i; stores_from
    · intro l; have := noStore_compileLoc b l; stores_from
  | @Solidity.Stmt.assignIncDec _ _ p i op _ l _ => by
    have := noStore_bumpCode p op
    simp only [compileStmt]
    apply storesFrom_opLocCode
    · intro _ j
      show StoresFrom _ ([.mload _] ++ bumpCode _ _ ++ ([.mstore _] ++ [.mstore _]))
      stores_from
    · intro l
      have := noStore_compileLoc b l
      show StoresFrom _ (compileLoc b l ++ [.dup 1, .sload] ++ bumpCode _ _ ++
        ([.dup 3, .sstore, .swap 1, .pop] ++ [.mstore _]))
      stores_from
  | .push q v _ => (noStore_pushCode b v q).storesFrom b
  | .pop q => by
    have := noStore_compileSPath b q
    simp only [compileStmt, popCode, assertTop]; stores_from
  | .transfer r a => by
    have := noStore_compileVal b r; have := noStore_compileVal b a
    simp only [compileStmt, assertTop]; stores_from
  | .send .. => fun _ _ h => nomatch h
  | .declMem .. => fun _ _ h => nomatch h
  | .rebindMem .. => fun _ _ h => nomatch h
  | .assignFromMem .. => fun _ _ h => nomatch h
  | .assignMem .. => fun _ _ h => nomatch h
  | @Solidity.Stmt.delete _ _ T l => by
    have := noStore_compileLoc b l
    simp only [compileStmt]; stores_from
  | .deleteMem .. => fun _ _ h => nomatch h
  | .assignNew .. => fun _ _ h => nomatch h
  | .ite c t e => by
    have := noStore_compileVal b c
    have := storesFrom_compileProg b t; have := storesFrom_compileProg b e
    simp only [compileStmt]; stores_from
  | .require c => by
    have := noStore_compileVal b c
    simp only [compileStmt, assertTop]; stores_from
  | .assert c => by
    have := noStore_compileVal b c
    simp only [compileStmt, assertTop]; stores_from
  | .revert => NoStore.storesFrom rfl _
  | .assumeFalse => NoStore.storesFrom rfl _
  | @Solidity.Stmt.call _ Γ _ ps _ _ _ args ret body => by
    have := (storesFrom_argsCode b args).mono (Nat.le_add_right b Γ.length)
    have := (storesFrom_retEnterCode b ps ret).mono (Nat.le_add_right b Γ.length)
    have := (storesFrom_compileProg (b + Γ.length) body).mono (Nat.le_add_right b Γ.length)
    have := storesFrom_retLeaveCode b ps ret
    simp only [compileStmt]; stores_from
  | .tryCall .. => fun _ _ h => nomatch h
  | .loop .. => fun _ _ h => nomatch h
  | .assignLocalPush .. => fun _ _ h => nomatch h
  | .pushOpAssign .. => fun _ _ h => nomatch h
  | .pushIncDec .. => fun _ _ h => nomatch h
  | .callReceiver .. => fun _ _ h => nomatch h
  | .callReceiverPush .. => fun _ _ h => nomatch h
  | .callRec .. => fun _ _ h => nomatch h
  | .revertData .. => fun _ _ h => nomatch h
  | .catchData .. => fun _ _ h => nomatch h
  | .block body => by simp only [compileStmt]; exact storesFrom_compileProg b body
/-- A block's code at base `b` stores to no level below `b`. -/
theorem storesFrom_compileProg (b : Nat) {Γ Γ' : Ctx} :
    (P : Solidity.Prog C Γ Γ') → StoresFrom b (compileProg b P)
  | .nil => fun _ _ h => nomatch h
  | .cons s P => by
    have := storesFrom_compileStmt b s; have := storesFrom_compileProg b P
    simp only [compileProg]; stores_from
end

/-- **A call keeps its caller's locals** until the returned value is copied:
the arguments, the return variable and the body store at levels
`b + Γ.length` and above, the callee's frame. -/
theorem storesFrom_callFrame (b : Nat) {Γ Γ' ps rs Γf : Ctx}
    (args : Solidity.Args C Γ ps) (ret : Solidity.CallRet Γ rs Γ')
    (body : Solidity.Prog C (rs ++ ps) Γf) :
    StoresFrom (b + Γ.length)
      (argsCode b args ++ retEnterCode b ps ret ++ compileProg (b + Γ.length) body) := by
  have := storesFrom_argsCode b args; have := storesFrom_retEnterCode b ps ret
  have := storesFrom_compileProg (b + Γ.length) body
  stores_from


namespace Sim

variable {L b : Nat} {Γ : Ctx} {F : Frag Γ} {σ : State C Γ} {m : Machine}

/-! The fields of `SimL` read on the typed state itself. -/

theorem store (h : Sim C L b F σ m) : ReprStore C L m.store σ.storage := SimL.store h

theorem fragile (h : Sim C L b F σ m) {R : RefTy} (i : Idx Γ (.alias R))
    (hi : F.get i = .fragile) :
    ∃ r s, Look.ofTEnv σ.env i = some r ∧ m.memAt (lvl b i) = .slot s ∧
      PathSlot C false r s ∧ ∃ sv, σ.storage.findLive r = some sv :=
  SimL.fragile h i hi

theorem net (h : Sim C L b F σ m) :
    ∀ a : Fin W, a ≠ m.self → netAt σ.net a.1 = (m.bal₀ a : Int) - m.bal a :=
  SimL.net h

theorem netSelf (h : Sim C L b F σ m) : netAt σ.net m.self = 0 := SimL.netSelf h

theorem env (h : Sim C L b F σ m) : EnvSim σ.tx m := SimL.env h

/-- A payment booked: the ledger down at `x`, and the balances moved to match. -/
theorem book (h : Sim C L b F σ m) (x : PrimTy.uint.Denote) (y : Int) (bl bl₀ : Fin W → Nat)
    (hn : ∀ a : Fin W, a ≠ m.self → netAt (σ.pay x y).net a.1 = (bl₀ a : Int) - bl a)
    (hself : netAt (σ.pay x y).net m.self = 0) :
    Sim C L b F (σ.pay x y) { m with bal := bl, bal₀ := bl₀ } :=
  SimL.book h x y bl bl₀ hn hself

/-- Under a looser bound on the arrays. -/
theorem mono {L' : Nat} (h : Sim C L b F σ m) (hL : L ≤ L') (hL' : L' ≤ Lmax) :
    Sim C L' b F σ m :=
  SimL.mono h hL hL'

/-- A storage write that lowers no array's length. -/
theorem store' (h : Sim C L b F σ m) {st' : WordStore} {stor : Solidity.Storage C}
    (hs : ReprStore C L st' stor) (hlen : ∀ x, LenSlot C x → m.store x ≤ st' x) :
    Sim C L b F (σ.withStorage stor) { m with store := st' } :=
  SimL.store' h hs hlen

/-- A storage write that may shrink an array (`pop`, `delete`): the fragile
aliases forgotten. -/
theorem storeDrop (h : Sim C L b F σ m) {st' : WordStore} {stor : Solidity.Storage C}
    (hs : ReprStore C L st' stor) :
    Sim C L b F.dropFragile (σ.withStorage stor) { m with store := st' } :=
  SimL.storeDrop h hs

end Sim

end Solidity.Evm
