import Solidity.Evm.BoundedSemantics
import Solidity.SemanticsProperties

/-!
# Semantic preservation of the Solidity → EVM compiler

The headline theorems (`compileProgram_preserves`,
`compileProgram_preserves_revert`) state: whenever the bounded
semantics (`execWBlock`) of a compiled block succeeds or reverts, the
*official* interpreter (`Semantics.execBlock`) does the same, and the
EVM machine of `Evm/Machine.lean` running the compiled code from any
representing configuration terminates at the end of the code in a
configuration representing the same final state (or reaches `REVERT`,
respectively).

The proof is a forward simulation in the style of Leroy's verified
compilation of IMP to a stack VM ("code in context"): every lemma
quantifies over a placement `codeAt C base code` of the compiled
fragment inside an arbitrary full program `C` — sound because the
compiler emits only *relative* forward jumps — and over the words below
the fragment's own temporaries, so the lemmas compose by
`codeAt.append_left/right` and `Steps.trans`.

Layout of the file:

- representation relations `ReprVal`/`ReprSVal`/`ReprState` between
  interpreter states and machine stack/storage;
- word-level transfer lemmas (`BitVec` arithmetic ↔ checked `Int`
  arithmetic);
- `strictOp_sim`: the strict binary operators;
- `compileExpr_sim`: expression simulation (values and reverts);
- `compileStmt_sim`/`compileBlock_sim`: statement and block simulation
  (final states and reverts);
- the top-level preservation theorems, composed with the agreement
  theorems of `Evm/BoundedSemantics.lean`.
-/

-- The agreement/simulation proofs below use uniform, defensive
-- `simp` lists across dozens of structurally similar cases; the
-- unused-argument lint would demand bespoke lists per case.
set_option linter.unusedSimpArgs false

namespace Solidity
namespace Evm

open Semantics
open SemanticsProperties

/-- `2^256` as a natural number. -/
def wordSizeN : Nat := 2 ^ 256

theorem wordSizeI_eq : wordSizeI = ((wordSizeN : Nat) : Int) := by
  simp [wordSizeI, wordSizeN]

/-! ## Representation relations -/

/-- A run-time value represented by a machine word: integers embed by
`BitVec.toNat` (hence are in `[0, 2^256)`), booleans by `0`/`1`. -/
def ReprVal : Value → Word → Prop
  | Value.int v, w => v = (w.toNat : Int)
  | Value.bool b, w => w = wBool b

/-- A primitive storage value represented by a machine word. -/
def ReprSVal : SVal → Word → Prop
  | SVal.int v, w => v = (w.toNat : Int)
  | SVal.bool b, w => w = wBool b
  | _, _ => False

theorem ReprVal.toSVal {v : Value} {w : Word} (h : ReprVal v w) :
    ReprSVal v.toSVal w := by
  cases v <;> simpa [ReprVal, ReprSVal, Value.toSVal] using h

theorem ReprSVal.asValue {sv : SVal} {w : Word} (h : ReprSVal sv w) :
    ∃ v, sv.asValue = .ok v ∧ ReprVal v w := by
  cases sv with
  | prim p =>
      cases p with
      | int n => exact ⟨Value.int n, rfl, h⟩
      | bool b => exact ⟨Value.bool b, rfl, h⟩
  | struct fields => exact absurd h (by simp [ReprSVal])
  | array elems => exact absurd h (by simp [ReprSVal])
  | map entries dflt => exact absurd h (by simp [ReprSVal])

/-- A struct field represented by a machine word: primitive fields as
in `ReprSVal`; non-primitive fields (nested structs, member arrays and
mappings) carry no machine claim — every access to them is outside the
fragment. -/
def ReprField : SVal → Word → Prop
  | SVal.int v, w => v = (w.toNat : Int)
  | SVal.bool b, w => w = wBool b
  | _, _ => True

theorem ReprVal.toField {v : Value} {w : Word} (h : ReprVal v w) :
    ReprField v.toSVal w := by
  cases v <;> simpa [ReprVal, ReprField, Value.toSVal] using h

theorem ReprField.asValue {sv : SVal} {w : Word} (h : ReprField sv w)
    {v : Value} (hav : sv.asValue = .ok v) : ReprVal v w := by
  cases sv with
  | prim p => cases p <;> (cases hav; exact h)
  | struct fields => simp [SVal.asValue] at hav
  | array elems => simp [SVal.asValue] at hav
  | map entries dflt => simp [SVal.asValue] at hav

/-- Per-root storage representation: a primitive root is the word at
its direct slot; a mapping root is represented entry-wise — for every
in-fragment key, the word at the derived slot `mapSlotW` represents the
mapping's value at that key (absent keys read the default, so the
machine's untouched region must represent the default too). Other
storage shapes are unrepresentable. -/
def ReprRoot (i : Nat) (sv : SVal) (st : Store) : Prop :=
  match sv with
  | SVal.map entries dflt =>
      ∀ k : Int, 0 ≤ k → k < keyBoundI →
        ReprSVal ((lookupBy k entries).getD dflt)
          (st.read (mapSlotW (slotWord i) (BitVec.ofNat 256 k.toNat)))
  | SVal.array elems =>
      elems.length ≤ keyBound ∧
      st.read (slotWord i) = BitVec.ofNat 256 elems.length ∧
      ∀ j : Nat, j < elems.length →
        ReprSVal (elems.getD j (SVal.int 0))
          (st.read (mapSlotW (slotWord i) (BitVec.ofNat 256 j)))
  | SVal.struct sfields =>
      sfields.length ≤ keyBound ∧
      ∀ j : Nat, j < sfields.length →
        ReprField (sfields.getD j ("", SVal.int 0)).2
          (st.read (mapSlotW (slotWord i) (BitVec.ofNat 256 j)))
  | sv => ReprSVal sv (st.read (slotWord i))

/-- The state-representation invariant tying an interpreter `State` to
a machine stack (the locals region) and storage.

* `Γ` lists the stack locals, most recent first; slot `i` of the
  machine stack holds the word representing local `Γ[i]`.
* `L` lists the storage roots; storage slot `i` (key `slotWord i`)
  holds the word representing root `L[i]`.
* Names in `Γ` are distinct, disjoint from `L`, and roots are unbound
  in the interpreter environment (the compiled fragment has no storage
  aliases). -/
structure ReprState (L Γ : List Name) (s : State) (σ : List Word)
    (st : Store) : Prop where
  len : σ.length = Γ.length
  nodup : Γ.Nodup
  disj : ∀ n ∈ Γ, n ∉ L
  locals : ∀ (i : Nat) (n : Name), Γ[i]? = some n →
    ∃ v, ∃ w : Word, lookupBy n s.env = some (Binding.val v) ∧
      σ[i]? = some w ∧ ReprVal v w
  rootsEnv : ∀ n ∈ L, lookupBy n s.env = none
  roots : ∀ (i : Nat) (n : Name), L[i]? = some n →
    ∃ sv, lookupBy n s.storage = some sv ∧ ReprRoot i sv st
  net : ∀ a : Int, 0 ≤ a → a < keyBoundI →
    0 ≤ s.getNet a ∧ s.getNet a < wordSizeI ∧
    st.read (netSlotW (BitVec.ofNat 256 a.toNat))
      = BitVec.ofNat 256 (s.getNet a).toNat
  /-- The contract balance is a machine word at the reserved slot
  `balanceSlotW` (the machine's `SELFBALANCE`). -/
  balance : 0 ≤ s.selfBalance ∧ s.selfBalance < wordSizeI ∧
    st.read balanceSlotW = BitVec.ofNat 256 s.selfBalance.toNat
  layoutNodup : L.Nodup
  layoutSmall : L.length ≤ layoutBound

/-! ## List auxiliaries -/

theorem findIdx?_eq_name {l : List Name} {name : Name} {i : Nat}
    (h : l.findIdx? (· = name) = some i) : l[i]? = some name := by
  obtain ⟨hlt, hp, -⟩ := List.findIdx?_eq_some_iff_getElem.mp h
  have hval : l[i] = name := by simpa using hp
  rw [List.getElem?_eq_some_iff]
  exact ⟨hlt, hval⟩

theorem findIdx?_none_not_mem {l : List Name} {name : Name}
    (h : l.findIdx? (· = name) = none) : name ∉ l := by
  intro hmem
  have := List.findIdx?_eq_none_iff.mp h name hmem
  simp at this

theorem mem_of_findIdx?_eq_some {l : List Name} {name : Name} {i : Nat}
    (h : l.findIdx? (· = name) = some i) : name ∈ l := by
  have := findIdx?_eq_name h
  exact List.mem_of_getElem? this

/-- In a `Nodup` list, an element sits at exactly one index. -/
theorem nodup_getElem?_inj {l : List Name} (hnd : l.Nodup) {i j : Nat}
    {name : Name} (hi : l[i]? = some name) (hj : l[j]? = some name) :
    i = j := by
  have hlt : i < l.length := by
    rcases List.getElem?_eq_some_iff.mp hi with ⟨h, -⟩
    exact h
  exact List.getElem?_inj hlt hnd (hi.trans hj.symm)

/-- First-match positions transfer along a field-name spine: when an
association list's name spine equals `spine` and `name` first occurs at
spine index `j`, then `lookupBy` reads position `j`, `setBy` is the
positional update at `j`, and that update preserves the spine. -/
theorem struct_field_at_findIdx {sfields : List (Name × SVal)}
    {spine : List Name}
    (hspine : sfields.map Prod.fst = spine) {name : Name} {j : Nat}
    (hidx : spine.findIdx? (· = name) = some j) :
    j < sfields.length ∧
    lookupBy name sfields = some (sfields.getD j ("", SVal.int 0)).2 ∧
    (∀ v : SVal, setBy name v sfields = sfields.set j (name, v)) ∧
    (∀ v : SVal, (sfields.set j (name, v)).map Prod.fst = spine) := by
  induction sfields generalizing spine j with
  | nil => subst hspine; simp at hidx
  | cons p rest ih =>
      obtain ⟨n₀, v₀⟩ := p
      subst hspine
      simp only [List.map_cons, List.findIdx?_cons] at hidx
      split at hidx
      case _ hp =>
        have hn : n₀ = name := by simpa using hp
        have hj : j = 0 := by simpa using hidx.symm
        subst hj
        subst hn
        refine ⟨by simp, ?_, ?_, ?_⟩
        · simp [lookupBy]
        · intro v; simp [setBy]
        · intro v; simp
      case _ hp =>
        cases hrec : (rest.map Prod.fst).findIdx? (· = name) with
        | none => rw [hrec] at hidx; simp at hidx
        | some j' =>
            rw [hrec] at hidx
            have hj : j = j' + 1 := by simpa using hidx.symm
            subst hj
            have hn : ¬ n₀ = name := by simpa using hp
            have hne : ¬ name = n₀ := fun h => hn h.symm
            obtain ⟨hlt, hlook, hset, hsp⟩ := ih rfl hrec
            refine ⟨by simpa using Nat.succ_lt_succ hlt, ?_, ?_, ?_⟩
            · simp only [lookupBy, if_neg hne]
              simpa using hlook
            · intro v
              simp only [setBy, if_neg hne]
              rw [hset v]
              rfl
            · intro v
              simp only [List.set_cons_succ, List.map_cons,
                List.cons.injEq]
              exact ⟨trivial, hsp v⟩

/-! ## Word auxiliaries -/

@[simp] theorem wBool_true : wBool true = 1 := rfl
@[simp] theorem wBool_false : wBool false = 0 := rfl

theorem one_ne_zero_word : (1 : Word) ≠ 0 := by decide

theorem wBool_eq_zero_iff {b : Bool} : wBool b = 0 ↔ b = false := by
  cases b <;> simp [wBool, one_ne_zero_word]

theorem wBool_ne_zero_iff {b : Bool} : wBool b ≠ 0 ↔ b = true := by
  cases b <;> simp [wBool, one_ne_zero_word]

theorem iszero_wBool (b : Bool) :
    wBool (decide (wBool b = 0)) = wBool (!b) := by
  cases b <;> simp [wBool, one_ne_zero_word]

/-- Storage slot keys are injective below the layout bound. -/
theorem slotWord_inj {i j : Nat} (hi : i < wordSizeN) (hj : j < wordSizeN)
    (h : slotWord i = slotWord j) : i = j := by
  have := congrArg BitVec.toNat h
  simp only [slotWord, BitVec.toNat_ofNat] at this
  unfold wordSizeN at hi hj
  omega

theorem slotWord_toNat {i : Nat} (h : i < layoutBound) :
    (slotWord i).toNat = i := by
  simp only [slotWord, BitVec.toNat_ofNat]
  simp only [layoutBound] at h
  omega

/-- The derived slot of a mapping entry, in the injectivity domain. -/
theorem mapSlotW_toNat {i : Nat} (hi : i < layoutBound) {kw : Word}
    (hk : kw.toNat < keyBound) :
    (mapSlotW (slotWord i) kw).toNat = (i + 1) * 2 ^ 224 + kw.toNat := by
  simp only [mapSlotW, slotWord_toNat hi, BitVec.toNat_ofNat]
  simp only [layoutBound] at hi
  simp only [keyBound] at hk
  omega

/-- Mapping-entry slots never collide with direct root slots. -/
theorem mapSlotW_ne_slotWord {i j : Nat} (hi : i < layoutBound)
    (hj : j < layoutBound) {kw : Word} (hk : kw.toNat < keyBound) :
    mapSlotW (slotWord i) kw ≠ slotWord j := by
  intro heq
  have h1 := congrArg BitVec.toNat heq
  rw [mapSlotW_toNat hi hk, slotWord_toNat hj] at h1
  simp only [layoutBound] at hi hj
  simp only [keyBound] at hk
  omega

/-- Mapping-entry slots are injective in (root, key). -/
theorem mapSlotW_inj {i j : Nat} (hi : i < layoutBound)
    (hj : j < layoutBound) {k₁ k₂ : Word} (hk₁ : k₁.toNat < keyBound)
    (hk₂ : k₂.toNat < keyBound)
    (heq : mapSlotW (slotWord i) k₁ = mapSlotW (slotWord j) k₂) :
    i = j ∧ k₁ = k₂ := by
  have h1 := congrArg BitVec.toNat heq
  rw [mapSlotW_toNat hi hk₁, mapSlotW_toNat hj hk₂] at h1
  simp only [layoutBound] at hi hj
  simp only [keyBound] at hk₁ hk₂
  refine ⟨by omega, ?_⟩
  apply BitVec.toNat_inj.mp
  omega

/-- The word of an in-fragment key, from its representation. -/
theorem keyWord_eq {k : Int} (h0 : 0 ≤ k) (hb : k < keyBoundI)
    {kw : Word} (hkw : k = (kw.toNat : Int)) :
    kw = BitVec.ofNat 256 k.toNat ∧ kw.toNat < keyBound := by
  simp only [keyBoundI] at hb
  simp only [keyBound]
  have h1 : kw.toNat = k.toNat := by omega
  refine ⟨?_, by omega⟩
  apply BitVec.toNat_inj.mp
  rw [BitVec.toNat_ofNat]
  omega

theorem netBase_toNat : netBase.toNat = 2 ^ 255 + 2 ^ 225 := by
  simp only [netBase, BitVec.toNat_ofNat]

theorem netSlotW_toNat {aw : Word} (haw : aw.toNat < keyBound) :
    (netSlotW aw).toNat = 2 ^ 255 + 2 ^ 225 + aw.toNat := by
  simp only [netSlotW, BitVec.toNat_add, netBase_toNat]
  simp only [keyBound] at haw
  omega

/-- Net-ledger slots never collide with direct root slots. -/
theorem netSlotW_ne_slotWord {j : Nat} (hj : j < layoutBound)
    {aw : Word} (haw : aw.toNat < keyBound) :
    netSlotW aw ≠ slotWord j := by
  intro heq
  have := congrArg BitVec.toNat heq
  rw [netSlotW_toNat haw, slotWord_toNat hj] at this
  simp only [layoutBound] at hj
  simp only [keyBound] at haw
  omega

/-- Net-ledger slots never collide with derived slots. -/
theorem netSlotW_ne_mapSlotW {i : Nat} (hi : i < layoutBound)
    {kw : Word} (hk : kw.toNat < keyBound)
    {aw : Word} (haw : aw.toNat < keyBound) :
    netSlotW aw ≠ mapSlotW (slotWord i) kw := by
  intro heq
  have := congrArg BitVec.toNat heq
  rw [netSlotW_toNat haw, mapSlotW_toNat hi hk] at this
  simp only [layoutBound] at hi
  simp only [keyBound] at hk haw
  omega

/-- Net-ledger slots are injective in the address. -/
theorem netSlotW_inj {a₁ a₂ : Word} (h₁ : a₁.toNat < keyBound)
    (h₂ : a₂.toNat < keyBound) (heq : netSlotW a₁ = netSlotW a₂) :
    a₁ = a₂ := by
  have := congrArg BitVec.toNat heq
  rw [netSlotW_toNat h₁, netSlotW_toNat h₂] at this
  exact BitVec.toNat_inj.mp (by omega)

theorem balanceSlotW_toNat : balanceSlotW.toNat = 2 ^ 255 + 2 ^ 226 := by
  simp only [balanceSlotW, BitVec.toNat_ofNat]

/-- The balance word never collides with a direct root slot. -/
theorem balanceSlotW_ne_slotWord {j : Nat} (hj : j < layoutBound) :
    balanceSlotW ≠ slotWord j := by
  intro heq
  have := congrArg BitVec.toNat heq
  rw [balanceSlotW_toNat, slotWord_toNat hj] at this
  simp only [layoutBound] at hj
  omega

/-- The balance word never collides with a derived slot. -/
theorem balanceSlotW_ne_mapSlotW {i : Nat} (hi : i < layoutBound)
    {kw : Word} (hk : kw.toNat < keyBound) :
    balanceSlotW ≠ mapSlotW (slotWord i) kw := by
  intro heq
  have := congrArg BitVec.toNat heq
  rw [balanceSlotW_toNat, mapSlotW_toNat hi hk] at this
  simp only [layoutBound] at hi
  simp only [keyBound] at hk
  omega

/-- The balance word never collides with a net-ledger slot. -/
theorem balanceSlotW_ne_netSlotW {aw : Word} (haw : aw.toNat < keyBound) :
    balanceSlotW ≠ netSlotW aw := by
  intro heq
  have := congrArg BitVec.toNat heq
  rw [balanceSlotW_toNat, netSlotW_toNat haw] at this
  simp only [keyBound] at haw
  omega

theorem store_read_write_self (st : Store) (k : Word) (v : Word) :
    (st.write k v).read k = v := by
  simp [Store.read, Store.write]

theorem store_read_write_ne (st : Store) {k k' : Word} (h : k' ≠ k)
    (v : Word) : (st.write k v).read k' = st.read k' := by
  simp [Store.read, Store.write, lookupBy_setBy_ne h]

/-! ## Steps helpers -/

theorem Steps.cast_pc {C : Code} {c₁ : Conf} {pc pc' : Nat}
    {σ : List Word} {st : Store} (h : Steps C c₁ ⟨pc, σ, st⟩)
    (hpc : pc = pc') : Steps C c₁ ⟨pc', σ, st⟩ := hpc ▸ h

theorem codeAt_cast {C : Code} {b b' : Nat} {c : Code}
    (h : codeAt C b c) (hb : b = b') : codeAt C b' c := hb ▸ h

/-! ## ReprState update lemmas -/

/-- Overwriting an existing local (machine: `SWAP (i+1); POP` writes
stack slot `i`) preserves the representation. -/
theorem ReprState.setLocal {L Γ : List Name} {s : State} {σ : List Word}
    {st : Store} (h : ReprState L Γ s σ st) {i : Nat} {name : Name}
    (hidx : Γ[i]? = some name) {v : Value} {w : Word}
    (hvw : ReprVal v w) :
    ReprState L Γ (s.setEnv name (Binding.val v)) (σ.set i w) st where
  len := by simp [h.len]
  nodup := h.nodup
  disj := h.disj
  locals := by
    intro j n hj
    by_cases hij : j = i
    · subst hij
      have hn : n = name := by
        rw [hidx] at hj
        exact (Option.some.inj hj).symm
      subst hn
      have hlt : j < σ.length := by
        obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.mp hidx
        have := h.len
        omega
      exact ⟨v, w, by simp [State.setEnv], by simp [List.getElem?_set_self hlt],
        hvw⟩
    · obtain ⟨v', w', henv, hσ, hrv⟩ := h.locals j n hj
      have hne : n ≠ name := fun heq =>
        hij (nodup_getElem?_inj h.nodup (heq ▸ hj) hidx)
      refine ⟨v', w', ?_, ?_, hrv⟩
      · simpa [State.setEnv, lookupBy_setBy_ne hne] using henv
      · rw [List.getElem?_set_ne (fun heq => hij heq.symm)]
        exact hσ
  rootsEnv := by
    intro n hn
    have hmem : name ∈ Γ := List.mem_of_getElem? hidx
    have hne : n ≠ name := fun heq => (h.disj name hmem) (heq ▸ hn)
    simpa [State.setEnv, lookupBy_setBy_ne hne] using h.rootsEnv n hn
  roots := h.roots
  net := h.net
  balance := h.balance
  layoutNodup := h.layoutNodup
  layoutSmall := h.layoutSmall

/-- Declaring a fresh local (machine: the initializer's value stays on
the stack as the new top slot) extends the representation. -/
theorem ReprState.pushLocal {L Γ : List Name} {s : State} {σ : List Word}
    {st : Store} (h : ReprState L Γ s σ st) {name : Name}
    (hnew : name ∉ Γ) (hnotL : name ∉ L) {v : Value} {w : Word}
    (hvw : ReprVal v w) :
    ReprState L (name :: Γ) (s.setEnv name (Binding.val v)) (w :: σ)
      st where
  len := by simp [h.len]
  nodup := by simp [List.nodup_cons, hnew, h.nodup]
  disj := by
    intro n hn
    rcases List.mem_cons.mp hn with rfl | hn'
    · exact hnotL
    · exact h.disj n hn'
  locals := by
    intro i n hi
    cases i with
    | zero =>
        have hn : name = n := by simpa using hi
        subst hn
        exact ⟨v, w, by simp [State.setEnv], by simp, hvw⟩
    | succ j =>
        have hj : Γ[j]? = some n := by simpa using hi
        obtain ⟨v', w', henv, hσ, hrv⟩ := h.locals j n hj
        have hne : n ≠ name := fun heq =>
          hnew (heq ▸ List.mem_of_getElem? hj)
        refine ⟨v', w', ?_, by simpa using hσ, hrv⟩
        simpa [State.setEnv, lookupBy_setBy_ne hne] using henv
  rootsEnv := by
    intro n hn
    have hne : n ≠ name := fun heq => hnotL (heq ▸ hn)
    simpa [State.setEnv, lookupBy_setBy_ne hne] using h.rootsEnv n hn
  roots := h.roots
  net := h.net
  balance := h.balance
  layoutNodup := h.layoutNodup
  layoutSmall := h.layoutSmall

/-- Writing a storage root (machine: `SSTORE` at its slot key)
preserves the representation. -/
theorem ReprState.setRoot {L Γ : List Name} {s : State} {σ : List Word}
    {st : Store} (h : ReprState L Γ s σ st) {i : Nat} {name : Name}
    (hidx : L[i]? = some name) {v : Value} {w : Word}
    (hvw : ReprVal v w) :
    ReprState L Γ { s with storage := setBy name v.toSVal s.storage } σ
      (st.write (slotWord i) w) where
  len := h.len
  nodup := h.nodup
  disj := h.disj
  locals := by
    intro j n hj
    obtain ⟨v', w', henv, hσ, hrv⟩ := h.locals j n hj
    exact ⟨v', w', henv, hσ, hrv⟩
  rootsEnv := by
    intro n hn
    exact h.rootsEnv n hn
  roots := by
    intro j n hj
    obtain ⟨hjlt, -⟩ := List.getElem?_eq_some_iff.mp hj
    obtain ⟨hilt, -⟩ := List.getElem?_eq_some_iff.mp hidx
    have hjb : j < layoutBound := by
      have := h.layoutSmall; omega
    have hib : i < layoutBound := by
      have := h.layoutSmall; omega
    by_cases hij : j = i
    · subst hij
      have hn : n = name := by
        rw [hidx] at hj
        exact (Option.some.inj hj).symm
      subst hn
      refine ⟨v.toSVal, by simp, ?_⟩
      cases v with
      | int nv =>
          simp only [Value.toSVal, ReprRoot]
          rw [store_read_write_self]
          exact hvw.toSVal
      | bool bv =>
          simp only [Value.toSVal, ReprRoot]
          rw [store_read_write_self]
          exact hvw.toSVal
    · obtain ⟨sv, hst, hroot⟩ := h.roots j n hj
      have hne : n ≠ name := fun heq =>
        hij (nodup_getElem?_inj h.layoutNodup (heq ▸ hj) hidx)
      have hslot : slotWord j ≠ slotWord i := by
        intro heq
        exact hij (slotWord_inj
          (by simp only [layoutBound] at hjb
              simp only [wordSizeN]; omega)
          (by simp only [layoutBound] at hib
              simp only [wordSizeN]; omega) heq)
      refine ⟨sv, by simpa [lookupBy_setBy_ne hne] using hst, ?_⟩
      cases sv with
      | map entries dflt =>
          simp only [ReprRoot]
          intro k hk0 hkb
          have hkey : (BitVec.ofNat 256 k.toNat).toNat < keyBound := by
            simp only [keyBoundI] at hkb
            simp only [keyBound]
            rw [BitVec.toNat_ofNat]
            omega
          rw [store_read_write_ne st
            (mapSlotW_ne_slotWord hjb hib hkey)]
          have hroot' := hroot
          simp only [ReprRoot] at hroot'
          exact hroot' k hk0 hkb
      | prim pv =>
          cases pv <;>
            (simp only [ReprRoot] at hroot ⊢
             rw [store_read_write_ne st hslot]
             exact hroot)
      | struct sfields' =>
          simp only [ReprRoot] at hroot ⊢
          obtain ⟨hlenS, hfldsS⟩ := hroot
          refine ⟨hlenS, ?_⟩
          intro j' hj'
          have hkeyS : (BitVec.ofNat 256 j').toNat < keyBound := by
            simp only [keyBound] at hlenS ⊢
            rw [BitVec.toNat_ofNat]
            omega
          rw [store_read_write_ne st
            (mapSlotW_ne_slotWord hjb hib hkeyS)]
          exact hfldsS j' hj'
      | array elems =>
          simp only [ReprRoot] at hroot ⊢
          obtain ⟨hlen, hlslot, helems⟩ := hroot
          refine ⟨hlen, ?_, ?_⟩
          · rw [store_read_write_ne st hslot]
            exact hlslot
          · intro j' hj'
            have hkey : (BitVec.ofNat 256 j').toNat < keyBound := by
              simp only [keyBound] at hlen ⊢
              rw [BitVec.toNat_ofNat]
              omega
            rw [store_read_write_ne st
              (mapSlotW_ne_slotWord hjb hib hkey)]
            exact helems j' hj'
  net := by
    intro a ha0 hab
    obtain ⟨h1, h2, h3⟩ := h.net a ha0 hab
    obtain ⟨hilt, -⟩ := List.getElem?_eq_some_iff.mp hidx
    have hib : i < layoutBound := by
      have := h.layoutSmall; omega
    have hkey : (BitVec.ofNat 256 a.toNat).toNat < keyBound := by
      simp only [keyBoundI] at hab
      simp only [keyBound]
      rw [BitVec.toNat_ofNat]
      omega
    refine ⟨h1, h2, ?_⟩
    rw [store_read_write_ne st (netSlotW_ne_slotWord hib hkey)]
    exact h3
  balance := by
    obtain ⟨h1, h2, h3⟩ := h.balance
    obtain ⟨hilt, -⟩ := List.getElem?_eq_some_iff.mp hidx
    have hib : i < layoutBound := by
      have := h.layoutSmall; omega
    refine ⟨h1, h2, ?_⟩
    rw [store_read_write_ne st (balanceSlotW_ne_slotWord hib)]
    exact h3
  layoutNodup := h.layoutNodup
  layoutSmall := h.layoutSmall

/-- Writing one entry of a mapping root (machine: `SSTORE` at the
derived slot) preserves the representation. -/
theorem ReprState.setMapRoot {L Γ : List Name} {s : State}
    {σ : List Word} {st : Store} (h : ReprState L Γ s σ st) {i : Nat}
    {name : Name} (hidx : L[i]? = some name)
    {entries : List (Int × SVal)} {dflt : SVal}
    (hst : lookupBy name s.storage = some (SVal.map entries dflt))
    {k : Int} (hk0 : 0 ≤ k) (hkb : k < keyBoundI)
    {v : Value} {w kw : Word} (hvw : ReprVal v w)
    (hkw : k = (kw.toNat : Int)) :
    ReprState L Γ
      { s with storage :=
          (setBy name (SVal.map (setBy k v.toSVal entries) dflt)
            s.storage) } σ
      (st.write (mapSlotW (slotWord i) kw) w) where
  len := h.len
  nodup := h.nodup
  disj := h.disj
  locals := by
    intro j n hj
    obtain ⟨v', w', henv, hσ, hrv⟩ := h.locals j n hj
    exact ⟨v', w', henv, hσ, hrv⟩
  rootsEnv := by
    intro n hn
    exact h.rootsEnv n hn
  roots := by
    intro j n hj
    obtain ⟨hjlt, -⟩ := List.getElem?_eq_some_iff.mp hj
    obtain ⟨hilt, -⟩ := List.getElem?_eq_some_iff.mp hidx
    have hjb : j < layoutBound := by
      have := h.layoutSmall; omega
    have hib : i < layoutBound := by
      have := h.layoutSmall; omega
    obtain ⟨hkweq, hkwlt⟩ := keyWord_eq hk0 hkb hkw
    by_cases hij : j = i
    · subst hij
      have hn : name = n := by
        rw [hidx] at hj
        exact Option.some.inj hj
      subst hn
      refine ⟨SVal.map (setBy k v.toSVal entries) dflt, by simp, ?_⟩
      obtain ⟨sv₀, hst₀, hroot₀⟩ := h.roots j name hidx
      rw [hst] at hst₀
      cases hst₀
      simp only [ReprRoot] at hroot₀ ⊢
      intro k' hk0' hkb'
      have hkey' : (BitVec.ofNat 256 k'.toNat).toNat < keyBound := by
        simp only [keyBoundI] at hkb'
        simp only [keyBound]
        rw [BitVec.toNat_ofNat]
        omega
      by_cases hkk : k' = k
      · subst hkk
        rw [lookupBy_setBy_self]
        rw [← hkweq, store_read_write_self]
        simpa using hvw.toSVal
      · rw [lookupBy_setBy_ne hkk]
        have hkwne : BitVec.ofNat 256 k'.toNat ≠ kw := by
          rw [hkweq]
          intro heq
          apply hkk
          have := congrArg BitVec.toNat heq
          rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat] at this
          simp only [keyBoundI] at hkb hkb'
          omega
        rw [store_read_write_ne st
          (fun heq =>
            hkwne (mapSlotW_inj hjb hjb hkey'
              (by rw [hkweq] at *; exact hkwlt) heq).2)]
        exact hroot₀ k' hk0' hkb'
    · obtain ⟨sv, hst', hroot⟩ := h.roots j n hj
      have hne : n ≠ name := fun heq =>
        hij (nodup_getElem?_inj h.layoutNodup (heq ▸ hj) hidx)
      refine ⟨sv, by simpa [lookupBy_setBy_ne hne] using hst', ?_⟩
      cases sv with
      | map entries' dflt' =>
          simp only [ReprRoot] at hroot ⊢
          intro k' hk0' hkb'
          have hkey' : (BitVec.ofNat 256 k'.toNat).toNat < keyBound := by
            simp only [keyBoundI] at hkb'
            simp only [keyBound]
            rw [BitVec.toNat_ofNat]
            omega
          rw [store_read_write_ne st
            (fun heq =>
              hij ((mapSlotW_inj hjb hib hkey'
                (by rw [hkweq] at *; exact hkwlt) heq).1))]
          exact hroot k' hk0' hkb'
      | prim pv =>
          cases pv <;>
            (simp only [ReprRoot] at hroot ⊢
             rw [store_read_write_ne st
               (fun heq => (mapSlotW_ne_slotWord hib hjb
                 (by rw [hkweq] at *; exact hkwlt)) heq.symm)]
             exact hroot)
      | struct sfields' =>
          simp only [ReprRoot] at hroot ⊢
          obtain ⟨hlenS, hfldsS⟩ := hroot
          refine ⟨hlenS, ?_⟩
          intro j' hj'
          have hkeyS : (BitVec.ofNat 256 j').toNat < keyBound := by
            simp only [keyBound] at hlenS ⊢
            rw [BitVec.toNat_ofNat]
            omega
          rw [store_read_write_ne st
            (fun heq =>
              hij ((mapSlotW_inj hjb hib hkeyS
                (by rw [hkweq] at *; exact hkwlt) heq).1))]
          exact hfldsS j' hj'
      | array elems =>
          simp only [ReprRoot] at hroot ⊢
          obtain ⟨hlen, hlslot, helems⟩ := hroot
          refine ⟨hlen, ?_, ?_⟩
          · rw [store_read_write_ne st
              (fun heq => (mapSlotW_ne_slotWord hib hjb
                (by rw [hkweq] at *; exact hkwlt)) heq.symm)]
            exact hlslot
          · intro j' hj'
            have hkey' : (BitVec.ofNat 256 j').toNat < keyBound := by
              simp only [keyBound] at hlen ⊢
              rw [BitVec.toNat_ofNat]
              omega
            rw [store_read_write_ne st
              (fun heq =>
                hij ((mapSlotW_inj hjb hib hkey'
                  (by rw [hkweq] at *; exact hkwlt) heq).1))]
            exact helems j' hj'
  net := by
    intro a ha0 hab
    obtain ⟨h1, h2, h3⟩ := h.net a ha0 hab
    obtain ⟨hilt, -⟩ := List.getElem?_eq_some_iff.mp hidx
    have hib : i < layoutBound := by
      have := h.layoutSmall; omega
    have hkwlt : kw.toNat < keyBound := by
      simp only [keyBoundI] at hkb
      simp only [keyBound]
      omega
    have hkey : (BitVec.ofNat 256 a.toNat).toNat < keyBound := by
      simp only [keyBoundI] at hab
      simp only [keyBound]
      rw [BitVec.toNat_ofNat]
      omega
    refine ⟨h1, h2, ?_⟩
    rw [store_read_write_ne st (netSlotW_ne_mapSlotW hib hkwlt hkey)]
    exact h3
  balance := by
    obtain ⟨h1, h2, h3⟩ := h.balance
    obtain ⟨hilt, -⟩ := List.getElem?_eq_some_iff.mp hidx
    have hib : i < layoutBound := by
      have := h.layoutSmall; omega
    have hkwlt : kw.toNat < keyBound := by
      simp only [keyBoundI] at hkb
      simp only [keyBound]
      omega
    refine ⟨h1, h2, ?_⟩
    rw [store_read_write_ne st (balanceSlotW_ne_mapSlotW hib hkwlt)]
    exact h3
  layoutNodup := h.layoutNodup
  layoutSmall := h.layoutSmall

/-- Writing one element of an array root (machine: `SSTORE` at the
derived slot; the length slot is untouched) preserves the
representation. -/
theorem ReprState.setArrayElem {L Γ : List Name} {s : State}
    {σ : List Word} {st : Store} (h : ReprState L Γ s σ st) {i : Nat}
    {name : Name} (hidx : L[i]? = some name)
    {elems : List SVal}
    (hst : lookupBy name s.storage = some (SVal.array elems))
    {k : Int} (hk0 : 0 ≤ k) (hlt : k.toNat < elems.length)
    {v : Value} {w kw : Word} (hvw : ReprVal v w)
    (hkw : k = (kw.toNat : Int)) :
    ReprState L Γ
      { s with storage :=
          (setBy name (SVal.array (elems.set k.toNat v.toSVal))
            s.storage) } σ
      (st.write (mapSlotW (slotWord i) kw) w) where
  len := h.len
  nodup := h.nodup
  disj := h.disj
  locals := by
    intro j n hj
    obtain ⟨v', w', henv, hσ, hrv⟩ := h.locals j n hj
    exact ⟨v', w', henv, hσ, hrv⟩
  rootsEnv := by
    intro n hn
    exact h.rootsEnv n hn
  roots := by
    intro j n hj
    obtain ⟨hjlt, -⟩ := List.getElem?_eq_some_iff.mp hj
    obtain ⟨hilt, -⟩ := List.getElem?_eq_some_iff.mp hidx
    have hjb : j < layoutBound := by
      have := h.layoutSmall; omega
    have hib : i < layoutBound := by
      have := h.layoutSmall; omega
    obtain ⟨sv₀, hst₀, hroot₀⟩ := h.roots i name hidx
    rw [hst] at hst₀
    cases hst₀
    have hroot₀' := hroot₀
    simp only [ReprRoot] at hroot₀'
    obtain ⟨hlen, hlslot, helems⟩ := hroot₀'
    have hkb : k < keyBoundI := by
      simp only [keyBoundI]
      simp only [keyBound] at hlen
      omega
    obtain ⟨hkweq, hkwlt⟩ := keyWord_eq hk0 hkb hkw
    by_cases hij : j = i
    · subst hij
      have hn : name = n := by
        rw [hidx] at hj
        exact Option.some.inj hj
      subst hn
      refine ⟨SVal.array (elems.set k.toNat v.toSVal), by simp, ?_⟩
      simp only [ReprRoot, List.length_set]
      refine ⟨hlen, ?_, ?_⟩
      · rw [store_read_write_ne st
          (fun heq => (mapSlotW_ne_slotWord hib hib hkwlt) heq.symm)]
        exact hlslot
      · intro j' hj'
        have hkey' : (BitVec.ofNat 256 j').toNat < keyBound := by
          simp only [keyBound] at hlen ⊢
          rw [BitVec.toNat_ofNat]
          omega
        by_cases hjk : j' = k.toNat
        · have hset : (elems.set k.toNat v.toSVal).getD j' (SVal.int 0)
              = v.toSVal := by
            subst hjk
            rw [List.getD_eq_getElem?_getD,
              List.getElem?_set_self (by omega)]
            rfl
          rw [hset]
          have hkwj : BitVec.ofNat 256 j' = kw := by
            rw [hjk, hkweq]
          rw [hkwj, store_read_write_self]
          exact hvw.toSVal
        · have hset : (elems.set k.toNat v.toSVal).getD j' (SVal.int 0)
              = elems.getD j' (SVal.int 0) := by
            rw [List.getD_eq_getElem?_getD,
              List.getElem?_set_ne (fun heq => hjk heq.symm),
              ← List.getD_eq_getElem?_getD]
          rw [hset]
          have hkwne : BitVec.ofNat 256 j' ≠ kw := by
            rw [hkweq]
            intro heq
            apply hjk
            have := congrArg BitVec.toNat heq
            rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat] at this
            simp only [keyBound] at hlen hkwlt
            omega
          rw [store_read_write_ne st
            (fun heq =>
              hkwne (mapSlotW_inj hib hib hkey' hkwlt heq).2)]
          exact helems j' hj'
    · obtain ⟨sv, hst', hroot⟩ := h.roots j n hj
      have hne : n ≠ name := fun heq =>
        hij (nodup_getElem?_inj h.layoutNodup (heq ▸ hj) hidx)
      refine ⟨sv, by simpa [lookupBy_setBy_ne hne] using hst', ?_⟩
      cases sv with
      | map entries' dflt' =>
          simp only [ReprRoot] at hroot ⊢
          intro k' hk0' hkb'
          have hkey' : (BitVec.ofNat 256 k'.toNat).toNat < keyBound := by
            simp only [keyBoundI] at hkb'
            simp only [keyBound]
            rw [BitVec.toNat_ofNat]
            omega
          rw [store_read_write_ne st
            (fun heq =>
              hij ((mapSlotW_inj hjb hib hkey' hkwlt heq).1))]
          exact hroot k' hk0' hkb'
      | prim pv =>
          cases pv <;>
            (simp only [ReprRoot] at hroot ⊢
             rw [store_read_write_ne st
               (fun heq => (mapSlotW_ne_slotWord hib hjb hkwlt) heq.symm)]
             exact hroot)
      | struct sfields' =>
          simp only [ReprRoot] at hroot ⊢
          obtain ⟨hlenS, hfldsS⟩ := hroot
          refine ⟨hlenS, ?_⟩
          intro j' hj'
          have hkeyS : (BitVec.ofNat 256 j').toNat < keyBound := by
            simp only [keyBound] at hlenS ⊢
            rw [BitVec.toNat_ofNat]
            omega
          rw [store_read_write_ne st
            (fun heq =>
              hij ((mapSlotW_inj hjb hib hkeyS hkwlt heq).1))]
          exact hfldsS j' hj'
      | array elems' =>
          simp only [ReprRoot] at hroot ⊢
          obtain ⟨hlen', hlslot', helems'⟩ := hroot
          refine ⟨hlen', ?_, ?_⟩
          · rw [store_read_write_ne st
              (fun heq => (mapSlotW_ne_slotWord hib hjb hkwlt) heq.symm)]
            exact hlslot'
          · intro j' hj'
            have hkey' : (BitVec.ofNat 256 j').toNat < keyBound := by
              simp only [keyBound] at hlen' ⊢
              rw [BitVec.toNat_ofNat]
              omega
            rw [store_read_write_ne st
              (fun heq =>
                hij ((mapSlotW_inj hjb hib hkey' hkwlt heq).1))]
            exact helems' j' hj'
  net := by
    intro a ha0 hab
    obtain ⟨h1, h2, h3⟩ := h.net a ha0 hab
    obtain ⟨hilt, -⟩ := List.getElem?_eq_some_iff.mp hidx
    have hib : i < layoutBound := by
      have := h.layoutSmall; omega
    obtain ⟨sv₀, hst₀, hroot₀⟩ := h.roots i name hidx
    rw [hst] at hst₀
    cases hst₀
    have hroot₀' := hroot₀
    simp only [ReprRoot] at hroot₀'
    obtain ⟨hlen, -, -⟩ := hroot₀'
    have hkwlt : kw.toNat < keyBound := by
      simp only [keyBound] at hlen ⊢
      omega
    have hkey : (BitVec.ofNat 256 a.toNat).toNat < keyBound := by
      simp only [keyBoundI] at hab
      simp only [keyBound]
      rw [BitVec.toNat_ofNat]
      omega
    refine ⟨h1, h2, ?_⟩
    rw [store_read_write_ne st (netSlotW_ne_mapSlotW hib hkwlt hkey)]
    exact h3
  balance := by
    obtain ⟨h1, h2, h3⟩ := h.balance
    obtain ⟨hilt, -⟩ := List.getElem?_eq_some_iff.mp hidx
    have hib : i < layoutBound := by
      have := h.layoutSmall; omega
    obtain ⟨sv₀, hst₀, hroot₀⟩ := h.roots i name hidx
    rw [hst] at hst₀
    cases hst₀
    have hroot₀' := hroot₀
    simp only [ReprRoot] at hroot₀'
    obtain ⟨hlen, -, -⟩ := hroot₀'
    have hkwlt : kw.toNat < keyBound := by
      simp only [keyBound] at hlen ⊢
      omega
    refine ⟨h1, h2, ?_⟩
    rw [store_read_write_ne st (balanceSlotW_ne_mapSlotW hib hkwlt)]
    exact h3
  layoutNodup := h.layoutNodup
  layoutSmall := h.layoutSmall

/-- Appending an element to an array root (machine: `SSTORE` the
element at the derived slot of index `length`, then `SSTORE`
`length + 1` at the root slot) preserves the representation. -/
theorem ReprState.pushArray {L Γ : List Name} {s : State}
    {σ : List Word} {st : Store} (h : ReprState L Γ s σ st) {i : Nat}
    {name : Name} (hidx : L[i]? = some name)
    {elems : List SVal}
    (hst : lookupBy name s.storage = some (SVal.array elems))
    (hlen1 : elems.length + 1 ≤ keyBound)
    {sv : SVal} {w : Word} (hsw : ReprSVal sv w) :
    ReprState L Γ
      { s with storage :=
          (setBy name (SVal.array (elems ++ [sv])) s.storage) } σ
      ((st.write (mapSlotW (slotWord i) (BitVec.ofNat 256 elems.length))
          w).write (slotWord i) (1 + BitVec.ofNat 256 elems.length))
    where
  len := h.len
  nodup := h.nodup
  disj := h.disj
  locals := by
    intro j n hj
    obtain ⟨v', w', henv, hσ, hrv⟩ := h.locals j n hj
    exact ⟨v', w', henv, hσ, hrv⟩
  rootsEnv := by
    intro n hn
    exact h.rootsEnv n hn
  roots := by
    intro j n hj
    obtain ⟨hjlt, -⟩ := List.getElem?_eq_some_iff.mp hj
    obtain ⟨hilt, -⟩ := List.getElem?_eq_some_iff.mp hidx
    have hjb : j < layoutBound := by
      have := h.layoutSmall; omega
    have hib : i < layoutBound := by
      have := h.layoutSmall; omega
    have hkeylen : (BitVec.ofNat 256 elems.length).toNat < keyBound := by
      simp only [keyBound] at hlen1 ⊢
      rw [BitVec.toNat_ofNat]
      omega
    have hread : ∀ key : Word, key ≠ slotWord i →
        key ≠ mapSlotW (slotWord i) (BitVec.ofNat 256 elems.length) →
        ((st.write
            (mapSlotW (slotWord i) (BitVec.ofNat 256 elems.length))
            w).write (slotWord i)
            (1 + BitVec.ofNat 256 elems.length)).read key
          = st.read key := by
      intro key h1 h2
      rw [store_read_write_ne _ h1, store_read_write_ne _ h2]
    by_cases hij : j = i
    · subst hij
      have hn : name = n := by
        rw [hidx] at hj
        exact Option.some.inj hj
      subst hn
      refine ⟨SVal.array (elems ++ [sv]), by simp, ?_⟩
      simp only [ReprRoot, List.length_append, List.length_cons,
        List.length_nil]
      refine ⟨by omega, ?_, ?_⟩
      · rw [store_read_write_self]
        apply BitVec.toNat_inj.mp
        rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
        have h1 : (1 : Word).toNat = 1 := rfl
        rw [h1]
        simp only [keyBound] at hlen1
        omega
      · intro j' hj'
        have hkey' : (BitVec.ofNat 256 j').toNat < keyBound := by
          simp only [keyBound] at hlen1 ⊢
          rw [BitVec.toNat_ofNat]
          omega
        by_cases hjlast : j' = elems.length
        · have hset : (elems ++ [sv]).getD j' (SVal.int 0) = sv := by
            subst hjlast
            rw [List.getD_eq_getElem?_getD,
              List.getElem?_append_right (Nat.le_refl _)]
            simp
          rw [hset, hjlast]
          rw [store_read_write_ne _
            (mapSlotW_ne_slotWord hjb hjb hkeylen)]
          rw [store_read_write_self]
          exact hsw
        · have hjlt' : j' < elems.length := by omega
          have hset : (elems ++ [sv]).getD j' (SVal.int 0)
              = elems.getD j' (SVal.int 0) := by
            rw [List.getD_eq_getElem?_getD,
              List.getElem?_append_left hjlt',
              ← List.getD_eq_getElem?_getD]
          rw [hset]
          have hkne : BitVec.ofNat 256 j'
              ≠ BitVec.ofNat 256 elems.length := by
            intro heq
            have := congrArg BitVec.toNat heq
            rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat] at this
            simp only [keyBound] at hlen1
            omega
          rw [hread _
            (fun heq =>
              (mapSlotW_ne_slotWord hjb hjb hkey') heq |>.elim)
            (fun heq =>
              hkne (mapSlotW_inj hjb hjb hkey' hkeylen heq).2)]
          obtain ⟨sv₀, hst₀, hroot₀⟩ := h.roots j name hidx
          rw [hst] at hst₀
          cases hst₀
          have hroot₀' := hroot₀
          simp only [ReprRoot] at hroot₀'
          exact hroot₀'.2.2 j' hjlt'
    · obtain ⟨sv', hst', hroot⟩ := h.roots j n hj
      have hne : n ≠ name := fun heq =>
        hij (nodup_getElem?_inj h.layoutNodup (heq ▸ hj) hidx)
      refine ⟨sv', by simpa [lookupBy_setBy_ne hne] using hst', ?_⟩
      have hslotne : slotWord j ≠ slotWord i := by
        intro heq
        exact hij (slotWord_inj
          (by simp only [layoutBound] at hjb
              simp only [wordSizeN]; omega)
          (by simp only [layoutBound] at hib
              simp only [wordSizeN]; omega) heq)
      cases sv' with
      | map entries' dflt' =>
          simp only [ReprRoot] at hroot ⊢
          intro k' hk0' hkb'
          have hkey' : (BitVec.ofNat 256 k'.toNat).toNat < keyBound := by
            simp only [keyBoundI] at hkb'
            simp only [keyBound]
            rw [BitVec.toNat_ofNat]
            omega
          rw [hread _
            (mapSlotW_ne_slotWord hjb hib hkey')
            (fun heq =>
              hij (mapSlotW_inj hjb hib hkey' hkeylen heq).1)]
          exact hroot k' hk0' hkb'
      | prim pv =>
          cases pv <;>
            (simp only [ReprRoot] at hroot ⊢
             rw [hread _ hslotne
               (fun heq =>
                 (mapSlotW_ne_slotWord hib hjb hkeylen) heq.symm)]
             exact hroot)
      | struct sfields' =>
          simp only [ReprRoot] at hroot ⊢
          obtain ⟨hlenS, hfldsS⟩ := hroot
          refine ⟨hlenS, ?_⟩
          intro j' hj'
          have hkeyS : (BitVec.ofNat 256 j').toNat < keyBound := by
            simp only [keyBound] at hlenS ⊢
            rw [BitVec.toNat_ofNat]
            omega
          rw [hread _
            (mapSlotW_ne_slotWord hjb hib hkeyS)
            (fun heq =>
              hij (mapSlotW_inj hjb hib hkeyS hkeylen heq).1)]
          exact hfldsS j' hj'
      | array elems' =>
          simp only [ReprRoot] at hroot ⊢
          obtain ⟨hlen', hlslot', helems'⟩ := hroot
          refine ⟨hlen', ?_, ?_⟩
          · rw [hread _ hslotne
              (fun heq =>
                (mapSlotW_ne_slotWord hib hjb hkeylen) heq.symm)]
            exact hlslot'
          · intro j' hj'
            have hkey' : (BitVec.ofNat 256 j').toNat < keyBound := by
              simp only [keyBound] at hlen' ⊢
              rw [BitVec.toNat_ofNat]
              omega
            rw [hread _
              (mapSlotW_ne_slotWord hjb hib hkey')
              (fun heq =>
                hij (mapSlotW_inj hjb hib hkey' hkeylen heq).1)]
            exact helems' j' hj'
  net := by
    intro a ha0 hab
    obtain ⟨h1, h2, h3⟩ := h.net a ha0 hab
    obtain ⟨hilt, -⟩ := List.getElem?_eq_some_iff.mp hidx
    have hib : i < layoutBound := by
      have := h.layoutSmall; omega
    have hkeylen : (BitVec.ofNat 256 elems.length).toNat
        < keyBound := by
      simp only [keyBound] at hlen1 ⊢
      rw [BitVec.toNat_ofNat]
      omega
    have hkey : (BitVec.ofNat 256 a.toNat).toNat < keyBound := by
      simp only [keyBoundI] at hab
      simp only [keyBound]
      rw [BitVec.toNat_ofNat]
      omega
    refine ⟨h1, h2, ?_⟩
    rw [store_read_write_ne _ (netSlotW_ne_slotWord hib hkey),
      store_read_write_ne _ (netSlotW_ne_mapSlotW hib hkeylen hkey)]
    exact h3
  balance := by
    obtain ⟨h1, h2, h3⟩ := h.balance
    obtain ⟨hilt, -⟩ := List.getElem?_eq_some_iff.mp hidx
    have hib : i < layoutBound := by
      have := h.layoutSmall; omega
    have hkeylen : (BitVec.ofNat 256 elems.length).toNat
        < keyBound := by
      simp only [keyBound] at hlen1 ⊢
      rw [BitVec.toNat_ofNat]
      omega
    refine ⟨h1, h2, ?_⟩
    rw [store_read_write_ne _ (balanceSlotW_ne_slotWord hib),
      store_read_write_ne _ (balanceSlotW_ne_mapSlotW hib hkeylen)]
    exact h3
  layoutNodup := h.layoutNodup
  layoutSmall := h.layoutSmall

/-- Dropping the last element of an array root (machine: `SSTORE`
`length - 1` at the root slot; the stale element slot is unobservable
because reads bounds-check first) preserves the representation. -/
theorem ReprState.popArray {L Γ : List Name} {s : State}
    {σ : List Word} {st : Store} (h : ReprState L Γ s σ st) {i : Nat}
    {name : Name} (hidx : L[i]? = some name)
    {elems : List SVal} {x : SVal} {restRev : List SVal}
    (hst : lookupBy name s.storage = some (SVal.array elems))
    (hrev : elems.reverse = x :: restRev) :
    ReprState L Γ
      { s with storage :=
          (setBy name (SVal.array restRev.reverse) s.storage) } σ
      (st.write (slotWord i) (BitVec.ofNat 256 elems.length - 1)) where
  len := h.len
  nodup := h.nodup
  disj := h.disj
  locals := by
    intro j n hj
    obtain ⟨v', w', henv, hσ, hrv⟩ := h.locals j n hj
    exact ⟨v', w', henv, hσ, hrv⟩
  rootsEnv := by
    intro n hn
    exact h.rootsEnv n hn
  roots := by
    intro j n hj
    obtain ⟨hjlt, -⟩ := List.getElem?_eq_some_iff.mp hj
    obtain ⟨hilt, -⟩ := List.getElem?_eq_some_iff.mp hidx
    have hjb : j < layoutBound := by
      have := h.layoutSmall; omega
    have hib : i < layoutBound := by
      have := h.layoutSmall; omega
    have helems_eq : elems = restRev.reverse ++ [x] := by
      have := congrArg List.reverse hrev
      simpa using this
    by_cases hij : j = i
    · subst hij
      have hn : name = n := by
        rw [hidx] at hj
        exact Option.some.inj hj
      subst hn
      obtain ⟨sv₀, hst₀, hroot₀⟩ := h.roots j name hidx
      rw [hst] at hst₀
      cases hst₀
      have hroot₀' := hroot₀
      simp only [ReprRoot] at hroot₀'
      obtain ⟨hlen, hlslot, helems⟩ := hroot₀'
      have hlenrr : elems.length = restRev.reverse.length + 1 := by
        rw [helems_eq]
        simp
      refine ⟨SVal.array restRev.reverse, by simp, ?_⟩
      simp only [ReprRoot]
      refine ⟨by omega, ?_, ?_⟩
      · rw [store_read_write_self]
        apply BitVec.toNat_inj.mp
        rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
        have h1 : (1 : Word).toNat = 1 := rfl
        rw [h1]
        simp only [keyBound] at hlen
        omega
      · intro j' hj'
        have hkey' : (BitVec.ofNat 256 j').toNat < keyBound := by
          simp only [keyBound] at hlen ⊢
          rw [BitVec.toNat_ofNat]
          omega
        rw [store_read_write_ne _
          (mapSlotW_ne_slotWord hjb hjb hkey')]
        have hset : restRev.reverse.getD j' (SVal.int 0)
            = elems.getD j' (SVal.int 0) := by
          rw [helems_eq, List.getD_eq_getElem?_getD,
            List.getD_eq_getElem?_getD,
            List.getElem?_append_left hj']
        rw [hset]
        exact helems j' (by omega)
    · obtain ⟨sv', hst', hroot⟩ := h.roots j n hj
      have hne : n ≠ name := fun heq =>
        hij (nodup_getElem?_inj h.layoutNodup (heq ▸ hj) hidx)
      have hslotne : slotWord j ≠ slotWord i := by
        intro heq
        exact hij (slotWord_inj
          (by simp only [layoutBound] at hjb
              simp only [wordSizeN]; omega)
          (by simp only [layoutBound] at hib
              simp only [wordSizeN]; omega) heq)
      refine ⟨sv', by simpa [lookupBy_setBy_ne hne] using hst', ?_⟩
      cases sv' with
      | map entries' dflt' =>
          simp only [ReprRoot] at hroot ⊢
          intro k' hk0' hkb'
          have hkey' : (BitVec.ofNat 256 k'.toNat).toNat < keyBound := by
            simp only [keyBoundI] at hkb'
            simp only [keyBound]
            rw [BitVec.toNat_ofNat]
            omega
          rw [store_read_write_ne _
            (mapSlotW_ne_slotWord hjb hib hkey')]
          exact hroot k' hk0' hkb'
      | prim pv =>
          cases pv <;>
            (simp only [ReprRoot] at hroot ⊢
             rw [store_read_write_ne _ hslotne]
             exact hroot)
      | struct sfields' =>
          simp only [ReprRoot] at hroot ⊢
          obtain ⟨hlenS, hfldsS⟩ := hroot
          refine ⟨hlenS, ?_⟩
          intro j' hj'
          have hkeyS : (BitVec.ofNat 256 j').toNat < keyBound := by
            simp only [keyBound] at hlenS ⊢
            rw [BitVec.toNat_ofNat]
            omega
          rw [store_read_write_ne _
            (mapSlotW_ne_slotWord hjb hib hkeyS)]
          exact hfldsS j' hj'
      | array elems' =>
          simp only [ReprRoot] at hroot ⊢
          obtain ⟨hlen', hlslot', helems'⟩ := hroot
          refine ⟨hlen', ?_, ?_⟩
          · rw [store_read_write_ne _ hslotne]
            exact hlslot'
          · intro j' hj'
            have hkey' : (BitVec.ofNat 256 j').toNat < keyBound := by
              simp only [keyBound] at hlen' ⊢
              rw [BitVec.toNat_ofNat]
              omega
            rw [store_read_write_ne _
              (mapSlotW_ne_slotWord hjb hib hkey')]
            exact helems' j' hj'
  net := by
    intro a ha0 hab
    obtain ⟨h1, h2, h3⟩ := h.net a ha0 hab
    obtain ⟨hilt, -⟩ := List.getElem?_eq_some_iff.mp hidx
    have hib : i < layoutBound := by
      have := h.layoutSmall; omega
    have hkey : (BitVec.ofNat 256 a.toNat).toNat < keyBound := by
      simp only [keyBoundI] at hab
      simp only [keyBound]
      rw [BitVec.toNat_ofNat]
      omega
    refine ⟨h1, h2, ?_⟩
    rw [store_read_write_ne st (netSlotW_ne_slotWord hib hkey)]
    exact h3
  balance := by
    obtain ⟨h1, h2, h3⟩ := h.balance
    obtain ⟨hilt, -⟩ := List.getElem?_eq_some_iff.mp hidx
    have hib : i < layoutBound := by
      have := h.layoutSmall; omega
    refine ⟨h1, h2, ?_⟩
    rw [store_read_write_ne st (balanceSlotW_ne_slotWord hib)]
    exact h3
  layoutNodup := h.layoutNodup
  layoutSmall := h.layoutSmall

/-- Writing one primitive field of a struct root (machine: `SSTORE` at
the field's derived slot; positional form — callers rewrite `setBy`
into the positional update via `struct_field_at_findIdx`) preserves
the representation. -/
theorem ReprState.setStructField {L Γ : List Name} {s : State}
    {σ : List Word} {st : Store} (h : ReprState L Γ s σ st) {i : Nat}
    {name : Name} (hidx : L[i]? = some name)
    {sfields : List (Name × SVal)}
    (hst : lookupBy name s.storage = some (SVal.struct sfields))
    {j : Nat} (hjlt : j < sfields.length) {fname : Name}
    {v : Value} {w : Word} (hvw : ReprVal v w) :
    ReprState L Γ
      { s with storage := (setBy name
          (SVal.struct (sfields.set j (fname, v.toSVal)))
          s.storage) } σ
      (st.write (mapSlotW (slotWord i) (BitVec.ofNat 256 j)) w) where
  len := h.len
  nodup := h.nodup
  disj := h.disj
  locals := by
    intro j' n hj'
    obtain ⟨v', w', henv, hσ, hrv⟩ := h.locals j' n hj'
    exact ⟨v', w', henv, hσ, hrv⟩
  rootsEnv := by
    intro n hn
    exact h.rootsEnv n hn
  roots := by
    intro jr n hjr
    obtain ⟨hjrlt, -⟩ := List.getElem?_eq_some_iff.mp hjr
    obtain ⟨hilt, -⟩ := List.getElem?_eq_some_iff.mp hidx
    have hjb : jr < layoutBound := by
      have := h.layoutSmall; omega
    have hib : i < layoutBound := by
      have := h.layoutSmall; omega
    obtain ⟨sv₀, hst₀, hroot₀⟩ := h.roots i name hidx
    rw [hst] at hst₀
    cases hst₀
    have hroot₀' := hroot₀
    simp only [ReprRoot] at hroot₀'
    obtain ⟨hlenS, hflds⟩ := hroot₀'
    have hkwlt : (BitVec.ofNat 256 j).toNat < keyBound := by
      simp only [keyBound] at hlenS ⊢
      rw [BitVec.toNat_ofNat]
      omega
    by_cases hij : jr = i
    · subst hij
      have hn : name = n := by
        rw [hidx] at hjr
        exact Option.some.inj hjr
      subst hn
      refine ⟨SVal.struct (sfields.set j (fname, v.toSVal)),
        by simp, ?_⟩
      simp only [ReprRoot, List.length_set]
      refine ⟨hlenS, ?_⟩
      intro j'' hj''
      have hkey'' : (BitVec.ofNat 256 j'').toNat < keyBound := by
        simp only [keyBound] at hlenS ⊢
        rw [BitVec.toNat_ofNat]
        omega
      by_cases hjj : j'' = j
      · have hset : ((sfields.set j (fname, v.toSVal)).getD j''
            ("", SVal.int 0)).2 = v.toSVal := by
          subst hjj
          rw [List.getD_eq_getElem?_getD,
            List.getElem?_set_self (by omega)]
          rfl
        rw [hset, hjj]
        rw [store_read_write_self]
        exact hvw.toField
      · have hset : (sfields.set j (fname, v.toSVal)).getD j''
            ("", SVal.int 0) = sfields.getD j'' ("", SVal.int 0) := by
          rw [List.getD_eq_getElem?_getD,
            List.getElem?_set_ne (fun heq => hjj heq.symm),
            ← List.getD_eq_getElem?_getD]
        rw [hset]
        have hkne : BitVec.ofNat 256 j'' ≠ BitVec.ofNat 256 j := by
          intro heq
          have := congrArg BitVec.toNat heq
          rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat] at this
          simp only [keyBound] at hlenS
          omega
        rw [store_read_write_ne st
          (fun heq =>
            hkne (mapSlotW_inj hib hib hkey'' hkwlt heq).2)]
        exact hflds j'' hj''
    · obtain ⟨sv, hst', hroot⟩ := h.roots jr n hjr
      have hne : n ≠ name := fun heq =>
        hij (nodup_getElem?_inj h.layoutNodup (heq ▸ hjr) hidx)
      refine ⟨sv, by simpa [lookupBy_setBy_ne hne] using hst', ?_⟩
      cases sv with
      | map entries' dflt' =>
          simp only [ReprRoot] at hroot ⊢
          intro k' hk0' hkb'
          have hkey' : (BitVec.ofNat 256 k'.toNat).toNat < keyBound := by
            simp only [keyBoundI] at hkb'
            simp only [keyBound]
            rw [BitVec.toNat_ofNat]
            omega
          rw [store_read_write_ne st
            (fun heq =>
              hij ((mapSlotW_inj hjb hib hkey' hkwlt heq).1))]
          exact hroot k' hk0' hkb'
      | prim pv =>
          cases pv <;>
            (simp only [ReprRoot] at hroot ⊢
             rw [store_read_write_ne st
               (fun heq => (mapSlotW_ne_slotWord hib hjb hkwlt) heq.symm)]
             exact hroot)
      | struct sfields'' =>
          simp only [ReprRoot] at hroot ⊢
          obtain ⟨hlen'', hflds''⟩ := hroot
          refine ⟨hlen'', ?_⟩
          intro j'' hj''
          have hkey'' : (BitVec.ofNat 256 j'').toNat < keyBound := by
            simp only [keyBound] at hlen'' ⊢
            rw [BitVec.toNat_ofNat]
            omega
          rw [store_read_write_ne st
            (fun heq =>
              hij ((mapSlotW_inj hjb hib hkey'' hkwlt heq).1))]
          exact hflds'' j'' hj''
      | array elems'' =>
          simp only [ReprRoot] at hroot ⊢
          obtain ⟨hlen'', hlslot'', helems''⟩ := hroot
          refine ⟨hlen'', ?_, ?_⟩
          · rw [store_read_write_ne st
              (fun heq =>
                (mapSlotW_ne_slotWord hib hjb hkwlt) heq.symm)]
            exact hlslot''
          · intro j'' hj''
            have hkey'' : (BitVec.ofNat 256 j'').toNat < keyBound := by
              simp only [keyBound] at hlen'' ⊢
              rw [BitVec.toNat_ofNat]
              omega
            rw [store_read_write_ne st
              (fun heq =>
                hij ((mapSlotW_inj hjb hib hkey'' hkwlt heq).1))]
            exact helems'' j'' hj''
  net := by
    intro a ha0 hab
    obtain ⟨h1, h2, h3⟩ := h.net a ha0 hab
    obtain ⟨hilt, -⟩ := List.getElem?_eq_some_iff.mp hidx
    have hib : i < layoutBound := by
      have := h.layoutSmall; omega
    obtain ⟨sv₀, hst₀, hroot₀⟩ := h.roots i name hidx
    rw [hst] at hst₀
    cases hst₀
    have hroot₀' := hroot₀
    simp only [ReprRoot] at hroot₀'
    obtain ⟨hlenS, -⟩ := hroot₀'
    have hkwlt : (BitVec.ofNat 256 j).toNat < keyBound := by
      simp only [keyBound] at hlenS ⊢
      rw [BitVec.toNat_ofNat]
      omega
    have hkey : (BitVec.ofNat 256 a.toNat).toNat < keyBound := by
      simp only [keyBoundI] at hab
      simp only [keyBound]
      rw [BitVec.toNat_ofNat]
      omega
    refine ⟨h1, h2, ?_⟩
    rw [store_read_write_ne st (netSlotW_ne_mapSlotW hib hkwlt hkey)]
    exact h3
  balance := by
    obtain ⟨h1, h2, h3⟩ := h.balance
    obtain ⟨hilt, -⟩ := List.getElem?_eq_some_iff.mp hidx
    have hib : i < layoutBound := by
      have := h.layoutSmall; omega
    obtain ⟨sv₀, hst₀, hroot₀⟩ := h.roots i name hidx
    rw [hst] at hst₀
    cases hst₀
    have hroot₀' := hroot₀
    simp only [ReprRoot] at hroot₀'
    obtain ⟨hlenS, -⟩ := hroot₀'
    have hkwlt : (BitVec.ofNat 256 j).toNat < keyBound := by
      simp only [keyBound] at hlenS ⊢
      rw [BitVec.toNat_ofNat]
      omega
    refine ⟨h1, h2, ?_⟩
    rw [store_read_write_ne st (balanceSlotW_ne_mapSlotW hib hkwlt)]
    exact h3
  layoutNodup := h.layoutNodup
  layoutSmall := h.layoutSmall

/-- Debiting the net ledger (machine: `SSTORE` at the address's
net-ledger slot) preserves the representation. -/
theorem ReprState.setNet {L Γ : List Name} {s : State} {σ : List Word}
    {st : Store} (h : ReprState L Γ s σ st)
    {a : Int} (ha0 : 0 ≤ a) (hab : a < keyBoundI)
    {amt : Int} (hamt0 : 0 ≤ amt) (hsub0 : amt ≤ s.getNet a)
    {aw amtw : Word}
    (haw : a = (aw.toNat : Int)) (hamtw : amt = (amtw.toNat : Int)) :
    ReprState L Γ (s.setNet a (s.getNet a - amt)) σ
      (st.write (netSlotW aw) (st.read (netSlotW aw) - amtw)) where
  len := h.len
  nodup := h.nodup
  disj := h.disj
  locals := by
    intro j n hj
    obtain ⟨v', w', henv, hσ, hrv⟩ := h.locals j n hj
    exact ⟨v', w', henv, hσ, hrv⟩
  rootsEnv := by
    intro n hn
    exact h.rootsEnv n hn
  roots := by
    intro j n hj
    obtain ⟨hjlt, -⟩ := List.getElem?_eq_some_iff.mp hj
    have hjb : j < layoutBound := by
      have := h.layoutSmall; omega
    have hawlt : aw.toNat < keyBound := by
      simp only [keyBoundI] at hab
      simp only [keyBound]
      omega
    obtain ⟨sv, hst', hroot⟩ := h.roots j n hj
    refine ⟨sv, hst', ?_⟩
    cases sv with
    | prim pv =>
        cases pv <;>
          (simp only [ReprRoot] at hroot ⊢
           rw [store_read_write_ne st
             (fun heq => (netSlotW_ne_slotWord hjb hawlt) heq.symm)]
           exact hroot)
    | map entries dflt =>
        simp only [ReprRoot] at hroot ⊢
        intro k' hk0' hkb'
        have hkey' : (BitVec.ofNat 256 k'.toNat).toNat < keyBound := by
          simp only [keyBoundI] at hkb'
          simp only [keyBound]
          rw [BitVec.toNat_ofNat]
          omega
        rw [store_read_write_ne st
          (fun heq =>
            (netSlotW_ne_mapSlotW hjb hkey' hawlt) heq.symm)]
        exact hroot k' hk0' hkb'
    | struct sfields =>
        simp only [ReprRoot] at hroot ⊢
        obtain ⟨hlenS, hflds⟩ := hroot
        refine ⟨hlenS, ?_⟩
        intro j'' hj''
        have hkey'' : (BitVec.ofNat 256 j'').toNat < keyBound := by
          simp only [keyBound] at hlenS ⊢
          rw [BitVec.toNat_ofNat]
          omega
        rw [store_read_write_ne st
          (fun heq =>
            (netSlotW_ne_mapSlotW hjb hkey'' hawlt) heq.symm)]
        exact hflds j'' hj''
    | array elems =>
        simp only [ReprRoot] at hroot ⊢
        obtain ⟨hlen', hlslot', helems'⟩ := hroot
        refine ⟨hlen', ?_, ?_⟩
        · rw [store_read_write_ne st
            (fun heq => (netSlotW_ne_slotWord hjb hawlt) heq.symm)]
          exact hlslot'
        · intro j'' hj''
          have hkey'' : (BitVec.ofNat 256 j'').toNat < keyBound := by
            simp only [keyBound] at hlen' ⊢
            rw [BitVec.toNat_ofNat]
            omega
          rw [store_read_write_ne st
            (fun heq =>
              (netSlotW_ne_mapSlotW hjb hkey'' hawlt) heq.symm)]
          exact helems' j'' hj''
  net := by
    intro a' ha0' hab'
    have hawlt : aw.toNat < keyBound := by
      simp only [keyBoundI] at hab
      simp only [keyBound]
      omega
    have hkey' : (BitVec.ofNat 256 a'.toNat).toNat < keyBound := by
      simp only [keyBoundI] at hab'
      simp only [keyBound]
      rw [BitVec.toNat_ofNat]
      omega
    by_cases haa : a' = a
    · subst haa
      obtain ⟨h1, h2, h3⟩ := h.net a' ha0' hab'
      have hget : (s.setNet a' (s.getNet a' - amt)).getNet a'
          = s.getNet a' - amt := by
        simp [State.getNet, State.setNet, lookupBy_setBy_self]
      rw [hget]
      have hawq : BitVec.ofNat 256 a'.toNat = aw := by
        apply BitVec.toNat_inj.mp
        rw [BitVec.toNat_ofNat]
        simp only [keyBoundI] at hab'
        omega
      rw [hawq] at h3 ⊢
      refine ⟨by omega, by omega, ?_⟩
      rw [store_read_write_self, h3]
      apply BitVec.toNat_inj.mp
      rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
      simp only [wordSizeI] at h2
      omega
    · obtain ⟨h1, h2, h3⟩ := h.net a' ha0' hab'
      have hget : (s.setNet a (s.getNet a - amt)).getNet a'
          = s.getNet a' := by
        simp [State.getNet, State.setNet, lookupBy_setBy_ne haa]
      rw [hget]
      refine ⟨h1, h2, ?_⟩
      have hne : netSlotW (BitVec.ofNat 256 a'.toNat)
          ≠ netSlotW aw := by
        intro heq
        have heq2 := netSlotW_inj hkey' hawlt heq
        apply haa
        have h4 := congrArg BitVec.toNat heq2
        rw [BitVec.toNat_ofNat] at h4
        simp only [keyBoundI] at hab'
        omega
      rw [store_read_write_ne st hne]
      exact h3
  balance := by
    obtain ⟨h1, h2, h3⟩ := h.balance
    have hawlt : aw.toNat < keyBound := by
      simp only [keyBoundI] at hab
      simp only [keyBound]
      omega
    refine ⟨h1, h2, ?_⟩
    rw [store_read_write_ne st (balanceSlotW_ne_netSlotW hawlt)]
    exact h3
  layoutNodup := h.layoutNodup
  layoutSmall := h.layoutSmall

/-- Debiting the contract balance (machine: `SSTORE` at `balanceSlotW`)
preserves the representation when the balance covers the amount. -/
theorem ReprState.debitBalance {L Γ : List Name} {s : State} {σ : List Word}
    {st : Store} (h : ReprState L Γ s σ st)
    {amt : Int} (hamt0 : 0 ≤ amt) (hbal : amt ≤ s.selfBalance)
    {amtw : Word} (hamtw : amt = (amtw.toNat : Int)) :
    ReprState L Γ { s with selfBalance := s.selfBalance - amt } σ
      (st.write balanceSlotW (st.read balanceSlotW - amtw)) where
  len := h.len
  nodup := h.nodup
  disj := h.disj
  locals := by
    intro j n hj
    obtain ⟨v', w', henv, hσ, hrv⟩ := h.locals j n hj
    exact ⟨v', w', henv, hσ, hrv⟩
  rootsEnv := by
    intro n hn
    exact h.rootsEnv n hn
  roots := by
    intro j n hj
    obtain ⟨hjlt, -⟩ := List.getElem?_eq_some_iff.mp hj
    have hjb : j < layoutBound := by
      have := h.layoutSmall; omega
    obtain ⟨sv, hst', hroot⟩ := h.roots j n hj
    refine ⟨sv, hst', ?_⟩
    cases sv with
    | prim pv =>
        cases pv <;>
          (simp only [ReprRoot] at hroot ⊢
           rw [store_read_write_ne st
             (fun heq => (balanceSlotW_ne_slotWord hjb) heq.symm)]
           exact hroot)
    | map entries dflt =>
        simp only [ReprRoot] at hroot ⊢
        intro k' hk0' hkb'
        have hkey' : (BitVec.ofNat 256 k'.toNat).toNat < keyBound := by
          simp only [keyBoundI] at hkb'
          simp only [keyBound]
          rw [BitVec.toNat_ofNat]
          omega
        rw [store_read_write_ne st
          (fun heq => (balanceSlotW_ne_mapSlotW hjb hkey') heq.symm)]
        exact hroot k' hk0' hkb'
    | struct sfields =>
        simp only [ReprRoot] at hroot ⊢
        obtain ⟨hlenS, hflds⟩ := hroot
        refine ⟨hlenS, ?_⟩
        intro j'' hj''
        have hkey'' : (BitVec.ofNat 256 j'').toNat < keyBound := by
          simp only [keyBound] at hlenS ⊢
          rw [BitVec.toNat_ofNat]
          omega
        rw [store_read_write_ne st
          (fun heq => (balanceSlotW_ne_mapSlotW hjb hkey'') heq.symm)]
        exact hflds j'' hj''
    | array elems =>
        simp only [ReprRoot] at hroot ⊢
        obtain ⟨hlen', hlslot', helems'⟩ := hroot
        refine ⟨hlen', ?_, ?_⟩
        · rw [store_read_write_ne st
            (fun heq => (balanceSlotW_ne_slotWord hjb) heq.symm)]
          exact hlslot'
        · intro j'' hj''
          have hkey'' : (BitVec.ofNat 256 j'').toNat < keyBound := by
            simp only [keyBound] at hlen' ⊢
            rw [BitVec.toNat_ofNat]
            omega
          rw [store_read_write_ne st
            (fun heq => (balanceSlotW_ne_mapSlotW hjb hkey'') heq.symm)]
          exact helems' j'' hj''
  net := by
    intro a ha0 hab
    obtain ⟨h1, h2, h3⟩ := h.net a ha0 hab
    have hkey : (BitVec.ofNat 256 a.toNat).toNat < keyBound := by
      simp only [keyBoundI] at hab
      simp only [keyBound]
      rw [BitVec.toNat_ofNat]
      omega
    refine ⟨h1, h2, ?_⟩
    rw [store_read_write_ne st
      (fun heq => (balanceSlotW_ne_netSlotW hkey) heq.symm)]
    exact h3
  balance := by
    obtain ⟨h1, h2, h3⟩ := h.balance
    dsimp only
    simp only [wordSizeI] at h2 ⊢
    refine ⟨by omega, by omega, ?_⟩
    rw [store_read_write_self, h3]
    apply BitVec.toNat_inj.mp
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    have hsb : s.selfBalance.toNat % 2 ^ 256 = s.selfBalance.toNat :=
      Nat.mod_eq_of_lt (by omega)
    have hsb' : (s.selfBalance - amt).toNat % 2 ^ 256 =
        (s.selfBalance - amt).toNat :=
      Nat.mod_eq_of_lt (by omega)
    rw [hsb, hsb']
    have hw : amtw.toNat < 2 ^ 256 := amtw.isLt
    omega
  layoutNodup := h.layoutNodup
  layoutSmall := h.layoutSmall

/-- Reading local `i` under `t` temporaries: the word sits at stack
position `t + i`. -/
theorem ReprState.read_local {L Γ : List Name} {s : State}
    {σ : List Word} {st : Store} (h : ReprState L Γ s σ st) {i : Nat}
    {name : Name} (hidx : Γ[i]? = some name) {σt : List Word} {t : Nat}
    (ht : σt.length = t) :
    ∃ v, ∃ w : Word, lookupBy name s.env = some (Binding.val v) ∧
      (σt ++ σ)[t + i]? = some w ∧ ReprVal v w := by
  obtain ⟨v, w, henv, hσ, hrv⟩ := h.locals i name hidx
  refine ⟨v, w, henv, ?_, hrv⟩
  rw [List.getElem?_append_right (by omega)]
  have : t + i - σt.length = i := by omega
  rw [this]
  exact hσ

/-! ## The expression claim -/

/-- What the compiled code of an expression guarantees, keyed on the
bounded evaluator's outcome: a value pushes its representing word and
control falls through to the end of the fragment; a revert reaches a
`REVERT`; `.stuck` claims nothing. -/
def EvalClaim (C : Code) (base len : Nat) (σf : List Word) (st : Store) :
    Res Value → Prop
  | .ok v => ∃ w, ReprVal v w ∧
      Steps C ⟨base, σf, st⟩ ⟨base + len, w :: σf, st⟩
  | .error .revert => Reverting C ⟨base, σf, st⟩
  | .error .stuck => True

@[simp] theorem EvalClaim_ok {C : Code} {base len : Nat} {σf : List Word}
    {st : Store} {v : Value} :
    EvalClaim C base len σf st (.ok v) ↔
      ∃ w, ReprVal v w ∧
        Steps C ⟨base, σf, st⟩ ⟨base + len, w :: σf, st⟩ := Iff.rfl

@[simp] theorem EvalClaim_revert {C : Code} {base len : Nat}
    {σf : List Word} {st : Store} :
    EvalClaim C base len σf st (.error .revert) ↔
      Reverting C ⟨base, σf, st⟩ := Iff.rfl

@[simp] theorem EvalClaim_stuck {C : Code} {base len : Nat}
    {σf : List Word} {st : Store} :
    EvalClaim C base len σf st (.error .stuck) := trivial

/-- Push a claim through the checked-arithmetic mirror at the tail of
`evalW`'s operator arms: a failed check is `.stuck` (no claim), a passed
check returns the value unchanged. -/
theorem EvalClaim_checkArithW {C : Code} {base len : Nat} {σf : List Word}
    {st : Store} {ty : Ty} {v : Value}
    (h : checkArith ty v = .ok v -> EvalClaim C base len σf st (.ok v)) :
    EvalClaim C base len σf st
      ((Except.ok v : Res Value) >>= fun x => checkArithW ty x) := by
  show EvalClaim C base len σf st (checkArithW ty v)
  cases hchk : checkArith ty v with
  | error e =>
      rw [checkArithW, hchk]
      exact EvalClaim_stuck
  | ok w =>
      rw [checkArithW, hchk]
      have hw : w = v := checkArith_ok_eq hchk
      subst hw
      exact h hchk

/-! ## Strict binary operators -/

/-- Inversion of the uint256 bound check on an integer result. Kept as
a standalone lemma: inlining the `split` into larger proofs makes the
kernel recurse deeply on the `2^256` bound. -/
theorem checkW_int_inv {n : Int} {v : Value}
    (h : checkW (Value.int n) = .ok v) :
    v = Value.int n ∧ 0 ≤ n ∧ n < wordSizeI := by
  simp only [checkW] at h
  split at h
  case isTrue hr =>
      refine ⟨?_, hr⟩
      cases h
      rfl
  case isFalse => exact absurd h (by simp)

/-- A strict operator's `applyBinOpW` never reverts (only `/` and `%`
revert, and those compile through the guarded scheme instead). -/
theorem strictOp_no_revert {op : BinOp} {tail : Code}
    (hop : strictOpCode op = some tail) {lv rv : Value} :
    applyBinOpW op lv rv ≠ .error .revert := by
  intro h
  have hab := applyBinOpW_revert h
  cases op <;>
    first
    | ((cases lv <;> cases rv <;>
        (simp only [applyBinOp, Value.asInt, Value.asBool, bind,
            Except.bind, pure, Except.pure] at hab <;>
          (try split at hab) <;> simp_all)) <;> done)
    | simp [strictOpCode] at hop

/-- The word-level content of a comparison: two `decide`s agree when
the compared propositions are equivalent. -/
theorem wBool_congr {p q : Prop} [Decidable p] [Decidable q]
    (h : p ↔ q) : wBool (decide p) = wBool (decide q) := by
  rw [decide_eq_decide.mpr h]

/-- Simulation of a strict operator's instruction tail: from the two
operand words (right on top), the tail computes the word of the
`applyBinOpW` result. -/
theorem strictOp_sim {op : BinOp} {tail : Code}
    (hop : strictOpCode op = some tail) {C : Code} {base : Nat}
    (hcode : codeAt C base tail) {σ : List Word} {st : Store}
    {lv rv v : Value} {wl wr : Word}
    (hl : ReprVal lv wl) (hr : ReprVal rv wr)
    (hab : applyBinOpW op lv rv = .ok v) :
    ∃ w, ReprVal v w ∧
      Steps C ⟨base, wr :: wl :: σ, st⟩
        ⟨base + tail.length, w :: σ, st⟩ := by
  cases op with
  | add =>
      simp only [strictOpCode, Option.some.injEq] at hop
      subst hop
      cases lv with
      | bool b =>
          simp [applyBinOpW, applyBinOp, Value.asInt, bind,
            Except.bind] at hab
      | int a =>
        cases rv with
        | bool b =>
            simp [applyBinOpW, applyBinOp, Value.asInt, bind,
              Except.bind] at hab
        | int b =>
            simp only [ReprVal] at hl hr
            simp only [applyBinOpW, applyBinOp, Value.asInt, bind,
              Except.bind, pure, Except.pure, BinOp.isArith,
              if_true] at hab
            obtain ⟨rfl, h0, h1⟩ := checkW_int_inv hab
            refine ⟨wr + wl, ?_, ?_⟩
            · simp only [ReprVal]
              rw [BitVec.toNat_add]
              simp only [wordSizeI] at h1
              omega
            · simpa using Steps.single (Step.add hcode.fetch)
  | sub =>
      simp only [strictOpCode, Option.some.injEq] at hop
      subst hop
      cases lv with
      | bool b =>
          simp [applyBinOpW, applyBinOp, Value.asInt, bind,
            Except.bind] at hab
      | int a =>
        cases rv with
        | bool b =>
            simp [applyBinOpW, applyBinOp, Value.asInt, bind,
              Except.bind] at hab
        | int b =>
            simp only [ReprVal] at hl hr
            subst hl hr
            simp only [applyBinOpW, applyBinOp, Value.asInt, bind,
              Except.bind, pure, Except.pure, BinOp.isArith,
              if_true] at hab
            obtain ⟨rfl, h0, h1⟩ := checkW_int_inv hab
            refine ⟨wl - wr, ?_, ?_⟩
            · simp only [ReprVal, BitVec.toNat_sub]
              simp only [wordSizeI] at h1
              omega
            · refine Steps.head (Step.swap hcode.fetch rfl rfl) ?_
              simpa using Steps.single (Step.sub (hcode.tail).fetch)
  | mul =>
      simp only [strictOpCode, Option.some.injEq] at hop
      subst hop
      cases lv with
      | bool b =>
          simp [applyBinOpW, applyBinOp, Value.asInt, bind,
            Except.bind] at hab
      | int a =>
        cases rv with
        | bool b =>
            simp [applyBinOpW, applyBinOp, Value.asInt, bind,
              Except.bind] at hab
        | int b =>
            simp only [ReprVal] at hl hr
            simp only [applyBinOpW, applyBinOp, Value.asInt, bind,
              Except.bind, pure, Except.pure, BinOp.isArith,
              if_true] at hab
            obtain ⟨rfl, h0, h1⟩ := checkW_int_inv hab
            refine ⟨wr * wl, ?_, ?_⟩
            · simp only [ReprVal]
              rw [BitVec.toNat_mul]
              rw [hl, hr] at h1 ⊢
              simp only [wordSizeI] at h1
              have hcast : ((wl.toNat * wr.toNat : Nat) : Int) =
                  ((wl.toNat : Nat) : Int) * ((wr.toNat : Nat) : Int) := by
                simp
              rw [← hcast] at h1
              rw [Nat.mul_comm wr.toNat wl.toNat, ← hcast]
              omega
            · simpa using Steps.single (Step.mul hcode.fetch)
  | pow =>
      simp only [strictOpCode, Option.some.injEq] at hop
      subst hop
      cases lv with
      | bool b =>
          simp [applyBinOpW, applyBinOp, Value.asInt, bind,
            Except.bind] at hab
      | int a =>
        cases rv with
        | bool b =>
            simp [applyBinOpW, applyBinOp, Value.asInt, bind,
              Except.bind] at hab
        | int b =>
            simp only [ReprVal] at hl hr
            subst hl hr
            have hnn : ¬((wr.toNat : Int) < 0) := by omega
            simp only [applyBinOpW, applyBinOp, Value.asInt, bind,
              Except.bind, pure, Except.pure, BinOp.isArith, if_true,
              hnn, if_false, Int.toNat_natCast] at hab
            obtain ⟨rfl, h0, h1⟩ := checkW_int_inv hab
            refine ⟨wExp wl wr, ?_, ?_⟩
            · simp only [ReprVal, wExp, BitVec.toNat_ofNat]
              simp only [wordSizeI] at h1
              have hcast : ((wl.toNat ^ wr.toNat : Nat) : Int) =
                  ((wl.toNat : Nat) : Int) ^ wr.toNat := by
                simp
              rw [← hcast] at h1
              rw [← hcast]
              omega
            · refine Steps.head (Step.swap hcode.fetch rfl rfl) ?_
              simpa using Steps.single (Step.exp (hcode.tail).fetch)
  | lt =>
      simp only [strictOpCode, Option.some.injEq] at hop
      subst hop
      cases lv with
      | bool b =>
          simp [applyBinOpW, applyBinOp, Value.asInt, bind,
            Except.bind] at hab
      | int a =>
        cases rv with
        | bool b =>
            simp [applyBinOpW, applyBinOp, Value.asInt, bind,
              Except.bind] at hab
        | int b =>
            simp only [ReprVal] at hl hr
            subst hl hr
            simp only [applyBinOpW, applyBinOp, Value.asInt, bind,
              Except.bind, pure, Except.pure, BinOp.isArith, isEqOp,
              Bool.false_and, if_false] at hab
            cases hab
            refine ⟨wBool (wl.ult wr), ?_, ?_⟩
            · simp only [ReprVal]
              have hult : wl.ult wr =
                  decide ((wl.toNat : Int) < (wr.toNat : Int)) := by
                simp only [BitVec.ult]
                rw [decide_eq_decide]
                omega
              rw [hult]
            · simpa using Steps.single (Step.gt hcode.fetch)
  | gt =>
      simp only [strictOpCode, Option.some.injEq] at hop
      subst hop
      cases lv with
      | bool b =>
          cases rv <;>
            simp [applyBinOpW, applyBinOp, Value.asInt, bind,
              Except.bind] at hab
      | int a =>
        cases rv with
        | bool b =>
            simp [applyBinOpW, applyBinOp, Value.asInt, bind,
              Except.bind] at hab
        | int b =>
            simp only [ReprVal] at hl hr
            subst hl hr
            simp only [applyBinOpW, applyBinOp, Value.asInt, bind,
              Except.bind, pure, Except.pure, BinOp.isArith, isEqOp,
              Bool.false_and, if_false] at hab
            cases hab
            refine ⟨wBool (wr.ult wl), ?_, ?_⟩
            · simp only [ReprVal]
              have hult : wr.ult wl =
                  decide ((wr.toNat : Int) < (wl.toNat : Int)) := by
                simp only [BitVec.ult]
                rw [decide_eq_decide]
                omega
              rw [hult]
            · simpa using Steps.single (Step.lt hcode.fetch)
  | le =>
      simp only [strictOpCode, Option.some.injEq] at hop
      subst hop
      cases lv with
      | bool b =>
          simp [applyBinOpW, applyBinOp, Value.asInt, bind,
            Except.bind] at hab
      | int a =>
        cases rv with
        | bool b =>
            simp [applyBinOpW, applyBinOp, Value.asInt, bind,
              Except.bind] at hab
        | int b =>
            simp only [ReprVal] at hl hr
            subst hl hr
            simp only [applyBinOpW, applyBinOp, Value.asInt, bind,
              Except.bind, pure, Except.pure, BinOp.isArith, isEqOp,
              Bool.false_and, if_false] at hab
            cases hab
            refine ⟨wBool (decide (wBool (wr.ult wl) = 0)), ?_, ?_⟩
            · simp only [ReprVal]
              rw [iszero_wBool]
              have hult : wr.ult wl =
                  decide ((wr.toNat : Int) < (wl.toNat : Int)) := by
                simp only [BitVec.ult]
                rw [decide_eq_decide]
                omega
              rw [hult, ← decide_not]
              exact wBool_congr (by omega)
            · refine Steps.head (Step.lt hcode.fetch) ?_
              simpa using Steps.single (Step.iszero (hcode.tail).fetch)
  | ge =>
      simp only [strictOpCode, Option.some.injEq] at hop
      subst hop
      cases lv with
      | bool b =>
          cases rv <;>
            simp [applyBinOpW, applyBinOp, Value.asInt, bind,
              Except.bind] at hab
      | int a =>
        cases rv with
        | bool b =>
            simp [applyBinOpW, applyBinOp, Value.asInt, bind,
              Except.bind] at hab
        | int b =>
            simp only [ReprVal] at hl hr
            subst hl hr
            simp only [applyBinOpW, applyBinOp, Value.asInt, bind,
              Except.bind, pure, Except.pure, BinOp.isArith, isEqOp,
              Bool.false_and, if_false] at hab
            cases hab
            refine ⟨wBool (decide (wBool (wl.ult wr) = 0)), ?_, ?_⟩
            · simp only [ReprVal]
              rw [iszero_wBool]
              have hult : wl.ult wr =
                  decide ((wl.toNat : Int) < (wr.toNat : Int)) := by
                simp only [BitVec.ult]
                rw [decide_eq_decide]
                omega
              rw [hult, ← decide_not]
              exact wBool_congr (by omega)
            · refine Steps.head (Step.gt hcode.fetch) ?_
              simpa using Steps.single (Step.iszero (hcode.tail).fetch)
  | eqB =>
      simp only [strictOpCode, Option.some.injEq] at hop
      subst hop
      cases hshape : sameShape lv rv with
      | false =>
          simp [applyBinOpW, applyBinOp, bind, Except.bind, pure,
            Except.pure, BinOp.isArith, isEqOp, hshape] at hab
      | true =>
        simp only [applyBinOpW, applyBinOp, bind, Except.bind, pure,
          Except.pure] at hab
        rw [if_neg (by simp [BinOp.isArith]),
          if_neg (by simp [isEqOp, hshape])] at hab
        cases hab
        cases lv with
        | int a =>
            cases rv with
            | bool q => simp [sameShape] at hshape
            | int b =>
                simp only [ReprVal] at hl hr
                subst hl hr
                refine ⟨wBool (decide (wr = wl)), ?_, ?_⟩
                · simp only [ReprVal]
                  refine wBool_congr ?_
                  simp only [PrimVal.int.injEq]
                  rw [← BitVec.toNat_inj]
                  omega
                · simpa using Steps.single (Step.eq hcode.fetch)
        | bool p =>
            cases rv with
            | int b => simp [sameShape] at hshape
            | bool q =>
                simp only [ReprVal] at hl hr
                subst hl hr
                refine ⟨wBool (decide (wBool q = wBool p)), ?_, ?_⟩
                · simp only [ReprVal]
                  refine wBool_congr ?_
                  cases p <;> cases q <;>
                    simp [wBool, one_ne_zero_word, Ne.symm one_ne_zero_word]
                · simpa using Steps.single (Step.eq hcode.fetch)
  | neB =>
      simp only [strictOpCode, Option.some.injEq] at hop
      subst hop
      cases hshape : sameShape lv rv with
      | false =>
          simp [applyBinOpW, applyBinOp, bind, Except.bind, pure,
            Except.pure, BinOp.isArith, isEqOp, hshape] at hab
      | true =>
        simp only [applyBinOpW, applyBinOp, bind, Except.bind, pure,
          Except.pure] at hab
        rw [if_neg (by simp [BinOp.isArith]),
          if_neg (by simp [isEqOp, hshape])] at hab
        cases hab
        cases lv with
        | int a =>
            cases rv with
            | bool q => simp [sameShape] at hshape
            | int b =>
                simp only [ReprVal] at hl hr
                subst hl hr
                refine ⟨wBool (decide (wBool (decide (wr = wl)) = 0)), ?_, ?_⟩
                · simp only [ReprVal]
                  rw [iszero_wBool]
                  have heq : decide (wr = wl) =
                      decide (Value.int (wl.toNat : Int) =
                        Value.int (wr.toNat : Int)) := by
                    rw [decide_eq_decide]
                    simp only [PrimVal.int.injEq]
                    rw [← BitVec.toNat_inj]
                    omega
                  rw [heq]
                · refine Steps.head (Step.eq hcode.fetch) ?_
                  simpa using Steps.single (Step.iszero (hcode.tail).fetch)
        | bool p =>
            cases rv with
            | int b => simp [sameShape] at hshape
            | bool q =>
                simp only [ReprVal] at hl hr
                subst hl hr
                refine ⟨wBool (decide (wBool (decide (wBool q = wBool p)) = 0)),
                  ?_, ?_⟩
                · simp only [ReprVal]
                  rw [iszero_wBool]
                  have heq : decide (wBool q = wBool p) =
                      decide (Value.bool p = Value.bool q) := by
                    rw [decide_eq_decide]
                    cases p <;> cases q <;>
                      simp [wBool, one_ne_zero_word, Ne.symm one_ne_zero_word]
                  rw [heq]
                · refine Steps.head (Step.eq hcode.fetch) ?_
                  simpa using Steps.single (Step.iszero (hcode.tail).fetch)
  | div => simp [strictOpCode] at hop
  | mod => simp [strictOpCode] at hop
  | and => simp [strictOpCode] at hop
  | or => simp [strictOpCode] at hop

/-! ## Guarded division and modulus -/

/-- A non-short-circuiting operator never takes a `scArm` shortcut. -/
theorem scArm_of_not_sc {op : BinOp} (h : op.shortCircuits = false)
    (lv : Value) : scArm op lv = none := by
  cases op <;> cases lv <;>
    first
    | rfl
    | (rename_i b; cases b <;> rfl)
    | simp [BinOp.shortCircuits] at h

theorem applyBinOpW_div_ok {lv rv v : Value}
    (h : applyBinOpW .div lv rv = .ok v) :
    ∃ a b : Int, lv = Value.int a ∧ rv = Value.int b ∧ ¬(b = 0) ∧
      v = Value.int (Int.tdiv a b) := by
  cases lv with
  | bool p =>
      cases rv with
      | bool q =>
          simp [applyBinOpW, applyBinOp, Value.asInt, bind,
            Except.bind] at h
      | int b =>
          by_cases hb : b = 0 <;>
            simp [applyBinOpW, applyBinOp, Value.asInt, bind,
              Except.bind, hb] at h
  | int a =>
      cases rv with
      | bool q =>
          simp [applyBinOpW, applyBinOp, Value.asInt, bind,
            Except.bind] at h
      | int b =>
          by_cases hb : b = 0
          · simp [applyBinOpW, applyBinOp, Value.asInt, bind,
              Except.bind, hb] at h
          · simp only [applyBinOpW, applyBinOp, Value.asInt, bind,
              Except.bind, pure, Except.pure, BinOp.isArith, if_true,
              hb, if_false] at h
            obtain ⟨hv, -, -⟩ := checkW_int_inv h
            exact ⟨a, b, rfl, rfl, hb, hv⟩

theorem applyBinOpW_div_revert {lv rv : Value}
    (h : applyBinOpW .div lv rv = .error .revert) :
    rv = Value.int 0 := by
  cases rv with
  | bool q =>
      cases lv <;>
        simp [applyBinOpW, applyBinOp, Value.asInt, bind,
          Except.bind] at h
  | int b =>
      cases lv with
      | bool p =>
          by_cases hb : b = 0
          · simp [hb]
          · simp [applyBinOpW, applyBinOp, Value.asInt, bind,
              Except.bind, hb] at h
      | int a =>
          by_cases hb : b = 0
          · simp [hb]
          · simp only [applyBinOpW, applyBinOp, Value.asInt, bind,
              Except.bind, pure, Except.pure, BinOp.isArith, if_true,
              hb, if_false] at h
            exact absurd h checkW_not_revert

theorem applyBinOpW_mod_ok {lv rv v : Value}
    (h : applyBinOpW .mod lv rv = .ok v) :
    ∃ a b : Int, lv = Value.int a ∧ rv = Value.int b ∧ ¬(b = 0) ∧
      v = Value.int (Int.tmod a b) := by
  cases lv with
  | bool p =>
      cases rv with
      | bool q =>
          simp [applyBinOpW, applyBinOp, Value.asInt, bind,
            Except.bind] at h
      | int b =>
          by_cases hb : b = 0 <;>
            simp [applyBinOpW, applyBinOp, Value.asInt, bind,
              Except.bind, hb] at h
  | int a =>
      cases rv with
      | bool q =>
          simp [applyBinOpW, applyBinOp, Value.asInt, bind,
            Except.bind] at h
      | int b =>
          by_cases hb : b = 0
          · simp [applyBinOpW, applyBinOp, Value.asInt, bind,
              Except.bind, hb] at h
          · simp only [applyBinOpW, applyBinOp, Value.asInt, bind,
              Except.bind, pure, Except.pure, BinOp.isArith, if_true,
              hb, if_false] at h
            obtain ⟨hv, -, -⟩ := checkW_int_inv h
            exact ⟨a, b, rfl, rfl, hb, hv⟩

theorem applyBinOpW_mod_revert {lv rv : Value}
    (h : applyBinOpW .mod lv rv = .error .revert) :
    rv = Value.int 0 := by
  cases rv with
  | bool q =>
      cases lv <;>
        simp [applyBinOpW, applyBinOp, Value.asInt, bind,
          Except.bind] at h
  | int b =>
      cases lv with
      | bool p =>
          by_cases hb : b = 0
          · simp [hb]
          · simp [applyBinOpW, applyBinOp, Value.asInt, bind,
              Except.bind, hb] at h
      | int a =>
          by_cases hb : b = 0
          · simp [hb]
          · simp only [applyBinOpW, applyBinOp, Value.asInt, bind,
              Except.bind, pure, Except.pure, BinOp.isArith, if_true,
              hb, if_false] at h
            exact absurd h checkW_not_revert

/-- A word representing a non-zero integer is non-zero (guard taken). -/
theorem word_ne_zero_of_int {b : Int} {wr : Word}
    (hr : b = (wr.toNat : Int)) (hb : ¬(b = 0)) : wr ≠ 0 := by
  intro h0
  apply hb
  subst h0
  simpa using hr

/-- A word representing zero is zero (guard falls into the revert). -/
theorem word_eq_zero_of_int {wr : Word}
    (hr : (0 : Int) = (wr.toNat : Int)) : wr = 0 := by
  have h : wr.toNat = 0 := by omega
  apply BitVec.toNat_inj.mp
  simpa using h

theorem strictOpCode_not_sc {op : BinOp} {tail : Code}
    (h : strictOpCode op = some tail) : op.shortCircuits = false := by
  cases op <;> simp_all [strictOpCode, BinOp.shortCircuits]

theorem binopTail_not_sc {op : BinOp} {ty : Ty} {tail : Code}
    (h : binopTail op ty = some tail) : op.shortCircuits = false := by
  unfold binopTail at h
  split at h
  case isTrue huc =>
      obtain ⟨hop, _⟩ := uintChecked_cases huc
      rcases hop with rfl | rfl | rfl <;> rfl
  case isFalse => exact strictOpCode_not_sc h

/-! ## Overflow-checked `uint` operators -/

/-- Inversion of the official `uint` check on an integer result. -/
theorem checkArith_uint_int_ok {n : Int} {v : Value}
    (h : checkArith Ty.uint (Value.int n) = .ok v) :
    v = Value.int n ∧ 0 ≤ n ∧ n < uintBound := by
  simp only [checkArith] at h
  split at h
  case isTrue hr =>
      refine ⟨?_, hr⟩
      cases h
      rfl
  case isFalse => exact absurd h (by simp)

theorem checkArith_uint_int_revert {n : Int}
    (h : checkArith Ty.uint (Value.int n) = .error .revert) :
    ¬ (0 ≤ n ∧ n < uintBound) := by
  simp only [checkArith] at h
  split at h
  case isTrue => exact absurd h (by simp)
  case isFalse hr => exact hr

theorem wBool_or (a b : Bool) : wBool a ||| wBool b = wBool (a || b) := by
  cases a <;> cases b <;> rfl

theorem uintChecked_and (ty : Ty) : uintChecked .and ty = false := by
  cases ty with
  | prim pt => cases pt <;> rfl
  | ref rt => rfl

theorem uintChecked_or (ty : Ty) : uintChecked .or ty = false := by
  cases ty with
  | prim pt => cases pt <;> rfl
  | ref rt => rfl

theorem uintChecked_div (ty : Ty) : uintChecked .div ty = false := by
  cases ty with
  | prim pt => cases pt <;> rfl
  | ref rt => rfl

theorem uintChecked_mod (ty : Ty) : uintChecked .mod ty = false := by
  cases ty with
  | prim pt => cases pt <;> rfl
  | ref rt => rfl

/-- The checked operators on integer operands are the official
operation followed by the official `uint` check. -/
theorem applyCheckedW_add_uint (a b : Int) :
    applyCheckedW .add Ty.uint (Value.int a) (Value.int b) =
      checkArith Ty.uint (Value.int (a + b)) := by
  simp only [applyCheckedW, uintChecked, if_true, applyBinOp, Value.asInt,
    bind, Except.bind]

theorem applyCheckedW_sub_uint (a b : Int) :
    applyCheckedW .sub Ty.uint (Value.int a) (Value.int b) =
      checkArith Ty.uint (Value.int (a - b)) := by
  simp only [applyCheckedW, uintChecked, if_true, applyBinOp, Value.asInt,
    bind, Except.bind]

theorem applyCheckedW_mul_uint (a b : Int) :
    applyCheckedW .mul Ty.uint (Value.int a) (Value.int b) =
      checkArith Ty.uint (Value.int (a * b)) := by
  simp only [applyCheckedW, uintChecked, if_true, applyBinOp, Value.asInt,
    bind, Except.bind]

/-- A checked operator on a boolean operand is stuck. -/
theorem applyCheckedW_bool_stuck {op : BinOp} {ty : Ty}
    (huc : uintChecked op ty = true) {lv rv : Value}
    (h : (∃ b, lv = Value.bool b) ∨ (∃ b, rv = Value.bool b)) :
    applyCheckedW op ty lv rv = .error .stuck := by
  obtain ⟨hop, rfl⟩ := uintChecked_cases huc
  rcases h with ⟨b, hb⟩ | ⟨b, hb⟩
  · subst hb
    rcases hop with rfl | rfl | rfl <;> cases rv <;>
      simp [applyCheckedW, uintChecked, applyBinOp, Value.asInt, bind,
        Except.bind]
  · subst hb
    rcases hop with rfl | rfl | rfl <;> cases lv <;>
      simp [applyCheckedW, uintChecked, applyBinOp, Value.asInt, bind,
        Except.bind]

/-- The word-level multiplication overflow test of `checkedOpCode .mul`:
with `p = a * b mod 2^256`, `b = 0 ∨ p / b = a` holds exactly when the
product did not wrap. -/
theorem mul_overflow_iff {a b : Nat} :
    (b = 0 ∨ a * b % 2 ^ 256 / b = a) ↔ a * b < 2 ^ 256 := by
  constructor
  · rintro (rfl | h)
    · simp
    · by_cases hb0 : b = 0
      · subst hb0; simp
      · have h1 : a * b % 2 ^ 256 / b * b ≤ a * b % 2 ^ 256 :=
          Nat.div_mul_le_self _ _
        rw [h] at h1
        have h2 : a * b % 2 ^ 256 < 2 ^ 256 := Nat.mod_lt _ (by decide)
        omega
  · intro h
    by_cases hb0 : b = 0
    · exact Or.inl hb0
    · right
      rw [Nat.mod_eq_of_lt h]
      exact Nat.mul_div_cancel a (Nat.pos_of_ne_zero hb0)

/-- Simulation of an overflow-checked tail: from the two operand words
(right on top) it computes the word of the checked result, or reaches
`REVERT` exactly when the official `uint` check reverts. -/
theorem checkedOp_sim {op : BinOp} {ty : Ty}
    (huc : uintChecked op ty = true) {C : Code} {base : Nat}
    (hcode : codeAt C base (checkedOpCode op)) {σ : List Word} {st : Store}
    {lv rv : Value} {wl wr : Word}
    (hl : ReprVal lv wl) (hr : ReprVal rv wr) :
    (∀ v, applyCheckedW op ty lv rv = .ok v →
      ∃ w, ReprVal v w ∧
        Steps C ⟨base, wr :: wl :: σ, st⟩
          ⟨base + (checkedOpCode op).length, w :: σ, st⟩) ∧
    (applyCheckedW op ty lv rv = .error .revert →
      Reverting C ⟨base, wr :: wl :: σ, st⟩) := by
  obtain ⟨hop, rfl⟩ := uintChecked_cases huc
  have hwl := wl.isLt
  have hwr := wr.isLt
  rcases hop with rfl | rfl | rfl
  · -- `+`
    cases lv with
    | bool b =>
        rw [applyCheckedW_bool_stuck huc (Or.inl ⟨b, rfl⟩)]
        exact ⟨fun v hv => (nomatch hv), fun hv => (nomatch hv)⟩
    | int a =>
      cases rv with
      | bool b =>
          rw [applyCheckedW_bool_stuck huc (Or.inr ⟨b, rfl⟩)]
          exact ⟨fun v hv => (nomatch hv), fun hv => (nomatch hv)⟩
      | int b =>
        simp only [ReprVal] at hl hr
        subst hl hr
        rw [applyCheckedW_add_uint]
        simp only [checkedOpCode] at hcode ⊢
        have hpre : Steps C ⟨base, wr :: wl :: σ, st⟩
            ⟨base + 6, wBool (!(BitVec.ult (wl + wr) wl)) :: (wl + wr) :: σ,
             st⟩ := by
          refine Steps.head (Step.dup hcode.fetch rfl) ?_
          refine Steps.head (Step.add (hcode.tail).fetch) ?_
          refine Steps.head (Step.swap ((hcode.tail).tail).fetch rfl rfl) ?_
          refine Steps.head
            (Step.dup (((hcode.tail).tail).tail).fetch rfl) ?_
          refine Steps.head
            (Step.lt ((((hcode.tail).tail).tail).tail).fetch) ?_
          have hz := Step.iszero (a := wBool (BitVec.ult (wl + wr) wl))
            (σ := (wl + wr) :: σ) (st := st)
            (((((hcode.tail).tail).tail).tail).tail).fetch
          rw [iszero_wBool] at hz
          exact Steps.single hz
        have hult : BitVec.ult (wl + wr) wl =
            decide (2 ^ 256 ≤ wl.toNat + wr.toNat) := by
          simp only [BitVec.ult, BitVec.toNat_add]
          rw [decide_eq_decide]
          omega
        rw [hult] at hpre
        constructor
        · intro v hv
          obtain ⟨rfl, h0, h1⟩ := checkArith_uint_int_ok hv
          simp only [uintBound] at h1
          have hlt : wl.toNat + wr.toNat < 2 ^ 256 := by omega
          refine ⟨wl + wr, ?_, ?_⟩
          · simp only [ReprVal]
            rw [BitVec.toNat_add, Nat.mod_eq_of_lt hlt]
            omega
          · rw [decide_eq_false (by omega), Bool.not_false, wBool_true] at hpre
            refine Steps.trans hpre ?_
            refine Steps.cast_pc (Steps.single (Step.jumpiTrue
              ((((((hcode.tail).tail).tail).tail).tail).tail).fetch
              one_ne_zero_word)) ?_
            simp only [List.length_cons, List.length_nil] <;> omega
        · intro hrev
          have hn := checkArith_uint_int_revert hrev
          simp only [uintBound] at hn
          rw [decide_eq_true (by omega), Bool.not_true, wBool_false] at hpre
          refine ⟨⟨base + 6 + 1, (wl + wr) :: σ, st⟩, ?_, ?_⟩
          · refine Steps.trans hpre ?_
            exact Steps.single (Step.jumpiFalse
              ((((((hcode.tail).tail).tail).tail).tail).tail).fetch)
          · exact (((((((hcode.tail).tail).tail).tail).tail).tail).tail).fetch
  · -- `-`
    cases lv with
    | bool b =>
        rw [applyCheckedW_bool_stuck huc (Or.inl ⟨b, rfl⟩)]
        exact ⟨fun v hv => (nomatch hv), fun hv => (nomatch hv)⟩
    | int a =>
      cases rv with
      | bool b =>
          rw [applyCheckedW_bool_stuck huc (Or.inr ⟨b, rfl⟩)]
          exact ⟨fun v hv => (nomatch hv), fun hv => (nomatch hv)⟩
      | int b =>
        simp only [ReprVal] at hl hr
        subst hl hr
        rw [applyCheckedW_sub_uint]
        simp only [checkedOpCode] at hcode ⊢
        have hpre : Steps C ⟨base, wr :: wl :: σ, st⟩
            ⟨base + 4, wBool (!(BitVec.ult wl wr)) :: wr :: wl :: σ, st⟩ := by
          refine Steps.head (Step.dup hcode.fetch rfl) ?_
          refine Steps.head (Step.dup (hcode.tail).fetch rfl) ?_
          refine Steps.head (Step.gt ((hcode.tail).tail).fetch) ?_
          have hz := Step.iszero (a := wBool (BitVec.ult wl wr))
            (σ := wr :: wl :: σ) (st := st)
            (((hcode.tail).tail).tail).fetch
          rw [iszero_wBool] at hz
          exact Steps.single hz
        have hult : BitVec.ult wl wr = decide (wl.toNat < wr.toNat) := by
          simp only [BitVec.ult]
        rw [hult] at hpre
        constructor
        · intro v hv
          obtain ⟨rfl, h0, h1⟩ := checkArith_uint_int_ok hv
          refine ⟨wl - wr, ?_, ?_⟩
          · simp only [ReprVal]
            rw [BitVec.toNat_sub]
            have : (2 ^ 256 - wr.toNat + wl.toNat) % 2 ^ 256 =
                wl.toNat - wr.toNat := by omega
            rw [this]
            omega
          · rw [decide_eq_false (by omega), Bool.not_false, wBool_true] at hpre
            refine Steps.trans hpre ?_
            refine Steps.head (Step.jumpiTrue
              ((((hcode.tail).tail).tail).tail).fetch one_ne_zero_word) ?_
            refine Steps.head (Step.swap
              ((((((hcode.tail).tail).tail).tail).tail).tail).fetch rfl rfl) ?_
            refine Steps.cast_pc (Steps.single (Step.sub
              (((((((hcode.tail).tail).tail).tail).tail).tail).tail).fetch)) ?_
            simp only [List.length_cons, List.length_nil] <;> omega
        · intro hrev
          have hn := checkArith_uint_int_revert hrev
          simp only [uintBound] at hn
          rw [decide_eq_true (by omega), Bool.not_true, wBool_false] at hpre
          refine ⟨⟨base + 4 + 1, wr :: wl :: σ, st⟩, ?_, ?_⟩
          · refine Steps.trans hpre ?_
            exact Steps.single (Step.jumpiFalse
              ((((hcode.tail).tail).tail).tail).fetch)
          · exact (((((hcode.tail).tail).tail).tail).tail).fetch
  · -- `*`
    cases lv with
    | bool b =>
        rw [applyCheckedW_bool_stuck huc (Or.inl ⟨b, rfl⟩)]
        exact ⟨fun v hv => (nomatch hv), fun hv => (nomatch hv)⟩
    | int a =>
      cases rv with
      | bool b =>
          rw [applyCheckedW_bool_stuck huc (Or.inr ⟨b, rfl⟩)]
          exact ⟨fun v hv => (nomatch hv), fun hv => (nomatch hv)⟩
      | int b =>
        simp only [ReprVal] at hl hr
        subst hl hr
        rw [applyCheckedW_mul_uint]
        simp only [checkedOpCode] at hcode ⊢
        have hpre : Steps C ⟨base, wr :: wl :: σ, st⟩
            ⟨base + 11,
             wBool (decide (wr = 0) || decide ((wl * wr) / wr = wl)) ::
               (wl * wr) :: σ, st⟩ := by
          refine Steps.head (Step.dup hcode.fetch rfl) ?_
          refine Steps.head (Step.dup (hcode.tail).fetch rfl) ?_
          refine Steps.head (Step.mul ((hcode.tail).tail).fetch) ?_
          refine Steps.head
            (Step.swap (((hcode.tail).tail).tail).fetch rfl rfl) ?_
          refine Steps.head
            (Step.dup ((((hcode.tail).tail).tail).tail).fetch rfl) ?_
          refine Steps.head
            (Step.dup (((((hcode.tail).tail).tail).tail).tail).fetch rfl) ?_
          refine Steps.head
            (Step.div ((((((hcode.tail).tail).tail).tail).tail).tail).fetch)
            ?_
          refine Steps.head
            (Step.eq
              (((((((hcode.tail).tail).tail).tail).tail).tail).tail).fetch)
            ?_
          refine Steps.head
            (Step.swap
              ((((((((hcode.tail).tail).tail).tail).tail).tail).tail).tail).fetch
              rfl rfl) ?_
          refine Steps.head
            (Step.iszero
              (((((((((hcode.tail).tail).tail).tail).tail).tail).tail).tail).tail).fetch)
            ?_
          have ho := Step.or (a := wBool (decide (wr = 0)))
            (b := wBool (decide (BitVec.udiv (wl * wr) wr = wl)))
            (σ := (wl * wr) :: σ) (st := st)
            ((((((((((hcode.tail).tail).tail).tail).tail).tail).tail).tail).tail).tail).fetch
          rw [wBool_or] at ho
          exact Steps.single ho
        have hcond : (decide (wr = 0) || decide ((wl * wr) / wr = wl)) =
            decide (wl.toNat * wr.toNat < 2 ^ 256) := by
          rw [← Bool.decide_or, decide_eq_decide, ← mul_overflow_iff,
            BitVec.toNat_eq, BitVec.toNat_eq, BitVec.toNat_udiv,
            BitVec.toNat_mul]
          simp
        rw [hcond] at hpre
        constructor
        · intro v hv
          obtain ⟨rfl, h0, h1⟩ := checkArith_uint_int_ok hv
          simp only [uintBound] at h1
          have hlt : wl.toNat * wr.toNat < 2 ^ 256 := by omega
          refine ⟨wl * wr, ?_, ?_⟩
          · simp only [ReprVal]
            rw [BitVec.toNat_mul, Nat.mod_eq_of_lt hlt]
            omega
          · rw [decide_eq_true hlt, wBool_true] at hpre
            refine Steps.trans hpre ?_
            refine Steps.cast_pc (Steps.single (Step.jumpiTrue
              (((((((((((hcode.tail).tail).tail).tail).tail).tail).tail).tail).tail).tail).tail).fetch
              one_ne_zero_word)) ?_
            simp only [List.length_cons, List.length_nil] <;> omega
        · intro hrev
          have hn := checkArith_uint_int_revert hrev
          simp only [uintBound] at hn
          have hge : ¬ wl.toNat * wr.toNat < 2 ^ 256 := by omega
          rw [decide_eq_false hge, wBool_false] at hpre
          refine ⟨⟨base + 11 + 1, (wl * wr) :: σ, st⟩, ?_, ?_⟩
          · refine Steps.trans hpre ?_
            exact Steps.single (Step.jumpiFalse
              (((((((((((hcode.tail).tail).tail).tail).tail).tail).tail).tail).tail).tail).tail).fetch)
          · exact
              ((((((((((((hcode.tail).tail).tail).tail).tail).tail).tail).tail).tail).tail).tail).tail).fetch

/-- Simulation of `binopTail`: the checked tail for `uintChecked`
operators, the strict tail otherwise (which never reverts). -/
theorem binopTail_sim {op : BinOp} {ty : Ty} {tail : Code}
    (hop : binopTail op ty = some tail) {C : Code} {base : Nat}
    (hcode : codeAt C base tail) {σ : List Word} {st : Store}
    {lv rv : Value} {wl wr : Word}
    (hl : ReprVal lv wl) (hr : ReprVal rv wr) :
    (∀ v, applyCheckedW op ty lv rv = .ok v →
      ∃ w, ReprVal v w ∧
        Steps C ⟨base, wr :: wl :: σ, st⟩ ⟨base + tail.length, w :: σ, st⟩) ∧
    (applyCheckedW op ty lv rv = .error .revert →
      Reverting C ⟨base, wr :: wl :: σ, st⟩) := by
  unfold binopTail at hop
  split at hop
  case isTrue huc =>
      cases hop
      exact checkedOp_sim huc hcode hl hr
  case isFalse huc =>
      constructor
      · intro v hv
        simp only [applyCheckedW, huc, Bool.false_eq_true, if_false] at hv
        cases hab : applyBinOpW op lv rv with
        | error e => rw [hab] at hv; simp [bind, Except.bind] at hv
        | ok u =>
            rw [hab] at hv
            simp only [bind, Except.bind] at hv
            cases hc : checkArith (op.retTy ty) u with
            | error e => rw [checkArithW, hc] at hv; exact absurd hv (by simp)
            | ok w =>
                rw [checkArithW, hc] at hv
                cases hv
                have := checkArith_ok_eq hc
                subst this
                exact strictOp_sim hop hcode hl hr hab
      · intro hrev
        simp only [applyCheckedW, huc, Bool.false_eq_true, if_false] at hrev
        cases hab : applyBinOpW op lv rv with
        | error e =>
            rw [hab] at hrev
            simp only [bind, Except.bind, Except.error.injEq] at hrev
            subst hrev
            exact absurd hab (strictOp_no_revert hop)
        | ok u =>
            rw [hab] at hrev
            simp only [bind, Except.bind] at hrev
            cases hc : checkArith (op.retTy ty) u with
            | error e => rw [checkArithW, hc] at hrev; exact absurd hrev (by simp)
            | ok w => rw [checkArithW, hc] at hrev; exact absurd hrev (by simp)

/-! ## Expression simulation -/

theorem compileExpr_sim (L Γ : List Name) (t : Nat) (e : WrappedExpr)
    {code : Code} (hc : compileExpr L Γ t e = some code)
    (s : State) {C : Code} {base : Nat} (hcode : codeAt C base code)
    {σt σ : List Word} {st : Store} (ht : σt.length = t)
    (hrepr : ReprState L Γ s σ st) :
    EvalClaim C base code.length (σt ++ σ) st (evalW s e) := by
  match e with
  | .bool b =>
      simp only [compileExpr, Option.some.injEq] at hc
      subst hc
      simp only [evalW, EvalClaim_ok]
      refine ⟨wBool b, rfl, ?_⟩
      simpa using Steps.single (Step.push hcode.fetch)
  | .intLit ty n =>
      simp only [compileExpr] at hc
      split at hc
      case _ hn =>
        simp only [Option.some.injEq] at hc
        subst hc
        simp only [evalW, EvalClaim_ok]
        refine ⟨BitVec.ofNat 256 n.toNat, ?_, ?_⟩
        · simp only [ReprVal]
          rw [BitVec.toNat_ofNat]
          simp only [wordSizeI] at hn
          omega
        · simpa using Steps.single (Step.push hcode.fetch)
      case _ => exact Option.noConfusion hc
  | .var kind ty fld =>
      cases kind with
      | memory => simp [compileExpr] at hc
      | stack =>
          simp only [compileExpr] at hc
          split at hc
          case _ hprim =>
            cases hfi : Γ.findIdx? (· = fld.name) with
            | none => rw [hfi] at hc; exact Option.noConfusion hc
            | some i =>
                simp only [hfi] at hc
                split at hc
                case _ hdepth =>
                  simp only [Option.some.injEq] at hc
                  subst hc
                  obtain ⟨v, w, henv, hσ, hrv⟩ :=
                    hrepr.read_local (findIdx?_eq_name hfi) ht
                  simp only [evalW, henv, EvalClaim_ok]
                  refine ⟨w, hrv, ?_⟩
                  simpa using Steps.single (Step.dup hcode.fetch hσ)
                case _ => exact Option.noConfusion hc
          case _ => exact Option.noConfusion hc
      | storage =>
          simp only [compileExpr] at hc
          split at hc
          case _ hcond =>
            cases hslot : slotOf? L fld.name with
            | none => rw [hslot] at hc; exact Option.noConfusion hc
            | some i =>
                simp only [hslot, Option.some.injEq] at hc
                subst hc
                have hLidx : L[i]? = some fld.name :=
                  findIdx?_eq_name (by simpa [slotOf?] using hslot)
                have hmem : fld.name ∈ L := List.mem_of_getElem? hLidx
                have henv : lookupBy fld.name s.env = none :=
                  hrepr.rootsEnv _ hmem
                obtain ⟨sv, hst, hroot⟩ := hrepr.roots i fld.name hLidx
                cases sv with
                | struct fields =>
                    simp [evalW, henv, hcond.1, hst, SVal.asValue]
                | array elems =>
                    simp [evalW, henv, hcond.1, hst, SVal.asValue]
                | map entries dflt =>
                    simp [evalW, henv, hcond.1, hst, SVal.asValue]
                | prim pv =>
                    cases pv <;>
                      (simp only [ReprRoot] at hroot
                       simp only [evalW, henv, hcond.1, if_pos, hst,
                         SVal.asValue, EvalClaim_ok]
                       refine ⟨st.read (slotWord i), hroot, ?_⟩
                       refine Steps.head (Step.push hcode.fetch) ?_
                       simpa using Steps.single
                         (Step.sload (hcode.tail).fetch))
          case _ => exact Option.noConfusion hc
  | .mkUnop op arg =>
      cases op with
      | neg => simp [compileExpr] at hc
      | not =>
          simp only [compileExpr] at hc
          cases hca : compileExpr L Γ t arg with
          | none => rw [hca] at hc; simp [bind, Option.bind] at hc
          | some ca =>
              rw [hca] at hc
              simp only [bind, Option.bind, pure, Option.pure_def, Option.some.injEq] at hc
              subst hc
              have iha := compileExpr_sim L Γ t arg hca s
                hcode.append_left ht hrepr
              simp only [evalW]
              cases hv : evalW s arg with
              | error err =>
                  cases err
                  · rw [hv] at iha
                    simp only [EvalClaim_revert] at iha
                    simp only [hv, bind, Except.bind, EvalClaim_revert]
                    exact iha
                  · simp only [hv, bind, Except.bind]
                    exact EvalClaim_stuck
              | ok v =>
                  rw [hv] at iha
                  simp only [EvalClaim_ok] at iha
                  obtain ⟨w, hw, hsteps⟩ := iha
                  simp only [hv, bind, Except.bind]
                  cases v with
                  | int n =>
                      simp only [applyUnOp, Value.asBool, bind, Except.bind]
                      exact EvalClaim_stuck
                  | bool b =>
                      simp only [ReprVal] at hw
                      subst hw
                      simp only [applyUnOp, Value.asBool, bind, Except.bind,
                        pure, Except.pure, EvalClaim_ok]
                      refine ⟨wBool (decide (wBool b = 0)), ?_, ?_⟩
                      · simp only [ReprVal, iszero_wBool]
                      · refine Steps.trans hsteps ?_
                        refine Steps.cast_pc
                          (Steps.single
                            (Step.iszero (hcode.append_right).fetch)) ?_
                        simp
                        omega
  | .mkTernary c thn els =>
      simp only [compileExpr] at hc
      cases hcc : compileExpr L Γ t c with
      | none => rw [hcc] at hc; simp [bind, Option.bind] at hc
      | some cc =>
        rw [hcc] at hc
        simp only [bind, Option.bind] at hc
        cases hct : compileExpr L Γ t thn with
        | none => rw [hct] at hc; simp [bind, Option.bind] at hc
        | some ct =>
          rw [hct] at hc
          simp only [bind, Option.bind] at hc
          cases hce : compileExpr L Γ t els with
          | none => rw [hce] at hc; simp [bind, Option.bind] at hc
          | some ce =>
            rw [hce] at hc
            simp only [bind, Option.bind, pure, Option.pure_def, Option.some.injEq] at hc
            subst hc
            -- code = cc ++ [iszero, jumpi (ct.length+1)] ++ ct
            --          ++ [jump ce.length] ++ ce
            have hcodecc : codeAt C base cc :=
              (((hcode.append_left).append_left).append_left).append_left
            have hcodemid :
                codeAt C (base + cc.length)
                  [Instr.iszero, Instr.jumpi (ct.length + 1)] :=
              (((hcode.append_left).append_left).append_left).append_right
            have hcodect : codeAt C (base + cc.length + 2) ct :=
              codeAt_cast (((hcode.append_left).append_left).append_right)
                (by simp only [List.length_append, List.length_cons,
                  List.length_nil]; omega)
            have hcodejmp :
                codeAt C (base + cc.length + 2 + ct.length)
                  [Instr.jump ce.length] :=
              codeAt_cast ((hcode.append_left).append_right)
                (by simp only [List.length_append, List.length_cons,
                  List.length_nil]; omega)
            have hcodece :
                codeAt C (base + cc.length + 2 + ct.length + 1) ce :=
              codeAt_cast (hcode.append_right)
                (by simp only [List.length_append, List.length_cons,
                  List.length_nil]; omega)
            have ihc := compileExpr_sim L Γ t c hcc s hcodecc ht hrepr
            simp only [evalW]
            cases hv : evalW s c with
            | error err =>
                cases err
                · rw [hv] at ihc
                  simp only [EvalClaim_revert] at ihc
                  simp only [hv, bind, Except.bind, EvalClaim_revert]
                  exact ihc
                · simp only [hv, bind, Except.bind]
                  exact EvalClaim_stuck
            | ok cv =>
                rw [hv] at ihc
                simp only [EvalClaim_ok] at ihc
                obtain ⟨wc, hwc, hstepsc⟩ := ihc
                simp only [hv, bind, Except.bind]
                cases cv with
                | int n => exact EvalClaim_stuck
                | bool b =>
                    simp only [ReprVal] at hwc
                    subst hwc
                    cases b with
                    | true =>
                        have iht := compileExpr_sim L Γ t thn hct s
                          hcodect ht hrepr
                        cases hvt : evalW s thn with
                        | error err =>
                            cases err
                            · rw [hvt] at iht
                              simp only [EvalClaim_revert] at iht
                              simp only [hvt, EvalClaim_revert]
                              refine Reverting.of_steps ?_ iht
                              refine Steps.trans hstepsc ?_
                              refine Steps.head
                                (Step.iszero hcodemid.fetch) ?_
                              refine Steps.cast_pc (Steps.single
                                (Step.jumpiFalse
                                  (hcodemid.tail).fetch)) ?_
                              omega
                            · simp only [hvt]
                              exact EvalClaim_stuck
                        | ok tv =>
                            rw [hvt] at iht
                            simp only [EvalClaim_ok] at iht
                            obtain ⟨wt, hwt, hstepst⟩ := iht
                            simp only [hvt, EvalClaim_ok]
                            refine ⟨wt, hwt, ?_⟩
                            refine Steps.trans hstepsc ?_
                            refine Steps.head
                              (Step.iszero hcodemid.fetch) ?_
                            refine Steps.trans (Steps.cast_pc
                              (Steps.single (Step.jumpiFalse
                                (hcodemid.tail).fetch))
                              (show base + List.length cc + 1 + 1 =
                                base + List.length cc + 2 by omega)) ?_
                            refine Steps.trans hstepst ?_
                            refine Steps.cast_pc
                              (Steps.single (Step.jump hcodejmp.fetch)) ?_
                            simp [List.length_append]
                            omega
                    | false =>
                        have ihe := compileExpr_sim L Γ t els hce s
                          hcodece ht hrepr
                        have hjump : Steps C
                            ⟨base, σt ++ σ, st⟩
                            ⟨base + cc.length + 2 + ct.length + 1,
                              σt ++ σ, st⟩ := by
                          refine Steps.trans hstepsc ?_
                          refine Steps.head
                            (Step.iszero hcodemid.fetch) ?_
                          refine Steps.cast_pc (Steps.single
                            (Step.jumpiTrue (hcodemid.tail).fetch
                              (by simp [wBool, one_ne_zero_word]))) ?_
                          omega
                        cases hve : evalW s els with
                        | error err =>
                            cases err
                            · rw [hve] at ihe
                              simp only [EvalClaim_revert] at ihe
                              simp only [hve, EvalClaim_revert]
                              exact Reverting.of_steps hjump ihe
                            · simp only [hve]
                              exact EvalClaim_stuck
                        | ok ev =>
                            rw [hve] at ihe
                            simp only [EvalClaim_ok] at ihe
                            obtain ⟨we, hwe, hstepse⟩ := ihe
                            simp only [hve, EvalClaim_ok]
                            refine ⟨we, hwe, ?_⟩
                            refine Steps.trans hjump ?_
                            refine Steps.cast_pc hstepse ?_
                            simp [List.length_append]
                            omega
  | .mkBinop op l r =>
      cases op
      case and =>
        simp only [compileExpr] at hc
        cases hcl : compileExpr L Γ t l with
        | none => rw [hcl] at hc; simp [bind, Option.bind] at hc
        | some cl =>
          rw [hcl] at hc
          simp only [bind, Option.bind] at hc
          cases hcr : compileExpr L Γ t r with
          | none => rw [hcr] at hc; simp [bind, Option.bind] at hc
          | some cr =>
            rw [hcr] at hc
            simp only [bind, Option.bind, pure, Option.pure_def, Option.some.injEq] at hc
            subst hc
            -- code = cl ++ [dup 1, iszero, jumpi (cr.length+1), pop] ++ cr
            have hcodecl : codeAt C base cl :=
              (hcode.append_left).append_left
            have hcodemid : codeAt C (base + cl.length)
                [Instr.dup 1, Instr.iszero,
                 Instr.jumpi (cr.length + 1), Instr.pop] :=
              (hcode.append_left).append_right
            have hcodecr : codeAt C (base + cl.length + 4) cr :=
              codeAt_cast (hcode.append_right)
                (by simp only [List.length_append, List.length_cons,
                  List.length_nil]; omega)
            have ihl := compileExpr_sim L Γ t l hcl s hcodecl ht hrepr
            simp only [evalW]
            cases hlv : evalW s l with
            | error err =>
                cases err
                · rw [hlv] at ihl
                  simp only [EvalClaim_revert] at ihl
                  simp only [hlv, bind, Except.bind, EvalClaim_revert]
                  exact ihl
                · simp only [hlv, bind, Except.bind]
                  exact EvalClaim_stuck
            | ok lv =>
                rw [hlv] at ihl
                simp only [EvalClaim_ok] at ihl
                obtain ⟨wl, hwl, hstepsl⟩ := ihl
                simp only [hlv, bind, Except.bind]
                cases lv with
                | int n =>
                    simp only [scArm, BinOp.shortCircuits, isBoolV,
                      Bool.and_true, Bool.not_false]
                    exact EvalClaim_stuck
                | bool b =>
                    simp only [ReprVal] at hwl
                    subst hwl
                    cases b with
                    | false =>
                        simp only [scArm, EvalClaim_ok]
                        refine ⟨wBool false, rfl, ?_⟩
                        refine Steps.trans hstepsl ?_
                        refine Steps.head
                          (Step.dup hcodemid.fetch rfl) ?_
                        refine Steps.head
                          (Step.iszero (hcodemid.tail).fetch) ?_
                        refine Steps.cast_pc (Steps.single
                          (Step.jumpiTrue ((hcodemid.tail).tail).fetch
                            (by simp [wBool, one_ne_zero_word]))) ?_
                        simp [List.length_append]
                        omega
                    | true =>
                        simp only [scArm, BinOp.shortCircuits, isBoolV,
                          Bool.and_false, Bool.not_true, if_neg,
                          Bool.false_eq_true]
                        have hmid : Steps C
                            ⟨base, σt ++ σ, st⟩
                            ⟨base + cl.length + 4, σt ++ σ, st⟩ := by
                          refine Steps.trans hstepsl ?_
                          refine Steps.head
                            (Step.dup hcodemid.fetch rfl) ?_
                          refine Steps.head
                            (Step.iszero (hcodemid.tail).fetch) ?_
                          refine Steps.head
                            (Step.jumpiFalse
                              ((hcodemid.tail).tail).fetch) ?_
                          refine Steps.cast_pc (Steps.single
                            (Step.pop (((hcodemid.tail).tail).tail).fetch))
                            ?_
                          omega
                        have ihr := compileExpr_sim L Γ t r hcr s
                          hcodecr ht hrepr
                        cases hrv : evalW s r with
                        | error err =>
                            cases err
                            · rw [hrv] at ihr
                              simp only [EvalClaim_revert] at ihr
                              simp only [hrv, bind, Except.bind,
                                EvalClaim_revert]
                              exact Reverting.of_steps hmid ihr
                            · simp only [hrv, bind, Except.bind]
                              exact EvalClaim_stuck
                        | ok rv =>
                            rw [hrv] at ihr
                            simp only [EvalClaim_ok] at ihr
                            obtain ⟨wr, hwr, hstepsr⟩ := ihr
                            simp only [hrv, bind, Except.bind]
                            cases rv with
                            | int m =>
                                simp only [applyCheckedW, uintChecked_and,
                                  Bool.false_eq_true, if_false, applyBinOpW,
                                  applyBinOp, Value.asBool, bind, Except.bind]
                                exact EvalClaim_stuck
                            | bool q =>
                                simp only [ReprVal] at hwr
                                subst hwr
                                simp only [applyCheckedW, uintChecked_and,
                                  Bool.false_eq_true, if_false, applyBinOpW,
                                  applyBinOp, Value.asBool, bind, Except.bind,
                                  pure, Except.pure, BinOp.isArith, isEqOp,
                                  Bool.true_and, EvalClaim_ok]
                                refine ⟨wBool q, by simp [ReprVal], ?_⟩
                                refine Steps.trans hmid ?_
                                refine Steps.cast_pc hstepsr ?_
                                simp [List.length_append]
                                omega
      case or =>
        simp only [compileExpr] at hc
        cases hcl : compileExpr L Γ t l with
        | none => rw [hcl] at hc; simp [bind, Option.bind] at hc
        | some cl =>
          rw [hcl] at hc
          simp only [bind, Option.bind] at hc
          cases hcr : compileExpr L Γ t r with
          | none => rw [hcr] at hc; simp [bind, Option.bind] at hc
          | some cr =>
            rw [hcr] at hc
            simp only [bind, Option.bind, pure, Option.pure_def, Option.some.injEq] at hc
            subst hc
            -- code = cl ++ [dup 1, jumpi (cr.length+1), pop] ++ cr
            have hcodecl : codeAt C base cl :=
              (hcode.append_left).append_left
            have hcodemid : codeAt C (base + cl.length)
                [Instr.dup 1, Instr.jumpi (cr.length + 1), Instr.pop] :=
              (hcode.append_left).append_right
            have hcodecr : codeAt C (base + cl.length + 3) cr :=
              codeAt_cast (hcode.append_right)
                (by simp only [List.length_append, List.length_cons,
                  List.length_nil]; omega)
            have ihl := compileExpr_sim L Γ t l hcl s hcodecl ht hrepr
            simp only [evalW]
            cases hlv : evalW s l with
            | error err =>
                cases err
                · rw [hlv] at ihl
                  simp only [EvalClaim_revert] at ihl
                  simp only [hlv, bind, Except.bind, EvalClaim_revert]
                  exact ihl
                · simp only [hlv, bind, Except.bind]
                  exact EvalClaim_stuck
            | ok lv =>
                rw [hlv] at ihl
                simp only [EvalClaim_ok] at ihl
                obtain ⟨wl, hwl, hstepsl⟩ := ihl
                simp only [hlv, bind, Except.bind]
                cases lv with
                | int n =>
                    simp only [scArm, BinOp.shortCircuits, isBoolV,
                      Bool.and_true, Bool.not_false]
                    exact EvalClaim_stuck
                | bool b =>
                    simp only [ReprVal] at hwl
                    subst hwl
                    cases b with
                    | true =>
                        simp only [scArm, EvalClaim_ok]
                        refine ⟨wBool true, rfl, ?_⟩
                        refine Steps.trans hstepsl ?_
                        refine Steps.head
                          (Step.dup hcodemid.fetch rfl) ?_
                        refine Steps.cast_pc (Steps.single
                          (Step.jumpiTrue ((hcodemid.tail)).fetch
                            (by simp [wBool, one_ne_zero_word]))) ?_
                        simp [List.length_append]
                        omega
                    | false =>
                        simp only [scArm, BinOp.shortCircuits, isBoolV,
                          Bool.and_false, Bool.not_true, if_neg,
                          Bool.false_eq_true]
                        have hmid : Steps C
                            ⟨base, σt ++ σ, st⟩
                            ⟨base + cl.length + 3, σt ++ σ, st⟩ := by
                          refine Steps.trans hstepsl ?_
                          refine Steps.head
                            (Step.dup hcodemid.fetch rfl) ?_
                          refine Steps.head
                            (Step.jumpiFalse ((hcodemid.tail)).fetch) ?_
                          refine Steps.cast_pc (Steps.single
                            (Step.pop (((hcodemid.tail).tail)).fetch)) ?_
                          omega
                        have ihr := compileExpr_sim L Γ t r hcr s
                          hcodecr ht hrepr
                        cases hrv : evalW s r with
                        | error err =>
                            cases err
                            · rw [hrv] at ihr
                              simp only [EvalClaim_revert] at ihr
                              simp only [hrv, bind, Except.bind,
                                EvalClaim_revert]
                              exact Reverting.of_steps hmid ihr
                            · simp only [hrv, bind, Except.bind]
                              exact EvalClaim_stuck
                        | ok rv =>
                            rw [hrv] at ihr
                            simp only [EvalClaim_ok] at ihr
                            obtain ⟨wr, hwr, hstepsr⟩ := ihr
                            simp only [hrv, bind, Except.bind]
                            cases rv with
                            | int m =>
                                simp only [applyCheckedW, uintChecked_or,
                                  Bool.false_eq_true, if_false, applyBinOpW,
                                  applyBinOp, Value.asBool, bind, Except.bind]
                                exact EvalClaim_stuck
                            | bool q =>
                                simp only [ReprVal] at hwr
                                subst hwr
                                simp only [applyCheckedW, uintChecked_or,
                                  Bool.false_eq_true, if_false, applyBinOpW,
                                  applyBinOp, Value.asBool, bind, Except.bind,
                                  pure, Except.pure, BinOp.isArith, isEqOp,
                                  Bool.true_and, EvalClaim_ok]
                                refine ⟨wBool q, by simp [ReprVal], ?_⟩
                                refine Steps.trans hmid ?_
                                refine Steps.cast_pc hstepsr ?_
                                simp [List.length_append]
                                omega
      case div =>
        simp only [compileExpr] at hc
        cases hcl : compileExpr L Γ t l with
        | none => rw [hcl] at hc; simp [bind, Option.bind] at hc
        | some cl =>
          rw [hcl] at hc
          simp only [bind, Option.bind] at hc
          cases hcr : compileExpr L Γ (t + 1) r with
          | none => rw [hcr] at hc; simp [bind, Option.bind] at hc
          | some cr =>
            rw [hcr] at hc
            simp only [bind, Option.bind, pure, Option.pure_def, Option.some.injEq] at hc
            subst hc
            -- code = cl ++ cr ++ [dup 1, jumpi 1, revert, swap 1, div]
            have hcodecl : codeAt C base cl :=
              (hcode.append_left).append_left
            have hcodecr : codeAt C (base + cl.length) cr :=
              (hcode.append_left).append_right
            have hcodetail : codeAt C (base + cl.length + cr.length)
                [Instr.dup 1, Instr.jumpi 1, Instr.revert,
                 Instr.swap 1, Instr.div] :=
              codeAt_cast (hcode.append_right)
                (by simp only [List.length_append, List.length_cons,
                  List.length_nil]; omega)
            have ihl := compileExpr_sim L Γ t l hcl s hcodecl ht hrepr
            simp only [evalW,
              scArm_of_not_sc (op := BinOp.div) rfl,
              BinOp.shortCircuits, Bool.false_and, Bool.false_eq_true,
              if_false]
            cases hlv : evalW s l with
            | error err =>
                cases err
                · rw [hlv] at ihl
                  simp only [EvalClaim_revert] at ihl
                  simp only [hlv, bind, Except.bind, EvalClaim_revert]
                  exact ihl
                · simp only [hlv, bind, Except.bind]
                  exact EvalClaim_stuck
            | ok lv =>
                rw [hlv] at ihl
                simp only [EvalClaim_ok] at ihl
                obtain ⟨wl, hwl, hstepsl⟩ := ihl
                simp only [hlv, bind, Except.bind]
                have ihr := compileExpr_sim L Γ (t + 1) r hcr s
                  (σt := wl :: σt) hcodecr (by simp [ht]) hrepr
                simp only [List.cons_append] at ihr
                cases hrv : evalW s r with
                | error err =>
                    cases err
                    · rw [hrv] at ihr
                      simp only [EvalClaim_revert] at ihr
                      simp only [hrv, bind, Except.bind, EvalClaim_revert]
                      exact Reverting.of_steps hstepsl ihr
                    · simp only [hrv, bind, Except.bind]
                      exact EvalClaim_stuck
                | ok rv =>
                    rw [hrv] at ihr
                    simp only [EvalClaim_ok] at ihr
                    obtain ⟨wr, hwr, hstepsr⟩ := ihr
                    simp only [hrv, bind, Except.bind]
                    have hboth : Steps C ⟨base, σt ++ σ, st⟩
                        ⟨base + cl.length + cr.length,
                          wr :: wl :: (σt ++ σ), st⟩ := by
                      refine Steps.trans hstepsl ?_
                      refine Steps.cast_pc hstepsr ?_
                      omega
                    simp only [applyCheckedW, uintChecked_div,
                      Bool.false_eq_true, if_false, bind, Except.bind]
                    cases hab : applyBinOpW BinOp.div lv rv with
                    | error err =>
                        cases err
                        · -- divisor zero: guard falls into REVERT
                          have hrv0 := applyBinOpW_div_revert hab
                          subst hrv0
                          simp only [ReprVal] at hwr
                          have hwr0 : wr = 0 := word_eq_zero_of_int hwr
                          subst hwr0
                          simp only [EvalClaim_revert]
                          refine ⟨⟨base + cl.length + cr.length + 2,
                            0 :: wl :: (σt ++ σ), st⟩, ?_, ?_⟩
                          · refine Steps.trans hboth ?_
                            refine Steps.head
                              (Step.dup hcodetail.fetch rfl) ?_
                            refine Steps.cast_pc (Steps.single
                              (Step.jumpiFalse (hcodetail.tail).fetch)) ?_
                            omega
                          · exact ((hcodetail.tail).tail).fetch
                        · exact EvalClaim_stuck
                    | ok v =>
                        refine EvalClaim_checkArithW fun _hchk => ?_
                        obtain ⟨a, b, hla, hrb, hb0, hv⟩ :=
                          applyBinOpW_div_ok hab
                        subst hla hrb hv
                        simp only [ReprVal] at hwl hwr
                        simp only [EvalClaim_ok]
                        refine ⟨wl / wr, ?_, ?_⟩
                        · simp only [ReprVal]
                          rw [hwl, hwr]
                          rw [BitVec.toNat_udiv]
                          rfl
                        · refine Steps.trans hboth ?_
                          refine Steps.head
                            (Step.dup hcodetail.fetch rfl) ?_
                          refine Steps.head
                            (Step.jumpiTrue (hcodetail.tail).fetch
                              (word_ne_zero_of_int hwr hb0)) ?_
                          refine Steps.head
                            (Step.swap
                              ((((hcodetail.tail).tail)).tail).fetch
                              rfl rfl) ?_
                          refine Steps.cast_pc (Steps.single
                            (Step.div
                              (((((hcodetail.tail).tail)).tail).tail).fetch))
                            ?_
                          simp [List.length_append]
                          omega
      case mod =>
        simp only [compileExpr] at hc
        cases hcl : compileExpr L Γ t l with
        | none => rw [hcl] at hc; simp [bind, Option.bind] at hc
        | some cl =>
          rw [hcl] at hc
          simp only [bind, Option.bind] at hc
          cases hcr : compileExpr L Γ (t + 1) r with
          | none => rw [hcr] at hc; simp [bind, Option.bind] at hc
          | some cr =>
            rw [hcr] at hc
            simp only [bind, Option.bind, pure, Option.pure_def, Option.some.injEq] at hc
            subst hc
            have hcodecl : codeAt C base cl :=
              (hcode.append_left).append_left
            have hcodecr : codeAt C (base + cl.length) cr :=
              (hcode.append_left).append_right
            have hcodetail : codeAt C (base + cl.length + cr.length)
                [Instr.dup 1, Instr.jumpi 1, Instr.revert,
                 Instr.swap 1, Instr.mod] :=
              codeAt_cast (hcode.append_right)
                (by simp only [List.length_append, List.length_cons,
                  List.length_nil]; omega)
            have ihl := compileExpr_sim L Γ t l hcl s hcodecl ht hrepr
            simp only [evalW,
              scArm_of_not_sc (op := BinOp.mod) rfl,
              BinOp.shortCircuits, Bool.false_and, Bool.false_eq_true,
              if_false]
            cases hlv : evalW s l with
            | error err =>
                cases err
                · rw [hlv] at ihl
                  simp only [EvalClaim_revert] at ihl
                  simp only [hlv, bind, Except.bind, EvalClaim_revert]
                  exact ihl
                · simp only [hlv, bind, Except.bind]
                  exact EvalClaim_stuck
            | ok lv =>
                rw [hlv] at ihl
                simp only [EvalClaim_ok] at ihl
                obtain ⟨wl, hwl, hstepsl⟩ := ihl
                simp only [hlv, bind, Except.bind]
                have ihr := compileExpr_sim L Γ (t + 1) r hcr s
                  (σt := wl :: σt) hcodecr (by simp [ht]) hrepr
                simp only [List.cons_append] at ihr
                cases hrv : evalW s r with
                | error err =>
                    cases err
                    · rw [hrv] at ihr
                      simp only [EvalClaim_revert] at ihr
                      simp only [hrv, bind, Except.bind, EvalClaim_revert]
                      exact Reverting.of_steps hstepsl ihr
                    · simp only [hrv, bind, Except.bind]
                      exact EvalClaim_stuck
                | ok rv =>
                    rw [hrv] at ihr
                    simp only [EvalClaim_ok] at ihr
                    obtain ⟨wr, hwr, hstepsr⟩ := ihr
                    simp only [hrv, bind, Except.bind]
                    have hboth : Steps C ⟨base, σt ++ σ, st⟩
                        ⟨base + cl.length + cr.length,
                          wr :: wl :: (σt ++ σ), st⟩ := by
                      refine Steps.trans hstepsl ?_
                      refine Steps.cast_pc hstepsr ?_
                      omega
                    simp only [applyCheckedW, uintChecked_mod,
                      Bool.false_eq_true, if_false, bind, Except.bind]
                    cases hab : applyBinOpW BinOp.mod lv rv with
                    | error err =>
                        cases err
                        · have hrv0 := applyBinOpW_mod_revert hab
                          subst hrv0
                          simp only [ReprVal] at hwr
                          have hwr0 : wr = 0 := word_eq_zero_of_int hwr
                          subst hwr0
                          simp only [EvalClaim_revert]
                          refine ⟨⟨base + cl.length + cr.length + 2,
                            0 :: wl :: (σt ++ σ), st⟩, ?_, ?_⟩
                          · refine Steps.trans hboth ?_
                            refine Steps.head
                              (Step.dup hcodetail.fetch rfl) ?_
                            refine Steps.cast_pc (Steps.single
                              (Step.jumpiFalse (hcodetail.tail).fetch)) ?_
                            omega
                          · exact ((hcodetail.tail).tail).fetch
                        · exact EvalClaim_stuck
                    | ok v =>
                        refine EvalClaim_checkArithW fun _hchk => ?_
                        obtain ⟨a, b, hla, hrb, hb0, hv⟩ :=
                          applyBinOpW_mod_ok hab
                        subst hla hrb hv
                        simp only [ReprVal] at hwl hwr
                        simp only [EvalClaim_ok]
                        refine ⟨wMod wl wr, ?_, ?_⟩
                        · simp only [ReprVal, wMod]
                          rw [if_neg (word_ne_zero_of_int hwr hb0)]
                          rw [hwl, hwr]
                          change _ = (((wl % wr).toNat : Nat) : Int)
                          rw [BitVec.toNat_umod]
                          rfl
                        · refine Steps.trans hboth ?_
                          refine Steps.head
                            (Step.dup hcodetail.fetch rfl) ?_
                          refine Steps.head
                            (Step.jumpiTrue (hcodetail.tail).fetch
                              (word_ne_zero_of_int hwr hb0)) ?_
                          refine Steps.head
                            (Step.swap
                              ((((hcodetail.tail).tail)).tail).fetch
                              rfl rfl) ?_
                          refine Steps.cast_pc (Steps.single
                            (Step.mod
                              (((((hcodetail.tail).tail)).tail).tail).fetch))
                            ?_
                          simp [List.length_append]
                          omega
      all_goals (
        simp only [compileExpr] at hc
        cases hopc : binopTail _ l.ty with
        | none => rw [hopc] at hc; simp [bind, Option.bind] at hc
        | some tail =>
          rw [hopc] at hc
          simp only [bind, Option.bind] at hc
          cases hcl : compileExpr L Γ t l with
          | none => rw [hcl] at hc; simp [bind, Option.bind] at hc
          | some cl =>
            rw [hcl] at hc
            simp only [bind, Option.bind] at hc
            cases hcr : compileExpr L Γ (t + 1) r with
            | none => rw [hcr] at hc; simp [bind, Option.bind] at hc
            | some cr =>
              rw [hcr] at hc
              simp only [bind, Option.bind, pure, Option.pure_def, Option.some.injEq] at hc
              subst hc
              have hcodecl : codeAt C base cl :=
                (hcode.append_left).append_left
              have hcodecr : codeAt C (base + cl.length) cr :=
                (hcode.append_left).append_right
              have hcodetail : codeAt C (base + cl.length + cr.length)
                  tail :=
                codeAt_cast (hcode.append_right)
                  (by simp only [List.length_append, List.length_cons,
                  List.length_nil]; omega)
              have ihl := compileExpr_sim L Γ t l hcl s hcodecl ht hrepr
              simp only [evalW, scArm_of_not_sc (binopTail_not_sc hopc),
                binopTail_not_sc hopc, Bool.false_and,
                Bool.false_eq_true, if_false]
              cases hlv : evalW s l with
              | error err =>
                  cases err
                  · rw [hlv] at ihl
                    simp only [EvalClaim_revert] at ihl
                    simp only [hlv, bind, Except.bind, EvalClaim_revert]
                    exact ihl
                  · simp only [hlv, bind, Except.bind]
                    exact EvalClaim_stuck
              | ok lv =>
                  rw [hlv] at ihl
                  simp only [EvalClaim_ok] at ihl
                  obtain ⟨wl, hwl, hstepsl⟩ := ihl
                  simp only [hlv, bind, Except.bind]
                  have ihr := compileExpr_sim L Γ (t + 1) r hcr s
                    (σt := wl :: σt) hcodecr (by simp [ht]) hrepr
                  simp only [List.cons_append] at ihr
                  cases hrv : evalW s r with
                  | error err =>
                      cases err
                      · rw [hrv] at ihr
                        simp only [EvalClaim_revert] at ihr
                        simp only [hrv, bind, Except.bind,
                          EvalClaim_revert]
                        exact Reverting.of_steps hstepsl ihr
                      · simp only [hrv, bind, Except.bind]
                        exact EvalClaim_stuck
                  | ok rv =>
                      rw [hrv] at ihr
                      simp only [EvalClaim_ok] at ihr
                      obtain ⟨wr, hwr, hstepsr⟩ := ihr
                      simp only [hrv, bind, Except.bind]
                      obtain ⟨hok, hrevert⟩ := binopTail_sim hopc hcodetail
                        (σ := σt ++ σ) (st := st) hwl hwr
                      cases hab : applyCheckedW _ l.ty lv rv with
                      | error err =>
                          cases err
                          · simp only [EvalClaim_revert]
                            exact Reverting.of_steps
                              (Steps.trans hstepsl hstepsr) (hrevert hab)
                          · exact EvalClaim_stuck
                      | ok v =>
                          obtain ⟨w, hw, hstepst⟩ := hok v hab
                          simp only [EvalClaim_ok]
                          refine ⟨w, hw, ?_⟩
                          refine Steps.trans hstepsl ?_
                          refine Steps.trans hstepsr ?_
                          refine Steps.cast_pc hstepst ?_
                          simp only [List.length_append]
                          omega)
  | .field kind fty fbase lfld =>
      cases kind with
      | memory => simp [compileExpr] at hc
      | stack => simp [compileExpr] at hc
      | storage =>
        match fbase with
        | .field .. => simp [compileExpr] at hc
        | .index .. => simp [compileExpr] at hc
        | .pushPlace .. => simp [compileExpr] at hc
        | .bool .. => simp [compileExpr] at hc
        | .intLit .. => simp [compileExpr] at hc
        | .mkCall .. => simp [compileExpr] at hc
        | .mkBinop .. => simp [compileExpr] at hc
        | .mkUnop .. => simp [compileExpr] at hc
        | .mkIncDec .. => simp [compileExpr] at hc
        | .mkTernary .. => simp [compileExpr] at hc
        | .var bkind bty fld =>
          cases bkind with
          | stack => simp [compileExpr] at hc
          | memory => simp [compileExpr] at hc
          | storage =>
            simp only [compileExpr] at hc
            split at hc
            case _ hcond =>
              cases hslot : slotOf? L fld.name with
              | none => rw [hslot] at hc; exact Option.noConfusion hc
              | some i =>
                simp only [hslot, Option.some.injEq] at hc
                subst hc
                have hLidx : L[i]? = some fld.name :=
                  findIdx?_eq_name (by simpa [slotOf?] using hslot)
                have hmem : fld.name ∈ L := List.mem_of_getElem? hLidx
                have henv : lookupBy fld.name s.env = none :=
                  hrepr.rootsEnv _ hmem
                obtain ⟨sv, hst, hroot⟩ :=
                  hrepr.roots i fld.name hLidx
                simp only [evalW, henv, if_pos hcond]
                cases sv with
                | prim p => cases p <;> (rw [hst]; exact EvalClaim_stuck)
                | struct fields => rw [hst]; exact EvalClaim_stuck
                | map entries dflt => rw [hst]; exact EvalClaim_stuck
                | array elems =>
                  simp only [hst]
                  have hroot' := hroot
                  simp only [ReprRoot] at hroot'
                  obtain ⟨hlen, hlslot, helems⟩ := hroot'
                  simp only [EvalClaim_ok]
                  refine ⟨st.read (slotWord i), ?_, ?_⟩
                  · rw [hlslot]
                    simp only [ReprVal]
                    rw [BitVec.toNat_ofNat]
                    simp only [keyBound] at hlen
                    omega
                  · refine Steps.head (Step.push hcode.fetch) ?_
                    simpa using Steps.single
                      (Step.sload (hcode.tail).fetch)
            case _ =>
              split at hc
              case _ hcondS =>
                cases bty with
                | prim p => simp [isStructTy] at hcondS
                | ref r =>
                  cases r with
                  | array e => simp [isStructTy] at hcondS
                  | mapping kt vt => simp [isStructTy] at hcondS
                  | struct sname =>
                    cases hslot : slotOf? L fld.name with
                    | none =>
                        rw [hslot] at hc; exact Option.noConfusion hc
                    | some i =>
                      simp only [hslot] at hc
                      cases hsidx : structIdx? sname lfld.name with
                      | none =>
                          rw [hsidx] at hc
                          exact Option.noConfusion hc
                      | some j =>
                        simp only [hsidx] at hc
                        split at hc
                        case _ hjb =>
                          simp only [Option.some.injEq] at hc
                          subst hc
                          have hLidx : L[i]? = some fld.name :=
                            findIdx?_eq_name
                              (by simpa [slotOf?] using hslot)
                          have hmem : fld.name ∈ L :=
                            List.mem_of_getElem? hLidx
                          have henv : lookupBy fld.name s.env = none :=
                            hrepr.rootsEnv _ hmem
                          obtain ⟨sv, hst, hroot⟩ :=
                            hrepr.roots i fld.name hLidx
                          simp only [evalW, henv, isArrayTy,
                            Bool.false_eq_true, and_false, if_false,
                            if_pos hcondS]
                          cases sv with
                          | prim p =>
                              cases p <;> (rw [hst]; exact EvalClaim_stuck)
                          | array elems =>
                              rw [hst]; exact EvalClaim_stuck
                          | map entries dflt =>
                              rw [hst]; exact EvalClaim_stuck
                          | struct sfields =>
                            simp only [hst]
                            by_cases hspine : sfields.map Prod.fst
                                = structSpineOf
                                  (Ty.ref (RefTy.struct sname))
                            case neg =>
                              simp only [if_neg hspine]
                              exact EvalClaim_stuck
                            case pos =>
                            simp only [if_pos hspine]
                            have hspine' : sfields.map Prod.fst
                                = (Semantics.structDef sname).map
                                    Prod.fst := by
                              simpa [structSpineOf] using hspine
                            have hidxSpine :
                                ((Semantics.structDef sname).map
                                  Prod.fst).findIdx?
                                    (· = lfld.name) = some j := by
                              rw [List.findIdx?_map]
                              exact hsidx
                            obtain ⟨hjlt', hlook, hsetp, hspp⟩ :=
                              struct_field_at_findIdx hspine' hidxSpine
                            simp only [hlook]
                            have hroot' := hroot
                            simp only [ReprRoot] at hroot'
                            obtain ⟨hlenS, hflds⟩ := hroot'
                            cases hav : (sfields.getD j
                                ("", SVal.int 0)).2.asValue with
                            | error err =>
                                cases err
                                · cases hgd : (sfields.getD j
                                      ("", SVal.int 0)).2 with
                                  | prim p =>
                                      cases p <;>
                                        (rw [hgd] at hav;
                                         simp [SVal.asValue] at hav)
                                  | _ =>
                                      (rw [hgd] at hav;
                                       simp [SVal.asValue] at hav)
                                · exact EvalClaim_stuck
                            | ok val =>
                              simp only [hav, EvalClaim_ok]
                              refine ⟨st.read (mapSlotW (slotWord i)
                                  (BitVec.ofNat 256 j)),
                                (hflds j hjlt').asValue hav, ?_⟩
                              refine Steps.head
                                (Step.push hcode.fetch) ?_
                              simpa using Steps.single
                                (Step.sload (hcode.tail).fetch)
                        case _ => exact Option.noConfusion hc
              case _ => exact Option.noConfusion hc
  | .index kind ty mbase key =>
      cases kind with
      | memory => simp [compileExpr] at hc
      | stack => simp [compileExpr] at hc
      | storage =>
        match mbase with
        | .field .. => simp [compileExpr] at hc
        | .index .. => simp [compileExpr] at hc
        | .pushPlace .. => simp [compileExpr] at hc
        | .bool .. => simp [compileExpr] at hc
        | .intLit .. => simp [compileExpr] at hc
        | .mkCall .. => simp [compileExpr] at hc
        | .mkBinop .. => simp [compileExpr] at hc
        | .mkUnop .. => simp [compileExpr] at hc
        | .mkIncDec .. => simp [compileExpr] at hc
        | .mkTernary .. => simp [compileExpr] at hc
        | .var bkind bty fld =>
          cases bkind with
          | stack => simp [compileExpr] at hc
          | memory => simp [compileExpr] at hc
          | storage =>
            simp only [compileExpr] at hc
            split at hc
            case _ horig =>
              cases hslot : slotOf? L fld.name with
              | none => rw [hslot] at hc; exact Option.noConfusion hc
              | some i =>
                simp only [hslot] at hc
                by_cases htyA : isArrayTy bty = true
                case pos =>
                  rw [if_pos htyA] at hc
                  cases hck : compileExpr L Γ t key with
                  | none => rw [hck] at hc; simp [bind, Option.bind] at hc
                  | some ck =>
                    simp only [hck, bind, Option.bind, pure,
                      Option.pure_def, Option.some.injEq] at hc
                    subst hc
                    have hLidx : L[i]? = some fld.name :=
                      findIdx?_eq_name (by simpa [slotOf?] using hslot)
                    have hmem : fld.name ∈ L :=
                      List.mem_of_getElem? hLidx
                    have henv : lookupBy fld.name s.env = none :=
                      hrepr.rootsEnv _ hmem
                    have hcodeck : codeAt C base ck := hcode.append_left
                    have hcodew : codeAt C (base + ck.length)
                        [Instr.push (slotWord i), Instr.sload,
                         Instr.dup 2, Instr.lt, Instr.jumpi 1,
                         Instr.revert, Instr.push (slotWord i),
                         Instr.mapslot, Instr.sload] :=
                      hcode.append_right
                    have ihk := compileExpr_sim L Γ t key hck s
                      hcodeck ht hrepr
                    simp only [evalW, henv, horig, if_pos]
                    cases hk : evalW s key with
                    | error err =>
                        cases err
                        · rw [hk] at ihk
                          simp only [EvalClaim_revert] at ihk
                          simp only [hk, bind, Except.bind,
                            EvalClaim_revert]
                          exact ihk
                        · simp only [hk, bind, Except.bind]
                          exact EvalClaim_stuck
                    | ok kv =>
                      rw [hk] at ihk
                      simp only [EvalClaim_ok] at ihk
                      obtain ⟨kw, hkwv, hstepsk⟩ := ihk
                      simp only [hk, bind, Except.bind]
                      cases kv with
                      | bool b => exact EvalClaim_stuck
                      | int k =>
                        simp only [ReprVal] at hkwv
                        have hk0 : 0 ≤ k := by omega
                        simp only [if_pos htyA, if_pos hk0]
                        obtain ⟨sv, hst, hroot⟩ :=
                          hrepr.roots i fld.name hLidx
                        cases sv with
                        | prim p => cases p <;> (rw [hst]; exact EvalClaim_stuck)
                        | struct fields => rw [hst]; exact EvalClaim_stuck
                        | map entries dflt => rw [hst]; exact EvalClaim_stuck
                        | array elems =>
                          simp only [hst]
                          simp only [ReprRoot] at hroot
                          obtain ⟨hlen, hlslot, helems⟩ := hroot
                          have hfpush1 := hcodew.fetch
                          have hfsload1 := (hcodew.tail).fetch
                          have hfdup := ((hcodew.tail).tail).fetch
                          have hflt := (((hcodew.tail).tail).tail).fetch
                          have hfjumpi :=
                            ((((hcodew.tail).tail).tail).tail).fetch
                          have hfrevert :=
                            (((((hcodew.tail).tail).tail).tail).tail).fetch
                          have hfpush2 :=
                            ((((((hcodew.tail).tail).tail).tail).tail).tail).fetch
                          have hfmapslot :=
                            (((((((hcodew.tail).tail).tail).tail).tail).tail).tail).fetch
                          have hfsload2 :=
                            ((((((((hcodew.tail).tail).tail).tail).tail).tail).tail).tail).fetch
                          by_cases hlt : k.toNat < elems.length
                          case pos =>
                            simp only [if_pos hlt]
                            have hkb : k < keyBoundI := by
                              simp only [keyBoundI]
                              simp only [keyBound] at hlen
                              omega
                            obtain ⟨hkweq, hkwlt⟩ :=
                              keyWord_eq hk0 hkb hkwv
                            have hsv := helems k.toNat hlt
                            rw [← hkweq] at hsv
                            obtain ⟨v, hav, hrv⟩ := hsv.asValue
                            rw [hav]
                            simp only [EvalClaim_ok]
                            refine ⟨st.read (mapSlotW (slotWord i) kw),
                              hrv, ?_⟩
                            have hult : BitVec.ult kw
                                (BitVec.ofNat 256 elems.length) = true := by
                              simp only [BitVec.ult, decide_eq_true_eq]
                              rw [BitVec.toNat_ofNat]
                              simp only [keyBound] at hlen
                              omega
                            refine Steps.trans hstepsk ?_
                            refine Steps.head (Step.push hfpush1) ?_
                            refine Steps.head (Step.sload hfsload1) ?_
                            rw [hlslot]
                            refine Steps.head (Step.dup hfdup rfl) ?_
                            refine Steps.head (Step.lt hflt) ?_
                            rw [hult]
                            simp only [wBool_true]
                            refine Steps.head
                              (Step.jumpiTrue hfjumpi one_ne_zero_word) ?_
                            refine Steps.head (Step.push hfpush2) ?_
                            refine Steps.head (Step.mapslot hfmapslot) ?_
                            refine Steps.cast_pc (Steps.single
                              (Step.sload hfsload2)) ?_
                            simp only [List.length_append,
                              List.length_cons, List.length_nil]
                            omega
                          case neg =>
                            simp only [if_neg hlt]
                            simp only [EvalClaim_revert]
                            have hult : BitVec.ult kw
                                (BitVec.ofNat 256 elems.length) = false := by
                              simp only [BitVec.ult]
                              rw [decide_eq_false_iff_not]
                              rw [BitVec.toNat_ofNat]
                              simp only [keyBound] at hlen
                              omega
                            refine Reverting.of_steps hstepsk ?_
                            refine ⟨⟨base + ck.length + 1 + 1 + 1 + 1 + 1,
                              kw :: (σt ++ σ), st⟩, ?_, ?_⟩
                            · refine Steps.head (Step.push hfpush1) ?_
                              refine Steps.head (Step.sload hfsload1) ?_
                              rw [hlslot]
                              refine Steps.head (Step.dup hfdup rfl) ?_
                              refine Steps.head (Step.lt hflt) ?_
                              rw [hult]
                              simp only [wBool_false]
                              exact Steps.single (Step.jumpiFalse hfjumpi)
                            · exact hfrevert
                case neg =>
                rw [if_neg htyA] at hc
                cases hck : compileExpr L Γ t key with
                | none => rw [hck] at hc; simp [bind, Option.bind] at hc
                | some ck =>
                  simp only [hck, bind, Option.bind, pure,
                    Option.pure_def, Option.some.injEq] at hc
                  subst hc
                  have hLidx : L[i]? = some fld.name :=
                    findIdx?_eq_name (by simpa [slotOf?] using hslot)
                  have hmem : fld.name ∈ L :=
                    List.mem_of_getElem? hLidx
                  have henv : lookupBy fld.name s.env = none :=
                    hrepr.rootsEnv _ hmem
                  have hcodeck : codeAt C base ck := hcode.append_left
                  have hcodew : codeAt C (base + ck.length)
                      [Instr.push (slotWord i), Instr.mapslot,
                       Instr.sload] := hcode.append_right
                  have ihk := compileExpr_sim L Γ t key hck s
                    hcodeck ht hrepr
                  simp only [evalW, henv, horig, if_pos]
                  cases hk : evalW s key with
                  | error err =>
                      cases err
                      · rw [hk] at ihk
                        simp only [EvalClaim_revert] at ihk
                        simp only [hk, bind, Except.bind,
                          EvalClaim_revert]
                        exact ihk
                      · simp only [hk, bind, Except.bind]
                        exact EvalClaim_stuck
                  | ok kv =>
                    rw [hk] at ihk
                    simp only [EvalClaim_ok] at ihk
                    obtain ⟨kw, hkwv, hstepsk⟩ := ihk
                    simp only [hk, bind, Except.bind]
                    cases kv with
                    | bool b => exact EvalClaim_stuck
                    | int k =>
                      simp only [if_neg htyA]
                      by_cases hkb : 0 ≤ k ∧ k < keyBoundI
                      case neg =>
                          simp only [if_neg hkb]
                          exact EvalClaim_stuck
                      case pos =>
                      simp only [if_pos hkb]
                      obtain ⟨sv, hst, hroot⟩ :=
                        hrepr.roots i fld.name hLidx
                      cases sv with
                      | prim p => cases p <;> (rw [hst]; exact EvalClaim_stuck)
                      | struct fields => rw [hst]; exact EvalClaim_stuck
                      | array elems => rw [hst]; exact EvalClaim_stuck
                      | map entries dflt =>
                        simp only [hst]
                        simp only [ReprRoot] at hroot
                        have hsv := hroot k hkb.1 hkb.2
                        obtain ⟨kweq, hkwlt⟩ :=
                          keyWord_eq hkb.1 hkb.2 hkwv
                        rw [← kweq] at hsv
                        obtain ⟨v, hav, hrv⟩ := hsv.asValue
                        rw [hav]
                        simp only [EvalClaim_ok]
                        refine ⟨st.read (mapSlotW (slotWord i) kw),
                          hrv, ?_⟩
                        refine Steps.trans hstepsk ?_
                        refine Steps.head (Step.push hcodew.fetch) ?_
                        refine Steps.head
                          (Step.mapslot (hcodew.tail).fetch) ?_
                        refine Steps.cast_pc (Steps.single
                          (Step.sload
                            ((hcodew.tail).tail).fetch)) ?_
                        simp only [List.length_append,
                          List.length_cons, List.length_nil]
                        omega
            case _ => exact Option.noConfusion hc
  | .pushPlace .. => simp [compileExpr] at hc
  | .mkCall .. => simp [compileExpr] at hc
  | .mkIncDec .. => simp [compileExpr] at hc
termination_by e.size
decreasing_by all_goals
  first
  | omega
  | (simp [Typed.WrappedExpr.size] <;> omega)

/-! ## Statement simulation -/

/-- What the compiled code of a statement (or block) guarantees, keyed
on the bounded executor's outcome: success falls through to the end of
the fragment in a configuration representing the final state under the
(possibly extended) local context; a revert reaches `REVERT`; `.stuck`
claims nothing. -/
def ExecClaim (C : Code) (base len : Nat) (L Γ' : List Name)
    (σ0 : List Word) (st0 : Store) : Res State → Prop
  | .ok s' => ∃ σ' st',
      Steps C ⟨base, σ0, st0⟩ ⟨base + len, σ', st'⟩ ∧
        ReprState L Γ' s' σ' st'
  | .error .revert => Reverting C ⟨base, σ0, st0⟩
  | .error .stuck => True

@[simp] theorem ExecClaim_ok {C : Code} {base len : Nat}
    {L Γ' : List Name} {σ0 : List Word} {st0 : Store} {s' : State} :
    ExecClaim C base len L Γ' σ0 st0 (.ok s') ↔
      ∃ σ' st', Steps C ⟨base, σ0, st0⟩ ⟨base + len, σ', st'⟩ ∧
        ReprState L Γ' s' σ' st' := Iff.rfl

@[simp] theorem ExecClaim_revert {C : Code} {base len : Nat}
    {L Γ' : List Name} {σ0 : List Word} {st0 : Store} :
    ExecClaim C base len L Γ' σ0 st0 (.error .revert) ↔
      Reverting C ⟨base, σ0, st0⟩ := Iff.rfl

@[simp] theorem ExecClaim_stuck {C : Code} {base len : Nat}
    {L Γ' : List Name} {σ0 : List Word} {st0 : Store} :
    ExecClaim C base len L Γ' σ0 st0 (.error .stuck) := trivial

theorem hasCompound_not_sc {op : BinOp}
    (h : op.hasCompoundAssign = true) : op.shortCircuits = false := by
  cases op <;> simp_all [BinOp.hasCompoundAssign, BinOp.shortCircuits]

/-- The compound-assignment operators are the arithmetic ones. -/
theorem hasCompound_arith {op : BinOp}
    (h : op.hasCompoundAssign = true) : op.isArith = true := by
  cases op <;> first | rfl | exact Bool.noConfusion h

/-- Under a successful compilation, compound assignment is `assignW`
of the operator expression whenever the bounded semantics claims
anything: both sides sequence the same pure sub-evaluations (target
read, key, right-hand side, operator, write), so where their guards
pass the outcome is order-independent; everywhere else the compound
statement is `.stuck`. -/
theorem execW_compound_eq (L Γ : List Name) {op : BinOp}
    (hop : op.hasCompoundAssign = true) {lhs : PlaceExpr}
    {rhs : WrappedExpr} {code : Code}
    (hc : compileAssign L Γ lhs.expr (.mkBinop op lhs.expr rhs) =
      some code) (s : State) :
    execW s (.compoundAssign op lhs rhs) =
        assignW s lhs.expr (.mkBinop op lhs.expr rhs) ∨
      execW s (.compoundAssign op lhs rhs) = .error .stuck := by
  obtain ⟨lexpr, hassignable⟩ := lhs
  match lexpr with
  | .var .stack ty fld =>
      cases henv : lookupBy fld.name s.env with
      | none =>
          exact Or.inr (by simp [execW, hop, evalW, henv, bind,
            Except.bind])
      | some b =>
        cases b with
        | spath root segs =>
            exact Or.inr (by simp [execW, hop, evalW, henv, bind,
              Except.bind])
        | mref id =>
            exact Or.inr (by simp [execW, hop, evalW, henv, bind,
              Except.bind])
        | val w =>
            refine Or.inl ?_
            simp only [execW, hop, if_true, assignW, writeW, evalW,
              henv, scArm_of_not_sc (hasCompound_not_sc hop),
              hasCompound_not_sc hop, hasCompound_arith hop,
              BinOp.retTy, Bool.false_and, Bool.false_eq_true,
              if_false, if_true, bind_assoc]
            rfl
  | .var .memory ty fld => simp [compileAssign] at hc
  | .var .storage ty fld =>
      simp only [compileAssign] at hc
      split at hc
      case _ hcond =>
        cases henv : lookupBy fld.name s.env with
        | some b =>
            exact Or.inr (by simp [execW, hop, evalW, henv, bind,
              Except.bind])
        | none =>
          cases hsl : lookupBy fld.name s.storage with
          | none =>
              exact Or.inr (by simp [execW, hop, evalW, henv, hcond.1,
                hsl, bind, Except.bind])
          | some sv =>
            cases hav : sv.asValue with
            | error err =>
                cases err
                · cases sv with
                  | prim p => cases p <;> simp [SVal.asValue] at hav
                  | _ => simp [SVal.asValue] at hav
                · exact Or.inr (by simp [execW, hop, evalW, henv,
                    hcond.1, hsl, hav, bind, Except.bind])
            | ok oldv =>
                refine Or.inl ?_
                simp only [execW, hop, if_true, assignW, writeW, evalW,
                  henv, hsl, hav, scArm_of_not_sc (hasCompound_not_sc hop),
                  hasCompound_not_sc hop, hasCompound_arith hop,
                  BinOp.retTy, Bool.false_and, Bool.false_eq_true,
                  if_false, hcond.1, hcond.2, and_self, if_true,
                  bind_assoc]
                rfl
      case _ => exact Option.noConfusion hc
  | .index kind ty base key =>
      cases kind with
      | memory => simp [compileAssign] at hc
      | stack => simp [compileAssign] at hc
      | storage =>
        match base with
        | .field .. => simp [compileAssign] at hc
        | .index .. => simp [compileAssign] at hc
        | .pushPlace .. => simp [compileAssign] at hc
        | .bool .. => simp [compileAssign] at hc
        | .intLit .. => simp [compileAssign] at hc
        | .mkCall .. => simp [compileAssign] at hc
        | .mkBinop .. => simp [compileAssign] at hc
        | .mkUnop .. => simp [compileAssign] at hc
        | .mkIncDec .. => simp [compileAssign] at hc
        | .mkTernary .. => simp [compileAssign] at hc
        | .var bkind bty fld =>
          cases bkind with
          | stack => simp [compileAssign] at hc
          | memory => simp [compileAssign] at hc
          | storage =>
            simp only [compileAssign] at hc
            split at hc
            case _ hcond =>
              have hprim := hcond.2
              cases henv : lookupBy fld.name s.env with
              | some b =>
                  first
                    | exact Or.inl (by
                        simp [execW, hop, assignW, writeW, evalW, henv, bind, Except.bind,
                          hasCompound_arith hop, BinOp.retTy])
                    | exact Or.inr (by
                        simp [execW, hop, assignW, writeW, evalW, henv, bind, Except.bind])
              | none =>
                cases hk : evalW s key with
                | error err =>
                    cases err <;>
                      first
                        | exact Or.inl (by
                            simp [execW, hop, assignW, writeW, evalW, henv, hcond.1, hk, scArm_of_not_sc (hasCompound_not_sc hop), hasCompound_not_sc hop, bind, Except.bind,
                              hasCompound_arith hop, BinOp.retTy])
                        | exact Or.inr (by
                            simp [execW, hop, assignW, writeW, evalW, henv, hcond.1, hk, scArm_of_not_sc (hasCompound_not_sc hop), hasCompound_not_sc hop, bind, Except.bind])
                | ok kv =>
                  cases kv with
                  | bool b =>
                      first
                        | exact Or.inl (by
                            simp [execW, hop, assignW, writeW, evalW, henv, hcond.1, hk, scArm_of_not_sc (hasCompound_not_sc hop), hasCompound_not_sc hop, bind, Except.bind,
                              hasCompound_arith hop, BinOp.retTy])
                        | exact Or.inr (by
                            simp [execW, hop, assignW, writeW, evalW, henv, hcond.1, hk, scArm_of_not_sc (hasCompound_not_sc hop), hasCompound_not_sc hop, bind, Except.bind])
                  | int k =>
                    by_cases htyA : isArrayTy bty = true
                    case pos =>
                      by_cases hk0 : 0 ≤ k
                      case neg =>
                          first
                            | exact Or.inl (by
                                simp [execW, hop, assignW, writeW, evalW, henv, hcond.1, hk, htyA, hk0, scArm_of_not_sc (hasCompound_not_sc hop), hasCompound_not_sc hop, bind, Except.bind,
                                  hasCompound_arith hop, BinOp.retTy])
                            | exact Or.inr (by
                                simp [execW, hop, assignW, writeW, evalW, henv, hcond.1, hk, htyA, hk0, scArm_of_not_sc (hasCompound_not_sc hop), hasCompound_not_sc hop, bind, Except.bind])
                      case pos =>
                      cases hs : lookupBy fld.name s.storage with
                      | none =>
                          first
                            | exact Or.inl (by
                                simp [execW, hop, assignW, writeW, evalW, henv, hcond.1, hprim, hk, htyA, hk0, hs, scArm_of_not_sc (hasCompound_not_sc hop), hasCompound_not_sc hop, bind, Except.bind,
                                  hasCompound_arith hop, BinOp.retTy])
                            | exact Or.inr (by
                                simp [execW, hop, assignW, writeW, evalW, henv, hcond.1, hprim, hk, htyA, hk0, hs, scArm_of_not_sc (hasCompound_not_sc hop), hasCompound_not_sc hop, bind, Except.bind])
                      | some sv =>
                        cases sv with
                        | prim p =>
                            cases p <;>
                              first
                                | exact Or.inl (by
                                    simp [execW, hop, assignW, writeW, evalW, henv, hcond.1, hprim, hk, htyA, hk0, hs, scArm_of_not_sc (hasCompound_not_sc hop), hasCompound_not_sc hop, bind, Except.bind,
                                      hasCompound_arith hop, BinOp.retTy])
                                | exact Or.inr (by
                                    simp [execW, hop, assignW, writeW, evalW, henv, hcond.1, hprim, hk, htyA, hk0, hs, scArm_of_not_sc (hasCompound_not_sc hop), hasCompound_not_sc hop, bind, Except.bind])
                        | struct fields =>
                            first
                              | exact Or.inl (by
                                  simp [execW, hop, assignW, writeW, evalW, henv, hcond.1, hprim, hk, htyA, hk0, hs, scArm_of_not_sc (hasCompound_not_sc hop), hasCompound_not_sc hop, bind, Except.bind,
                                    hasCompound_arith hop, BinOp.retTy])
                              | exact Or.inr (by
                                  simp [execW, hop, assignW, writeW, evalW, henv, hcond.1, hprim, hk, htyA, hk0, hs, scArm_of_not_sc (hasCompound_not_sc hop), hasCompound_not_sc hop, bind, Except.bind])
                        | map entries dflt =>
                            first
                              | exact Or.inl (by
                                  simp [execW, hop, assignW, writeW, evalW, henv, hcond.1, hprim, hk, htyA, hk0, hs, scArm_of_not_sc (hasCompound_not_sc hop), hasCompound_not_sc hop, bind, Except.bind,
                                    hasCompound_arith hop, BinOp.retTy])
                              | exact Or.inr (by
                                  simp [execW, hop, assignW, writeW, evalW, henv, hcond.1, hprim, hk, htyA, hk0, hs, scArm_of_not_sc (hasCompound_not_sc hop), hasCompound_not_sc hop, bind, Except.bind])
                        | array elems =>
                          by_cases hlt : k.toNat < elems.length
                          case neg =>
                              exact Or.inr (by
                                simp [execW, hop, evalW, henv, hcond.1,
                                  hk, htyA, hk0, hs, hlt, bind,
                                  Except.bind])
                          case pos =>
                            cases hav : (elems[k.toNat]'hlt).asValue with
                            | error err =>
                                cases err
                                · cases hgd : elems[k.toNat]'hlt with
                                  | prim p =>
                                      cases p <;>
                                        (rw [hgd] at hav;
                                         simp [SVal.asValue] at hav)
                                  | _ =>
                                      (rw [hgd] at hav;
                                       simp [SVal.asValue] at hav)
                                · first
                                    | exact Or.inl (by
                                        simp [execW, hop, assignW, writeW, evalW, henv, hcond.1, hprim, hk, htyA, hk0, hs, hlt, hav, scArm_of_not_sc (hasCompound_not_sc hop), hasCompound_not_sc hop, bind, Except.bind,
                                        hasCompound_arith hop, BinOp.retTy])
                                    | exact Or.inr (by
                                        simp [execW, hop, assignW, writeW, evalW, henv, hcond.1, hprim, hk, htyA, hk0, hs, hlt, hav, scArm_of_not_sc (hasCompound_not_sc hop), hasCompound_not_sc hop, bind, Except.bind])
                            | ok old =>
                              cases hr : evalW s rhs with
                              | error err =>
                                  cases err <;>
                                    first
                                      | exact Or.inl (by
                                          simp [execW, hop, assignW, writeW, evalW, henv, hcond.1, hprim, hk, htyA, hk0, hs, hlt, hav, hr, scArm_of_not_sc (hasCompound_not_sc hop), hasCompound_not_sc hop, bind, Except.bind,
                                            hasCompound_arith hop, BinOp.retTy])
                                      | exact Or.inr (by
                                          simp [execW, hop, assignW, writeW, evalW, henv, hcond.1, hprim, hk, htyA, hk0, hs, hlt, hav, hr, scArm_of_not_sc (hasCompound_not_sc hop), hasCompound_not_sc hop, bind, Except.bind])
                              | ok rv =>
                                  cases hab : applyCheckedW op (Typed.WrappedExpr.index Kind.storage ty (Typed.WrappedExpr.var Kind.storage bty fld) key).ty old rv with
                                  | error err =>
                                      cases err <;>
                                        first
                                          | exact Or.inl (by
                                              simp [execW, hop, assignW, writeW, evalW, henv, hcond.1, hprim, hk, htyA, hk0, hs, hlt, hav, hr, hab, scArm_of_not_sc (hasCompound_not_sc hop), hasCompound_not_sc hop, bind, Except.bind,
                                                hasCompound_arith hop, BinOp.retTy])
                                          | exact Or.inr (by
                                              simp [execW, hop, assignW, writeW, evalW, henv, hcond.1, hprim, hk, htyA, hk0, hs, hlt, hav, hr, hab, scArm_of_not_sc (hasCompound_not_sc hop), hasCompound_not_sc hop, bind, Except.bind])
                                  | ok new =>
                                      first
                                        | exact Or.inl (by
                                            simp [execW, hop, assignW, writeW, evalW, henv, hcond.1, hprim, hk, htyA, hk0, hs, hlt, hav, hr, hab, scArm_of_not_sc (hasCompound_not_sc hop), hasCompound_not_sc hop, bind, Except.bind,
                                              hasCompound_arith hop, BinOp.retTy])
                                        | exact Or.inr (by
                                            simp [execW, hop, assignW, writeW, evalW, henv, hcond.1, hprim, hk, htyA, hk0, hs, hlt, hav, hr, hab, scArm_of_not_sc (hasCompound_not_sc hop), hasCompound_not_sc hop, bind, Except.bind])
                    case neg =>
                    by_cases hkb : 0 ≤ k ∧ k < keyBoundI
                    case neg =>
                        first
                          | exact Or.inl (by
                              simp [execW, hop, assignW, writeW, evalW, henv, hcond.1, hk, htyA, hkb, scArm_of_not_sc (hasCompound_not_sc hop), hasCompound_not_sc hop, bind, Except.bind,
                                hasCompound_arith hop, BinOp.retTy])
                          | exact Or.inr (by
                              simp [execW, hop, assignW, writeW, evalW, henv, hcond.1, hk, htyA, hkb, scArm_of_not_sc (hasCompound_not_sc hop), hasCompound_not_sc hop, bind, Except.bind])
                    case pos =>
                    cases hs : lookupBy fld.name s.storage with
                    | none =>
                        first
                          | exact Or.inl (by
                              simp [execW, hop, assignW, writeW, evalW, henv, hcond.1, hprim, hk, htyA, hkb, hs, scArm_of_not_sc (hasCompound_not_sc hop), hasCompound_not_sc hop, bind, Except.bind,
                                hasCompound_arith hop, BinOp.retTy])
                          | exact Or.inr (by
                              simp [execW, hop, assignW, writeW, evalW, henv, hcond.1, hprim, hk, htyA, hkb, hs, scArm_of_not_sc (hasCompound_not_sc hop), hasCompound_not_sc hop, bind, Except.bind])
                    | some sv =>
                      cases sv with
                      | prim p =>
                          cases p <;>
                            first
                              | exact Or.inl (by
                                  simp [execW, hop, assignW, writeW, evalW, henv, hcond.1, hprim, hk, htyA, hkb, hs, scArm_of_not_sc (hasCompound_not_sc hop), hasCompound_not_sc hop, bind, Except.bind,
                                    hasCompound_arith hop, BinOp.retTy])
                              | exact Or.inr (by
                                  simp [execW, hop, assignW, writeW, evalW, henv, hcond.1, hprim, hk, htyA, hkb, hs, scArm_of_not_sc (hasCompound_not_sc hop), hasCompound_not_sc hop, bind, Except.bind])
                      | struct fields =>
                          first
                            | exact Or.inl (by
                                simp [execW, hop, assignW, writeW, evalW, henv, hcond.1, hprim, hk, htyA, hkb, hs, scArm_of_not_sc (hasCompound_not_sc hop), hasCompound_not_sc hop, bind, Except.bind,
                                  hasCompound_arith hop, BinOp.retTy])
                            | exact Or.inr (by
                                simp [execW, hop, assignW, writeW, evalW, henv, hcond.1, hprim, hk, htyA, hkb, hs, scArm_of_not_sc (hasCompound_not_sc hop), hasCompound_not_sc hop, bind, Except.bind])
                      | array elems =>
                          first
                            | exact Or.inl (by
                                simp [execW, hop, assignW, writeW, evalW, henv, hcond.1, hprim, hk, htyA, hkb, hs, scArm_of_not_sc (hasCompound_not_sc hop), hasCompound_not_sc hop, bind, Except.bind,
                                  hasCompound_arith hop, BinOp.retTy])
                            | exact Or.inr (by
                                simp [execW, hop, assignW, writeW, evalW, henv, hcond.1, hprim, hk, htyA, hkb, hs, scArm_of_not_sc (hasCompound_not_sc hop), hasCompound_not_sc hop, bind, Except.bind])
                      | map entries dflt =>
                        cases hav : ((lookupBy k entries).getD
                            dflt).asValue with
                        | error err =>
                            cases err
                            · cases hgd : (lookupBy k entries).getD
                                  dflt with
                              | prim p =>
                                  cases p <;>
                                    (rw [hgd] at hav;
                                     simp [SVal.asValue] at hav)
                              | _ =>
                                  (rw [hgd] at hav;
                                   simp [SVal.asValue] at hav)
                            · first
                                | exact Or.inl (by
                                    simp [execW, hop, assignW, writeW, evalW, henv, hcond.1, hprim, hk, htyA, hkb, hs, hav, scArm_of_not_sc (hasCompound_not_sc hop), hasCompound_not_sc hop, bind, Except.bind,
                                    hasCompound_arith hop, BinOp.retTy])
                                | exact Or.inr (by
                                    simp [execW, hop, assignW, writeW, evalW, henv, hcond.1, hprim, hk, htyA, hkb, hs, hav, scArm_of_not_sc (hasCompound_not_sc hop), hasCompound_not_sc hop, bind, Except.bind])
                        | ok old =>
                          cases hr : evalW s rhs with
                          | error err =>
                              cases err <;>
                                first
                                  | exact Or.inl (by
                                      simp [execW, hop, assignW, writeW, evalW, henv, hcond.1, hprim, hk, htyA, hkb, hs, hav, hr, scArm_of_not_sc (hasCompound_not_sc hop), hasCompound_not_sc hop, bind, Except.bind,
                                        hasCompound_arith hop, BinOp.retTy])
                                  | exact Or.inr (by
                                      simp [execW, hop, assignW, writeW, evalW, henv, hcond.1, hprim, hk, htyA, hkb, hs, hav, hr, scArm_of_not_sc (hasCompound_not_sc hop), hasCompound_not_sc hop, bind, Except.bind])
                          | ok rv =>
                              cases hab : applyCheckedW op (Typed.WrappedExpr.index Kind.storage ty (Typed.WrappedExpr.var Kind.storage bty fld) key).ty old rv with
                              | error err =>
                                  cases err <;>
                                    first
                                      | exact Or.inl (by
                                          simp [execW, hop, assignW, writeW, evalW, henv, hcond.1, hprim, hk, htyA, hkb, hs, hav, hr, hab, scArm_of_not_sc (hasCompound_not_sc hop), hasCompound_not_sc hop, bind, Except.bind,
                                            hasCompound_arith hop, BinOp.retTy])
                                      | exact Or.inr (by
                                          simp [execW, hop, assignW, writeW, evalW, henv, hcond.1, hprim, hk, htyA, hkb, hs, hav, hr, hab, scArm_of_not_sc (hasCompound_not_sc hop), hasCompound_not_sc hop, bind, Except.bind])
                              | ok new =>
                                  first
                                    | exact Or.inl (by
                                        simp [execW, hop, assignW, writeW, evalW, henv, hcond.1, hprim, hk, htyA, hkb, hs, hav, hr, hab, scArm_of_not_sc (hasCompound_not_sc hop), hasCompound_not_sc hop, bind, Except.bind,
                                          hasCompound_arith hop, BinOp.retTy])
                                    | exact Or.inr (by
                                        simp [execW, hop, assignW, writeW, evalW, henv, hcond.1, hprim, hk, htyA, hkb, hs, hav, hr, hab, scArm_of_not_sc (hasCompound_not_sc hop), hasCompound_not_sc hop, bind, Except.bind])
            case _ => exact Option.noConfusion hc
  | .field fkind fty fbase lfld =>
      cases fkind with
      | memory => simp [compileAssign] at hc
      | stack => simp [compileAssign] at hc
      | storage =>
        match fbase with
        | .field .. => simp [compileAssign] at hc
        | .index .. => simp [compileAssign] at hc
        | .pushPlace .. => simp [compileAssign] at hc
        | .bool .. => simp [compileAssign] at hc
        | .intLit .. => simp [compileAssign] at hc
        | .mkCall .. => simp [compileAssign] at hc
        | .mkBinop .. => simp [compileAssign] at hc
        | .mkUnop .. => simp [compileAssign] at hc
        | .mkIncDec .. => simp [compileAssign] at hc
        | .mkTernary .. => simp [compileAssign] at hc
        | .var bkind bty fld =>
          cases bkind with
          | stack => simp [compileAssign] at hc
          | memory => simp [compileAssign] at hc
          | storage =>
            simp only [compileAssign] at hc
            split at hc
            case _ hcond =>
              have hprim := hcond.2.2
              have hAf : isArrayTy bty = false :=
                isArrayTy_eq_false_of_isStructTy hcond.2.1
              cases henv : lookupBy fld.name s.env with
              | some b =>
                  first
                    | exact Or.inl (by
                        simp [execW, hop, assignW, writeW, evalW, henv, bind, Except.bind,
                          hasCompound_arith hop, BinOp.retTy])
                    | exact Or.inr (by
                        simp [execW, hop, assignW, writeW, evalW, henv, bind, Except.bind])
              | none =>
                cases hs : lookupBy fld.name s.storage with
                | none =>
                    first
                      | exact Or.inl (by
                          simp [execW, hop, assignW, writeW, evalW, henv, hcond.1, hcond.2.1, hAf, hprim, hs, scArm_of_not_sc (hasCompound_not_sc hop), hasCompound_not_sc hop, bind, Except.bind,
                            hasCompound_arith hop, BinOp.retTy])
                      | exact Or.inr (by
                          simp [execW, hop, assignW, writeW, evalW, henv, hcond.1, hcond.2.1, hAf, hprim, hs, scArm_of_not_sc (hasCompound_not_sc hop), hasCompound_not_sc hop, bind, Except.bind])
                | some sv =>
                  cases sv with
                  | prim p =>
                      cases p <;>
                        first
                          | exact Or.inl (by
                              simp [execW, hop, assignW, writeW, evalW, henv, hcond.1, hcond.2.1, hAf, hprim, hs, scArm_of_not_sc (hasCompound_not_sc hop), hasCompound_not_sc hop, bind, Except.bind,
                                hasCompound_arith hop, BinOp.retTy])
                          | exact Or.inr (by
                              simp [execW, hop, assignW, writeW, evalW, henv, hcond.1, hcond.2.1, hAf, hprim, hs, scArm_of_not_sc (hasCompound_not_sc hop), hasCompound_not_sc hop, bind, Except.bind])
                  | array elems =>
                      first
                        | exact Or.inl (by
                            simp [execW, hop, assignW, writeW, evalW, henv, hcond.1, hcond.2.1, hAf, hprim, hs, scArm_of_not_sc (hasCompound_not_sc hop), hasCompound_not_sc hop, bind, Except.bind,
                              hasCompound_arith hop, BinOp.retTy])
                        | exact Or.inr (by
                            simp [execW, hop, assignW, writeW, evalW, henv, hcond.1, hcond.2.1, hAf, hprim, hs, scArm_of_not_sc (hasCompound_not_sc hop), hasCompound_not_sc hop, bind, Except.bind])
                  | map entries dflt =>
                      first
                        | exact Or.inl (by
                            simp [execW, hop, assignW, writeW, evalW, henv, hcond.1, hcond.2.1, hAf, hprim, hs, scArm_of_not_sc (hasCompound_not_sc hop), hasCompound_not_sc hop, bind, Except.bind,
                              hasCompound_arith hop, BinOp.retTy])
                        | exact Or.inr (by
                            simp [execW, hop, assignW, writeW, evalW, henv, hcond.1, hcond.2.1, hAf, hprim, hs, scArm_of_not_sc (hasCompound_not_sc hop), hasCompound_not_sc hop, bind, Except.bind])
                  | struct sfields =>
                    by_cases hspine : sfields.map Prod.fst
                        = structSpineOf bty
                    case neg =>
                        first
                          | exact Or.inl (by
                              simp [execW, hop, assignW, writeW, evalW, henv, hcond.1, hcond.2.1, hAf, hprim, hs, hspine, scArm_of_not_sc (hasCompound_not_sc hop), hasCompound_not_sc hop, bind, Except.bind,
                                hasCompound_arith hop, BinOp.retTy])
                          | exact Or.inr (by
                              simp [execW, hop, assignW, writeW, evalW, henv, hcond.1, hcond.2.1, hAf, hprim, hs, hspine, scArm_of_not_sc (hasCompound_not_sc hop), hasCompound_not_sc hop, bind, Except.bind])
                    case pos =>
                    cases hlf : lookupBy lfld.name sfields with
                    | none =>
                        first
                          | exact Or.inl (by
                              simp [execW, hop, assignW, writeW, evalW, henv, hcond.1, hcond.2.1, hAf, hprim, hs, hspine, hlf, scArm_of_not_sc (hasCompound_not_sc hop), hasCompound_not_sc hop, bind, Except.bind,
                                hasCompound_arith hop, BinOp.retTy])
                          | exact Or.inr (by
                              simp [execW, hop, assignW, writeW, evalW, henv, hcond.1, hcond.2.1, hAf, hprim, hs, hspine, hlf, scArm_of_not_sc (hasCompound_not_sc hop), hasCompound_not_sc hop, bind, Except.bind])
                    | some v0 =>
                      cases hav : v0.asValue with
                      | error err =>
                          cases err
                          · cases v0 with
                            | prim p =>
                                cases p <;> simp [SVal.asValue] at hav
                            | _ => simp [SVal.asValue] at hav
                          · first
                              | exact Or.inl (by
                                  simp [execW, hop, assignW, writeW, evalW, henv, hcond.1, hcond.2.1, hAf, hprim, hs, hspine, hlf, hav, scArm_of_not_sc (hasCompound_not_sc hop), hasCompound_not_sc hop, bind, Except.bind,
                                  hasCompound_arith hop, BinOp.retTy])
                              | exact Or.inr (by
                                  simp [execW, hop, assignW, writeW, evalW, henv, hcond.1, hcond.2.1, hAf, hprim, hs, hspine, hlf, hav, scArm_of_not_sc (hasCompound_not_sc hop), hasCompound_not_sc hop, bind, Except.bind])
                      | ok old =>
                        cases hr : evalW s rhs with
                        | error err =>
                            cases err <;>
                              first
                                | exact Or.inl (by
                                    simp [execW, hop, assignW, writeW, evalW, henv, hcond.1, hcond.2.1, hAf, hprim, hs, hspine, hlf, hav, hr, scArm_of_not_sc (hasCompound_not_sc hop), hasCompound_not_sc hop, bind, Except.bind,
                                      hasCompound_arith hop, BinOp.retTy])
                                | exact Or.inr (by
                                    simp [execW, hop, assignW, writeW, evalW, henv, hcond.1, hcond.2.1, hAf, hprim, hs, hspine, hlf, hav, hr, scArm_of_not_sc (hasCompound_not_sc hop), hasCompound_not_sc hop, bind, Except.bind])
                        | ok rv =>
                          cases hab : applyCheckedW op (Typed.WrappedExpr.field Kind.storage fty (Typed.WrappedExpr.var Kind.storage bty fld) lfld).ty old rv with
                          | error err =>
                              cases err <;>
                                first
                                  | exact Or.inl (by
                                      simp [execW, hop, assignW, writeW, evalW, henv, hcond.1, hcond.2.1, hAf, hprim, hs, hspine, hlf, hav, hr, hab, scArm_of_not_sc (hasCompound_not_sc hop), hasCompound_not_sc hop, bind, Except.bind,
                                        hasCompound_arith hop, BinOp.retTy])
                                  | exact Or.inr (by
                                      simp [execW, hop, assignW, writeW, evalW, henv, hcond.1, hcond.2.1, hAf, hprim, hs, hspine, hlf, hav, hr, hab, scArm_of_not_sc (hasCompound_not_sc hop), hasCompound_not_sc hop, bind, Except.bind])
                          | ok nv =>
                              first
                                | exact Or.inl (by
                                    simp [execW, hop, assignW, writeW, evalW, henv, hcond.1, hcond.2.1, hAf, hprim, hs, hspine, hlf, hav, hr, hab, scArm_of_not_sc (hasCompound_not_sc hop), hasCompound_not_sc hop, bind, Except.bind,
                                      hasCompound_arith hop, BinOp.retTy])
                                | exact Or.inr (by
                                    simp [execW, hop, assignW, writeW, evalW, henv, hcond.1, hcond.2.1, hAf, hprim, hs, hspine, hlf, hav, hr, hab, scArm_of_not_sc (hasCompound_not_sc hop), hasCompound_not_sc hop, bind, Except.bind])
            case _ => exact Option.noConfusion hc
  | .pushPlace .. => simp [compileAssign] at hc
  | .bool .. => simp [compileAssign] at hc
  | .intLit .. => simp [compileAssign] at hc
  | .mkCall .. => simp [compileAssign] at hc
  | .mkBinop .. => simp [compileAssign] at hc
  | .mkUnop .. => simp [compileAssign] at hc
  | .mkIncDec .. => simp [compileAssign] at hc
  | .mkTernary .. => simp [compileAssign] at hc

/-- `SWAP (i+1); POP` writes stack slot `i`. -/
theorem writeLocal_steps {C : Code} {pcw i : Nat}
    (hcodew : codeAt C pcw [Instr.swap (i + 1), Instr.pop])
    {w wi : Word} {σ : List Word} {st : Store} (hσi : σ[i]? = some wi) :
    Steps C ⟨pcw, w :: σ, st⟩ ⟨pcw + 2, σ.set i w, st⟩ := by
  refine Steps.head (Step.swap hcodew.fetch rfl (by simpa using hσi)) ?_
  refine Steps.cast_pc (Steps.single (Step.pop (hcodew.tail).fetch)) ?_
  omega

/-- Simulation of a compiled assignment: the generated code follows the
interpreter's order (mapping target key first, then the right-hand
side) and performs the write. -/
theorem compileAssign_sim (L Γ : List Name) (lhs rhs : WrappedExpr)
    {code : Code} (hc : compileAssign L Γ lhs rhs = some code)
    (s : State) {C : Code} {base : Nat} (hcode : codeAt C base code)
    {σ : List Word} {st : Store} (hrepr : ReprState L Γ s σ st) :
    ExecClaim C base code.length L Γ σ st (assignW s lhs rhs) := by
  match lhs with
  | .var .stack ty fld =>
      simp only [compileAssign] at hc
      split at hc
      case _ hprim =>
        cases hfi : Γ.findIdx? (· = fld.name) with
        | none => rw [hfi] at hc; exact Option.noConfusion hc
        | some i =>
            simp only [hfi] at hc
            split at hc
            case _ hdepth =>
              cases hcr : compileExpr L Γ 0 rhs with
              | none => rw [hcr] at hc; simp [bind, Option.bind] at hc
              | some cr =>
                  simp only [hcr, bind, Option.bind, pure,
                    Option.pure_def, Option.some.injEq] at hc
                  subst hc
                  have hΓi := findIdx?_eq_name hfi
                  have ihr := compileExpr_sim L Γ 0 rhs hcr s
                    (σt := []) (hcode.append_left) rfl hrepr
                  simp only [List.nil_append] at ihr
                  have hcodew : codeAt C (base + cr.length)
                      [Instr.swap (i + 1), Instr.pop] :=
                    hcode.append_right
                  simp only [assignW]
                  cases hv : evalW s rhs with
                  | error err =>
                      cases err
                      · rw [hv] at ihr
                        simp only [EvalClaim_revert] at ihr
                        simp only [hv, bind, Except.bind, ExecClaim_revert]
                        exact ihr
                      · simp only [hv, bind, Except.bind]
                        exact ExecClaim_stuck
                  | ok v =>
                      rw [hv] at ihr
                      simp only [EvalClaim_ok] at ihr
                      obtain ⟨w, hw, hsteps⟩ := ihr
                      obtain ⟨v', wi, henv, hσi, hrvi⟩ :=
                        hrepr.locals i fld.name hΓi
                      simp only [hv, bind, Except.bind, ExecClaim_ok]
                      refine ⟨σ.set i w, st, ?_, ?_⟩
                      · refine Steps.trans hsteps ?_
                        refine Steps.cast_pc
                          (writeLocal_steps hcodew hσi) ?_
                        simp only [List.length_append, List.length_cons,
                          List.length_nil]
                        omega
                      · exact hrepr.setLocal hΓi hw
            case _ => exact Option.noConfusion hc
      case _ => exact Option.noConfusion hc
  | .var .memory ty fld => simp [compileAssign] at hc
  | .var .storage ty fld =>
      simp only [compileAssign] at hc
      split at hc
      case _ hcond =>
        cases hslot : slotOf? L fld.name with
        | none => rw [hslot] at hc; exact Option.noConfusion hc
        | some i =>
            simp only [hslot] at hc
            cases hcr : compileExpr L Γ 0 rhs with
            | none => rw [hcr] at hc; simp [bind, Option.bind] at hc
            | some cr =>
                simp only [hcr, bind, Option.bind, pure,
                  Option.pure_def, Option.some.injEq] at hc
                subst hc
                have hLidx : L[i]? = some fld.name :=
                  findIdx?_eq_name (by simpa [slotOf?] using hslot)
                obtain ⟨sv, hst, hroot⟩ := hrepr.roots i fld.name hLidx
                have ihr := compileExpr_sim L Γ 0 rhs hcr s
                  (σt := []) (hcode.append_left) rfl hrepr
                simp only [List.nil_append] at ihr
                have hcodew : codeAt C (base + cr.length)
                    [Instr.push (slotWord i), Instr.sstore] :=
                  hcode.append_right
                simp only [assignW, hcond, and_self, if_true]
                cases hv : evalW s rhs with
                | error err =>
                    cases err
                    · rw [hv] at ihr
                      simp only [EvalClaim_revert] at ihr
                      simp only [hv, bind, Except.bind, ExecClaim_revert]
                      exact ihr
                    · simp only [hv, bind, Except.bind]
                      exact ExecClaim_stuck
                | ok v =>
                    rw [hv] at ihr
                    simp only [EvalClaim_ok] at ihr
                    obtain ⟨w, hw, hsteps⟩ := ihr
                    simp only [hv, bind, Except.bind, hst, ExecClaim_ok]
                    refine ⟨σ, st.write (slotWord i) w, ?_, ?_⟩
                    · refine Steps.trans hsteps ?_
                      refine Steps.head (Step.push hcodew.fetch) ?_
                      refine Steps.cast_pc (Steps.single
                        (Step.sstore (hcodew.tail).fetch)) ?_
                      simp only [List.length_append, List.length_cons,
                        List.length_nil]
                      omega
                    · exact hrepr.setRoot hLidx hw
      case _ => exact Option.noConfusion hc
  | .index kind ty mbase key =>
      cases kind with
      | memory => simp [compileAssign] at hc
      | stack => simp [compileAssign] at hc
      | storage =>
        match mbase with
        | .field .. => simp [compileAssign] at hc
        | .index .. => simp [compileAssign] at hc
        | .pushPlace .. => simp [compileAssign] at hc
        | .bool .. => simp [compileAssign] at hc
        | .intLit .. => simp [compileAssign] at hc
        | .mkCall .. => simp [compileAssign] at hc
        | .mkBinop .. => simp [compileAssign] at hc
        | .mkUnop .. => simp [compileAssign] at hc
        | .mkIncDec .. => simp [compileAssign] at hc
        | .mkTernary .. => simp [compileAssign] at hc
        | .var bkind bty fld =>
          cases bkind with
          | stack => simp [compileAssign] at hc
          | memory => simp [compileAssign] at hc
          | storage =>
            simp only [compileAssign] at hc
            split at hc
            case _ hcond =>
              cases hslot : slotOf? L fld.name with
              | none => rw [hslot] at hc; exact Option.noConfusion hc
              | some i =>
                simp only [hslot] at hc
                by_cases htyA : isArrayTy bty = true
                case pos =>
                  rw [if_pos htyA] at hc
                  cases hck : compileExpr L Γ 0 key with
                  | none => rw [hck] at hc; simp [bind, Option.bind] at hc
                  | some ck =>
                    simp only [hck, bind, Option.bind] at hc
                    cases hcr : compileExpr L Γ 1 rhs with
                    | none =>
                        rw [hcr] at hc; simp [bind, Option.bind] at hc
                    | some cr =>
                      simp only [hcr, bind, Option.bind, pure,
                        Option.pure_def, Option.some.injEq] at hc
                      subst hc
                      have hLidx : L[i]? = some fld.name :=
                        findIdx?_eq_name (by simpa [slotOf?] using hslot)
                      have hmem : fld.name ∈ L :=
                        List.mem_of_getElem? hLidx
                      have henv : lookupBy fld.name s.env = none :=
                        hrepr.rootsEnv _ hmem
                      have hcodeck : codeAt C base ck :=
                        (hcode.append_left).append_left
                      have hcodecr : codeAt C (base + ck.length) cr :=
                        (hcode.append_left).append_right
                      have hcodew : codeAt C
                          (base + ck.length + cr.length)
                          [Instr.push (slotWord i), Instr.sload,
                           Instr.dup 3, Instr.lt, Instr.jumpi 1,
                           Instr.revert, Instr.swap 1,
                           Instr.push (slotWord i), Instr.mapslot,
                           Instr.sstore] :=
                        codeAt_cast (hcode.append_right)
                          (by simp only [List.length_append]; omega)
                      have ihk := compileExpr_sim L Γ 0 key hck s
                        (σt := []) hcodeck rfl hrepr
                      simp only [List.nil_append] at ihk
                      simp only [assignW, henv, hcond.1, hcond.2,
                        if_true]
                      cases hk : evalW s key with
                      | error err =>
                          simp only [hk]
                          exact ExecClaim_stuck
                      | ok kv =>
                        rw [hk] at ihk
                        simp only [EvalClaim_ok] at ihk
                        obtain ⟨kw, hkwv, hstepsk⟩ := ihk
                        simp only [hk, bind, Except.bind]
                        cases kv with
                        | bool b => exact ExecClaim_stuck
                        | int k =>
                          simp only [ReprVal] at hkwv
                          have hk0 : 0 ≤ k := by omega
                          simp only [if_pos htyA, if_pos hk0]
                          obtain ⟨sv, hst, hroot⟩ :=
                            hrepr.roots i fld.name hLidx
                          cases sv with
                          | prim p => cases p <;> (rw [hst]; exact ExecClaim_stuck)
                          | struct fields =>
                              rw [hst]; exact ExecClaim_stuck
                          | map entries dflt =>
                              rw [hst]; exact ExecClaim_stuck
                          | array elems =>
                            simp only [hst]
                            have ihr := compileExpr_sim L Γ 1 rhs hcr s
                              (σt := [kw]) hcodecr rfl hrepr
                            simp only [List.cons_append, List.nil_append]
                              at ihr
                            cases hr : evalW s rhs with
                            | error err =>
                                cases err
                                · rw [hr] at ihr
                                  simp only [EvalClaim_revert] at ihr
                                  simp only [hr, bind, Except.bind,
                                    ExecClaim_revert]
                                  exact Reverting.of_steps hstepsk ihr
                                · simp only [hr, bind, Except.bind]
                                  exact ExecClaim_stuck
                            | ok v =>
                              rw [hr] at ihr
                              simp only [EvalClaim_ok] at ihr
                              obtain ⟨w, hw, hstepsr⟩ := ihr
                              simp only [hr, bind, Except.bind]
                              have hroot' := hroot
                              simp only [ReprRoot] at hroot'
                              obtain ⟨hlen, hlslot, helems⟩ := hroot'
                              have hfpush1 := hcodew.fetch
                              have hfsload := (hcodew.tail).fetch
                              have hfdup := ((hcodew.tail).tail).fetch
                              have hflt :=
                                (((hcodew.tail).tail).tail).fetch
                              have hfjumpi :=
                                ((((hcodew.tail).tail).tail).tail).fetch
                              have hfrevert :=
                                (((((hcodew.tail).tail).tail).tail).tail).fetch
                              have hfswap :=
                                ((((((hcodew.tail).tail).tail).tail).tail).tail).fetch
                              have hfpush2 :=
                                (((((((hcodew.tail).tail).tail).tail).tail).tail).tail).fetch
                              have hfmapslot :=
                                ((((((((hcodew.tail).tail).tail).tail).tail).tail).tail).tail).fetch
                              have hfsstore :=
                                (((((((((hcodew.tail).tail).tail).tail).tail).tail).tail).tail).tail).fetch
                              by_cases hlt : k.toNat < elems.length
                              case pos =>
                                simp only [if_pos hlt]
                                simp only [ExecClaim_ok]
                                have hult : BitVec.ult kw
                                    (BitVec.ofNat 256 elems.length)
                                    = true := by
                                  simp only [BitVec.ult,
                                    decide_eq_true_eq]
                                  rw [BitVec.toNat_ofNat]
                                  simp only [keyBound] at hlen
                                  omega
                                refine ⟨σ,
                                  st.write (mapSlotW (slotWord i) kw) w,
                                  ?_, ?_⟩
                                · refine Steps.trans hstepsk ?_
                                  refine Steps.trans hstepsr ?_
                                  refine Steps.head
                                    (Step.push hfpush1) ?_
                                  refine Steps.head
                                    (Step.sload hfsload) ?_
                                  rw [hlslot]
                                  refine Steps.head
                                    (Step.dup hfdup rfl) ?_
                                  refine Steps.head (Step.lt hflt) ?_
                                  rw [hult]
                                  simp only [wBool_true]
                                  refine Steps.head (Step.jumpiTrue
                                    hfjumpi one_ne_zero_word) ?_
                                  refine Steps.head
                                    (Step.swap hfswap rfl rfl) ?_
                                  refine Steps.head
                                    (Step.push hfpush2) ?_
                                  refine Steps.head
                                    (Step.mapslot hfmapslot) ?_
                                  refine Steps.cast_pc (Steps.single
                                    (Step.sstore hfsstore)) ?_
                                  simp only [List.length_append,
                                    List.length_cons, List.length_nil]
                                  omega
                                · exact hrepr.setArrayElem hLidx hst
                                    hk0 hlt hw hkwv
                              case neg =>
                                simp only [if_neg hlt]
                                simp only [ExecClaim_revert]
                                have hult : BitVec.ult kw
                                    (BitVec.ofNat 256 elems.length)
                                    = false := by
                                  simp only [BitVec.ult]
                                  rw [decide_eq_false_iff_not]
                                  rw [BitVec.toNat_ofNat]
                                  simp only [keyBound] at hlen
                                  omega
                                refine Reverting.of_steps hstepsk ?_
                                refine Reverting.of_steps hstepsr ?_
                                refine ⟨⟨base + ck.length + cr.length
                                    + 1 + 1 + 1 + 1 + 1,
                                  w :: kw :: σ, st⟩, ?_, ?_⟩
                                · refine Steps.head
                                    (Step.push hfpush1) ?_
                                  refine Steps.head
                                    (Step.sload hfsload) ?_
                                  rw [hlslot]
                                  refine Steps.head
                                    (Step.dup hfdup rfl) ?_
                                  refine Steps.head (Step.lt hflt) ?_
                                  rw [hult]
                                  simp only [wBool_false]
                                  exact Steps.single
                                    (Step.jumpiFalse hfjumpi)
                                · exact hfrevert
                case neg =>
                rw [if_neg htyA] at hc
                cases hck : compileExpr L Γ 0 key with
                | none => rw [hck] at hc; simp [bind, Option.bind] at hc
                | some ck =>
                  simp only [hck, bind, Option.bind] at hc
                  cases hcr : compileExpr L Γ 1 rhs with
                  | none =>
                      rw [hcr] at hc; simp [bind, Option.bind] at hc
                  | some cr =>
                    simp only [hcr, bind, Option.bind, pure,
                      Option.pure_def, Option.some.injEq] at hc
                    subst hc
                    have hLidx : L[i]? = some fld.name :=
                      findIdx?_eq_name (by simpa [slotOf?] using hslot)
                    have hmem : fld.name ∈ L :=
                      List.mem_of_getElem? hLidx
                    have henv : lookupBy fld.name s.env = none :=
                      hrepr.rootsEnv _ hmem
                    -- code = (ck ++ cr) ++ [swap 1, push, mapslot, sstore]
                    have hcodeck : codeAt C base ck :=
                      (hcode.append_left).append_left
                    have hcodecr : codeAt C (base + ck.length) cr :=
                      (hcode.append_left).append_right
                    have hcodew : codeAt C (base + ck.length + cr.length)
                        [Instr.swap 1, Instr.push (slotWord i),
                         Instr.mapslot, Instr.sstore] :=
                      codeAt_cast (hcode.append_right)
                        (by simp only [List.length_append]; omega)
                    have ihk := compileExpr_sim L Γ 0 key hck s
                      (σt := []) hcodeck rfl hrepr
                    simp only [List.nil_append] at ihk
                    simp only [assignW, henv, hcond.1, hcond.2,
                      if_true]
                    cases hk : evalW s key with
                    | error err =>
                        simp only [hk]
                        exact ExecClaim_stuck
                    | ok kv =>
                      rw [hk] at ihk
                      simp only [EvalClaim_ok] at ihk
                      obtain ⟨kw, hkwv, hstepsk⟩ := ihk
                      simp only [hk, bind, Except.bind]
                      cases kv with
                      | bool b => exact ExecClaim_stuck
                      | int k =>
                        simp only [if_neg htyA]
                        by_cases hkb : 0 ≤ k ∧ k < keyBoundI
                        case neg =>
                            simp only [if_neg hkb]
                            exact ExecClaim_stuck
                        case pos =>
                        simp only [if_pos hkb]
                        obtain ⟨sv, hst, hroot⟩ :=
                          hrepr.roots i fld.name hLidx
                        cases sv with
                        | prim p => cases p <;> (rw [hst]; exact ExecClaim_stuck)
                        | struct fields =>
                            rw [hst]; exact ExecClaim_stuck
                        | array elems =>
                            rw [hst]; exact ExecClaim_stuck
                        | map entries dflt =>
                          rw [hst]
                          have ihr := compileExpr_sim L Γ 1 rhs hcr s
                            (σt := [kw]) hcodecr rfl hrepr
                          simp only [List.cons_append, List.nil_append]
                            at ihr
                          cases hr : evalW s rhs with
                          | error err =>
                              cases err
                              · rw [hr] at ihr
                                simp only [EvalClaim_revert] at ihr
                                simp only [hr, bind, Except.bind,
                                  ExecClaim_revert]
                                exact Reverting.of_steps hstepsk ihr
                              · simp only [hr, bind, Except.bind]
                                exact ExecClaim_stuck
                          | ok v =>
                            rw [hr] at ihr
                            simp only [EvalClaim_ok] at ihr
                            obtain ⟨w, hw, hstepsr⟩ := ihr
                            simp only [hr, bind, Except.bind]
                            simp only [ExecClaim_ok]
                            refine ⟨σ,
                              st.write (mapSlotW (slotWord i) kw) w,
                              ?_, ?_⟩
                            · refine Steps.trans hstepsk ?_
                              refine Steps.trans hstepsr ?_
                              refine Steps.head
                                (Step.swap hcodew.fetch rfl rfl) ?_
                              refine Steps.head
                                (Step.push (hcodew.tail).fetch) ?_
                              refine Steps.head
                                (Step.mapslot
                                  ((hcodew.tail).tail).fetch) ?_
                              refine Steps.cast_pc (Steps.single
                                (Step.sstore
                                  (((hcodew.tail).tail).tail).fetch)) ?_
                              simp only [List.length_append,
                                List.length_cons, List.length_nil]
                              omega
                            · exact hrepr.setMapRoot hLidx hst hkb.1
                                hkb.2 hw hkwv
            case _ => exact Option.noConfusion hc
  | .field fkind fty fbase lfld =>
      cases fkind with
      | memory => simp [compileAssign] at hc
      | stack => simp [compileAssign] at hc
      | storage =>
        match fbase with
        | .field .. => simp [compileAssign] at hc
        | .index .. => simp [compileAssign] at hc
        | .pushPlace .. => simp [compileAssign] at hc
        | .bool .. => simp [compileAssign] at hc
        | .intLit .. => simp [compileAssign] at hc
        | .mkCall .. => simp [compileAssign] at hc
        | .mkBinop .. => simp [compileAssign] at hc
        | .mkUnop .. => simp [compileAssign] at hc
        | .mkIncDec .. => simp [compileAssign] at hc
        | .mkTernary .. => simp [compileAssign] at hc
        | .var bkind bty fld =>
          cases bkind with
          | stack => simp [compileAssign] at hc
          | memory => simp [compileAssign] at hc
          | storage =>
            simp only [compileAssign] at hc
            split at hc
            case _ hcond =>
              cases bty with
              | prim p => simp [isStructTy] at hcond
              | ref r =>
                cases r with
                | array e => simp [isStructTy] at hcond
                | mapping kt vt => simp [isStructTy] at hcond
                | struct sname =>
                  cases hslot : slotOf? L fld.name with
                  | none =>
                      rw [hslot] at hc; exact Option.noConfusion hc
                  | some i =>
                    simp only [hslot] at hc
                    cases hsidx : structIdx? sname lfld.name with
                    | none =>
                        rw [hsidx] at hc; exact Option.noConfusion hc
                    | some j =>
                      simp only [hsidx] at hc
                      split at hc
                      case _ hjb =>
                        cases hcr : compileExpr L Γ 0 rhs with
                        | none =>
                            rw [hcr] at hc
                            simp [bind, Option.bind] at hc
                        | some cr =>
                          simp only [hcr, bind, Option.bind, pure,
                            Option.pure_def, Option.some.injEq] at hc
                          subst hc
                          have hLidx : L[i]? = some fld.name :=
                            findIdx?_eq_name
                              (by simpa [slotOf?] using hslot)
                          have hmem : fld.name ∈ L :=
                            List.mem_of_getElem? hLidx
                          have henv : lookupBy fld.name s.env = none :=
                            hrepr.rootsEnv _ hmem
                          have ihr := compileExpr_sim L Γ 0 rhs hcr s
                            (σt := []) (hcode.append_left) rfl hrepr
                          simp only [List.nil_append] at ihr
                          have hcodew : codeAt C (base + cr.length)
                              [Instr.push (mapSlotW (slotWord i)
                                (BitVec.ofNat 256 j)), Instr.sstore] :=
                            hcode.append_right
                          have hcondSI : fld.origin
                              = some StorageOrigin.global ∧
                              isStructTy (Ty.ref (RefTy.struct sname))
                                = true := ⟨hcond.1, hcond.2.1⟩
                          simp only [assignW, henv, if_pos hcondSI,
                            if_pos hcond.2.2]
                          cases hr : evalW s rhs with
                          | error err =>
                              cases err
                              · rw [hr] at ihr
                                simp only [EvalClaim_revert] at ihr
                                simp only [hr, bind, Except.bind,
                                  ExecClaim_revert]
                                exact ihr
                              · simp only [hr, bind, Except.bind]
                                exact ExecClaim_stuck
                          | ok v =>
                            rw [hr] at ihr
                            simp only [EvalClaim_ok] at ihr
                            obtain ⟨w, hw, hstepsr⟩ := ihr
                            simp only [hr, bind, Except.bind]
                            obtain ⟨sv, hst, hroot⟩ :=
                              hrepr.roots i fld.name hLidx
                            cases sv with
                            | prim p => cases p <;> (rw [hst]; exact ExecClaim_stuck)
                            | array elems =>
                                rw [hst]; exact ExecClaim_stuck
                            | map entries dflt =>
                                rw [hst]; exact ExecClaim_stuck
                            | struct sfields =>
                              simp only [hst]
                              by_cases hspine : sfields.map Prod.fst
                                  = structSpineOf
                                    (Ty.ref (RefTy.struct sname))
                              case neg =>
                                simp only [if_neg hspine]
                                exact ExecClaim_stuck
                              case pos =>
                              simp only [if_pos hspine]
                              have hspine' : sfields.map Prod.fst
                                  = (Semantics.structDef sname).map
                                      Prod.fst := by
                                simpa [structSpineOf] using hspine
                              have hidxSpine :
                                  ((Semantics.structDef sname).map
                                    Prod.fst).findIdx?
                                      (· = lfld.name) = some j := by
                                rw [List.findIdx?_map]
                                exact hsidx
                              obtain ⟨hjlt', hlook, hsetp, hspp⟩ :=
                                struct_field_at_findIdx hspine'
                                  hidxSpine
                              simp only [hlook]
                              rw [hsetp v.toSVal]
                              simp only [ExecClaim_ok]
                              refine ⟨σ, st.write (mapSlotW (slotWord i)
                                  (BitVec.ofNat 256 j)) w, ?_, ?_⟩
                              · refine Steps.trans hstepsr ?_
                                refine Steps.head
                                  (Step.push hcodew.fetch) ?_
                                refine Steps.cast_pc (Steps.single
                                  (Step.sstore (hcodew.tail).fetch)) ?_
                                first
                                | omega
                                | (simp only [List.length_append,
                                    List.length_cons,
                                    List.length_nil] <;> omega)
                              · exact hrepr.setStructField hLidx hst
                                  hjlt' hw
                      case _ => exact Option.noConfusion hc
            case _ => exact Option.noConfusion hc
  | .pushPlace .. => simp [compileAssign] at hc
  | .bool .. => simp [compileAssign] at hc
  | .intLit .. => simp [compileAssign] at hc
  | .mkCall .. => simp [compileAssign] at hc
  | .mkBinop .. => simp [compileAssign] at hc
  | .mkUnop .. => simp [compileAssign] at hc
  | .mkIncDec .. => simp [compileAssign] at hc
  | .mkTernary .. => simp [compileAssign] at hc

/-- The word representing a `stackDecl` default value. -/
theorem reprVal_default {ty : Ty} (hprim : ty.isPrimitive = true) :
    ReprVal (match ty with
             | Ty.bool => Value.bool false
             | _ => Value.int 0) (0 : Word) := by
  cases ty with
  | prim p => cases p <;> simp_all [ReprVal, Ty.isPrimitive, wBool]
  | ref r => simp_all [ReprVal, Ty.isPrimitive, wBool]

/-- The word representing the default storage value of a primitive
type (a valueless `push`). -/
theorem reprSVal_default {ty : Ty} (hprim : ty.isPrimitive = true) :
    ReprSVal (defaultForTy ty) 0 := by
  cases ty with
  | prim p =>
      cases p <;>
        simp_all [defaultForTy, defaultForFields, ReprSVal, Ty.isPrimitive,
          wBool]
  | ref r =>
      simp_all [defaultForTy, defaultForFields, ReprSVal, Ty.isPrimitive,
        wBool]

/-- The instruction tail shared by both `push` code paths: with the new
element's word and the length word on the stack, store the element at
the derived slot of index `length` and bump the length slot. -/
theorem pushTail_steps {C : Code} {p i : Nat}
    (hcodew : codeAt C p [Instr.dup 2, Instr.push (slotWord i),
      Instr.mapslot, Instr.sstore, Instr.push 1, Instr.add,
      Instr.push (slotWord i), Instr.sstore])
    {w lenw : Word} {σ : List Word} {st : Store} :
    Steps C ⟨p, w :: lenw :: σ, st⟩
      ⟨p + 8, σ, (st.write (mapSlotW (slotWord i) lenw) w).write
        (slotWord i) (1 + lenw)⟩ := by
  refine Steps.head (Step.dup hcodew.fetch rfl) ?_
  refine Steps.head (Step.push (hcodew.tail).fetch) ?_
  refine Steps.head (Step.mapslot ((hcodew.tail).tail).fetch) ?_
  refine Steps.head (Step.sstore (((hcodew.tail).tail).tail).fetch) ?_
  refine Steps.head
    (Step.push ((((hcodew.tail).tail).tail).tail).fetch) ?_
  refine Steps.head
    (Step.add (((((hcodew.tail).tail).tail).tail).tail).fetch) ?_
  refine Steps.head
    (Step.push
      ((((((hcodew.tail).tail).tail).tail).tail).tail).fetch) ?_
  refine Steps.cast_pc (Steps.single (Step.sstore
    (((((((hcodew.tail).tail).tail).tail).tail).tail).tail).fetch)) ?_
  omega

mutual

theorem compileStmt_sim (L Γ : List Name) (stmt : Stmt)
    {code : Code} {Γ' : List Name}
    (hc : compileStmt L Γ stmt = some (code, Γ'))
    (s : State) {C : Code} {base : Nat} (hcode : codeAt C base code)
    {σ : List Word} {st : Store} (hrepr : ReprState L Γ s σ st) :
    ExecClaim C base code.length L Γ' σ st (execW s stmt) := by
  match stmt with
  | .expr e =>
      simp only [compileStmt] at hc
      cases hce : compileExpr L Γ 0 e with
      | none => rw [hce] at hc; simp [bind, Option.bind] at hc
      | some ce =>
          simp only [hce, bind, Option.bind, pure, Option.pure_def,
            Option.some.injEq, Prod.mk.injEq] at hc
          obtain ⟨hc1, hc2⟩ := hc
          subst hc1 hc2
          have ihr := compileExpr_sim L Γ 0 e hce s (σt := [])
            (hcode.append_left) rfl hrepr
          simp only [List.nil_append] at ihr
          simp only [execW]
          cases hv : evalW s e with
          | error err =>
              cases err
              · rw [hv] at ihr
                simp only [EvalClaim_revert] at ihr
                simp only [hv, bind, Except.bind, ExecClaim_revert]
                exact ihr
              · simp only [hv, bind, Except.bind]
                exact ExecClaim_stuck
          | ok v =>
              rw [hv] at ihr
              simp only [EvalClaim_ok] at ihr
              obtain ⟨w, hw, hsteps⟩ := ihr
              simp only [hv, bind, Except.bind, ExecClaim_ok]
              refine ⟨σ, st, ?_, hrepr⟩
              refine Steps.trans hsteps ?_
              refine Steps.cast_pc (Steps.single
                (Step.pop (hcode.append_right).fetch)) ?_
              simp only [List.length_append, List.length_cons,
                List.length_nil]
              omega
  | .assign lhs rhs =>
      simp only [compileStmt] at hc
      cases hca : compileAssign L Γ lhs.expr rhs with
      | none => rw [hca] at hc; simp [bind, Option.bind] at hc
      | some c =>
          simp only [hca, bind, Option.bind, pure, Option.pure_def,
            Option.some.injEq, Prod.mk.injEq] at hc
          obtain ⟨hc1, hc2⟩ := hc
          subst hc1 hc2
          simp only [execW]
          exact compileAssign_sim L Γ lhs.expr rhs hca s hcode hrepr
  | .compoundAssign op lhs rhs =>
      simp only [compileStmt] at hc
      split at hc
      case _ hop =>
        cases hca : compileAssign L Γ lhs.expr (.mkBinop op lhs.expr rhs)
          with
        | none => rw [hca] at hc; simp [bind, Option.bind] at hc
        | some c =>
            simp only [hca, bind, Option.bind, pure, Option.pure_def,
              Option.some.injEq, Prod.mk.injEq] at hc
            obtain ⟨hc1, hc2⟩ := hc
            subst hc1 hc2
            rcases execW_compound_eq L Γ hop hca s with heq | heq
            · rw [heq]
              exact compileAssign_sim L Γ lhs.expr
                (.mkBinop op lhs.expr rhs) hca s hcode hrepr
            · rw [heq]
              exact ExecClaim_stuck
      case _ => exact Option.noConfusion hc
  | .stackDecl ty name init =>
      simp only [compileStmt] at hc
      split at hc
      case _ hcond =>
        have hprim : ty.isPrimitive = true := hcond.1
        have hnotL : name ∉ L := by
          intro hmem
          exact hcond.2 (by simpa using hmem)
        cases hfi : Γ.findIdx? (· = name) with
        | some i =>
            simp only [hfi] at hc
            split at hc
            case _ hdepth =>
              have hΓi := findIdx?_eq_name hfi
              obtain ⟨v', wi, henv', hσi, hrvi⟩ :=
                hrepr.locals i name hΓi
              cases hinit : init with
              | none =>
                  simp only [hinit, bind, Option.bind, pure,
                    Option.pure_def, Option.some.injEq,
                    Prod.mk.injEq] at hc
                  obtain ⟨hc1, hc2⟩ := hc
                  subst hc1 hc2
                  simp only [execW, hprim, if_true]
                  have hcodew := hcode.append_right
                  have hpush := hcode.append_left
                  cases ty
                  case ref r => simp [Ty.isPrimitive] at hprim
                  case prim p =>
                    cases p
                    all_goals (
                      simp only [ExecClaim_ok]
                      refine ⟨σ.set i 0, st, ?_, ?_⟩
                      · refine Steps.head (Step.push hpush.fetch) ?_
                        refine Steps.cast_pc
                          (writeLocal_steps hcodew hσi) ?_
                        simp only [List.length_append, List.length_cons,
                          List.length_nil]
                        all_goals omega
                      · first
                        | exact hrepr.setLocal hΓi
                            (by simp [ReprVal, wBool])
                        | exact hrepr.setLocal hΓi (by simp [ReprVal]))
              | some rhs =>
                  cases hcr : compileExpr L Γ 0 rhs with
                  | none =>
                      simp [hinit, hcr, bind, Option.bind] at hc
                  | some cr =>
                      simp only [hinit, hcr, bind, Option.bind, pure,
                        Option.pure_def, Option.some.injEq,
                        Prod.mk.injEq] at hc
                      obtain ⟨hc1, hc2⟩ := hc
                      subst hc1 hc2
                      have ihr := compileExpr_sim L Γ 0 rhs hcr s
                        (σt := []) (hcode.append_left) rfl hrepr
                      simp only [List.nil_append] at ihr
                      simp only [execW, hprim, if_true]
                      cases hv : evalW s rhs with
                      | error err =>
                          cases err
                          · rw [hv] at ihr
                            simp only [EvalClaim_revert] at ihr
                            simp only [hv, bind, Except.bind,
                              ExecClaim_revert]
                            exact ihr
                          · simp only [hv, bind, Except.bind]
                            exact ExecClaim_stuck
                      | ok v =>
                          rw [hv] at ihr
                          simp only [EvalClaim_ok] at ihr
                          obtain ⟨w, hw, hsteps⟩ := ihr
                          simp only [hv, bind, Except.bind, ExecClaim_ok]
                          refine ⟨σ.set i w, st, ?_, ?_⟩
                          · refine Steps.trans hsteps ?_
                            refine Steps.cast_pc
                              (writeLocal_steps (hcode.append_right)
                                hσi) ?_
                            simp only [List.length_append,
                              List.length_cons, List.length_nil]
                            omega
                          · exact hrepr.setLocal hΓi hw
            case _ => exact Option.noConfusion hc
        | none =>
            simp only [hfi] at hc
            have hnew : name ∉ Γ := findIdx?_none_not_mem hfi
            cases hinit : init with
            | none =>
                simp only [hinit, bind, Option.bind, pure,
                  Option.pure_def, Option.some.injEq,
                  Prod.mk.injEq] at hc
                obtain ⟨hc1, hc2⟩ := hc
                subst hc1 hc2
                simp only [execW, hprim, if_true]
                cases ty
                case ref r => simp [Ty.isPrimitive] at hprim
                case prim p =>
                  cases p
                  all_goals (
                    simp only [ExecClaim_ok]
                    refine ⟨0 :: σ, st, ?_, ?_⟩
                    · refine Steps.cast_pc
                        (Steps.single (Step.push hcode.fetch)) ?_
                      simp
                    · first
                      | exact hrepr.pushLocal hnew hnotL
                          (by simp [ReprVal, wBool])
                      | exact hrepr.pushLocal hnew hnotL
                          (by simp [ReprVal]))
            | some rhs =>
                cases hcr : compileExpr L Γ 0 rhs with
                | none =>
                    simp [hinit, hcr, bind, Option.bind] at hc
                | some cr =>
                    simp only [hinit, hcr, bind, Option.bind, pure,
                      Option.pure_def, Option.some.injEq,
                      Prod.mk.injEq] at hc
                    obtain ⟨hc1, hc2⟩ := hc
                    subst hc1 hc2
                    have ihr := compileExpr_sim L Γ 0 rhs hcr s
                      (σt := []) hcode rfl hrepr
                    simp only [List.nil_append] at ihr
                    simp only [execW, hprim, if_true]
                    cases hv : evalW s rhs with
                    | error err =>
                        cases err
                        · rw [hv] at ihr
                          simp only [EvalClaim_revert] at ihr
                          simp only [hv, bind, Except.bind,
                            ExecClaim_revert]
                          exact ihr
                        · simp only [hv, bind, Except.bind]
                          exact ExecClaim_stuck
                    | ok v =>
                        rw [hv] at ihr
                        simp only [EvalClaim_ok] at ihr
                        obtain ⟨w, hw, hsteps⟩ := ihr
                        simp only [hv, bind, Except.bind, ExecClaim_ok]
                        exact ⟨w :: σ, st, hsteps,
                          hrepr.pushLocal hnew hnotL hw⟩
      case _ => exact Option.noConfusion hc
  | .ite cond thn els =>
      simp only [compileStmt] at hc
      cases hcc : compileExpr L Γ 0 cond with
      | none => rw [hcc] at hc; simp [bind, Option.bind] at hc
      | some cc =>
        simp only [hcc, bind, Option.bind] at hc
        cases hct : compileBlock L Γ thn with
        | none => rw [hct] at hc; simp [bind, Option.bind] at hc
        | some pt =>
          obtain ⟨ct, Γt⟩ := pt
          simp only [hct, bind, Option.bind] at hc
          cases hce : compileBlock L Γ els with
          | none => rw [hce] at hc; simp [bind, Option.bind] at hc
          | some pe =>
            obtain ⟨ce, Γe⟩ := pe
            simp only [hce, bind, Option.bind] at hc
            split at hc
            case _ hΓ =>
              obtain ⟨hΓt, hΓe⟩ := hΓ
              rw [hΓt] at hct
              rw [hΓe] at hce
              simp only [pure, Option.pure_def, Option.some.injEq,
                Prod.mk.injEq] at hc
              obtain ⟨hc1, hc2⟩ := hc
              subst hc1 hc2
              have hcodecc : codeAt C base cc :=
                (((hcode.append_left).append_left).append_left).append_left
              have hcodemid :
                  codeAt C (base + cc.length)
                    [Instr.iszero, Instr.jumpi (ct.length + 1)] :=
                (((hcode.append_left).append_left).append_left).append_right
              have hcodect : codeAt C (base + cc.length + 2) ct :=
                codeAt_cast
                  (((hcode.append_left).append_left).append_right)
                  (by simp only [List.length_append, List.length_cons,
                    List.length_nil]; omega)
              have hcodejmp :
                  codeAt C (base + cc.length + 2 + ct.length)
                    [Instr.jump ce.length] :=
                codeAt_cast ((hcode.append_left).append_right)
                  (by simp only [List.length_append, List.length_cons,
                    List.length_nil]; omega)
              have hcodece :
                  codeAt C (base + cc.length + 2 + ct.length + 1) ce :=
                codeAt_cast (hcode.append_right)
                  (by simp only [List.length_append, List.length_cons,
                    List.length_nil]; omega)
              have ihc := compileExpr_sim L Γ 0 cond hcc s (σt := [])
                hcodecc rfl hrepr
              simp only [List.nil_append] at ihc
              simp only [execW]
              cases hv : evalW s cond with
              | error err =>
                  cases err
                  · rw [hv] at ihc
                    simp only [EvalClaim_revert] at ihc
                    simp only [hv, bind, Except.bind, ExecClaim_revert]
                    exact ihc
                  · simp only [hv, bind, Except.bind]
                    exact ExecClaim_stuck
              | ok cv =>
                  rw [hv] at ihc
                  simp only [EvalClaim_ok] at ihc
                  obtain ⟨wc, hwc, hstepsc⟩ := ihc
                  simp only [hv, bind, Except.bind]
                  cases cv with
                  | int n => exact ExecClaim_stuck
                  | bool b =>
                      simp only [ReprVal] at hwc
                      subst hwc
                      cases b with
                      | true =>
                          have iht := compileBlock_sim L Γ thn hct s
                            hcodect hrepr
                          have hentry : Steps C ⟨base, σ, st⟩
                              ⟨base + cc.length + 2, σ, st⟩ := by
                            refine Steps.trans hstepsc ?_
                            refine Steps.head
                              (Step.iszero hcodemid.fetch) ?_
                            refine Steps.cast_pc (Steps.single
                              (Step.jumpiFalse (hcodemid.tail).fetch))
                              (by omega)
                          cases hb : execWBlock s thn with
                          | error err =>
                              cases err
                              · rw [hb] at iht
                                simp only [ExecClaim_revert] at iht
                                simp only [hb, ExecClaim_revert]
                                exact Reverting.of_steps hentry iht
                              · exact ExecClaim_stuck
                          | ok s' =>
                              rw [hb] at iht
                              simp only [ExecClaim_ok] at iht
                              obtain ⟨σ', st', hsteps', hrepr'⟩ := iht
                              simp only [hb, ExecClaim_ok]
                              refine ⟨σ', st', ?_, hrepr'⟩
                              refine Steps.trans hentry ?_
                              refine Steps.trans hsteps' ?_
                              refine Steps.cast_pc (Steps.single
                                (Step.jump hcodejmp.fetch)) ?_
                              simp only [List.length_append,
                                List.length_cons, List.length_nil]
                              omega
                      | false =>
                          have ihe := compileBlock_sim L Γ els hce s
                            hcodece hrepr
                          have hentry : Steps C ⟨base, σ, st⟩
                              ⟨base + cc.length + 2 + ct.length + 1,
                                σ, st⟩ := by
                            refine Steps.trans hstepsc ?_
                            refine Steps.head
                              (Step.iszero hcodemid.fetch) ?_
                            refine Steps.cast_pc (Steps.single
                              (Step.jumpiTrue (hcodemid.tail).fetch
                                (by simp [wBool, one_ne_zero_word])))
                              (by omega)
                          cases hb : execWBlock s els with
                          | error err =>
                              cases err
                              · rw [hb] at ihe
                                simp only [ExecClaim_revert] at ihe
                                simp only [hb, ExecClaim_revert]
                                exact Reverting.of_steps hentry ihe
                              · exact ExecClaim_stuck
                          | ok s' =>
                              rw [hb] at ihe
                              simp only [ExecClaim_ok] at ihe
                              obtain ⟨σ', st', hsteps', hrepr'⟩ := ihe
                              simp only [hb, ExecClaim_ok]
                              refine ⟨σ', st', ?_, hrepr'⟩
                              refine Steps.trans hentry ?_
                              refine Steps.cast_pc hsteps' ?_
                              simp only [List.length_append,
                                List.length_cons, List.length_nil]
                              omega
            case _ => exact Option.noConfusion hc
  | .requireStmt cond =>
      simp only [compileStmt] at hc
      cases hcc : compileExpr L Γ 0 cond with
      | none => rw [hcc] at hc; simp [bind, Option.bind] at hc
      | some cc =>
          simp only [hcc, bind, Option.bind, pure, Option.pure_def,
            Option.some.injEq, Prod.mk.injEq] at hc
          obtain ⟨hc1, hc2⟩ := hc
          subst hc1 hc2
          have ihc := compileExpr_sim L Γ 0 cond hcc s (σt := [])
            (hcode.append_left) rfl hrepr
          simp only [List.nil_append] at ihc
          have hcodeg := hcode.append_right
          simp only [execW]
          cases hv : evalW s cond with
          | error err =>
              cases err
              · rw [hv] at ihc
                simp only [EvalClaim_revert] at ihc
                simp only [hv, bind, Except.bind, ExecClaim_revert]
                exact ihc
              · simp only [hv, bind, Except.bind]
                exact ExecClaim_stuck
          | ok cv =>
              rw [hv] at ihc
              simp only [EvalClaim_ok] at ihc
              obtain ⟨wc, hwc, hstepsc⟩ := ihc
              simp only [hv, bind, Except.bind]
              cases cv with
              | int n => exact ExecClaim_stuck
              | bool b =>
                  simp only [ReprVal] at hwc
                  subst hwc
                  cases b with
                  | true =>
                      simp only [ExecClaim_ok]
                      refine ⟨σ, st, ?_, hrepr⟩
                      refine Steps.trans hstepsc ?_
                      refine Steps.cast_pc (Steps.single
                        (Step.jumpiTrue hcodeg.fetch
                          (by simp [wBool, one_ne_zero_word]))) ?_
                      simp only [List.length_append, List.length_cons,
                        List.length_nil]
                      omega
                  | false =>
                      simp only [ExecClaim_revert]
                      refine ⟨⟨base + cc.length + 1, σ, st⟩, ?_, ?_⟩
                      · refine Steps.trans hstepsc ?_
                        exact Steps.single (Step.jumpiFalse hcodeg.fetch)
                      · exact (hcodeg.tail).fetch
  | .assertStmt cond =>
      simp only [compileStmt] at hc
      cases hcc : compileExpr L Γ 0 cond with
      | none => rw [hcc] at hc; simp [bind, Option.bind] at hc
      | some cc =>
          simp only [hcc, bind, Option.bind, pure, Option.pure_def,
            Option.some.injEq, Prod.mk.injEq] at hc
          obtain ⟨hc1, hc2⟩ := hc
          subst hc1 hc2
          have ihc := compileExpr_sim L Γ 0 cond hcc s (σt := [])
            (hcode.append_left) rfl hrepr
          simp only [List.nil_append] at ihc
          have hcodeg := hcode.append_right
          simp only [execW]
          cases hv : evalW s cond with
          | error err =>
              cases err
              · rw [hv] at ihc
                simp only [EvalClaim_revert] at ihc
                simp only [hv, bind, Except.bind, ExecClaim_revert]
                exact ihc
              · simp only [hv, bind, Except.bind]
                exact ExecClaim_stuck
          | ok cv =>
              rw [hv] at ihc
              simp only [EvalClaim_ok] at ihc
              obtain ⟨wc, hwc, hstepsc⟩ := ihc
              simp only [hv, bind, Except.bind]
              cases cv with
              | int n => exact ExecClaim_stuck
              | bool b =>
                  simp only [ReprVal] at hwc
                  subst hwc
                  cases b with
                  | true =>
                      simp only [ExecClaim_ok]
                      refine ⟨σ, st, ?_, hrepr⟩
                      refine Steps.trans hstepsc ?_
                      refine Steps.cast_pc (Steps.single
                        (Step.jumpiTrue hcodeg.fetch
                          (by simp [wBool, one_ne_zero_word]))) ?_
                      simp only [List.length_append, List.length_cons,
                        List.length_nil]
                      omega
                  | false =>
                      simp only [ExecClaim_revert]
                      refine ⟨⟨base + cc.length + 1, σ, st⟩, ?_, ?_⟩
                      · refine Steps.trans hstepsc ?_
                        exact Steps.single (Step.jumpiFalse hcodeg.fetch)
                      · exact (hcodeg.tail).fetch
  | .revert msg =>
      simp only [compileStmt, pure, Option.pure_def, Option.some.injEq,
        Prod.mk.injEq] at hc
      obtain ⟨hc1, hc2⟩ := hc
      subst hc1 hc2
      simp only [execW, ExecClaim_revert]
      exact ⟨⟨base, σ, st⟩, Steps.refl _, hcode.fetch⟩
  | .storageDecl ty name init => simp [compileStmt] at hc
  | .storagePlaceAlias ty name init => simp [compileStmt] at hc
  | .memoryDecl ty name init => simp [compileStmt] at hc
  | .delete target => simp [compileStmt] at hc
  | .push target value =>
      obtain ⟨texpr, hassign⟩ := target
      match texpr with
      | .field .. => simp [compileStmt] at hc
      | .index .. => simp [compileStmt] at hc
      | .pushPlace .. => simp [compileStmt] at hc
      | .bool .. => simp [compileStmt] at hc
      | .intLit .. => simp [compileStmt] at hc
      | .mkCall .. => simp [compileStmt] at hc
      | .mkBinop .. => simp [compileStmt] at hc
      | .mkUnop .. => simp [compileStmt] at hc
      | .mkIncDec .. => simp [compileStmt] at hc
      | .mkTernary .. => simp [compileStmt] at hc
      | .var kind tyA fld =>
        cases kind with
        | stack => simp [compileStmt] at hc
        | memory => simp [compileStmt] at hc
        | storage =>
          match tyA with
          | Ty.bool => simp [compileStmt] at hc
          | Ty.uint => simp [compileStmt] at hc
          | Ty.int => simp [compileStmt] at hc
          | Ty.ref (RefTy.struct nm) => simp [compileStmt] at hc
          | Ty.ref (RefTy.mapping kt vt) => simp [compileStmt] at hc
          | Ty.ref (RefTy.array elemTy) =>
            simp only [compileStmt] at hc
            split at hc
            case _ hcond =>
              cases hslot : slotOf? L fld.name with
              | none => rw [hslot] at hc; exact Option.noConfusion hc
              | some i =>
                simp only [hslot] at hc
                have hLidx : L[i]? = some fld.name :=
                  findIdx?_eq_name (by simpa [slotOf?] using hslot)
                have hmem : fld.name ∈ L := List.mem_of_getElem? hLidx
                have henv : lookupBy fld.name s.env = none :=
                  hrepr.rootsEnv _ hmem
                obtain ⟨sv₀, hst, hroot⟩ :=
                  hrepr.roots i fld.name hLidx
                cases value with
                | none =>
                  simp only [bind, Option.bind, pure, Option.pure_def,
                    Option.some.injEq, Prod.mk.injEq] at hc
                  obtain ⟨hc1, hc2⟩ := hc
                  subst hc1 hc2
                  simp only [execW, henv, if_pos hcond]
                  cases sv₀ with
                  | prim p => cases p <;> (rw [hst]; exact ExecClaim_stuck)
                  | struct fields => rw [hst]; exact ExecClaim_stuck
                  | map entries dflt => rw [hst]; exact ExecClaim_stuck
                  | array elems =>
                    simp only [hst]
                    have hroot' := hroot
                    simp only [ReprRoot] at hroot'
                    obtain ⟨hlen, hlslot, helems⟩ := hroot'
                    by_cases hlen1 : elems.length + 1 ≤ keyBound
                    case neg =>
                      simp only [bind, Except.bind, if_neg hlen1]
                      exact ExecClaim_stuck
                    case pos =>
                    simp only [bind, Except.bind, if_pos hlen1,
                      ExecClaim_ok]
                    have hcodehead : codeAt C base
                        [Instr.push (slotWord i), Instr.sload,
                         Instr.push 0] :=
                      hcode.append_left
                    have hcodetail : codeAt C (base + 1 + 1 + 1)
                        [Instr.dup 2, Instr.push (slotWord i),
                         Instr.mapslot, Instr.sstore, Instr.push 1,
                         Instr.add, Instr.push (slotWord i),
                         Instr.sstore] :=
                      codeAt_cast
                        (show codeAt C
                            (base + [Instr.push (slotWord i),
                              Instr.sload, Instr.push 0].length) _ from
                          hcode.append_right)
                        (by first
                            | omega
                            | (simp only [List.length_append,
                                List.length_cons,
                                List.length_nil] <;> omega))
                    refine ⟨σ,
                      (st.write (mapSlotW (slotWord i)
                          (BitVec.ofNat 256 elems.length)) 0).write
                        (slotWord i)
                        (1 + BitVec.ofNat 256 elems.length),
                      ?_, ?_⟩
                    · refine Steps.head
                        (Step.push hcodehead.fetch) ?_
                      refine Steps.head
                        (Step.sload (hcodehead.tail).fetch) ?_
                      rw [hlslot]
                      refine Steps.head
                        (Step.push
                          ((hcodehead.tail).tail).fetch) ?_
                      refine Steps.cast_pc
                        (pushTail_steps hcodetail) ?_
                      first
                      | omega
                      | (simp only [List.length_append,
                          List.length_cons,
                          List.length_nil] <;> omega)
                    · exact hrepr.pushArray hLidx hst hlen1
                        (reprSVal_default hcond.2)
                | some rhs =>
                  by_cases hprim : rhs.ty.isPrimitive = true
                  case neg =>
                    simp only [if_neg hprim] at hc
                    simp [bind, Option.bind] at hc
                  case pos =>
                  simp only [if_pos hprim] at hc
                  cases hcv : compileExpr L Γ 1 rhs with
                  | none =>
                      rw [hcv] at hc; simp [bind, Option.bind] at hc
                  | some cv =>
                    simp only [hcv, bind, Option.bind, pure,
                      Option.pure_def, Option.some.injEq,
                      Prod.mk.injEq] at hc
                    obtain ⟨hc1, hc2⟩ := hc
                    subst hc1 hc2
                    simp only [execW, henv, if_pos hcond]
                    cases sv₀ with
                    | prim p => cases p <;> (rw [hst]; exact ExecClaim_stuck)
                    | struct fields => rw [hst]; exact ExecClaim_stuck
                    | map entries dflt =>
                        rw [hst]; exact ExecClaim_stuck
                    | array elems =>
                      simp only [hst]
                      have hroot' := hroot
                      simp only [ReprRoot] at hroot'
                      obtain ⟨hlen, hlslot, helems⟩ := hroot'
                      have hcodehead : codeAt C base
                          [Instr.push (slotWord i), Instr.sload] :=
                        (hcode.append_left).append_left
                      have hcodecv : codeAt C (base + 1 + 1) cv :=
                        codeAt_cast
                          ((hcode.append_left).append_right)
                          (by first
                              | omega
                              | (simp only [List.length_append,
                                  List.length_cons,
                                  List.length_nil] <;> omega))
                      have hcodetail : codeAt C
                          (base + 1 + 1 + cv.length)
                          [Instr.dup 2, Instr.push (slotWord i),
                           Instr.mapslot, Instr.sstore, Instr.push 1,
                           Instr.add, Instr.push (slotWord i),
                           Instr.sstore] :=
                        codeAt_cast (hcode.append_right)
                          (by first
                              | omega
                              | (simp only [List.length_append,
                                  List.length_cons,
                                  List.length_nil] <;> omega))
                      have ihv := compileExpr_sim L Γ 1 rhs hcv s
                        (σt := [BitVec.ofNat 256 elems.length])
                        hcodecv rfl hrepr
                      simp only [List.cons_append, List.nil_append]
                        at ihv
                      simp only [hprim, if_true]
                      cases hr : evalW s rhs with
                      | error err =>
                          cases err
                          · rw [hr] at ihv
                            simp only [EvalClaim_revert] at ihv
                            simp only [hr, bind, Except.bind,
                              ExecClaim_revert]
                            refine Reverting.of_steps ?_ ihv
                            refine Steps.head
                              (Step.push hcodehead.fetch) ?_
                            rw [← hlslot]
                            exact Steps.single
                              (Step.sload (hcodehead.tail).fetch)
                          · simp only [hr, bind, Except.bind]
                            exact ExecClaim_stuck
                      | ok v =>
                        rw [hr] at ihv
                        simp only [EvalClaim_ok] at ihv
                        obtain ⟨w, hw, hstepsv⟩ := ihv
                        by_cases hlen1 : elems.length + 1 ≤ keyBound
                        case neg =>
                          simp only [hr, bind, Except.bind,
                            if_neg hlen1]
                          exact ExecClaim_stuck
                        case pos =>
                        simp only [hr, bind, Except.bind,
                          if_pos hlen1, ExecClaim_ok]
                        refine ⟨σ,
                          (st.write (mapSlotW (slotWord i)
                              (BitVec.ofNat 256 elems.length))
                            w).write (slotWord i)
                            (1 + BitVec.ofNat 256 elems.length),
                          ?_, ?_⟩
                        · refine Steps.head
                            (Step.push hcodehead.fetch) ?_
                          refine Steps.head
                            (Step.sload (hcodehead.tail).fetch) ?_
                          rw [hlslot]
                          refine Steps.trans hstepsv ?_
                          refine Steps.cast_pc
                            (pushTail_steps hcodetail) ?_
                          first
                          | omega
                          | (simp only [List.length_append,
                              List.length_cons,
                              List.length_nil] <;> omega)
                        · exact hrepr.pushArray hLidx hst hlen1
                            hw.toSVal
            case _ => exact Option.noConfusion hc
  | .pushAssign target value => simp [compileStmt] at hc
  | .pushFieldAssign target fld value => simp [compileStmt] at hc
  | .pop target =>
      obtain ⟨texpr, hassign⟩ := target
      match texpr with
      | .field .. => simp [compileStmt] at hc
      | .index .. => simp [compileStmt] at hc
      | .pushPlace .. => simp [compileStmt] at hc
      | .bool .. => simp [compileStmt] at hc
      | .intLit .. => simp [compileStmt] at hc
      | .mkCall .. => simp [compileStmt] at hc
      | .mkBinop .. => simp [compileStmt] at hc
      | .mkUnop .. => simp [compileStmt] at hc
      | .mkIncDec .. => simp [compileStmt] at hc
      | .mkTernary .. => simp [compileStmt] at hc
      | .var kind tyA fld =>
        cases kind with
        | stack => simp [compileStmt] at hc
        | memory => simp [compileStmt] at hc
        | storage =>
          match tyA with
          | Ty.bool => simp [compileStmt] at hc
          | Ty.uint => simp [compileStmt] at hc
          | Ty.int => simp [compileStmt] at hc
          | Ty.ref (RefTy.struct nm) => simp [compileStmt] at hc
          | Ty.ref (RefTy.mapping kt vt) => simp [compileStmt] at hc
          | Ty.ref (RefTy.array elemTy) =>
            simp only [compileStmt] at hc
            split at hc
            case _ horig =>
              cases hslot : slotOf? L fld.name with
              | none => rw [hslot] at hc; exact Option.noConfusion hc
              | some i =>
                simp only [hslot, pure, Option.pure_def,
                  Option.some.injEq, Prod.mk.injEq] at hc
                obtain ⟨hc1, hc2⟩ := hc
                subst hc1 hc2
                have hLidx : L[i]? = some fld.name :=
                  findIdx?_eq_name (by simpa [slotOf?] using hslot)
                have hmem : fld.name ∈ L := List.mem_of_getElem? hLidx
                have henv : lookupBy fld.name s.env = none :=
                  hrepr.rootsEnv _ hmem
                obtain ⟨sv₀, hst, hroot⟩ :=
                  hrepr.roots i fld.name hLidx
                simp only [execW, henv, if_pos horig]
                cases sv₀ with
                | prim p => cases p <;> (rw [hst]; exact ExecClaim_stuck)
                | struct fields => rw [hst]; exact ExecClaim_stuck
                | map entries dflt => rw [hst]; exact ExecClaim_stuck
                | array elems =>
                  simp only [hst]
                  have hroot' := hroot
                  simp only [ReprRoot] at hroot'
                  obtain ⟨hlen, hlslot, helems⟩ := hroot'
                  have hf0 := hcode.fetch
                  have hf1 := (hcode.tail).fetch
                  have hf2 := ((hcode.tail).tail).fetch
                  have hf3 := (((hcode.tail).tail).tail).fetch
                  have hf4 := ((((hcode.tail).tail).tail).tail).fetch
                  have hf5 :=
                    (((((hcode.tail).tail).tail).tail).tail).fetch
                  have hf6 :=
                    ((((((hcode.tail).tail).tail).tail).tail).tail).fetch
                  have hf7 :=
                    (((((((hcode.tail).tail).tail).tail).tail).tail).tail).fetch
                  have hf8 :=
                    ((((((((hcode.tail).tail).tail).tail).tail).tail).tail).tail).fetch
                  have hf9 :=
                    (((((((((hcode.tail).tail).tail).tail).tail).tail).tail).tail).tail).fetch
                  cases hrev : elems.reverse with
                  | nil =>
                    have hlen0 : elems.length = 0 := by
                      have := congrArg List.length hrev
                      simpa using this
                    have hz : BitVec.ofNat 256 elems.length = 0 := by
                      rw [hlen0]; rfl
                    simp only [hrev, ExecClaim_revert]
                    refine ⟨⟨base + 1 + 1 + 1 + 1, (0 : Word) :: σ,
                      st⟩, ?_, ?_⟩
                    · refine Steps.head (Step.push hf0) ?_
                      refine Steps.head (Step.sload hf1) ?_
                      rw [hlslot, hz]
                      refine Steps.head (Step.dup hf2 rfl) ?_
                      exact Steps.single (Step.jumpiFalse hf3)
                    · exact hf4
                  | cons x restRev =>
                    have hne0 : elems.length ≠ 0 := by
                      intro h0
                      rw [List.length_eq_zero_iff] at h0
                      rw [h0] at hrev
                      simp at hrev
                    have hnz : BitVec.ofNat 256 elems.length
                        ≠ (0 : Word) := by
                      intro h0
                      have := congrArg BitVec.toNat h0
                      rw [BitVec.toNat_ofNat] at this
                      simp only [keyBound] at hlen
                      have h00 : (0 : Word).toNat = 0 := rfl
                      rw [h00] at this
                      omega
                    simp only [hrev, ExecClaim_ok]
                    refine ⟨σ,
                      st.write (slotWord i)
                        (BitVec.ofNat 256 elems.length - 1), ?_, ?_⟩
                    · refine Steps.head (Step.push hf0) ?_
                      refine Steps.head (Step.sload hf1) ?_
                      rw [hlslot]
                      refine Steps.head (Step.dup hf2 rfl) ?_
                      refine Steps.head
                        (Step.jumpiTrue hf3 hnz) ?_
                      refine Steps.head (Step.push hf5) ?_
                      refine Steps.head (Step.swap hf6 rfl rfl) ?_
                      refine Steps.head (Step.sub hf7) ?_
                      refine Steps.head (Step.push hf8) ?_
                      refine Steps.cast_pc
                        (Steps.single (Step.sstore hf9)) ?_
                      first
                      | omega
                      | (simp only [List.length_append,
                          List.length_cons,
                          List.length_nil] <;> omega)
                    · exact hrepr.popArray hLidx hst hrev
            case _ => exact Option.noConfusion hc
  | .transfer recipient amount =>
      simp only [compileStmt] at hc
      cases hca : compileExpr L Γ 0 recipient with
      | none => rw [hca] at hc; simp [bind, Option.bind] at hc
      | some ca =>
        simp only [hca, bind, Option.bind] at hc
        cases hcm : compileExpr L Γ 1 amount with
        | none => rw [hcm] at hc; simp [bind, Option.bind] at hc
        | some cm =>
          simp only [hcm, bind, Option.bind, pure, Option.pure_def,
            Option.some.injEq, Prod.mk.injEq] at hc
          obtain ⟨hc1, hc2⟩ := hc
          subst hc1 hc2
          have iha := compileExpr_sim L Γ 0 recipient hca s
            (σt := []) (((hcode.append_left).append_left).append_left)
            rfl hrepr
          simp only [List.nil_append] at iha
          have hcodepa : codeAt C (base + ca.length)
              [Instr.push netBase, Instr.add] :=
            ((hcode.append_left).append_left).append_right
          have hcodecm : codeAt C (base + ca.length + 1 + 1) cm :=
            codeAt_cast ((hcode.append_left).append_right)
              (by first
                  | omega
                  | (simp only [List.length_append, List.length_cons,
                      List.length_nil] <;> omega))
          have hcodet : codeAt C (base + ca.length + 1 + 1 + cm.length)
              transferTail :=
            codeAt_cast (hcode.append_right)
              (by first
                  | omega
                  | (simp only [List.length_append, List.length_cons,
                      List.length_nil] <;> omega))
          simp only [execW]
          cases hr : evalW s recipient with
          | error err =>
              cases err
              · rw [hr] at iha
                simp only [EvalClaim_revert] at iha
                simp only [hr, bind, Except.bind, ExecClaim_revert]
                exact iha
              · simp only [hr, bind, Except.bind]
                exact ExecClaim_stuck
          | ok av =>
            rw [hr] at iha
            simp only [EvalClaim_ok] at iha
            obtain ⟨aw, hawv, hstepsa⟩ := iha
            simp only [hr, bind, Except.bind]
            cases av with
            | bool b => exact ExecClaim_stuck
            | int a =>
              simp only [ReprVal] at hawv
              by_cases habc : 0 ≤ a ∧ a < keyBoundI
              case neg =>
                  simp only [if_neg habc]
                  exact ExecClaim_stuck
              case pos =>
              simp only [if_pos habc]
              have ihm := compileExpr_sim L Γ 1 amount hcm s
                (σt := [netBase + aw]) hcodecm rfl hrepr
              simp only [List.cons_append, List.nil_append] at ihm
              cases hm : evalW s amount with
              | error err =>
                  cases err
                  · rw [hm] at ihm
                    simp only [EvalClaim_revert] at ihm
                    simp only [hm, bind, Except.bind, ExecClaim_revert]
                    refine Reverting.of_steps ?_ ihm
                    refine Steps.trans hstepsa ?_
                    refine Steps.head (Step.push hcodepa.fetch) ?_
                    exact Steps.single (Step.add (hcodepa.tail).fetch)
                  · simp only [hm, bind, Except.bind]
                    exact ExecClaim_stuck
              | ok mv =>
                rw [hm] at ihm
                simp only [EvalClaim_ok] at ihm
                obtain ⟨amtw, hamtv, hstepsm⟩ := ihm
                simp only [hm, bind, Except.bind]
                cases mv with
                | bool b => exact ExecClaim_stuck
                | int amt =>
                  simp only [ReprVal] at hamtv
                  obtain ⟨hbal0, hbalw, hbalread⟩ := hrepr.balance
                  -- Run to just after the `ISZERO` of the balance guard:
                  -- the top word is `1` iff the balance covers `amt`.
                  have hpre : Steps C ⟨base, σ, st⟩
                      ⟨base + ca.length + 1 + 1 + cm.length + 6,
                       wBool (!(BitVec.ult (st.read balanceSlotW) amtw)) ::
                         st.read balanceSlotW :: amtw :: (netBase + aw) ::
                         σ, st⟩ := by
                    refine Steps.trans hstepsa ?_
                    refine Steps.head (Step.push hcodepa.fetch) ?_
                    refine Steps.head
                      (Step.add (hcodepa.tail).fetch) ?_
                    refine Steps.trans hstepsm ?_
                    refine Steps.head (Step.push hcodet.fetch) ?_
                    refine Steps.head
                      (Step.sload (hcodet.tail).fetch) ?_
                    refine Steps.head
                      (Step.dup ((hcodet.tail).tail).fetch rfl) ?_
                    refine Steps.head
                      (Step.dup (((hcodet.tail).tail).tail).fetch rfl) ?_
                    refine Steps.head
                      (Step.lt ((((hcodet.tail).tail).tail).tail).fetch) ?_
                    have hz := Step.iszero
                      (a := wBool (BitVec.ult (st.read balanceSlotW) amtw))
                      (σ := st.read balanceSlotW :: amtw :: (netBase + aw) :: σ)
                      (st := st)
                      (((((hcodet.tail).tail).tail).tail).tail).fetch
                    rw [iszero_wBool] at hz
                    refine Steps.cast_pc (Steps.single hz) ?_
                    first
                    | omega
                    | (simp only [List.length_append, List.length_cons,
                        List.length_nil] <;> omega)
                  have hbalnat : (st.read balanceSlotW).toNat =
                      s.selfBalance.toNat := by
                    rw [hbalread, BitVec.toNat_ofNat]
                    apply Nat.mod_eq_of_lt
                    simp only [wordSizeI] at hbalw
                    omega
                  by_cases hneg : amt < 0
                  case pos =>
                      simp only [if_pos hneg]
                      exact ExecClaim_stuck
                  case neg =>
                  simp only [if_neg hneg]
                  by_cases hbal : s.selfBalance < amt
                  case pos =>
                      -- insufficient balance: the guard falls into `REVERT`
                      simp only [if_pos hbal, ExecClaim_revert]
                      have hlt : BitVec.ult (st.read balanceSlotW) amtw = true := by
                        simp only [BitVec.ult, decide_eq_true_eq, hbalnat]
                        omega
                      rw [hlt, Bool.not_true, wBool_false] at hpre
                      refine ⟨⟨base + ca.length + 1 + 1 + cm.length + 6 + 1,
                        st.read balanceSlotW :: amtw :: (netBase + aw) :: σ,
                        st⟩, ?_, ?_⟩
                      · refine Steps.trans hpre ?_
                        exact Steps.single (Step.jumpiFalse
                          ((((((hcodet.tail).tail).tail).tail).tail).tail).fetch)
                      · exact
                          (((((((hcodet.tail).tail).tail).tail).tail).tail).tail).fetch
                  case neg =>
                  simp only [if_neg hbal]
                  by_cases hled : 0 ≤ s.getNet a - amt
                  case neg =>
                      simp only [if_neg hled]
                      exact ExecClaim_stuck
                  case pos =>
                  simp only [if_pos hled]
                  simp only [ExecClaim_ok]
                  have hge : BitVec.ult (st.read balanceSlotW) amtw = false := by
                    simp only [BitVec.ult, decide_eq_false_iff_not, hbalnat]
                    omega
                  rw [hge, Bool.not_false, wBool_true] at hpre
                  refine ⟨σ, ((st.write balanceSlotW
                      (st.read balanceSlotW - amtw)).write (netBase + aw)
                    ((st.write balanceSlotW
                      (st.read balanceSlotW - amtw)).read (netBase + aw) - amtw)),
                    ?_, ?_⟩
                  · refine Steps.trans hpre ?_
                    have hc7 : codeAt C (base + ca.length + 1 + 1 + cm.length + 6 + 1 + 1)
                        [Instr.dup 2, Instr.swap 1, Instr.sub,
                         Instr.push balanceSlotW, Instr.sstore,
                         Instr.dup 2, Instr.sload, Instr.sub, Instr.swap 1,
                         Instr.sstore] :=
                      ((((((((hcodet.tail).tail).tail).tail).tail).tail).tail).tail)
                    refine Steps.head (Step.jumpiTrue
                      ((((((hcodet.tail).tail).tail).tail).tail).tail).fetch
                      one_ne_zero_word) ?_
                    refine Steps.head (Step.dup hc7.fetch rfl) ?_
                    refine Steps.head
                      (Step.swap (hc7.tail).fetch rfl rfl) ?_
                    refine Steps.head
                      (Step.sub ((hc7.tail).tail).fetch) ?_
                    refine Steps.head
                      (Step.push (((hc7.tail).tail).tail).fetch) ?_
                    refine Steps.head
                      (Step.sstore ((((hc7.tail).tail).tail).tail).fetch) ?_
                    refine Steps.head
                      (Step.dup (((((hc7.tail).tail).tail).tail).tail).fetch
                        rfl) ?_
                    refine Steps.head
                      (Step.sload
                        ((((((hc7.tail).tail).tail).tail).tail).tail).fetch) ?_
                    refine Steps.head
                      (Step.sub
                        (((((((hc7.tail).tail).tail).tail).tail).tail).tail).fetch)
                      ?_
                    refine Steps.head
                      (Step.swap
                        ((((((((hc7.tail).tail).tail).tail).tail).tail).tail).tail).fetch
                        rfl rfl) ?_
                    refine Steps.cast_pc (Steps.single (Step.sstore
                      (((((((((hc7.tail).tail).tail).tail).tail).tail).tail).tail).tail).fetch))
                      ?_
                    first
                    | omega
                    | (simp only [List.length_append, List.length_cons,
                        List.length_nil, transferTail] <;> omega)
                  · have hdeb := hrepr.debitBalance (by omega) (by omega) hamtv
                    have hnet := hdeb.setNet habc.1 habc.2 (by omega)
                      (show amt ≤ s.getNet a by omega) hawv hamtv
                    simpa only [netSlotW, State.setNet, State.getNet] using hnet
  | .callStmt result fn args => simp [compileStmt] at hc
termination_by sizeOf stmt

theorem compileBlock_sim (L Γ : List Name) (stmts : List Stmt)
    {code : Code} {Γ' : List Name}
    (hc : compileBlock L Γ stmts = some (code, Γ'))
    (s : State) {C : Code} {base : Nat} (hcode : codeAt C base code)
    {σ : List Word} {st : Store} (hrepr : ReprState L Γ s σ st) :
    ExecClaim C base code.length L Γ' σ st (execWBlock s stmts) := by
  match stmts with
  | [] =>
      simp only [compileBlock, pure, Option.pure_def, Option.some.injEq,
        Prod.mk.injEq] at hc
      obtain ⟨hc1, hc2⟩ := hc
      subst hc1 hc2
      simp only [execWBlock, ExecClaim_ok]
      exact ⟨σ, st, Steps.cast_pc (Steps.refl _) (by simp), hrepr⟩
  | stmt :: rest =>
      simp only [compileBlock] at hc
      cases hc1 : compileStmt L Γ stmt with
      | none => rw [hc1] at hc; simp [bind, Option.bind] at hc
      | some p1 =>
        obtain ⟨c1, Γ1⟩ := p1
        simp only [hc1, bind, Option.bind] at hc
        cases hc2 : compileBlock L Γ1 rest with
        | none => rw [hc2] at hc; simp [bind, Option.bind] at hc
        | some p2 =>
            obtain ⟨c2, Γ2⟩ := p2
            simp only [hc2, bind, Option.bind, pure, Option.pure_def,
              Option.some.injEq, Prod.mk.injEq] at hc
            obtain ⟨hca, hcb⟩ := hc
            subst hca hcb
            have ih1 := compileStmt_sim L Γ stmt hc1 s
              (hcode.append_left) hrepr
            simp only [execWBlock]
            cases hs1 : execW s stmt with
            | error err =>
                cases err
                · rw [hs1] at ih1
                  simp only [ExecClaim_revert] at ih1
                  simp only [hs1, bind, Except.bind, ExecClaim_revert]
                  exact ih1
                · simp only [hs1, bind, Except.bind]
                  exact ExecClaim_stuck
            | ok s1 =>
                rw [hs1] at ih1
                simp only [ExecClaim_ok] at ih1
                obtain ⟨σ1, st1, hsteps1, hrepr1⟩ := ih1
                have ih2 := compileBlock_sim L Γ1 rest hc2 s1
                  (hcode.append_right) hrepr1
                simp only [hs1, bind, Except.bind]
                cases hs2 : execWBlock s1 rest with
                | error err =>
                    cases err
                    · rw [hs2] at ih2
                      simp only [ExecClaim_revert] at ih2
                      simp only [hs2, ExecClaim_revert]
                      exact Reverting.of_steps hsteps1 ih2
                    · exact ExecClaim_stuck
                | ok s2 =>
                    rw [hs2] at ih2
                    simp only [ExecClaim_ok] at ih2
                    obtain ⟨σ2, st2, hsteps2, hrepr2⟩ := ih2
                    simp only [hs2, ExecClaim_ok]
                    refine ⟨σ2, st2, ?_, hrepr2⟩
                    refine Steps.trans hsteps1 ?_
                    refine Steps.cast_pc hsteps2 ?_
                    simp only [List.length_append]
                    omega
termination_by sizeOf stmts

end

/-! ## Top-level preservation theorems -/

theorem codeAt_self (C : Code) : codeAt C 0 C :=
  ⟨[], [], by simp, rfl⟩

/-- **Compilation preserves the semantics — successful executions.**

If a block compiles under storage layout `L` and its bounded (uint256)
execution from `s` succeeds with `s'`, then

1. the *official* interpreter (`Semantics.execBlock`) also computes
   `s'`, and
2. the EVM machine, running the compiled code from an empty stack and
   any storage representing `s`, halts at the end of the code with a
   stack and storage representing `s'`. -/
theorem compile_preserves_ok
    {L : List Name} {b : Block} {code : Code}
    (hc : compileProgram L b = some code)
    {s s' : State} (hexec : execWBlock s b = .ok s')
    {st : Store} (hrepr : ReprState L [] s [] st) :
    execBlock s b = .ok s' ∧
      ∃ Γ' σ' st',
        Steps code ⟨0, [], st⟩ ⟨code.length, σ', st'⟩ ∧
          ReprState L Γ' s' σ' st' := by
  constructor
  · have h := execWBlock_agree s b
    rw [hexec] at h
    simpa using (Agrees_ok.mp h)
  · simp only [compileProgram] at hc
    cases hcb : compileBlock L [] b with
    | none => rw [hcb] at hc; simp [bind, Option.bind] at hc
    | some p =>
        obtain ⟨c, Γ'⟩ := p
        simp only [hcb, bind, Option.bind, pure, Option.pure_def,
          Option.some.injEq] at hc
        subst hc
        have hclaim := compileBlock_sim L [] b hcb s (codeAt_self c) hrepr
        rw [hexec] at hclaim
        simp only [ExecClaim_ok] at hclaim
        obtain ⟨σ', st', hsteps, hrepr'⟩ := hclaim
        exact ⟨Γ', σ', st', by simpa using hsteps, hrepr'⟩

/-- **Compilation preserves the semantics — reverting executions.**

If a block compiles and its bounded execution reverts, the official
interpreter reverts, and the machine reaches a `REVERT` instruction. -/
theorem compile_preserves_revert
    {L : List Name} {b : Block} {code : Code}
    (hc : compileProgram L b = some code)
    {s : State} (hexec : execWBlock s b = .error .revert)
    {st : Store} (hrepr : ReprState L [] s [] st) :
    execBlock s b = .error .revert ∧
      Reverting code ⟨0, [], st⟩ := by
  constructor
  · have h := execWBlock_agree s b
    rw [hexec] at h
    exact Agrees_revert.mp h
  · simp only [compileProgram] at hc
    cases hcb : compileBlock L [] b with
    | none => rw [hcb] at hc; simp [bind, Option.bind] at hc
    | some p =>
        obtain ⟨c, Γ'⟩ := p
        simp only [hcb, bind, Option.bind, pure, Option.pure_def,
          Option.some.injEq] at hc
        subst hc
        have hclaim := compileBlock_sim L [] b hcb s (codeAt_self c) hrepr
        rw [hexec] at hclaim
        simpa using hclaim

/-- The final storage of a compiled run decodes each layout root: if
preservation put the machine in a configuration representing `s'`, then
reading slot `i` gives exactly the word representing root `L[i]`'s final
value in the interpreter state. (Unfolding of `ReprState.roots`, stated
for the calculus trail.) -/
theorem final_storage_decodes
    {L Γ' : List Name} {s' : State} {σ' : List Word} {st' : Store}
    (h : ReprState L Γ' s' σ' st') {i : Nat} {name : Name}
    (hidx : L[i]? = some name) :
    ∃ sv, lookupBy name s'.storage = some sv ∧ ReprRoot i sv st' :=
  h.roots i name hidx

/-! ## Uniqueness of the machine verdict

The preservation theorems exhibit one machine execution; determinism
(`Step.deterministic`, `Steps.unique_terminal`) makes it the only one.
Combined with the runner-soundness lemmas of `Evm/Machine.lean`, every
verdict of the executable runner is pinned down: on a successful
bounded execution the runner can only report the representing final
state, and it can never report success on a reverting one. -/

/-- On a successful execution, *any* `.ok` verdict of the runner (any
fuel) reports exactly a stack and storage representing the final
state — the machine cannot reach any other halted configuration. -/
theorem preserved_ok_run_unique
    {L : List Name} {b : Block} {code : Code}
    (hc : compileProgram L b = some code)
    {s s' : State} (hexec : execWBlock s b = .ok s')
    {st : Store} (hrepr : ReprState L [] s [] st)
    {fuel : Nat} {σr : List Word} {str : Store}
    (hrun : run code fuel ⟨0, [], st⟩ = .ok σr str) :
    ∃ Γ', ReprState L Γ' s' σr str := by
  obtain ⟨-, Γ', σ', st', hsteps, hrepr'⟩ :=
    compile_preserves_ok hc hexec hrepr
  obtain ⟨pc, hsteps₂, hhalt⟩ := run_ok_sound hrun
  have t₁ : Terminal code ⟨code.length, σ', st'⟩ :=
    terminal_of_end (Nat.le_refl _)
  have t₂ : Terminal code ⟨pc, σr, str⟩ := Terminal.of_halted hhalt
  have heq := Steps.unique_terminal hsteps hsteps₂ t₁ t₂
  simp only [Conf.mk.injEq] at heq
  obtain ⟨-, hσ, hst⟩ := heq
  exact ⟨Γ', hσ ▸ hst ▸ hrepr'⟩

/-- On a successful execution the runner can never report a revert. -/
theorem preserved_ok_not_reverted
    {L : List Name} {b : Block} {code : Code}
    (hc : compileProgram L b = some code)
    {s s' : State} (hexec : execWBlock s b = .ok s')
    {st : Store} (hrepr : ReprState L [] s [] st)
    {fuel : Nat} :
    run code fuel ⟨0, [], st⟩ ≠ .reverted := by
  intro hrun
  obtain ⟨-, Γ', σ', st', hsteps, -⟩ :=
    compile_preserves_ok hc hexec hrepr
  obtain ⟨crev, hsteps₂, hfetch⟩ := run_revert_sound hrun
  have t₁ : Terminal code ⟨code.length, σ', st'⟩ :=
    terminal_of_end (Nat.le_refl _)
  have t₂ : Terminal code crev := by
    obtain ⟨pc, σ0, st0⟩ := crev
    exact terminal_of_revert hfetch
  have heq := Steps.unique_terminal hsteps hsteps₂ t₁ t₂
  rw [← heq] at hfetch
  have hfetch' : code[code.length]? = some Instr.revert := hfetch
  rw [List.getElem?_eq_none (Nat.le_refl _)] at hfetch'
  exact Option.noConfusion hfetch'

/-- On a reverting execution the runner can never report success. -/
theorem preserved_revert_not_ok
    {L : List Name} {b : Block} {code : Code}
    (hc : compileProgram L b = some code)
    {s : State} (hexec : execWBlock s b = .error .revert)
    {st : Store} (hrepr : ReprState L [] s [] st)
    {fuel : Nat} {σr : List Word} {str : Store} :
    run code fuel ⟨0, [], st⟩ ≠ .ok σr str := by
  intro hrun
  obtain ⟨-, hreverting⟩ := compile_preserves_revert hc hexec hrepr
  obtain ⟨crev, hsteps₁, hfetch⟩ := hreverting
  obtain ⟨pc, hsteps₂, hhalt⟩ := run_ok_sound hrun
  have t₁ : Terminal code crev := by
    obtain ⟨p, σ0, st0⟩ := crev
    exact terminal_of_revert hfetch
  have t₂ : Terminal code ⟨pc, σr, str⟩ := Terminal.of_halted hhalt
  have heq := Steps.unique_terminal hsteps₁ hsteps₂ t₁ t₂
  rw [heq] at hfetch
  cases hhalt with
  | inl hend =>
      have hpc : pc = code.length := hend
      subst hpc
      have hfetch' : code[code.length]? = some Instr.revert := hfetch
      rw [List.getElem?_eq_none (Nat.le_refl _)] at hfetch'
      exact Option.noConfusion hfetch'
  | inr hstop =>
      have h₁ : code[pc]? = some Instr.stop := hstop
      have h₂ : code[pc]? = some Instr.revert := hfetch
      rw [h₁] at h₂
      exact Instr.noConfusion (Option.some.inj h₂)

/-! ## Function calls, by verified inlining

The source semantics gives `Stmt.callStmt` meaning *only* through
inlining: `Semantics.execStmt` is stuck on a call, and
`SolidityJudgment.checkInlined` first expands calls through the
function table (`SoliditySyntax.funDef`, KeY's `functionBodyExpand`)
and then runs the interpreter. The compiler follows the same
convention: a call-bearing block is compiled by compiling its
inlining, and the preservation theorems above apply verbatim to the
inlined block — which *is* the block's meaning. The corollaries below
restate them so the connection is explicit; no new trust is involved
(the inliner sits on the source side of the simulation, inside both
the interpreter run and the compiled code). -/

/-- Compile a block that may contain function calls: expand calls
through the function table to `depth` (an unexpandable or too-deep
call leaves a `callStmt`, which `compileStmt` rejects), then compile.
Any code this produces is covered by the corollaries below. -/
def compileProgramInlined (L : List Name) (depth : Nat) (b : Block) :
    Option Code :=
  compileProgram L (SoliditySyntax.inlineBlock depth b)

/-- **Preservation for call-bearing programs — success.** If the
inlined block's bounded execution succeeds, the official interpreter
computes the same final state on the inlined block (the source-level
meaning of `b`, per `SolidityJudgment.checkInlined`), and the machine
runs the compiled code to its end in a representing configuration. -/
theorem compileInlined_preserves_ok
    {L : List Name} {depth : Nat} {b : Block} {code : Code}
    (hc : compileProgramInlined L depth b = some code)
    {s s' : State}
    (hexec : execWBlock s (SoliditySyntax.inlineBlock depth b) = .ok s')
    {st : Store} (hrepr : ReprState L [] s [] st) :
    execBlock s (SoliditySyntax.inlineBlock depth b) = .ok s' ∧
      ∃ Γ' σ' st',
        Steps code ⟨0, [], st⟩ ⟨code.length, σ', st'⟩ ∧
          ReprState L Γ' s' σ' st' :=
  compile_preserves_ok hc hexec hrepr

/-- **Preservation for call-bearing programs — revert.** -/
theorem compileInlined_preserves_revert
    {L : List Name} {depth : Nat} {b : Block} {code : Code}
    (hc : compileProgramInlined L depth b = some code)
    {s : State}
    (hexec : execWBlock s (SoliditySyntax.inlineBlock depth b) =
      .error .revert)
    {st : Store} (hrepr : ReprState L [] s [] st) :
    execBlock s (SoliditySyntax.inlineBlock depth b) = .error .revert ∧
      Reverting code ⟨0, [], st⟩ :=
  compile_preserves_revert hc hexec hrepr

/-- A call-free block is its own inlining, so on call-free programs
`compileProgramInlined` and `compileProgram` are literally the same
function — inlining changes nothing retroactively. -/
theorem compileProgramInlined_callFree {L : List Name} {depth : Nat}
    {b : Block} (h : SoliditySyntax.blockCallFree b = true) :
    compileProgramInlined L depth b = compileProgram L b := by
  unfold compileProgramInlined
  rw [SoliditySyntax.inlineBlock_id_of_callFree depth b h]

/-! ## Judgment transfer

`SolidityJudgment.check` is the project's dynamic-logic verdict: run
the block, then evaluate the postcondition in the final state (a
revert validates a `box` judgment and refutes a `diamond` one). The
theorems below transfer a *bounded* verdict to both worlds at once:
`judgeW`/`revertW` are decidable checkers (dischargeable by
`native_decide`), and each checked verdict yields the official
`SolidityJudgment.Holds` **and** a machine-level reading — the
compiled block+postcondition runs to completion with `1` on top of
the stack (success), or the compiled block reaches `REVERT` (box). -/

/-- Compile a judgment: the block's code followed by code evaluating
the postcondition under the block's final local context. A complete
run leaves the postcondition's word on top of the final stack. -/
def compileJudgment (L : List Name) (b : Block) (post : WrappedExpr) :
    Option Code := do
  let (c, Γ') ← compileBlock L [] b
  let cp ← compileExpr L Γ' 0 post
  pure (c ++ cp)

/-- Bounded judgment checker: the bounded run succeeds and the bounded
postcondition evaluates to `true`. -/
def judgeW (b : Block) (post : WrappedExpr) (s0 : State) : Bool :=
  match execWBlock s0 b with
  | .ok s' =>
      match evalW s' post with
      | .ok (Value.bool true) => true
      | _ => false
  | _ => false

/-- Bounded revert checker (validates `box` judgments). -/
def revertW (b : Block) (s0 : State) : Bool :=
  match execWBlock s0 b with
  | .error .revert => true
  | _ => false

/-- **Judgment transfer — success.** A `judgeW`-checked judgment holds
under the official semantics (any modality), and the machine, running
the compiled block+postcondition from any storage representing `s0`,
falls through to the end of the code with the word `1` (true) on top
of the stack. -/
theorem judgment_transfer
    {L : List Name} {b : Block} {post : WrappedExpr} {code : Code}
    (hc : compileJudgment L b post = some code)
    {s0 : State} (hw : judgeW b post s0 = true)
    {st : Store} (hrepr : ReprState L [] s0 [] st)
    (sm : SolidityModality) :
    (SolidityJudgment.mk ⟨sm, b⟩ post).Holds s0 ∧
      ∃ σ' st',
        Steps code ⟨0, [], st⟩ ⟨code.length, 1 :: σ', st'⟩ := by
  unfold judgeW at hw
  cases hexec : execWBlock s0 b with
  | error e => rw [hexec] at hw; cases e <;> simp at hw
  | ok s' =>
    simp only [hexec] at hw
    cases hpost : evalW s' post with
    | error e => simp only [hpost] at hw; cases e <;> simp at hw
    | ok v =>
      simp only [hpost] at hw
      cases v with
      | int n => simp at hw
      | bool bv =>
        cases bv with
        | false => simp at hw
        | true =>
          have hofb := execWBlock_agree s0 b
          rw [hexec] at hofb
          simp only [Agrees_ok, id] at hofb
          have hofp := evalW_agree post s'
          rw [hpost] at hofp
          simp only [Agrees_ok] at hofp
          constructor
          · simp [SolidityJudgment.Holds, SolidityJudgment.check,
              hofb, hofp]
          · simp only [compileJudgment] at hc
            cases hcb : compileBlock L [] b with
            | none => rw [hcb] at hc; simp [bind, Option.bind] at hc
            | some p =>
              obtain ⟨c, Γ'⟩ := p
              simp only [hcb, bind, Option.bind] at hc
              cases hcp : compileExpr L Γ' 0 post with
              | none =>
                  rw [hcp] at hc; simp [bind, Option.bind] at hc
              | some cp =>
                simp only [hcp, bind, Option.bind, pure,
                  Option.pure_def, Option.some.injEq] at hc
                subst hc
                have hclaim := compileBlock_sim L [] b hcb s0
                  ((codeAt_self (c ++ cp)).append_left) hrepr
                rw [hexec] at hclaim
                simp only [ExecClaim_ok] at hclaim
                obtain ⟨σ1, st1, hsteps1, hrepr1⟩ := hclaim
                simp only [Nat.zero_add] at hsteps1
                have hcodep : codeAt (c ++ cp) c.length cp :=
                  codeAt_cast
                    ((codeAt_self (c ++ cp)).append_right)
                    (by omega)
                have hclaimp := compileExpr_sim L Γ' 0 post hcp s'
                  (σt := []) hcodep rfl hrepr1
                simp only [List.nil_append] at hclaimp
                rw [hpost] at hclaimp
                simp only [EvalClaim_ok] at hclaimp
                obtain ⟨w, hwv, hsteps2⟩ := hclaimp
                have hw1 : w = 1 := by
                  simpa [ReprVal] using hwv
                subst hw1
                refine ⟨σ1, st1, ?_⟩
                refine Steps.cast_pc
                  (Steps.trans hsteps1 hsteps2) ?_
                simp [List.length_append]

/-- **Judgment transfer — revert.** A `revertW`-checked block
validates its `box` judgments officially, and the compiled code
reaches a `REVERT` instruction on the machine. -/
theorem judgment_transfer_revert
    {L : List Name} {b : Block} {post : WrappedExpr} {code : Code}
    (hc : compileJudgment L b post = some code)
    {s0 : State} (hw : revertW b s0 = true)
    {st : Store} (hrepr : ReprState L [] s0 [] st) :
    (SolidityJudgment.mk ⟨SolidityModality.box, b⟩ post).Holds s0 ∧
      Reverting code ⟨0, [], st⟩ := by
  unfold revertW at hw
  cases hexec : execWBlock s0 b with
  | ok s' => rw [hexec] at hw; simp at hw
  | error e =>
    rw [hexec] at hw
    cases e
    case stuck => simp at hw
    case _ =>
      have hofb := execWBlock_agree s0 b
      rw [hexec] at hofb
      simp only [Agrees_revert] at hofb
      constructor
      · simp [SolidityJudgment.Holds, SolidityJudgment.check, hofb]
      · simp only [compileJudgment] at hc
        cases hcb : compileBlock L [] b with
        | none => rw [hcb] at hc; simp [bind, Option.bind] at hc
        | some p =>
          obtain ⟨c, Γ'⟩ := p
          simp only [hcb, bind, Option.bind] at hc
          cases hcp : compileExpr L Γ' 0 post with
          | none => rw [hcp] at hc; simp [bind, Option.bind] at hc
          | some cp =>
            simp only [hcp, bind, Option.bind, pure,
              Option.pure_def, Option.some.injEq] at hc
            subst hc
            have hclaim := compileBlock_sim L [] b hcb s0
              ((codeAt_self (c ++ cp)).append_left) hrepr
            rw [hexec] at hclaim
            simpa using hclaim

end Evm
end Solidity
