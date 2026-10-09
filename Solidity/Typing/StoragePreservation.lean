import Solidity.Typing.Storage
import Solidity.Semantics.Properties

/-!
# Storage values the erased operations produce are typed

Lemmas about `SVal.hasTy` (`Typing/Storage.lean`) that the typing of the
erased state (`Typing/State.lean`, `Typing/Soundness.lean`) and the
invariants of `Typing/Reachability.lean` read: lengths kept by `delete`
and the copies, lookups in a nodup-keyed list, a fresh default inhabits
its type (`defaultForTy_hasTy`: `defaultOk_true`, since no struct repeats
a member name), arithmetic gives ints (`applyBinOp_arith_int`), and the
slot a `push` recycles (`pushSlot_prim`).  The typed run keeps its storage
typed by construction (`State.erase_wt`, `Typing/TypedWT.lean`), so no
preservation lemma for a write is left here.
-/

namespace Solidity
namespace Semantics

open SemanticsProperties (lookupBy_setBy_self lookupBy_setBy_ne lookupBy_eq_some_mem)

/-! ## `hasTy` of a list -/

theorem hasTyElems_of_forall_mem {elem : Ty} {elems : List SVal}
    (h : ∀ v ∈ elems, v.hasTy elem = true) :
    SVal.hasTy.hasTyElems elem elems = true := by
  induction elems with
  | nil => rfl
  | cons v rest ih =>
      simp only [SVal.hasTy.hasTyElems, Bool.and_eq_true]
      exact ⟨h v (List.Mem.head _), ih fun w hw => h w (List.Mem.tail _ hw)⟩

/-! ## Lengths -/

/-- `delete` keeps a list of elements as long as it was: a fixed-size
array's length survives it. -/
theorem SVal.defaultOfElems_length (elems : List SVal) :
    (SVal.defaultOf.defaultOfElems elems).length = elems.length := by
  induction elems with
  | nil => rfl
  | cons _ _ ih => simp [SVal.defaultOf.defaultOfElems, ih]

/-- A copy keeps a list of elements as long as the copied one. -/
theorem SVal.stripElems_length' (elems : List SVal) :
    (SVal.strip.stripElems elems).length = elems.length := by
  induction elems with
  | nil => rfl
  | cons _ _ ih => simp [SVal.strip.stripElems, ih]

/-- A copy over old elements is as long as the new ones. -/
theorem SVal.overlayElems_length (olds news : List SVal) :
    (SVal.overlay.overlayElems olds news).length = news.length := by
  induction news generalizing olds with
  | nil => cases olds <;> rfl
  | cons x xs ih =>
    cases olds with
    | nil => simp [SVal.overlay.overlayElems, SVal.stripElems_length']
    | cons o os => simp [SVal.overlay.overlayElems, ih]

/-! ## Lookups in a nodup-keyed list -/

theorem lookupBy_isSome_of_mem [DecidableEq κ] {l : List (κ × α)}
    {k : κ} {v : α} (hmem : (k, v) ∈ l) :
    (lookupBy k l).isSome = true := by
  induction l with
  | nil => cases hmem
  | cons p rest ih =>
      obtain ⟨k', v'⟩ := p
      by_cases hk : k = k'
      · simp [lookupBy, hk]
      · cases hmem with
        | head => exact absurd rfl hk
        | tail _ hmem => simpa [lookupBy, hk] using ih hmem

/-- On a nodup-keyed association list, membership determines lookup. -/
theorem lookupBy_eq_of_nodup [DecidableEq κ] {l : List (κ × α)} {k : κ}
    {v : α} (hnd : nodupKeysB l = true) (hmem : (k, v) ∈ l) :
    lookupBy k l = some v := by
  induction l with
  | nil => cases hmem
  | cons p rest ih =>
      obtain ⟨k', v'⟩ := p
      simp only [nodupKeysB, Bool.and_eq_true] at hnd
      cases hmem with
      | head => simp [lookupBy]
      | tail _ hmem =>
          by_cases hk : k = k'
          · subst hk
            have := lookupBy_isSome_of_mem hmem
            rw [Option.isNone_iff_eq_none.mp hnd.1] at this
            exact Bool.noConfusion this
          · simpa [lookupBy, hk] using ih hnd.2 hmem

/-! ## The `defaultForTy` side condition

The depth charge the fuelled version carried is gone with the fuel:
`defaultForTy` is correct at every nesting depth now
(`Semantics.structDef_rank_lt`), so the no-duplicate-row condition is all
the content that is left. -/

mutual
/-- The side condition under which `defaultForTy` inhabits its type:
each `structDef` row is the one its field name looks up to, which rules
out duplicate field names. Decidable per concrete type. -/
def defaultOk : Ty -> Bool
  | Ty.prim _ => true
  | Ty.ref (RefTy.struct s) => defaultOkFields s (structDef s)
  | Ty.ref (RefTy.array _) => true
  | Ty.ref (RefTy.fixed e _) => defaultOk e
  | Ty.ref (RefTy.mapping _ value) => defaultOk value
termination_by ty => (tyRank ty, sizeOf ty)
decreasing_by
  · exact Prod.Lex.left _ _ (structDef_rank_lt _)
  all_goals first
    | (apply Prod.Lex.left; simp [tyRank]; done)
    | (apply Prod.Lex.right; simp; omega)

def defaultOkFields (s : Name) : List (Name × Ty) -> Bool
  | [] => true
  | (n, t) :: rest =>
      defaultOk t && (lookupBy n (structDef s) == some t) &&
        defaultOkFields s rest
termination_by l => (fieldsRank l, sizeOf l)
decreasing_by
  all_goals (apply lex_le_lt
             · simp only [fieldsRank]; omega
             · simp; omega)
end

/-- **Every type's fresh default is well-formed**: no struct of the table
repeats a member name (`structDef_nodup`), so each row is the one its name
looks up to. -/
theorem defaultOk_true : ∀ (ty : Ty), defaultOk ty = true := by
  intro ty
  induction ty using defaultForTy.induct
    (motive2 := fun l => ∀ (s : Name), (∀ nt ∈ l, lookupBy nt.1 (structDef s) = some nt.2) →
      defaultOkFields s l = true) with
  | case1 | case2 | case3 | case5 => rw [defaultOk]
  | case4 name ih =>
      rw [defaultOk]
      exact ih name fun nt hm => lookupBy_eq_of_nodup (structDef_nodup name) hm
  | case6 elem n ih => rw [defaultOk]; exact ih
  | case7 key value ih => rw [defaultOk]; exact ih
  | case8 => rw [defaultOkFields]
  | case9 n t rest iht ihrest =>
      rename_i s h
      have hl : lookupBy n (structDef s) = some t := h (n, t) List.mem_cons_self
      rw [defaultOkFields, iht, hl, ihrest s fun nt hm => h nt (List.mem_cons_of_mem _ hm)]
      simp only [beq_self_eq_true, Bool.and_self]

/-- Fresh defaults inhabit their type, under `defaultOk`. -/
theorem defaultForTy_hasTy_of : ∀ {ty : Ty}, defaultOk ty = true ->
    (defaultForTy ty).hasTy ty = true := by
  intro ty
  induction ty using defaultForTy.induct
    (motive2 := fun l => ∀ (s : Name), defaultOkFields s l = true ->
      SVal.hasTy.hasTyFields s (defaultForFields l) = true) with
  | case1 => intro _; simp [defaultForTy, SVal.hasTy]
  | case2 => intro _; simp [defaultForTy, SVal.hasTy]
  | case3 => intro _; simp [defaultForTy, SVal.hasTy]
  | case4 name ih =>
      intro h
      simp only [defaultOk] at h
      simpa only [defaultForTy, SVal.hasTy] using ih name h
  | case5 elem =>
      intro _
      simp [defaultForTy, SVal.hasTy, SVal.hasTy.hasTyElems]
  | case6 elem n ih =>
      intro h
      simp only [defaultOk] at h
      simp only [defaultForTy, SVal.hasTy, Bool.and_eq_true, beq_iff_eq, List.length_replicate]
      exact ⟨⟨⟨trivial, trivial⟩, hasTyElems_of_forall_mem fun v hv => by
        rw [List.eq_of_mem_replicate hv]; exact ih h⟩, rfl⟩
  | case7 key value ih =>
      intro h
      simp only [defaultOk] at h
      simp only [defaultForTy, SVal.hasTy, SVal.hasTy.hasTyEntries,
        Bool.true_and]
      exact ih h
  | case8 => simp [defaultForFields, SVal.hasTy.hasTyFields]
  | case9 n t rest iht ihrest =>
      rename_i s h
      simp only [defaultOkFields, Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨⟨hok, hlook⟩, hrest⟩ := h
      simp only [defaultForFields, SVal.hasTy.hasTyFields, hlook,
        Bool.and_eq_true]
      exact ⟨iht hok, ihrest s hrest⟩

/-- **Fresh defaults inhabit their type.** -/
theorem defaultForTy_hasTy {ty : Ty} : (defaultForTy ty).hasTy ty = true :=
  defaultForTy_hasTy_of (defaultOk_true ty)

/-- `asValue` round-trips through `toSVal`: reading a primitive out of
storage and writing it back is the identity. -/
theorem SVal.asValue_toSVal {v : SVal} {w : Value}
    (h : v.asValue = Except.ok w) : w.toSVal = v := by
  cases v with
  | prim p =>
      cases p <;> simp only [SVal.asValue] at h <;>
        simp [<- Except.ok.inj h, Value.toSVal]
  | struct fields => exact nomatch h
  | array elems => exact nomatch h
  | map entries dflt => exact nomatch h

/-- Arithmetic operators produce ints (comparisons and connectives are
the `Value.bool` results — that split is why a compound assignment
(`BinOp.hasCompoundAssign`) needs `op.isArith`). -/
theorem applyBinOp_arith_int {op : BinOp} {l r v : Value}
    (hop : op.isArith = true) (h : applyBinOp op l r = Except.ok v) :
    ∃ n, v = Value.int n := by
  cases op <;> simp only [BinOp.isArith] at hop <;>
    try exact Bool.noConfusion hop
  all_goals
    simp only [applyBinOp, bind, Except.bind] at h
  all_goals
    repeat' split at h
  all_goals
    first
    | exact ⟨_, (Except.ok.inj h).symm⟩
    | exact nomatch h

/-! ## Layout key uniqueness -/

/-! `nodupKeysB` (`AST.lean`): `wellTypedStorageB` checks every layout row
against the single stored value at its root, so a duplicated root would
check one value against two types (a counterexample removed with the
untyped layer, to be ported: `docs/kernel-port.md`'s "Port later"). -/

/-! ## The recycled slot a `push` lands on

`Semantics.pushSlot` either hands back a slot a `pop` cleared — still an
element of the array, so still of the element type — or materialises the
type's default.  Both inhabit the element type. -/

/-- The `isPrimitive` branch of `pushSlot` is redundant where the recycled
slot inhabits the element type: clearing a primitive gives the type's own
default.  So the two readings of "the slot a `push` lands on" agree on every
well-typed storage, and the branch buys the EVM layer its typing-free view. -/
theorem pushSlot_prim {elemTy : Ty} {c : SVal} {rest : List SVal}
    (hp : elemTy.isPrimitive = true) (hc : c.hasTy elemTy = true) :
    (pushSlot elemTy (c :: rest)).1 = c.defaultOf := by
  cases elemTy with
  | ref r => simp [Ty.isPrimitive] at hp
  | prim pt =>
      cases c with
      | prim p =>
          cases pt <;> cases p <;>
            simp_all [pushSlot, SVal.defaultOf, defaultForTy, SVal.hasTy,
              Ty.isPrimitive]
      | struct _ => cases pt <;> simp [SVal.hasTy] at hc
      | array _ _ => cases pt <;> simp [SVal.hasTy] at hc
      | map _ _ => cases pt <;> simp [SVal.hasTy] at hc

end Semantics
end Solidity
