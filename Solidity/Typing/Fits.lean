import Solidity.Typing.Tight

/-!
# Reachable storage fits (decision 77, its conditional form)

`Typing/Constructibility.lean` characterises the reachable storages among
those that fit (`SVal.Fits`: every mapping key and array slot in range,
what a literal can write), and `huge_reachable_not_fits` shows that a
contract whose fixed-size array is past `2^256` elements reaches a storage
that does not fit.  This module proves the converse under solc's own bound:
for a contract whose fixed sizes are all at most `2^256` (`FixedFits`, what
solc's "type too large for storage" implies), **every reachable storage
fits** (`reachable_fits`), so `reachable_iff_fits` drops the premise.

A word is in range and a fixed-size array has exactly its type's length by
the typed state; a dynamic array has fewer than `2^256` live elements
(`SVal.array`'s bound).  What is not by construction is a third run
invariant beside the canonical and the tight one (`bndH`): every mapping key
is in its key type's range (`SMap`'s keys are `Int`s; a key is written
through `PrimTy.key` of a typed index, or along an alias's path, which the
locals part of the invariant keeps, `LTy.Keyed`), and every dynamic array's
live and recycled slots together are fewer than `2^256`: `push` takes a
recycled slot or checks the bound (`Storage.full`), `pop` and `delete` move
slots, never add one, and a copy keeps the larger of the old slot count and
the new length.
-/

namespace Solidity

open Semantics (structDef lookupBy setBy nodupKeysB)

variable {C : Contract}

/-! ## Bounded values -/

/-- A bounded node: a dynamic array's slots fewer than `2^256` in all, a
mapping's keys in their key type's range. -/
def bndH : Hered where
  arr := fun {_} {n} _ sh => n + sh.length < 2 ^ 256
  fix _ _ := True
  map K := fun m _ => ∀ e ∈ m.toList, K.keyOk e.1

/-- `v` bounded. -/
abbrev SVal.Bnd {T : Ty} (v : SVal T) : Prop := v.All bndH

/-- Every root bounded. -/
abbrev Storage.Bnd (st : Storage C) : Prop := st.All bndH

theorem SList.length_ofList {E : Ty} (l : List (SVal E)) : (SList.ofList l).length = l.length := by
  simp only [SList.length, SList.toList_ofList]

theorem SList.length_nil {E : Ty} : (SList.nil (E := E)).length = 0 := by
  simp only [SList.length, SList.toList_nil, List.length_nil]

theorem bndH_nil (E : Ty) : bndH.arr (SVec.nil (E := E)) (SList.nil (E := E)) := by
  show 0 + SList.length SList.nil < 2 ^ 256
  rw [SList.length_nil]; decide

/-- A default is bounded. -/
theorem SVal.dflt_bnd (T : Ty) : (SVal.dflt T).Bnd :=
  SVal.dflt_all (P := bndH) bndH_nil (fun _ _ => trivial)
    (fun _ _ e he => by rw [SMap.toList_nil] at he; exact nomatch he) T

/-- **Every storage operation keeps the nodes bounded**: an entry is written
at a key in range, and slots are moved, recycled or pushed below the
bound. -/
theorem bndH_run : HeredRun bndH (fun _ => True) where
  save e sh i x hi _ harr _ := by
    show (List.take _ _).length + (SList.ofList _).length < _
    rw [SList.length_ofList, List.length_take, List.length_drop, List.length_set,
      List.length_append, SVec.length_toList]
    have : sh.toList.length = sh.length := rfl
    have harr' : _ + sh.length < 2 ^ 256 := harr
    omega
  map m d k x hk _ hm e he := by
    rw [SMap.toList_ofList] at he
    rcases fst_mem_setBy he with h | ⟨w, hw⟩
    · rw [h]; exact hk
    · exact hm (e.1, w) hw
  strip _ _ harr _ := by
    show _ + SList.length .nil < _
    rw [SList.length_nil]
    have harr' : _ + _ < 2 ^ 256 := harr
    omega
  del e sh harr _ := by
    show 0 + (SList.ofList _).length < _
    rw [SList.length_ofList, List.length_append, SVec.length_toList]
    have : sh.toList.length = sh.length := rfl
    have harr' : _ + sh.length < 2 ^ 256 := harr
    omega
  ov oel osh nel nsh ho hn _ _ _ := by
    show _ + (SList.ofList _).length < _
    rw [SList.length_ofList, List.length_append, List.length_map, List.length_drop,
      List.length_drop, SVec.length_toList]
    have h1 : osh.toList.length = osh.length := rfl
    have ho' : _ + osh.length < 2 ^ 256 := ho
    have hn' : _ + nsh.length < 2 ^ 256 := hn
    omega
  push e sh x _ hb harr _ _ _ := by
    show (e.toList ++ [x]).length + (SList.ofList _).length < _
    rw [SList.length_ofList, List.length_append, SVec.length_toList, List.length_singleton]
    have harr' : _ + sh.length < 2 ^ 256 := harr
    have : sh.toList.length = sh.length := rfl
    cases hs : sh.toList with
    | nil => simp only [pushSlot, List.length_nil]; omega
    | cons c rest =>
      rw [hs, List.length_cons] at this
      simp only [pushSlot] at this ⊢
      omega
  pop e sh last keep hlast _ harr _ _ := by
    show (e.toList.dropLast).length + (SList.ofList _).length < _
    rw [SList.length_ofList, List.length_dropLast, List.length_cons, SVec.length_toList]
    have hpos : 0 < e.toList.length := List.length_pos_of_mem hlast
    rw [SVec.length_toList] at hpos
    have : sh.toList.length = sh.length := rfl
    have harr' : _ + sh.length < 2 ^ 256 := harr
    omega
  dflt := SVal.dflt_bnd
  plain v _ h := SVal.all_mono' (P := bndH) (Q := plainH)
    (fun _ sh hn hsh => by
      have hsh' : sh = .nil := hsh
      subst hsh'
      show _ + SList.length .nil < _
      rw [SList.length_nil]; omega)
    (fun _ _ _ => trivial) (fun _ _ h => h.elim) v h

/-- The storage a contract starts with is bounded. -/
theorem Storage.init_bnd : (Storage.init C).Bnd :=
  SFields.dflt_all (P := bndH) bndH_nil (fun _ _ => trivial)
    (fun _ _ e he => by rw [SMap.toList_nil] at he; exact nomatch he) C.vars

/-- The third run invariant: bounded storage, aliases along keys a program
writes. -/
abbrev fitsInv (C : Contract) : RunInv C := heredInv C bndH

/-- A block run from a bounded state ends, if in a state, in a bounded one.
The twin of `Prog.run_canon` (`Typing/Reachability.lean`) for this
invariant: nothing cites it, it is kept as the run-level statement beside
`reachable_bnd`. -/
theorem Prog.run_bnd {Γ Γ' : Ctx} (P : Prog C Γ Γ') {σ : State C Γ} {o : Out C σ.H Γ'}
    (hσ : (fitsInv C).HoldsT σ) (h : P.run σ = .ok o) : o.st.storage.Bnd :=
  Prog.run_all bndH_run (fun _ => trivial) P hσ h

/-- **Reachable ⇒ bounded**: every storage a program reaches from the
contract's initial state has its keys in range and its arrays' slots below
`2^256`. -/
theorem reachable_bnd {st : Storage C} (h : Reachable C st) : st.Bnd :=
  Reachable.all bndH_run (fun _ => trivial) Storage.init_bnd h

/-! ## Fixed sizes -/

/-- Every fixed-size array type a path reaches from `T` has at most `2^256`
elements. -/
def FixedFitsAt (T : Ty) : Prop := ∀ E n, Path T (.ref (.fixed E n)) → n ≤ 2 ^ 256

/-- **The contract's fixed sizes fit**: every fixed-size array type in its
storage layout has at most `2^256` elements, which solc's "type too large
for storage" check implies (`Huge` is refused). -/
def FixedFits (C : Contract) : Prop := ∀ nt ∈ C.vars, FixedFitsAt nt.2

/-- Bounded at types whose fixed sizes fit is fitting. -/
theorem fixedFits_mono : fitsH.Mono bndH FixedFitsAt :=
  ⟨fun _ hT _ hm E n p => hT E n (.field (lookupBy_of_nodup (structDef_nodup _) hm) p),
    fun _ hT E n p => hT E n (.at 0 p), fun _ _ hT E n p => hT E n (.atF 0 p),
    fun _ _ hT E n p => hT E n (.key 0 p),
    fun _ _ _ _ h => h, fun E n hT _ => hT E n .nil, fun _ _ _ h => h⟩

/-- A bounded value fits, its fixed sizes within `2^256`. -/
theorem SVal.fits_of_bnd {T : Ty} (v : SVal T) (hT : FixedFitsAt T) (h : v.Bnd) : v.Fits :=
  SVal.all_mono (P := fitsH) (Q := bndH) (G := FixedFitsAt) fixedFits_mono v hT h

/-- A bounded storage fits, its fixed sizes within `2^256`. -/
theorem Storage.fits_of_bnd (hf : FixedFits C) (st : Storage C) (h : st.Bnd) : st.Fits :=
  SFields.all_mono (P := fitsH) (Q := bndH) (G := FixedFitsAt) fixedFits_mono st hf h

/-- **Reachable ⇒ fits** (decision 77, its conditional form): for a contract
whose fixed sizes are at most `2^256` (solc's "type too large for storage"),
every reachable storage has its keys and slots in range. -/
theorem reachable_fits (hf : FixedFits C) {st : Storage C} (h : Reachable C st) : st.Fits :=
  Storage.fits_of_bnd hf st (reachable_bnd h)

end Solidity
