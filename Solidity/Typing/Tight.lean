import Solidity.Typing.Reachability

/-!
# Tight storage: what every reachable storage satisfies beyond canonical

`Typing/Reachability.lean` proves reachable ⇒ canonical (`reachable_canon`).
The converse needs three more facts, which every run keeps and
`SVal.Canon` does not say; `SVal.Tight` (`tightH`) is exactly them:

- an array whose element type has no well-formed default has no slots at
  all: `push()` needs the default, and nothing else makes one (no struct of
  the table lacks one since decision 16 refused a repeated member name,
  `refusedStructs`; the clause stays for a type `defaultOkS` refuses);
- the slots past the end of an array of words are cleared: `pop`, `delete`
  and a shorter copy clear what they leave, and past an end only a reference
  reaches, never a word (`SVal.Live`, from `Storage.checkIndex`);
- a mapping keyed by a reference type has no entries: no program indexes
  it (`IndexTy.map` takes a word key; a `bool` one is hashed as `0`/`1`).

A fixed-size array has nothing past its end by its type.  `Prog.run_tight`
is the preservation theorem: every contract carries well-formed storage
types (`Contract.vars_ok`), and the typed run keeps
`heredInv C tightH` (`Typing/HeredRun.lean`, `tightH_run`).  Under
`Ty.okDeep` the first clause is vacuous, so a copy out of memory is tight
(`SVal.Plain`).

`SVal.Fits` (`fitsH`) is what the builder of
`Typing/Constructibility.lean` needs to write a value with literals: every
dynamic array's slots, past its end too, fewer than `2^256`, every
fixed-size array at most `2^256` long (a mapping's keys are values of its
key type).
-/

namespace Solidity

open Semantics (structDef lookupBy setBy nodupKeysB)

variable {C : Contract}

/-! ## The tight values -/

/-- A tight node: an array whose elements have no well-formed default has no
slots, the slots past the end of an array of words are defaults. -/
def tightH : Hered where
  arr := fun {E} {n} _ sh => (E.defaultOkS = false → n = 0 ∧ sh = .nil) ∧
    (E.isPrimitive = true → ∀ w ∈ sh.toList, w = SVal.dflt E)
  fix _ _ := True
  map _ := fun _ _ => True

/-- `v` is tight. -/
abbrev SVal.Tight {T : Ty} (v : SVal T) : Prop := v.All tightH

/-- Every root tight. -/
abbrev Storage.Tight (st : Storage C) : Prop := st.All tightH

/-- A word's `delete` is the default. -/
theorem SVal.defaultOf_of_prim {E : Ty} (hE : E.isPrimitive = true) (x : SVal E) :
    x.defaultOf = SVal.dflt E := by
  cases E with
  | prim p => cases x; simp only [SVal.defaultOf, SVal.dflt_prim]
  | ref _ => exact nomatch hE

/-- The slots `push` leaves past the end are among those that were. -/
theorem pushSlot_snd_sub {E : Ty} : {l : List (SVal E)} → ∀ w ∈ (pushSlot E l).2, w ∈ l
  | [], _, h => nomatch h
  | _ :: _, _, h => List.mem_cons_of_mem _ h

theorem SVec.toList_eq_nil {E : Ty} {n : Nat} (e : SVec E n) (h : n = 0) : e.toList = [] :=
  List.eq_nil_of_length_eq_zero (by rw [SVec.length_toList]; exact h)

/-- A default is tight. -/
theorem SVal.dflt_tight (T : Ty) : (SVal.dflt T).Tight :=
  SVal.dflt_all (P := tightH)
    (fun _ => ⟨fun _ => ⟨rfl, rfl⟩, fun _ w hw => by rw [SList.toList_nil] at hw; exact nomatch hw⟩)
    (fun _ _ => trivial) (fun _ _ => trivial) T

/-- A storage reference reaches a type with well-formed defaults all the
way down, as guaranteed by its contract. -/
theorem SRef.okDeep {U : Ty} (r : SRef C U) : U.okDeep = true :=
  Path.okDeep r.path (C.root_okDeep r.hroot)

/-- An array with nothing past its end, of elements with a well-formed
default, is a tight node. -/
theorem tight_of_plainArr {E : Ty} {n : Nat} (e : SVec E n) (sh : SList E) (_ : n < 2 ^ 256)
    (hE : E.okDeep = true)
    (hsh : plainH.arr e sh) : tightH.arr e sh := by
  have hsh' : sh = .nil := hsh
  subst hsh'
  refine ⟨fun hd => ?_, fun _ w hw => ?_⟩
  · rw [okDeep_defaultOkS hE] at hd; exact nomatch hd
  · rw [SList.toList_nil] at hw; exact nomatch hw

/-- **Every storage operation keeps the nodes tight**, at `okDeep` types: a
word is written into a live slot only, a key only at a word key type, and a
push and a copy out of memory find a well-formed default. -/
theorem tightH_run : HeredRun tightH (fun T => T.okDeep = true) where
  save e sh i x hi hlive harr _ := by
    refine ⟨fun hd => ?_, fun hp w hw => ?_⟩
    · obtain ⟨hn, hsh⟩ := harr.1 hd
      subst hsh
      rw [SVec.toList_eq_nil e hn, SList.toList_nil] at hi
      exact absurd hi (Nat.not_lt_zero _)
    · rw [SList.toList_ofList, List.drop_set, if_pos (hlive hp),
        List.drop_left' (SVec.length_toList e)] at hw
      exact harr.2 hp w hw
  map _ _ _ _ _ _ := trivial
  strip _ sh harr _ :=
    ⟨fun hd => ⟨(harr.1 hd).1, rfl⟩, fun _ w hw => by rw [SList.toList_nil] at hw; exact nomatch hw⟩
  del e sh harr _ := by
    refine ⟨fun hd => ⟨rfl, ?_⟩, fun hp w hw => ?_⟩
    · obtain ⟨hn, hsh⟩ := harr.1 hd
      subst hsh
      rw [SVec.toList_defaultOf, SVec.toList_eq_nil e hn, SList.toList_nil]
      rfl
    · rw [SList.toList_ofList] at hw
      rcases List.mem_append.mp hw with hw | hw
      · rw [SVec.toList_defaultOf] at hw
        obtain ⟨u, -, rfl⟩ := List.mem_map.mp hw
        exact SVal.defaultOf_of_prim hp u
      · exact harr.2 hp w hw
  ov oel osh nel nsh ho hn _ _ _ := by
    refine ⟨fun hd => ⟨(hn.1 hd).1, ?_⟩, fun hp w hw => ?_⟩
    · obtain ⟨hm, hosh⟩ := ho.1 hd
      subst hosh
      rw [SVec.toList_eq_nil oel hm, SList.toList_nil]
      simp only [List.drop_nil, List.map_nil, List.append_nil]
      rfl
    · rw [SList.toList_ofList] at hw
      rcases List.mem_append.mp hw with hw | hw
      · obtain ⟨u, -, rfl⟩ := List.mem_map.mp hw
        exact SVal.defaultOf_of_prim hp u
      · exact ho.2 hp w (List.mem_of_mem_drop hw)
  push e sh x hG _ harr _ _ _ := by
    refine ⟨fun hd => ?_, fun hp w hw => ?_⟩
    · rw [okDeep_defaultOkS (by simpa only [Ty.okDeep] using hG)] at hd; exact nomatch hd
    · rw [SList.toList_ofList] at hw
      exact harr.2 hp w (pushSlot_snd_sub w hw)
  pop e sh last keep hlast hkeep harr _ _ := by
    refine ⟨fun hd => ?_, fun hp w hw => ?_⟩
    · rw [SVec.toList_eq_nil e (harr.1 hd).1] at hlast; exact nomatch hlast
    · rw [SList.toList_ofList] at hw
      rcases List.mem_cons.mp hw with hw | hw
      · cases keep with
        | true => rw [hkeep rfl] at hp; exact nomatch hp
        | false => rw [hw]; exact SVal.defaultOf_of_prim hp last
      · exact harr.2 hp w hw
  dflt := SVal.dflt_tight
  plain v hT h := SVal.all_mono_deep (P := tightH) (Q := plainH) tight_of_plainArr
    (fun _ _ _ _ => trivial) (fun _ _ _ h => h.elim) v hT h

/-- The storage a contract starts with is tight. -/
theorem Storage.init_tight : (Storage.init C).Tight :=
  SFields.dflt_all (P := tightH)
    (fun _ => ⟨fun _ => ⟨rfl, rfl⟩, fun _ w hw => by rw [SList.toList_nil] at hw; exact nomatch hw⟩)
    (fun _ _ => trivial) (fun _ _ => trivial) C.vars

/-- What a run keeps beyond canonical: tight storage, its aliases along keys
a program writes. -/
abbrev tightInv (C : Contract) : RunInv C := heredInv C tightH

/-- **Tightness**: a block run from a state whose storage is tight, its aliases
bound along keys a program writes, ends, if in a state, in one whose storage
is tight. -/
theorem Prog.run_tight {Γ Γ' : Ctx} (P : Prog C Γ Γ') {σ : State C Γ}
    {o : Out C σ.H Γ'} (hσ : (tightInv C).HoldsT σ) (h : P.run σ = .ok o) :
    o.st.storage.Tight :=
  Prog.run_all tightH_run SRef.okDeep P hσ h

/-- **Reachable ⇒ tight**, for every contract. -/
theorem reachable_tight {st : Storage C} (h : Reachable C st) : st.Tight :=
  Reachable.all tightH_run SRef.okDeep Storage.init_tight h

/-! ## Values the builder writes -/

/-- A node the builder writes with literals: a dynamic array's slots fewer
than `2^256` in all (the builder pushes them all), a fixed-size array at
most `2^256` long (its indices are `uint`s). -/
def fitsH : Hered where
  arr := fun {_} {n} _ sh => n + sh.length < 2 ^ 256
  fix _ n := n ≤ 2 ^ 256
  map _ := fun _ _ => True

/-- `v`'s slots in range. -/
abbrev SVal.Fits {T : Ty} (v : SVal T) : Prop := v.All fitsH

/-- Every root's keys and slots in range. -/
abbrev Storage.Fits (st : Storage C) : Prop := st.All fitsH

end Solidity
