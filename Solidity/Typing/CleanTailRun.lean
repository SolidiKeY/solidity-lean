import Solidity.Typing.CleanTail
import Solidity.Typing.HeredRun

/-!
# Clean tails, kept by a contract that exposes nothing

`Storage.CleanTail` (`Typing/CleanTail.lean`) is not kept by every run: a
write through an alias left past a live end by a shrink (a `pop`, a
`delete`, a copy over a longer array) lands in the slots past the end, and
an empty `push` later exposes it (`docs/options.md`, O6).  It is kept by a
program that never shrinks an array while a storage alias may point into
it (`Prog.exposesNone`): then every alias stays at live slots, every write
lands at live slots, and what lies past an end is only what a clear left,
an ordinary default.

**The invariant** (`CTInv`) is the clean storage and every alias local live
(`Storage.LiveAll`: every dynamic array along its path entered below its
length).  A statement keeps it (`Stmt.keeps_ct`), and where an alias may be
held around it (its own context's, or a caller's: the flag `g`) it also
keeps every live reference live (`Storage.Grows`): such a statement shrinks
no array but one of words, which no alias enters.

**The check** (`Stmt.ctSafe`) is syntactic, on the elaborated program: a
statement that may shrink an array of references (an assignment or a
`delete` of a reference, a copy out of memory, a `pop` of references) only
where no alias is in scope, here or in a caller (`outer`); a recursive call
is not unfolded and fails it.  A contract all of whose functions pass it
keeps clean tails from its deployment on (`ReachableBy.cleanTail`).
-/

namespace Solidity

open Semantics (structDef lookupBy setBy lookupBy_setBy_self lookupBy_setBy_ne
  lookupBy_eq_some_mem)

variable {C : Contract}

/-! ## Live slots, every array -/

/-- Along `p` from `x`, every dynamic array entered below its live length. -/
def SVal.LiveAll : {T U : Ty} → SVal T → Path T U → Prop
  | _, _, _, .nil => True
  | _, _, .struct fs, .field h p => (fs.get h).LiveAll p
  | _, _, @SVal.array _ n e sh _, .at i p =>
    i.1.toNat < n ∧ ∀ y, (e.toList ++ sh.toList)[i.1.toNat]? = some y → y.LiveAll p
  | _, _, .fixed e, .atF i p => ∀ y, e.toList[i.1.toNat]? = some y → y.LiveAll p
  | _, _, .map m d, .key k p =>
    match lookupBy k m.toList with
    | some y => y.LiveAll p
    | none => d.LiveAll p

theorem SVal.liveAll_nil {T : Ty} (x : SVal T) : x.LiveAll .nil := by
  cases x <;> simp only [SVal.LiveAll]

theorem SVal.LiveAll.live : {T U : Ty} → {x : SVal T} → {p : Path T U} → x.LiveAll p →
    x.Live p
  | _, _, x, .nil, _ => SVal.live_nil x
  | _, _, .struct fs, .field h p, hl => by
    simp only [SVal.LiveAll] at hl; simp only [SVal.Live]; exact hl.live
  | _, _, .array e sh _, .at i p, hl => by
    simp only [SVal.LiveAll] at hl; simp only [SVal.Live]
    exact fun y hy => ⟨fun _ => hl.1, (hl.2 y hy).live⟩
  | _, _, .fixed e, .atF i p, hl => by
    simp only [SVal.LiveAll] at hl; simp only [SVal.Live]; exact fun y hy => (hl y hy).live
  | _, _, .map m d, .key k p, hl => by
    simp only [SVal.LiveAll] at hl; simp only [SVal.Live]
    split
    · rename_i y hy; simp only [hy] at hl; exact hl.live
    · rename_i hy; simp only [hy] at hl; exact hl.live

/-- Live along a path, then along what it finds. -/
theorem SVal.liveAll_append : {T R U : Ty} → (x : SVal T) → (p : Path T R) → (q : Path R U) →
    x.LiveAll p → (∀ y, x.findM p = some y → y.LiveAll q) → x.LiveAll (p.append q)
  | _, _, _, x, .nil, q, _, h => by rw [Path.append_nil]; exact h x (SVal.findM_nil' x)
  | _, _, _, .struct fs, .field hf p, q, hp, h => by
    rw [Path.append_field]
    simp only [SVal.LiveAll] at hp ⊢
    exact SVal.liveAll_append _ p q hp fun y hy => h y (by simp only [SVal.findM]; exact hy)
  | _, _, _, .array e sh _, .at i p, q, hp, h => by
    rw [Path.append_at]
    simp only [SVal.LiveAll] at hp ⊢
    refine ⟨hp.1, fun y hy => SVal.liveAll_append y p q (hp.2 y hy) fun z hz => h z ?_⟩
    simp only [SVal.findM, hy]; exact hz
  | _, _, _, .fixed e, .atF i p, q, hp, h => by
    rw [Path.append_atF]
    simp only [SVal.LiveAll] at hp ⊢
    exact fun y hy => SVal.liveAll_append y p q (hp y hy) fun z hz =>
      h z (by simp only [SVal.findM, hy]; exact hz)
  | _, _, _, .map m d, .key k p, q, hp, h => by
    rw [Path.append_key]
    simp only [SVal.LiveAll] at hp ⊢
    split
    · rename_i y hy
      simp only [hy] at hp
      exact SVal.liveAll_append y p q hp fun z hz => h z (by simp only [SVal.findM, hy]; exact hz)
    · rename_i hy
      simp only [hy] at hp
      exact SVal.liveAll_append d p q hp fun z hz => h z (by simp only [SVal.findM, hy]; exact hz)

/-! ## A save at live slots keeps the tails clean -/

/-- **A save keeps clean tails** where it enters every array at a live slot:
what lies past each end is left as it was. -/
theorem SVal.saveM_ct : {T U : Ty} → {x : SVal T} → (p : Path T U) → {new : SVal U} →
    {x' : SVal T} → x.All cleanTailH → new.All cleanTailH → x.LiveAll p →
    x.saveM p new = some x' → x'.All cleanTailH
  | _, _, x, .nil, new, x', _, hn, _, h => by
    cases x <;> (simp only [SVal.saveM, Option.some.injEq] at h; subst h; exact hn)
  | _, _, .struct fs, .field hf p, new, x', hx, hn, hl, h => by
    simp only [SVal.saveM, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨y, hy, rfl⟩ := h
    simp only [SVal.All] at hx ⊢
    simp only [SVal.LiveAll] at hl
    exact SFields.all_set hf hx (SVal.saveM_ct p (SFields.all_get hf hx) hn hl hy)
  | _, _, @SVal.array E n e sh _, .at i p, new, x', hx, hn, hl, h => by
    simp only [SVal.saveM] at h
    split at h
    · rename_i y hy
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨z, hz, rfl⟩ := h
      simp only [SVal.All] at hx ⊢
      simp only [SVal.LiveAll] at hl
      have hall : ∀ w ∈ e.toList ++ sh.toList, w.All cleanTailH := by
        intro w hw
        rcases List.mem_append.mp hw with hw | hw
        · exact SVec.all_iff.mp hx.2.1 w hw
        · exact SList.all_iff.mp hx.2.2 w hw
      have hzA := SVal.saveM_ct p (hall y (List.mem_of_getElem? hy)) hn (hl.2 y hy) hz
      have hset : ∀ w ∈ (e.toList ++ sh.toList).set i.1.toNat z, w.All cleanTailH := by
        intro w hw
        rcases List.mem_or_eq_of_mem_set hw with hw | hw
        · exact hall w hw
        · exact hw ▸ hzA
      have hdrop : ((e.toList ++ sh.toList).set i.1.toNat z).drop n = sh.toList := by
        rw [List.drop_set_of_lt hl.1]
        exact List.drop_left' (SVec.length_toList e)
      refine ⟨?_, SVec.all_ofList.mpr fun w hw => hset w (List.mem_of_mem_take hw),
        SList.all_ofList.mpr fun w hw => hset w (List.mem_of_mem_drop hw)⟩
      change (SList.ofList _).OrdinaryDefault
      rw [hdrop, SList.ordinaryDefault_ofList, ← SList.ordinaryDefault_iff]
      exact hx.1
    · exact nomatch h
  | _, _, .fixed e, .atF i p, new, x', hx, hn, hl, h => by
    simp only [SVal.saveM] at h
    split at h
    · rename_i y hy
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨z, hz, rfl⟩ := h
      simp only [SVal.All] at hx ⊢
      simp only [SVal.LiveAll] at hl
      have hzA := SVal.saveM_ct p
        (SVec.all_iff.mp hx.2 y (List.mem_of_getElem? hy)) hn (hl y hy) hz
      refine ⟨hx.1, SVec.all_iff.mpr fun w hw => ?_⟩
      rw [SVec.toList_set] at hw
      rcases List.mem_or_eq_of_mem_set hw with hw | hw
      · exact SVec.all_iff.mp hx.2 w hw
      · exact hw ▸ hzA
    · exact nomatch h
  | _, _, .map m d, .key k p, new, x', hx, hn, hl, h => by
    simp only [SVal.All] at hx
    simp only [SVal.LiveAll] at hl
    simp only [SVal.saveM] at h
    split at h
    · rename_i y hy
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨z, hz, rfl⟩ := h
      have hzA := SVal.saveM_ct p
        (SMap.all_iff.mp hx.2.1 (k, y) (lookupBy_eq_some_mem hy)) hn
        (by simpa only [hy] using hl) hz
      simp only [SVal.All]
      refine ⟨trivial, SMap.all_ofList.mpr fun e he => ?_, hx.2.2⟩
      rcases mem_setBy he with he | he
      · rw [he]; exact hzA
      · exact SMap.all_iff.mp hx.2.1 e he
    · rename_i hy
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨z, hz, rfl⟩ := h
      have hzA := SVal.saveM_ct p hx.2.2 hn (by simpa only [hy] using hl) hz
      simp only [SVal.All]
      refine ⟨trivial, SMap.all_ofList.mpr fun e he => ?_, hx.2.2⟩
      rcases mem_setBy he with he | he
      · rw [he]; exact hzA
      · exact SMap.all_iff.mp hx.2.1 e he

end Solidity
