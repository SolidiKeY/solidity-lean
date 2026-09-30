import Solidity.Calculus.UpdateRules

/-!
# The rewrites of a chain's line

Past the last statement a worked example keeps going, and so
does KeY: the stack of updates the program left merges into one parallel
update, the right-hand sides substituted, dead
captures go, the update is applied, and Theory laws read the terms down to
values:

    { se1 := 10 } { sp1 := alice.account } { storage := save(storage, sp1.balance, se1) } φ
      ⇝ { se1 := 10 ‖ sp1 := alice.account ‖ storage := save(storage, alice.account.balance, 10) } φ

None of these is a step of the strategy (`Fml.step`).  Each is here a
function on the whole line, computing the line after, with the one fact a
chain needs of it: wherever the line after holds, the line before does
(`LineRw`).  The semantics is `Calculus/UpdateRules.lean`'s and
`Calculus/TermRules.lean`'s; this module says *where* a rule acts.  A
function returns `none` where its rule does not fit or would change
nothing, so a link never repeats its line.

| `LineRw` | computes | line before ⇝ line after | sound by | the rule on `⊢` |
|---|---|---|---|---|
| `mergeAt i` | `Fml.mergeAt` | `{U}{V} ⇝ {U ‖ {U}V}`, `U` at `i` | `Upd.merge_holds` (iff) | `merge`, `mergeStorage` |
| `mergeSpine n` | `Fml.mergeSpine` | the first `n + 1` updates into one | `n` merges (iff) | — |
| `updRule r i` | `Fml.updRuleAt` | `simplifyUpdate`, `applySkip`, `applyOnRigid` | `UpdRule.sound` (iff) | `simplify` |
| `dropShadowed i` | `Fml.dropShadowedAt` | the elements a later one overwrites go | `Upd.dropShadowed_holds` (iff) | — |
| `applyOnRigidBox i` | `Fml.applyOnRigidBoxAt` | `[{U}] φ ⇝ φ[U]`, `φ` first-order | `Fml.subst_box(_st)` | `applyOnRigidBox` |
| `applyStorageBox i` | `Fml.applyStorageBoxAt` | `[{storage := s}] φ ⇝ φ[s/storage]` | `Fml.withSt_box` | `applyStorageBox` |
| `law h` | `Fml.rwLaw` | `t ⇝ t'` in every equation | `Fml.rwEq_holds` (iff) | `theoryRw` |
| `lawUpd h ht i` | `Fml.rwUpdAt` | `t ⇝ t'` in `[{Uᵢ}]`'s right-hand sides | `Upd.rw_box` | `updRw` |

KeY's names: the merges are `sequentialToParallel`, `dropShadowed` is
`simplifyUpdate` for the overwritten elements alone, the two `apply…Box`
are `applyOnRigidFormula`, and a law is the theory taclet it names.

**Where.**  A line is an update prefix, its *spine* `{U₀}{U₁}…{Uₙ} ψ`, over
a body `ψ`: a program still to run, or the postcondition.  A chain rewrites
the spine at a position, so the functions take one, `i` counted from the
outside (`Fml.atSpine` walks there); the innermost pair of three updates is
`mergeAt 1`.  The `⊢` rules act on the last update of the context; a chain's
line has no context, and names the position instead.  An update under a
connective (a branch's `c → {U} …`) is not reached: no worked trace merges
there.  A law acts where `Fml.rwEq` does — every equation, never `defined(…)`,
an update's right-hand side or a program — and `lawUpd` in one box update's
right-hand sides, where `t'` cannot halt (`Term.EvalRefines.of_theq`).

**What is looked at.**  A function looks at nothing below what it rewrites,
so a line over an opaque postcondition `φ` computes as far as its concrete
part goes, and a link on it is `rfl`.  The merges look at two updates, never
the body; `dropShadowed`, `applySkip` and `lawUpd` at one update.  The rules
whose premise is about the body read it: `simplifyUpdate` (the variables it
reads), `applyOnRigid` and the `apply…Box` (a first-order body), `law` (its
equations).

**The modality of an update.**  An update carries the modality it was
produced under, and merging `{U}_m {V}_m'` needs `m = m'`: a halting update
is true under the box and false under the diamond.  An update that cannot
halt (`Upd.total`: literals and paths of state variables, what the rules
capture) reads alike under both (`Upd.holds_total`), so a merge with one
takes the other's modality without comparing them.  That is what lets the
merges compute over a modality variable `m`; a merge of two updates
that may both halt compares `m' = m`, which a variable does not decide.  The
`…Box` rules and `lawUpd` are sound under the box only, and match `.box`.

**Merging, innermost first.**  `{U}{V}` merges when `U` writes only locals
(`Upd.envOnly`, substituted into `V`), or is one storage write over a `V`
whose storage reads are all `storage` terms (`withSt`).  So
`{a := t ‖ storage := S}{x := u}` does not merge (a parallel update of locals
and the storage over another is KeY's general case, whose substitution is
simultaneous), but inside out every merge of a stack the program leaves is
one of the two: `{storage := S}{x := u}` first, then `{a := t}` into the
result.  `Fml.mergeSpine` merges that way.  It takes the count from the
chain: whether the body is one more update is a question about the body.
-/

namespace Solidity

open Semantics

variable {C : Contract}

/-! ## What a chain needs of a rewrite -/

/-- A rewrite of a chain's line: the line after, computed (`apply`), and why
the line before follows from it (`sound`).  A link `φ ⇝ ψ` by `r` is
`r.apply φ = some ψ`, proved by `rfl` on a line whose rewritten part is
concrete. -/
structure LineRw (C : Contract) where
  /-- The line after, or `none` where the rule does not fit. -/
  apply : Fml C → Option (Fml C)
  /-- Wherever the line after holds, the line before does. -/
  sound : ∀ {φ ψ : Fml C}, apply φ = some ψ → ∀ σ, holds σ ψ → holds σ φ

/-- A line rewritten to a valid one is valid. -/
theorem LineRw.valid (r : LineRw C) {φ ψ : Fml C} (h : r.apply φ = some ψ) (hψ : Valid ψ) :
    Valid φ :=
  fun σ => r.sound h σ (hψ σ)

/-- A postcondition that follows from another after the same run:
`{ x := 1 } (y ≐ 1)` gives `{ x := 1 } true`. -/
theorem Modality.after_mono (m : Modality) {p q : State → Prop} (h : ∀ τ, p τ → q τ) :
    (r : Res State) → m.after p r → m.after q r
  | .ok τ, hp => h τ hp
  | .error _, hp => hp

/-! ## A position on the spine -/

/-- `f` on the update at position `i` of the spine, `0` the outermost:
`f m U φ` rewrites `{U}_m φ`.  The updates above it stay; nothing below
`{U} φ` is looked at but what `f` looks at. -/
def Fml.atSpine (f : Modality → Upd C → Fml C → Option (Fml C)) : Nat → Fml C → Option (Fml C)
  | 0, .upd m U φ => f m U φ
  | i + 1, .upd m U φ => (φ.atSpine f i).map (.upd m U)
  | _, _ => none

/-- A rewrite of one update, one direction, is one of the line. -/
theorem Fml.atSpine_sound {f : Modality → Upd C → Fml C → Option (Fml C)}
    (hf : ∀ {m U φ ψ}, f m U φ = some ψ → ∀ σ, holds σ ψ → holds σ (.upd m U φ)) :
    (i : Nat) → (φ : Fml C) → ∀ {ψ : Fml C}, φ.atSpine f i = some ψ → ∀ σ, holds σ ψ → holds σ φ
  | 0, .upd m U φ, _, h, σ, hψ => hf h σ hψ
  | i + 1, .upd m U φ, _, h, σ, hψ => by
    simp only [Fml.atSpine, Option.map_eq_some_iff] at h
    obtain ⟨φ', h', rfl⟩ := h
    exact m.after_mono (fun τ => Fml.atSpine_sound hf i φ h' τ) _ hψ
  | 0, .tt, _, h, _, _ | 0, .eq .., _, h, _, _ | 0, .defined _, _, h, _, _
  | 0, .not _, _, h, _, _ | 0, .and .., _, h, _, _ | 0, .imp .., _, h, _, _
  | 0, .modal .., _, h, _, _ | 0, .havoc _, _, h, _, _ | 0, .all .., _, h, _, _
  | _ + 1, .tt, _, h, _, _ | _ + 1, .eq .., _, h, _, _ | _ + 1, .defined _, _, h, _, _
  | _ + 1, .not _, _, h, _, _ | _ + 1, .and .., _, h, _, _ | _ + 1, .imp .., _, h, _, _
  | _ + 1, .modal .., _, h, _, _ | _ + 1, .havoc _, _, h, _, _ | _ + 1, .all .., _, h, _, _ =>
    nomatch h

/-- A rewrite of one update that is an equivalence is one of the line. -/
theorem Fml.atSpine_holds {f : Modality → Upd C → Fml C → Option (Fml C)}
    (hf : ∀ {m U φ ψ}, f m U φ = some ψ → ∀ σ, (holds σ ψ ↔ holds σ (.upd m U φ))) :
    (i : Nat) → (φ : Fml C) → ∀ {ψ : Fml C}, φ.atSpine f i = some ψ → ∀ σ, (holds σ ψ ↔ holds σ φ)
  | 0, .upd m U φ, _, h, σ => hf h σ
  | i + 1, .upd m U φ, _, h, σ => by
    simp only [Fml.atSpine, Option.map_eq_some_iff] at h
    obtain ⟨φ', h', rfl⟩ := h
    exact m.after_congr (fun τ => Fml.atSpine_holds hf i φ h' τ) _
  | 0, .tt, _, h, _ | 0, .eq .., _, h, _ | 0, .defined _, _, h, _
  | 0, .not _, _, h, _ | 0, .and .., _, h, _ | 0, .imp .., _, h, _
  | 0, .modal .., _, h, _ | 0, .havoc _, _, h, _ | 0, .all .., _, h, _
  | _ + 1, .tt, _, h, _ | _ + 1, .eq .., _, h, _ | _ + 1, .defined _, _, h, _
  | _ + 1, .not _, _, h, _ | _ + 1, .and .., _, h, _ | _ + 1, .imp .., _, h, _
  | _ + 1, .modal .., _, h, _ | _ + 1, .havoc _, _, h, _ | _ + 1, .all .., _, h, _ =>
    nomatch h

/-! ## `sequentialToParallel` -/

/-- An update that cannot halt reads alike under either modality:
`{ se1 := 10 } φ` under the box is `{ se1 := 10 } φ` under the diamond. -/
theorem Upd.holds_total {U : Upd C} (hU : U.total = true) (m m' : Modality) (φ : Fml C)
    (σ : State) : holds σ (.upd m U φ) ↔ holds σ (.upd m' U φ) := by
  obtain ⟨τ, hτ⟩ := Upd.foldl_total σ U hU σ
  simp only [holds, Upd.apply, hτ, Modality.after]

/-- `{U}_m {V}_m'` as one parallel update and its modality, if a rule merges
them: `U` of locals substituted into `V`, or `U` one storage write
substituted for `V`'s `storage`.  The two modalities are compared only when
neither update can stand for the other's: `{ se1 := 10 }` cannot halt, so it
merges under any `m'`. -/
def Upd.merge (m : Modality) (U : Upd C) (m' : Modality) (V : Upd C) :
    Option (Modality × Upd C) :=
  if (U.envOnly && (U.total || decide (m' = m))) = true then some (m', U ++ V.subst U)
  else match U with
    | [.storage s] =>
      if (V.all (·.stExplicit) && (V.total || decide (m' = m))) = true then
        some (m, .storage s :: V.withSt s)
      else none
    | _ => none

/-- **`sequentialToParallel`**: the merged update holds exactly where the
two did.

Example: `{ sp1 := alice.account } { storage := save(storage, sp1.balance, se1) }`
merges to `{ sp1 := alice.account ‖ storage := save(storage, alice.account.balance, se1) }`. -/
theorem Upd.merge_holds {m m' m'' : Modality} {U V W : Upd C}
    (h : Upd.merge m U m' V = some (m'', W)) (φ : Fml C) (σ : State) :
    holds σ (.upd m'' W φ) ↔ holds σ (.upd m U (.upd m' V φ)) := by
  unfold Upd.merge at h
  split at h
  · rename_i hc
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hc
    rw [(UpdRule.sequentialToParallel (m := m') (V := V) (φ := φ) hc.1).sound σ]
    rcases hc.2 with ht | rfl
    · exact Upd.holds_total ht m' m _ σ
    · exact Iff.rfl
  · split at h
    · split at h
      · rename_i s _ hc
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hc
        rw [Upd.mergeStorage_holds m s V hc.1 φ σ]
        simp only [holds]
        refine m.after_congr (fun τ => ?_) _
        rcases hc.2 with ht | rfl
        · exact Upd.holds_total ht m m' φ τ
        · exact Iff.rfl
      · nomatch h
    · nomatch h

/-- `{U}_m φ` merged with the update at the head of `φ`. -/
def Fml.mergeInto (m : Modality) (U : Upd C) : Fml C → Option (Fml C)
  | .upd m' V φ => (Upd.merge m U m' V).map fun r => .upd r.1 r.2 φ
  | _ => none

theorem Fml.mergeInto_holds {m : Modality} {U : Upd C} {φ ψ : Fml C}
    (h : Fml.mergeInto m U φ = some ψ) (σ : State) : holds σ ψ ↔ holds σ (.upd m U φ) := by
  cases φ with
  | upd m' V χ =>
    simp only [Fml.mergeInto, Option.map_eq_some_iff] at h
    obtain ⟨⟨m'', W⟩, hw, rfl⟩ := h
    exact Upd.merge_holds hw χ σ
  | _ => nomatch h

/-- `sequentialToParallel` on the updates at positions `i` and `i + 1`. -/
def Fml.mergeAt (i : Nat) : Fml C → Option (Fml C) := Fml.atSpine Fml.mergeInto i

theorem Fml.mergeAt_holds {i : Nat} {φ ψ : Fml C} (h : φ.mergeAt i = some ψ) (σ : State) :
    holds σ ψ ↔ holds σ φ :=
  Fml.atSpine_holds (fun h σ => Fml.mergeInto_holds h σ) i φ h σ

/-- The first `n + 1` updates of the spine merged into one, the innermost
pair first: `sequentialToParallel` `n` times, as a chain's last line
shows it.  `none` unless every pair merges, and for `n = 0`, which would
merge nothing. -/
def Fml.mergeSpine : Nat → Fml C → Option (Fml C)
  | 1, .upd m U φ => Fml.mergeInto m U φ
  | n + 2, .upd m U φ => (φ.mergeSpine (n + 1)).bind (Fml.mergeInto m U)
  | _, _ => none

theorem Fml.mergeSpine_holds :
    (n : Nat) → (φ : Fml C) → ∀ {ψ : Fml C}, φ.mergeSpine n = some ψ → ∀ σ, (holds σ ψ ↔ holds σ φ)
  | 1, .upd m U φ, _, h, σ => Fml.mergeInto_holds h σ
  | n + 2, .upd m U φ, _, h, σ => by
    simp only [Fml.mergeSpine, Option.bind_eq_some_iff] at h
    obtain ⟨χ, hχ, h⟩ := h
    rw [Fml.mergeInto_holds h σ]
    simp only [holds]
    exact m.after_congr (fun τ => Fml.mergeSpine_holds (n + 1) φ hχ τ) _
  | 0, _, _, h, _ => nomatch h
  | 1, .tt, _, h, _ | 1, .eq .., _, h, _ | 1, .defined _, _, h, _
  | 1, .not _, _, h, _ | 1, .and .., _, h, _ | 1, .imp .., _, h, _
  | 1, .modal .., _, h, _ | 1, .havoc _, _, h, _ | 1, .all .., _, h, _
  | _ + 2, .tt, _, h, _ | _ + 2, .eq .., _, h, _ | _ + 2, .defined _, _, h, _
  | _ + 2, .not _, _, h, _ | _ + 2, .and .., _, h, _ | _ + 2, .imp .., _, h, _
  | _ + 2, .modal .., _, h, _ | _ + 2, .havoc _, _, h, _ | _ + 2, .all .., _, h, _ =>
    nomatch h

/-- An update rule (`UpdRuleName.top`) on the update at position `i`:
`simplifyUpdate`, `applySkip`, `applyOnRigid`, each an equivalence.  (Its
`sequentialToParallel` is `Fml.mergeAt`'s without the storage write.) -/
def Fml.updRuleAt (r : UpdRuleName) (i : Nat) : Fml C → Option (Fml C) := Fml.atSpine r.top i

theorem Fml.updRuleAt_holds {r : UpdRuleName} {i : Nat} {φ ψ : Fml C} (h : φ.updRuleAt r i = some ψ)
    (σ : State) : holds σ ψ ↔ holds σ φ :=
  Fml.atSpine_holds (fun h σ => (UpdRuleName.top_rule h).sound σ) i φ h σ

/-! ## `simplifyUpdate` without the body

`simplifyUpdate` drops an element that cannot halt when the formula under
the update does not read its variable, or a later element writes it again.
The second needs nothing of the formula: an overwritten element is dropped
under any body (KeY's `\dropEffectlessElementaries` with every variable
read). -/

/-- The update without the elements a later element overwrites. -/
def Upd.dropShadowed (U : Upd C) : Upd C := U.dropEffectless U.targets

/-- Dropping an overwritten element changes no binding.

Example: `{ acc := alice.account ‖ acc := bob.account }` binds what
`{ acc := bob.account }` binds. -/
theorem Upd.dropShadowed_holds (m : Modality) (U : Upd C) (φ : Fml C) (σ : State) :
    holds σ (.upd m U.dropShadowed φ) ↔ holds σ (.upd m U φ) :=
  m.after_frame (Upd.dropEffectless_apply U.targets U σ) fun _ _ h =>
    holds_frame φ (fun x _ hG => by
      obtain ⟨hx, hn⟩ := List.mem_filter.1 hG
      simp only [decide_eq_true_eq] at hn
      exact hn hx) h

/-- The overwritten elements of `{U}_m φ` dropped, if there is one. -/
def Fml.dropShadowedTop (m : Modality) (U : Upd C) (φ : Fml C) : Option (Fml C) :=
  if U.dropShadowed.length < U.length then some (.upd m U.dropShadowed φ) else none

/-- The overwritten elements of the update at position `i` dropped. -/
def Fml.dropShadowedAt (i : Nat) : Fml C → Option (Fml C) := Fml.atSpine Fml.dropShadowedTop i

theorem Fml.dropShadowedAt_holds {i : Nat} {φ ψ : Fml C} (h : φ.dropShadowedAt i = some ψ)
    (σ : State) : holds σ ψ ↔ holds σ φ :=
  Fml.atSpine_holds (fun h σ => by
    unfold Fml.dropShadowedTop at h
    split at h
    · cases h; exact Upd.dropShadowed_holds _ _ _ σ
    · nomatch h) i φ h σ

/-! ## An update applied to the body, under the box -/

/-- `applyOnRigidFormula` under the box (`Proves.applyOnRigidBox`): `[{U}] φ ⇝ φ[U]`
for a first-order `φ`, `U` of locals, or of locals and storage writes under a
`φ` that reads no storage. -/
def Fml.applyOnRigidBoxTop : Modality → Upd C → Fml C → Option (Fml C)
  | .box, U, φ =>
    if ((U.envOnly || U.localsOrStorage && φ.stFree) && φ.rigid && φ.sortedFor U) = true then
      some (φ.subst U)
    else none
  | .diamond, _, _ => none

theorem Fml.applyOnRigidBoxTop_sound {m : Modality} {U : Upd C} {φ ψ : Fml C}
    (h : Fml.applyOnRigidBoxTop m U φ = some ψ) (σ : State) (hψ : holds σ ψ) :
    holds σ (.upd m U φ) := by
  cases m with
  | diamond => nomatch h
  | box =>
    simp only [Fml.applyOnRigidBoxTop] at h
    split at h
    · rename_i hc
      cases h
      simp only [Bool.and_eq_true] at hc
      obtain ⟨⟨hU, hr⟩, hs⟩ := hc
      rcases Bool.or_eq_true_iff.1 hU with hU | hU
      · exact Fml.subst_box hU hr hs σ hψ
      · simp only [Bool.and_eq_true] at hU
        exact Fml.subst_box_st hU.1 hU.2 hs σ hψ
    · nomatch h

/-- `applyOnRigidFormula` on the box update at position `i`. -/
def Fml.applyOnRigidBoxAt (i : Nat) : Fml C → Option (Fml C) := Fml.atSpine Fml.applyOnRigidBoxTop i

/-- `applyOnRigidFormula` for a storage write under the box
(`Proves.applyStorageBox`): `[{storage := s}] φ ⇝ φ[s/storage]`. -/
def Fml.applyStorageBoxTop : Modality → Upd C → Fml C → Option (Fml C)
  | .box, [.storage s], φ => if (φ.rigid && φ.stExplicit) = true then some (φ.withSt s) else none
  | _, _, _ => none

theorem Fml.applyStorageBoxTop_sound {m : Modality} {U : Upd C} {φ ψ : Fml C}
    (h : Fml.applyStorageBoxTop m U φ = some ψ) (σ : State) (hψ : holds σ ψ) :
    holds σ (.upd m U φ) := by
  unfold Fml.applyStorageBoxTop at h
  split at h
  · split at h
    · rename_i hc
      cases h
      simp only [Bool.and_eq_true] at hc
      exact Fml.withSt_box hc.1 hc.2 σ hψ
    · nomatch h
  · nomatch h

/-- `applyOnRigidFormula` on the box storage write at position `i`. -/
def Fml.applyStorageBoxAt (i : Nat) : Fml C → Option (Fml C) := Fml.atSpine Fml.applyStorageBoxTop i

/-! ## Theory laws

A law `h : Term.Theq t t'` rewrites `t` to `t'` where `Fml.rwEq` does: in
every equation, at any depth, never in `defined(…)`, an update's
right-hand side or a program (`Calculus/TermRules.lean` says why).  In the
right-hand sides of a box update it rewrites too when `t'` cannot halt
(`Term.EvalRefines.of_theq`), one update at a time:
`{ … ‖ v := find(save(S, p, 10), p) } ⇝ { … ‖ v := 10 }`. -/

/-- Some equation of the formula changes under the rewrite. -/
def Fml.eqRewrites (q : Term C × Term C) : Fml C → Bool
  | .eq a b => a.rw q != a || b.rw q != b
  | .not φ | .upd _ _ φ | .modal _ _ φ | .havoc φ | .all _ _ φ => φ.eqRewrites q
  | .and φ ψ | .imp φ ψ => φ.eqRewrites q || ψ.eqRewrites q
  | .tt | .defined _ => false

/-- The law `q.1 ≐ q.2` on every equation of the line, if it rewrites one. -/
def Fml.rwLaw (q : Term C × Term C) (φ : Fml C) : Option (Fml C) :=
  if φ.eqRewrites q = true then some (φ.rwEq q) else none

theorem Fml.rwLaw_holds {q : Term C × Term C} (h : Term.Theq q.1 q.2) {φ ψ : Fml C}
    (hl : φ.rwLaw q = some ψ) (σ : State) : holds σ ψ ↔ holds σ φ := by
  unfold Fml.rwLaw at hl
  split at hl
  · cases hl; exact Fml.rwEq_holds h φ σ
  · nomatch hl

deriving instance DecidableEq for UpdElem

/-- The law on the right-hand sides of `[{U}] φ` (`Proves.updRw`), if it
rewrites one. -/
def Fml.rwUpdTop (q : Term C × Term C) : Modality → Upd C → Fml C → Option (Fml C)
  | .box, U, φ => if (U.rw q != U) = true then some (.upd .box (U.rw q) φ) else none
  | .diamond, _, _ => none

theorem Fml.rwUpdTop_sound {q : Term C × Term C} (hq : Term.EvalRefines q.1 q.2) {m : Modality}
    {U : Upd C} {φ ψ : Fml C} (h : Fml.rwUpdTop q m U φ = some ψ) (σ : State)
    (hψ : holds σ ψ) : holds σ (.upd m U φ) := by
  cases m with
  | diamond => nomatch h
  | box =>
    simp only [Fml.rwUpdTop] at h
    split at h
    · cases h; exact Upd.rw_box hq (fun _ h => h) σ hψ
    · nomatch h

/-- The law on the right-hand sides of the box update at position `i`. -/
def Fml.rwUpdAt (q : Term C × Term C) (i : Nat) : Fml C → Option (Fml C) :=
  Fml.atSpine (Fml.rwUpdTop q) i

/-! ## The rewrites, bundled -/

namespace LineRw

/-- `sequentialToParallel` on the updates at positions `i` and `i + 1`. -/
def mergeAt (i : Nat) : LineRw C := ⟨Fml.mergeAt i, fun h σ => (Fml.mergeAt_holds h σ).1⟩

/-- `sequentialToParallel` on the first `n + 1` updates, the innermost pair first. -/
def mergeSpine (n : Nat) : LineRw C :=
  ⟨Fml.mergeSpine n, fun h σ => (Fml.mergeSpine_holds n _ h σ).1⟩

/-- An update rule at position `i`: `simplifyUpdate`, `applySkip`, `applyOnRigid`. -/
def updRule (r : UpdRuleName) (i : Nat) : LineRw C :=
  ⟨Fml.updRuleAt r i, fun h σ => (Fml.updRuleAt_holds h σ).1⟩

/-- The overwritten elements of the update at position `i` dropped. -/
def dropShadowed (i : Nat) : LineRw C :=
  ⟨Fml.dropShadowedAt i, fun h σ => (Fml.dropShadowedAt_holds h σ).1⟩

/-- `applyOnRigidFormula` on the box update at position `i`. -/
def applyOnRigidBox (i : Nat) : LineRw C :=
  ⟨Fml.applyOnRigidBoxAt i, Fml.atSpine_sound Fml.applyOnRigidBoxTop_sound i _⟩

/-- `applyOnRigidFormula` on the box storage write at position `i`. -/
def applyStorageBox (i : Nat) : LineRw C :=
  ⟨Fml.applyStorageBoxAt i, Fml.atSpine_sound Fml.applyStorageBoxTop_sound i _⟩

/-- The law `h` on every equation of the line. -/
def law {t t' : Term C} (h : Term.Theq t t') : LineRw C :=
  ⟨Fml.rwLaw (t, t'), fun hl σ => (Fml.rwLaw_holds h hl σ).1⟩

/-- The law `h`, onto a term that cannot halt, on the right-hand sides of the
box update at position `i`. -/
def lawUpd {t t' : Term C} (h : Term.Theq t t') (ht : t'.total = true) (i : Nat) : LineRw C :=
  ⟨Fml.rwUpdAt (t, t') i,
    Fml.atSpine_sound (Fml.rwUpdTop_sound (Term.EvalRefines.of_theq h ht)) i _⟩

end LineRw

end Solidity
