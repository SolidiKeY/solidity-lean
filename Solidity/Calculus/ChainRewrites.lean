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
| `updRule r i` | `Fml.updRuleAt` | `applySkip`, `applyOnRigid` | `UpdRule.sound` (iff) | `simplify` |
| `simplify i` | `Fml.simplifyAt` | the elements `ψ` does not read, or a later one overwrites, go | `Upd.dropEffectless_holds_of` (iff) | `simplify` |
| `simplifyFresh i` | `Fml.simplifyFreshAt` | the same, `ψ` asked its fresh variables only | `Upd.dropEffectless_holds_of` (iff) | — |
| `applyOnRigidBox i` | `Fml.applyOnRigidBoxAt` | `[{U}] φ ⇝ φ[U]`, `φ` first-order; any modality if `U` cannot halt | `Fml.subst_box(_st)` | `applyOnRigidBox` |
| `applyStorageBox i` | `Fml.applyStorageBoxAt` | `[{storage := s}] φ ⇝ φ[s/storage]` | `Fml.withSt_box` | `applyStorageBox` |
| `law h` | `Fml.rwLaw` | `t ⇝ t'` in every equation | `Fml.rwEq_holds` (iff) | `theoryRw` |
| `lawUpd h ht i` | `Fml.rwUpdAt` | `t ⇝ t'` in `[{Uᵢ}]`'s right-hand sides | `Upd.rw_box` | `updRw` |

KeY's names: the merges are `sequentialToParallel`, the two `simplify…` are
`simplifyUpdate` (with `applySkip` when they empty the update), the two
`apply…Box` are `applyOnRigidFormula`, and a law is the theory taclet it
names.

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
the body; `applySkip` and `lawUpd` at one update.  The rules whose premise
is about the body read it: `simplify` (the variables it reads),
`applyOnRigid` and the `apply…Box` (a first-order body), `law` (its
equations).  `simplifyFresh` reads only the body's fresh variables, which a
postcondition `φ : Post C` has none of: over `φ` it computes by `simp` from
`Post.noFresh`, not by `rfl` (`Chain.proveRw`, `Calculus/Chains.lean`).

**The modality of an update.**  An update carries the modality it was
produced under, and merging `{U}_m {V}_m'` needs `m = m'`: a halting update
is true under the box and false under the diamond.  An update that cannot
halt (`Upd.total`: literals and paths of state variables, what the rules
capture) reads alike under both (`Upd.holds_total`), so a merge with one
takes the other's modality without comparing them.  That is what lets the
merges compute over a modality variable `m`; a merge of two updates
that may both halt compares `m' = m`, which a variable does not decide.  The
same holds of `applyOnRigidBox`: under the box, or where `U` cannot halt.
`applyStorageBox` and `lawUpd` are the box's only, since a storage write and
a right-hand side a law rewrites can halt; they match `.box`.

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
  | 0, φ, _, h, σ, hψ => by
    cases φ with
    | upd m U φ => exact hf h σ hψ
    | _ => nomatch h
  | i + 1, φ, _, h, σ, hψ => by
    cases φ with
    | upd m U φ =>
      simp only [Fml.atSpine, Option.map_eq_some_iff] at h
      obtain ⟨φ', h', rfl⟩ := h
      exact m.after_mono (fun τ => Fml.atSpine_sound hf i φ h' τ) _ hψ
    | _ => nomatch h

/-- A rewrite of one update that is an equivalence is one of the line. -/
theorem Fml.atSpine_holds {f : Modality → Upd C → Fml C → Option (Fml C)}
    (hf : ∀ {m U φ ψ}, f m U φ = some ψ → ∀ σ, (holds σ ψ ↔ holds σ (.upd m U φ))) :
    (i : Nat) → (φ : Fml C) → ∀ {ψ : Fml C}, φ.atSpine f i = some ψ → ∀ σ, (holds σ ψ ↔ holds σ φ)
  | 0, φ, _, h, σ => by
    cases φ with
    | upd m U φ => exact hf h σ
    | _ => nomatch h
  | i + 1, φ, _, h, σ => by
    cases φ with
    | upd m U φ =>
      simp only [Fml.atSpine, Option.map_eq_some_iff] at h
      obtain ⟨φ', h', rfl⟩ := h
      exact m.after_congr (fun τ => Fml.atSpine_holds hf i φ h' τ) _
    | _ => nomatch h

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
  | 0, _, _, h, _ => nomatch h
  | 1, φ, _, h, σ => by
    cases φ with
    | upd m U φ => exact Fml.mergeInto_holds h σ
    | _ => nomatch h
  | n + 2, φ, _, h, σ => by
    cases φ with
    | upd m U φ =>
      simp only [Fml.mergeSpine, Option.bind_eq_some_iff] at h
      obtain ⟨χ, hχ, h⟩ := h
      rw [Fml.mergeInto_holds h σ]
      simp only [holds]
      exact m.after_congr (fun τ => Fml.mergeSpine_holds (n + 1) φ hχ τ) _
    | _ => nomatch h

/-- An update rule (`UpdRuleName.top`) on the update at position `i`:
`applySkip`, `applyOnRigid`, each an equivalence.  `sequentialToParallel`
and `simplifyUpdate` give `none`: those rules are `Fml.mergeAt` (and
`Fml.mergeSpine`), which also merges a storage write and compares no
modality where an update cannot halt, and `Fml.simplifyAt` (and
`Fml.simplifyFreshAt`), which also drops the update it empties, so a link
labelled with one has one spelling. -/
def Fml.updRuleAt : UpdRuleName → Nat → Fml C → Option (Fml C)
  | .sequentialToParallel, _, _ | .simplifyUpdate, _, _ => none
  | .applySkip, i, φ => Fml.atSpine UpdRuleName.applySkip.top i φ
  | .applyOnRigid, i, φ => Fml.atSpine UpdRuleName.applyOnRigid.top i φ

theorem Fml.updRuleAt_holds {r : UpdRuleName} {i : Nat} {φ ψ : Fml C} (h : φ.updRuleAt r i = some ψ)
    (σ : State) : holds σ ψ ↔ holds σ φ := by
  have top : ∀ (r : UpdRuleName), φ.atSpine r.top i = some ψ → (holds σ ψ ↔ holds σ φ) :=
    fun _ h => Fml.atSpine_holds (fun h σ => (UpdRuleName.top_rule h).sound σ) i φ h σ
  cases r with
  | sequentialToParallel | simplifyUpdate => nomatch h
  | applySkip => exact top _ h
  | applyOnRigid => exact top _ h

/-! ## `simplifyUpdate`

`simplifyUpdate` drops an element that cannot halt when the formula under
the update does not read its variable, or a later element writes it again;
an update it empties goes too (`applySkip`), since `dl!{}` has no spelling
for KeY's `skip`.  What the formula reads is asked of the update's own
variables only (`Upd.dropEffectless_holds_of`): any list `F` that holds
every one the formula reads will do, and the fewer it holds the more goes.

* `Fml.simplifyAt` reads the formula's variables, as KeY's
  `\dropEffectlessElementaries` does: `{ x := 10 ‖ y := 1 } y ≐ 1 ⇝ { y := 1 } y ≐ 1`.
* `Fml.simplifyFreshAt` reads only its *fresh* variables (`Fml.freshVars`),
  and counts every user variable the update writes as read.  A postcondition
  `φ : Post C` names no fresh variable, so over `φ` a capture of the rules
  (`se1`, `pv`) goes, and the rewrite computes from `Post.noFresh` rather than
  by `rfl` (`Chain.proveRw`): `{ pv := 10 ‖ acc := alice.account ‖
  storage := S } φ ⇝ { storage := S } φ`.  An overwritten element goes too,
  whatever it writes: `{ acc := alice.account ‖ acc := bob.account } φ`
  keeps the second. -/

/-- The fresh variables a formula mentions (`Var.idx` not `0`), taken apart
connective by connective, so that a postcondition's are asked of it alone
(`Post.freshVars_eq_nil`). -/
def Fml.freshVars : Fml C → List Var
  | .tt => []
  | .eq a b => (a.vars ++ b.vars).filter (·.idx != 0)
  | .defined t => t.vars.filter (·.idx != 0)
  | .not φ | .havoc φ => φ.freshVars
  | .and φ ψ | .imp φ ψ => φ.freshVars ++ ψ.freshVars
  | .upd _ U φ => U.vars.filter (·.idx != 0) ++ φ.freshVars
  | .modal _ P φ => (Prog.vars P).filter (·.idx != 0) ++ φ.freshVars
  | .all x _ φ => [x].filter (·.idx != 0) ++ φ.freshVars

theorem Fml.freshVars_eq : (φ : Fml C) → φ.freshVars = φ.vars.filter (·.idx != 0)
  | .tt | .eq .. | .defined _ => rfl
  | .not φ | .havoc φ => Fml.freshVars_eq φ
  | .and φ ψ | .imp φ ψ => by
    simp only [Fml.freshVars, Fml.vars, List.filter_append, Fml.freshVars_eq φ, Fml.freshVars_eq ψ]
  | .upd _ _ φ | .modal _ _ φ => by
    simp only [Fml.freshVars, Fml.vars, List.filter_append, Fml.freshVars_eq φ]
  | .all x _ φ => by
    simp only [Fml.freshVars, Fml.vars, Fml.freshVars_eq φ, ← List.filter_append, List.singleton_append]

/-- Dropping the effectless elements, reading `F` for what the formula
reads, changes no binding the formula sees, if `F` holds every variable of
the update the formula reads. -/
theorem Upd.dropEffectless_holds_of {F : List Var} {U : Upd C} {φ : Fml C}
    (hF : ∀ x ∈ φ.vars, x ∈ U.targets → x ∈ F) (m : Modality) (σ : State) :
    holds σ (.upd m (U.dropEffectless F) φ) ↔ holds σ (.upd m U φ) :=
  m.after_frame (Upd.dropEffectless_apply F U σ) fun _ _ h =>
    holds_frame φ (fun x hx hG => by
      obtain ⟨hU, hn⟩ := List.mem_filter.1 hG
      simp only [decide_eq_true_eq] at hn
      exact hn (hF x hx hU)) h

/-- `{U}_m φ` with its effectless elements dropped, `F` read for what `φ`
reads, and the update with them if none is left; `none` if none goes. -/
def Fml.simplifyWith (F : List Var) (m : Modality) (U : Upd C) (φ : Fml C) : Option (Fml C) :=
  if (U.dropEffectless F).length < U.length then
    some (match U.dropEffectless F with
      | [] => φ
      | V => .upd m V φ)
  else none

theorem Fml.simplifyWith_holds {F : List Var} {m : Modality} {U : Upd C} {φ ψ : Fml C}
    (hF : ∀ x ∈ φ.vars, x ∈ U.targets → x ∈ F) (h : Fml.simplifyWith F m U φ = some ψ)
    (σ : State) : holds σ ψ ↔ holds σ (.upd m U φ) := by
  unfold Fml.simplifyWith at h
  split at h
  · cases h
    rw [← Upd.dropEffectless_holds_of hF m σ]
    split
    · rename_i hV
      rw [hV]
      exact Iff.rfl
    · exact Iff.rfl
  · nomatch h

/-- `simplifyUpdate` on `{U}_m φ`, reading `φ`'s variables. -/
def Fml.simplifyTop (m : Modality) (U : Upd C) (φ : Fml C) : Option (Fml C) :=
  Fml.simplifyWith φ.vars m U φ

/-- `simplifyUpdate` on `{U}_m φ`, reading `φ`'s fresh variables, and every
user variable `U` writes. -/
def Fml.simplifyFreshTop (m : Modality) (U : Upd C) (φ : Fml C) : Option (Fml C) :=
  Fml.simplifyWith (φ.freshVars ++ U.targets.filter (·.idx == 0)) m U φ

theorem Fml.simplifyFreshTop_holds {m : Modality} {U : Upd C} {φ ψ : Fml C}
    (h : Fml.simplifyFreshTop m U φ = some ψ) (σ : State) : holds σ ψ ↔ holds σ (.upd m U φ) :=
  Fml.simplifyWith_holds (fun x hx hU => by
    rw [List.mem_append, Fml.freshVars_eq, List.mem_filter, List.mem_filter]
    by_cases h0 : x.idx = 0
    · exact .inr ⟨hU, by simp only [h0, BEq.rfl]⟩
    · exact .inl ⟨hx, by simp only [h0, bne_iff_ne, ne_eq, not_false_eq_true]⟩) h σ

/-- `simplifyUpdate` on the update at position `i`, reading the formula's variables. -/
def Fml.simplifyAt (i : Nat) : Fml C → Option (Fml C) := Fml.atSpine Fml.simplifyTop i

/-- `simplifyUpdate` on the update at position `i`, reading the formula's
fresh variables: it computes over a postcondition `φ : Post C`. -/
def Fml.simplifyFreshAt (i : Nat) : Fml C → Option (Fml C) := Fml.atSpine Fml.simplifyFreshTop i

/-! ## An update applied to the body, under the box

`[{U}] φ ⇝ φ[U]` holds where `U` halts because the box does, so these rules
are the box's.  Under the diamond an update that cannot halt reads as under
the box (`Upd.holds_total`), so `applyOnRigidBox` applies there too, and at
a modality variable `m`: it asks `U.total || m = .box`, which a total `U`
decides without `m`, as the merges do.  A storage write is never total (its
path may be missing), and neither is an update whose right-hand side a law
rewrites (`find(save(…), p)` halts where `p` does not resolve), so
`applyStorageBox` and `lawUpd` stay the box's. -/

/-- A line under the box gives it under `m` where `m` is the box or `U`
cannot halt. -/
theorem Fml.upd_of_box {m : Modality} {U : Upd C} {φ : Fml C} (hm : U.total = true ∨ m = .box)
    {σ : State} (h : holds σ (.upd .box U φ)) : holds σ (.upd m U φ) := by
  rcases hm with hU | rfl
  · exact (Upd.holds_total hU .box m φ σ).1 h
  · exact h

/-- `applyOnRigidFormula` under the box (`Proves.applyOnRigidBox`): `[{U}] φ ⇝ φ[U]`
for a first-order `φ`, `U` of locals, or of locals and storage writes under a
`φ` that reads no storage; under any modality where `U` cannot halt. -/
def Fml.applyOnRigidBoxTop (m : Modality) (U : Upd C) (φ : Fml C) : Option (Fml C) :=
  if ((U.total || decide (m = .box)) && (U.envOnly || U.localsOrStorage && φ.stFree) &&
      φ.rigid && φ.sortedFor U) = true then
    some (φ.subst U)
  else none

theorem Fml.applyOnRigidBoxTop_sound {m : Modality} {U : Upd C} {φ ψ : Fml C}
    (h : Fml.applyOnRigidBoxTop m U φ = some ψ) (σ : State) (hψ : holds σ ψ) :
    holds σ (.upd m U φ) := by
  unfold Fml.applyOnRigidBoxTop at h
  split at h
  · rename_i hc
    cases h
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hc
    obtain ⟨⟨⟨hm, hU⟩, hr⟩, hs⟩ := hc
    refine Fml.upd_of_box hm ?_
    rcases hU with hU | hU
    · exact Fml.subst_box hU hr hs σ hψ
    · exact Fml.subst_box_st hU.1 hU.2 hs σ hψ
  · nomatch h

/-- `applyOnRigidFormula` on the update at position `i`. -/
def Fml.applyOnRigidBoxAt (i : Nat) : Fml C → Option (Fml C) := Fml.atSpine Fml.applyOnRigidBoxTop i

/-- `applyOnRigidFormula` for a storage write under the box
(`Proves.applyStorageBox`): `[{storage := s}] φ ⇝ φ[s/storage]`.  The box
only: the write halts where its path does not resolve. -/
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

-- Here rather than on `UpdElem` (`Update.lean`) to spare a low edit; it moves
-- to that type's `deriving` clause at the next batched edit of `Update.lean`.
deriving instance DecidableEq for UpdElem

/-- The law on the right-hand sides of `[{U}] φ` (`Proves.updRw`), if it
rewrites one.  The box only: the rewritten update may run where `U` halts
(`find(save(S, p, 10), p) ⇝ 10`), which the diamond would count against. -/
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

/-- An update rule at position `i`: `applySkip`, `applyOnRigid`.
`sequentialToParallel` is `mergeAt`/`mergeSpine` and `simplifyUpdate` is
`simplify`/`simplifyFresh`; here they give no line. -/
def updRule (r : UpdRuleName) (i : Nat) : LineRw C :=
  ⟨Fml.updRuleAt r i, fun h σ => (Fml.updRuleAt_holds h σ).1⟩

/-- `simplifyUpdate` on the update at position `i`, reading the formula's variables. -/
def simplify (i : Nat) : LineRw C :=
  ⟨Fml.simplifyAt i, Fml.atSpine_sound (fun h σ => (Fml.simplifyWith_holds (fun _ h _ => h) h σ).1) i _⟩

/-- `simplifyUpdate` on the update at position `i`, reading the formula's
fresh variables. -/
def simplifyFresh (i : Nat) : LineRw C :=
  ⟨Fml.simplifyFreshAt i, Fml.atSpine_sound (fun h σ => (Fml.simplifyFreshTop_holds h σ).1) i _⟩

/-- `applyOnRigidFormula` on the update at position `i`, under the box or where it cannot halt. -/
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
