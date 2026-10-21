import Solidity.Calculus.Graft
import Solidity.Calculus.Sound
import Solidity.Calculus.Logic
import Solidity.Calculus.FirstOrder
import Solidity.Calculus.Close

/-!
# `sequentialToParallel` on scoped lines

KeY's `sequentialToParallel2` (`{u}{u2}φ ⇝ {u ‖ {u}u2}φ`) on a scoped line,
so that a scoped chain merges its stack while the program is still open
(`Examples/Chains/StorageToMemory.lean`'s `FieldCopy` and `TokenCopy`), as
`Calculus/RewritePast.lean`'s does past it.
The merge of two updates and why it is sound are
`Calculus/Graft.lean`'s (`Upd.seqPar`, `holds_upd_seqPar`), which the
sequent's `merge` reads too; here they are found on a line's update spine,
through its quantifiers and hidden binders.  This module's spine merge
(`Fml.mergeRun`) substitutes no storage (`Upd.graft` with no `Upd.lastSt`).
A merge over a storage or memory write is `FmlRw.stateMerge`
(`Calculus/RewriteScoped.lean`, `Upd.mergeSt?`/`Upd.mergeMem?` of
`Calculus/StatePartsScoped.lean`) while the program is open, and
`Calculus/RewritePast.lean`'s past it.

The merge is a function the kernel evaluates (`Fml.mergeRun`), and its
soundness one theorem: `Fml.mergeRun_leads`.  It is written with `match` on
the indexed families, against Gate G0's first condition: an exemption, timed
in `docs/intrinsic.md` (W3b), since it runs once a link and not once a step.
-/

namespace Solidity

open Solidity (Modality)

variable {C : Contract}

/-- `{U}_m {V}_m ψ` merged into `{W}_m ψ`, through the hidden binders between
the two (`U` moved under each, `Upd.lift?`), each at a type other than a
memory one or under an update that allocates nothing (`Upd.keepsNext`). -/
def Fml.merge2 (m : Modality) : {Γ Δ : Ctx} → Upd C Γ Δ → Fml C Δ → Option (Fml C Γ)
  | _, _, U, .upd m' V ψ =>
    if m' = m then (U.graft U.held U.envOnly none V).map (.upd m · ψ) else none
  | _, _, U, .bind m' x t ψ =>
    if (t.notMem || U.keepsNext) = true then
      (U.lift? (t := t)).bind fun U' => (Fml.merge2 m U' ψ).map (.bind m' x t)
    else none
  | _, _, _, _ => none

/-- `sequentialToParallel` on the updates at positions `k` and `k + 1` of
the line's update spine, under its quantifiers and hidden binders. -/
def Fml.mergeAt {Γ : Ctx} : Nat → Fml C Γ → Option (Fml C Γ)
  | k, .all x p φ => (Fml.mergeAt k φ).map (.all x p)
  | k, .bind m x t φ => (Fml.mergeAt k φ).map (.bind m x t)
  | 0, .upd m U φ => Fml.merge2 m U φ
  | k + 1, .upd m U φ => (Fml.mergeAt k φ).map (.upd m U)
  | _, _ => none

/-- `sequentialToParallel` `n` times at the position `k`: the `n + 1`
updates from there merged into one, the outermost pair first. -/
def Fml.mergeRun {Γ : Ctx} (k : Nat) : Nat → Fml C Γ → Option (Fml C Γ)
  | 0, φ => some φ
  | n + 1, φ => (φ.mergeAt k).bind (Fml.mergeRun k n)

/-- `φ ~[sequentialToParallel]~> ψ` on scoped lines: the `n + 1` updates
from position `k` of `φ`'s spine merge into `ψ`'s one. -/
def Fml.MergeBy {Γ : Ctx} (k n : Nat) (φ ψ : Fml C Γ) : Prop := φ.mergeRun k n = some ψ

section Leads

variable {Γ : Ctx}

/-- **The merged update leads to the two.** -/
theorem Fml.merge2_leads {m : Modality} : {Γ Δ : Ctx} → (U : Upd C Γ Δ) →
    (φ : Fml C Δ) → {ψ : Fml C Γ} → Fml.merge2 m U φ = some ψ → ∀ σ, holds σ ψ → holds σ (.upd m U φ)
  | _, _, U, .upd m' V χ, ψ, h => by
    simp only [Fml.merge2] at h
    split at h
    · rename_i hc
      subst hc
      obtain ⟨W, hW, rfl⟩ := Option.map_eq_some_iff.1 h
      exact fun σ hψ => holds_upd_graft (st := none) (fun _ _ _ _ h => Option.noConfusion h) hW σ hψ
    · cases h
  | _, _, U, .bind m' x t χ, ψ, h => by
    simp only [Fml.merge2] at h
    split at h
    · rename_i ht
      obtain ⟨U', hU', h⟩ := Option.bind_eq_some_iff.1 h
      obtain ⟨χ', hχ', rfl⟩ := Option.map_eq_some_iff.1 h
      intro σ hψ
      exact Fml.upd_bind_of_lift hU' ht σ
        (Modality.forallB_imp (fun v h => Fml.merge2_leads U' χ hχ' _ h) hψ)
    · cases h
  | _, _, _, .tt, _, h | _, _, _, .eq .., _, h | _, _, _, .wellFormed _, _, h | _, _, _, .not _, _, h
  | _, _, _, .and .., _, h | _, _, _, .imp .., _, h | _, _, _, .modal .., _, h
  | _, _, _, .havoc _, _, h | _, _, _, .all .., _, h | _, _, _, .anon .., _, h
  | _, _, _, .allocAll .., _, h => nomatch h

theorem Fml.mergeAt_leads : {Γ : Ctx} → (k : Nat) → (φ : Fml C Γ) → {ψ : Fml C Γ} →
    φ.mergeAt k = some ψ → ∀ σ, holds σ ψ → holds σ φ
  | _, k, .all x p φ, ψ₀, h => by
    have h : (Fml.mergeAt k φ).map (Fml.all x p) = some ψ₀ := by rw [← h]; cases k <;> rfl
    obtain ⟨ψ, hψ, rfl⟩ := Option.map_eq_some_iff.1 h
    exact fun σ hs v => Fml.mergeAt_leads k φ hψ _ (hs v)
  | _, k, .bind m x t φ, ψ₀, h => by
    have h : (Fml.mergeAt k φ).map (Fml.bind m x t) = some ψ₀ := by rw [← h]; cases k <;> rfl
    obtain ⟨ψ, hψ, rfl⟩ := Option.map_eq_some_iff.1 h
    exact fun σ hs => Modality.forallB_imp (fun v => Fml.mergeAt_leads k φ hψ _) hs
  | _, 0, .upd m U φ, _, h => Fml.merge2_leads U φ h
  | _, k + 1, .upd m U φ, _, h => by
    obtain ⟨ψ, hψ, rfl⟩ := Option.map_eq_some_iff.1 h
    exact fun σ hs => Upd.afterT_imp hs fun σ' a => Fml.mergeAt_leads k φ hψ σ' a
  | _, k, .tt, _, h | _, k, .eq .., _, h | _, k, .wellFormed _, _, h | _, k, .not _, _, h
  | _, k, .and .., _, h | _, k, .imp .., _, h | _, k, .modal .., _, h | _, k, .havoc _, _, h
  | _, k, .anon .., _, h | _, k, .allocAll .., _, h => by
    cases k <;> cases h

theorem Fml.mergeRun_leads (k : Nat) : (n : Nat) → (φ : Fml C Γ) → {ψ : Fml C Γ} →
    φ.mergeRun k n = some ψ → ∀ σ, holds σ ψ → holds σ φ
  | 0, φ, _, h => by cases h; exact fun _ h => h
  | n + 1, φ, _, h => by
    obtain ⟨χ, hχ, h⟩ := Option.bind_eq_some_iff.1 h
    exact fun σ hψ => Fml.mergeAt_leads k φ hχ σ (Fml.mergeRun_leads k n χ h σ hψ)

end Leads

end Solidity
