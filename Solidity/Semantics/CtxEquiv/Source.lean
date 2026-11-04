import Solidity.Semantics.CtxEquiv.Unify
import Solidity.Source.Session

/-!
# Contextual equivalence of source programs (S1.1)

The independent source semantics with the events of unfinished
transactions (`sourceLangEvents`, `Solidity/Source/Session.lean`) is a G01
language over session environments, so a source program is a `Contract`
directly: deployment from the session's deployer, then the adversary's
transactions, callbacks and credits (`srcContract`).  Contextual equivalence
of two source programs is G01 refinement of their sessions against every
allowed environment (`srcContract_ctxEquiv_iff`); equal sessions are
equivalent (`srcContract_ctxEquiv_of_sessions`).
-/

namespace Solidity.CtxEquiv

open Solidity.Roadmap (SessionEnv Refines)
open Solidity.Source

variable {E : Env}

/-- A source program deployed against G50 adversaries, counting every
horizon. -/
def srcContract (P : SrcProg E) : Contract := Deployed.mk' (sourceLangEvents E) P id

theorem srcContract_ctxEquiv_iff {E₁ E₂ : Env} (P : SrcProg E₁) (Q : SrcProg E₂) :
    CtxEquiv (srcContract P) (srcContract Q) ↔
      ∀ s, s.Allowed → Refines (fun _ => True) (fun _ => True) (sessionAtEvents P s)
        (sessionAtEvents Q s) :=
  ctxEquivOn_iff_refines SessionEnv.Allowed (sourceLangEvents E₁) (sourceLangEvents E₂) P Q id id

/-- Programs with the same session prefixes at every environment and horizon
are contextually equivalent. -/
theorem srcContract_ctxEquiv_of_sessions {E₁ E₂ : Env} {P : SrcProg E₁} {Q : SrcProg E₂}
    (h : ∀ s n, sessionAtEvents P s n = sessionAtEvents Q s n) :
    CtxEquiv (srcContract P) (srcContract Q) := by
  have hb : ∀ s, (srcContract P).behav s = (srcContract Q).behav s := by
    intro s
    funext π
    apply propext
    exact ⟨fun ⟨n, hn, he⟩ => ⟨n, hn, (h s n).symm.trans he⟩,
      fun ⟨n, hn, he⟩ => ⟨n, hn, (h s n).trans he⟩⟩
  exact ⟨fun s _ => by rw [hb s]; exact Behav.Below.refl _,
    fun s _ => by rw [hb s]; exact Behav.Below.refl _⟩

/-- Every source program is contextually equivalent to itself. -/
theorem srcContract_refl (P : SrcProg E) : CtxEquiv (srcContract P) (srcContract P) :=
  CtxEquiv.refl _

/-- A source completion transfers along refinement with its exact events:
the transaction outcomes, return and revert data. -/
theorem srcContract_completes {E₁ E₂ : Env} {P : SrcProg E₁} {Q : SrcProg E₂}
    (h : CtxRefines (srcContract P) (srcContract Q)) {s : SessionEnv} (hs : s.Allowed) {n : Nat}
    {o : Solidity.Roadmap.Outcome} (ho : (sessionAtEvents P s n).final = some o) :
    ∃ m, sessionAtEvents Q s m = sessionAtEvents P s n := by
  obtain ⟨m, _, hm⟩ := CtxRefinesOn.completes h hs (r := n) trivial ho
  exact ⟨m, hm⟩

end Solidity.CtxEquiv
