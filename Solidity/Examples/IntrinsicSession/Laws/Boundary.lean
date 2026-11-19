import Solidity.Correctness.IntrinsicSession.Laws.Boundary
import Solidity.Examples.IntrinsicSession.Spec

/-! The seven boundary laws on the one-contract session of `Spec.lean`, resumed at `w`: its
start, the boundaries it reaches and the worlds it lists. -/
namespace Solidity.Examples.IntrinsicSession.Laws.Boundary

open Solidity.Roadmap Solidity.Semantics.IntrinsicSession Solidity.Examples.IntrinsicSession.Spec
open Solidity.Goals.IntrinsicSession (Code TypedWorld Good Observed Credited outcomes)
open Solidity.Lowering.V08.EnvironmentProjection (liftWord liftAddress)

variable {C : Contract} {code : Code} {w : ContractWorld.World code.catalog} {F : Fixed}
  {r : Bound} {e : SessionEnv} (s : OneRequest C code w F r e) (allowed : e.Allowed)

/-- `starts`, `boundary_observed`, `boundary_code`: the session starts at `w` with the empty
history, which is observed, in its code; the start is not idle. -/
example : (view F).Boundary s.start e [] 0 ⟨code, w⟩ ∧ Observed (spec F) s.start e [] ∧
    (⟨code, w⟩ : TypedWorld).code = ((view F).typed s.start).code ∧ e.requests [] 0 ≠ none :=
  have b := Laws.starts F ⟨code, w⟩ e allowed
  ⟨b, Laws.boundary_observed F _ _ _ _ _ b, Laws.boundary_code F _ _ _ _ _ b,
    fun idle => nomatch s.next.symm.trans idle⟩

/-- `listed_boundary`, with `boundary_observed` and `boundary_code`: a world the session lists
at a good bound stands at a boundary whose history the prefix has reached, and which is
observed, in the session's code. -/
example (good : Good (spec F) r) {ω : Start} (mem : ω ∈ (spec F).worlds s.start e r) :
    ∃ h n, (view F).Boundary s.start e h n ((view F).typed ω) ∧
      h <+: ((spec F).lang.sem s.start e r).events ∧ Observed (spec F) s.start e h ∧
      ((view F).typed ω).code = code :=
  have ⟨h, n, b, pre⟩ := Laws.listed_boundary F s.start e r good ω mem
  ⟨h, n, b, pre, Laws.boundary_observed F _ _ _ _ _ b, Laws.boundary_code F _ _ _ _ _ b⟩

/-- `idle`: at a boundary of the session with no further action, a good bound that reaches
its history shows exactly it, and a history with an outcome is a final prefix. -/
example {h n t} (b : (view F).Boundary s.start e h n t) (ended : e.requests h n = none)
    (good : Good (spec F) r) (pre : h <+: ((spec F).lang.sem s.start e r).events)
    (has : outcomes h ≠ []) : ((spec F).lang.sem s.start e r).events = h ∧
    ∃ r', Good (spec F) r' ∧ ((spec F).lang.sem s.start e r').events = h ∧
      ((spec F).lang.sem s.start e r').final ≠ none :=
  have law := Laws.idle F s.start e h n t allowed b ended
  ⟨law.1 r good pre, law.2 has⟩

/-- `dropped`: the session's first request is affordable, so it is not dropped; a later
unaffordable one is, at the same history and world. -/
example {h n t q} (b : (view F).Boundary s.start e h n t)
    (next : e.requests h n = some (.request q)) (unfunded : ¬ Funded F e h q) :
    (view F).Boundary s.start e h (n + 1) t ∧ (h = [] → n ≠ 0) :=
  ⟨Laws.dropped F s.start e h n t q allowed b next unfunded, fun nil zero => by
    subst nil zero
    cases s.next.symm.trans next
    exact unfunded s.funded⟩

/-- `credited`: a credit at a boundary of the session is observed after its history, a good
bound reaching the history shows it alone or the credit, and a sum that is a word is the
target's funds at the next boundary. -/
example {h n} {cw : ContractWorld.World code.catalog} {target value sum}
    (b : (view F).Boundary s.start e h n ⟨code, cw⟩)
    (next : e.requests h n = some (.credit target value))
    (good : Good (spec F) r) (pre : h <+: ((spec F).lang.sem s.start e r).events)
    (word : PrimTy.ofInt? .uint ((cw.funds (liftAddress target)).1 + (liftWord value).1) =
      some sum) :
    Observed (spec F) s.start e (h ++ [.credit target value]) ∧
    (((spec F).lang.sem s.start e r).events = h ∨
      h ++ [.credit target value] <+: ((spec F).lang.sem s.start e r).events) ∧
    ∃ cw', Credited cw (liftAddress target) sum cw' ∧ cw'.funds (liftAddress target) = sum ∧
      (view F).Boundary s.start e (h ++ [.credit target value]) (n + 1) ⟨code, cw'⟩ :=
  have ⟨seen, cases, after⟩ := Laws.credited F s.start e h n code cw target value allowed b next
  have ⟨cw', credited, next'⟩ := after sum word
  ⟨seen, cases r good pre, cw', credited, credited.2.2.2, next'⟩

end Solidity.Examples.IntrinsicSession.Laws.Boundary
