import Solidity.Automation.SummaryCache
import Solidity.Automation.SummaryContracts

/-! Consumers of the reusable certificate API: cache laws and typed call sites. -/
namespace Solidity.Automation.Summary.Tests

-- Any checked verdict is reusable without invoking even a different checker.
example {valid : Key → Prop} (cache : Cache valid) (key : Key)
    (verdict : Verdict valid key) (verify : (key : Key) → Option (Verdict valid key)) :
    (cache.insert key verdict).check key verify =
      (some verdict, cache.insert key verdict, false) :=
  Cache.check_hit _ _ _ _ (Cache.lookup_insert cache key verdict)

-- An unknown attempt preserves exactly the cache available to a later retry.
example {valid : Key → Prop} (cache : Cache valid) (key : Key)
    (verify : (key : Key) → Option (Verdict valid key))
    (miss : cache.lookup key = none) (unknown : verify key = none) :
    (cache.check key verify).2.1 = cache :=
  congrArg (fun result => result.2.1) (Cache.check_unknown cache key verify miss unknown)

private def skipSpec (C : Contract) (m : Modality) : Specification C [] [] [] :=
  { body := .nil, requires := .tt, ensures := .tt, modality := m, mutability := .pure }

-- Prove the callee once, universally over caller frames and return targets.
private theorem skipCertified (C : Contract) (m : Modality) : (skipSpec C m).Certified := by
  apply Specification.certify
  · intro Γ Γ' ret σ
    cases ret with
    | none =>
      intro _ τ _
      exact ⟨True.intro, nofun⟩
    | rets bs =>
      cases bs
      intro _ τ _
      exact ⟨True.intro, nofun⟩
  · rfl
  · intro Γ Γ' ret
    rfl

-- Both modalities reuse the certificate behind quantified caller locals.
private theorem callSkip (C : Contract) (m : Modality) {Γ : Ctx}
    (H : Hyps C [] Γ) (hb : H.boxOnly = true) :
    Fml.Valid (H.wrap
      (.modal m (.cons (.call "skip" .nil .none (.nil : Prog C [] [])) .nil) .nil .tt)) := by
  apply (skipSpec C m).use (skipCertified C m)
  · apply H.wrap_valid hb
    intro σ
    exact ⟨True.intro, nofun⟩
  · apply H.wrap_valid hb
    intro σ
    refine ⟨?_, nofun⟩
    intro τ _ _
    exact ⟨True.intro, nofun⟩

example (C : Contract) : Fml.Valid (C := C)
    (.modal .box (.cons (.call "skip" .nil .none (.nil : Prog C [] [])) .nil) .nil .tt) :=
  callSkip C .box .nil rfl

example (C : Contract) : Fml.Valid (C := C)
    (.all (.user "x") .uint (.all (.user "b") .bool
      (.modal .diamond
        (.cons (.call "skip" .nil .none (.nil : Prog C [] [])) .nil) .nil .tt))) :=
  callSkip C .diamond ((Hyps.nil.all (.user "x") .uint).all (.user "b") .bool) rfl

private def changedBody (C : Contract) : Specification C [] [] [] :=
  { skipSpec C .diamond with body := .cons .revert .nil }

private def changedPost (C : Contract) : Specification C [] [] [] :=
  { skipSpec C .box with ensures := .ff }

-- A certificate for the original body cannot certify a changed body.
example (_C : Contract) : True := by
  fail_if_success
    have : (changedBody _C).Certified :=
      skipCertified _C .diamond
  trivial

-- Nor can it certify a stronger postcondition.
example (_C : Contract) : True := by
  fail_if_success
    have : (changedPost _C).Certified := skipCertified _C .box
  trivial

end Solidity.Automation.Summary.Tests
