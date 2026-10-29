import Solidity.Calculus.Sound.TryConditions
import Solidity.Semantics.TryCreateConditions
import Solidity.Examples.Tactics.ExternalTryUniversal
import Solidity.Tools.Upstream

/-! Conditional try controls. These retain original unconditional refutations,
check every failure boundary separately, and make no callback-profile change.
The original upstream source examples exercise successful/caught alternatives
without box annotations; these nearby controls certify the negative boundaries. -/
namespace Solidity.Examples.Tactics.TryConditions
open Lean ExternalTryWitness
local instance : InContract := ⟨Probe⟩
open scoped Scoped

/-- The address and signature are fixed source syntax; the oracle premise is
explicit and local to the theorem, not an added global source profile. -/
def guardedCall : ExtCall Probe [] := ⟨.lit 7 rfl, "fetch", []⟩

/-- Ordinary source-shaped conditional success for *any* typed starting state.
The actual oracle witness discharges the specialized condition/formula interface. -/
theorem guarded_source_success (σ : State Probe [])
    (he : Semantics.lookupBy (guardedCall.keyT σ) σ.tx.ext = some (.ok [])) :
    holds σ (dl!{ ⟨ try I(7).fetch() { } catch { }; ⟩ true } : Fml Probe []) := by
  have hz : (guardedCall.addr.evalT σ).1 ≠ 0 := by
    change (7 : Int) ≠ 0
    decide
  have hc : TRun.tryCondition guardedCall Binders.nil Prog.nil Prog.nil CodeBinder.none
      Prog.nil Prog.nil Args.nil Prog.nil false σ (.ok ⟨σ, List.prefix_refl _⟩) := by
    simp only [TRun.tryCondition, hz, if_false, Bool.false_and, Bool.false_eq_true, he]
    rfl
  exact (try_condition_formula guardedCall Binders.nil Prog.nil Prog.nil CodeBinder.none
    Prog.nil Prog.nil Args.nil Prog.nil false σ (.ok ⟨σ, List.prefix_refl _⟩) hc
    Prog.nil Frames.nil Fml.tt).2 ⟨True.intro, by intro h; cases h⟩

/-- A failure in a successful continuation is not caught by its own try. -/
def successFails : Prog Probe [] [] := sol{
  try I(7).fetch() { revert(); } catch { tag = 99; }
}
theorem success_body_uncaught :
    (Prog.runFrames (input (.ok [])) successFails .nil).halt? = some .revert := by decide +kernel

/-- A failure in the selected catch body is not caught again. -/
def catchFails : Prog Probe [] [] := sol{
  try I(7).fetch() { tag = 1; } catch { assert(false); }
}
theorem catch_body_uncaught :
    (Prog.runFrames (input (.other [])) catchFails .nil).halt? = some .panic := by decide +kernel

/-- Allocating an actual payload does not make a failing handler normal. -/
def payloadFails : Prog Probe [] [] := sol{
  try I(7).fetch() { tag = 1; } catch (bytes memory data) { assert(data.length == 0); }
}
theorem allocated_payload_failure :
    (Prog.runFrames (input (.other [5])) payloadFails .nil).halt? = some .panic := by decide +kernel

/-- The remaining program executes after a normally caught clause. -/
def restFails : Prog Probe [] [] := sol{
  try I(7).fetch() { tag = 1; } catch { tag = 2; }
  revert();
}
theorem continuation_failure :
    (Prog.runFrames (input (.other [])) restFails .nil).halt? = some .revert := by decide +kernel

/-- Frames are not dropped from the account after normal try completion. -/
theorem frame_failure :
    (Prog.runFrames (input (.other []))
      (sol{ try I(7).fetch() { tag = 1; } catch { tag = 2; } } : Prog Probe [] [])
      (.seq (sol{ revert(); }) .nil)).halt? = some .revert := by decide +kernel

/-- Reuse the replay adapter's actual input validation; no global state domain
is narrowed. Ordinary jobs without this explicit context keep their old input. -/
def contextReport (context : Option Lean.Json) : Lean.Json :=
  Tools.Upstream.replay Probe [] (Lean.Json.mkObj
    ([("requiresSelfContext", toJson true), ("vectors", toJson #[Lean.Json.null])] ++
      context.toList.map fun c => ("hostContext", c)))
def selfContext (address : String) : Lean.Json := Lean.Json.mkObj
  [("kind", toJson "direct-self-try"), ("selfAddress", toJson address)]

theorem missing_context_refused :
    ((contextReport none).getObjValAs? String "reason").toOption = some "missing self-try deployment context" := by decide +kernel

/-- Kernel checks the typed validator actually used before installing context. -/
theorem zero_context_refused : Tools.Upstream.selfTryContextValid "direct-self-try" 0 = false := by decide +kernel

theorem wide_context_refused : Tools.Upstream.selfTryContextValid "direct-self-try" (2^160) = false := by decide +kernel

/- Runtime JSON/decimal parsing is checked separately from the typed proof. -/
/-- info: some "invalid self-try deployment context" -/
#guard_msgs in #eval ((contextReport (some (selfContext "0"))).getObjValAs? String "reason").toOption
/-- info: some "invalid self-try deployment context" -/
#guard_msgs in #eval ((contextReport (some (selfContext "1461501637330902918203684832716283019655932542976"))).getObjValAs? String "reason").toOption

/-- A reference-only physical assembly context cannot enter the native adapter. -/
theorem reference_context_refused :
    Tools.Upstream.selfTryContextValid "direct-self-try-reference" 4096 = false := by decide +kernel

/-- Malformed selector data does not become an Error reason in the model. -/
theorem short_error_data : Semantics.decodeError ((Semantics.encodeError [97, 98]).take 3) = none := by decide +kernel

/-- A truncated Panic word does not bind a code. -/
theorem short_panic_data : Semantics.decodePanic ((Semantics.encodePanic 67).take 35) = none := by decide +kernel

/-- The unchanged model requires exactly 36 bytes, including for trailing data.
This is a model policy certificate, not a claim that solc rejects such data. -/
theorem trailing_panic_data : Semantics.decodePanic (Semantics.encodePanic 67 ++ [0]) = none := by decide +kernel

/-- A complete model Panic payload binds its actual code. -/
theorem complete_panic_data : Semantics.decodePanic (Semantics.encodePanic 67) = some ⟨67, rfl⟩ := by decide +kernel

end Solidity.Examples.Tactics.TryConditions
