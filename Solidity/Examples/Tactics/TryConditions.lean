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

/-- Pinned solc accepts a complete Panic word with a trailing byte. The old
exact-length policy certificate is retained at commit ffabfb22 and in task evidence. -/
theorem trailing_panic_data : Semantics.decodePanic (Semantics.encodePanic 67 ++ [0]) = some ⟨67, rfl⟩ := by decide +kernel

/-- A complete model Panic payload binds its actual code. -/
theorem complete_panic_data : Semantics.decodePanic (Semantics.encodePanic 67) = some ⟨67, rfl⟩ := by decide +kernel


/-- A representative256-byte datum: selector, code67 and a zero suffix.
The original EVM memory suffix is separate reference evidence. This intrinsic
control makes no physical-memory source-admission or exact-payload claim. -/
def longPanic : Semantics.RevertData := Semantics.encodePanic 67 ++ List.replicate 220 0

/-- A complete prefix retains code67 despite220 trailing bytes. -/
theorem long_panic_data : Semantics.decodePanic longPanic = some ⟨67, rfl⟩ := by decide +kernel

/-- A nonzero suffix is ignored, not shifted into or appended to the code. -/
theorem panic_word_order : Semantics.decodePanic (Semantics.encodePanic 258 ++ Semantics.wordBytes 999) =
    some ⟨258, rfl⟩ := by decide +kernel

/-- The zero code is a valid uint256, not a malformed payload. -/
theorem zero_panic_data : Semantics.decodePanic (Semantics.encodePanic 0 ++ [255]) = some ⟨0, rfl⟩ := by decide +kernel

/-- The high bit of the32-byte word is unsigned and retained. -/
theorem unsigned_panic_data : (Semantics.decodePanic (Semantics.encodePanic (2^255) ++ [1])).map Subtype.val =
    some (2^255 : Int) := by decide +kernel

/-- An incorrect selector cannot bind a code even with a full word and suffix. -/
theorem wrong_panic_selector : Semantics.decodePanic ([0x4e,0x48,0x7b,0x72] ++ Semantics.wordBytes 67 ++ [0]) = none := by decide +kernel

/-- Three bytes and six bytes are the original a/b truncated shapes. -/
theorem truncated_panic_data : Semantics.decodePanic (longPanic.take 3) = none ∧
    Semantics.decodePanic (longPanic.take 6) = none := by decide +kernel

/-- A uint word without the four selector bytes is not Panic returndata. -/
theorem missing_panic_selector : Semantics.decodePanic (Semantics.wordBytes 67) = none := by decide +kernel

/-- Unknown bytes after a valid Panic selector cannot be excluded merely
because the pattern is longer than36 bytes. -/
theorem long_pattern_not_excluded :
    Pat.notPanic (Semantics.panicSelector.map some ++ List.replicate 252 none) = false := by decide +kernel

/-- A short pattern or a known incorrect selector really excludes Panic. -/
theorem malformed_patterns_excluded :
    Pat.notPanic (List.replicate 35 none) = true ∧
    Pat.notPanic ([some 0x4e,some 0x48,some 0x7b,some 0x72] ++ List.replicate 252 none) = true := by decide +kernel

/-- A raw callee body retains actual halt bytes in an intrinsic typed program. -/
def rawPanicBody {Γ : Ctx} (d : Semantics.RevertData) : Prog Probe Γ Γ :=
    .cons (.revertData [.bytes d]) .nil

/-- The callee call is factored independently of the data length. -/
def panicCallee (d : Semantics.RevertData) : Stmt Probe [] [] :=
    .call guardedCall.fn .nil (.rets .nil) (rawPanicBody d)

/-- Raw data survives argument/frame setup without unfolding its byte list. -/
theorem panic_callee_halts (d : Semantics.RevertData) (σ : State Probe []) :
    (panicCallee d).run σ = .error (THalt.ofData d) := by
  change (.error (THalt.ofData (d ++ [])) : TRes _) = _
  rw [List.append_nil]

/-- Actual self identity and empty oracle; no concrete oracle installation. -/
def panicState : State Probe [] := { State.init Probe with tx := { selfAddress := ⟨7,rfl⟩ } }

/-- The Panic continuation completes; other data is rethrown unchanged.
This typed composition is not an assembly source adapter. -/
def panicStatement (d : Semantics.RevertData) : Stmt Probe [] [] :=
    .tryCall guardedCall .nil .nil (rawPanicBody d) .none .nil (rawPanicBody d)
      .nil (rawPanicBody d) true

/-- A256-byte actual self-call failure reaches the deterministic Panic tail. -/
theorem deterministic_long_panic : (panicStatement longPanic).run panicState =
    .ok ⟨panicState,List.prefix_refl _⟩ := by
  change TRun.tryCall guardedCall .nil .refl (Prog.nil : Prog Probe [] []).runR
    .refl (rawPanicBody longPanic).runR .none .refl (Prog.nil : Prog Probe [] []).runR
    .refl (rawPanicBody longPanic).runR .nil .refl (rawPanicBody longPanic).runR true panicState = _
  have hc : TRun.call (.nil : Args Probe [] []) (.rets .nil) .refl
      (rawPanicBody longPanic).runR panicState = .error (.revertWith longPanic) :=
    panic_callee_halts longPanic panicState
  have hs : (guardedCall.addr.evalT panicState).1 = panicState.tx.selfAddress.1 := rfl
  have he : Semantics.decodeError longPanic = none := by decide +kernel
  simp only [TRun.tryCall, hs, decide_true, Bool.true_and, if_true, hc, he, long_panic_data]
  rfl

/-- Undecodable short returndata remains the exact rethrown actual halt. -/
theorem deterministic_short_rethrown : ((panicStatement (longPanic.take 6)).run panicState).halt? =
    some (.revertWith (longPanic.take 6)) := by rfl

/-- The existing catchData producer preserves all raw bytes independently
of whether the Panic decoder can bind a code. -/
theorem raw_failure_preserved :
    TRun.catchBytes guardedCall .nil .nil .refl (rawPanicBody (longPanic.take 3)).runR true panicState =
      .ok (longPanic.take 3) := by rfl

/-- Under the unchanged callback relation, the actual successful Panic
alternative exists. Other legacy callback alternatives are not removed. -/
theorem callback_long_panic (J : StateInv Probe) :
    ExecS J panicState (panicStatement longPanic) (.ok ⟨panicState,List.prefix_refl _⟩) := by
  have hc := ExecS.det (J := J) (σ := panicState) (s := panicCallee longPanic) rfl
  rw [panic_callee_halts] at hc
  exact ExecS.trySelfPanic (v := ⟨67,rfl⟩) (by decide) rfl hc
    (.inr ⟨longPanic,rfl,long_panic_data⟩) ExecP.nil

/-- Every suffix is ignored after the actual complete unsigned word67;
this covers real compiler memory tails without injecting their bytes. -/
theorem panic_suffix_independent (tail : List UInt8) :
    Semantics.decodePanic (Semantics.encodePanic 67 ++ tail) = some ⟨67,rfl⟩ := by
  have hsel : (Semantics.encodePanic 67 ++ tail).take 4 = Semantics.panicSelector := rfl
  have hlen : 36 ≤ (Semantics.encodePanic 67 ++ tail).length := by
    rw [List.length_append]
    change 36 ≤ 36 + tail.length
    omega
  have hword : Semantics.bytesNat (((Semantics.encodePanic 67 ++ tail).drop 4).take 32) = 67 := rfl
  simp only [Semantics.decodePanic, if_pos (And.intro hsel hlen), hword]
  rfl

/-- Every full uint256 word is representable, including all32 bytes set. -/
theorem maximum_panic_data : (Semantics.decodePanic (Semantics.encodePanic (2^256-1) ++ [255])).map Subtype.val =
    some (2^256-1 : Int) := by decide +kernel

/-- Existing raw binding preserves the entire suffix, even when Panic decodes. -/
theorem raw_long_preserved : CatchKind.raw.decode longPanic = some longPanic := by decide +kernel

/-- An incorrect selector is rethrown with all actual bytes unchanged. -/
theorem wrong_selector_rethrown :
    ((panicStatement ([0x4e,0x48,0x7b,0x72] ++ Semantics.wordBytes 67 ++ [255])).run panicState).halt? =
      some (.revertWith ([0x4e,0x48,0x7b,0x72] ++ Semantics.wordBytes 67 ++ [255])) := by rfl

/-- A typed code binder stores the actual decoded word before its local
is dropped; the caller storage survives that exact scope transport. -/
def capturePanicStatement (d : Semantics.RevertData) : Stmt Probe [] [] :=
    .tryCall guardedCall .nil .nil (rawPanicBody d) (.some (.user "code"))
      (.cons (.assign (.root "reasonCode" rfl) (.val (.simple (.local .here)))) .nil)
      (rawPanicBody d) .nil (rawPanicBody d) true

/-- The observed67 is read from actual caller storage after binding/pop. -/
def capturedPanicCode (d : Semantics.RevertData) : TRes (Option String) := do
  let out ← (capturePanicStatement d).run panicState
  pure (Tools.fmtRoot out.st.storage "reasonCode")

/-- A trailing payload binds code67, not a suffix-derived value. -/
theorem actual_panic_code_capture : capturedPanicCode longPanic = .ok (some "67") := by
  have observed : (capturedPanicCode longPanic).toOption = some (some "67") := by decide +kernel
  cases actual : capturedPanicCode longPanic with
  | error e =>
    rw [actual] at observed
    cases observed
  | ok value =>
    rw [actual] at observed
    exact congrArg Except.ok (Option.some.inj observed)

/-- Empty raw failure keeps the pre-existing bare-revert normalization. -/
theorem empty_failure_is_bare : (panicCallee []).run panicState = .error .revert :=
  panic_callee_halts [] panicState

end Solidity.Examples.Tactics.TryConditions
