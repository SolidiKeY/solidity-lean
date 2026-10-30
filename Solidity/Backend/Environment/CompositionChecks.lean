import Solidity.Backend.Environment.Frames
import Solidity.Backend.Environment.ObservationsChecks

/-! Inhabited mixed observations, source sequence controls and stability countermodels. -/
namespace Solidity.Backend.Environment

private abbrev BR : RefTy := .array (.prim .uint)
private abbrev BG : Ctx := [.mem BR]
private def initial : State default BG :=
  { storage := Storage.init default
    H := [BR]
    heap := (⟨[lenU 1 (by decide), lenU 2 (by decide), lenU 3 (by decide)], by decide⟩, ())
    env := (some ⟨0, rfl⟩, ()) }
private def source : State default BG := represented initial sample
private def path : MPath default BG (.ref BR) := .var .here rfl
private def ref : HRef source.H BR := ⟨0, rfl⟩
private def mem : Memory := writeBytes (fun _ => 0xbb) 7 [1, 2, 3]
private def selector : Fin (256 ^ (4 : Fin 33).val) := ⟨0x12345678, by decide⟩
private def literal : Val default BG .uint :=
  .simple (.lit (lenU selector.val (constant_bound 4 selector)).1
    (lenU selector.val (constant_bound 4 selector)).2)
private def code : List Instr :=
  [select .msgSender] ++ ([constant 4 selector] ++ (keccakCode ⟨7, by decide⟩ ⟨3, by decide⟩ ++ []))

private def mixed : ValuesCertificate source
    [.simple (.env .msgSender rfl), literal, .hash .keccak path rfl] sample code mem :=
  consCertificate (environmentCertificate source sample (represented_ok initial sample) .msgSender mem)
    (consCertificate (literalCertificate source sample 4 selector mem)
      (consCertificate (hashCertificate source path ref rfl sample
          ⟨7, by decide⟩ ⟨3, by decide⟩ mem ⟨by decide, by decide +kernel⟩)
        (nilCertificate source sample mem)))

/-- Actual intrinsic sender/metadata/hash denotations compose over one inhabited
heap and arbitrary pre-existing target stack; this is not an assumed premise. -/
theorem mixed_observation_control (tail : List Word) :
    evalValues source [.simple (.env .msgSender rfl), literal, .hash .keccak path rfl] =
      .ok [sample.sender.1, lenU selector.val (constant_bound 4 selector), source.heap.hash .keccak ref] ∧
    runSlice sample code ⟨tail, mem⟩ =
      some ⟨[source.heap.hash .keccak ref, lenU selector.val (constant_bound 4 selector),
        sample.sender.1] ++ tail, mem⟩ := by
  exact ⟨mixed.source, mixed.target tail⟩

/-- A single actual stream also composes materialization with the hash slice. -/
theorem materialize_then_hash (f : Frame) (m : Memory) (tail : List Word) :
    runSlice f (materialize 7 [1, 2, 3] ++ keccakCode ⟨7, by decide⟩ ⟨3, by decide⟩)
      ⟨tail, m⟩ = some ⟨digest [1, 2, 3] :: tail, writeBytes m 7 [1, 2, 3]⟩ := by
  rw [runSlice_append, runSlice_data f _ _ (materialize_supported _ _), materialize_correct]
  · change runSlice f (keccakCode _ _) _ = _
    rw [runSlice_crypto f _ _ (keccak_supported _ _), keccak_correct]
    have hr : readMemory (writeBytes m 7 [1, 2, 3]) 7 [1, 2, 3].length = [1, 2, 3] :=
      read_written [1, 2, 3] 7 m
    change readMemory (writeBytes m 7 [1, 2, 3]) 7 3 = [1, 2, 3] at hr
    rw [hr]
  · decide

/-- Two successive source argument effects are retained by ordinary typed
sequence composition, even when their returned values are discarded. -/
theorem source_effect_control {C : Contract} (σ : State C [.val .uint]) :
    (Prog.run σ (.cons (.assignLocal .here (.simple (.lit 1 rfl)))
      (.cons (.assignLocal .here (.binop .add rfl rfl (.simple (.local .here))
        (.simple (.lit 2 rfl)))) .nil))).map
      (fun out => (TEnv.get (.here : Idx [.val .uint] (.val .uint)) out.st.env).1) = .ok 3 := by
  rfl

/-- Changing evaluation order changes the exact halt, so erasure/reordering of
argument effects is not licensed by unobservability of logs. -/
theorem source_order_control {C : Contract} {Γ : Ctx} (σ : State C Γ) :
    Prog.run σ (.cons (.assert (.simple (.bool false))) (.cons .revert .nil)) = .error .panic ∧
    Prog.run σ (.cons .revert (.cons (.assert (.simple (.bool false))) .nil)) = .error .revert :=
  ⟨rfl, rfl⟩

theorem source_order_distinguishes {C : Contract} {Γ : Ctx} (σ : State C Γ) :
    (Prog.run σ (.cons (.assert (.simple (.bool false))) (.cons .revert .nil))).halt? ≠
      (Prog.run σ (.cons .revert (.cons (.assert (.simple (.bool false))) .nil))).halt? := by
  intro h
  change (some THalt.panic : Option THalt) = some THalt.revert at h
  contradiction

/-- Source code order is also visible in the exact target stack sequence. -/
theorem opcode_order_control :
    runSlice sample [select .msgSender, select .selfAddress] ⟨[], fun _ => 0⟩ ≠
      runSlice sample [select .selfAddress, select .msgSender] ⟨[], fun _ => 0⟩ := by
  intro h
  have values :
      (runSlice sample [select .msgSender, select .selfAddress] ⟨[], fun _ => 0⟩).map
        (fun s => s.stack.map Subtype.val) =
      (runSlice sample [select .selfAddress, select .msgSender] ⟨[], fun _ => 0⟩).map
        (fun s => s.stack.map Subtype.val) :=
    congrArg (fun result => result.map fun s => s.stack.map Subtype.val) h
  change some [7, 9] = some [9, 7] at values
  contradiction

theorem repeated_balance_control :
    (step sample (.op .BALANCE) [sample.self.1]).bind
      (fun stack => step sample (.op .BALANCE) (sample.self.1 :: stack)) =
      some [lenU 41 (by decide), lenU 41 (by decide)] := by decide +kernel

/-- Forced credits really can change own-balance reads between frames. -/
theorem forced_credit_counterexample :
    step sample (.op .SELFBALANCE) [] ≠
      step (overwriteFunds sample sample.self (lenU 42 (by decide))) (.op .SELFBALANCE) [] := by
  decide +kernel

theorem changed_time_counterexample :
    step sample (.op .TIMESTAMP) [] ≠
      step { sample with time := lenU 14 (by decide) } (.op .TIMESTAMP) [] := by decide +kernel

/-- info: 'Solidity.Backend.Environment.consCertificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms consCertificate
/-- info: 'Solidity.Backend.Environment.mixed_observation_control' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms mixed_observation_control
/-- info: 'Solidity.Backend.Environment.materialize_then_hash' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms materialize_then_hash
/-- info: 'Solidity.Backend.Environment.source_sequence_success' depends on axioms: [propext] -/
#guard_msgs in
#print axioms source_sequence_success
/-- info: 'Solidity.Backend.Environment.source_effect_control' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms source_effect_control
/-- info: 'Solidity.Backend.Environment.repeated_across_stable' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms repeated_across_stable
end Solidity.Backend.Environment
