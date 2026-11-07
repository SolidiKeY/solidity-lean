import Solidity.Lowering.V08.SourceAbiControls

/-! Regression: ABI argument evaluation and encoding must share the reached
locals/heap; successful bytes alone do not identify the result allocation.
The existing mixed fixture supplies both actual steps, including argument-local
updates and hash-input allocation. Timeout preserves earlier effects rather
than assuming rollback. No new encoder, Source admission or target certificate. -/
namespace H62.AuditV08Adapters.SourceAbiJoint
open Solidity Source
open Solidity.Lowering.V08
open SourceCustomErrorControls

/-- Both original execution premises coexist with their exact shared state. -/
def Joint (pipeline : Roadmap.Pipeline) (static packed : Bool) : Prop :=
  (Source.evalArgs (global pipeline) {frame with static:=static} 16
    SourceAbiControls.arguments).run (locals,populated) =
    (.ok (SourceAbiControls.values pipeline),
      (.cons (.bool false) .nil,SourceKeccak.afterLiteral populated binary)) ∧
  (Source.encodeVals {frame with static:=static} 16 packed
    (SourceAbiControls.values pipeline) : Source.EM E [.bool] _).run
      (.cons (.bool false) .nil,SourceKeccak.afterLiteral populated binary) =
    (.ok (SourceAbiControls.data packed pipeline),
      (.cons (.bool false) .nil,SourceKeccak.afterLiteral populated binary))

theorem joint (pipeline : Roadmap.Pipeline) (static packed : Bool) :
    Joint pipeline static packed :=
  ⟨SourceAbiControls.arguments_execute pipeline static,
    SourceAbiControls.encoding_execute pipeline static packed⟩

/-- Full original ABI expression result, including reached allocator pointer. -/
theorem actual (pipeline : Roadmap.Pipeline) (static packed : Bool) :
    (Source.evalE (global pipeline) {frame with static:=static} 17
      (.abiEncode (if packed then .encodePacked else .encode)
        SourceAbiControls.arguments)).run (locals,populated) =
    (.ok (.val (.memRef rfl 2)),(.cons (.bool false) .nil,
      SourceKeccak.afterLiteral (SourceKeccak.afterLiteral populated binary)
        (SourceAbiControls.data packed pipeline))) := by
  have h := joint pipeline static packed
  exact SourceAbi.execute (global pipeline) {frame with static:=static} 16 packed
    SourceAbiControls.arguments locals (.cons (.bool false) .nil) (.cons (.bool false) .nil)
    populated _ _ (SourceAbiControls.values pipeline) _ h.1 h.2

/-- Existing insufficient-horizon execution retains the earlier local write. -/
theorem timeout_after_effects (pipeline : Roadmap.Pipeline) (static packed : Bool) :
    (Source.evalE (global pipeline) {frame with static:=static} 6
      (.abiEncode (if packed then .encodePacked else .encode)
        SourceAbiControls.arguments)).run (locals,populated) =
    (.error .timeout,(.cons (.bool false) .nil,populated)) :=
  SourceAbiControls.insufficient_after_effects pipeline static packed

theorem timeout_not_rollback (pipeline : Roadmap.Pipeline) (static packed : Bool) :
    (Source.evalE (global pipeline) {frame with static:=static} 6
      (.abiEncode (if packed then .encodePacked else .encode)
        SourceAbiControls.arguments)).run (locals,populated) ≠
      (.error .timeout,(locals,populated)) := by
  rw [timeout_after_effects]
  intro same
  have localSame := congrArg (fun result => result.2.1.get .here) same
  cases localSame

/-- Existing whole-state refusal prevents silently skipping the hash allocation. -/
theorem skipped_allocation_refused (pipeline : Roadmap.Pipeline) (static packed : Bool) :
    (Source.evalE (global pipeline) {frame with static:=static} 17
      (.abiEncode (if packed then .encodePacked else .encode)
        SourceAbiControls.arguments)).run (locals,populated) ≠
      (.ok (.val (.memRef rfl 1)),(.cons (.bool false) .nil,
        SourceKeccak.afterLiteral populated (SourceAbiControls.data packed pipeline))) :=
  SourceAbiControls.wrong_skipped_hash pipeline static packed

/-- Every typed word supplies the original bytes32 observation and encoder
premise together, for arbitrary Source environments and caller contexts. -/
theorem word_joint {E : Source.Env} {Γ : RCtx} (word : Roadmap.Word) :
    ∃ value : Source.Val E.layout STy.bytes32, value.word = some word ∧
      ∀ (frame : Source.Fr) (horizon : Nat) (packed : Bool),
        (Source.encodeOne frame horizon packed (.val value) : Source.EM E Γ _) =
          pure (false,Source.wordBytes word) := by
  refine ⟨Source.mkBytes (n:=32) (h:=by decide +kernel) (Source.wordBytes word),
    SourceAbi.word_bytes_field word, ?_⟩
  intro frame horizon packed
  exact SourceAbi.encode_fixed_bytes32 frame horizon packed _ word
    (SourceAbi.word_bytes_field word)

/-- Exact single-value encoder run retains arbitrary supplied locals/state.
This does not assert that an outer ABI expression succeeds at zero horizon. -/
theorem word_actual_run {E : Source.Env} {Γ : RCtx}
    (word : Roadmap.Word) (frame : Source.Fr) (horizon : Nat) (packed : Bool)
    (locals : Source.Locals E.layout Γ) (state : Source.St E) :
    let value : Source.Val E.layout STy.bytes32 :=
      Source.mkBytes (n:=32) (h:=by decide +kernel) (Source.wordBytes word)
    (Source.encodeOne frame horizon packed (.val value) : Source.EM E Γ _).run (locals,state) =
      (.ok (false,Source.wordBytes word),(locals,state)) := by
  dsimp only
  rw [SourceAbi.encode_fixed_bytes32 frame horizon packed _ word
    (SourceAbi.word_bytes_field word)]
  rfl

/-- A different observed word cannot justify this same value's encoder premise. -/
theorem other_word_refused {D : Source.Layout} (word other : Roadmap.Word)
    (different : word ≠ other) :
    ¬ ((Source.mkBytes (n:=32) (h:=by decide +kernel) (Source.wordBytes word) :
      Source.Val D STy.bytes32).word = some other) := by
  rw [SourceAbi.word_bytes_field]
  intro same
  exact different (Option.some.inj same)

/-- The negative observation domain contains genuinely distinct typed words. -/
theorem distinct_word_inputs : Source.toWord 0 ≠ Source.toWord 1 := by decide +kernel

/-- Selector arguments, conversion and encoding share exact reached state. -/
def SelectorJoint (pipeline : Roadmap.Pipeline) (static : Bool) : Prop :=
  (Source.evalArgs (global pipeline) {frame with static:=static} 17
    SourceAbiControls.selectorArgs).run (locals,populated) =
    (.ok (.cons (.strLit SourceAbiControls.selectorBytes) (SourceAbiControls.values pipeline)),
      (.cons (.bool false) .nil,SourceKeccak.afterLiteral populated binary)) ∧
  (Source.convRV {frame with static:=static} 17 (.fixedBytes 4 (by decide +kernel))
    (.strLit SourceAbiControls.selectorBytes) : Source.EM E [.bool] _).run
      (.cons (.bool false) .nil,SourceKeccak.afterLiteral populated binary) =
    (.ok (.val (Source.mkBytes (n:=4) (h:=by decide +kernel) SourceAbiControls.selectorBytes)),
      (.cons (.bool false) .nil,SourceKeccak.afterLiteral populated binary)) ∧
  (Source.encodeVals {frame with static:=static} 17 false
    (SourceAbiControls.values pipeline) : Source.EM E [.bool] _).run
      (.cons (.bool false) .nil,SourceKeccak.afterLiteral populated binary) =
    (.ok (SourceAbiControls.data false pipeline),
      (.cons (.bool false) .nil,SourceKeccak.afterLiteral populated binary))

theorem selector_joint (pipeline : Roadmap.Pipeline) (static : Bool) :
    SelectorJoint pipeline static :=
  ⟨SourceAbiControls.selector_arguments_execute pipeline static, rfl,
    SourceAbiControls.encoding_execute pipeline static false⟩

theorem actual_selector (pipeline : Roadmap.Pipeline) (static : Bool) :
    (Source.evalE (global pipeline) {frame with static:=static} 18
      (.abiEncode .encodeWithSelector SourceAbiControls.selectorArgs)).run (locals,populated) =
    (.ok (.val (.memRef rfl 2)),(.cons (.bool false) .nil,
      SourceKeccak.afterLiteral (SourceKeccak.afterLiteral populated binary)
        (SourceAbiControls.selectorBytes ++ SourceAbiControls.data false pipeline))) := by
  have h := selector_joint pipeline static
  have result := SourceAbi.selector_execute (global pipeline) {frame with static:=static} 17
    SourceAbiControls.selectorArgs locals (.cons (.bool false) .nil)
    (.cons (.bool false) .nil) (.cons (.bool false) .nil) populated
    (SourceKeccak.afterLiteral populated binary) (SourceKeccak.afterLiteral populated binary)
    (SourceKeccak.afterLiteral populated binary) (.strLit SourceAbiControls.selectorBytes)
    (SourceAbiControls.values pipeline)
    (Source.mkBytes (n:=4) (h:=by decide +kernel) SourceAbiControls.selectorBytes)
    (SourceAbiControls.data false pipeline) h.1 h.2.1 h.2.2
  simpa only [SourceAbiControls.selector_value_bytes] using result

/-- Signature arguments, actual byte reading and encoding retain shared state. -/
def SignatureJoint (pipeline : Roadmap.Pipeline) (static : Bool) : Prop :=
  (Source.evalArgs (global pipeline) {frame with static:=static} 17
    SourceAbiControls.signatureArgs).run (locals,populated) =
    (.ok (.cons (.strLit []) (SourceAbiControls.values pipeline)),
      (.cons (.bool false) .nil,SourceKeccak.afterLiteral populated binary)) ∧
  (Source.bytesOfRV {frame with static:=static} 17 (.strLit []) : Source.EM E [.bool] _).run
      (.cons (.bool false) .nil,SourceKeccak.afterLiteral populated binary) =
    (.ok [],(.cons (.bool false) .nil,SourceKeccak.afterLiteral populated binary)) ∧
  (Source.encodeVals {frame with static:=static} 17 false
    (SourceAbiControls.values pipeline) : Source.EM E [.bool] _).run
      (.cons (.bool false) .nil,SourceKeccak.afterLiteral populated binary) =
    (.ok (SourceAbiControls.data false pipeline),
      (.cons (.bool false) .nil,SourceKeccak.afterLiteral populated binary))

theorem signature_joint (pipeline : Roadmap.Pipeline) (static : Bool) :
    SignatureJoint pipeline static :=
  ⟨SourceAbiControls.signature_arguments_execute pipeline static, rfl,
    SourceAbiControls.encoding_execute pipeline static false⟩

theorem actual_signature (pipeline : Roadmap.Pipeline) (static : Bool) :
    (Source.evalE (global pipeline) {frame with static:=static} 18
      (.abiEncode .encodeWithSignature SourceAbiControls.signatureArgs)).run (locals,populated) =
    (.ok (.val (.memRef rfl 2)),(.cons (.bool false) .nil,
      SourceKeccak.afterLiteral (SourceKeccak.afterLiteral populated binary)
        ((Source.wordBytes ((global pipeline).fixed.hash [])).take 4 ++
          SourceAbiControls.data false pipeline))) := by
  have h := signature_joint pipeline static
  exact SourceAbi.signature_execute (global pipeline) {frame with static:=static} 17
    SourceAbiControls.signatureArgs locals (.cons (.bool false) .nil)
    (.cons (.bool false) .nil) (.cons (.bool false) .nil) populated
    (SourceKeccak.afterLiteral populated binary) (SourceKeccak.afterLiteral populated binary)
    (SourceKeccak.afterLiteral populated binary) (.strLit []) (SourceAbiControls.values pipeline)
    [] (SourceAbiControls.data false pipeline) h.1 h.2.1 h.2.2

/-- Actual published pin suffices for arbitrary raw signature-byte prefixes. -/
theorem prefix_pin_joint (pipeline : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    (global pipeline).fixed.Keccak ∧
    (Source.wordBytes ((global pipeline).fixed.hash bytes)).take 4 =
      (Semantics.wordBytes (keccakBytes (bytes.map (fun byte => (byte.toNat : Int)))).1.toNat).take 4 :=
  ⟨Roadmap.Controls.toyFixed_keccak,
    SourceAbi.signature_prefix_transport (global pipeline) Roadmap.Controls.toyFixed_keccak bytes⟩

/-- Actual early argument timeout, before conversion/read/encoding/output allocation. -/
theorem prefix_argument_step (pipeline : Roadmap.Pipeline) (static : Bool) :
    (Source.evalArgs (global pipeline) {frame with static:=static} 6
      SourceAbiControls.selectorArgs).run (locals,populated) =
    (.error .timeout,(.cons (.bool false) .nil,populated)) := rfl

/-- Preserve original generic AbiKind quantifier on the reached argument failure. -/
theorem actual_prefix_failure (pipeline : Roadmap.Pipeline) (static : Bool) (kind : Source.AbiKind) :
    (Source.evalE (global pipeline) {frame with static:=static} 7
      (.abiEncode kind SourceAbiControls.selectorArgs)).run (locals,populated) =
    (.error .timeout,(.cons (.bool false) .nil,populated)) :=
  SourceAbi.prefixed_arguments_failure (global pipeline) {frame with static:=static} 6 kind
    SourceAbiControls.selectorArgs locals (.cons (.bool false) .nil) populated populated
    .timeout (prefix_argument_step pipeline static)

theorem prefix_failure_not_rollback (pipeline : Roadmap.Pipeline) (static : Bool) (kind : Source.AbiKind) :
    (Source.evalE (global pipeline) {frame with static:=static} 7
      (.abiEncode kind SourceAbiControls.selectorArgs)).run (locals,populated) ≠
      (.error .timeout,(locals,populated)) := by
  rw [actual_prefix_failure]
  intro same
  have localSame := congrArg (fun result => result.2.1.get .here) same
  cases localSame

/-- Literal ABI execution and both timeout boundaries share an actual populated
state. Raw literals allocate only the result, unlike the mixed hash fixture. -/
theorem literal_boundaries (pipeline : Roadmap.Pipeline) (static packed : Bool)
    (extra : Nat) (bytes : Roadmap.Bytes) :
    (Source.evalE (global pipeline) {frame with static:=static} (extra+4)
      (SourceAbi.literal packed bytes)).run (locals,populated) =
      (.ok (.val (.memRef rfl 1)),(locals,SourceKeccak.afterLiteral populated
        (if packed then bytes else Source.abiLayout [(true,bytes)]))) ∧
    (Source.evalE (global pipeline) {frame with static:=static} 0
      (SourceAbi.literal packed bytes)).run (locals,populated) =
      (.error .timeout,(locals,populated)) ∧
    (Source.evalE (global pipeline) {frame with static:=static} 1
      (SourceAbi.literal packed bytes)).run (locals,populated) =
      (.error .timeout,(locals,populated)) :=
  ⟨SourceAbi.literal_execution (global pipeline) {frame with static:=static}
      extra packed bytes locals populated,
    SourceAbi.zero_horizon (global pipeline) {frame with static:=static} packed bytes locals populated,
    SourceAbi.argument_horizon_zero (global pipeline) {frame with static:=static}
      packed bytes locals populated⟩

/-- Arbitrary selector/signature literal bytes retain exact normalization and
allocator pointer. They are not callable declarations or admission filters. -/
theorem prefixed_literal_boundaries (pipeline : Roadmap.Pipeline) (static : Bool)
    (extra : Nat) (selector signature bytes : Roadmap.Bytes) :
    (Source.evalE (global pipeline) {frame with static:=static} (extra+5)
      (SourceAbi.selectorLiteral selector bytes)).run (locals,populated) =
      (.ok (.val (.memRef rfl 1)),(locals,SourceKeccak.afterLiteral populated
        (Source.fitBytes 4 selector ++ Source.abiLayout [(true,bytes)]))) ∧
    (Source.evalE (global pipeline) {frame with static:=static} (extra+5)
      (SourceAbi.signatureLiteral signature bytes)).run (locals,populated) =
      (.ok (.val (.memRef rfl 1)),(locals,SourceKeccak.afterLiteral populated
        ((Source.wordBytes ((global pipeline).fixed.hash signature)).take 4 ++
          Source.abiLayout [(true,bytes)]))) :=
  ⟨SourceAbi.selector_literal_execution (global pipeline) {frame with static:=static}
      extra selector bytes locals populated,
    SourceAbi.signature_literal_execution (global pipeline) {frame with static:=static}
      extra signature bytes locals populated⟩

#print axioms literal_boundaries
#print axioms prefixed_literal_boundaries

#print axioms selector_joint
#print axioms actual_selector
#print axioms signature_joint
#print axioms actual_signature
#print axioms prefix_pin_joint
#print axioms prefix_argument_step
#print axioms actual_prefix_failure
#print axioms prefix_failure_not_rollback

#print axioms word_joint
#print axioms word_actual_run
#print axioms other_word_refused
#print axioms distinct_word_inputs

#print axioms joint
#print axioms actual
#print axioms timeout_after_effects
#print axioms timeout_not_rollback
#print axioms skipped_allocation_refused
end H62.AuditV08Adapters.SourceAbiJoint
