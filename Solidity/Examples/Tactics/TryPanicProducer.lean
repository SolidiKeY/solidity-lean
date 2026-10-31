import Solidity.Evm.TryPanicProducer

/-!
# M1 controls: computed source-linked witness versus a constructed call

No original source admission, bytecode run, callback change or expected EVM
bytes are used here. The constant-size constructed body below is deliberately
NOT the original f(uint) body. P4/P5b/P8 remain prerequisites for that claim.
-/
namespace Solidity.Examples.Tactics.TryPanicProducer
open Evm.TryByteImage Evm.TryPanicProducer
variable {C : Contract}

/-- Two siblings with equal call depth still have distinct keys. -/
theorem wrong_invocation (p : Pipeline) (n d : Nat) (σ : State C Input) :
    frameKey p (n + 1) d σ ≠ frameKey p n d σ := by
  intro h
  have bad := congrArg FrameKey.invocation h
  change n + 1 = n at bad
  omega

/-- Different pipelines cannot be exchanged because their payloads agree. -/
theorem wrong_pipeline (n d : Nat) (σ : State C Input) :
    frameKey .legacy n d σ ≠ frameKey .viaIR n d σ := by
  intro h
  have bad := congrArg FrameKey.pipeline h
  cases bad

/-- Reversing operations is refused by the whole source-plan certificate. -/
def reversedPlan (p : Pipeline) : StorePlan :=
  { originalPlan p with
    firstAt := at4
    firstWord := codeWord
    secondAt := at0
    secondWord := selectorWord }

/-- Original f stores at0 then4; equal bytes do not replace this source identity. -/
theorem wrong_order (p : Pipeline) : reversedPlan p ≠ originalPlan p := by
  intro h
  have bad := congrArg (fun pl : StorePlan => pl.firstAt.offset.val.toNat) h
  change (4 : Nat) = 0 at bad
  cases bad

/-- These specific source constants have zero overlap; reversed stores do
produce the same bytes. That observation cannot discharge source-order identity. -/
def reverseComputed36 : List UInt8 := List.ofFn fun i : Fin 36 =>
  if 0 ≤ i.val ∧ i.val < 32 then wordByte selectorWord i.val else
  if 4 ≤ i.val ∧ i.val < 36 then wordByte codeWord (i.val - 4) else 0

/-- The original zero overlap permits equal bytes for reversed stores. -/
theorem reversed_same_bytes : reverseComputed36 = computed36 := by decide +kernel

/-- A same-shaped call to a different declaration is not a source witness. -/
def wrongTargetPlan (p : Pipeline) : StorePlan :=
  { originalPlan p with source := { link p with callee := 8 } }

/-- Original this.f resolves declaration7, not a same-shaped declaration8. -/
theorem wrong_target (p : Pipeline) : wrongTargetPlan p ≠ originalPlan p := by
  intro h
  have bad := congrArg (fun pl : StorePlan => pl.source.callee) h
  change (8 : Nat) = 7 at bad
  cases bad

/-- A reused declaration number in different source bytes is also refused. -/
def wrongSourcePlan (p : Pipeline) : StorePlan :=
  { originalPlan p with source :=
    { link p with bundle := { (link p).bundle with source := "contract Wrong {}" } } }

/-- Original declaration7 in another source unit body is not this bundle. -/
theorem wrong_source (p : Pipeline) : wrongSourcePlan p ≠ originalPlan p := by
  intro h
  have bad := congrArg (fun pl : StorePlan => pl.source.bundle.source) h
  cases p <;> exact (by decide : "contract Wrong {}" ≠ originalSource) bad

/-- A wrong parameter value cannot furnish the M1 size-entry witness. This
is certificate refusal, not a new execution verdict for general f(size). -/
theorem wrong_size (σ : State C []) :
    TEnv.get sizeSlot (σ.push (t := .val .uint) codeWord).env ≠ size36 := by
  intro h
  have bad := congrArg (fun w : U256 => w.val.toNat) h
  change (67 : Nat) = 36 at bad
  cases bad

/-- Synthetic overlap that really is order-sensitive: no false countermodel
is inferred from the original selector's zero overlap. -/
theorem last_writer_control (σ : State C Input) (k : FrameKey) :
    (store32 (store32 (fresh σ k) at0 codeWord) at0 freeWord).data
      ⟨31, by change 31 < 96; decide⟩ = 128 := by
  rw [overlap_last _ _ _ _ _ _ (by change 0 ≤ 31 ∧ 31 < 32; decide)]
  change wordByte freeWord 31 = 128
  decide +kernel

/-- Unaligned write at4 places the actual code at35, not31 or36. -/
theorem code_byte_order (σ : State C Input) (k : FrameKey) :
    (image σ k).data ⟨35, by change 35 < 96; decide⟩ = 67 ∧
    (image σ k).data ⟨36, by change 36 < 96; decide⟩ = 0 := by
  constructor <;>
    (simp only [image, entry, store32, fresh, at0, at4, at64, zero,
      Int.reduceToNat, Nat.reduceAdd]; rfl)

/-- Short complete-prefix data is not accepted as a Panic word. -/
theorem short_refused : Semantics.decodePanic (computed36.take 35) = none := by decide +kernel

/-- The approved decoder keeps its trailing-data behavior without changing
or re-encoding the raw producer halt. -/
theorem trailing_decodes : Semantics.decodePanic (computed36 ++ [0]) = some codeWord := by
  decide +kernel

/-- Wrong selector and empty payload remain undecoded. -/
theorem wrong_selector_refused : Semantics.decodePanic (computed36.drop 1) = none := by
  decide +kernel

/-- An empty halt has no Panic selector or code. -/
theorem empty_refused : Semantics.decodePanic [] = none := by decide +kernel

/-- Wrong decoded postcondition is actually false. -/
theorem wrong_code : Semantics.decodePanic computed36 ≠ some size36 := by
  rw [computed36_decode]
  intro h
  have bad := congrArg (fun w : U256 => w.val.toNat) (Option.some.inj h)
  change (67 : Nat) = 36 at bad
  cases bad

/-- Byte95 distinguishes a wrong free-word initialization from the true entry,
even though the original36-byte observation does not inspect that byte. -/
def peek95 (μ : FrameMem C Input) : Option UInt8 :=
  if h : 95 < μ.capacity then some (μ.data ⟨95, h⟩) else none

def wrongInit (σ : State C Input) (k : FrameKey) : FrameMem C Input :=
  store32 (fresh σ k) at64 ⟨64, rfl⟩

/-- A free pointer64 cannot certify the original mstore(64,128) entry. -/
theorem wrong_initialization (σ : State C Input) (k : FrameKey) :
    ¬ InitialFor σ k (wrongInit σ k) := by
  intro h
  have bad := congrArg peek95 h
  have h64 : peek95 (wrongInit σ k) = some 64 := by
    simp only [peek95, wrongInit, store32, fresh, at64, Int.reduceToNat, Nat.reduceAdd]
    rfl
  have h128 : peek95 (entry σ k) = some 128 := by
    simp only [peek95, entry, store32, fresh, at64, Int.reduceToNat, Nat.reduceAdd]
    rfl
  rw [h64, h128] at bad
  cases bad

/-- The bytes-to-typed consumer retains exact empty-data normalization. -/
theorem empty_halt (σ : State C Input) :
    bytesHalt [] (by decide) σ = .error .revert := bytesHalt_exact _ _ _

/-- A producer-only256-byte image control preserves initialized byte95. This
is a pure expanded-capacity snapshot, NOT target REVERT/gas correspondence. -/
def longSpan : ByteSpan (96 + 5 * 32) := ⟨zero, ⟨256, rfl⟩, .inr (by decide)⟩

theorem long_length (σ : State C Input) (k : FrameKey) :
    (snapshot (expandZero (image σ k) 5) longSpan).length = 256 := snapshot_length _ _

theorem long_initialized_byte (σ : State C Input) (k : FrameKey) :
    (snapshot (expandZero (image σ k) 5) longSpan)[95]'(by
      rw [long_length]; decide) = 128 := by
  rw [snapshot_get]
  change (expandZero (image σ k) 5).data ⟨95, by change 95 < 256; decide⟩ = 128
  rw [expandZero_old (image σ k) 5 ⟨95, by change 95 < 96; decide⟩]
  exact initialized_word σ k

/-- Constructed constant-size body control. It sets its own scalar temporary
and uses the computed producer; this is explicitly NOT a source f(uint) import. -/
def constructedBody (p : Pipeline) (n depth : Nat) : TStep C Input (.mem bytesR :: Input) :=
  fun σ => producer36 (frameKey p n depth σ) (σ.setLocal sizeSlot size36) rfl

/-- The manual constant36 body runs the computed producer and has its raw halt. -/
theorem constructedBody_halt (p : Pipeline) (n depth : Nat) (σ : State C Input) :
    constructedBody p n depth σ = .error (THalt.ofData computed36) :=
  producer36_halt _ _ rfl

def args36 : Args C Γ Input := .snoc .nil .uint (.user "size") (.simple (.lit 36 rfl))

/-- An actual intrinsic call evaluates36, enters the return/parameter frame
and runs the constructed body. No oracle/assumed hcall supplies the result. -/
theorem constructed_call_halt (p : Pipeline) (n depth : Nat) (σ : State C Γ) :
    TRun.call args36 (.rets .nil) (.push .refl) (constructedBody p n depth) σ =
      .error (THalt.ofData computed36) := by
  unfold TRun.call
  simp only [Args.evalT, args36, Val.evalT, Simple.evalT, bind, Except.bind,
    pure, Except.pure]
  rw [constructedBody_halt]

/-- The manually constructed call retains its raw bytes through self catch. -/
def call7 : ExtCall C Γ := ⟨.lit 7 rfl, "f", [⟨.uint, .lit 36 rfl⟩]⟩

/-- The manual self call catches its own computed bytes with self=true. -/
theorem constructed_raw_catch (p : Pipeline) (n depth : Nat) (σ : State C Γ)
    (hself : σ.tx.selfAddress.val = 7) :
    TRun.catchBytes call7 .nil args36 (.push .refl) (constructedBody p n depth) true σ =
      .ok computed36 := by
  apply TRun.catchBytes_self_data
  · change (7 : Int) ≠ 0; decide
  · exact hself.symm
  · exact constructed_call_halt p n depth σ

/-- Panic scalar capture copies the actual code to a caller return slot.
The caller heap/globals, self flag and handler scope are retained by tryCall. -/
def handler : TStep C [.val .uint, .val .uint] [.val .uint, .val .uint] :=
  TRun.assignLocal (.there .here) (.simple (.local .here))

def failClause : TStep C Γ Γ := TRun.assert (.simple (.bool false))

def constructedTry (p : Pipeline) (n depth : Nat) (self : Bool) : TStep C Input Input :=
  TRun.tryCall call7 .nil .refl failClause .refl failClause (.some (.user "c"))
    .refl handler .refl failClause args36 (.push .refl) (constructedBody p n depth) self

/-- Original terminal revert carries nonempty raw bytes, not a primitive panic. -/
theorem raw_halt : THalt.ofData computed36 = .revertWith computed36 := by
  rw [computed36_panic]
  rfl

/-- The computed Panic selector is not an Error(string) selector. -/
theorem no_error_decode : Semantics.decodeError computed36 = none := by decide +kernel

/-- Constructed self try binds67, writes its actual return slot, drops catch
scope and rolls back the callee's ghost allocation to the original caller heap. -/
theorem constructed_return (p : Pipeline) (n depth : Nat) (σ : State C Input)
    (hself : σ.tx.selfAddress.val = 7) :
    constructedTry p n depth true σ = .ok ⟨σ.setLocal .here codeWord, List.prefix_refl _⟩ := by
  have hc := constructed_call_halt p n depth σ
  rw [raw_halt] at hc
  have hs : (call7.addr.evalT σ).val = σ.tx.selfAddress.val := hself.symm
  have hzero : σ.tx.selfAddress.val ≠ 0 := by rw [hself]; decide
  simp only [constructedTry, TRun.tryCall, hs, decide_true,
    Bool.true_and, hc, no_error_decode, computed36_decode, if_neg hzero, if_true]
  rfl

/-- Without self dispatch and without an actual oracle entry, the constructed
callee must not be replayed as an external response. -/
theorem self_flag_required (p : Pipeline) (n depth : Nat) (σ : State C Input)
    (hempty : σ.tx.ext = []) :
    constructedTry p n depth false σ = .error .revert := by
  have hz : (call7.addr.evalT σ).val ≠ 0 := by change (7 : Int) ≠ 0; decide
  simp only [constructedTry, TRun.tryCall, hz, if_false, Bool.false_and,
    Bool.false_eq_true, hempty, Semantics.lookupBy]

/-- Zero-length snapshot needs no address access, even at the largest uint. -/
def emptyHuge : ByteSpan 96 :=
  ⟨⟨((2 ^ 256 - 1 : Nat) : Int),
    PrimTy.inRange_uint_of_lt (Nat.sub_lt (Nat.two_pow_pos 256) (by decide))⟩,
    zero, .inl rfl⟩

/-- Synthetic revert(maxUint,0) reads no cell and returns empty bytes. -/
theorem empty_outside_capacity (σ : State C Input) (k : FrameKey) :
    snapshot (image σ k) emptyHuge = [] := snapshot_empty _ _ rfl

/-- Natural interval bounds cannot silently wrap past the end of capacity. -/
theorem overflowing_slice_refused (s : ByteSpan 96)
    (ha : s.offset.val.toNat = 95) (hn : s.length.val.toNat = 2) : False := by
  rcases s.fits with h | h <;> omega

/-- The producer-only long suffix is zero-filled, not supplied by a reference. -/
theorem long_zero_suffix (σ : State C Input) (k : FrameKey) (i : Nat)
    (hlo : 96 ≤ i) (hhi : i < 256) :
    (snapshot (expandZero (image σ k) 5) longSpan)[i]'(by rw [long_length]; exact hhi) = 0 := by
  rw [snapshot_get]
  simpa only [longSpan, zero, Int.reduceToNat, Nat.zero_add] using
    (expandZero_new (image σ k) 5 ⟨i, by change i < 256; exact hhi⟩ hlo)

/-- The zero receiver fails before any body/catch dispatch, unchanged. -/
theorem zero_receiver_refused (p : Pipeline) (n depth : Nat) (σ : State C Input) :
    TRun.catchBytes (⟨.lit 0 rfl, "f", []⟩ : ExtCall C Input) .nil args36
      (.push .refl) (constructedBody p n depth) true σ = .error .revert := rfl

/-- An unexpected receiver cannot reuse the constructed self-call proof. -/
theorem wrong_receiver_refused (p : Pipeline) (n depth : Nat) (σ : State C Input)
    (hs : σ.tx.selfAddress.val = 8) (he : σ.tx.ext = []) :
    TRun.catchBytes call7 .nil args36 (.push .refl) (constructedBody p n depth) true σ =
      .error .revert := by
  simp only [TRun.catchBytes, call7, Simple.evalT, hs, he, Semantics.lookupBy]
  rfl

/-- Concrete nonzero-self input inhabits the constructed return theorem. -/
def concreteInput (C : Contract) : State C Input :=
  ({ State.init C with tx := { selfAddress := ⟨7, rfl⟩, msgSender := ⟨9, rfl⟩ } }).push zero

/-- Both pipeline-tagged controls construct a normal result, not just a
conditional theorem whose receiver premises might have no witness. -/
theorem both_constructed_returns (C : Contract) :
    constructedTry .legacy 1 1 true (concreteInput C) =
      .ok ⟨(concreteInput C).setLocal .here codeWord, List.prefix_refl _⟩ ∧
    constructedTry .viaIR 1 1 true (concreteInput C) =
      .ok ⟨(concreteInput C).setLocal .here codeWord, List.prefix_refl _⟩ :=
  ⟨constructed_return _ _ _ _ rfl, constructed_return _ _ _ _ rfl⟩

/-- Two actual caller memory locals alias one preexisting typed object. They
are not passed into the scalar callee or laid out in its fresh byte image. -/
def aliasCaller (C : Contract) : State C [.mem bytesR, .mem bytesR] :=
  let σ : State C [] := { State.init C with tx := { selfAddress := ⟨7, rfl⟩ } }
  let a := σ.alloc (bytesObj σ.H [9] (by decide))
  (a.1.push (t := .mem bytesR) (some a.2)).push (t := .mem bytesR) (some a.2)

/-- The self-call raw-data witness is nonvacuous with real live caller aliases. -/
theorem aliases_raw_catch (C : Contract) (p : Pipeline) :
    TRun.catchBytes call7 .nil args36 (.push .refl) (constructedBody p 1 1) true (aliasCaller C) =
      .ok computed36 := constructed_raw_catch p 1 1 _ rfl

/-- A subsequent typed capture keeps both old alias IDs equal; it does not
redirect either local to the new immutable snapshot object. -/
theorem capture_aliases (C : Contract) :
    let σ := aliasCaller C
    let τ := σ.allocPush (bytesObj σ.H computed36 (by rw [computed36_length]; decide))
    TEnv.get (.there .here) τ.env = TEnv.get (.there (.there .here)) τ.env := rfl

/-- Actual old object exists at0 and fresh computed capture has identity1. -/
theorem capture_identity_nonvacuous (C : Contract) :
    ((aliasCaller C).alloc (bytesObj (aliasCaller C).H computed36
      (by rw [computed36_length]; decide))).2.id = 1 := rfl

end Solidity.Examples.Tactics.TryPanicProducer
