import Solidity.Backend.AbiWorld.ReturnedBytesPrefix

/-! Finite actual compiler applications, after the separately checked nonempty prefix. -/
namespace Solidity.Backend.AbiWorld.ReturnedBytesControls
open Evm Evm.Memory ReturnedBytes

private def body (n : Nat) (escape : Bool) (hn : n < 2 ^ 256) :
    Prog C [.mem bytesR, .mem bytesR] [.val .bool, .mem bytesR, .mem bytesR] :=
  .cons (.rebindMem .here (if escape then .newArr (.lit n (PrimTy.inRange_uint_of_lt hn)) rfl
    else .alias (.var (.there .here) rfl)))
  (if 0 < n && escape then
    .cons (litWrite (n - 1) (by omega) 255)
      (.cons (.declLocal .bool (.user "private") (some (.simple (.bool true)))) .nil)
   else .cons (.declLocal .bool (.user "private") (some (.simple (.bool true)))) .nil)
private def stage (n : Nat) (escape : Bool) (hn : n < 2 ^ 256) : Prog C Entry Output :=
  .cons (.declMem bytesR (.user "argument")
    (some (.newArr (.lit n (PrimTy.inRange_uint_of_lt hn)) rfl)) rfl rfl)
  ((if 0 < n then .cons (litWrite (n - 1) (by omega) 255) else fun k => k)
    (.cons (.call "returnBytes" (.snocMemory .nil bytesR (.user "arg") (.var .here rfl))
      (.mem bytesR (.user "result") rfl rfl) (body n escape hn))
    (if 0 < n then .cons (litWrite 0 (by decide +kernel) 7) .nil else .nil)))

private def argument (n : Nat) : List UInt8 :=
  if 0 < n then (List.replicate n 0).set (n - 1) 255 else []
private def expected (n : Nat) : List UInt8 := if 0 < n then (argument n).set 0 7 else []

private def summary (o : Solidity.Out C entry.st.H Output) : Option (List Nat × List UInt8 × List UInt8) := do
  let a ← TEnv.get (.there .here) o.st.env
  let old ← TEnv.get (.there (.there .here)) o.st.env
  let ret ← TEnv.get .here o.st.env
  let saved ← ((Val.read (.root "saved" rfl) : Val C Output .uint).evalT o.st).toOption
  pure ([o.st.H.length, old.id, a.id, ret.id,
    (TEnv.get (.there (.there (.there .here))) o.st.env).1.toNat, saved.1.toNat],
    ReturnedBytes.payload o.st.heap old, ReturnedBytes.payload o.st.heap a)

private theorem range_of_all {H : HTy} {hp : Heap H} {r : HRef H bytesR}
    (h : (hp.get r).1.all (fun v => decide (v.1.toNat < 256)) = true) : ByteRange hp r :=
  fun v hv => of_decide_eq_true ((List.all_eq_true.mp h) v hv)

private theorem reference_eq_of_id {H : HTy} {R : RefTy} (x : Option (HRef H R))
    (r : HRef H R) (h : x.map HRef.id = some r.id) : x = some r := by
  cases x with
  | none => cases h
  | some s =>
    have he : s.id = r.id := Option.some.inj h
    exact congrArg some (eq_of_heq (HRef.heq_of_id s r he).2)

/-- Finite fixture data carries actual typed programs/certificates and discharged
facts; it is not a new language or a general compilation/admission restriction. -/
private structure Fixture where
  n : Nat
  escape : Bool
  bound : n < 2 ^ 256
  cert : Compiler.Compilation 1 prefixCert.frag (stage n escape bound)
  memoryCalls : cert.isMemoryCalls = true
  need : cert.requiredFrame = 6
  cost : cert.allocationCost entry.st = if escape then 2 * n + 3 else n + 2
  space : prefixCursor.val + (if escape then 2 * n + 3 else n + 2) < W
  out : Solidity.Out C entry.st.H Output
  run : (stage n escape bound).run entry.st = .ok out
  noPay : Evm.Prog.pays (stage n escape bound) = false
  ref : HRef out.st.H bytesR
  get : TEnv.get .here out.st.env = some ref
  bytes : ReturnedBytes.payload out.st.heap ref = expected n
  byteRange : ByteRange out.st.heap ref
  length : out.st.heap.len ref .dyn = n
  shape : summary out = some ([if escape then 4 else 3, 0, 1, if escape then 3 else 1, 42, 9],
    [161, 178], if escape then argument n else expected n)

private def emptyCert : Compiler.Compilation 1 prefixCert.frag (stage 0 false (by decide +kernel)) :=
  (Compiler.compile 1 prefixCert.frag (stage 0 false (by decide +kernel))).get (by decide +kernel)
private def emptyOut : Solidity.Out C entry.st.H Output :=
  (((stage 0 false (by decide +kernel)).run entry.st).toOption).get (by decide +kernel)
attribute [irreducible] emptyCert emptyOut

private def empty : Fixture where
  n := 0
  escape := false
  bound := by decide +kernel
  cert := emptyCert
  memoryCalls := by decide +kernel
  need := by decide +kernel
  cost := by decide +kernel
  space := by decide +kernel
  out := emptyOut
  run := by unfold emptyOut; exact source_get _ (by decide +kernel)
  noPay := by decide +kernel
  ref := ⟨1, by decide +kernel⟩
  get := reference_eq_of_id _ _ (by decide +kernel)
  bytes := by decide +kernel
  byteRange := range_of_all (by decide +kernel)
  length := by decide +kernel
  shape := by decide +kernel

private def threeCert : Compiler.Compilation 1 prefixCert.frag (stage 3 false (by decide +kernel)) :=
  (Compiler.compile 1 prefixCert.frag (stage 3 false (by decide +kernel))).get (by decide +kernel)
private def threeOut : Solidity.Out C entry.st.H Output :=
  (((stage 3 false (by decide +kernel)).run entry.st).toOption).get (by decide +kernel)
attribute [irreducible] threeCert threeOut

private def three : Fixture where
  n := 3
  escape := false
  bound := by decide +kernel
  cert := threeCert
  memoryCalls := by decide +kernel
  need := by decide +kernel
  cost := by decide +kernel
  space := by decide +kernel
  out := threeOut
  run := by unfold threeOut; exact source_get _ (by decide +kernel)
  noPay := by decide +kernel
  ref := ⟨1, by decide +kernel⟩
  get := reference_eq_of_id _ _ (by decide +kernel)
  bytes := by decide +kernel
  byteRange := range_of_all (by decide +kernel)
  length := by decide +kernel
  shape := by decide +kernel

private def b31Cert : Compiler.Compilation 1 prefixCert.frag (stage 31 false (by decide +kernel)) :=
  (Compiler.compile 1 prefixCert.frag (stage 31 false (by decide +kernel))).get (by decide +kernel)
private def b31Out : Solidity.Out C entry.st.H Output :=
  (((stage 31 false (by decide +kernel)).run entry.st).toOption).get (by decide +kernel)
attribute [irreducible] b31Cert b31Out

private def b31 : Fixture where
  n := 31
  escape := false
  bound := by decide +kernel
  cert := b31Cert
  memoryCalls := by decide +kernel
  need := by decide +kernel
  cost := by decide +kernel
  space := by decide +kernel
  out := b31Out
  run := by unfold b31Out; exact source_get _ (by decide +kernel)
  noPay := by decide +kernel
  ref := ⟨1, by decide +kernel⟩
  get := reference_eq_of_id _ _ (by decide +kernel)
  bytes := by decide +kernel
  byteRange := range_of_all (by decide +kernel)
  length := by decide +kernel
  shape := by decide +kernel

private def b32Cert : Compiler.Compilation 1 prefixCert.frag (stage 32 false (by decide +kernel)) :=
  (Compiler.compile 1 prefixCert.frag (stage 32 false (by decide +kernel))).get (by decide +kernel)
private def b32Out : Solidity.Out C entry.st.H Output :=
  (((stage 32 false (by decide +kernel)).run entry.st).toOption).get (by decide +kernel)
attribute [irreducible] b32Cert b32Out

private def b32 : Fixture where
  n := 32
  escape := false
  bound := by decide +kernel
  cert := b32Cert
  memoryCalls := by decide +kernel
  need := by decide +kernel
  cost := by decide +kernel
  space := by decide +kernel
  out := b32Out
  run := by unfold b32Out; exact source_get _ (by decide +kernel)
  noPay := by decide +kernel
  ref := ⟨1, by decide +kernel⟩
  get := reference_eq_of_id _ _ (by decide +kernel)
  bytes := by decide +kernel
  byteRange := range_of_all (by decide +kernel)
  length := by decide +kernel
  shape := by decide +kernel

private def b33Cert : Compiler.Compilation 1 prefixCert.frag (stage 33 false (by decide +kernel)) :=
  (Compiler.compile 1 prefixCert.frag (stage 33 false (by decide +kernel))).get (by decide +kernel)
private def b33Out : Solidity.Out C entry.st.H Output :=
  (((stage 33 false (by decide +kernel)).run entry.st).toOption).get (by decide +kernel)
attribute [irreducible] b33Cert b33Out

private def b33 : Fixture where
  n := 33
  escape := false
  bound := by decide +kernel
  cert := b33Cert
  memoryCalls := by decide +kernel
  need := by decide +kernel
  cost := by decide +kernel
  space := by decide +kernel
  out := b33Out
  run := by unfold b33Out; exact source_get _ (by decide +kernel)
  noPay := by decide +kernel
  ref := ⟨1, by decide +kernel⟩
  get := reference_eq_of_id _ _ (by decide +kernel)
  bytes := by decide +kernel
  byteRange := range_of_all (by decide +kernel)
  length := by decide +kernel
  shape := by decide +kernel

private def escape33Cert : Compiler.Compilation 1 prefixCert.frag (stage 33 true (by decide +kernel)) :=
  (Compiler.compile 1 prefixCert.frag (stage 33 true (by decide +kernel))).get (by decide +kernel)
private def escape33Out : Solidity.Out C entry.st.H Output :=
  (((stage 33 true (by decide +kernel)).run entry.st).toOption).get (by decide +kernel)
attribute [irreducible] escape33Cert escape33Out

private def escape33 : Fixture where
  n := 33
  escape := true
  bound := by decide +kernel
  cert := escape33Cert
  memoryCalls := by decide +kernel
  need := by decide +kernel
  cost := by decide +kernel
  space := by decide +kernel
  out := escape33Out
  run := by unfold escape33Out; exact source_get _ (by decide +kernel)
  noPay := by decide +kernel
  ref := ⟨3, by decide +kernel⟩
  get := reference_eq_of_id _ _ (by decide +kernel)
  bytes := by decide +kernel
  byteRange := range_of_all (by decide +kernel)
  length := by decide +kernel
  shape := by decide +kernel

private def ErrorFacts (bs : List UInt8) : Prop :=
    ((Source.errorData bs).drop 4).take 32 = Semantics.wordBytes 32 ∧
    ((Source.errorData bs).drop 36).take 32 = Semantics.wordBytes bs.length ∧
    ((Source.errorData bs).drop 68).take bs.length = bs ∧
    (Source.errorData bs).drop (68 + bs.length) =
      List.replicate ((32 - bs.length % 32) % 32) 0 ∧
    CatchKind.reason.decode (Source.errorData bs) = some bs

private theorem fixture_error (f : Fixture) : ErrorFacts (expected f.n) := by
  have hn : (expected f.n).length < 2 ^ 256 := by
    rw [← f.bytes, payload_length]
    exact f.out.st.heap.len_dyn_lt f.ref
  exact (error_observations _ hn).2

private def growCursor (f : Fixture) : Fin W :=
  ⟨prefixCursor.val + f.cert.allocationCost entry.st, by rw [f.cost]; exact f.space⟩

/-- The application retains exact represented frame, allocator, old typed address,
complete bytes and catch observation from the actual public compiler branch. -/
private def Application (f : Fixture) (base : Nat → Fin W) : Prop :=
  ∃ m' base', Evm.run f.cert.code prefixMachine = .ok m' 0 ∧
    m'.stack = prefixMachine.stack ∧
    StateRepr 1 1 128 f.cert.frag f.out.st base' m' ∧
    BaseExtends entry.st.H base base' ∧ base' oldRef.id = base oldRef.id ∧
    GrowsAllocator 1 128 (f.cert.allocationCost entry.st) entry.st base prefixMachine f.out.st base' m' ∧
    localBytes m' 1 (.here : Idx Output (.mem bytesR)) = some (expected f.n) ∧
    (localBytes m' 1 (.here : Idx Output (.mem bytesR))).bind
      (fun bs => CatchKind.reason.decode (Source.errorData bs)) = some (expected f.n) ∧ ErrorFacts (expected f.n) ∧
    StructAllocatorRepr f.out.st.heap base' 128 (growCursor f) m'

private theorem apply_fixture (f : Fixture) (base : Nat → Fin W)
    (hs : StateRepr 1 1 128 prefixCert.frag entry.st base prefixMachine)
    (ha : StructAllocatorRepr entry.st.heap base 128 prefixCursor prefixMachine) : Application f base := by
  have hi : f.cert.Input 1 128 base entry.st prefixMachine := by
    apply (f.cert.memoryCalls_input f.memoryCalls 1 128 base entry.st prefixMachine).mpr
    refine ⟨hs, ?_, .inr ⟨by decide, prefixCursor, ha, ?_⟩⟩
    · rw [f.need]; decide
    · rw [f.cost]; exact f.space
  obtain ⟨m', base', ht, hk, hr, hb, hg, hbytes, hcatch⟩ := compiled_return f.cert f.memoryCalls
    hi f.noPay f.out f.run .here f.ref f.get f.byteRange
  rw [f.bytes] at hbytes hcatch
  have ha' : StructAllocatorRepr f.out.st.heap base' 128 (growCursor f) m' := by
    unfold growCursor
    exact hg prefixCursor (by decide) ha (by rw [f.cost]; exact f.space)
  exact ⟨m', base', ht, hk, hr, hb, hb oldRef, hg, hbytes, hcatch, fixture_error f, ha'⟩

/-- All six actual compiled applications start from a real nonempty setup
execution. In particular BaseExtends is instantiated at the real old object0. -/
theorem nonempty_applications : ∃ base,
    Evm.run prefixCert.code machine = .ok prefixMachine 0 ∧
    StateRepr 1 1 128 prefixCert.frag entry.st base prefixMachine ∧
    entry.st.H.length = 1 ∧ oldRef.id = 0 ∧ prefixMachine.stack = [w[77]] ∧
    Application empty base ∧ Application three base ∧ Application b31 base ∧
    Application b32 base ∧ Application b33 base ∧ Application escape33 base := by
  obtain ⟨base, ht, hs, ha, hk⟩ := nonempty_entry
  exact ⟨base, ht, hs, by decide +kernel, rfl, hk,
    apply_fixture _ _ hs ha, apply_fixture _ _ hs ha, apply_fixture _ _ hs ha,
    apply_fixture _ _ hs ha, apply_fixture _ _ hs ha, apply_fixture _ _ hs ha⟩

private def fixtures : List Fixture := [empty, three, b31, b32, b33, escape33]
private def terminal (f : Fixture) : Machine :=
  match Evm.run f.cert.code prefixMachine with | .ok m _ => m | _ => prefixMachine

private theorem terminal_run (f : Fixture) : Evm.run f.cert.code prefixMachine = .ok (terminal f) 0 := by
  obtain ⟨base, ht, hs, ha, hk⟩ := nonempty_entry
  obtain ⟨m', base', ht', _⟩ := apply_fixture f base hs ha
  rw [terminal, ht']

private theorem observed (f : Fixture) :
    localBytes (terminal f) 1 (.here : Idx Output (.mem bytesR)) = some (expected f.n) := by
  obtain ⟨base, ht, hs, ha, hk⟩ := nonempty_entry
  obtain ⟨m', base', ht', hk', hr, hb, hold, hg, hbytes, _⟩ := apply_fixture f base hs ha
  rw [terminal, ht']
  exact hbytes

/-- Complete finite payloads, including all zeros and both word boundaries,
are applications of the uniform theorem, not just fixed head/tail samples. -/
theorem complete_payloads :
    fixtures.map (fun f => localBytes (terminal f) 1 (.here : Idx Output (.mem bytesR))) =
      [some [], some [7, 0, 255], some (expected 31), some (expected 32),
        some (expected 33), some (expected 33)] := by
  simp only [fixtures, List.map_cons, List.map_nil, observed]
  rfl

/-- Every finite actual application has all Error offset/length/complete data/
zero-padding/catch facts, not merely a standalone three-cell decode pair. -/
theorem finite_packet_facts : ∀ f ∈ fixtures, ErrorFacts (expected f.n) :=
  fun f _ => fixture_error f

theorem finite_source_observations : fixtures.map (fun f => summary f.out) =
    [some ([3,0,1,1,42,9], [161,178], []),
     some ([3,0,1,1,42,9], [161,178], expected 3),
     some ([3,0,1,1,42,9], [161,178], expected 31),
     some ([3,0,1,1,42,9], [161,178], expected 32),
     some ([3,0,1,1,42,9], [161,178], expected 33),
     some ([4,0,1,3,42,9], [161,178], argument 33)] := by
  simp only [fixtures, List.map_cons, List.map_nil, empty.shape, three.shape,
    b31.shape, b32.shape, b33.shape, escape33.shape]
  rfl

private theorem resource_row (f : Fixture) :
    (f.cert.requiredFrame, f.cert.allocationCost entry.st, (growCursor f).val) =
      (6, if f.escape then 2*f.n+3 else f.n+2,
        prefixCursor.val + (if f.escape then 2*f.n+3 else f.n+2)) := by
  change (_, _, prefixCursor.val + _) = _
  rw [f.need, f.cost]

/-- Actual expanded frame, reached stage cost and final cursor for all cases.
The old object is already allocated when these stage costs begin at259. -/
theorem finite_resources : fixtures.map
    (fun f => (f.cert.requiredFrame, f.cert.allocationCost entry.st, (growCursor f).val)) =
      [(6,2,261),(6,5,264),(6,33,292),(6,34,293),(6,35,294),(6,69,328)] := by
  simp only [fixtures, List.map_cons, List.map_nil, resource_row, prefix_resources.2]
  rfl

theorem finite_packet_sizes : fixtures.map
    (fun f => ((expected f.n).length, (Source.errorData (expected f.n)).length,
      ((32 - (expected f.n).length % 32) % 32))) =
      [(0,68,0),(3,100,29),(31,100,1),(32,100,0),(33,132,31),(33,132,31)] := by decide +kernel

/-- Exact pointer/header baseline and older object/scalar/store/stack sentinel. -/
theorem target_baseline :
    (terminal b33).mem 4 = w[259] ∧ (terminal b33).mem 259 = w[33] ∧
    (terminal escape33).mem 4 = w[294] ∧ (terminal escape33).mem 294 = w[33] ∧
    (terminal b33).mem 2 = w[256] ∧ (terminal b33).mem 1 = w[42] ∧
    (terminal b33).mem 127 = w[99] ∧ (terminal b33).store (.root 0) = 9 ∧
    (terminal b33).stack = [w[77]] := by decide +kernel

/-- Numeric wrong headers/pointers can observe different VALID data. These
controls reject wrong claims, not impose new calldata or pointer admission. -/
theorem wrong_length_pointer_order :
    localBytes (writeMachine (terminal b33) 259 w[32]) 1 (.here : Idx Output (.mem bytesR)) ≠
      some (expected 33) ∧
    localBytes (writeMachine (terminal b33) 4 w[256]) 1 (.here : Idx Output (.mem bytesR)) =
      some [161,178] ∧
    localBytes (writeMachine (writeMachine (terminal b33) 260 w[255]) 292 w[7])
      1 (.here : Idx Output (.mem bytesR)) ≠ some (expected 33) := by decide +kernel

/-- Range and symbolic cells refuse observation. Compiler acceptance of word300
remains covered by the unchanged prior wide_agrees/byte_observation_negatives. -/
theorem invalid_cell_observations :
    localBytes (writeMachine (terminal b33) 261 w[300]) 1 (.here : Idx Output (.mem bytesR)) = none ∧
    byteCell w[300] = none ∧ byteCell (.slot (.root 0)) = none := by decide +kernel

theorem wrong_catch_and_offset_claims :
    Semantics.decodePanic (Source.errorData (expected 33)) = none ∧
    ((Source.errorData (expected 33)).drop 4).take 32 ≠ Semantics.wordBytes 64 ∧
    CatchKind.raw.decode (Source.errorData (expected 33)) ≠ some (expected 33) := by
  refine ⟨error_not_panic _, ?_, ?_⟩
  · rw [PublishedLayout.source_error_bytes, error_offset]
    decide +kernel
  · decide +kernel

private theorem observed_packet (f : Fixture) :
    (localBytes (terminal f) 1 (.here : Idx Output (.mem bytesR))).map Source.errorData =
      some (Source.errorData (expected f.n)) := by rw [observed]; rfl

/-- Complete actual observed payloads logically feed the existing Error encoder;
no instruction emission or byte-addressed execution is asserted. -/
theorem observed_error_packets : fixtures.map (fun f =>
    (localBytes (terminal f) 1 (.here : Idx Output (.mem bytesR))).map Source.errorData) =
      fixtures.map (fun f => some (Source.errorData (expected f.n))) := by
  apply List.map_congr_left
  intro f hf
  exact observed_packet f

private def wideStage : Prog C Entry Output :=
  .cons (.declMem bytesR (.user "argument") (some (.newArr (.lit 3 rfl) rfl)) rfl rfl)
  (.cons (.assignMem (litLoc 1 (by decide +kernel)) (.val (u 300)))
  (.cons (.call "returnWideWord" (.snocMemory .nil bytesR (.user "arg") (.var .here rfl))
    (.mem bytesR (.user "result") rfl rfl) (body 3 false (by decide +kernel)))
  (.cons (litWrite 0 (by decide +kernel) 7) .nil)))
private def wideCert : Compiler.Compilation 1 prefixCert.frag wideStage :=
  (Compiler.compile 1 prefixCert.frag wideStage).get (by decide +kernel)
private def wideOut : Solidity.Out C entry.st.H Output :=
  (wideStage.run entry.st).toOption.get (by decide +kernel)
attribute [irreducible] wideCert wideOut
private def wideRef : HRef wideOut.st.H bytesR := ⟨1, by decide +kernel⟩
private def wideTerminal : Machine :=
  match Evm.run wideCert.code prefixMachine with | .ok m _ => m | _ => prefixMachine

/-- Actual compilation ACCEPTS the returned uint300 after the same real nonempty
prefix. Actual source/target execution succeeds, yet the UNIFORM observer
refuses the out-of-range element. No compiler/source profile is narrowed. -/
theorem compiled_word300_observation : ∃ base m' base',
    wideCert.Input 1 128 base entry.st prefixMachine ∧
    wideStage.run entry.st = .ok wideOut ∧
    TEnv.get (.here : Idx Output (.mem bytesR)) wideOut.st.env = some wideRef ∧
    Evm.run wideCert.code prefixMachine = .ok m' 0 ∧ m'.stack = prefixMachine.stack ∧
    StateRepr 1 1 128 wideCert.frag wideOut.st base' m' ∧
    BaseExtends entry.st.H base base' ∧ base' oldRef.id = base oldRef.id ∧
    GrowsAllocator 1 128 (wideCert.allocationCost entry.st) entry.st base prefixMachine wideOut.st base' m' ∧
    (wideOut.st.heap.get wideRef).1.map (fun v => v.1.toNat) = [7,300,0] ∧
    ¬ ByteRange wideOut.st.heap wideRef ∧
    localBytes m' 1 (.here : Idx Output (.mem bytesR)) = none := by
  obtain ⟨base, ht, hs, ha, hk⟩ := nonempty_entry
  have hm : wideCert.isMemoryCalls = true := by decide +kernel
  have hi : wideCert.Input 1 128 base entry.st prefixMachine := by
    apply (wideCert.memoryCalls_input hm 1 128 base entry.st prefixMachine).mpr
    refine ⟨hs, by decide +kernel, .inr ⟨by decide, prefixCursor, ha, by decide +kernel⟩⟩
  have ho : wideStage.run entry.st = .ok wideOut := by
    unfold wideOut
    exact source_get _ (by decide +kernel)
  have hget : TEnv.get (.here : Idx Output (.mem bytesR)) wideOut.st.env = some wideRef :=
    reference_eq_of_id _ _ (by decide +kernel)
  obtain ⟨m', base', hrun, hstack, hrepr, hbase, hgrow⟩ :=
    CompiledMemoryCalls.completed_transport wideCert hm hi (by decide +kernel) wideOut ho
  rw [memory_call_pushes_zero wideCert hm, Nat.add_zero] at hrepr
  have he : wideTerminal = m' := by rw [wideTerminal, hrun]
  have hnone : localBytes wideTerminal 1 (.here : Idx Output (.mem bytesR)) = none := by decide +kernel
  rw [he] at hnone
  refine ⟨base, m', base', hi, ho, hget, hrun, hstack, hrepr, hbase, hbase oldRef, hgrow,
    by decide +kernel, ?_, hnone⟩
  intro hb
  have hv : (⟨300, by decide +kernel⟩ : PrimTy.uint.Denote) ∈ (wideOut.st.heap.get wideRef).1 := by decide +kernel
  have hn := hb _ hv
  exact (by decide : ¬ (300 : Nat) < 256) hn

/-- info: 'Solidity.Backend.AbiWorld.ReturnedBytesControls.compiled_word300_observation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms compiled_word300_observation

/-- info: 'Solidity.Backend.AbiWorld.ReturnedBytesControls.nonempty_applications' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms nonempty_applications
/-- info: 'Solidity.Backend.AbiWorld.ReturnedBytesControls.complete_payloads' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms complete_payloads
/-- info: 'Solidity.Backend.AbiWorld.ReturnedBytesControls.finite_packet_facts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms finite_packet_facts
/-- info: 'Solidity.Backend.AbiWorld.ReturnedBytesControls.finite_source_observations' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms finite_source_observations
/-- info: 'Solidity.Backend.AbiWorld.ReturnedBytesControls.finite_resources' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms finite_resources
/-- info: 'Solidity.Backend.AbiWorld.ReturnedBytesControls.finite_packet_sizes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms finite_packet_sizes
/-- info: 'Solidity.Backend.AbiWorld.ReturnedBytesControls.target_baseline' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms target_baseline
/-- info: 'Solidity.Backend.AbiWorld.ReturnedBytesControls.wrong_length_pointer_order' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms wrong_length_pointer_order
/-- info: 'Solidity.Backend.AbiWorld.ReturnedBytesControls.invalid_cell_observations' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms invalid_cell_observations
/-- info: 'Solidity.Backend.AbiWorld.ReturnedBytesControls.wrong_catch_and_offset_claims' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms wrong_catch_and_offset_claims
/-- info: 'Solidity.Backend.AbiWorld.ReturnedBytesControls.observed_error_packets' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms observed_error_packets
/-- info: 'Solidity.Backend.AbiWorld.CompiledMemoryCalls.wide_agrees' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CompiledMemoryCalls.wide_agrees

end Solidity.Backend.AbiWorld.ReturnedBytesControls
