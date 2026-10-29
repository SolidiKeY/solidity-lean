import Solidity.Keccak

/-!
# The pinned EVM and its observation interface (G06), as statements

Roadmap G06 fixes the EVM that contract 4 (`Execution`) and contract 5
(`PublicCorrectness`) of `Solidity/Roadmap/Contracts.lean` end in.  This
module states that interface: the pin with its recorded idealizations, the
Osaka precompile table, the fixed functions both sides share, the resources
of a pinned execution and the shape of the core/Bridge certificate.  It
defines no EVM and claims no theorem beyond checks of its own shape.
`docs/feature-work/roadmap-g06-evm.md` explains each definition, the
inventory of machine disagreements it answers, and the bridge lemmas an
external adapter owes.

**Independent of the compiler and of G01's statements.**  The module imports
only `Solidity.Keccak` (no import at all below it), so whatever instantiates
`Pinned` cannot reach a compiler module through it (G01's import gate,
item 3).  It does not import `Solidity.Roadmap.Contracts`: `Pinned` is
parameterized by the artifact type and the prefix type with its order, and
the document maps it to G01's `EvmSpec`.

**Resources are what gas decides.**  A pinned execution's resource is a
`Schedule` (every gas number chosen outside the compiled system, and the
depth at which the environment enters it) and evaluator fuel.  More fuel
extends a prefix; a different schedule is a different execution, so the
order compares fuel at an equal schedule.  Gas exhaustion is therefore not
the end of a prefix: a frame or a transaction that runs out fails, its
caller sees the failure and continues (the 2026-10-29 decisions).

**Fixed functions are parameters.**  Keccak-256 and the precompiles are
fields of `Fixed`, shared by the source semantics and the pinned EVM; the
public theorem quantifies over every `Fixed`, so its instance by the real
functions is a bridge lemma, not a trust assumption.  The only premise on
them is the per-run `Fixed.NoCollision`.
-/

namespace Solidity.Roadmap.Evm

/-- Bytes, as `Contracts.lean`'s observations carry them. -/
abbrev Bytes := List UInt8

/-! ## The pin -/

/-- The EVM fork of the pinned semantics and of the compiled bytecode
(G00 Q3). -/
inductive Fork where
  | osaka
  deriving DecidableEq, Repr

/-- A pinned EVM: the fork, and each fixed limit, `none` where it is a
recorded idealization. -/
structure Pin where
  fork : Fork
  /-- EIP-170's runtime code size limit. -/
  runtimeCodeLimit : Option Nat
  /-- EIP-3860's initcode size limit. -/
  initcodeLimit : Option Nat
  /-- EIP-7825's per-transaction gas limit cap (open: question Q2 of the
  G06 document). -/
  txGasCap : Option Nat
  /-- The message-call/creation depth limit. -/
  callDepth : Nat
  /-- The operand stack limit, per frame. -/
  stackLimit : Nat
  /-- The gas stipend a value transfer adds (`transfer`, `send`). -/
  stipend : Nat
  deriving DecidableEq, Repr

/-- Osaka as the chain runs it. -/
def osaka : Pin where
  fork := .osaka
  runtimeCodeLimit := some 24576
  initcodeLimit := some 49152
  txGasCap := some (2 ^ 24)
  callDepth := 1024
  stackLimit := 1024
  stipend := 2300

/-- **The pin of the decisions:** Osaka with EIP-170 and EIP-3860 idealized
(G01 Q2), any code size deploys.  The gas cap stays Osaka's until Q2 of the
G06 document is answered. -/
def pinned : Pin := { osaka with runtimeCodeLimit := none, initcodeLimit := none }

/-- The pin differs from Osaka in the code size limits only. -/
theorem pinned_eq : pinned = { osaka with runtimeCodeLimit := none, initcodeLimit := none } := rfl

/-- The gas a `CALL` can forward at most: all but one 64th (EIP-150). -/
def allButOne64 (g : Nat) : Nat := g - g / 64

/-- A call or creation made by a frame at depth `d` fails before it runs:
the depth limit leaves no room for the new frame. -/
def Pin.callFails (p : Pin) (d : Nat) : Bool := p.callDepth ≤ d

/-! ## The Osaka precompiles

Calls to these addresses run the fixed functions of `Fixed`, never
environment code (decision "precompile addresses"). -/

/-- The precompiled contracts of Osaka: Frontier's four, Byzantium's and
Istanbul's, Cancun's point evaluation, Prague's BLS12-381 (EIP-2537) and
Osaka's P-256 verification (EIP-7951). -/
inductive Precompile where
  | ecrecover | sha256 | ripemd160 | identity | modexp
  | bnAdd | bnMul | bnPairing | blake2f | pointEvaluation
  | blsG1Add | blsG1Msm | blsG2Add | blsG2Msm | blsPairing
  | blsMapFpToG1 | blsMapFp2ToG2
  | p256Verify
  deriving DecidableEq, Repr

/-- Its address. -/
def Precompile.address : Precompile → Nat
  | .ecrecover => 0x01 | .sha256 => 0x02 | .ripemd160 => 0x03 | .identity => 0x04
  | .modexp => 0x05 | .bnAdd => 0x06 | .bnMul => 0x07 | .bnPairing => 0x08
  | .blake2f => 0x09 | .pointEvaluation => 0x0a
  | .blsG1Add => 0x0b | .blsG1Msm => 0x0c | .blsG2Add => 0x0d | .blsG2Msm => 0x0e
  | .blsPairing => 0x0f | .blsMapFpToG1 => 0x10 | .blsMapFp2ToG2 => 0x11
  | .p256Verify => 0x100

/-- Every precompile, in address order. -/
def Precompile.all : List Precompile :=
  [.ecrecover, .sha256, .ripemd160, .identity, .modexp, .bnAdd, .bnMul, .bnPairing,
   .blake2f, .pointEvaluation, .blsG1Add, .blsG1Msm, .blsG2Add, .blsG2Msm, .blsPairing,
   .blsMapFpToG1, .blsMapFp2ToG2, .p256Verify]

/-- The precompile at an address, if any. -/
def Precompile.ofAddress? (a : Nat) : Option Precompile :=
  Precompile.all.find? (·.address == a)

theorem Precompile.mem_all (p : Precompile) : p ∈ Precompile.all := by
  cases p <;> decide

/-- The address table is a partial inverse: each precompile is found at its
address, so no two share one. -/
theorem Precompile.ofAddress?_address (p : Precompile) : Precompile.ofAddress? p.address = some p := by
  cases p <;> decide

theorem Precompile.address_injective {p q : Precompile} (h : p.address = q.address) : p = q := by
  have hp := Precompile.ofAddress?_address p
  rw [h, Precompile.ofAddress?_address q] at hp
  exact (Option.some.inj hp).symm

/-- No precompile sits at address `0`, which stays an account without code
(the approved assumption of G01 Q4), and each is a 160-bit address. -/
theorem Precompile.address_pos_lt (p : Precompile) : 0 < p.address ∧ p.address < 2 ^ 160 := by
  cases p <;> decide

/-! ## Fixed functions -/

/-- The functions the source semantics and the pinned EVM share, fixed for a
whole run and quantified by the public theorem.  A precompile's result is
`none` for an exceptional halt (an invalid input); its gas is what it
charges, which matters where the source fixes the forwarded gas (the
`stipend` of a payment). -/
structure Fixed where
  keccak : Bytes → Nat
  keccak_lt : ∀ b, keccak b < 2 ^ 256
  precompile : Precompile → Bytes → Option Bytes
  precompileGas : Precompile → Bytes → Nat

/-- Keccak-256 of `Solidity/Keccak.lean`, as a word: the instance of
`Fixed.keccak`.  The hash has 32 bytes, so the reduction is the identity;
it states the bound without a lemma about `Keccak.ofBytes`. -/
def keccakWord (b : Bytes) : Nat := Keccak.keccak256Nat (b.map UInt8.toNat) % 2 ^ 256

/-- **The per-run hash premise** (G01 Q3): the preimages an execution prefix
hashes do not collide.  `hashed` is the list of those preimages, read off the
prefix; global injectivity is never assumed. -/
def Fixed.NoCollision (F : Fixed) (hashed : List Bytes) : Prop :=
  ∀ a ∈ hashed, ∀ b ∈ hashed, F.keccak a = F.keccak b → a = b

/-- A shorter list of preimages keeps the premise. -/
theorem Fixed.NoCollision.mono {F : Fixed} {hs hs' : List Bytes} (h : F.NoCollision hs')
    (sub : ∀ x ∈ hs, x ∈ hs') : F.NoCollision hs :=
  fun a ha b hb e => h a (sub a ha) b (sub b hb) e

/-- The minimal big-endian bytes of a number (`0` has none), as RLP writes
a scalar. -/
def beBytes (n : Nat) : List Nat :=
  if n = 0 then [] else beBytes (n / 256) ++ [n % 256]

/-- `n` as exactly `k` big-endian bytes. -/
def beFixed (k n : Nat) : List Nat := (List.range k).reverse.map fun i => (n >>> (8 * i)) % 256

/-- The RLP length prefix with offset `o` (`0x80` for a string, `0xc0` for
a list). -/
def rlpHead (o len : Nat) : List Nat :=
  if len < 56 then [o + len] else (o + 55 + (beBytes len).length) :: beBytes len

/-- RLP of a byte string. -/
def rlpBytes (b : List Nat) : List Nat :=
  match b with
  | [x] => if x < 0x80 then [x] else rlpHead 0x80 1 ++ [x]
  | _ => rlpHead 0x80 b.length ++ b

/-- RLP of a list of encoded items. -/
def rlpList (items : List (List Nat)) : List Nat :=
  let payload := items.flatten
  rlpHead 0xc0 payload.length ++ payload

/-- **The address `CREATE` gives** the `nonce`-th creation of `sender`:
the low 160 bits of `keccak(rlp [sender, nonce])`.  A fixed function of
`Fixed.keccak`, so the source semantics can name the address without
choosing it (no collision premise: a creation at an occupied address fails,
EIP-684/EIP-7610). -/
def Fixed.createAddress (F : Fixed) (sender nonce : Nat) : Nat :=
  F.keccak ((rlpList [rlpBytes (beFixed 20 sender), rlpBytes (beBytes nonce)]).map
    fun n => n.toUInt8) % 2 ^ 160

theorem Fixed.createAddress_lt (F : Fixed) (sender nonce : Nat) :
    F.createAddress sender nonce < 2 ^ 160 :=
  Nat.mod_lt _ (Nat.pow_pos (by decide))

/-- The fixed functions with the real Keccak-256 and unspecified
precompiles: enough to check `createAddress` against known addresses. -/
def withKeccak : Fixed where
  keccak := keccakWord
  keccak_lt _ := Nat.mod_lt _ (Nat.pow_pos (by decide))
  precompile _ _ := none
  precompileGas _ _ := 0

-- The addresses of the first creations of a well-known sender.
#guard withKeccak.createAddress 0x6ac7ea33f8831ea9dcc53393aaa88b25a785dbf0 0 ==
    0xcd234a471b72ba2f1ccf0a70fcaba648a5eecd8d
#guard withKeccak.createAddress 0x6ac7ea33f8831ea9dcc53393aaa88b25a785dbf0 1 ==
    0x343c43a37d37dff08ae8c4a11544c718abb4fcf8
-- RLP of a long string and of the scalar 1024.
#guard rlpBytes (List.replicate 56 0x61) == [0xb8, 56] ++ List.replicate 56 0x61
#guard rlpBytes (beBytes 1024) == [0x82, 0x04, 0x00]

/-! ## Resources -/

/-- Every gas number chosen outside the compiled system, and the depths at
which the environment enters it: the gas limit of the `i`-th transaction
request, the gas the environment forwards to the `k`-th frame of the system
it enters (a callback or a call from outside), and that frame's depth.  The
gas the system's own calls forward is the compiler's choice, not here. -/
structure Schedule where
  txGas : Nat → Nat
  entryGas : Nat → Nat
  entryDepth : Nat → Nat

/-- A pinned execution's resource: a schedule and the adapter's evaluator
fuel. -/
structure Res where
  schedule : Schedule
  fuel : Nat

/-- More fuel at the same schedule.  A different schedule is a different
execution, not a longer prefix of the same one. -/
instance : LE Res := ⟨fun a b => a.schedule = b.schedule ∧ a.fuel ≤ b.fuel⟩

theorem Res.le_refl (a : Res) : a ≤ a := ⟨rfl, Nat.le_refl _⟩

theorem Res.le_trans {a b c : Res} (h₁ : a ≤ b) (h₂ : b ≤ c) : a ≤ c :=
  ⟨h₁.1.trans h₂.1, Nat.le_trans h₁.2 h₂.2⟩

/-- **The admissible resources** of a pin: a transaction's gas within the
cap where the pin has one, and an entered frame no deeper than the depth
limit.  Every fuel is admissible, so unbounded behaviour is the family's. -/
def Res.Admissible (p : Pin) (r : Res) : Prop :=
  (∀ c, p.txGasCap = some c → ∀ i, r.schedule.txGas i ≤ c) ∧
  ∀ k, r.schedule.entryDepth k ≤ p.callDepth

/-- Fuel does not change admissibility. -/
theorem Res.Admissible.of_le {p : Pin} {a b : Res} (h : a ≤ b) (ha : Res.Admissible p a) :
    Res.Admissible p b := by
  unfold Res.Admissible at ha ⊢
  rw [← h.1]
  exact ha

/-- The source side of a schedule: where a frame or a transaction fails from
resources, as the number of its events before the failure, or never.  The
source semantics also fails every call made at the depth limit
(`Pin.callFails`); no source resource can avoid that. -/
structure FailurePoints where
  tx : Nat → Option Nat
  entry : Nat → Option Nat

/-! ## Observation -/

/-- How a frame of the pinned EVM halts: `STOP`/`RETURN` with its return
data, `REVERT` with its data, or an exceptional halt (out of gas, an invalid
or unassigned opcode, a bad jump, a stack limit, a static-mode write). -/
inductive Halt where
  | success (returnData : Bytes)
  | revert (revertData : Bytes)
  | exceptional
  deriving DecidableEq, Repr

/-- What the caller of a frame observes: whether it succeeded, and the
return data buffer it can read.  An exceptional halt is a failure with no
data, as `REVERT(0, 0)` is; the two are one observation. -/
def Halt.observe : Halt → Bool × Bytes
  | .success d => (true, d)
  | .revert d => (false, d)
  | .exceptional => (false, [])

theorem Halt.observe_exceptional : Halt.exceptional.observe = (Halt.revert []).observe := rfl

/-- A successful halt is never observed as a failure, whatever its data. -/
theorem Halt.observe_success {h : Halt} {d : Bytes} : h.observe = (true, d) ↔ h = .success d := by
  cases h <;> simp only [Halt.observe, Prod.mk.injEq, Bool.false_eq_true, false_and,
    reduceCtorEq, true_and, Halt.success.injEq]

/-! ## The pinned semantics and the certificate boundary -/

/-- **A pinned EVM, as a language over artifacts.**  `P` is the prefix type
with its order (`Contracts.lean`'s `Prefix Event Outcome` and `Prefix.Le`),
`Art` the artifact type (`Artifact`).  `sem a e r` deploys `a` in the
environment `e` (the world, every environment account's code, the request
and block sequence) and runs the session at resource `r`.  An invalid
request (its sender cannot cover value and upfront gas) never executes. -/
structure Pinned (Art P : Type) [LE P] where
  pin : Pin
  fixed : Fixed
  Env : Type
  Allowed : Env → Prop
  sem : Art → Env → Res → P
  consistent : ∀ a e r r', r ≤ r' → sem a e r ≤ sem a e r'

/-- `Pinned.Admissible` is its pin's. -/
def Pinned.Admissible {Art P : Type} [LE P] (V : Pinned Art P) : Res → Prop :=
  Res.Admissible V.pin

/-- Two prefixes are the same observation. -/
def SameObs {P : Type} [LE P] (x y : P) : Prop := x ≤ y ∧ y ≤ x

/-- **The core/Bridge certificate.**  An external EVM `ext` (an adapter over
EVMYulLean in `Bridge/`) certifies the core's pinned semantics `core` when
the pins and the fixed functions agree and each admissible execution of one
is observed exactly as some admissible execution of the other, per artifact,
in both directions.  The environments correspond per execution, not by a
fixed map: which transactions run out of gas depends on the code.  The
core states this; only the adapter proves it. -/
structure Certificate {Art P : Type} [LE P] (core ext : Pinned Art P) : Prop where
  pin : core.pin = ext.pin
  fixed : core.fixed = ext.fixed
  back : ∀ a e r, ext.Allowed e → ext.Admissible r →
    ∃ e' r', core.Allowed e' ∧ core.Admissible r' ∧ SameObs (ext.sem a e r) (core.sem a e' r')
  forth : ∀ a e' r', core.Allowed e' → core.Admissible r' →
    ∃ e r, ext.Allowed e ∧ ext.Admissible r ∧ SameObs (core.sem a e' r') (ext.sem a e r)

/-- A certificate is symmetric: the boundary transfers in both directions. -/
theorem Certificate.symm {Art P : Type} [LE P] {core ext : Pinned Art P}
    (c : Certificate core ext) : Certificate ext core :=
  ⟨c.pin.symm, c.fixed.symm, c.forth, c.back⟩

/-- Every pinned EVM certifies itself, so the boundary is not vacuous on
its own; `SameObs` needs a reflexive order. -/
theorem Certificate.refl {Art P : Type} [LE P] (refl : ∀ x : P, x ≤ x) (V : Pinned Art P) :
    Certificate V V :=
  ⟨rfl, rfl, fun _ e r he hr => ⟨e, r, he, hr, refl _, refl _⟩,
    fun _ e r he hr => ⟨e, r, he, hr, refl _, refl _⟩⟩

end Solidity.Roadmap.Evm

/-- info: 'Solidity.Roadmap.Evm.Precompile.address_injective' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Roadmap.Evm.Precompile.address_injective
/-- info: 'Solidity.Roadmap.Evm.Certificate.symm' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Roadmap.Evm.Certificate.symm
