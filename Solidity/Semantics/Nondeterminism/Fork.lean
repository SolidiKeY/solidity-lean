import Solidity.Semantics.Nondeterminism.Split

/-!
# The fork parameter (S6.1)

D2 pins Osaka. Its choices are fields of a `ForkSpec`, and `ForkSpec.osaka`
is one instance:

- the block fields the fork defines (no `block.slotnum` before Amsterdam,
  and `block.difficulty` reading `prevrandao` from Paris, EIP-4399);
- the precompile table;
- the code-size limits (EIP-170, EIP-3860), the transaction gas cap
  (EIP-7825) and the block gas limit;
- the call depth and stack limit;
- the gas constants the source rules read;
- the `blockhash` window;
- the stipend rule's constants.

Osaka agrees with the existing Osaka choices by `rfl`: the G06 pin
(`osaka_pin`), the G01/G06 idealized pin (`osaka_idealized_pin`),
EIP-150's forwarding (`osaka_forward`), and the precompile table
(`osaka_precompiles`). The Yul view and `Language.BlockField` agreements are
in `Solidity/Semantics/Nondeterminism/ForkAgreement.lean`, and the stipend
rule's in `Solidity/Semantics/Nondeterminism/ForkStipend.lean`.

**What is a parameter, and what is not.** The parameter is a record. Only
the stipend rule (`ForkStipend.lean`) and the controls read it so far. The
cold and warm access costs and the `SSTORE` sentry are recorded for X03 and
read by nothing yet. The rest of D2's schedule is not a field: memory
expansion, refunds, code deposit, creation and intrinsic costs, precompile
gas (`Evm.Fixed.precompileGas`), and opcode availability (for example `CLZ`,
EIP-7939). `Evm.Fork` has one constructor, so `pin?` is `none` off Osaka.

**Block fields are intrinsic to the fork.** A `BlockEnv F` reads a field
only with a proof that `F` has it (`BlockEnv.read`); `blobhash` is gated on
`blobbasefee`, both Cancun's (EIP-4844, EIP-7516). So `block.slotnum` under
Osaka has no reading at all (`osaka_no_slotnum`, `field?_slotnum_osaka`).
`ForkSpec` carries two invariants: `number` and `timestamp` exist, and the
field `block.difficulty` reads exists (`difficulty_has`).

**Instances other than Osaka are contrast only.**

- `prague` is Osaka without the P-256 precompile (EIP-7951) and without the
  EIP-7825 cap. Osaka's other changes (`CLZ`, the MODEXP bounds and
  repricing of EIP-7823/EIP-7883) are not fields, so they are not undone.
- `osakaWithSlotnum` is Osaka plus EIP-7843's `SLOTNUM`, tagged `.custom`.
  It is not Amsterdam.

**Block fields stay environment.** `EnvChoice F` is G01's session
environment plus the block environment of each action, indexed as
`SessionEnv.requests` indexes actions, so the block cannot change inside a
transaction. The chain premise `EnvChoice.Chain` (non-decreasing `number`
and `timestamp`, constant `chainid`) is part of `EnvChoice.Allowed`.
`ForkedSplit` reads `EnvChoice F`, and `ForkedSplit.at F` is a split
language. The fork is a third kind of input, a setting both sides share
(as `EvmSpec.pin`), neither environment nor compiler output. `HoldsOn` asks
for every fork of a list.

The module imports only `Split.lean`, the G01 contracts and the G06
interface, so a source module may import it once G07's whitelist names it.
-/

namespace Solidity.Semantics.Nondeterminism

open Solidity.Roadmap

/-! ## Forks and their choices -/

/-- Named forks, in order, and `custom` for drafts and controls. Only
`osaka` has an instance that claims to be the fork. -/
inductive Fork where
  | london
  | paris
  | shanghai
  | cancun
  | prague
  | osaka
  | amsterdam
  | custom
  deriving DecidableEq, Repr

/-- The G06 fork, where G06 has one (only Osaka today). -/
def Fork.toEvm? : Fork → Option Evm.Fork
  | .osaka => some .osaka
  | _ => none

/-- The block and transaction inputs a source may read. -/
inductive EnvField where
  | coinbase
  | number
  | timestamp
  | difficulty
  | prevrandao
  | gaslimit
  | chainid
  | basefee
  | blobbasefee
  | slotnum
  | origin
  | gasprice
  deriving DecidableEq, Repr

/-- Gas constants of a fork's schedule. Only `callStipend` and
`forwardDivisor` are read so far. -/
structure GasConstants where
  /-- A cold `SLOAD` (EIP-2929). -/
  coldSload : Nat
  /-- A cold account access (EIP-2929). -/
  coldAccount : Nat
  /-- A warm access (EIP-2929). -/
  warmAccess : Nat
  /-- `SSTORE` fails with this much gas or less left (EIP-2200). -/
  sstoreSentry : Nat
  /-- The stipend a value transfer adds. -/
  callStipend : Nat
  /-- A call forwards all but one `forwardDivisor`-th (EIP-150). -/
  forwardDivisor : Nat
  deriving DecidableEq, Repr

/-- The field `block.difficulty` reads. -/
def difficultyField (readsPrevrandao : Bool) : EnvField :=
  if readsPrevrandao then .prevrandao else .difficulty

/-- **A fork**: its block fields, precompiles, limits and gas constants. -/
structure ForkSpec where
  fork : Fork
  has : EnvField → Bool
  number_has : has .number = true
  timestamp_has : has .timestamp = true
  /-- `block.difficulty` reads `prevrandao` (EIP-4399, from Paris). -/
  difficultyReadsPrevrandao : Bool
  /-- The field `block.difficulty` reads exists. -/
  difficulty_has : has (difficultyField difficultyReadsPrevrandao) = true
  precompile : Evm.Precompile → Bool
  runtimeCodeLimit : Option Nat
  initcodeLimit : Option Nat
  txGasCap : Option Nat
  blockGasLimited : Bool
  callDepth : Nat
  stackLimit : Nat
  gas : GasConstants
  /-- `blockhash` answers for the previous `blockhashWindow` blocks. -/
  blockhashWindow : Nat
  /-- The stipend rule's gas per node and reserve (`Stipend.CostModel`):
  design constants of the source rule for this fork's cold costs. -/
  stipendUnit : Nat
  stipendReserve : Nat

/-- Osaka's gas constants. -/
def GasConstants.osaka : GasConstants where
  coldSload := 2100
  coldAccount := 2600
  warmAccess := 100
  sstoreSentry := 2300
  callStipend := 2300
  forwardDivisor := 64

/-- Osaka's block fields: every field but the pre-Paris difficulty and `slotnum`. -/
def osakaHas : EnvField → Bool
  | .difficulty => false
  | .slotnum => false
  | _ => true

namespace ForkSpec

/-- **Osaka**, as D2 pins it. -/
def osaka : ForkSpec where
  fork := .osaka
  has := osakaHas
  number_has := rfl
  timestamp_has := rfl
  difficultyReadsPrevrandao := true
  difficulty_has := rfl
  precompile _ := true
  runtimeCodeLimit := some 24576
  initcodeLimit := some 49152
  txGasCap := some (2 ^ 24)
  blockGasLimited := true
  callDepth := 1024
  stackLimit := 1024
  gas := GasConstants.osaka
  blockhashWindow := 256
  stipendUnit := 50
  stipendReserve := 300

/-- **Prague**, as far as the fields reach: no P-256 precompile (EIP-7951)
and no transaction gas cap (EIP-7825). -/
def prague : ForkSpec :=
  { osaka with
    fork := .prague
    precompile := fun p => p != .p256Verify
    txGasCap := none }

/-- **Osaka with `SLOTNUM`** (EIP-7843, which solc gates on Amsterdam). Not
Amsterdam. -/
def osakaWithSlotnum : ForkSpec :=
  { osaka with
    fork := .custom
    has := fun f => f == .slotnum || osakaHas f
    number_has := rfl
    timestamp_has := rfl
    difficulty_has := rfl }

/-- A pre-Paris-like control: `block.difficulty` reads its own field and
`prevrandao` does not exist. -/
def difficultyControl : ForkSpec :=
  { osaka with
    fork := .custom
    has := fun f => f != .prevrandao && f != .slotnum
    number_has := rfl
    timestamp_has := rfl
    difficultyReadsPrevrandao := false
    difficulty_has := rfl }

/-- The four idealizations of G01 Q2 and G06 Q2 (`Evm.pinned`). -/
def idealize (F : ForkSpec) : ForkSpec :=
  { F with runtimeCodeLimit := none, initcodeLimit := none, txGasCap := none, blockGasLimited := false }

/-- D2's reading: code-size limits stay (as creation failures); only the
transaction cap and the block gas limit are idealized. -/
def d2 (F : ForkSpec) : ForkSpec :=
  { F with txGasCap := none, blockGasLimited := false }

/-- The G06 pin of a fork G06 knows, from the fields. -/
def pin? (F : ForkSpec) : Option Evm.Pin :=
  F.fork.toEvm?.map fun f =>
    { fork := f, runtimeCodeLimit := F.runtimeCodeLimit, initcodeLimit := F.initcodeLimit,
      txGasCap := F.txGasCap, blockGasLimited := F.blockGasLimited, callDepth := F.callDepth,
      stackLimit := F.stackLimit, stipend := F.gas.callStipend }

/-- The gas a call forwards at most. -/
def forward (F : ForkSpec) (g : Nat) : Nat := g - g / F.gas.forwardDivisor

/-! ### Osaka is an instance -/

theorem osaka_pin : osaka.pin? = some Evm.osaka := rfl

theorem osaka_idealized_pin : osaka.idealize.pin? = some Evm.pinned := rfl

/-- D2's pin keeps the code-size limits that `Evm.pinned` idealizes. -/
theorem osaka_d2_pin :
    osaka.d2.pin? = some { Evm.pinned with runtimeCodeLimit := some 24576, initcodeLimit := some 49152 } :=
  rfl

theorem osaka_forward (g : Nat) : osaka.forward g = Evm.allButOne64 g := rfl

theorem osaka_precompiles (p : Evm.Precompile) : osaka.precompile p = true := rfl

theorem osaka_stipend : osaka.gas.callStipend = Evm.pinned.stipend := rfl

/-- **`block.slotnum` is not an Osaka field.** -/
theorem osaka_no_slotnum : osaka.has .slotnum = false := rfl

theorem osakaWithSlotnum_slotnum : osakaWithSlotnum.has .slotnum = true := rfl

/-- Negative controls: Prague is not Osaka. -/
theorem prague_differs : prague.precompile .p256Verify = false ∧ prague.txGasCap = none ∧
    prague.pin? = none :=
  ⟨rfl, rfl, rfl⟩

/-- Only the slotnum field separates the draft from Osaka. -/
theorem osakaWithSlotnum_has (f : EnvField) (hf : f ≠ .slotnum) :
    osakaWithSlotnum.has f = osaka.has f := by
  cases f <;> first | rfl | exact absurd rfl hf

end ForkSpec

/-! ## Block environments -/

/-- **The block inputs of one transaction under fork `F`**: a word for each
field `F` has, the historical block hashes and the transaction's blob
hashes. -/
structure BlockEnv (F : ForkSpec) where
  read : (f : EnvField) → F.has f = true → Word
  historicalHash : Word → Word
  blobHashes : List Word

namespace BlockEnv

variable {F : ForkSpec}

/-- `block.number`. -/
def number (e : BlockEnv F) : Word := e.read .number F.number_has

/-- `block.timestamp`. -/
def timestamp (e : BlockEnv F) : Word := e.read .timestamp F.timestamp_has

/-- `block.difficulty`: the field the fork reads for it. -/
def difficulty (e : BlockEnv F) : Word := e.read _ F.difficulty_has

/-- A field, where the fork has it. -/
def field? (e : BlockEnv F) (f : EnvField) : Option Word :=
  if h : F.has f = true then some (e.read f h) else none

/-- `blockhash(q)`: the previous `F.blockhashWindow` blocks only. -/
def blockhash (e : BlockEnv F) (q : Word) : Word :=
  if q.val < e.number.val ∧ e.number.val - q.val ≤ F.blockhashWindow then e.historicalHash q
  else ⟨0, by decide⟩

/-- `blobhash(i)`, where the fork has blobs (gated on `blobbasefee`). -/
def blobhash? (e : BlockEnv F) (i : Word) : Option Word :=
  if F.has .blobbasefee = true then some (e.blobHashes[i.val]?.getD ⟨0, by decide⟩) else none

/-- Every field at one word (an inhabited witness for every fork). -/
def const (F : ForkSpec) (w : Word) : BlockEnv F := ⟨fun _ _ => w, fun _ => w, []⟩

theorem field?_of_has (e : BlockEnv F) {f : EnvField} (h : F.has f = true) :
    e.field? f = some (e.read f h) := by
  simp only [field?, h, dif_pos]

theorem field?_of_not_has (e : BlockEnv F) {f : EnvField} (h : F.has f = false) :
    e.field? f = none := by
  simp only [field?, h, Bool.false_eq_true, dif_neg, not_false_eq_true]

/-- **Under Osaka, `block.slotnum` has no reading.** -/
theorem field?_slotnum_osaka (e : BlockEnv ForkSpec.osaka) : e.field? .slotnum = none :=
  e.field?_of_not_has ForkSpec.osaka_no_slotnum

/-- Under the draft it reads the environment. -/
theorem field?_slotnum_withSlotnum (e : BlockEnv ForkSpec.osakaWithSlotnum) :
    e.field? .slotnum = some (e.read .slotnum rfl) :=
  e.field?_of_has rfl

/-- `block.difficulty` is `prevrandao` under Osaka. -/
theorem difficulty_osaka (e : BlockEnv ForkSpec.osaka) : e.difficulty = e.read .prevrandao rfl := rfl

/-- Negative control: under the pre-Paris control it is its own field. -/
theorem difficulty_control (e : BlockEnv ForkSpec.difficultyControl) :
    e.difficulty = e.read .difficulty rfl ∧ e.field? .prevrandao = none :=
  ⟨rfl, e.field?_of_not_has rfl⟩

end BlockEnv

/-! ## The environment with block fields, and forked split languages -/

/-- **The environment under fork `F`**: G01's session environment and the
block inputs of each action (indexed as `SessionEnv.requests`). -/
structure EnvChoice (F : ForkSpec) where
  session : SessionEnv
  block : Nat → BlockEnv F

/-- **The chain premise**: block numbers and timestamps do not decrease
from action to action, and the chain id is constant. -/
def EnvChoice.Chain {F : ForkSpec} (e : EnvChoice F) : Prop :=
  ∀ i j, i ≤ j → (e.block i).number.val ≤ (e.block j).number.val ∧
    (e.block i).timestamp.val ≤ (e.block j).timestamp.val ∧
    (e.block i).field? .chainid = (e.block j).field? .chainid

/-- An environment is allowed when its session is and the chain premise holds. -/
def EnvChoice.Allowed {F : ForkSpec} (e : EnvChoice F) : Prop := e.session.Allowed ∧ e.Chain

/-- One block for every action meets the chain premise. -/
theorem EnvChoice.chain_const {F : ForkSpec} (s : SessionEnv) (b : BlockEnv F) :
    (⟨s, fun _ => b⟩ : EnvChoice F).Chain :=
  fun _ _ _ => ⟨Nat.le_refl _, Nat.le_refl _, rfl⟩

/-- **A split language with a fork parameter.** -/
structure ForkedSplit where
  Prog : Type
  Res : Type
  resLE : LE Res
  Allowed : (F : ForkSpec) → EnvChoice F → Prop
  Admissible : ForkSpec → Res → Prop
  sem : (F : ForkSpec) → CompilerChoice → Prog → EnvChoice F → Prefixes Res Event Outcome
  consistent : ∀ F c p e, @Prefixes.Consistent Res Event Outcome resLE (sem F c p e)
  readsD1 : Prog → Bool

namespace ForkedSplit

variable (L : ForkedSplit)

/-- The split language at one fork; its environment is `EnvChoice F`. -/
def «at» (F : ForkSpec) : SplitSpec where
  Prog := L.Prog
  Env := EnvChoice F
  Res := L.Res
  resLE := L.resLE
  Allowed := L.Allowed F
  Admissible := L.Admissible F
  sem := L.sem F
  consistent := L.consistent F
  readsD1 := L.readsD1

/-- **Under both pipelines, at every fork of a list.** -/
def HoldsOn (forks : List ForkSpec) (art : ForkSpec → Pipeline → Artifact) (p : L.Prog)
    (Φ : Prefix Event Outcome → Prop) : Prop :=
  ∀ F, F ∈ forks → (L.at F).HoldsBoth (art F) p Φ

/-- The language does not read the block environment or the fork for `p`:
the session decides. -/
def ForkBlind (p : L.Prog) : Prop :=
  ∀ F F' c (e : EnvChoice F) (e' : EnvChoice F'), e.session = e'.session → L.sem F c p e = L.sem F' c p e'

variable {L}

theorem HoldsOn.osaka {forks : List ForkSpec} {art : ForkSpec → Pipeline → Artifact} {p : L.Prog}
    {Φ : Prefix Event Outcome → Prop} (h : L.HoldsOn forks art p Φ) (hm : ForkSpec.osaka ∈ forks) :
    (L.at ForkSpec.osaka).HoldsBoth (art ForkSpec.osaka) p Φ :=
  h _ hm

/-- A fork-blind program whose allowed sessions and bounds are allowed at
Osaka: Osaka suffices. -/
theorem holdsOn_of_forkBlind {forks : List ForkSpec} {art : Pipeline → Artifact} {p : L.Prog}
    {Φ : Prefix Event Outcome → Prop} (hb : L.ForkBlind p)
    (hal : ∀ F (e : EnvChoice F), L.Allowed F e →
      L.Allowed ForkSpec.osaka ⟨e.session, fun _ => BlockEnv.const _ ⟨0, by decide⟩⟩)
    (had : ∀ F r, L.Admissible F r → L.Admissible ForkSpec.osaka r)
    (h : (L.at ForkSpec.osaka).HoldsBoth art p Φ) : L.HoldsOn forks (fun _ => art) p Φ := by
  intro F _ q g e he r hr
  have e₁ : L.sem F ⟨q, art q, g⟩ p e =
      L.sem ForkSpec.osaka ⟨q, art q, g⟩ p ⟨e.session, fun _ => BlockEnv.const _ ⟨0, by decide⟩⟩ :=
    hb F ForkSpec.osaka _ e _ rfl
  show Φ (L.sem F ⟨q, art q, g⟩ p e r)
  rw [e₁]
  exact h q g _ (hal F e he) r (had F r hr)

end ForkedSplit

/-- **A session-only split language, at every fork**: it reads the session
of the environment only; an environment is allowed when the chain premise
holds and its session is allowed. -/
def SplitSpec.forked (L : SplitSpec) (toEnv : SessionEnv → L.Env) : ForkedSplit where
  Prog := L.Prog
  Res := L.Res
  resLE := L.resLE
  Allowed _ e := e.Chain ∧ L.Allowed (toEnv e.session)
  Admissible _ := L.Admissible
  sem _ c p e := L.sem c p (toEnv e.session)
  consistent _ c p e := L.consistent c p (toEnv e.session)
  readsD1 := L.readsD1

theorem SplitSpec.forked_blind (L : SplitSpec) (toEnv : SessionEnv → L.Env) (p : L.Prog) :
    (L.forked toEnv).ForkBlind p := by
  intro F F' c e e' hs
  show L.sem c p (toEnv e.session) = L.sem c p (toEnv e'.session)
  rw [hs]

/-! ## Witnesses and negative controls -/

namespace ForkControls

open ForkSpec

/-- A language whose run reads `block.slotnum` of the first action when the
fork has it: success with the field's low byte, a revert where it has none. -/
def slotnumLang : ForkedSplit where
  Prog := Unit
  Res := Nat
  resLE := inferInstance
  Allowed _ e := e.Chain
  Admissible _ _ := True
  sem _ _ _ e _ := ⟨[], some (match (e.block 0).field? .slotnum with
    | some w => .success [UInt8.ofNat w.val]
    | none => .revert [])⟩
  consistent _ _ _ _ _ _ _ := Prefix.Le.refl _
  readsD1 _ := false

def reverts (x : Prefix Event Outcome) : Prop := x.final = some (.revert [])

/-- An inhabited environment at every fork. -/
def envAt (F : ForkSpec) (w : Word) : EnvChoice F :=
  ⟨{ deployer := ⟨0, by decide⟩, deployNonce := ⟨0, by decide⟩, deployValue := ⟨0, by decide⟩,
     deployArgs := [], balance := fun _ => ⟨0, by decide⟩, hasCode := fun _ _ => false,
     requests := fun _ _ => none, callee := fun _ => .answer (.success []) },
   fun _ => BlockEnv.const F w⟩

theorem envAt_allowed (F : ForkSpec) (w : Word) : (envAt F w).session.Allowed ∧ (envAt F w).Chain :=
  ⟨⟨fun _ => rfl, fun _ _ _ => rfl, fun _ _ _ _ _ _ => rfl⟩, EnvChoice.chain_const _ _⟩

/-- Under Osaka every run reverts: there is no slotnum to read. -/
theorem slotnum_osaka : slotnumLang.HoldsOn [osaka] (fun _ _ => Artifact.empty) () reverts := by
  intro F hF q g e _ r _
  simp only [List.mem_singleton] at hF
  subst hF
  simp only [reverts, ForkedSplit.at, slotnumLang, BlockEnv.field?_slotnum_osaka]

/-- **Negative control**: the slotnum fork reads it, so the same statement fails there. -/
theorem slotnum_withSlotnum_not :
    ¬ slotnumLang.HoldsOn [osaka, osakaWithSlotnum] (fun _ _ => Artifact.empty) () reverts := by
  intro h
  have := h osakaWithSlotnum (List.Mem.tail _ (List.Mem.head _))
    .legacy (GasOracle.const ⟨0, by decide⟩) (envAt _ ⟨5, by decide⟩) (envAt_allowed _ _).2
    (0 : Nat) trivial
  simp only [reverts, slotnumLang, ForkedSplit.at, BlockEnv.field?_slotnum_withSlotnum] at this
  cases this

end ForkControls

end Solidity.Semantics.Nondeterminism
/-- info: 'Solidity.Semantics.Nondeterminism.ForkSpec.osaka_pin' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Semantics.Nondeterminism.ForkSpec.osaka_pin
/-- info: 'Solidity.Semantics.Nondeterminism.ForkSpec.osaka_idealized_pin' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Semantics.Nondeterminism.ForkSpec.osaka_idealized_pin
/-- info: 'Solidity.Semantics.Nondeterminism.ForkSpec.osaka_d2_pin' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Semantics.Nondeterminism.ForkSpec.osaka_d2_pin
/-- info: 'Solidity.Semantics.Nondeterminism.ForkSpec.prague_differs' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Semantics.Nondeterminism.ForkSpec.prague_differs
/-- info: 'Solidity.Semantics.Nondeterminism.ForkSpec.osakaWithSlotnum_has' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Semantics.Nondeterminism.ForkSpec.osakaWithSlotnum_has
/-- info: 'Solidity.Semantics.Nondeterminism.BlockEnv.field?_slotnum_osaka' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Semantics.Nondeterminism.BlockEnv.field?_slotnum_osaka
/-- info: 'Solidity.Semantics.Nondeterminism.BlockEnv.difficulty_control' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Semantics.Nondeterminism.BlockEnv.difficulty_control
/-- info: 'Solidity.Semantics.Nondeterminism.ForkedSplit.holdsOn_of_forkBlind' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Semantics.Nondeterminism.ForkedSplit.holdsOn_of_forkBlind
/-- info: 'Solidity.Semantics.Nondeterminism.ForkControls.slotnum_osaka' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Semantics.Nondeterminism.ForkControls.slotnum_osaka
/-- info: 'Solidity.Semantics.Nondeterminism.ForkControls.slotnum_withSlotnum_not' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Semantics.Nondeterminism.ForkControls.slotnum_withSlotnum_not
