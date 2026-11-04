import Solidity.Semantics.Nondeterminism.Split
import Solidity.Yul.Views.Inputs
import Solidity.Language.Features

/-!
# The fork parameter (S6.1)

D2 pins Osaka. Its choices are the gas constants, the code-size and
transaction-gas limits, the precompile table, the call depth and the
`blockhash` window, together with the block fields the fork defines (no
`block.slotnum` before Amsterdam). These are fields of a `ForkSpec`, not
constants, and `ForkSpec.osaka` is one instance. Its agreement with the
existing Osaka choices is proved by `rfl`:

- the G06 pin: `osaka_pin` (`Evm.osaka`) and `osaka_idealized_pin`
  (`Evm.pinned`, the four recorded idealizations);
- EIP-150's forwarding rule: `osaka_forward` (`Evm.allButOne64`);
- the precompile table: `osaka_precompiles` (all of `Evm.Precompile`);
- the Yul view of the environment: `ofViews_field` and `osaka_blockhash`
  (`Yul.Views.Environment`, `Yul.Views.blockhash`);
- the stipend rule: `ForkSpec.osaka_stipendRule` in
  `Solidity/Semantics/Nondeterminism/ForkStipend.lean` (`Stipend.rule`).

**Block fields are intrinsic to the fork.** A `BlockEnv F` reads a field
only with a proof that `F` has it (`BlockEnv.read`). So `block.slotnum` under
Osaka is not a value that happens to be absent: it has no reading
(`osaka_no_slotnum`, `BlockEnv.field?_slotnum_osaka`). Under
`osakaWithSlotnum` it reads the environment's value. That instance is Osaka
plus EIP-7843's `SLOTNUM`, the field solc gates on Amsterdam; Amsterdam's
other changes are not modelled. `prague` is the fork before Osaka. It lacks
the P-256 precompile (EIP-7951) and EIP-7825's transaction gas cap.

**Block fields stay environment.** `EnvChoice F` is G01's session
environment plus a block environment after each history. A `ForkedSplit`
reads it, and `ForkedSplit.at F` is a split language whose environment is
`EnvChoice F`. So the fork is a third kind of input: neither quantified with
the environment nor produced by the compiler, but a setting both sides
share, as `EvmSpec.pin` is. `HoldsOn` asks for a list of forks.

The block environment is what X02 adds to the source. The fields mirror
`Yul.Views.EnvRead` and `Language.BlockField`. `ForkSpec.ofBlockField` maps a
`block.*` member to its field, so `block.difficulty` reads `prevrandao` when
`difficultyReadsPrevrandao` holds (EIP-4399).
-/

namespace Solidity.Semantics.Nondeterminism

open Solidity.Roadmap

/-! ## Forks and their choices -/

/-- Named forks, in order. Only `prague`, `osaka` and `amsterdam` have instances here. -/
inductive Fork where
  | london
  | paris
  | shanghai
  | cancun
  | prague
  | osaka
  | amsterdam
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

/-- The gas numbers of a fork's schedule the source rules read. -/
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

/-- **A fork**: its block fields, precompiles, limits and gas constants.
`number` and `timestamp` exist in every fork. -/
structure ForkSpec where
  fork : Fork
  has : EnvField → Bool
  number_has : has .number = true
  timestamp_has : has .timestamp = true
  /-- `block.difficulty` reads `prevrandao` (EIP-4399, from Paris). -/
  difficultyReadsPrevrandao : Bool
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
  /-- The stipend rule's gas per node and reserve (`Stipend.CostModel`). -/
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

/-- **Prague**: no P-256 precompile (EIP-7951) and no transaction gas cap
(EIP-7825), both Osaka's. -/
def prague : ForkSpec :=
  { osaka with
    fork := .prague
    precompile := fun p => p != .p256Verify
    txGasCap := none }

/-- **Osaka with `SLOTNUM`** (EIP-7843, which solc gates on Amsterdam).
Amsterdam's other changes are not modelled. -/
def osakaWithSlotnum : ForkSpec :=
  { osaka with
    fork := .amsterdam
    has := fun f => f == .slotnum || osakaHas f
    number_has := rfl
    timestamp_has := rfl }

/-- The four recorded idealizations of G01 Q2 and G06 Q2. -/
def idealize (F : ForkSpec) : ForkSpec :=
  { F with runtimeCodeLimit := none, initcodeLimit := none, txGasCap := none, blockGasLimited := false }

/-- The G06 pin of a fork G06 knows. -/
def pin? (F : ForkSpec) : Option Evm.Pin :=
  F.fork.toEvm?.map fun f =>
    { fork := f, runtimeCodeLimit := F.runtimeCodeLimit, initcodeLimit := F.initcodeLimit,
      txGasCap := F.txGasCap, blockGasLimited := F.blockGasLimited, callDepth := F.callDepth,
      stackLimit := F.stackLimit, stipend := F.gas.callStipend }

/-- The gas a call forwards at most. -/
def forward (F : ForkSpec) (g : Nat) : Nat := g - g / F.gas.forwardDivisor

/-- The field a `block.*` member reads. -/
def ofBlockField (F : ForkSpec) : Language.BlockField → EnvField
  | .coinbase => .coinbase
  | .difficulty => if F.difficultyReadsPrevrandao then .prevrandao else .difficulty
  | .prevrandao => .prevrandao
  | .number => .number
  | .gaslimit => .gaslimit
  | .chainid => .chainid
  | .basefee => .basefee
  | .blobbasefee => .blobbasefee
  | .slotnum => .slotnum

/-! ### Osaka is an instance -/

theorem osaka_pin : osaka.pin? = some Evm.osaka := rfl

theorem osaka_idealized_pin : osaka.idealize.pin? = some Evm.pinned := rfl

theorem osaka_forward (g : Nat) : osaka.forward g = Evm.allButOne64 g := rfl

theorem osaka_precompiles (p : Evm.Precompile) : osaka.precompile p = true := rfl

theorem osaka_stipend : osaka.gas.callStipend = Evm.pinned.stipend := rfl

/-- **`block.slotnum` is not an Osaka field.** -/
theorem osaka_no_slotnum : osaka.has .slotnum = false := rfl

theorem osakaWithSlotnum_slotnum : osakaWithSlotnum.has .slotnum = true := rfl

/-- `block.difficulty` reads `prevrandao` under Osaka. -/
theorem osaka_difficulty : osaka.ofBlockField .difficulty = .prevrandao := rfl

/-- Negative control: without EIP-4399 it reads its own field. -/
theorem preParis_difficulty :
    ({ osaka with difficultyReadsPrevrandao := false } : ForkSpec).ofBlockField .difficulty = .difficulty :=
  rfl

/-- Negative controls: Prague is not Osaka. -/
theorem prague_differs : prague.precompile .p256Verify = false ∧ prague.txGasCap = none ∧
    prague.pin? = none :=
  ⟨rfl, rfl, rfl⟩

/-- Only the slotnum field separates the Amsterdam draft from Osaka. -/
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

/-- A field, where the fork has it. -/
def field? (e : BlockEnv F) (f : EnvField) : Option Word :=
  if h : F.has f = true then some (e.read f h) else none

/-- A `block.*` member, where the fork has its field. -/
def blockField? (e : BlockEnv F) (b : Language.BlockField) : Option Word :=
  e.field? (F.ofBlockField b)

/-- `blockhash(q)`: the previous `F.blockhashWindow` blocks only. -/
def blockhash (e : BlockEnv F) (q : Word) : Word :=
  if q.val < e.number.val ∧ e.number.val - q.val ≤ F.blockhashWindow then e.historicalHash q
  else ⟨0, by decide⟩

/-- `blobhash(i)`. -/
def blobhash (e : BlockEnv F) (i : Word) : Word := e.blobHashes[i.val]?.getD ⟨0, by decide⟩

/-- Every field at one word (an inhabited witness for every fork). -/
def const (F : ForkSpec) (w : Word) : BlockEnv F := ⟨fun _ _ => w, fun _ => w, []⟩

theorem field?_of_has (e : BlockEnv F) {f : EnvField} (h : F.has f = true) :
    e.field? f = some (e.read f h) := by
  simp only [field?, h, dif_pos]

theorem field?_of_not_has (e : BlockEnv F) {f : EnvField} (h : F.has f = false) :
    e.field? f = none := by
  simp only [field?, h, Bool.false_eq_true, dif_neg, not_false_eq_true]

/-- **Under Osaka, `block.slotnum` has no reading.** -/
theorem field?_slotnum_osaka (e : BlockEnv ForkSpec.osaka) : e.blockField? .slotnum = none :=
  e.field?_of_not_has ForkSpec.osaka_no_slotnum

/-- Under the Amsterdam draft it reads the environment. -/
theorem field?_slotnum_withSlotnum (e : BlockEnv ForkSpec.osakaWithSlotnum) :
    e.blockField? .slotnum = some (e.read .slotnum rfl) :=
  e.field?_of_has rfl

end BlockEnv

/-! ### Osaka's block environment is the Yul view's -/

/-- The field of a Yul environment read. -/
def EnvField.ofRead : Yul.Views.EnvRead → EnvField
  | .coinbase => .coinbase
  | .number => .number
  | .timestamp => .timestamp
  | .prevrandao => .prevrandao
  | .gaslimit => .gaslimit
  | .chainid => .chainid
  | .basefee => .basefee
  | .blobbasefee => .blobbasefee
  | .origin => .origin
  | .gasprice => .gasprice

/-- The Yul read of an Osaka field. -/
def EnvField.toRead : (f : EnvField) → ForkSpec.osaka.has f = true → Yul.Views.EnvRead
  | .coinbase, _ => .coinbase
  | .number, _ => .number
  | .timestamp, _ => .timestamp
  | .prevrandao, _ => .prevrandao
  | .gaslimit, _ => .gaslimit
  | .chainid, _ => .chainid
  | .basefee, _ => .basefee
  | .blobbasefee, _ => .blobbasefee
  | .origin, _ => .origin
  | .gasprice, _ => .gasprice
  | .difficulty, h => absurd h (by decide)
  | .slotnum, h => absurd h (by decide)

/-- The Osaka block environment of a Yul environment. -/
def BlockEnv.ofViews (v : Yul.Views.Environment) : BlockEnv ForkSpec.osaka where
  read f h := v.read (f.toRead h)
  historicalHash := v.historicalHash
  blobHashes := v.blobHashes

theorem ofViews_has (r : Yul.Views.EnvRead) : ForkSpec.osaka.has (EnvField.ofRead r) = true := by
  cases r <;> rfl

/-- **Every Yul read is the Osaka field.** -/
theorem ofViews_field (v : Yul.Views.Environment) (r : Yul.Views.EnvRead) :
    (BlockEnv.ofViews v).field? (EnvField.ofRead r) = some (v.read r) := by
  rw [BlockEnv.field?_of_has _ (ofViews_has r)]
  cases r <;> rfl

/-- **Osaka's `blockhash` is the Yul view's.** -/
theorem osaka_blockhash (v : Yul.Views.Environment) (q : Word) :
    (BlockEnv.ofViews v).blockhash q = Yul.Views.blockhash v q := rfl

theorem osaka_blobhash (v : Yul.Views.Environment) (i : Word) :
    (BlockEnv.ofViews v).blobhash i = Yul.Views.blobhash v i := rfl

/-! ## The environment with block fields, and forked split languages -/

/-- **The environment under fork `F`**: G01's session environment and the
block inputs of the transaction after each history. -/
structure EnvChoice (F : ForkSpec) where
  session : SessionEnv
  block : List Event → BlockEnv F

/-- An environment is allowed when its session is. -/
def EnvChoice.Allowed {F : ForkSpec} (e : EnvChoice F) : Prop := e.session.Allowed

/-- **A split language with a fork parameter.** -/
structure ForkedSplit where
  Prog : Type
  Res : Type
  resLE : LE Res
  Allowed : (F : ForkSpec) → EnvChoice F → Prop
  Admissible : ForkSpec → Res → Prop
  sem : (F : ForkSpec) → CompilerChoice → Prog → EnvChoice F → Prefixes Res Event Outcome
  consistent : ∀ F c p e, @Prefixes.Consistent Res Event Outcome resLE (sem F c p e)

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

/-- A fork-blind program with the same allowed sessions and bounds at every
fork: Osaka suffices. -/
theorem holdsOn_of_forkBlind {forks : List ForkSpec} {art : Pipeline → Artifact} {p : L.Prog}
    {Φ : Prefix Event Outcome → Prop} (hb : L.ForkBlind p)
    (hal : ∀ F (e : EnvChoice F), L.Allowed F e → L.Allowed ForkSpec.osaka ⟨e.session, fun _ => BlockEnv.const _ ⟨0, by decide⟩⟩)
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
of the environment only. -/
def SplitSpec.forked (L : SplitSpec) (toEnv : SessionEnv → L.Env) : ForkedSplit where
  Prog := L.Prog
  Res := L.Res
  resLE := L.resLE
  Allowed _ e := L.Allowed (toEnv e.session)
  Admissible _ := L.Admissible
  sem _ c p e := L.sem c p (toEnv e.session)
  consistent _ c p e := L.consistent c p (toEnv e.session)

theorem SplitSpec.forked_blind (L : SplitSpec) (toEnv : SessionEnv → L.Env) (p : L.Prog) :
    (L.forked toEnv).ForkBlind p := by
  intro F F' c e e' hs
  show L.sem c p (toEnv e.session) = L.sem c p (toEnv e'.session)
  rw [hs]

/-! ## Witnesses and negative controls -/

namespace ForkControls

open ForkSpec

/-- A language whose run reads `block.slotnum` when the fork has it:
success with the field's low byte, a revert where it has none. -/
def slotnumLang : ForkedSplit where
  Prog := Unit
  Res := Nat
  resLE := inferInstance
  Allowed _ _ := True
  Admissible _ _ := True
  sem _ _ _ e _ := ⟨[], some (match (e.block []).blockField? .slotnum with
    | some w => .success [UInt8.ofNat w.val]
    | none => .revert [])⟩
  consistent _ _ _ _ _ _ _ := Prefix.Le.refl _

def reverts (x : Prefix Event Outcome) : Prop := x.final = some (.revert [])

/-- An inhabited environment at every fork. -/
def envAt (F : ForkSpec) (w : Word) : EnvChoice F :=
  ⟨{ deployer := ⟨0, by decide⟩, deployNonce := ⟨0, by decide⟩, deployValue := ⟨0, by decide⟩,
     deployArgs := [], balance := fun _ => ⟨0, by decide⟩, hasCode := fun _ _ => false,
     requests := fun _ _ => none, callee := fun _ => .answer (.success []) },
   fun _ => BlockEnv.const F w⟩

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
    .legacy (GasOracle.const ⟨0, by decide⟩) (envAt _ ⟨5, by decide⟩) trivial (0 : Nat) trivial
  simp only [reverts, slotnumLang, ForkedSplit.at, BlockEnv.field?_slotnum_withSlotnum] at this
  cases this

end ForkControls

end Solidity.Semantics.Nondeterminism
/-- info: 'Solidity.Semantics.Nondeterminism.ForkSpec.osaka_pin' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Semantics.Nondeterminism.ForkSpec.osaka_pin
/-- info: 'Solidity.Semantics.Nondeterminism.ForkSpec.osaka_idealized_pin' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Semantics.Nondeterminism.ForkSpec.osaka_idealized_pin
/-- info: 'Solidity.Semantics.Nondeterminism.ForkSpec.prague_differs' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Semantics.Nondeterminism.ForkSpec.prague_differs
/-- info: 'Solidity.Semantics.Nondeterminism.ForkSpec.osakaWithSlotnum_has' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Semantics.Nondeterminism.ForkSpec.osakaWithSlotnum_has
/-- info: 'Solidity.Semantics.Nondeterminism.BlockEnv.field?_slotnum_osaka' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Semantics.Nondeterminism.BlockEnv.field?_slotnum_osaka
/-- info: 'Solidity.Semantics.Nondeterminism.ofViews_field' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Semantics.Nondeterminism.ofViews_field
/-- info: 'Solidity.Semantics.Nondeterminism.osaka_blockhash' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Semantics.Nondeterminism.osaka_blockhash
/-- info: 'Solidity.Semantics.Nondeterminism.ForkedSplit.holdsOn_of_forkBlind' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Semantics.Nondeterminism.ForkedSplit.holdsOn_of_forkBlind
/-- info: 'Solidity.Semantics.Nondeterminism.ForkControls.slotnum_osaka' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Semantics.Nondeterminism.ForkControls.slotnum_osaka
/-- info: 'Solidity.Semantics.Nondeterminism.ForkControls.slotnum_withSlotnum_not' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Semantics.Nondeterminism.ForkControls.slotnum_withSlotnum_not
