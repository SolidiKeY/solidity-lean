import Solidity.Semantics.Nondeterminism.Fork
import Solidity.Yul.Views.Inputs
import Solidity.Language.Features

/-!
# Osaka's block environment agrees with the Yul view and the source syntax (S6.1)

Kept apart from `Solidity/Semantics/Nondeterminism/Fork.lean`, so the fork
parameter itself imports no Yul or `Lean` module.

- `BlockEnv.ofViews` reads a Yul `Environment` as an Osaka block
  environment. Every Yul read is the Osaka field (`ofViews_field`), and
  `blockhash` and `blobhash` agree (`osaka_blockhash`, `osaka_blobhash`).
- `ForkSpec.ofBlockField` maps a `block.*` member (`Language.BlockField`,
  the parser's diagnostic type, which has no `timestamp` member) to its
  field. `block.difficulty` reads `prevrandao` under Osaka.
-/

namespace Solidity.Semantics.Nondeterminism

open Solidity.Roadmap

/-- The field a `block.*` member reads. -/
def ForkSpec.ofBlockField (F : ForkSpec) : Language.BlockField → EnvField
  | .coinbase => .coinbase
  | .difficulty => difficultyField F.difficultyReadsPrevrandao
  | .prevrandao => .prevrandao
  | .number => .number
  | .gaslimit => .gaslimit
  | .chainid => .chainid
  | .basefee => .basefee
  | .blobbasefee => .blobbasefee
  | .slotnum => .slotnum

/-- A `block.*` member, where the fork has its field. -/
def BlockEnv.blockField? {F : ForkSpec} (e : BlockEnv F) (b : Language.BlockField) : Option Word :=
  e.field? (F.ofBlockField b)

theorem osaka_difficulty : ForkSpec.osaka.ofBlockField .difficulty = .prevrandao := rfl

theorem control_difficulty : ForkSpec.difficultyControl.ofBlockField .difficulty = .difficulty := rfl

/-- `block.slotnum` has no reading under Osaka. -/
theorem blockField_slotnum_osaka (e : BlockEnv ForkSpec.osaka) : e.blockField? .slotnum = none :=
  e.field?_slotnum_osaka

/-- `block.difficulty` always has a reading. -/
theorem blockField_difficulty {F : ForkSpec} (e : BlockEnv F) :
    e.blockField? .difficulty = some e.difficulty :=
  e.field?_of_has F.difficulty_has

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
    (BlockEnv.ofViews v).blobhash? i = some (Yul.Views.blobhash v i) := rfl

end Solidity.Semantics.Nondeterminism
/-- info: 'Solidity.Semantics.Nondeterminism.ofViews_field' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Semantics.Nondeterminism.ofViews_field
/-- info: 'Solidity.Semantics.Nondeterminism.osaka_blockhash' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Semantics.Nondeterminism.osaka_blockhash
/-- info: 'Solidity.Semantics.Nondeterminism.osaka_blobhash' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Semantics.Nondeterminism.osaka_blobhash
/-- info: 'Solidity.Semantics.Nondeterminism.blockField_slotnum_osaka' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Semantics.Nondeterminism.blockField_slotnum_osaka
/-- info: 'Solidity.Semantics.Nondeterminism.blockField_difficulty' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Semantics.Nondeterminism.blockField_difficulty
