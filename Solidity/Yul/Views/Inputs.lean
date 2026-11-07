import Solidity.Yul.Views.WordMemory

/-! Raw input preparation. No frontend row is reopened by these definitions.
The environment is universally supplied, never sampled or inferred from code.
Fork admission, source integration and shared-session agreement remain gates. -/
namespace Solidity.Yul.Views

/-- Raw calldata loads pad missing bytes with zero, even beyond the end. -/
def calldataBytes (input : List UInt8) : ByteView := fun a => input[a]?.getD 0

/-- Successful calldata input must fit the EVM word-sized length. -/
def CalldataValid (input : List UInt8) : Prop := input.length < 2 ^ 256

def calldatasize (input : List UInt8) : Nat := input.length

def calldatasizeWord (input : List UInt8) (h : CalldataValid input) : Roadmap.Word :=
  ⟨input.length, h⟩

def calldataload (input : List UInt8) (a : Nat) : Nat := mloadNat (calldataBytes input) a

/-- Intrinsically bounded raw load, for eventual Yul builtin integration. -/
def calldataloadWord (input : List UInt8) (a : Nat) : Roadmap.Word :=
  mload (calldataBytes input) a

def calldatacopy (m : ByteView) (input : List UInt8) (dst src n : Nat) : ByteView :=
  copyBytes m (calldataBytes input) dst src n

theorem calldata_zero (input : List UInt8) (a : Nat) (h : input.length ≤ a) :
    calldataBytes input a = 0 := by
  simp only [calldataBytes, List.getElem?_eq_none h, Option.getD_none]

theorem calldataload_zero (input : List UInt8) (a : Nat) (ha : input.length ≤ a) :
    calldataload input a = 0 := by
  have hz : ∀ n, readBE (calldataBytes input) a n = 0 := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [readBE, ih, calldata_zero input (a + n) (by omega)]
      rfl
  exact hz 32

/-- Uses the approved fixed hash, without any collision premise. -/
def keccak256 (fixed : Roadmap.Evm.Fixed) (m : ByteView) (a n : Nat) : Roadmap.Word :=
  ⟨fixed.keccak (readBytes m a n), fixed.keccak_lt _⟩

theorem keccak256_congr (fixed : Roadmap.Evm.Fixed) (m m' : ByteView) (a n : Nat)
    (h : readBytes m a n = readBytes m' a n) :
    keccak256 fixed m a n = keccak256 fixed m' a n := by
  apply Fin.ext
  exact congrArg fixed.keccak h

/-- The approved Osaka environment inputs. No gas/msize/pc/own-code operation. -/
inductive EnvRead where
  | coinbase | number | timestamp | prevrandao | gaslimit | chainid
  | basefee | blobbasefee | origin | gasprice
  deriving DecidableEq, Repr

structure Environment where
  coinbase : Roadmap.Address
  origin : Roadmap.Address
  number : Roadmap.Word
  timestamp : Roadmap.Word
  prevrandao : Roadmap.Word
  gaslimit : Roadmap.Word
  chainid : Roadmap.Word
  basefee : Roadmap.Word
  blobbasefee : Roadmap.Word
  gasprice : Roadmap.Word
  historicalHash : Roadmap.Word → Roadmap.Word
  blobHashes : List Roadmap.Word

def Environment.read (e : Environment) : EnvRead → Roadmap.Word
  | .coinbase => ⟨e.coinbase.val, Nat.lt_trans e.coinbase.isLt (by decide)⟩
  | .origin => ⟨e.origin.val, Nat.lt_trans e.origin.isLt (by decide)⟩
  | .number => e.number
  | .timestamp => e.timestamp
  | .prevrandao => e.prevrandao
  | .gaslimit => e.gaslimit
  | .chainid => e.chainid
  | .basefee => e.basefee
  | .blobbasefee => e.blobbasefee
  | .gasprice => e.gasprice

/-- Osaka blockhash: strictly previous 256 blocks only. -/
def blockhash (e : Environment) (query : Roadmap.Word) : Roadmap.Word :=
  if query.val < e.number.val ∧ e.number.val - query.val ≤ 256 then e.historicalHash query else 0

/-- Every universally supplied environment returns its own historical hash for
an eligible prior block; no hash value or compiler behavior is assumed. -/
theorem blockhash_in_window (e : Environment) (query : Roadmap.Word)
    (past : query.val < e.number.val) (recent : e.number.val - query.val ≤ 256) :
    blockhash e query = e.historicalHash query :=
  if_pos ⟨past, recent⟩

/-- Regression boundary: current/future blocks and blocks older than the prior
256-block window return zero, independently of the historical-hash function. -/
theorem blockhash_outside_window (e : Environment) (query : Roadmap.Word)
    (outside : ¬ (query.val < e.number.val ∧ e.number.val - query.val ≤ 256)) :
    blockhash e query = 0 :=
  if_neg outside

def blobhash (e : Environment) (i : Roadmap.Word) : Roadmap.Word :=
  e.blobHashes[i.val]?.getD 0

/-- An eligible blob index returns the supplied word at that exact index.
No blob list is sampled or inferred from program code. -/
theorem blobhash_in_bounds (e : Environment) (index : Roadmap.Word)
    (inside : index.val < e.blobHashes.length) :
    blobhash e index = e.blobHashes[index.val]'inside := by
  exact congrArg (fun entry => entry.getD 0) (List.getElem?_eq_getElem inside)

/-- Regression boundary: every index beyond the supplied blob list yields zero,
independently of all other environment fields and hash inputs. -/
theorem blobhash_outside_bounds (e : Environment) (index : Roadmap.Word)
    (outside : e.blobHashes.length ≤ index.val) : blobhash e index = 0 := by
  exact congrArg (fun entry => entry.getD 0) (List.getElem?_eq_none outside)

theorem environment_address_width (e : Environment) :
    (e.read .coinbase).val < 2 ^ 160 ∧ (e.read .origin).val < 2 ^ 160 :=
  ⟨e.coinbase.isLt, e.origin.isLt⟩

end Solidity.Yul.Views
