import Solidity.Backend.Environment.Composition

/-! G31 backfill B: environment frames, ledger footprints and stable repeated reads. -/
namespace Solidity.Backend.Environment

/-- Precisely stated whole-frame stability. Forced credits and callback frames
are not assumed to satisfy this; the footprint laws below permit other changes. -/
structure Stable (f g : Frame) : Prop where
  self : f.self = g.self
  sender : f.sender = g.sender
  value : f.value = g.value
  time : f.time = g.time
  ledger : ∀ a, f.funds a = g.funds a

theorem Stable.observe {f g : Frame} (h : Stable f g) (k : EnvKey) :
    observe f k = observe g k := by
  cases k
  · exact congrArg Subtype.val h.sender
  · exact h.value
  · exact h.time
  · exact (h.ledger f.self).trans (congrArg g.funds h.self)
  · exact congrArg Subtype.val h.self

theorem stable_selection {f g : Frame} (h : Stable f g) (k : EnvKey) (tail : List Word) :
    step f (select k) tail = step g (select k) tail := by
  rw [select_correct, select_correct, h.observe]

/-- BALANCE depends only on its truncated address's entry; every other frame
field and every other ledger entry may change. -/
theorem balance_frame (f g : Frame) (word : Word) (tail : List Word)
    (entry : f.funds (account word) = g.funds (account word)) :
    step f (.op .BALANCE) (word :: tail) = step g (.op .BALANCE) (word :: tail) := by
  rw [balance_correct, balance_correct, entry]

def overwriteFunds (f : Frame) (address : Address) (newBalance : Word) : Frame :=
  { f with funds := fun a => if a = address then newBalance else f.funds a }

/-- Extending/changing the ledger away from a read account is a frame. -/
theorem ledger_other (f : Frame) (changed : Address) (amount word : Word)
    (tail : List Word) (different : account word ≠ changed) :
    step (overwriteFunds f changed amount) (.op .BALANCE) (word :: tail) =
      step f (.op .BALANCE) (word :: tail) := by
  apply balance_frame
  exact if_neg different

/-- Own-balance stability requires agreement at self, not merely the transaction
identity. In particular it must not be asserted across arbitrary forced credits. -/
theorem self_balance_frame (f g : Frame) (tail : List Word)
    (ownEntry : f.funds f.self = g.funds g.self) :
    step f (.op .SELFBALANCE) tail = step g (.op .SELFBALANCE) tail := by
  change some (f.funds f.self :: tail) = some (g.funds g.self :: tail)
  rw [ownEntry]

theorem repeated_read (f : Frame) (k : EnvKey) (tail : List Word) :
    (step f (select k) tail).bind (step f (select k)) =
      some (observe f k :: observe f k :: tail) := by
  rw [select_correct]
  exact select_correct f k _

theorem repeated_across_stable {f g : Frame} (h : Stable f g) (k : EnvKey)
    (tail : List Word) :
    (step f (select k) tail).bind (step g (select k)) =
      some (observe f k :: observe f k :: tail) := by
  rw [select_correct]
  change step g (select k) (observe f k :: tail) = _
  rw [select_correct, ← h.observe]

/-- BALANCE consumes its operand, so repeated reads explicitly reinsert the
same address. Across frames only this account entry needs to remain stable. -/
theorem repeated_balance (f g : Frame) (word : Word) (tail : List Word)
    (entry : f.funds (account word) = g.funds (account word)) :
    (step f (.op .BALANCE) (word :: tail)).bind
      (fun stack => step g (.op .BALANCE) (word :: stack)) =
      some (f.funds (account word) :: f.funds (account word) :: tail) := by
  rw [balance_correct]
  change step g (.op .BALANCE) (word :: f.funds (account word) :: tail) = _
  rw [balance_correct, ← entry]

/-- Arbitrary source storage, heap/typing extension, locals, contract and net
ledger changes are harmless for environment reads only under these two explicit
stability equalities. No source-world theorem is modified. -/
theorem source_environment_frame {C D : Contract} {Γ Δ : Ctx}
    (σ : State C Γ) (τ : State D Δ) (tx : σ.tx = τ.tx)
    (balance : σ.selfBalance = τ.selfBalance) (k : EnvKey) :
    σ.envVal k = τ.envVal k := by
  cases k
  · exact congrArg TTx.msgSender tx
  · exact congrArg TTx.msgValue tx
  · exact congrArg TTx.timestamp tx
  · exact balance
  · exact congrArg TTx.selfAddress tx

/-- The legacy response table is not an observed environment field. Its arbitrary
replacement does not restrict the final history-dependent oracle obligation. -/
theorem response_table_frame {C : Contract} {Γ : Ctx} (σ : State C Γ)
    (responses : List (Semantics.ExtKey × Semantics.ExtResult)) (k : EnvKey) :
    ({ σ with tx := { σ.tx with ext := responses } } : State C Γ).envVal k = σ.envVal k := by
  cases k <;> rfl

def admittedOp : Op → Bool
  | .ADDRESS | .CALLER | .CALLVALUE | .TIMESTAMP | .BALANCE | .SELFBALANCE => true
  | _ => false

/-- Exhaustive local refusal: no excluded opcode accidentally enters the
six-opcode environment relation, including code/log/chain/gas observations. -/
theorem refuse_non_environment (f : Frame) (op : Op) (tail : List Word)
    (excluded : admittedOp op = false) : step f (.op op) tail = none := by
  cases op <;> first | rfl | contradiction

/-- Every excluded BlockField and the raw msg/tx fields remain absent from the
committed EnvKey parser; timestamp/sender/value are the positive controls. -/
theorem excluded_constructor_controls :
    (["coinbase", "difficulty", "prevrandao", "number", "gaslimit", "chainid",
      "basefee", "blobbasefee", "slotnum", "blockhash"].map
      (EnvKey.ofParts "block")) = List.replicate 10 none ∧
    EnvKey.ofParts "msg" "data" = none ∧ EnvKey.ofParts "msg" "sig" = none ∧
    EnvKey.ofParts "tx" "origin" = none ∧ EnvKey.ofParts "tx" "gasprice" = none ∧
    EnvKey.ofParts "block" "timestamp" = some .timestamp ∧
    EnvKey.ofParts "msg" "sender" = some .msgSender ∧
    EnvKey.ofParts "msg" "value" = some .msgValue := by decide +kernel

/-- Exact finite opcode boundary of the composed evaluator. -/
def sliceOpSupported : Op → Bool
  | .ADDRESS | .CALLER | .CALLVALUE | .TIMESTAMP | .BALANCE | .SELFBALANCE |
    .MSTORE8 | .KECCAK256 | .SUB | .MSTORE | .SHR | .SHL => true
  | _ => false

theorem slice_refuses_unsupported (f : Frame) (op : Op) (s : Slice)
    (unsupported : sliceOpSupported op = false) : runSlice f [.op op] s = none := by
  have h : sliceStep f (.op op) s = none := by
    cases op <;> first | rfl | contradiction
  change (sliceStep f (.op op) s).bind _ = none
  rw [h]
  rfl

/-- Excluded observations are refused by the composed slice too, not just its
environment subrelation. STATICCALL is deliberately still outside this evaluator. -/
theorem slice_refusal_controls (f : Frame) (s : Slice) :
    [Op.COINBASE, .PREVRANDAO, .NUMBER, .GASLIMIT, .CHAINID, .BASEFEE,
      .BLOBBASEFEE, .BLOBHASH, .BLOCKHASH, .ORIGIN, .GASPRICE, .GAS, .MSIZE, .PC,
      .RETURNDATASIZE, .RETURNDATACOPY, .CALLDATALOAD,
      .CODESIZE, .CODECOPY, .EXTCODESIZE, .EXTCODECOPY, .EXTCODEHASH, .LOG 0].map
      (fun op => runSlice f [.op op] s) = List.replicate 23 none := rfl

end Solidity.Backend.Environment
