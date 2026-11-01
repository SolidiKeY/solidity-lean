import Solidity.Backend.Opcode
import Solidity.Semantics.ContractWorld

/-!
# G31 environment instruction slices

An independent, gas-free meaning for the six admitted Osaka environment
instructions. Stack head is top. Words and account identities reuse the
intrinsic semantic types. `step` refuses all other instructions; it is not a
pinned-EVM interpreter. The caller must supply sufficient gas and execution
fuel and a stack below the real 1024-word capacity for pushes; these resource
conditions are not represented or proved by this local evaluator. The source denotation is the existing `State.envVal`,
never defined through instruction selection. Full EVM and world composition
remain separate obligations.
-/

namespace Solidity.Backend.Environment

abbrev Word := Semantics.Word
abbrev Address := ContractWorld.Address

/-- The execution frame and an arbitrary ledger. Own balance is a ledger read,
not a second unconstrained input. No time monotonicity is presumed. -/
structure Frame where
  self : Address
  sender : Address
  value : Word
  time : Word
  funds : Address → Word

/-- The low 160 bits of a stack word name the BALANCE account. -/
def account (w : Word) : Address :=
  let n : Nat := w.1.toNat % 2 ^ 160
  ⟨⟨(n : Int), by
    have h : w.1.toNat % 2 ^ 160 < 2 ^ 160 := Nat.mod_lt w.1.toNat (by decide : 0 < (2 : Nat) ^ 160)
    simp only [PrimTy.inRange, decide_eq_true_eq]
    constructor
    · omega
    · omega⟩, by
      change ((w.1.toNat % (2 : Nat) ^ 160 : Nat) : Int) < (2 : Int) ^ 160
      have h : w.1.toNat % 2 ^ 160 < 2 ^ 160 := Nat.mod_lt w.1.toNat (by decide : 0 < (2 : Nat) ^ 160)
      omega⟩

/-- Truncation is exact, including words with nonzero high bits. -/
theorem account_value (w : Word) : (account w).1.1 = (w.1.toNat % 2 ^ 160 : Nat) := rfl

/-- Already bounded addresses survive conversion without changing identity. -/
theorem account_address (a : Address) : account a.1 = a := by
  apply Subtype.ext
  apply Subtype.ext
  have hn : 0 ≤ a.1.1 := (of_decide_eq_true a.1.2).1
  have ht : a.1.1.toNat < 2 ^ 160 := by omega
  simp only [account, Nat.mod_eq_of_lt ht, Int.toNat_of_nonneg hn]

/-- Numeric observations of the frame, independently of code generation. -/
def observe (f : Frame) : EnvKey → Word
  | .msgSender => f.sender.1
  | .msgValue => f.value
  | .timestamp => f.time
  | .selfBalance => f.funds f.self
  | .selfAddress => f.self.1

/-- Actual Backend instruction selection, with no symbolic pseudo-opcodes. -/
def select : EnvKey → Instr
  | .msgSender => .op .CALLER
  | .msgValue => .op .CALLVALUE
  | .timestamp => .op .TIMESTAMP
  | .selfBalance => .op .SELFBALANCE
  | .selfAddress => .op .ADDRESS

/-- The local opcode meaning. BALANCE consumes one word; SELFBALANCE consumes
none. Underflow and instructions outside this slice fail explicitly. -/
def step (f : Frame) : Instr → List Word → Option (List Word)
  | .op .ADDRESS, st => some (f.self.1 :: st)
  | .op .CALLER, st => some (f.sender.1 :: st)
  | .op .CALLVALUE, st => some (f.value :: st)
  | .op .TIMESTAMP, st => some (f.time :: st)
  | .op .SELFBALANCE, st => some (f.funds f.self :: st)
  | .op .BALANCE, a :: st => some (f.funds (account a) :: st)
  | _, _ => none

/-- Every admitted observation preserves an arbitrary pre-existing stack tail. -/
theorem select_correct (f : Frame) (k : EnvKey) (tail : List Word) :
    step f (select k) tail = some (observe f k :: tail) := by cases k <;> rfl

/-- BALANCE uses the low address bits and preserves the tail after its operand. -/
theorem balance_correct (f : Frame) (a : Word) (tail : List Word) :
    step f (.op .BALANCE) (a :: tail) = some (f.funds (account a) :: tail) := rfl

theorem balance_address (f : Frame) (a : Address) (tail : List Word) :
    step f (.op .BALANCE) (a.1 :: tail) = some (f.funds a :: tail) := by
  rw [balance_correct, account_address]

theorem own_balance (f : Frame) (tail : List Word) :
    step f (.op .BALANCE) (f.self.1 :: tail) =
      step f (.op .SELFBALANCE) tail := by rw [balance_address]; rfl

/-- Arbitrary worlds, including arbitrary account catalogs and roles, share
exactly the existing intrinsic balance observation when their ledgers agree.
This is an observation adapter, not a world-execution composition theorem. -/
theorem world_balance {K : Type} {contracts : K → Contract}
    (w : ContractWorld.World contracts) (f : Frame) (ledger : f.funds = w.funds)
    (a : Word) (tail : List Word) :
    step f (.op .BALANCE) (a :: tail) = some (w.balance (account a) :: tail) := by
  rw [balance_correct, ledger]
  rfl

/-- Precisely the boundary absent from the older single-contract state:
identities are real addresses, and own balance is tied to the current ledger.
Storage, heap, locals, net deltas and the external-response oracle are arbitrary. -/
structure Represents {C : Contract} {Γ : Ctx} (f : Frame) (σ : State C Γ) : Prop where
  sender : σ.tx.msgSender = f.sender.1
  self : σ.tx.selfAddress = f.self.1
  value : σ.tx.msgValue = f.value
  time : σ.tx.timestamp = f.time
  balance : σ.selfBalance = f.funds f.self

theorem Represents.denote {C : Contract} {Γ : Ctx} {f : Frame} {σ : State C Γ}
    (h : Represents f σ) (k : EnvKey) : σ.envVal k = observe f k := by
  cases k
  · exact h.sender
  · exact h.value
  · exact h.time
  · exact h.balance
  · exact h.self

/-- Certificate against the current intrinsic expression denotation. No
restriction on the state's oracle, heap or net ledger is introduced. -/
theorem intrinsic_correct {C : Contract} {Γ : Ctx} {f : Frame} {σ : State C Γ}
    (h : Represents f σ) (k : EnvKey) (tail : List Word) :
    Val.evalT σ (.simple (.env k rfl) : Val C Γ .uint) = .ok (observe f k) ∧
    step f (select k) tail = some (observe f k :: tail) := by
  constructor
  · change Except.ok (σ.envVal k) = Except.ok (observe f k)
    rw [h.denote k]
  · exact select_correct f k tail

/-- The actual bytes of all five EnvKey constructors, in constructor order. -/
theorem selected_bytes :
    ([EnvKey.msgSender, .msgValue, .timestamp, .selfBalance, .selfAddress].map
      (fun k => (select k).encode)).flatten = [0x33, 0x34, 0x42, 0x47, 0x30] := by decide

theorem balance_bytes : (Instr.op .BALANCE).encode = [0x31] := rfl

theorem balance_underflow (f : Frame) : step f (.op .BALANCE) [] = none := rfl

/-- Excluded chain/code/log observations have no meaning in this slice. -/
theorem refused_fields (f : Frame) (st : List Word) :
    step f (.op .CHAINID) st = none ∧ step f (.op .NUMBER) st = none ∧
    step f (.op .ORIGIN) st = none ∧ step f (.op .EXTCODEHASH) st = none ∧
    step f (.op (.LOG 0)) st = none := by exact ⟨rfl, rfl, rfl, rfl, rfl⟩

end Solidity.Backend.Environment
