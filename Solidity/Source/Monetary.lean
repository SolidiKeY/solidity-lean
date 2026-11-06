import Solidity.Roadmap.Contracts

/-!
# H19 natural monetary interface

Balances are exact naturals, including values outside the EVM word range.
Fits is an explicit predicate, not a constructor field. The total wordView
is explicitly modular; it is lossless only under Fits. checkedWord rejects
an out-of-range projection, not a failure plan or transaction. Consumers
must derive the invariant for actual EVM-reachable states before claiming
balance agreement; a favorable modular decoder is not such a proof.

This interface step does not yet change Source.Account.balance, the ledger,
Eval.balance or root funding. Their measured migration remains open.
-/
namespace Solidity.Source.Monetary
open Solidity.Roadmap (Address Word)

abbrev Balance := Nat

def wordLimit : Nat := 2 ^ 256

def Fits (balance : Balance) : Prop := balance < wordLimit

instance (balance : Balance) : Decidable (Fits balance) :=
  inferInstanceAs (Decidable (balance < wordLimit))

def BalancesFit (balances : Address → Balance) : Prop :=
  ∀ address, Fits (balances address)

def ofWord (word : Word) : Balance := word.val

/-- Word-valued observations are a separate projection of exact money. -/
def wordView (balance : Balance) : Word :=
  ⟨balance % wordLimit, Nat.mod_lt _ (by decide : 0 < wordLimit)⟩

def checkedWord (balance : Balance) : Option Word :=
  if h : Fits balance then some ⟨balance,h⟩ else none

def fromWords (balances : Address → Word) : Address → Balance :=
  fun address => ofWord (balances address)

/-- The existing recipient-overflow refusal is retained by this primitive. -/
def credit? (balance : Balance) (value : Word) : Option Balance :=
  if balance + value.val < wordLimit then some (balance + value.val) else none

/-- Exact natural subtraction after the actual affordability check. -/
def debit? (balance : Balance) (value : Word) : Option Balance :=
  if value.val ≤ balance then some (balance - value.val) else none

/-- An admissible monetary datum, not an admitted EVM-word projection. -/
def wide : Balance := wordLimit


/-- The explicit range fact is produced from actual word-valued input. -/
theorem ofWord_fits (word : Word) : Fits (ofWord word) := word.isLt

/-- A word projection loses no information on a proved in-range balance. -/
theorem wordView_exact (balance : Balance) (h : Fits balance) :
    (wordView balance).val = balance := by
  simp only [wordView, Nat.mod_eq_of_lt h]

/-- Word snapshots produce the invariant; it is not baked into Balance. -/
theorem fromWords_fit (snapshot : Address → Word) : BalancesFit (fromWords snapshot) :=
  fun address => (snapshot address).isLt

theorem wide_exact : wide = 2 ^ 256 := rfl
theorem wide_not_fits : ¬ Fits wide := by decide
theorem wide_checked_rejected : checkedWord wide = none := by decide
theorem wide_word_projection : (wordView wide).val = 0 := by decide
theorem wide_debit : debit? wide ⟨1,by decide⟩ = some (2 ^ 256 - 1) := by decide
theorem credit_overflow_refused : credit? (2 ^ 256 - 1) ⟨1,by decide⟩ = none := by decide

end Solidity.Source.Monetary
