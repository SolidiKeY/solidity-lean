import SolidityBridge.ExternalEvm.FiniteStorage
import SolidityBridge.ExternalEvm.RBMapErase
import EvmYul.StateOps

/-! Actual upstream account storage reads and writes, including zero erasure.
Account presence is explicit; no hash injectivity or address separation is used. -/
namespace Solidity.Evm.StorageSlots
open Batteries

def encode (a : Fin W) : EvmYul.UInt256 :=
  ⟨⟨a.val, by simpa only [EvmYul.UInt256.size, W] using a.isLt⟩⟩

def decode (a : EvmYul.UInt256) : Fin W :=
  ⟨a.toNat, by simpa only [EvmYul.UInt256.size, W] using a.val.isLt⟩

theorem encode_decode (a : EvmYul.UInt256) : encode (decode a) = a := by
  cases a
  rfl

theorem decode_encode (a : Fin W) : decode (encode a) = a := rfl

/-- The relation reads actual upstream account storage, including the absent
account's zero default. Access-list changes are not storage writes. -/
def storageRead (s : EvmYul.State .EVM) (n : EvmYul.UInt256) : Fin W :=
  decode (EvmYul.State.sload s n).2

private theorem word_compare_nat (a b : EvmYul.UInt256) :
    compare a b = compare a.val.val b.val.val := by
  cases a with
  | mk a =>
    cases b with
    | mk b =>
      change (compare a.val b.val).then .eq = compare a.val b.val
      cases compare a.val b.val <;> rfl

local instance wordTrans : Std.TransCmp (compare : EvmYul.UInt256 → EvmYul.UInt256 → Ordering) where
  eq_swap := by
    intro a b
    rw [word_compare_nat, word_compare_nat]
    exact Std.OrientedCmp.eq_swap
  isLE_trans := by
    intro a b c hab hbc
    rw [word_compare_nat] at hab hbc ⊢
    exact Std.TransCmp.isLE_trans hab hbc

local instance addressTrans : Std.TransCmp (compare : EvmYul.AccountAddress → EvmYul.AccountAddress → Ordering) :=
  inferInstanceAs (Std.TransCmp (compareOn (fun a : EvmYul.AccountAddress => a.val)))

private theorem word_compare_eq (a b : EvmYul.UInt256) : compare a b = .eq ↔ a = b := by
  rw [word_compare_nat, Nat.compare_eq_eq]
  constructor
  · intro h
    cases a
    cases b
    exact congrArg EvmYul.UInt256.mk (Fin.ext h)
  · rintro rfl
    rfl

private theorem word_beq_eq (a b : EvmYul.UInt256) : (a == b) = true ↔ a = b := by
  cases a with
  | mk a =>
    cases b with
    | mk b =>
      change (a == b) = true ↔ EvmYul.UInt256.mk a = EvmYul.UInt256.mk b
      rw [beq_iff_eq]
      exact ⟨congrArg EvmYul.UInt256.mk, EvmYul.UInt256.mk.inj⟩

/-- Read-over-write for the actual account transformer. The zero branch
uses the proved erase law, so nonempty initial storage and clears are covered. -/
theorem account_read_write (acc : EvmYul.Account .EVM) (key value query : EvmYul.UInt256) :
    (acc.updateStorage key value).lookupStorage query =
      if query = key then value else acc.lookupStorage query := by
  unfold EvmYul.Account.updateStorage
  split
  · rename_i hz
    have hv : value = (default : EvmYul.UInt256) := (word_beq_eq value default).mp hz
    subst value
    change (acc.storage.erase key).findD query (.ofNat 0) = _
    rw [RBMap.findD, find_erase]
    by_cases hq : query = key
    · subst query
      rw [if_pos (Std.ReflCmp.compare_self), if_pos rfl]
      rfl
    · have hc : compare key query ≠ .eq := by
        intro he
        exact hq ((word_compare_eq key query).mp he).symm
      rw [if_neg hc, if_neg hq]
      rfl
  · change (acc.storage.insert key value).findD query (.ofNat 0) = _
    rw [RBMap.findD, RBMap.find?_insert]
    by_cases hq : query = key
    · subst query
      rw [if_pos (Std.ReflCmp.compare_self), if_pos rfl]
      rfl
    · have hc : compare query key ≠ .eq := by
        intro he
        exact hq ((word_compare_eq query key).mp he)
      rw [if_neg hc, if_neg hq]
      rfl

/-- The actual SSTORE transformer preserves the executing account and installs
its updated storage. Refund/access-list effects are retained but unobserved. -/
theorem account_after_sstore (s : EvmYul.State .EVM) (acc : EvmYul.Account .EVM)
    (ha : s.lookupAccount s.executionEnv.codeOwner = some acc)
    (key value : EvmYul.UInt256) :
    (EvmYul.State.sstore s key value).lookupAccount
      (EvmYul.State.sstore s key value).executionEnv.codeOwner =
      some (acc.updateStorage key value) := by
  rcases acc with ⟨⟨nonce, balance, storage, code⟩, transient⟩
  have ha' : s.accountMap.find? s.executionEnv.codeOwner =
      some (EvmYul.Account.mk ⟨nonce, balance, storage, code⟩ transient) := ha
  simp only [EvmYul.State.sstore, EvmYul.State.lookupAccount, RBMap.find!, ha',
    Option.getD_some, Option.option]
  change (s.accountMap.insert s.executionEnv.codeOwner
    ((EvmYul.Account.mk ⟨nonce, balance, storage, code⟩ transient).updateStorage key value)).find?
      s.executionEnv.codeOwner = _
  exact RBMap.find?_insert_of_eq _ Std.ReflCmp.compare_self

/-- Universal actual-evaluator storage law on a present executing account.
No restriction on initial storage, zero values, or other account entries. -/
theorem storage_read_write (s : EvmYul.State .EVM) (acc : EvmYul.Account .EVM)
    (ha : s.lookupAccount s.executionEnv.codeOwner = some acc)
    (key value query : EvmYul.UInt256) :
    storageRead (EvmYul.State.sstore s key value) query =
      if query = key then decode value else storageRead s query := by
  have hp := account_after_sstore s acc ha key value
  change decode (((EvmYul.State.sstore s key value).lookupAccount
    (EvmYul.State.sstore s key value).executionEnv.codeOwner).option
      (.ofNat 0) (fun a => a.lookupStorage query)) =
    if query = key then decode value else
      decode ((s.lookupAccount s.executionEnv.codeOwner).option (.ofNat 0) (fun a => a.lookupStorage query))
  rw [hp, ha]
  change decode ((acc.updateStorage key value).lookupStorage query) =
    if query = key then decode value else decode (acc.lookupStorage query)
  rw [account_read_write]
  split <;> rfl

end Solidity.Evm.StorageSlots

/-- info: 'Solidity.Evm.StorageSlots.account_read_write' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Evm.StorageSlots.account_read_write
/-- info: 'Solidity.Evm.StorageSlots.storage_read_write' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Evm.StorageSlots.storage_read_write
