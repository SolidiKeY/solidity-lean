import Solidity.Typing.Values

namespace H62.AuditTyping.ValuesListsWitnesses
open Solidity
open Solidity.Semantics

-- Both carrier types are inhabited Bool, with its actual equality instance.
theorem lookup_mem : ∃ (k v : Bool) (l : List (Bool × Bool)), (k,v) ∈ l :=
  ⟨false, false, [(false,false)], by decide⟩

theorem lookup_nodup : ∃ (k v : Bool) (l : List (Bool × Bool)),
    nodupKeysB l = true ∧ (k,v) ∈ l :=
  ⟨false, false, [(false,false)], by decide⟩

theorem mem_set : ∃ (k v : Bool) (e : Bool × Bool) (l : List (Bool × Bool)), e ∈ setBy k v l :=
  ⟨false, false, (false,false), [], by decide⟩

theorem none_set : ∃ (k k' _v : Bool) (l : List (Bool × Bool)), k ≠ k' ∧ lookupBy k l = none :=
  ⟨false, true, false, [], by decide⟩

theorem nodup_set : ∃ (_k _v : Bool) (l : List (Bool × Bool)), nodupKeysB l = true :=
  ⟨false, false, [], by decide⟩

theorem set_lookup : ∃ (k v : Bool) (l : List (Bool × Bool)), lookupBy k l = some v :=
  ⟨false, false, [(false,false)], by decide⟩

theorem lookup_append : ∃ (k : Bool) (l₁ _l₂ : List (Bool × Bool)), lookupBy k l₁ = none :=
  ⟨false, [], [(false,false)], by decide⟩

theorem set_append : ∃ (k _v : Bool) (l₁ _l₂ : List (Bool × Bool)), lookupBy k l₁ = none :=
  ⟨false, false, [], [(false,false)], by decide⟩

theorem nodup_mid : ∃ (k v : Bool) (l₁ l₂ : List (Bool × Bool)), nodupKeysB (l₁ ++ (k,v)::l₂) = true :=
  ⟨false, false, [], [], by decide⟩

end H62.AuditTyping.ValuesListsWitnesses
