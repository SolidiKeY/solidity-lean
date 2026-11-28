import Solidity.Calculus.ProvesDerive
import Solidity.Calculus.SurfaceSpec
import Solidity.Calculus.Surface
import Solidity.Calculus.Closers

/-!
# solc-verify: records in a mapping of structs

Source: <https://github.com/SRI-CSL/solidity/blob/8ea107cecd90ffff0d6a8f276b434b5ac9aa043b/test/solc-verify/examples/Storage.sol>.
Changes: `@notice postcondition` is `ensures`. A `modifies L if c` whose `c`
the function `require`s is `assignable L`. `clear`'s two `modifies`
(its record; any record when the owner sends) are `assignable records`
and an `ensures` that a non-owner changes no other record. The parameter
`at`, a specification keyword, is `at_`. solc-verify proves everything.
-/

namespace Solidity.Examples.Benchmark.SolcVerify.Storage

/-- The source contract, with its clauses. -/
def Storage : Contract := contract!{
  struct Record {
    int data;
    bool set;
  }
  mapping(address=>Record) records;
  address owner;
  constructor() {
    owner = msg.sender;
  }
  assignable owner;
  function changeOwner(address newOwner) public {
    require(msg.sender == owner);
    owner = newOwner;
  }
  function isSet(Record storage record) internal view returns(bool) {
    return record.set;
  }
  assignable records[msg.sender];
  ensures records[msg.sender].set;
  ensures records[msg.sender].data == data;
  function set(int data) public {
    require(!isSet(records[msg.sender]));
    Record memory rec = Record(data, true);
    records[msg.sender] = rec;
  }
  assignable records[msg.sender].data;
  ensures records[msg.sender].data == data;
  function update(int data) public {
    Record storage rec = records[msg.sender];
    require(isSet(rec));
    rec.data = data;
  }
  assignable records;
  ensures msg.sender != \old(owner) -> \forall address a; a != msg.sender -> records[a].set == \old(records[a].set) && records[a].data == \old(records[a].data);
  ensures !records[at_].set;
  ensures records[at_].data == 0;
  function clear(address at_) public {
    require(msg.sender == owner || msg.sender == at_);
    Record storage rec = records[at_];
    rec.set = false;
    rec.data = 0;
  }
}
local instance : InContract := ⟨Storage⟩
open scoped Scoped

/-- The constructor has no clause. Proved. -/
theorem constructor_spec : ⊢ spec!{ constructor } := by sol_prove
/-- `changeOwner` modifies `owner` only. Proved. -/
theorem changeOwner_spec : ⊢ spec!{ changeOwner } := by sol_prove
/-- `set` writes the sender's record, set, with `data`. Proved. -/
theorem set_spec : ⊢ spec!{ set } := by sol_prove
/-- `update` writes the sender's `data` only. Proved. -/
theorem update_spec : ⊢ spec!{ update } := by sol_prove
/-- `clear` resets the record at `at_`, and a non-owner touches no other. Proved. -/
theorem clear_spec : ⊢ spec!{ clear } := by sol_auto

end Solidity.Examples.Benchmark.SolcVerify.Storage
