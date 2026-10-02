import Solidity.Calculus.Chains
import Solidity.Calculus.ChainRewrites
import Solidity.Calculus.Close
import Solidity.FreshNames

/-!
# The additional storage array cases as chains

The calculus's push examples as chains over any modality `m` and postcondition `φ`
(`Examples/Chains/Storage.lean` says how to read one).  Everything runs in `Pushes`: `values`, `tokens`,
`bucket.tokens`, `bob`, a `Token` state variable `tok`, and `makeValue()`, which reads `seed`.
Stand-ins: `bucket.tokens` for `alice.account.tokens`, `tok` (copied as `find(storage, tok)`) for a token
value, `Token storage sp = tokens.push(); … sp.value` for `tokens.push().value`, a member of a call, which is
refused.  A call is inlined, so `makeValue()` leaves its callee's local `se2` where the printed line has the
call itself.  Not drawn: merges of a push's alias `{ storage := … ‖ sp := … }` under another update, which
do not merge (a parallel update of locals and the storage over another).
-/

namespace Solidity.Examples.Chains.StorageArrays

/-! ## Example: Additional Storage Array Cases -/

/-- The arrays of the examples in one contract. -/
def Pushes : Contract := contract!{
  uint seed; uint[] values; Token[] tokens; Person bob; TokenBucket bucket; Token tok;
  function makeValue() returns (uint) { return seed; }
}
local instance : InContract := ⟨Pushes⟩
section
variable (m : Modality) (φ : Post Pushes)

namespace PushCall
def names : FreshTable := [("pv", "se1")]
local instance : FreshNames := .ofTable names
#guard (FreshNames.clashes Pushes names).isEmpty
/-- `values.push(makeValue());`: the argument is captured (`pv`), the call inlined and run, then the value pushed; the length is `values.length`. -/
def chain :
    dl![m]{ ⟨[ values.push(makeValue()); ]⟩ φ }
    ~*> dl![m]{ { pv := 0 } { se2 := 0 } { se2 := select(storage, seed) } { pv := se2 }
          { storage := save(save(storage, values[values.length], pv), values.length, values.length + 1) } φ } :=
  calc dl![m]{ ⟨[ values.push(makeValue()); ]⟩ φ }
    _ = dl![m]{ ⟨[ uint pv = makeValue(); values.push(pv); ]⟩ φ } := rfl
    _ ~*> dl![m]{ { pv := 0 } { se2 := 0 } { se2 := select(storage, seed) } { pv := se2 } ⟨[ values.push(pv); ]⟩ φ } := by sol_chain
    _ ~[storagePushValueSave]~>
        dl![m]{ { pv := 0 } { se2 := 0 } { se2 := select(storage, seed) } { pv := se2 }
          { storage := save(save(storage, values[values.length], pv), values.length, values.length + 1) } ⟨[ ]⟩ φ } := rfl
    _ ~[emptyModality]~>
        dl![m]{ { pv := 0 } { se2 := 0 } { se2 := select(storage, seed) } { pv := se2 }
          { storage := save(save(storage, values[values.length], pv), values.length, values.length + 1) } φ } := rfl
end PushCall

namespace PushStorageSource
def names : FreshTable := [("bobAcc", "sp1")]
local instance : FreshNames := .ofTable names
#guard (FreshNames.clashes Pushes names).isEmpty
/-- `Token storage tokRef = bob.account.token; tokens.push(tokRef);`: the element appended is the value found at the alias path.  The nested initialiser is aliased one member at a time (`bobAcc`). -/
def chain :
    dl![m]{ ⟨[ Token storage tokRef = bob.account.token; tokens.push(tokRef); ]⟩ φ }
    ~~> dl![m]{ { bobAcc := bob.account ‖ tokRef := bob.account.token ‖
          storage := save(save(storage, tokens[tokens.length], find(storage, bob.account.token)),
            tokens.length, tokens.length + 1) } φ } :=
  calc dl![m]{ ⟨[ Token storage tokRef = bob.account.token; tokens.push(tokRef); ]⟩ φ }
    _ ~*> dl![m]{ { bobAcc := bob.account } { tokRef := bobAcc.token } ⟨[ tokens.push(tokRef); ]⟩ φ } := by sol_chain
    _ ~[sequentialToParallel]~>
        dl![m]{ { bobAcc := bob.account ‖ tokRef := bob.account.token } ⟨[ tokens.push(tokRef); ]⟩ φ } := by rfl
    _ ~[storagePushValueCopySource]~>
        dl![m]{ { bobAcc := bob.account ‖ tokRef := bob.account.token }
          { storage := save(save(storage, tokens[tokens.length], find(storage, tokRef)),
            tokens.length, tokens.length + 1) } ⟨[ ]⟩ φ } := rfl
    _ ~[emptyModality]~>
        dl![m]{ { bobAcc := bob.account ‖ tokRef := bob.account.token }
          { storage := save(save(storage, tokens[tokens.length], find(storage, tokRef)),
            tokens.length, tokens.length + 1) } φ } := rfl
    _ ~[sequentialToParallel]~>
        dl![m]{ { bobAcc := bob.account ‖ tokRef := bob.account.token ‖
          storage := save(save(storage, tokens[tokens.length], find(storage, bob.account.token)),
            tokens.length, tokens.length + 1) } φ } := by rfl
end PushStorageSource

namespace PushNonsimple
def names : FreshTable := [("sp", "sp1")]
local instance : FreshNames := .ofTable names
#guard (FreshNames.clashes Pushes names).isEmpty
/-- `bucket.tokens.push(tok);`: a nonsimple array path is first shortened to a storage alias `sp`. -/
def chain :
    dl![m]{ ⟨[ bucket.tokens.push(tok); ]⟩ φ }
    ~~> dl![m]{ { sp := bucket.tokens ‖
          storage := save(save(storage, bucket.tokens[bucket.tokens.length], find(storage, tok)),
            bucket.tokens.length, bucket.tokens.length + 1) } φ } :=
  calc dl![m]{ ⟨[ bucket.tokens.push(tok); ]⟩ φ }
    _ ~[storagePushValue_unfold_leftFstReceiver]~>
        dl![m]{ ⟨[ Token[] storage sp = bucket.tokens; sp.push(tok); ]⟩ φ } := by sol_chain
    _ ~*> dl![m]{ { sp := bucket.tokens } ⟨[ sp.push(tok); ]⟩ φ } := by sol_chain
    _ ~[storagePushValueCopySource]~>
        dl![m]{ { sp := bucket.tokens }
          { storage := save(save(storage, sp[sp.length], find(storage, tok)), sp.length, sp.length + 1) } ⟨[ ]⟩ φ } := rfl
    _ ~[emptyModality]~>
        dl![m]{ { sp := bucket.tokens }
          { storage := save(save(storage, sp[sp.length], find(storage, tok)), sp.length, sp.length + 1) } φ } := rfl
    _ ~[sequentialToParallel]~>
        dl![m]{ { sp := bucket.tokens ‖
          storage := save(save(storage, bucket.tokens[bucket.tokens.length], find(storage, tok)),
            bucket.tokens.length, bucket.tokens.length + 1) } φ } := by rfl
end PushNonsimple

namespace EmptyPush
/-- `tokens.push();`: a bare push on a reference-element array only bumps the length. -/
def bare :
    dl![m]{ ⟨[ tokens.push(); ]⟩ φ }
    ~*> dl![m]{ { storage := save(storage, tokens.length, tokens.length + 1) } φ } :=
  calc dl![m]{ ⟨[ tokens.push(); ]⟩ φ }
    _ ~[storagePushLengthSaveReferenceElement]~>
        dl![m]{ { storage := save(storage, tokens.length, tokens.length + 1) } ⟨[ ]⟩ φ } := rfl
    _ ~[emptyModality]~> dl![m]{ { storage := save(storage, tokens.length, tokens.length + 1) } φ } := rfl

/-- `uint i = tokens.push().value;`, as `Token storage sp = tokens.push(); uint i = sp.value;`: the old-length slot bound by `storageLocalRootPushBind`, then read.  Stops at the stack: the printed line resolves `i` as `find` over the pushed storage. -/
def bound :
    dl![m]{ ⟨[ Token storage sp = tokens.push(); uint i = sp.value; ]⟩ φ }
    ~*> dl![m]{ { storage := save(storage, tokens.length, tokens.length + 1) ‖ sp := tokens[tokens.length] }
          { i := find(storage, sp.value) } φ } :=
  calc dl![m]{ ⟨[ Token storage sp = tokens.push(); uint i = sp.value; ]⟩ φ }
    _ ~[storageLocalDeclInitDrop]~> dl![m]{ ⟨[ sp = tokens.push(); uint i = sp.value; ]⟩ φ } := rfl
    _ ~[storageLocalRootPushBind]~>
        dl![m]{ { storage := save(storage, tokens.length, tokens.length + 1) ‖ sp := tokens[tokens.length] }
          ⟨[ uint i = sp.value; ]⟩ φ } := rfl
    _ ~*> dl![m]{ { storage := save(storage, tokens.length, tokens.length + 1) ‖ sp := tokens[tokens.length] }
          { i := find(storage, sp.value) } φ } := by sol_chain

/-- `values.push() = makeValue();`: a push used as a target is the push of its right-hand side (the first step, an equality), then as for `values.push(makeValue())`; the element is written before the length. -/
def lvalue :
    dl![m]{ ⟨[ values.push() = makeValue(); ]⟩ φ }
    ~*> dl![m]{ { se1 := 0 } { se2 := 0 } { se2 := select(storage, seed) } { se1 := se2 }
          { storage := save(save(storage, values[values.length], se1), values.length, values.length + 1) } φ } :=
  calc dl![m]{ ⟨[ values.push() = makeValue(); ]⟩ φ }
    _ = dl![m]{ ⟨[ uint se1 = makeValue(); values.push(se1); ]⟩ φ } := rfl
    _ ~*> dl![m]{ { se1 := 0 } { se2 := 0 } { se2 := select(storage, seed) } { se1 := se2 }
          { storage := save(save(storage, values[values.length], se1), values.length, values.length + 1) } φ } := by sol_chain
end EmptyPush

namespace PushLvalue
local instance : FreshNames := .ofTable PushStorageSource.names
/-- `Token storage tokRef = bob.account.token; tokens.push() = tokRef;`: the push lvalue normalises to `tokens.push(tokRef)`, which copies the value the alias finds.  The element is written before the length, the printed order reversed. -/
def refSource :
    dl![m]{ ⟨[ Token storage tokRef = bob.account.token; tokens.push() = tokRef; ]⟩ φ }
    ~~> dl![m]{ { bobAcc := bob.account ‖ tokRef := bob.account.token ‖
          storage := save(save(storage, tokens[tokens.length], find(storage, bob.account.token)),
            tokens.length, tokens.length + 1) } φ } :=
  calc dl![m]{ ⟨[ Token storage tokRef = bob.account.token; tokens.push() = tokRef; ]⟩ φ }
    _ = dl![m]{ ⟨[ Token storage tokRef = bob.account.token; tokens.push(tokRef); ]⟩ φ } := rfl
    _ ~~> dl![m]{ { bobAcc := bob.account ‖ tokRef := bob.account.token ‖
          storage := save(save(storage, tokens[tokens.length], find(storage, bob.account.token)),
            tokens.length, tokens.length + 1) } φ } := PushStorageSource.chain m φ

/-- `tokens.push().value = 11;`, from its first step `uint pv = 11; Token storage sp = tokens.push(); sp.value = pv;` (the member of a call is refused): the slot bound, then written. -/
def field :
    dl![m]{ ⟨[ uint pv = 11; Token storage sp = tokens.push(); sp.value = pv; ]⟩ φ }
    ~*> dl![m]{ { pv := 11 }
          { storage := save(storage, tokens.length, tokens.length + 1) ‖ sp := tokens[tokens.length] }
          { storage := save(storage, sp.value, pv) } φ } :=
  calc dl![m]{ ⟨[ uint pv = 11; Token storage sp = tokens.push(); sp.value = pv; ]⟩ φ }
    _ ~*> dl![m]{ { pv := 11 }
          { storage := save(storage, tokens.length, tokens.length + 1) ‖ sp := tokens[tokens.length] }
          ⟨[ sp.value = pv; ]⟩ φ } := by sol_chain
    _ ~[storageFieldWriteSave]~>
        dl![m]{ { pv := 11 }
          { storage := save(storage, tokens.length, tokens.length + 1) ‖ sp := tokens[tokens.length] }
          { storage := save(storage, sp.value, pv) } ⟨[ ]⟩ φ } := rfl
    _ ~[emptyModality]~>
        dl![m]{ { pv := 11 }
          { storage := save(storage, tokens.length, tokens.length + 1) ‖ sp := tokens[tokens.length] }
          { storage := save(storage, sp.value, pv) } φ } := rfl
end PushLvalue

namespace BucketPush
def names : FreshTable := [("sp", "sp1")]
local instance : FreshNames := .ofTable names
#guard (FreshNames.clashes Pushes names).isEmpty
/-- `bucket.tokens.push();`: the receiver is aliased (`sp`), then the bare push. -/
def bare :
    dl![m]{ ⟨[ bucket.tokens.push(); ]⟩ φ }
    ~~> dl![m]{ { sp := bucket.tokens ‖
          storage := save(storage, bucket.tokens.length, bucket.tokens.length + 1) } φ } :=
  calc dl![m]{ ⟨[ bucket.tokens.push(); ]⟩ φ }
    _ ~[storagePush_unfold_leftFstReceiver]~>
        dl![m]{ ⟨[ Token[] storage sp = bucket.tokens; sp.push(); ]⟩ φ } := by sol_chain
    _ ~*> dl![m]{ { sp := bucket.tokens } ⟨[ sp.push(); ]⟩ φ } := by sol_chain
    _ ~[storagePushLengthSaveReferenceElement]~>
        dl![m]{ { sp := bucket.tokens } { storage := save(storage, sp.length, sp.length + 1) } ⟨[ ]⟩ φ } := rfl
    _ ~[emptyModality]~>
        dl![m]{ { sp := bucket.tokens } { storage := save(storage, sp.length, sp.length + 1) } φ } := rfl
    _ ~[sequentialToParallel]~>
        dl![m]{ { sp := bucket.tokens ‖
          storage := save(storage, bucket.tokens.length, bucket.tokens.length + 1) } φ } := by rfl
end BucketPush

namespace BucketPushRef
def names : FreshTable := [("bobAcc", "sp1"), ("sp", "sp2")]
local instance : FreshNames := .ofTable names
#guard (FreshNames.clashes Pushes names).isEmpty
set_option maxHeartbeats 300000 in
/-- `Token storage tokRef = bob.account.token; bucket.tokens.push() = tokRef;`: the source is snapshotted, the receiver aliased (`sp`); the final storage update uses the original path, not the temporary alias. -/
def chain :
    dl![m]{ ⟨[ Token storage tokRef = bob.account.token; bucket.tokens.push() = tokRef; ]⟩ φ }
    ~~> dl![m]{ { bobAcc := bob.account ‖ tokRef := bob.account.token ‖ sp := bucket.tokens ‖
          storage := save(save(storage, bucket.tokens[bucket.tokens.length], find(storage, bob.account.token)),
            bucket.tokens.length, bucket.tokens.length + 1) } φ } :=
  calc dl![m]{ ⟨[ Token storage tokRef = bob.account.token; bucket.tokens.push() = tokRef; ]⟩ φ }
    _ = dl![m]{ ⟨[ Token storage tokRef = bob.account.token; bucket.tokens.push(tokRef); ]⟩ φ } := rfl
    _ ~*> dl![m]{ { bobAcc := bob.account } { tokRef := bobAcc.token } { sp := bucket.tokens }
          ⟨[ sp.push(tokRef); ]⟩ φ } := by sol_chain
    _ ~[sequentialToParallel]~>
        dl![m]{ { bobAcc := bob.account ‖ tokRef := bob.account.token } { sp := bucket.tokens }
          ⟨[ sp.push(tokRef); ]⟩ φ } := by rfl
    _ ~[sequentialToParallel]~>
        dl![m]{ { bobAcc := bob.account ‖ tokRef := bob.account.token ‖ sp := bucket.tokens }
          ⟨[ sp.push(tokRef); ]⟩ φ } := by rfl
    _ ~[storagePushValueCopySource]~>
        dl![m]{ { bobAcc := bob.account ‖ tokRef := bob.account.token ‖ sp := bucket.tokens }
          { storage := save(save(storage, sp[sp.length], find(storage, tokRef)), sp.length, sp.length + 1) } ⟨[ ]⟩ φ } := rfl
    _ ~[emptyModality]~>
        dl![m]{ { bobAcc := bob.account ‖ tokRef := bob.account.token ‖ sp := bucket.tokens }
          { storage := save(save(storage, sp[sp.length], find(storage, tokRef)), sp.length, sp.length + 1) } φ } := rfl
    _ ~[sequentialToParallel]~>
        dl![m]{ { bobAcc := bob.account ‖ tokRef := bob.account.token ‖ sp := bucket.tokens ‖
          storage := save(save(storage, bucket.tokens[bucket.tokens.length], find(storage, bob.account.token)),
            bucket.tokens.length, bucket.tokens.length + 1) } φ } := by rfl

/-- `bucket.tokens.push().value = valueVal;`, from its first step (the member of a call is refused): `pv` snapshotted, the receiver aliased (`sp1`), the slot bound (`tokSlot`) and written.  The printed line with `Token[] storage sp1 = bucket.tokens; tokSlot = sp1.push();` is left `_`, as `dl!{ … }` cannot read an alias assigned from a push. -/
def field :
    dl![m]{ ⟨[ uint pv = valueVal; Token storage tokSlot = bucket.tokens.push(); tokSlot.value = pv; ]⟩ φ }
    ~*> dl![m]{ { pv := valueVal } { sp1 := bucket.tokens }
          { storage := save(storage, sp1.length, sp1.length + 1) ‖ tokSlot := sp1[sp1.length] }
          { storage := save(storage, tokSlot.value, pv) } φ } :=
  calc dl![m]{ ⟨[ uint pv = valueVal; Token storage tokSlot = bucket.tokens.push(); tokSlot.value = pv; ]⟩ φ }
    _ ~*> dl![m]{ { pv := valueVal } ⟨[ tokSlot = bucket.tokens.push(); tokSlot.value = pv; ]⟩ φ } := by sol_chain
    _ ~[storageLocalRootPush_unfold_leftFstReceiver]~> _ := by sol_chain
    _ ~*> dl![m]{ { pv := valueVal } { sp1 := bucket.tokens }
          { storage := save(storage, sp1.length, sp1.length + 1) ‖ tokSlot := sp1[sp1.length] }
          { storage := save(storage, tokSlot.value, pv) } φ } := by sol_chain
end BucketPushRef

end
end Solidity.Examples.Chains.StorageArrays
