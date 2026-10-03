import Solidity.Calculus.Chains
import Solidity.Calculus.ChainRewrites
import Solidity.Calculus.LastLine
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
call itself.  A line of the strategy that binds an alias through another alias (`{ tokRef := bobAcc.token }`),
or a callee's local (`{ pv := se2 }`), is crossed unwritten, the next written line being its merge, which
binds the alias to its path as the printed line does.  A push's alias `{ storage := … ‖ sp := p[p.length] }`
merges with the update after it (`Upd.mergeStL`), the alias standing for the pre-state slot.  Every chain
ends at one parallel update, its dead captures dropped last (`~[simplifyUpdate]~>`), checked by `#last_line`.
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
/-- `values.push(makeValue());`: the argument is captured (`pv`), the call inlined and run (its local `se2` is the printed `makeValue()`), then the value pushed; the length is `values.length`.  The merge resolves the pushed value to `select(storage, seed)`, and the dead captures go. -/
theorem chain :
    dl![m]{ ⟨[ values.push(makeValue()); ]⟩ φ }
    ~~> dl![m]{ { se2 := select(storage, seed) ‖ pv := select(storage, seed) ‖
          storage := save(save(storage, values[values.length], select(storage, seed)), values.length, values.length + 1) } φ } :=
  calc dl![m]{ ⟨[ values.push(makeValue()); ]⟩ φ }
    _ = dl![m]{ ⟨[ uint pv = makeValue(); values.push(pv); ]⟩ φ } := rfl
    _ ~*> _ := by sol_chain
    _ ~[sequentialToParallel]~>
        dl![m]{ { pv := 0 ‖ se2 := 0 ‖ se2 := select(storage, seed) ‖ pv := select(storage, seed) ‖
          storage := save(save(storage, values[values.length], select(storage, seed)), values.length, values.length + 1) } φ } := by sol_chain
    _ ~[simplifyUpdate]~>
        dl![m]{ { se2 := select(storage, seed) ‖ pv := select(storage, seed) ‖
          storage := save(save(storage, values[values.length], select(storage, seed)), values.length, values.length + 1) } φ } := by sol_chain
#last_line chain
end PushCall

namespace PushStorageSource
def names : FreshTable := [("bobAcc", "sp1")]
local instance : FreshNames := .ofTable names
#guard (FreshNames.clashes Pushes names).isEmpty
/-- `Token storage tokRef = bob.account.token; tokens.push(tokRef);`: the element appended is the value found at the alias path.  The nested initialiser is aliased one member at a time (`bobAcc`, then `tokRef` through it), lines crossed unwritten; the merge binds `tokRef` to `bob.account.token`, as printed, and the pushed value to `find(storage, bob.account.token)`; the dead `bobAcc` goes last. -/
theorem chain :
    dl![m]{ ⟨[ Token storage tokRef = bob.account.token; tokens.push(tokRef); ]⟩ φ }
    ~~> dl![m]{ { tokRef := bob.account.token ‖
          storage := save(save(storage, tokens[tokens.length], find(storage, bob.account.token)),
            tokens.length, tokens.length + 1) } φ } :=
  calc dl![m]{ ⟨[ Token storage tokRef = bob.account.token; tokens.push(tokRef); ]⟩ φ }
    _ ~*> _ := by sol_chain
    _ ~[sequentialToParallel]~>
        dl![m]{ { bobAcc := bob.account ‖ tokRef := bob.account.token ‖
          storage := save(save(storage, tokens[tokens.length], find(storage, bob.account.token)),
            tokens.length, tokens.length + 1) } φ } := by sol_chain
    _ ~[simplifyUpdate]~>
        dl![m]{ { tokRef := bob.account.token ‖
          storage := save(save(storage, tokens[tokens.length], find(storage, bob.account.token)),
            tokens.length, tokens.length + 1) } φ } := by sol_chain
#last_line chain
end PushStorageSource

namespace PushNonsimple
def names : FreshTable := [("sp", "sp1")]
local instance : FreshNames := .ofTable names
#guard (FreshNames.clashes Pushes names).isEmpty
/-- `bucket.tokens.push(tok);`: a nonsimple array path is first shortened to a storage alias `sp`, dead once the push is on its path. -/
theorem chain :
    dl![m]{ ⟨[ bucket.tokens.push(tok); ]⟩ φ }
    ~~> dl![m]{ { storage := save(save(storage, bucket.tokens[bucket.tokens.length], find(storage, tok)),
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
    _ ~[simplifyUpdate]~>
        dl![m]{ { storage := save(save(storage, bucket.tokens[bucket.tokens.length], find(storage, tok)),
            bucket.tokens.length, bucket.tokens.length + 1) } φ } := by sol_chain
#last_line chain
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
#last_line bare

/-- `uint i = tokens.push().value;`, as `Token storage sp = tokens.push(); uint i = sp.value;`: the old-length slot bound by `storageLocalRootPushBind`, then read; the read merges under the push, the alias standing for the pre-state slot, and stays a read of that slot (recycled, whatever it holds). -/
theorem bound :
    dl![m]{ ⟨[ Token storage sp = tokens.push(); uint i = sp.value; ]⟩ φ }
    ~~> dl![m]{ { storage := save(storage, tokens.length, tokens.length + 1) ‖ sp := tokens[tokens.length] ‖
          i := find(save(storage, tokens.length, tokens.length + 1), tokens[tokens.length].value) } φ } :=
  calc dl![m]{ ⟨[ Token storage sp = tokens.push(); uint i = sp.value; ]⟩ φ }
    _ ~[storageLocalDeclInitDrop]~> dl![m]{ ⟨[ sp = tokens.push(); uint i = sp.value; ]⟩ φ } := rfl
    _ ~[storageLocalRootPushBind]~>
        dl![m]{ { storage := save(storage, tokens.length, tokens.length + 1) ‖ sp := tokens[tokens.length] }
          ⟨[ uint i = sp.value; ]⟩ φ } := rfl
    _ ~*> dl![m]{ { storage := save(storage, tokens.length, tokens.length + 1) ‖ sp := tokens[tokens.length] }
          { i := find(storage, sp.value) } φ } := by sol_chain
    _ ~[sequentialToParallel]~>
        dl![m]{ { storage := save(storage, tokens.length, tokens.length + 1) ‖ sp := tokens[tokens.length] ‖
          i := find(save(storage, tokens.length, tokens.length + 1), tokens[tokens.length].value) } φ } := by sol_chain
#last_line bound

/-- `values.push() = makeValue();`: a push used as a target is the push of its right-hand side (the first step, an equality), then as for `values.push(makeValue())`; the element is written before the length. -/
theorem lvalue :
    dl![m]{ ⟨[ values.push() = makeValue(); ]⟩ φ }
    ~~> dl![m]{ { se2 := select(storage, seed) ‖ se1 := select(storage, seed) ‖
          storage := save(save(storage, values[values.length], select(storage, seed)), values.length, values.length + 1) } φ } :=
  calc dl![m]{ ⟨[ values.push() = makeValue(); ]⟩ φ }
    _ = dl![m]{ ⟨[ uint se1 = makeValue(); values.push(se1); ]⟩ φ } := rfl
    _ ~*> _ := by sol_chain
    _ ~[sequentialToParallel]~>
        dl![m]{ { se1 := 0 ‖ se2 := 0 ‖ se2 := select(storage, seed) ‖ se1 := select(storage, seed) ‖
          storage := save(save(storage, values[values.length], select(storage, seed)), values.length, values.length + 1) } φ } := by sol_chain
    _ ~[simplifyUpdate]~>
        dl![m]{ { se2 := select(storage, seed) ‖ se1 := select(storage, seed) ‖
          storage := save(save(storage, values[values.length], select(storage, seed)), values.length, values.length + 1) } φ } := by sol_chain
#last_line lvalue
end EmptyPush

namespace PushLvalue
local instance : FreshNames := .ofTable PushStorageSource.names
/-- `Token storage tokRef = bob.account.token; tokens.push() = tokRef;`: the push lvalue normalises to `tokens.push(tokRef)`, which copies the value the alias finds.  The element is written before the length, the printed order reversed. -/
theorem refSource :
    dl![m]{ ⟨[ Token storage tokRef = bob.account.token; tokens.push() = tokRef; ]⟩ φ }
    ~~> dl![m]{ { tokRef := bob.account.token ‖
          storage := save(save(storage, tokens[tokens.length], find(storage, bob.account.token)),
            tokens.length, tokens.length + 1) } φ } :=
  calc dl![m]{ ⟨[ Token storage tokRef = bob.account.token; tokens.push() = tokRef; ]⟩ φ }
    _ = dl![m]{ ⟨[ Token storage tokRef = bob.account.token; tokens.push(tokRef); ]⟩ φ } := rfl
    _ ~~> dl![m]{ { tokRef := bob.account.token ‖
          storage := save(save(storage, tokens[tokens.length], find(storage, bob.account.token)),
            tokens.length, tokens.length + 1) } φ } := PushStorageSource.chain m φ
#last_line refSource

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
/-- `bucket.tokens.push();`: the receiver is aliased (`sp`), then the bare push; the alias goes last. -/
theorem bare :
    dl![m]{ ⟨[ bucket.tokens.push(); ]⟩ φ }
    ~~> dl![m]{ { storage := save(storage, bucket.tokens.length, bucket.tokens.length + 1) } φ } :=
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
    _ ~[simplifyUpdate]~>
        dl![m]{ { storage := save(storage, bucket.tokens.length, bucket.tokens.length + 1) } φ } := by sol_chain
#last_line bare
end BucketPush

namespace BucketPushRef
def names : FreshTable := [("bobAcc", "sp1"), ("sp", "sp2")]
local instance : FreshNames := .ofTable names
#guard (FreshNames.clashes Pushes names).isEmpty
set_option maxHeartbeats 300000 in
/-- `Token storage tokRef = bob.account.token; bucket.tokens.push() = tokRef;`: the source is snapshotted, the receiver aliased (`sp`); the final storage update uses the original path, not the temporary alias.  The strategy's lines bind `tokRef` through `bobAcc` and are crossed unwritten; the merge binds it to `bob.account.token`; the dead aliases go last. -/
theorem chain :
    dl![m]{ ⟨[ Token storage tokRef = bob.account.token; bucket.tokens.push() = tokRef; ]⟩ φ }
    ~~> dl![m]{ { tokRef := bob.account.token ‖
          storage := save(save(storage, bucket.tokens[bucket.tokens.length], find(storage, bob.account.token)),
            bucket.tokens.length, bucket.tokens.length + 1) } φ } :=
  calc dl![m]{ ⟨[ Token storage tokRef = bob.account.token; bucket.tokens.push() = tokRef; ]⟩ φ }
    _ = dl![m]{ ⟨[ Token storage tokRef = bob.account.token; bucket.tokens.push(tokRef); ]⟩ φ } := rfl
    _ ~*> _ := by sol_chain
    _ ~[sequentialToParallel]~>
        dl![m]{ { bobAcc := bob.account ‖ tokRef := bob.account.token ‖ sp := bucket.tokens ‖
          storage := save(save(storage, bucket.tokens[bucket.tokens.length], find(storage, bob.account.token)),
            bucket.tokens.length, bucket.tokens.length + 1) } φ } := by sol_chain
    _ ~[simplifyUpdate]~>
        dl![m]{ { tokRef := bob.account.token ‖
          storage := save(save(storage, bucket.tokens[bucket.tokens.length], find(storage, bob.account.token)),
            bucket.tokens.length, bucket.tokens.length + 1) } φ } := by sol_chain
#last_line chain

/-- `bucket.tokens.push().value = valueVal;`, from its first step (the member of a call is refused): `pv` snapshotted, the receiver aliased (`sp1`), the slot bound (`tokSlot`) and written.  The printed line with `Token[] storage sp1 = bucket.tokens; tokSlot = sp1.push();` is left `_`, as `dl!{ … }` cannot read an alias assigned from a push, and so are the steps to the slot bound through `sp1`; the merge binds it to `bucket.tokens[bucket.tokens.length]`.  The write does not merge over the push's parallel update (locals and the storage over another). -/
def field :
    dl![m]{ ⟨[ uint pv = valueVal; Token storage tokSlot = bucket.tokens.push(); tokSlot.value = pv; ]⟩ φ }
    ~~> dl![m]{ { pv := valueVal ‖ sp1 := bucket.tokens ‖
          storage := save(storage, bucket.tokens.length, bucket.tokens.length + 1) ‖
          tokSlot := bucket.tokens[bucket.tokens.length] }
          { storage := save(storage, tokSlot.value, pv) } φ } :=
  calc dl![m]{ ⟨[ uint pv = valueVal; Token storage tokSlot = bucket.tokens.push(); tokSlot.value = pv; ]⟩ φ }
    _ ~*> dl![m]{ { pv := valueVal } ⟨[ tokSlot = bucket.tokens.push(); tokSlot.value = pv; ]⟩ φ } := by sol_chain
    _ ~[storageLocalRootPush_unfold_leftFstReceiver]~> _ := by sol_chain
    _ ~> _ := by sol_chain
    _ ~> _ := by sol_chain
    _ ~> _ := by sol_chain
    _ ~[sequentialToParallel]~>
        dl![m]{ { pv := valueVal ‖ sp1 := bucket.tokens ‖
          storage := save(storage, bucket.tokens.length, bucket.tokens.length + 1) ‖
          tokSlot := bucket.tokens[bucket.tokens.length] }
          ⟨[ tokSlot.value = pv; ]⟩ φ } := by sol_chain
    _ ~[storageFieldWriteSave]~> _ := by sol_chain
    _ ~> dl![m]{ { pv := valueVal ‖ sp1 := bucket.tokens ‖
          storage := save(storage, bucket.tokens.length, bucket.tokens.length + 1) ‖
          tokSlot := bucket.tokens[bucket.tokens.length] }
          { storage := save(storage, tokSlot.value, pv) } φ } := by sol_chain
end BucketPushRef

end
end Solidity.Examples.Chains.StorageArrays
