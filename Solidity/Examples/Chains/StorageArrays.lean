import Solidity.Calculus.Chains
import Solidity.Calculus.ChainRewrites
import Solidity.Calculus.LastLine
import Solidity.Calculus.Close
import Solidity.FreshNames

/-!
# The additional storage array cases as chains

The calculus's push examples, each one chain term over any modality `m` and postcondition `φ`
(`Examples/Chains/Storage.lean` says how to read one).  Everything runs in `Pushes`: `values`, `tokens`,
`bucket.tokens`, `bob`, a `Token` state variable `tok`, and `makeValue()`, which reads `seed`.
Stand-ins: `bucket.tokens` for `alice.account.tokens`, `tok` (copied as `find(storage, tok)`) for a token
value, `Token storage sp = tokens.push(); … sp.value` for `tokens.push().value`, a member of a call, which is
refused; such a chain starts at the paper's second line.  So does one whose first `⇝` is a capture the
elaborator makes (`values.push(makeValue())` is `uint pv = makeValue(); values.push(pv);` once elaborated).
A call is inlined, so `makeValue()` leaves its callee's local `se2` where the printed line has the call
itself.

The strategy's runs are grouped as the paper prints them; past the merge every read is resolved one law a
link, every capture kept, which `#last_line` checks.  The first line's update gives `seed` 7, `valueVal` 42
and the token copied a `value` of 10.  The pushed `makeValue()` ends at `7`; a struct read
(`find(…, bob.account.token)`, `find(…, tok)`) has no literal, and a starting length has no spelling
(`Examples/Chains/Storage.lean`), so the lengths stay symbolic.  A push's alias
`{ storage := … ‖ sp := p[p.length] }` merges with the update after it (`Upd.mergeStL`), the alias standing
for the pre-state slot.
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
/-- `values.push(makeValue());` with `seed` 7: the argument captured (`pv`, the elaborator's), the call
inlined and run (its local `se2` is the printed `makeValue()`), then the value pushed, the paper's one `⇝*`;
the merge, and the read of `seed` resolved (`findOnSave`).  The length is `values.length`. -/
theorem chain :
    dl![m]{ { storage := store(storage, seed, 7) } ⟨[ values.push(makeValue()); ]⟩ φ }
    ~*> dl![m]{
        { storage := store(storage, seed, 7) }
          { pv := 0 } { se2 := 0 } { se2 := select(storage, seed) } { pv := se2 }
          { storage := save(save(storage, values[values.length], pv), values.length, values.length + 1) } φ }
    ~[sequentialToParallel]~> dl![m]{
        { pv := 0 ‖ se2 := 0 ‖ se2 := select(store(storage, seed, 7), seed) ‖ pv := select(store(storage, seed, 7), seed) ‖
            storage :=
              save(save(store(storage, seed, 7), values[values.length], select(store(storage, seed, 7), seed)), values.length,
                values.length + 1) }
          φ }
    ~[findOnSave]~> dl![m]{
        { pv := 0 ‖ se2 := 0 ‖ se2 := 7 ‖ pv := 7 ‖
            storage := save(save(store(storage, seed, 7), values[values.length], 7), values.length, values.length + 1) }
          φ } := by
  sol_chain
#last_line chain
end PushCall

namespace PushStorageSource
def names : FreshTable := [("bobAcc", "sp1")]
local instance : FreshNames := .ofTable names
#guard (FreshNames.clashes Pushes names).isEmpty
/-- `Token storage tokRef = bob.account.token; tokens.push(tokRef);` from a storage where
`bob.account.token.value` is 10: the element appended is the value found at the alias path.  The paper's one
`⇝*`: the nested initialiser aliased one member at a time (`bobAcc`, then `tokRef` through it), then the
push; the merge binds `tokRef` to `bob.account.token`, as printed.  A struct read has no literal: no law reads
`bob.account.token` through the write below it. -/
theorem chain :
    dl![m]{ { storage := save(storage, bob.account.token.value, 10) }
        ⟨[ Token storage tokRef = bob.account.token; tokens.push(tokRef); ]⟩ φ }
    ~*> dl![m]{
        { storage := save(storage, bob.account.token.value, 10) }
          { bobAcc := bob.account } { tokRef := bobAcc.token }
          { storage := save(save(storage, tokens[tokens.length], find(storage, tokRef)), tokens.length, tokens.length + 1) }
          φ }
    ~[sequentialToParallel]~> dl![m]{
        { bobAcc := bob.account ‖ tokRef := bob.account.token ‖
            storage :=
              save(save(save(storage, bob.account.token.value, 10), tokens[tokens.length],
                  find(save(storage, bob.account.token.value, 10), bob.account.token)),
                tokens.length, tokens.length + 1) }
          φ } := by
  sol_chain
#last_line chain
end PushStorageSource

namespace PushNonsimple
def names : FreshTable := [("sp", "sp1")]
local instance : FreshNames := .ofTable names
#guard (FreshNames.clashes Pushes names).isEmpty
/-- `bucket.tokens.push(tok);` from a storage where `tok.value` is 10: a nonsimple array path is first
shortened to a storage alias `sp` (the paper's `⇝`), then the paper's `⇝*` binds it and pushes; the merge
puts the push on the original path.  A struct read has no literal: no law reads `tok` through the write
below it. -/
theorem chain :
    dl![m]{ { storage := save(storage, tok.value, 10) } ⟨[ bucket.tokens.push(tok); ]⟩ φ }
    ~[storagePushValue_unfold_leftFstReceiver]~> dl![m]{ { storage := save(storage, tok.value, 10) }
        ⟨[ Token[] storage sp = bucket.tokens; sp.push(tok); ]⟩ φ }
    ~*> dl![m]{
        { storage := save(storage, tok.value, 10) }
          { sp := bucket.tokens }
          { storage := save(save(storage, sp[sp.length], find(storage, tok)), sp.length, sp.length + 1) } φ }
    ~[sequentialToParallel]~> dl![m]{
        { sp := bucket.tokens ‖
            storage :=
              save(save(save(storage, tok.value, 10), bucket.tokens[bucket.tokens.length],
                  find(save(storage, tok.value, 10), tok)),
                bucket.tokens.length, bucket.tokens.length + 1) }
          φ } := by
  sol_chain
#last_line chain
end PushNonsimple

namespace EmptyPush
/-- `tokens.push();`: a bare push on a reference-element array only bumps the length, the paper's one `⇝`
(the rule and the empty program after it). -/
def bare :
    dl![m]{ ⟨[ tokens.push(); ]⟩ φ }
    ~*> dl![m]{ { storage := save(storage, tokens.length, tokens.length + 1) } φ } := by
  sol_chain
#last_line bare

/-- `uint i = tokens.push().value;`, from its first step `Token storage sp = tokens.push(); uint i = sp.value;`:
the paper's one `⇝*`, the old-length slot bound by `storageLocalRootPushBind` and read; the read merges under
the push, the alias standing for the pre-state slot, and stays a read of that slot (recycled, whatever it
holds), as printed: no law reads a slot through a push's length write. -/
theorem bound :
    dl![m]{ ⟨[ Token storage sp = tokens.push(); uint i = sp.value; ]⟩ φ }
    ~*> dl![m]{
        { storage := save(storage, tokens.length, tokens.length + 1) ‖ sp := tokens[tokens.length] }
          { i := find(storage, sp.value) } φ }
    ~[sequentialToParallel]~> dl![m]{
        { storage := save(storage, tokens.length, tokens.length + 1) ‖ sp := tokens[tokens.length] ‖
            i := find(save(storage, tokens.length, tokens.length + 1), tokens[tokens.length].value) }
          φ } := by
  sol_chain
#last_line bound

section
/-- `pv`, the right-hand side snapshotted. -/
local instance : FreshNames := .ofTable [("pv", "se1")]
#guard (FreshNames.clashes Pushes [("pv", "se1")]).isEmpty
/-- `values.push() = makeValue();` with `seed` 7: a push used as a target is the push of its right-hand side
(the paper's `⇝`, the elaborator's), then as for `values.push(makeValue())`, whose chain this is: the program
is the same once elaborated.  The element is written before the length. -/
theorem lvalue :
    dl![m]{ { storage := store(storage, seed, 7) } ⟨[ values.push() = makeValue(); ]⟩ φ }
    ~*> dl![m]{
        { storage := store(storage, seed, 7) }
          { pv := 0 } { se2 := 0 } { se2 := select(storage, seed) } { pv := se2 }
          { storage := save(save(storage, values[values.length], pv), values.length, values.length + 1) } φ }
    ~[sequentialToParallel]~> dl![m]{
        { pv := 0 ‖ se2 := 0 ‖ se2 := select(store(storage, seed, 7), seed) ‖ pv := select(store(storage, seed, 7), seed) ‖
            storage :=
              save(save(store(storage, seed, 7), values[values.length], select(store(storage, seed, 7), seed)), values.length,
                values.length + 1) }
          φ }
    ~[findOnSave]~> dl![m]{
        { pv := 0 ‖ se2 := 0 ‖ se2 := 7 ‖ pv := 7 ‖
            storage := save(save(store(storage, seed, 7), values[values.length], 7), values.length, values.length + 1) }
          φ } :=
  PushCall.chain m φ
#last_line lvalue
end
end EmptyPush

namespace PushLvalue
local instance : FreshNames := .ofTable PushStorageSource.names
/-- `Token storage tokRef = bob.account.token; tokens.push() = tokRef;` from a storage where
`bob.account.token.value` is 10: the push lvalue normalises to `tokens.push(tokRef)` (the elaborator's), which
copies the value the alias finds, so the chain is `PushStorageSource`'s.  The element is written before the
length, the printed order reversed. -/
theorem refSource :
    dl![m]{ { storage := save(storage, bob.account.token.value, 10) }
        ⟨[ Token storage tokRef = bob.account.token; tokens.push() = tokRef; ]⟩ φ }
    ~*> dl![m]{
        { storage := save(storage, bob.account.token.value, 10) }
          { bobAcc := bob.account } { tokRef := bobAcc.token }
          { storage := save(save(storage, tokens[tokens.length], find(storage, tokRef)), tokens.length, tokens.length + 1) }
          φ }
    ~[sequentialToParallel]~> dl![m]{
        { bobAcc := bob.account ‖ tokRef := bob.account.token ‖
            storage :=
              save(save(save(storage, bob.account.token.value, 10), tokens[tokens.length],
                  find(save(storage, bob.account.token.value, 10), bob.account.token)),
                tokens.length, tokens.length + 1) }
          φ } :=
  PushStorageSource.chain m φ
#last_line refSource

/-- `tokens.push().value = 11;`, from its first step `uint pv = 11; Token storage sp = tokens.push(); sp.value = pv;`
(the member of a call is refused): the paper's one `⇝*`, the slot bound and written, then the three updates
merged. -/
theorem field :
    dl![m]{ ⟨[ uint pv = 11; Token storage sp = tokens.push(); sp.value = pv; ]⟩ φ }
    ~*> dl![m]{
        { pv := 11 }
          { storage := save(storage, tokens.length, tokens.length + 1) ‖ sp := tokens[tokens.length] }
          { storage := save(storage, sp.value, pv) } φ }
    ~[sequentialToParallel]~> dl![m]{
        { pv := 11 ‖ sp := tokens[tokens.length] ‖
            storage := save(save(storage, tokens.length, tokens.length + 1), tokens[tokens.length].value, 11) }
          φ } := by
  sol_chain
#last_line field
end PushLvalue

namespace BucketPush
def names : FreshTable := [("sp", "sp1")]
local instance : FreshNames := .ofTable names
#guard (FreshNames.clashes Pushes names).isEmpty
/-- `bucket.tokens.push();`: the receiver aliased (`sp`, the paper's `⇝`), then the paper's `⇝*`, the alias
bound and the bare push; the merge puts the push on the original path. -/
theorem bare :
    dl![m]{ ⟨[ bucket.tokens.push(); ]⟩ φ }
    ~[storagePush_unfold_leftFstReceiver]~> dl![m]{ ⟨[ Token[] storage sp = bucket.tokens; sp.push(); ]⟩ φ }
    ~*> dl![m]{ { sp := bucket.tokens } { storage := save(storage, sp.length, sp.length + 1) } φ }
    ~[sequentialToParallel]~>
      dl![m]{ { sp := bucket.tokens ‖ storage := save(storage, bucket.tokens.length, bucket.tokens.length + 1) } φ } := by
  sol_chain
#last_line bare
end BucketPush

namespace BucketPushRef
def names : FreshTable := [("bobAcc", "sp1"), ("sp", "sp2")]
local instance : FreshNames := .ofTable names
#guard (FreshNames.clashes Pushes names).isEmpty
/-- `Token storage tokRef = bob.account.token; bucket.tokens.push() = tokRef;` from a storage where
`bob.account.token.value` is 10: the paper's one `⇝*`, the source aliased one member at a time (`bobAcc`, then
`tokRef` through it), the push normalised to `bucket.tokens.push(tokRef)` (the elaborator's), the receiver
aliased (`sp`) and the push; the merge binds `tokRef` to `bob.account.token` and puts the push on the
original path, not the temporary alias.  A struct read has no literal. -/
theorem chain :
    dl![m]{ { storage := save(storage, bob.account.token.value, 10) }
        ⟨[ Token storage tokRef = bob.account.token; bucket.tokens.push() = tokRef; ]⟩ φ }
    ~*> dl![m]{
        { storage := save(storage, bob.account.token.value, 10) }
          { bobAcc := bob.account } { tokRef := bobAcc.token } { sp := bucket.tokens }
          { storage := save(save(storage, sp[sp.length], find(storage, tokRef)), sp.length, sp.length + 1) } φ }
    ~[sequentialToParallel]~> dl![m]{
        { bobAcc := bob.account ‖ tokRef := bob.account.token ‖ sp := bucket.tokens ‖
            storage :=
              save(save(save(storage, bob.account.token.value, 10), bucket.tokens[bucket.tokens.length],
                  find(save(storage, bob.account.token.value, 10), bob.account.token)),
                bucket.tokens.length, bucket.tokens.length + 1) }
          φ } := by
  sol_chain
#last_line chain
end BucketPushRef

namespace BucketPushField
/-- `bucket.tokens.push().value = valueVal;` with `valueVal` 42, from its first step `uint pv = valueVal;
Token storage sp = bucket.tokens.push(); sp.value = pv;` (the member of a call is refused): the paper's first
`⇝*`, `pv` snapshotted and the receiver aliased (`sp1`); its second, the slot bound through `sp1` (`sp`) and
written; then the merge, which binds `sp` to `bucket.tokens[bucket.tokens.length]` and puts the write on the
original path. -/
theorem field :
    dl![m]{ { valueVal := 42 } ⟨[ uint pv = valueVal; Token storage sp = bucket.tokens.push(); sp.value = pv; ]⟩ φ }
    ~*> dl![m]{ { valueVal := 42 } { pv := valueVal }
        ⟨[ Token[] storage sp1 = bucket.tokens; sp = sp1.push(); sp.value = pv; ]⟩ φ }
    ~*> dl![m]{
        { valueVal := 42 }
          { pv := valueVal }
          { sp1 := bucket.tokens }
          { storage := save(storage, sp1.length, sp1.length + 1) ‖ sp := sp1[sp1.length] }
          { storage := save(storage, sp.value, pv) } φ }
    ~[sequentialToParallel]~> dl![m]{
        { valueVal := 42 ‖ pv := 42 ‖ sp1 := bucket.tokens ‖ sp := bucket.tokens[bucket.tokens.length] ‖
            storage :=
              save(save(storage, bucket.tokens.length, bucket.tokens.length + 1), bucket.tokens[bucket.tokens.length].value,
                42) }
          φ } := by
  sol_chain
#last_line field
end BucketPushField

end
end Solidity.Examples.Chains.StorageArrays
