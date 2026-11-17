import Solidity.Goals.IntrinsicStorage

/-! Pin and controls for the intrinsic storage accounting goal. -/

namespace Solidity.Goals

/--
info: open Solidity.Goals.intrinsicStorageAccounting ← Solidity.Semantics.IntrinsicSession.storage_accounting_correct plan is0-intrinsic-session
-/
#guard_msgs in
-- Concrete storage/frame accounting is specified; session implementation remains OPEN (H720).
#roadmap_goal intrinsicStorageAccounting

/-! Layout controls for the storage prerequisite: ideal slot terms (`Storage.Loc`,
`Pre`) of actual typed paths. None enumerates an address, key or word domain. -/
namespace IntrinsicStorageLayoutControls
open Solidity.Storage Solidity.Semantics Solidity.Semantics.IntrinsicStorage

private def ledgerKey (k : PrimTy.uint.Denote) : Path (.ref (.struct "LedgerUse")) .uint :=
  .field (f := "ledger") (T := .ref (.struct "Ledger")) (by decide)
    (.field (f := "balances") (T := .ref (.mapping .uint .uint)) (by decide) (.key k .nil))

-- The nested ledger's nonce occupies slot zero, so its mapping starts at one.
example (k : PrimTy.uint.Denote) :
    locate (ledgerKey k) (.root 0) = .hash (keyWord k) (.root 1) 0 := by rfl

private def personAge (i : PrimTy.uint.Denote) :
    Path (.ref (.array (.ref (.struct "Person")))) .uint :=
  .at i (.field (f := "age") (T := .uint) (by decide) .nil)

-- Person has three slots; age follows the two-slot Account member.
example (i : PrimTy.uint.Denote) :
    locate (personAge i) (.root 7) = .data (.root 7) (i.val.toNat * 3 + 2) := by rfl

-- A mapping to Person arrays composes its key and array/member path.
example (k i : PrimTy.uint.Denote) :
    locate ((Path.key k .nil).append (personAge i)) (.root 7) =
      .data (.hash (keyWord k) (.root 7) 0) (i.val.toNat * 3 + 2) := by
  rw [locate_append]
  rfl

-- Descending into an array member retains the enclosing mapping's hash input.
example (k i : PrimTy.uint.Denote) :
    ancestry (.hash (keyWord k) (.root 7) 0) <+:
      ancestry (locate (personAge i) (.hash (keyWord k) (.root 7) 0)) :=
  ancestry_locate (personAge i) _

-- Field boundaries and fixed-array strides agree with the dependent struct layout.
example {s f : Name} {T : Ty} (h : lookupBy f (structDef s) = some T) :
    offset s f + size T ≤ size (.ref (.struct s)) := by
  rw [size_struct]
  exact offsetIn_bound h

example (n : Nat) : size (.ref (.fixed (.ref (.struct "Person")) n)) = n * 3 := by
  rw [size_fixed, size_struct]
  rfl

-- Equal encoded inputs reached by actual typed references decode to equal preimages.
-- This neither assumes nor concludes injectivity of keccak.
example {C : Contract} {T : Ty} (r : SRef C T) {p q : Pre}
    (hp : p ∈ ancestry (reference r)) (hq : q ∈ ancestry (reference r))
    (h : encoded p = encoded q) : p = q :=
  encoded_inj (ancestry_words _ (reference_bounded r) _ hp)
    (ancestry_words _ (reference_bounded r) _ hq) h

-- Array data and mapping entry encodings cannot be confused, even at the same word.
example : encoded (.data 7) ≠ encoded (.entry 7 0) := by
  intro h
  have e := encoded_inj (p := .data 7) (q := .entry 7 0)
    (by unfold Pre.Words; decide) (by unfold Pre.Words; decide) h
  cases e

end IntrinsicStorageLayoutControls

/-! Preimage controls: the strengthened laws pin concrete storage and the actual
frame observers of the landed `IntrinsicStorage.Preimages` modules. -/
namespace IntrinsicSession
open Solidity.Roadmap Solidity.Storage Solidity.Semantics Solidity.Semantics.IntrinsicStorage

/-- No empty or toy accounting: every slot preimage of an actual typed read in
an account of a typed world is among the world's stored keys, and so (by
`Laws.stored_hashed`) among the slot preimages of a run resumed there. -/
example (F : Fixed) (I : IntrinsicSpec) (V : View I) (laws : Laws F I V)
    (storage : StorageLaws F I V) (t : TypedWorld) (a : ContractWorld.Address)
    (k : Fin t.code.contracts.length) (st : Solidity.Storage (t.code.catalog k))
    (ha : t.world.accounts a = some ⟨k, st⟩) {T : Ty} (r : SRef (t.code.catalog k) T)
    {v : SVal T} (hv : st.find r = some v) {p : Pre} (hp : p ∈ ancestry (reference r))
    (e : I.lang.Env) (res : I.lang.Res) :
    encoded p ∈ I.slotHashed (I.ofWorld (V.resume t)) e res :=
  laws.stored_hashed t e res _ (storage.stored t ▸ read_stored t.world a k st ha r hv hp)

/-- Every slot input a frame accounts for is also an accounted hash input. -/
example (I : IntrinsicSpec) (p : I.lang.Prog) (en : I.lang.Env) (r : I.lang.Res)
    (a : Inputs) (h : FrameInputs I p en r a) {b : List UInt8} (hb : b ∈ a.slots) :
    b ∈ I.hashed p en r :=
  h.2 b (a.slot_hashed hb)

/-- A completed observation of a call frame is the actual call: the fuel the
laws witness cannot stand in for a truncated frame. -/
example {K : Type} [DecidableEq K] {contracts : K → Contract} (n : Nat)
    (w : ContractWorld.World contracts) {k : K} {α : Type} (r : ContractWorld.Handle k)
    (entry : ContractWorld.Entry (contracts k) α) (ctx : ContractWorld.Context)
    (fin : (Frame.call n w r entry ctx).result ≠ .error .diverge) :
    (Frame.call n w r entry ctx).result = w.call r entry ctx :=
  (Frame.call_approx n w r entry ctx).eq fin

/-- Rollback of a failed frame discards its world, never its observed inputs, so
the inputs hashed before a revert stay accounted. -/
example {K : Type} [DecidableEq K] {contracts : K → Contract} (n : Nat)
    (w : ContractWorld.World contracts) (k : K) (self : ContractWorld.Address)
    (ctor : Prog (contracts k) [] []) (ctx : ContractWorld.Context) {e : THalt}
    (h : (Frame.create n w k self ctor ctx).result = .error e) :
    (Frame.atomic w (Frame.create n w k self ctor ctx)).2 =
      (Frame.create n w k self ctor ctx).inputs := by
  rw [Frame.atomic_failed w _ h]

end IntrinsicSession

end Solidity.Goals
