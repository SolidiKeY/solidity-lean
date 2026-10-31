import Solidity.Semantics.ContractWorldCertificates
import Solidity.Semantics.TransientWorld
import SolidityBridge.RoadmapV15.WordByteTransport

/-!
Consequences of the published typed, opt-in world API, consumed read only.
The owner supplies actual frame results; source admission, nonce/log semantics,
gas and pinned-EVM/world correspondence are not supplied by these theorems.
Transient reset occurs once at the outer boundary, never between siblings.
-/
namespace SolidityBridge.RoadmapV15
open Solidity Solidity.ContractWorld
variable {K : Type} {contracts : K → Contract}

/-- An actual failed frame retains the original balance bytes while the
existing boundary clears its input transient region. Exact halts are exposed
separately by world_transaction_prefix_failure. -/
theorem world_failure_balance_bytes {α : Type} (w : World contracts)
    (frame : World contracts → TRes (World contracts × α)) (e : THalt)
    (failed : frame w.resetTransient = .error e) (a : Address) :
    (Backend.toBytesBE 32
      (Backend.Scalar.encodeValue .uint ((w.transact frame).1.balance a)).toNat).toList =
      (Backend.toBytesBE 32 (Backend.Scalar.encodeValue .uint (w.balance a)).toNat).toList := by
  rw [World.transact_failure w frame e failed]
  rfl

/-- Code identity is retained, but transient cells are normalized rather than
incorrectly asserting equality to an arbitrary unnormalized entry store. -/
theorem world_failure_accounts {α : Type} (w : World contracts)
    (frame : World contracts → TRes (World contracts × α)) (e : THalt)
    (failed : frame w.resetTransient = .error e) (a : Address) :
    (w.transact frame).1.accounts a =
      (w.accounts a).map (fun ⟨k, st⟩ => ⟨k, Storage.resetTransient st⟩) := by
  rw [World.transact_failure w frame e failed]
  exact World.resetTransient_accounts w a

variable [DecidableEq K]

/-- A successful prefix and failed suffix are the actual existing operation
sequence's failure, not an assumed simulation or acceptance Boolean. -/
theorem world_sequence_failure (w mid : World contracts) (first second : Operation contracts)
    (e : THalt) (hprefix : first.run w = .ok mid) (suffix : second.run mid = .error e) :
    (Operation.seq first second).run w = .error e := by
  change (first.run w).bind (fun next => second.run next) = .error e
  rw [hprefix]
  exact suffix

/-- Exact result-valued transaction failure after an actual operation prefix.
The suffix sees mid, NOT mid.resetTransient; all returned halt data are kept. -/
theorem world_transaction_prefix_failure {α : Type} (w mid : World contracts)
    (first : Operation contracts) (tail : World contracts → TRes (World contracts × α))
    (e : THalt) (hprefix : first.run w.resetTransient = .ok mid)
    (suffix : tail mid = .error e) :
    w.transact (fun before => (first.run before).bind tail) = (w.resetTransient, .error e) := by
  apply World.transact_failure w _ e
  change (first.run w.resetTransient).bind tail = .error e
  rw [hprefix]
  exact suffix

/-- A result-valued successful suffix commits its actual result and normalized
world. There is no normalization between the prefix and suffix. -/
theorem world_transaction_prefix_success {α : Type} (w mid next : World contracts)
    (first : Operation contracts) (tail : World contracts → TRes (World contracts × α))
    (result : α) (hprefix : first.run w.resetTransient = .ok mid)
    (suffix : tail mid = .ok (next, result)) :
    w.transact (fun before => (first.run before).bind tail) =
      (next.resetTransient, .ok result) := by
  apply World.transact_commit w next _ result
  change (first.run w.resetTransient).bind tail = .ok (next, result)
  rw [hprefix]
  exact suffix

/-- Source operation-tree failure preserves the exact halt, with the published
entry/exit transient convention. Error.exhausted/diverge are not completed steps. -/
theorem world_operation_transaction_failure (w mid : World contracts)
    (first second : Operation contracts) (e : THalt)
    (hprefix : first.run w.resetTransient = .ok mid) (suffix : second.run mid = .error e) :
    (Operation.seq first second).transact w = (w.resetTransient, .error e) :=
  Operation.transact_failure (world_sequence_failure w.resetTransient mid first second e hprefix suffix)

/-- Persistent path observations survive an actual failed complete frame.
The persistent-root premise is essential; transient paths are reset instead. -/
theorem world_failure_persistent {α : Type} {U : Ty} (w : World contracts)
    (frame : World contracts → TRes (World contracts × α)) (e : THalt)
    (failed : frame w.resetTransient = .error e) {k : K} (r : Handle k)
    (path : SRef (contracts k) U) (persistent : path.root ∉ (contracts k).transientRoots) :
    ((w.transact frame).1.storage? r).bind (fun st => st.find path) =
      (w.storage? r).bind (fun st => st.find path) := by
  rw [World.transact_failure w frame e failed]
  exact World.resetTransient_persistent w r path persistent

/-- A caught creation failure resumes the suffix at its precise input world,
which may already contain a successful paid caller prefix. -/
theorem world_caught_creation_tail {α : Type} (w : World contracts) (a : α) (k : K)
    (target : α → Address) (ctor : α → Prog (contracts k) [] []) (context : α → Context)
    (e : THalt) (mutable : (context a).isStatic = false)
    (failed : w.create k (target a) (ctor a) (context a) = .error e)
    (caught : catchable e = true) (tail : Operation contracts) :
    (Operation.seq (.tryCreate (.ok a) k target ctor context) tail).run w = tail.run w := by
  change ((Operation.tryCreate (.ok a) k target ctor context).run w).bind tail.run = tail.run w
  rw [Operation.tryCreate_caught w a k target ctor context e mutable failed caught]
  rfl

/-- A failed argument remains outside the creation catch and prevents the tail,
including exact revert data and non-completing halts. -/
theorem world_argument_failure_tail {α : Type} (w : World contracts) (e : THalt) (k : K)
    (target : α → Address) (ctor : α → Prog (contracts k) [] []) (context : α → Context)
    (tail : Operation contracts) :
    (Operation.seq (.tryCreate (.error e) k target ctor context) tail).run w = .error e := by
  change ((Operation.tryCreate (.error e) k target ctor context).run w).bind tail.run = .error e
  rw [Operation.tryCreate_argument_failure w e k target ctor context]
  rfl
end SolidityBridge.RoadmapV15
