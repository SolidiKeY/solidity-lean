import Solidity.Backend.Failure.Checkpoint

/-!
Transport of published local checkpoint relations and the approved G01 hash
premise. Local journals are not transaction worlds. No new execution semantics,
hash assumption, account relation or resource adequacy claim is introduced.
-/
namespace SolidityBridge.RoadmapV15
open Solidity Solidity.Roadmap

/-- Membership transport covers reordering, duplicate queries and rollback
views. Both lists remain restricted to the supplied run's actual preimages. -/
theorem hashPremise_mono {F : Fixed} {xs ys runHashes runSlots : List Bytes}
    (hh : ∀ x ∈ xs, x ∈ runHashes) (hs : ∀ x ∈ ys, x ∈ runSlots)
    (h : HashPremise F runHashes runSlots) : HashPremise F xs ys :=
  ⟨h.1.mono hh, h.2.mono hs⟩

/-- A transaction's suffix inherits the whole observed run's premise.
Premises for two isolated transactions alone are insufficient: cross-run
collisions and region overlaps are still obligations of the supplied premise. -/
theorem hashPremise_suffix {F : Fixed} (beforeHashes txHashes beforeSlots txSlots : List Bytes)
    (h : HashPremise F (beforeHashes ++ txHashes) (beforeSlots ++ txSlots)) :
    HashPremise F txHashes txSlots :=
  hashPremise_mono
    (fun _ hx => List.mem_append_right beforeHashes hx)
    (fun _ hx => List.mem_append_right beforeSlots hx) h

open Backend.Failure.Local

/-- A relation between published local journals transports across the same
success/revert outcome when both the live journals and restored snapshots are
related. The snapshot premise must be supplied by the world/transaction owner. -/
theorem checkpoint_relation {P T P' T' : Type}
    (R : Journal P T → Journal P' T' → Prop)
    (left : Checkpoint P T) (right : Checkpoint P' T')
    (live : Journal P T) (live' : Journal P' T') (o : Outcome)
    (hsaved : R (restore left) (restore right)) (hlive : R live live') :
    R (finish left o live) (finish right o live') := by
  cases o with
  | success bytes => exact hlive
  | revert bytes => exact hsaved

/-- Exact payload equality is independent of rollback of the journal. -/
theorem checkpoint_observation {P T P' T' O : Type}
    (observe : Journal P T → O) (observe' : Journal P' T' → O)
    (left : Checkpoint P T) (right : Checkpoint P' T')
    (live : Journal P T) (live' : Journal P' T') (o : Outcome)
    (hsaved : observe (restore left) = observe' (restore right))
    (hlive : observe live = observe' live') :
    (o, observe (finish left o live)) = (o, observe' (finish right o live')) := by
  exact congrArg (fun value => (o, value))
    (checkpoint_relation (fun a b => observe a = observe' b)
      left right live live' o hsaved hlive)

end SolidityBridge.RoadmapV15
