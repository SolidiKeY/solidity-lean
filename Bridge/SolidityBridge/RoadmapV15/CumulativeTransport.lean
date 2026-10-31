import SolidityBridge.RoadmapV15.PremiseTransport

/-!
Exact decomposition of the approved cumulative run premise and relational
composition of published local journals. Cross-run clauses below are equivalent
to the original premise, not new hash assumptions. Production execution query
tracking and transaction-world rollback must still be supplied by their owners.
-/
namespace SolidityBridge.RoadmapV15
open Solidity Solidity.Roadmap

/-- A cumulative approved premise decomposes into the two local premises and
exactly the cross-preimage/cross-region clauses it already contains. Same-preimage
repeats are allowed; the fixed hash, region length and roots are unchanged. -/
theorem hashPremise_append_iff (F : Fixed) (ah bh aslots bslots : List Bytes) :
    HashPremise F (ah ++ bh) (aslots ++ bslots) ↔
      HashPremise F ah aslots ∧ HashPremise F bh bslots ∧
      (∀ x ∈ ah, ∀ y ∈ bh, F.hash x = F.hash y → x = y) ∧
      (∀ x ∈ aslots, ∀ y ∈ bslots, x ≠ y →
        ¬ Hash.Near (2 ^ 256) F.regionLen (F.hash x).val (F.hash y).val) := by
  constructor
  · intro h
    refine ⟨hashPremise_mono (fun _ hx => List.mem_append_left bh hx)
      (fun _ hx => List.mem_append_left bslots hx) h,
      hashPremise_suffix ah bh aslots bslots h, ?_, ?_⟩
    · intro x hx y hy he
      exact h.1 x (List.mem_append_left bh hx) y (List.mem_append_right ah hy) he
    · intro x hx y hy hne
      exact h.2.1 x (List.mem_append_left bslots hx) y (List.mem_append_right aslots hy) hne
  · rintro ⟨ha, hb, hcross, hregions⟩
    constructor
    · exact Hash.collisionFree_append.mpr ⟨ha.1, hb.1, hcross⟩
    · constructor
      · intro x hx y hy hne
        rcases List.mem_append.mp hx with hx | hx <;>
          rcases List.mem_append.mp hy with hy | hy
        · exact ha.2.1 x hx y hy hne
        · exact hregions x hx y hy hne
        · intro hoverlap
          exact hregions y hy x hx (Ne.symm hne) hoverlap.symm
        · exact hb.2.1 x hx y hy hne
      · intro x hx r hr
        rcases List.mem_append.mp hx with hx | hx
        · exact ha.2.2 x hx r hr
        · exact hb.2.2 x hx r hr

/-- Reordering two recorded segments changes neither approved premise. This
is only query-list transport, never a claim that executions commute. -/
theorem hashPremise_append_comm (F : Fixed) (ah bh aslots bslots : List Bytes) :
    HashPremise F (ah ++ bh) (aslots ++ bslots) ↔
      HashPremise F (bh ++ ah) (bslots ++ aslots) := by
  constructor <;> intro h
  · apply hashPremise_mono (runHashes := ah ++ bh) (runSlots := aslots ++ bslots) _ _ h
    · intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact List.mem_append_right ah hx
      · exact List.mem_append_left bh hx
    · intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact List.mem_append_right aslots hx
      · exact List.mem_append_left bslots hx
  · apply hashPremise_mono (runHashes := bh ++ ah) (runSlots := bslots ++ aslots) _ _ h
    · intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact List.mem_append_right bh hx
      · exact List.mem_append_left ah hx
    · intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact List.mem_append_right bslots hx
      · exact List.mem_append_left aslots hx

open Backend.Failure.Local

/-- Compose published checkpoint relations for arbitrary inner/outer outcomes.
All three correspondence premises are explicit; no production-world snapshot
or nonce/log/balance preservation is manufactured by this local theorem. -/
theorem checkpoint_relation_nested {P T P' T' : Type}
    (R : Journal P T → Journal P' T' → Prop)
    (outer : Checkpoint P T) (outer' : Checkpoint P' T')
    (inner : Checkpoint P T) (inner' : Checkpoint P' T')
    (live : Journal P T) (live' : Journal P' T') (innerOutcome outerOutcome : Outcome)
    (ho : R (restore outer) (restore outer')) (hi : R (restore inner) (restore inner'))
    (hl : R live live') :
    R (finish outer outerOutcome (finish inner innerOutcome live))
      (finish outer' outerOutcome (finish inner' innerOutcome live')) :=
  checkpoint_relation R outer outer' _ _ outerOutcome ho
    (checkpoint_relation R inner inner' live live' innerOutcome hi hl)

end SolidityBridge.RoadmapV15
