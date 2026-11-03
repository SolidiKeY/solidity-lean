import Solidity.Semantics.AbiEntry

/-! Entry-only port of V13 85d13e5c7db386fd832391be5f7d04970ad31f22.
The codec equality/window section stays with V13; ordered entry proofs and
statements are retained. Structural composition of the EXISTING indexed entry recursion. These
identities retain the same fuel, exact cursor and ordered failure propagation;
they are not a new decoder or a desired-execution hypothesis. -/
namespace Solidity.Backend.AbiEntry.EntryComposition
open Solidity.AbiEntry

def appendEntries {ps qs : List Param} (es : Entries ps) (fs : Entries qs) : Entries (ps ++ qs) :=
  Entries.casesOn (motive := fun ps _ => Entries qs → Entries (ps ++ qs)) es
    (fun fs => fs) (fun e tail fs => .cons e (appendEntries tail fs)) fs
termination_by structural es

theorem heads_cons (p : Param) (ps : List Param) :
    headsOf (p :: ps) = p.shape.headSize + headsOf ps := rfl

theorem heads_append (ps qs : List Param) : headsOf (ps ++ qs) = headsOf ps + headsOf qs := by
  induction ps with
  | nil => simp only [List.nil_append,headsOf,List.map_nil,Shape.headsSize,Nat.zero_add]
  | cons p ps ih => simp only [List.cons_append,heads_cons,ih,Nat.add_assoc]

/-- Arbitrary parameter-list concatenation preserves the actual head position,
allocation cursor, same fuel, and all failures in their original order. -/
theorem enter_append (I : Input) (f : Nat) (ps qs : List Param) (pos a : Nat) :
    enter I f (ps ++ qs) pos a = (do
      let (es,a') ← enter I f ps pos a
      let (fs,a'') ← enter I f qs (pos + headsOf ps) a'
      pure (appendEntries es fs,a'')) := by
  induction ps generalizing pos a with
  | nil =>
    simp only [List.nil_append,headsOf,List.map_nil,Shape.headsSize,Nat.add_zero,
      enter,bind,Except.bind,pure,Except.pure,appendEntries]
    cases enter I f qs pos a <;> rfl
  | cons p ps ih =>
    cases loc : p.loc
    case value | memory =>
      cases h : melem I f p.shape 4 (4 + pos) a with
      | error e => simp only [List.cons_append,enter,loc,h,bind,Except.bind]
      | ok va =>
        rcases va with ⟨v,a'⟩
        simp only [List.cons_append,enter,loc,h,bind,Except.bind,pure,Except.pure,ih,heads_cons,Nat.add_assoc]
        cases h' : enter I f ps (pos + p.shape.headSize) a' with
        | error e => rfl
        | ok ea =>
          rcases ea with ⟨es,a''⟩
          dsimp only
          cases enter I f qs (pos + (p.shape.headSize + headsOf ps)) a'' <;> rfl
    case calldata =>
      cases h : cref I p.shape 4 pos with
      | error e => simp only [List.cons_append,enter,loc,h,bind,Except.bind]
      | ok ref =>
        rcases ref with ⟨addr,len⟩
        simp only [List.cons_append,enter,loc,h,bind,Except.bind,pure,Except.pure,ih,heads_cons,Nat.add_assoc]
        cases h' : enter I f ps (pos + p.shape.headSize) a with
        | error e => rfl
        | ok ea =>
          rcases ea with ⟨es,a'⟩
          dsimp only
          cases enter I f qs (pos + (p.shape.headSize + headsOf ps)) a' <;> rfl



/-- A failed prefix is not reclassified or hidden by a later parameter list. -/
theorem prefix_failure (I : Input) (f : Nat) (ps qs : List Param) (pos a : Nat) (e : Fail)
    (h : enter I f ps pos a = .error e) : enter I f (ps ++ qs) pos a = .error e := by
  rw [enter_append,h]
  rfl

/-- A selected tail starts at the actual reached cursor and full prefix head
extent, retaining its own failure. Both sides retain the same original fuel
argument; no remaining-fuel consumption relation is claimed. -/
theorem tail_failure (I : Input) (f : Nat) (ps qs : List Param) (pos a a' : Nat)
    (es : Entries ps) (e : Fail) (prefixRun : enter I f ps pos a = .ok (es,a'))
    (tail : enter I f qs (pos + headsOf ps) a' = .error e) :
    enter I f (ps ++ qs) pos a = .error e := by
  rw [enter_append,prefixRun]
  simp only [bind,Except.bind,tail]

/-- info: 'Solidity.Backend.AbiEntry.EntryComposition.heads_append' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms heads_append
/-- info: 'Solidity.Backend.AbiEntry.EntryComposition.enter_append' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms enter_append
/-- info: 'Solidity.Backend.AbiEntry.EntryComposition.prefix_failure' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms prefix_failure
/-- info: 'Solidity.Backend.AbiEntry.EntryComposition.tail_failure' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms tail_failure
/-- info: 'Solidity.Backend.AbiEntry.EntryComposition.heads_cons' does not depend on any axioms -/
#guard_msgs in #print axioms heads_cons
end Solidity.Backend.AbiEntry.EntryComposition
