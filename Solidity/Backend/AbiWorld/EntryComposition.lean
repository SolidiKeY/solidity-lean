import Solidity.Backend.AbiWorld.TupleReadback

/-! Structural composition of the EXISTING indexed entry recursion. These
identities retain the same fuel, exact cursor and ordered failure propagation;
they are not a new decoder or a desired-execution hypothesis. -/
namespace Solidity.Backend.AbiWorld.EntryComposition
open AbiEntry

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



/-- Any two actual dynamic intrinsic values use the actual assembled head
length and first payload length. This is a codec equality, not another codec. -/
theorem encoded_dynamic_pair {s t : AbiEntry.Shape} (v : AbiEntry.Val s) (w : AbiEntry.Val t)
    (hs : s.dynamic = true) (ht : t.dynamic = true) :
    encodeArgs (.cons v (.cons w .nil)) = AbiEntry.wordBytes 64 ++
      AbiEntry.wordBytes (64 + (Val.enc v).length) ++ Val.enc v ++ Val.enc w := by
  simp only [encodeArgs,Vals.parts,hs,ht,AbiEntry.assemble,List.foldl_cons,List.foldl_nil,
    ite_true,Nat.zero_add,AbiEntry.assemble.go,List.append_nil,List.append_assoc]

/-- Actual byte windows for the dynamic pair layout, arbitrary selector and
suffix. The range premise is on the real offset, not just a value length. -/
theorem layout_reads (first second selector post : List UInt8) (sel : selector.length = 4)
    (range : 64 + first.length < AbiEntry.W) :
    let data := selector ++ AbiEntry.wordBytes 64 ++ AbiEntry.wordBytes (64 + first.length) ++ first ++ second ++ post
    load data 4 = 64 ∧ load data 36 = 64 + first.length ∧
    data.drop 68 = first ++ second ++ post ∧ data.drop (4 + (64 + first.length)) = second ++ post := by
  dsimp only
  refine ⟨?_,?_,?_,?_⟩
  · simpa only [List.append_assoc,sel] using CanonicalReadback.load_word selector
      (AbiEntry.wordBytes (64 + first.length) ++ first ++ second ++ post) 64 (by decide)
  · simpa only [List.append_assoc,List.length_append,MixedPacket.word_length,sel] using
      CanonicalReadback.load_word (selector ++ AbiEntry.wordBytes 64) (first ++ second ++ post)
        (64 + first.length) range
  · have h : (selector ++ AbiEntry.wordBytes 64 ++ AbiEntry.wordBytes (64 + first.length)).length = 68 := by
      simp only [List.length_append,MixedPacket.word_length,sel]
    simpa only [List.append_assoc] using List.drop_left' h (l₂ := first ++ second ++ post)
  · have h : (selector ++ AbiEntry.wordBytes 64 ++ AbiEntry.wordBytes (64 + first.length) ++ first).length =
        4 + (64 + first.length) := by simp only [List.length_append,MixedPacket.word_length,sel]; omega
    simpa only [List.append_assoc] using List.drop_left' h (l₂ := second ++ post)



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

/-- info: 'Solidity.Backend.AbiWorld.EntryComposition.heads_append' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms heads_append
/-- info: 'Solidity.Backend.AbiWorld.EntryComposition.enter_append' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms enter_append
/-- info: 'Solidity.Backend.AbiWorld.EntryComposition.encoded_dynamic_pair' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms encoded_dynamic_pair
/-- info: 'Solidity.Backend.AbiWorld.EntryComposition.layout_reads' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms layout_reads
/-- info: 'Solidity.Backend.AbiWorld.EntryComposition.prefix_failure' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms prefix_failure
/-- info: 'Solidity.Backend.AbiWorld.EntryComposition.tail_failure' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms tail_failure
end Solidity.Backend.AbiWorld.EntryComposition
