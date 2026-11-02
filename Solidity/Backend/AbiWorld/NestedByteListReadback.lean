import Solidity.Backend.AbiWorld.NestedByteReadback

/-! Actual heterogeneous recursive-array/word composition beyond LeafShapes.
This is a generic typed two-parameter client, not arbitrary recursive-list
coverage, Source admission or an unknown-memory encoder. -/
namespace Solidity.Backend.AbiWorld.NestedByteListReadback
open AbiEntry
abbrev Element := NestedByteReadback.Element

def packet {n : Nat} {k : Kind} (xs : Seq Element n) (w : Word k) : Vals [.array Element,.word k] :=
  .cons (.array xs) (.cons (.word w) .nil)

def params (k : Kind) (lazy : Bool) : List Param :=
  [{shape := .array Element,loc := if lazy then .calldata else .memory},{shape := .word k,loc := .value}]

def input {n : Nat} {k : Kind} (xs : Seq Element n) (w : Word k) (selector post : List UInt8) (free : Nat) : Input :=
  ⟨selector ++ encodeArgs (packet xs w) ++ post,free⟩

theorem encoded {n : Nat} {k : Kind} (xs : Seq Element n) (w : Word k) :
    encodeArgs (packet xs w) = AbiEntry.wordBytes 64 ++ AbiEntry.wordBytes w.val ++ Val.enc (.array xs) := by
  simp only [packet,encodeArgs,Vals.parts,Shape.dynamic,Val.enc,AbiEntry.assemble,List.foldl_cons,List.foldl_nil,
    ite_true,Bool.false_eq_true,ite_false,MixedPacket.word_length,Nat.zero_add,AbiEntry.assemble.go,List.append_nil]

/-- Canonical recursive array plus ANY actual validated Word k. The scalar is
read from the same actual input, with no ByteRange premise or assumed decoder
result. Original same parameter fuel and exact array allocation are retained. -/
theorem roundtrip {n : Nat} {k : Kind} (xs : Seq Element n) (w : Word k) (selector post : List UInt8)
    (free f : Nat) (lazy : Bool) (sel : selector.length = 4)
    (size : (input xs w selector post free).size ≤ lim)
    (allocation : free + (n * 32 + 32 + NestedByteReadback.tailCost xs) ≤ lim)
    (fuel : NestedByteReadback.fuelNeed xs + 2 ≤ f) :
    ∃ es : Entries (params k lazy),
      enter (input xs w selector post free) f (params k lazy) 0 0 =
        .ok (es,if lazy then 0 else n * 32 + 32 + NestedByteReadback.tailCost xs) ∧
      entry (input xs w selector post free) f (params k lazy) = .ok es ∧
      bodyValues (input xs w selector post free) f (params k lazy) es 0 = .ok (packet xs w) ∧
      verdict (input xs w selector post free) f (params k lazy) = .run (packet xs w) := by
  let I := input xs w selector post free
  let cost := n * 32 + 32 + NestedByteReadback.tailCost xs
  let a := if lazy then 0 else cost
  have data : I.data = selector ++ AbiEntry.wordBytes 64 ++ AbiEntry.wordBytes w.val ++ Val.enc (.array xs) ++ post := by
    simp only [I,input,encoded,List.append_assoc]
  have rh : load I.data 4 = 64 := by
    rw [data]
    simpa only [List.append_assoc,sel] using CanonicalReadback.load_word selector
      (AbiEntry.wordBytes w.val ++ Val.enc (.array xs) ++ post) 64 (by decide)
  have rwrd : load I.data 36 = w.val := by
    rw [data]
    simpa only [List.append_assoc,List.length_append,MixedPacket.word_length,sel] using
      CanonicalReadback.load_word (selector ++ AbiEntry.wordBytes 64) (Val.enc (.array xs) ++ post) w.val w.lt
  obtain ⟨g,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : f ≠ 0)
  have dec := NestedByteReadback.mdec_array xs I (selector ++ AbiEntry.wordBytes 64 ++ AbiEntry.wordBytes w.val)
    post 0 g (by simpa only [List.append_assoc] using data) size
    (by simpa only [I,input,Nat.zero_add] using allocation) (by omega)
  simp only [List.length_append,sel,MixedPacket.word_length,Nat.zero_add] at dec
  have dm : melem I (g + 1) (.array Element) 4 4 0 = .ok (.array xs,cost) := by
    simp only [melem,Shape.dynamic,ite_true,rh,if_neg (by decide : ¬ lim < 64)]
    exact dec
  have ew : eager I (g + 1) (.array Element) 0 = .ok (.array xs) := by simp only [eager,Nat.add_zero,dm]
  obtain ⟨addr,len,cr,lv⟩ := eager_cref (I := I) size ew
  let p : Param := {shape := .array Element,loc := if lazy then .calldata else .memory}
  let q : Param := {shape := .word k,loc := .value}
  obtain ⟨hs,he,hb⟩ := DynamicListReadback.one_success p (.array xs) I 0 0 (g + 1) cost addr len
    (by simpa only [Nat.zero_add] using dm) ew cr
  have he' : enter I (g + 1) [p] 0 0 = .ok (hs,a) := by
    cases lazy <;> simpa only [p,a,Bool.false_eq_true,ite_false,ite_true,BEq.beq,reduceCtorEq,
      decide_false,decide_true,Nat.zero_add] using he
  have dw := WordListReadback.word_melem I k w 32 a (g + 1) rwrd (by omega)
  have we : eager I (g + 1) (.word k) 32 = .ok (.word w) := by
    simp only [eager,WordListReadback.word_melem I k w 32 0 (g + 1) rwrd (by omega)]
  obtain ⟨ts,te,tb⟩ := DynamicListReadback.one_success q (.word w) I 32 a (g + 1) 0 36 0
    (by simpa only [Nat.add_zero] using dw) we rfl
  have te' : enter I (g + 1) [q] 32 a = .ok (ts,a) := by
    simpa only [q,BEq.beq,reduceCtorEq,decide_false,Bool.false_eq_true,ite_false,Nat.add_zero] using te
  have en : enter I (g + 1) [p,q] 0 0 = .ok (EntryComposition.appendEntries hs ts,a) := by
    change enter I (g + 1) ([p] ++ [q]) 0 0 = _
    rw [EntryComposition.enter_append,he']
    simp only [headsOf,p,List.map_cons,List.map_nil,Shape.headsSize,Shape.headSize,Nat.add_zero,Nat.zero_add,
      te',bind,Except.bind,pure,Except.pure]
  have body : bodyValues I (g + 1) [p,q] (EntryComposition.appendEntries hs ts) 0 = .ok (packet xs w) := by
    have h := BodyComposition.body_success I (g + 1) hs ts (.cons (.array xs) .nil) (.cons (.word w) .nil) 0 hb
      (by simpa only [headsOf,p,List.map_cons,List.map_nil,Shape.headsSize,Shape.headSize,Nat.add_zero,Nat.zero_add] using tb)
    simpa only [BodyComposition.appendValues_cons,BodyComposition.appendValues_nil,packet] using h
  have heads : ¬ I.size < 4 + headsOf [p,q] := by
    simp only [headsOf,p,q,List.map_cons,List.map_nil,Shape.headsSize,Shape.headSize,Nat.add_zero,
      Input.size,data,List.length_append,MixedPacket.word_length,sel]
    omega
  have ep : entry I (g + 1) [p,q] = .ok (EntryComposition.appendEntries hs ts) := by rw [entry,if_neg heads,en]
  refine ⟨EntryComposition.appendEntries hs ts,en,ep,body,?_⟩
  change verdict I (g + 1) [p,q] = _
  rw [verdict,ep]
  simp only [body]

theorem input_size {n : Nat} {k : Kind} (xs : Seq Element n) (w : Word k) (selector post : List UInt8) (free : Nat) :
    (input xs w selector post free).size = selector.length + 96 + n * 32 + NestedByteReadback.tailCost xs + post.length := by
  simp only [input,Input.size,encoded,List.length_append,MixedPacket.word_length,NestedByteReadback.array_length]
  omega


/-- info: 'Solidity.Backend.AbiWorld.NestedByteListReadback.encoded' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms encoded
/-- info: 'Solidity.Backend.AbiWorld.NestedByteListReadback.roundtrip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms roundtrip
/-- info: 'Solidity.Backend.AbiWorld.NestedByteListReadback.input_size' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms input_size

end Solidity.Backend.AbiWorld.NestedByteListReadback
