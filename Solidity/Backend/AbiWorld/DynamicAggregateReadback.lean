import Solidity.Backend.AbiWorld.DynamicListReadback

/-! Actual mixed dynamic tuple decoding. Member recursion consumes its original
fuel and allocates after the tuple's real outer frame; byte offsets remain
relative to the tuple base. No second semantics or runtime encoder. -/
namespace Solidity.Backend.AbiWorld.DynamicAggregateReadback
open AbiEntry DynamicListReadback

theorem bytes_at (bs : List UInt8) (I : Input) (pre post : List UInt8) (base src off a f : Nat)
    (data : I.data = pre ++ Val.enc (.bytes bs) ++ post) (position : pre.length = base + off)
    (read : load I.data src = off) (offset : off ≤ lim)
    (allocation : I.free + (a + BytesReadback.allocationBytes bs) ≤ lim) (fuel : 2 ≤ f) :
    melem I f .bytes base src a = .ok (.bytes bs,a + BytesReadback.allocationBytes bs) := by
  obtain ⟨g,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : f ≠ 0)
  have decoded := BytesReadback.mdec_bytes bs I pre
    (List.replicate (roundUp bs.length - bs.length) 0 ++ post) a g
    (by simpa only [Val.enc,List.append_assoc] using data) allocation (by omega)
  rw [position] at decoded
  simp only [melem,Shape.dynamic,read,if_neg (Nat.not_lt.mpr offset),decoded,ite_true]

/-- Arbitrary heterogeneous word/bytes members at arbitrary real byte windows.
The SAME input is used, but mmembers decreases the original fuel per member. -/
theorem members_window (ss : List AbiEntry.Shape) (vs : Vals ss) (I : Input)
    (hp hs tp ts : List UInt8) (base pos off a f : Nat) (leaves : LeafShapes ss)
    (headData : I.data = hp ++ (AbiEntry.assemble.go (Vals.parts vs) off).1 ++ hs)
    (tailData : I.data = tp ++ (AbiEntry.assemble.go (Vals.parts vs) off).2 ++ ts)
    (headPos : hp.length = base + pos) (tailPos : tp.length = base + off)
    (size : I.size ≤ lim) (allocation : I.free + (a + tailSize vs) ≤ lim) (fuel : ss.length + 2 ≤ f) :
    mmembers I f ss base pos a = .ok (vs,a + tailSize vs) := by
  induction ss generalizing hp tp pos off a f with
  | nil => cases vs; cases f <;> rfl
  | cons s ss ih =>
    have rest : LeafShapes ss := fun s hs => leaves s (List.mem_cons_of_mem _ hs)
    obtain ⟨g,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by simp only [List.length_cons] at fuel; omega : f ≠ 0)
    have gf : ss.length + 2 ≤ g := by simp only [List.length_cons] at fuel; omega
    rcases leaves s List.mem_cons_self with ⟨k,rfl⟩ | rfl
    · cases vs with
      | cons v vs => cases v with
        | word w =>
          have read : load I.data (base + pos) = w.val := by
            rw [← headPos,headData,go_word]
            simpa only [List.append_assoc] using CanonicalReadback.load_word hp
              ((AbiEntry.assemble.go (Vals.parts vs) off).1 ++ hs) w.val w.lt
          have dm := StaticAggregateReadback.word_at I k w base (base + pos) a g read (by omega)
          have tail := ih vs (hp ++ AbiEntry.wordBytes w.val) tp (pos + 32) off a g rest
            (by simpa only [go_word,List.append_assoc] using headData)
            (by simpa only [go_word] using tailData)
            (by simp only [List.length_append,MixedPacket.word_length,headPos]; omega) tailPos
            (by simpa only [tail_word] using allocation) gf
          simp only [mmembers,dm,Shape.headSize,tail,tail_word]
    · cases vs with
      | cons v vs => cases v with
        | bytes bs =>
          let b := BytesReadback.allocationBytes bs
          have plen : (Val.enc (.bytes bs)).length = b := BytesArrayReadback.byte_payload_length bs
          have offlim : off ≤ lim := by
            have h : tp.length ≤ I.size := by simp only [Input.size,tailData,List.length_append]; omega
            omega
          have read : load I.data (base + pos) = off := by
            rw [← headPos,headData,go_bytes]
            simpa only [List.append_assoc] using CanonicalReadback.load_word hp
              ((AbiEntry.assemble.go (Vals.parts vs) (off + (Val.enc (.bytes bs)).length)).1 ++ hs) off
              (Nat.lt_of_le_of_lt offlim (by decide))
          have bnd : I.free + (a + b) ≤ lim := by rw [tail_bytes] at allocation; omega
          have dm := bytes_at bs I tp
            ((AbiEntry.assemble.go (Vals.parts vs) (off + (Val.enc (.bytes bs)).length)).2 ++ ts)
            base (base + pos) off a g
            (by simpa only [go_bytes,List.append_assoc] using tailData) tailPos read offlim bnd (by omega)
          have tail := ih vs (hp ++ AbiEntry.wordBytes off) (tp ++ Val.enc (.bytes bs))
            (pos + 32) (off + (Val.enc (.bytes bs)).length) (a + b) g rest
            (by simpa only [go_bytes,List.append_assoc] using headData)
            (by simpa only [go_bytes,List.append_assoc] using tailData)
            (by simp only [List.length_append,MixedPacket.word_length,headPos]; omega)
            (by simp only [List.length_append,tailPos]; omega)
            (by rw [tail_bytes] at allocation; omega) gf
          simp only [mmembers,dm,Shape.headSize,tail,tail_bytes,b,Nat.add_assoc]

/-- Actual mixed tuple constructor: its outer member-pointer allocation is
additional to every bytes object; fuel is derived from mmembers, not enter. -/
theorem mdec_tuple (ss : List AbiEntry.Shape) (vs : Vals ss) (I : Input) (pre post : List UInt8)
    (a f : Nat) (leaves : LeafShapes ss) (data : I.data = pre ++ encodeArgs vs ++ post)
    (size : I.size ≤ lim) (allocation : I.free + (a + (ss.length * 32 + tailSize vs)) ≤ lim)
    (fuel : ss.length + 3 ≤ f) :
    mdec I f (.tuple ss) pre.length a = .ok (.tuple vs,a + (ss.length * 32 + tailSize vs)) := by
  let off := ss.length * 32
  let h := (AbiEntry.assemble.go (Vals.parts vs) off).1
  let t := (AbiEntry.assemble.go (Vals.parts vs) off).2
  have layout : encodeArgs vs = h ++ t := encoded ss vs leaves
  have hlen : h.length = off := head_length ss vs off leaves
  have region : pre.length + Shape.headsSize ss ≤ I.size := by
    simp only [Input.size,data,List.length_append,encoded_length ss vs leaves,heads_leaves ss leaves]
    omega
  obtain ⟨g,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : f ≠ 0)
  have outer : I.free + (a + ss.length * 32) ≤ lim := by omega
  have decoded := members_window ss vs I pre (t ++ post) (pre ++ h) post pre.length 0 off
    (a + ss.length * 32) g leaves
    (by simpa only [layout,List.append_assoc,h] using data)
    (by simpa only [layout,List.append_assoc,t] using data)
    (by omega) (by simp only [List.length_append,hlen]) size (by omega) (by omega)
  simp only [mdec,if_neg (Nat.not_lt.mpr region),alloc,StaticAggregateReadback.aligned,if_pos outer,decoded,Nat.add_assoc]

theorem tuple_encoded (ss : List AbiEntry.Shape) (vs : Vals ss) (dynamic : Shape.anyDynamic ss = true) :
    encodeArgs (.cons (.tuple vs) .nil) = AbiEntry.wordBytes 32 ++ encodeArgs vs := by
  simp only [encodeArgs,Vals.parts,Shape.dynamic,dynamic,Val.enc,AbiEntry.assemble,List.foldl_cons,
    List.foldl_nil,ite_true,Nat.zero_add,AbiEntry.assemble.go,List.append_nil]

/-- A genuinely dynamic Shape.tuple, not a flattened top-level parameter
list. Both memory and calldata body identity follow from actual eager decode
and the published eager_cref theorem, with the tuple's outer allocation. -/
theorem tuple_roundtrip (ss : List AbiEntry.Shape) (vs : Vals ss) (selector post : List UInt8) (free f : Nat)
    (lazy : Bool) (leaves : LeafShapes ss) (dynamic : Shape.anyDynamic ss = true) (sel : selector.length = 4)
    (size : (selector ++ encodeArgs (.cons (.tuple vs) .nil) ++ post).length ≤ lim)
    (allocation : free + (ss.length * 32 + tailSize vs) ≤ lim) (fuel : ss.length + 4 ≤ f) :
    ∃ es : Entries (StaticAggregateReadback.tupleParams ss lazy),
      enter ⟨selector ++ encodeArgs (.cons (.tuple vs) .nil) ++ post,free⟩ f
        (StaticAggregateReadback.tupleParams ss lazy) 0 0 =
          .ok (es,if lazy then 0 else ss.length * 32 + tailSize vs) ∧
      entry ⟨selector ++ encodeArgs (.cons (.tuple vs) .nil) ++ post,free⟩ f
        (StaticAggregateReadback.tupleParams ss lazy) = .ok es ∧
      bodyValues ⟨selector ++ encodeArgs (.cons (.tuple vs) .nil) ++ post,free⟩ f
        (StaticAggregateReadback.tupleParams ss lazy) es 0 = .ok (.cons (.tuple vs) .nil) ∧
      verdict ⟨selector ++ encodeArgs (.cons (.tuple vs) .nil) ++ post,free⟩ f
        (StaticAggregateReadback.tupleParams ss lazy) = .run (.cons (.tuple vs) .nil) := by
  let I : Input := ⟨selector ++ encodeArgs (.cons (.tuple vs) .nil) ++ post,free⟩
  have data : I.data = (selector ++ AbiEntry.wordBytes 32) ++ encodeArgs vs ++ post := by
    simp only [I,tuple_encoded ss vs dynamic,List.append_assoc]
  have read : load I.data 4 = 32 := by
    simp only [I,tuple_encoded ss vs dynamic]
    simpa only [sel,List.append_assoc] using CanonicalReadback.load_word selector (encodeArgs vs ++ post) 32 (by decide)
  obtain ⟨g,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : f ≠ 0)
  have dec := mdec_tuple ss vs I (selector ++ AbiEntry.wordBytes 32) post 0 g leaves data size
    (by simpa only [I,Nat.zero_add] using allocation) (by omega)
  simp only [List.length_append,sel,MixedPacket.word_length,Nat.zero_add] at dec
  have dm : melem I (g + 1) (.tuple ss) 4 4 0 = .ok (.tuple vs,ss.length * 32 + tailSize vs) := by
    simp only [melem,Shape.dynamic,dynamic,ite_true,read,if_neg (by decide : ¬ lim < 32),dec]
  have ew : eager I (g + 1) (.tuple ss) 0 = .ok (.tuple vs) := by simp only [eager,Nat.add_zero,dm]
  obtain ⟨addr,len,cr,lv⟩ := eager_cref (I := I) size ew
  let p : Param := {shape := .tuple ss,loc := if lazy then .calldata else .memory}
  obtain ⟨es,en,body⟩ := one_success p (.tuple vs) I 0 0 (g + 1) (ss.length * 32 + tailSize vs) addr len
    (by simpa only [Nat.zero_add] using dm) ew cr
  have heads : ¬ I.size < 4 + headsOf [p] := by
    simp only [headsOf,p,List.map_cons,List.map_nil,Shape.headsSize,Shape.headSize,dynamic,
      ite_true,Nat.add_zero,Input.size,I,tuple_encoded ss vs dynamic,List.length_append,sel,MixedPacket.word_length]
    omega
  have ep : entry I (g + 1) [p] = .ok es := by rw [entry,if_neg heads,en]
  refine ⟨es,?_,ep,body,?_⟩
  · cases lazy <;> simpa only [p,Bool.false_eq_true,ite_false,ite_true,BEq.beq,reduceCtorEq,
      decide_false,decide_true,Nat.zero_add] using en
  · change verdict I (g + 1) [p] = _
    rw [verdict,ep]
    simp only [body]


/-- info: 'Solidity.Backend.AbiWorld.DynamicAggregateReadback.bytes_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms bytes_at
/-- info: 'Solidity.Backend.AbiWorld.DynamicAggregateReadback.members_window' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms members_window
/-- info: 'Solidity.Backend.AbiWorld.DynamicAggregateReadback.mdec_tuple' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms mdec_tuple
/-- info: 'Solidity.Backend.AbiWorld.DynamicAggregateReadback.tuple_encoded' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms tuple_encoded
/-- info: 'Solidity.Backend.AbiWorld.DynamicAggregateReadback.tuple_roundtrip' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms tuple_roundtrip

end Solidity.Backend.AbiWorld.DynamicAggregateReadback
