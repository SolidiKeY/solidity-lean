import Solidity.Backend.AbiWorld.ByteSequenceReadback

/-! Actual recursive Seq(array.bytes) canonical readback. Existing codecs,
values, decoders and allocation/fuel order remain unchanged. All bounds are
sufficient auxiliary facts, not new admission or runtime encoding semantics. -/
namespace Solidity.Backend.AbiWorld.NestedByteReadback
open AbiEntry
open DynamicListReadback (tails_independent one_success)
open ByteSequenceReadback (input params values encoded dynamic_head)

abbrev Element : AbiEntry.Shape := .array .bytes

def innerCost {m : Nat} (ys : Seq .bytes m) : Nat := m * 32 + 32 + ByteSequenceReadback.tailBytes ys

def innerFuel {m : Nat} (_ys : Seq .bytes m) : Nat := m + 4

/-- Sufficient ORIGINAL mseq fuel, derived per actual recursive element.
Not a default fuel change, minimality assertion or CPU/gas bound. -/
def fuelNeed : {n : Nat} → Seq Element n → Nat
  | _, .nil => 0
  | _, .cons (.array ys) xs => max (innerFuel ys) (fuelNeed xs) + 1

def tailCost {n : Nat} (xs : Seq Element n) : Nat :=
  (AbiEntry.assemble.go (Seq.parts xs) 0).2.length

theorem inner_length {m : Nat} (ys : Seq .bytes m) : (Val.enc (.array ys)).length = innerCost ys := by
  rw [ByteSequenceReadback.array_length]
  simp only [innerCost]
  omega

theorem go_cons {m n : Nat} (ys : Seq .bytes m) (xs : Seq Element n) (off : Nat) :
    AbiEntry.assemble.go (Seq.parts (.cons (.array ys) xs)) off =
      (AbiEntry.wordBytes off ++ (AbiEntry.assemble.go (Seq.parts xs) (off + (Val.enc (.array ys)).length)).1,
       Val.enc (.array ys) ++ (AbiEntry.assemble.go (Seq.parts xs) (off + (Val.enc (.array ys)).length)).2) := rfl

theorem tail_cons {m n : Nat} (ys : Seq .bytes m) (xs : Seq Element n) :
    tailCost (.cons (.array ys) xs) = innerCost ys + tailCost xs := by
  simp only [tailCost,go_cons,List.length_append]
  rw [tails_independent _ _ 0,inner_length]

theorem head_length {n : Nat} (xs : Seq Element n) (off : Nat) :
    (AbiEntry.assemble.go (Seq.parts xs) off).1.length = n * 32 := by
  induction n generalizing off with
  | zero => cases xs; rfl
  | succ n ih =>
    cases xs with
    | cons v xs => cases v with
      | array ys => simp only [go_cons,List.length_append,MixedPacket.word_length,ih,Nat.succ_mul]; omega

theorem head_fold {n : Nat} (xs : Seq Element n) (a : Nat) :
    (Seq.parts xs).foldl (fun acc (d,b) => acc + if d then 32 else b.length) a = a + n * 32 := by
  induction n generalizing a with
  | zero => cases xs; simp only [Seq.parts,List.foldl_nil,Nat.zero_mul,Nat.add_zero]
  | succ n ih =>
    cases xs with
    | cons v xs => cases v with
      | array ys => simp only [Seq.parts,Element,Shape.dynamic,List.foldl_cons,ite_true,ih,Nat.succ_mul]; omega

theorem fixed_encoded {n : Nat} (xs : Seq Element n) :
    Val.enc (.fixed xs) = (AbiEntry.assemble.go (Seq.parts xs) (n * 32)).1 ++
      (AbiEntry.assemble.go (Seq.parts xs) (n * 32)).2 := by
  simp only [Val.enc,AbiEntry.assemble,head_fold xs 0,Nat.zero_add]

theorem fixed_length {n : Nat} (xs : Seq Element n) :
    (Val.enc (.fixed xs)).length = n * 32 + tailCost xs := by
  rw [fixed_encoded,List.length_append,head_length,tails_independent _ _ 0]
  rfl

/-- The existing byte-array decoder validates its OWN count and inner heads
relative to the point AFTER that count. No inner successful-run premise. -/
theorem element_at {m : Nat} (ys : Seq .bytes m) (I : Input) (pre post : List UInt8) (base src off a f : Nat)
    (data : I.data = pre ++ Val.enc (.array ys) ++ post) (position : pre.length = base + off)
    (read : load I.data src = off) (offset : off ≤ lim) (size : I.size ≤ lim)
    (allocation : I.free + (a + innerCost ys) ≤ lim) (fuel : innerFuel ys ≤ f) :
    melem I f Element base src a = .ok (.array ys,a + innerCost ys) := by
  unfold innerFuel at fuel
  obtain ⟨g,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : f ≠ 0)
  have dec := ByteSequenceReadback.mdec_array ys I pre post a g data size allocation (by omega)
  rw [position] at dec
  simp only [melem,Element,Shape.dynamic,read,if_neg (Nat.not_lt.mpr offset),ite_true]
  exact dec

/-- Arbitrary actual recursive sequence, original index/base/cursor, with
codec-derived byte windows and a recursively DERIVED sufficient fuel bound. -/
theorem sequence_window {n : Nat} (xs : Seq Element n) (I : Input)
    (hp hs tp ts : List UInt8) (base i off a f : Nat)
    (headData : I.data = hp ++ (AbiEntry.assemble.go (Seq.parts xs) off).1 ++ hs)
    (tailData : I.data = tp ++ (AbiEntry.assemble.go (Seq.parts xs) off).2 ++ ts)
    (headPos : hp.length = base + i * 32) (tailPos : tp.length = base + off)
    (size : I.size ≤ lim) (allocation : I.free + (a + tailCost xs) ≤ lim) (fuel : fuelNeed xs ≤ f) :
    mseq I f Element base i n a = .ok (xs,a + tailCost xs) := by
  induction n generalizing hp tp i off a f with
  | zero => cases xs; cases f <;> rfl
  | succ n ih =>
    cases xs with
    | cons v xs => cases v with
      | array ys =>
        have l := Nat.le_max_left (innerFuel ys) (fuelNeed xs)
        have r := Nat.le_max_right (innerFuel ys) (fuelNeed xs)
        simp only [fuelNeed] at fuel
        obtain ⟨g,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : f ≠ 0)
        have offlim : off ≤ lim := by
          have h : tp.length ≤ I.size := by simp only [Input.size,tailData,List.length_append]; omega
          omega
        have read : load I.data (base + i * 32) = off := by
          rw [← headPos,headData,go_cons]
          simpa only [List.append_assoc] using CanonicalReadback.load_word hp
            ((AbiEntry.assemble.go (Seq.parts xs) (off + (Val.enc (.array ys)).length)).1 ++ hs) off
            (Nat.lt_of_le_of_lt offlim (by decide))
        have bnd : I.free + (a + innerCost ys) ≤ lim := by rw [tail_cons] at allocation; omega
        have dm := element_at ys I tp
          ((AbiEntry.assemble.go (Seq.parts xs) (off + (Val.enc (.array ys)).length)).2 ++ ts)
          base (base + i * 32) off a g
          (by simpa only [go_cons,List.append_assoc] using tailData) tailPos read offlim size bnd (by omega)
        have rest := ih xs (hp ++ AbiEntry.wordBytes off) (tp ++ Val.enc (.array ys))
          (i + 1) (off + (Val.enc (.array ys)).length) (a + innerCost ys) g
          (by simpa only [go_cons,List.append_assoc] using headData)
          (by simpa only [go_cons,List.append_assoc] using tailData)
          (by simp only [List.length_append,MixedPacket.word_length,headPos]; omega)
          (by simp only [List.length_append,tailPos]; omega)
          (by rw [tail_cons] at allocation; omega) (by omega)
        simp only [mseq,Element,Shape.headSize,dm,rest,tail_cons,Nat.add_assoc]

/-- Exact outer fixed constructor; its zero-count header guard is retained. -/
theorem mdec_fixed {n : Nat} (xs : Seq Element n) (I : Input) (pre post : List UInt8) (a f : Nat)
    (data : I.data = pre ++ Val.enc (.fixed xs) ++ post) (size : I.size ≤ lim)
    (header : pre.length + 31 < I.size)
    (allocation : I.free + (a + (n * 32 + tailCost xs)) ≤ lim) (fuel : fuelNeed xs + 1 ≤ f) :
    mdec I f (.fixed Element n) pre.length a = .ok (.fixed xs,a + (n * 32 + tailCost xs)) := by
  let h := (AbiEntry.assemble.go (Seq.parts xs) (n * 32)).1
  let t := (AbiEntry.assemble.go (Seq.parts xs) (n * 32)).2
  have layout : Val.enc (.fixed xs) = h ++ t := fixed_encoded xs
  have hlen : h.length = n * 32 := head_length xs _
  have region : pre.length + n * 32 ≤ I.size := by
    simp only [Input.size,data,List.length_append,fixed_length]; omega
  have count : n ≤ lim := by omega
  have outer : I.free + (a + n * 32) ≤ lim := by omega
  obtain ⟨g,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : f ≠ 0)
  have dec := sequence_window xs I pre (t ++ post) (pre ++ h) post pre.length 0 (n * 32) (a + n * 32) g
    (by simpa only [layout,List.append_assoc,h] using data)
    (by simpa only [layout,List.append_assoc,t] using data)
    (by omega) (by simp only [List.length_append,hlen]) size (by omega) (by omega)
  simp only [mdec,if_pos header,if_neg (Nat.not_lt.mpr count),alloc,StaticAggregateReadback.aligned,
    if_pos outer,Element,Shape.headSize,if_neg (Nat.not_lt.mpr region),dec,Nat.add_assoc]

/-- Actual outer dynamic array, with its OWN post-count relative-offset base. -/
theorem mdec_array {n : Nat} (xs : Seq Element n) (I : Input) (pre post : List UInt8) (a f : Nat)
    (data : I.data = pre ++ Val.enc (.array xs) ++ post) (size : I.size ≤ lim)
    (allocation : I.free + (a + (n * 32 + 32 + tailCost xs)) ≤ lim) (fuel : fuelNeed xs + 1 ≤ f) :
    mdec I f (.array Element) pre.length a = .ok (.array xs,a + (n * 32 + 32 + tailCost xs)) := by
  have count : n ≤ lim := by omega
  have nword : n < AbiEntry.W := Nat.lt_of_le_of_lt count (by decide)
  have layout0 : Val.enc (.array xs) = AbiEntry.wordBytes n ++ Val.enc (.fixed xs) := rfl
  have read : load I.data pre.length = n := by
    rw [data,layout0]
    simpa only [List.append_assoc] using CanonicalReadback.load_word pre (Val.enc (.fixed xs) ++ post) n nword
  have header : pre.length + 31 < I.size := by
    simp only [Input.size,data,layout0,List.length_append,MixedPacket.word_length]; omega
  have region : pre.length + 32 + n * 32 ≤ I.size := by
    simp only [Input.size,data,layout0,List.length_append,MixedPacket.word_length,fixed_length]; omega
  let h := (AbiEntry.assemble.go (Seq.parts xs) (n * 32)).1
  let t := (AbiEntry.assemble.go (Seq.parts xs) (n * 32)).2
  have layout : Val.enc (.array xs) = AbiEntry.wordBytes n ++ h ++ t := by rw [layout0,fixed_encoded]; simp only [h,t,List.append_assoc]
  have hlen : h.length = n * 32 := head_length xs _
  have outer : I.free + (a + (n * 32 + 32)) ≤ lim := by omega
  obtain ⟨g,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : f ≠ 0)
  have dec := sequence_window xs I (pre ++ AbiEntry.wordBytes n) (t ++ post)
    (pre ++ AbiEntry.wordBytes n ++ h) post (pre.length + 32) 0 (n * 32) (a + (n * 32 + 32)) g
    (by simpa only [layout,List.append_assoc,h] using data)
    (by simpa only [layout,List.append_assoc,t] using data)
    (by simp only [List.length_append,MixedPacket.word_length])
    (by simp only [List.length_append,MixedPacket.word_length,hlen]) size (by omega) (by omega)
  simp only [mdec,read,if_pos header,if_neg (Nat.not_lt.mpr count),alloc,CanonicalReadback.roundUp_words,
    if_pos outer,Element,Shape.headSize,if_neg (Nat.not_lt.mpr region)]
  unfold mdec.match_3
  rw [read,dec]
  simp only [Nat.add_assoc]

private theorem single_dynamic {s : AbiEntry.Shape} (v : AbiEntry.Val s) (selector post : List UInt8)
    (free f cost : Nat) (lazy : Bool) (dynamic : s.dynamic = true) (sel : selector.length = 4)
    (size : (input v selector post free).size ≤ lim) (fuel : 1 ≤ f)
    (decoded : mdec (input v selector post free) (f - 1) s 36 0 = .ok (v,cost)) :
    ∃ es : Entries (params s lazy),
      enter (input v selector post free) f (params s lazy) 0 0 = .ok (es,if lazy then 0 else cost) ∧
      entry (input v selector post free) f (params s lazy) = .ok es ∧
      bodyValues (input v selector post free) f (params s lazy) es 0 = .ok (values v) ∧
      verdict (input v selector post free) f (params s lazy) = .run (values v) := by
  let I := input v selector post free
  obtain ⟨g,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : f ≠ 0)
  have read : load I.data 4 = 32 := by
    simp only [I,input,encoded v dynamic]
    simpa only [sel,List.append_assoc] using CanonicalReadback.load_word selector (Val.enc v ++ post) 32 (by decide)
  have dm : melem I (g + 1) s 4 4 0 = .ok (v,cost) := by
    simp only [melem,dynamic,ite_true,read,if_neg (by decide : ¬ lim < 32)]
    exact decoded
  have ew : eager I (g + 1) s 0 = .ok v := by simp only [eager,Nat.add_zero,dm]
  obtain ⟨addr,len,cr,lv⟩ := eager_cref (I := I) size ew
  let p : Param := {shape := s,loc := if lazy then .calldata else .memory}
  obtain ⟨es,en,body⟩ := one_success p v I 0 0 (g + 1) cost addr len
    (by simpa only [Nat.zero_add] using dm) ew cr
  have heads : ¬ I.size < 4 + headsOf [p] := by
    simp only [headsOf,p,List.map_cons,List.map_nil,Shape.headsSize,dynamic_head s dynamic,
      Nat.add_zero,I,input,Input.size,encoded v dynamic,List.length_append,MixedPacket.word_length,sel]
    omega
  have ep : entry I (g + 1) [p] = .ok es := by rw [entry,if_neg heads,en]
  refine ⟨es,?_,ep,body,?_⟩
  · cases lazy <;> simpa only [p,Bool.false_eq_true,ite_false,ite_true,BEq.beq,reduceCtorEq,
      decide_false,decide_true,Nat.zero_add] using en
  · change verdict I (g + 1) [p] = _
    rw [verdict,ep]
    simp only [body,values]

/-- Actual recursive bytes[][] memory/calldata entry and indexed body identity.
The helper's decoder premise is DISCHARGED by mdec_array, not assumed. -/
theorem array_roundtrip {n : Nat} (xs : Seq Element n) (selector post : List UInt8) (free f : Nat) (lazy : Bool)
    (sel : selector.length = 4) (size : (input (.array xs) selector post free).size ≤ lim)
    (allocation : free + (n * 32 + 32 + tailCost xs) ≤ lim) (fuel : fuelNeed xs + 2 ≤ f) :
    ∃ es : Entries (params (.array Element) lazy),
      enter (input (.array xs) selector post free) f (params (.array Element) lazy) 0 0 =
        .ok (es,if lazy then 0 else n * 32 + 32 + tailCost xs) ∧
      entry (input (.array xs) selector post free) f (params (.array Element) lazy) = .ok es ∧
      bodyValues (input (.array xs) selector post free) f (params (.array Element) lazy) es 0 = .ok (values (.array xs)) ∧
      verdict (input (.array xs) selector post free) f (params (.array Element) lazy) = .run (values (.array xs)) := by
  have dec := mdec_array xs (input (.array xs) selector post free) (selector ++ AbiEntry.wordBytes 32) post 0 (f - 1)
    (by simp only [input,encoded (.array xs) rfl,List.append_assoc]) size
    (by simpa only [input,Nat.zero_add] using allocation) (by omega)
  simp only [List.length_append,sel,MixedPacket.word_length,Nat.zero_add] at dec
  exact single_dynamic (.array xs) selector post free f _ lazy rfl sel size (by omega) dec

/-- Actual recursive bytes[][n] fixed constructor. Header guard remains even
for the outer empty count; inner empty arrays retain their actual count words. -/
theorem fixed_roundtrip {n : Nat} (xs : Seq Element n) (selector post : List UInt8) (free f : Nat) (lazy : Bool)
    (sel : selector.length = 4) (size : (input (.fixed xs) selector post free).size ≤ lim)
    (header : 67 < (input (.fixed xs) selector post free).size)
    (allocation : free + (n * 32 + tailCost xs) ≤ lim) (fuel : fuelNeed xs + 2 ≤ f) :
    ∃ es : Entries (params (.fixed Element n) lazy),
      enter (input (.fixed xs) selector post free) f (params (.fixed Element n) lazy) 0 0 =
        .ok (es,if lazy then 0 else n * 32 + tailCost xs) ∧
      entry (input (.fixed xs) selector post free) f (params (.fixed Element n) lazy) = .ok es ∧
      bodyValues (input (.fixed xs) selector post free) f (params (.fixed Element n) lazy) es 0 = .ok (values (.fixed xs)) ∧
      verdict (input (.fixed xs) selector post free) f (params (.fixed Element n) lazy) = .run (values (.fixed xs)) := by
  have dec := mdec_fixed xs (input (.fixed xs) selector post free) (selector ++ AbiEntry.wordBytes 32) post 0 (f - 1)
    (by simp only [input,encoded (.fixed xs) rfl,List.append_assoc]) size
    (by simpa only [List.length_append,sel,MixedPacket.word_length] using header)
    (by simpa only [input,Nat.zero_add] using allocation) (by omega)
  simp only [List.length_append,sel,MixedPacket.word_length,Nat.zero_add] at dec
  exact single_dynamic (.fixed xs) selector post free f _ lazy rfl sel size (by omega) dec

theorem array_length {n : Nat} (xs : Seq Element n) :
    (Val.enc (.array xs)).length = 32 + (n * 32 + tailCost xs) := by
  change (AbiEntry.wordBytes n ++ Val.enc (.fixed xs)).length = _
  rw [List.length_append,MixedPacket.word_length,fixed_length]

theorem array_input_size {n : Nat} (xs : Seq Element n) (selector post : List UInt8) (free : Nat) :
    (input (.array xs) selector post free).size = selector.length + 64 + n * 32 + tailCost xs + post.length := by
  simp only [input,Input.size,encoded (.array xs) rfl,List.length_append,MixedPacket.word_length,array_length]
  omega

theorem fixed_input_size {n : Nat} (xs : Seq Element n) (selector post : List UInt8) (free : Nat) :
    (input (.fixed xs) selector post free).size = selector.length + 32 + n * 32 + tailCost xs + post.length := by
  simp only [input,Input.size,encoded (.fixed xs) rfl,List.length_append,MixedPacket.word_length,fixed_length]
  omega


/-- info: 'Solidity.Backend.AbiWorld.NestedByteReadback.inner_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms inner_length
/-- info: 'Solidity.Backend.AbiWorld.NestedByteReadback.go_cons' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms go_cons
/-- info: 'Solidity.Backend.AbiWorld.NestedByteReadback.tail_cons' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms tail_cons
/-- info: 'Solidity.Backend.AbiWorld.NestedByteReadback.head_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms head_length
/-- info: 'Solidity.Backend.AbiWorld.NestedByteReadback.head_fold' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms head_fold
/-- info: 'Solidity.Backend.AbiWorld.NestedByteReadback.fixed_encoded' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms fixed_encoded
/-- info: 'Solidity.Backend.AbiWorld.NestedByteReadback.fixed_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms fixed_length
/-- info: 'Solidity.Backend.AbiWorld.NestedByteReadback.element_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms element_at
/-- info: 'Solidity.Backend.AbiWorld.NestedByteReadback.sequence_window' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms sequence_window
/-- info: 'Solidity.Backend.AbiWorld.NestedByteReadback.mdec_fixed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms mdec_fixed
/-- info: 'Solidity.Backend.AbiWorld.NestedByteReadback.mdec_array' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms mdec_array
/-- info: 'Solidity.Backend.AbiWorld.NestedByteReadback.array_roundtrip' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms array_roundtrip
/-- info: 'Solidity.Backend.AbiWorld.NestedByteReadback.fixed_roundtrip' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms fixed_roundtrip
/-- info: 'Solidity.Backend.AbiWorld.NestedByteReadback.array_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms array_length
/-- info: 'Solidity.Backend.AbiWorld.NestedByteReadback.array_input_size' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms array_input_size
/-- info: 'Solidity.Backend.AbiWorld.NestedByteReadback.fixed_input_size' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms fixed_input_size

end Solidity.Backend.AbiWorld.NestedByteReadback
