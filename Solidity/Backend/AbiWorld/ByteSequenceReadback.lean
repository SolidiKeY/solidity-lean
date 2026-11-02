import Solidity.Backend.AbiWorld.DynamicAggregateReadback

/-! Canonical actual Seq.bytes consumers. All layout, validation, allocation
and fuel are the existing AbiEntry definitions. No alternate decoder, admission
predicate or unknown-memory runtime encoder is supplied. -/
namespace Solidity.Backend.AbiWorld.ByteSequenceReadback
open AbiEntry DynamicListReadback

/-- Actual ordered byte-object tail extent, not a new allocator. -/
def tailBytes {n : Nat} (xs : Seq .bytes n) : Nat :=
  (AbiEntry.assemble.go (Seq.parts xs) 0).2.length

theorem go_cons {n : Nat} (bs : List UInt8) (xs : Seq .bytes n) (off : Nat) :
    AbiEntry.assemble.go (Seq.parts (.cons (.bytes bs) xs)) off =
      (AbiEntry.wordBytes off ++ (AbiEntry.assemble.go (Seq.parts xs) (off + (Val.enc (.bytes bs)).length)).1,
       Val.enc (.bytes bs) ++ (AbiEntry.assemble.go (Seq.parts xs) (off + (Val.enc (.bytes bs)).length)).2) := rfl

theorem tail_cons {n : Nat} (bs : List UInt8) (xs : Seq .bytes n) :
    tailBytes (.cons (.bytes bs) xs) = BytesReadback.allocationBytes bs + tailBytes xs := by
  simp only [tailBytes,go_cons,List.length_append]
  rw [tails_independent _ _ 0]
  exact congrArg (fun n => n + (AbiEntry.assemble.go (Seq.parts xs) 0).2.length)
    (BytesArrayReadback.byte_payload_length bs)

theorem head_length {n : Nat} (xs : Seq .bytes n) (off : Nat) :
    (AbiEntry.assemble.go (Seq.parts xs) off).1.length = n * 32 := by
  induction n generalizing off with
  | zero => cases xs; rfl
  | succ n ih =>
    cases xs with
    | cons v xs => cases v with
      | bytes bs => simp only [go_cons,List.length_append,MixedPacket.word_length,ih,Nat.succ_mul]; omega

theorem head_fold {n : Nat} (xs : Seq .bytes n) (a : Nat) :
    (Seq.parts xs).foldl (fun acc (d,b) => acc + if d then 32 else b.length) a = a + n * 32 := by
  induction n generalizing a with
  | zero => cases xs; simp only [Seq.parts,List.foldl_nil,Nat.zero_mul,Nat.add_zero]
  | succ n ih =>
    cases xs with
    | cons v xs => cases v with
      | bytes bs => simp only [Seq.parts,Shape.dynamic,List.foldl_cons,ite_true,ih,Nat.succ_mul]; omega

theorem fixed_encoded {n : Nat} (xs : Seq .bytes n) :
    Val.enc (.fixed xs) = (AbiEntry.assemble.go (Seq.parts xs) (n * 32)).1 ++
      (AbiEntry.assemble.go (Seq.parts xs) (n * 32)).2 := by
  simp only [Val.enc,AbiEntry.assemble,head_fold xs 0,Nat.zero_add]

theorem fixed_length {n : Nat} (xs : Seq .bytes n) :
    (Val.enc (.fixed xs)).length = n * 32 + tailBytes xs := by
  rw [fixed_encoded,List.length_append,head_length,tails_independent _ _ 0]
  rfl

/-- Empty sequence execution uses no fuel or allocation; its enclosing
fixed/array constructor still performs its OWN original header/alloc checks. -/
theorem zero (I : Input) (f base i a : Nat) :
    mseq I f .bytes base i 0 a = .ok (.nil,a) := by cases f <;> rfl

/-- Arbitrary remaining count and original element index. The exact head and
tail byte windows come from actual Seq.parts/assemble.go, not a successful-run
premise. Offsets are relative to base; original fuel decreases per element. -/
theorem sequence_window {n : Nat} (xs : Seq .bytes n) (I : Input)
    (hp hs tp ts : List UInt8) (base i off a f : Nat)
    (headData : I.data = hp ++ (AbiEntry.assemble.go (Seq.parts xs) off).1 ++ hs)
    (tailData : I.data = tp ++ (AbiEntry.assemble.go (Seq.parts xs) off).2 ++ ts)
    (headPos : hp.length = base + i * 32) (tailPos : tp.length = base + off)
    (size : I.size ≤ lim) (allocation : I.free + (a + tailBytes xs) ≤ lim) (fuel : n + 2 ≤ f) :
    mseq I f .bytes base i n a = .ok (xs,a + tailBytes xs) := by
  induction n generalizing hp tp i off a f with
  | zero => cases xs; cases f <;> rfl
  | succ n ih =>
    cases xs with
    | cons v xs => cases v with
      | bytes bs =>
        obtain ⟨g,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : f ≠ 0)
        let b := BytesReadback.allocationBytes bs
        have offlim : off ≤ lim := by
          have h : tp.length ≤ I.size := by simp only [Input.size,tailData,List.length_append]; omega
          omega
        have read : load I.data (base + i * 32) = off := by
          rw [← headPos,headData,go_cons]
          simpa only [List.append_assoc] using CanonicalReadback.load_word hp
            ((AbiEntry.assemble.go (Seq.parts xs) (off + (Val.enc (.bytes bs)).length)).1 ++ hs) off
            (Nat.lt_of_le_of_lt offlim (by decide))
        have bnd : I.free + (a + b) ≤ lim := by rw [tail_cons] at allocation; omega
        have dm := DynamicAggregateReadback.bytes_at bs I tp
          ((AbiEntry.assemble.go (Seq.parts xs) (off + (Val.enc (.bytes bs)).length)).2 ++ ts)
          base (base + i * 32) off a g
          (by simpa only [go_cons,List.append_assoc] using tailData) tailPos read offlim bnd (by omega)
        have rest := ih xs (hp ++ AbiEntry.wordBytes off) (tp ++ Val.enc (.bytes bs))
          (i + 1) (off + (Val.enc (.bytes bs)).length) (a + b) g
          (by simpa only [go_cons,List.append_assoc] using headData)
          (by simpa only [go_cons,List.append_assoc] using tailData)
          (by simp only [List.length_append,MixedPacket.word_length,headPos]; omega)
          (by simp only [List.length_append,tailPos]; omega)
          (by rw [tail_cons] at allocation; omega) (by omega)
        simp only [mseq,Shape.headSize,dm,rest,tail_cons,b,Nat.add_assoc]

/-- Canonical fixed array of dynamic bytes. Explicit original header guard
is retained even for n=0: empty encoding alone cannot discharge it. -/
theorem mdec_fixed {n : Nat} (xs : Seq .bytes n) (I : Input) (pre post : List UInt8) (a f : Nat)
    (data : I.data = pre ++ Val.enc (.fixed xs) ++ post) (size : I.size ≤ lim)
    (header : pre.length + 31 < I.size)
    (allocation : I.free + (a + (n * 32 + tailBytes xs)) ≤ lim) (fuel : n + 3 ≤ f) :
    mdec I f (.fixed .bytes n) pre.length a = .ok (.fixed xs,a + (n * 32 + tailBytes xs)) := by
  let h := (AbiEntry.assemble.go (Seq.parts xs) (n * 32)).1
  let t := (AbiEntry.assemble.go (Seq.parts xs) (n * 32)).2
  have layout : Val.enc (.fixed xs) = h ++ t := fixed_encoded xs
  have hlen : h.length = n * 32 := head_length xs _
  have region : pre.length + n * 32 ≤ I.size := by
    simp only [Input.size,data,List.length_append,fixed_length]
    omega
  have count : n ≤ lim := by omega
  have outer : I.free + (a + n * 32) ≤ lim := by omega
  obtain ⟨g,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : f ≠ 0)
  have decoded := sequence_window xs I pre (t ++ post) (pre ++ h) post pre.length 0 (n * 32)
    (a + n * 32) g
    (by simpa only [layout,List.append_assoc,h] using data)
    (by simpa only [layout,List.append_assoc,t] using data)
    (by omega) (by simp only [List.length_append,hlen]) size (by omega) (by omega)
  simp only [mdec,if_pos header,if_neg (Nat.not_lt.mpr count),alloc,StaticAggregateReadback.aligned,
    if_pos outer,Shape.headSize,if_neg (Nat.not_lt.mpr region),decoded,Nat.add_assoc]

/-- Canonical dynamic bytes array. The element head/offset base is AFTER the
count word. Actual outer count allocation is n*32+32 plus every byte object. -/
theorem mdec_array {n : Nat} (xs : Seq .bytes n) (I : Input) (pre post : List UInt8) (a f : Nat)
    (data : I.data = pre ++ Val.enc (.array xs) ++ post) (size : I.size ≤ lim)
    (allocation : I.free + (a + (n * 32 + 32 + tailBytes xs)) ≤ lim) (fuel : n + 3 ≤ f) :
    mdec I f (.array .bytes) pre.length a = .ok (.array xs,a + (n * 32 + 32 + tailBytes xs)) := by
  have count : n ≤ lim := by omega
  have nword : n < AbiEntry.W := Nat.lt_of_le_of_lt count (by decide)
  have read : load I.data pre.length = n := by
    rw [data]
    simpa only [Val.enc,List.append_assoc] using CanonicalReadback.load_word pre
      (AbiEntry.assemble (Seq.parts xs) ++ post) n nword
  have header : pre.length + 31 < I.size := by
    simp only [Input.size,data,Val.enc,List.length_append,MixedPacket.word_length]; omega
  have region : pre.length + 32 + n * 32 ≤ I.size := by
    change I.data.length ≤ lim at size
    have length : (Val.enc (.array xs)).length = 32 + (n * 32 + tailBytes xs) := by
      change (AbiEntry.wordBytes n ++ Val.enc (.fixed xs)).length = _
      rw [List.length_append,MixedPacket.word_length,fixed_length]
    simp only [Input.size,data,List.length_append,length]; omega
  let h := (AbiEntry.assemble.go (Seq.parts xs) (n * 32)).1
  let t := (AbiEntry.assemble.go (Seq.parts xs) (n * 32)).2
  have layout : Val.enc (.array xs) = AbiEntry.wordBytes n ++ h ++ t := by
    change AbiEntry.wordBytes n ++ Val.enc (.fixed xs) = _
    rw [fixed_encoded]; simp only [h,t,List.append_assoc]
  have hlen : h.length = n * 32 := head_length xs _
  obtain ⟨g,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : f ≠ 0)
  have outer : I.free + (a + (n * 32 + 32)) ≤ lim := by omega
  have decoded := sequence_window xs I (pre ++ AbiEntry.wordBytes n) (t ++ post)
    (pre ++ AbiEntry.wordBytes n ++ h) post (pre.length + 32) 0 (n * 32) (a + (n * 32 + 32)) g
    (by simpa only [layout,List.append_assoc,h] using data)
    (by simpa only [layout,List.append_assoc,t] using data)
    (by simp only [List.length_append,MixedPacket.word_length])
    (by simp only [List.length_append,MixedPacket.word_length,hlen])
    size (by omega) (by omega)
  simp only [mdec,read,if_pos header,if_neg (Nat.not_lt.mpr count),alloc,
    CanonicalReadback.roundUp_words,if_pos outer,Shape.headSize,if_neg (Nat.not_lt.mpr region)]
  unfold mdec.match_3
  rw [read,decoded]
  simp only [Nat.add_assoc]

def values {s : AbiEntry.Shape} (v : AbiEntry.Val s) : Vals [s] := .cons v .nil

def params (s : AbiEntry.Shape) (lazy : Bool) : List Param :=
  [{shape := s,loc := if lazy then .calldata else .memory}]

def input {s : AbiEntry.Shape} (v : AbiEntry.Val s) (selector post : List UInt8) (free : Nat) : Input :=
  ⟨selector ++ encodeArgs (values v) ++ post,free⟩

theorem encoded {s : AbiEntry.Shape} (v : AbiEntry.Val s) (dynamic : s.dynamic = true) :
    encodeArgs (values v) = AbiEntry.wordBytes 32 ++ Val.enc v := by
  simp only [values,encodeArgs,Vals.parts,dynamic,AbiEntry.assemble,List.foldl_cons,List.foldl_nil,
    ite_true,Nat.zero_add,AbiEntry.assemble.go,List.append_nil]

theorem dynamic_head (s : AbiEntry.Shape) (dynamic : s.dynamic = true) : s.headSize = 32 := by
  cases s <;> simp only [Shape.dynamic] at dynamic <;> simp only [Shape.headSize,dynamic,ite_true]

/-- Internal composition only. The actual mdec premise is discharged by BOTH
constructor endpoints below, not counted as a generic shape correctness law. -/
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

/-- Actual canonical bytes[] entry/body identity, arbitrary selector/suffix
and input/free bounds, exact outer+inner allocation and ORIGINAL fuel. -/
theorem array_roundtrip {n : Nat} (xs : Seq .bytes n) (selector post : List UInt8) (free f : Nat) (lazy : Bool)
    (sel : selector.length = 4) (size : (input (.array xs) selector post free).size ≤ lim)
    (allocation : free + (n * 32 + 32 + tailBytes xs) ≤ lim) (fuel : n + 4 ≤ f) :
    ∃ es : Entries (params (.array .bytes) lazy),
      enter (input (.array xs) selector post free) f (params (.array .bytes) lazy) 0 0 =
        .ok (es,if lazy then 0 else n * 32 + 32 + tailBytes xs) ∧
      entry (input (.array xs) selector post free) f (params (.array .bytes) lazy) = .ok es ∧
      bodyValues (input (.array xs) selector post free) f (params (.array .bytes) lazy) es 0 = .ok (values (.array xs)) ∧
      verdict (input (.array xs) selector post free) f (params (.array .bytes) lazy) = .run (values (.array xs)) := by
  have dec := mdec_array xs (input (.array xs) selector post free) (selector ++ AbiEntry.wordBytes 32) post 0 (f - 1)
    (by simp only [input,encoded (.array xs) rfl,List.append_assoc]) size
    (by simpa only [input,Nat.zero_add] using allocation) (by omega)
  simp only [List.length_append,sel,MixedPacket.word_length,Nat.zero_add] at dec
  exact single_dynamic (.array xs) selector post free f _ lazy rfl sel size (by omega) dec

/-- Actual canonical bytes[n] entry/body identity. The extra fixed-header
premise is precisely the original zero-count guard, never silently waived. -/
theorem fixed_roundtrip {n : Nat} (xs : Seq .bytes n) (selector post : List UInt8) (free f : Nat) (lazy : Bool)
    (sel : selector.length = 4) (size : (input (.fixed xs) selector post free).size ≤ lim)
    (header : 67 < (input (.fixed xs) selector post free).size)
    (allocation : free + (n * 32 + tailBytes xs) ≤ lim) (fuel : n + 4 ≤ f) :
    ∃ es : Entries (params (.fixed .bytes n) lazy),
      enter (input (.fixed xs) selector post free) f (params (.fixed .bytes n) lazy) 0 0 =
        .ok (es,if lazy then 0 else n * 32 + tailBytes xs) ∧
      entry (input (.fixed xs) selector post free) f (params (.fixed .bytes n) lazy) = .ok es ∧
      bodyValues (input (.fixed xs) selector post free) f (params (.fixed .bytes n) lazy) es 0 = .ok (values (.fixed xs)) ∧
      verdict (input (.fixed xs) selector post free) f (params (.fixed .bytes n) lazy) = .run (values (.fixed xs)) := by
  have dec := mdec_fixed xs (input (.fixed xs) selector post free) (selector ++ AbiEntry.wordBytes 32) post 0 (f - 1)
    (by simp only [input,encoded (.fixed xs) rfl,List.append_assoc]) size
    (by simpa only [List.length_append,sel,MixedPacket.word_length] using header)
    (by simpa only [input,Nat.zero_add] using allocation) (by omega)
  simp only [List.length_append,sel,MixedPacket.word_length,Nat.zero_add] at dec
  exact single_dynamic (.fixed xs) selector post free f _ lazy rfl sel size (by omega) dec

theorem array_length {n : Nat} (xs : Seq .bytes n) :
    (Val.enc (.array xs)).length = 32 + (n * 32 + tailBytes xs) := by
  change (AbiEntry.wordBytes n ++ Val.enc (.fixed xs)).length = _
  rw [List.length_append,MixedPacket.word_length,fixed_length]

theorem array_input_size {n : Nat} (xs : Seq .bytes n) (selector post : List UInt8) (free : Nat) :
    (input (.array xs) selector post free).size = selector.length + 64 + n * 32 + tailBytes xs + post.length := by
  simp only [input,Input.size,encoded (.array xs) rfl,List.length_append,MixedPacket.word_length,array_length]
  omega

theorem fixed_input_size {n : Nat} (xs : Seq .bytes n) (selector post : List UInt8) (free : Nat) :
    (input (.fixed xs) selector post free).size = selector.length + 32 + n * 32 + tailBytes xs + post.length := by
  simp only [input,Input.size,encoded (.fixed xs) rfl,List.length_append,MixedPacket.word_length,fixed_length]
  omega


/-- info: 'Solidity.Backend.AbiWorld.ByteSequenceReadback.go_cons' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms go_cons
/-- info: 'Solidity.Backend.AbiWorld.ByteSequenceReadback.tail_cons' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms tail_cons
/-- info: 'Solidity.Backend.AbiWorld.ByteSequenceReadback.head_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms head_length
/-- info: 'Solidity.Backend.AbiWorld.ByteSequenceReadback.head_fold' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms head_fold
/-- info: 'Solidity.Backend.AbiWorld.ByteSequenceReadback.fixed_encoded' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms fixed_encoded
/-- info: 'Solidity.Backend.AbiWorld.ByteSequenceReadback.fixed_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms fixed_length
/-- info: 'Solidity.Backend.AbiWorld.ByteSequenceReadback.zero' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms zero
/-- info: 'Solidity.Backend.AbiWorld.ByteSequenceReadback.sequence_window' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms sequence_window
/-- info: 'Solidity.Backend.AbiWorld.ByteSequenceReadback.mdec_fixed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms mdec_fixed
/-- info: 'Solidity.Backend.AbiWorld.ByteSequenceReadback.mdec_array' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms mdec_array
/-- info: 'Solidity.Backend.AbiWorld.ByteSequenceReadback.encoded' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms encoded
/-- info: 'Solidity.Backend.AbiWorld.ByteSequenceReadback.dynamic_head' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms dynamic_head
/-- info: 'Solidity.Backend.AbiWorld.ByteSequenceReadback.array_roundtrip' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms array_roundtrip
/-- info: 'Solidity.Backend.AbiWorld.ByteSequenceReadback.fixed_roundtrip' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms fixed_roundtrip
/-- info: 'Solidity.Backend.AbiWorld.ByteSequenceReadback.array_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms array_length
/-- info: 'Solidity.Backend.AbiWorld.ByteSequenceReadback.array_input_size' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms array_input_size
/-- info: 'Solidity.Backend.AbiWorld.ByteSequenceReadback.fixed_input_size' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms fixed_input_size

end Solidity.Backend.AbiWorld.ByteSequenceReadback
