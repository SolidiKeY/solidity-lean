import Solidity.Backend.AbiWorld.RecursiveLayout

/-! Canonical actual decoder readback for arbitrary intrinsic recursive values.
A trailing window of at least32 bytes is an auxiliary sufficient condition for
original lookahead guards (notably fixed0), NOT a source admission restriction.
No desired successful-run premise, alternate evaluator or semantics is defined. -/
namespace Solidity.Backend.AbiWorld.RecursiveReadback
open AbiEntry RecursiveLayout

/-- Exact existing array-constructor equation. Its actual mseq premise is
proved recursively below, never assumed at a headline endpoint. -/
theorem array_step (I : Input) (e : AbiEntry.Shape) (g p a n final : Nat) (xs : Seq e n)
    (read : load I.data p = n) (header : p + 31 < I.size) (count : n ≤ lim)
    (outer : I.free + (a + (n * 32 + 32)) ≤ lim) (region : p + 32 + n * e.headSize ≤ I.size)
    (dec : mseq I g e (p + 32) 0 n (a + (n * 32 + 32)) = .ok (xs,final)) :
    mdec I (g + 1) (.array e) p a = .ok (.array xs,final) := by
  simp only [mdec,read,if_pos header,if_neg (Nat.not_lt.mpr count),alloc,CanonicalReadback.roundUp_words,
    if_pos outer,if_neg (Nat.not_lt.mpr region)]
  unfold mdec.match_3
  rw [read,dec]

mutual
/-- Actual mdec, all constructors and dependent values. -/
theorem value (f : Nat) {s : AbiEntry.Shape} (v : AbiEntry.Val s) (I : Input) (pre post : List UInt8) (a : Nat)
    (data : I.data = pre ++ Val.enc v ++ post) (padding : 32 ≤ post.length) (size : I.size ≤ lim)
    (room : I.free + (a + allocation v) ≤ lim) (fuel : need v ≤ f) :
    mdec I f s pre.length a = .ok (v,a + allocation v) := by
  cases hf : f with
  | zero => cases v <;> simp only [need] at fuel <;> omega
  | succ g =>
    cases v with
    | word w =>
      have read : load I.data pre.length = w.val := by
        rw [data]
        exact CanonicalReadback.load_word pre post w.val w.lt
      simp only [mdec,read,w.valid,dite_true,allocation,Nat.add_zero]
    | bytes bs =>
      exact BytesReadback.mdec_bytes bs I pre (List.replicate (roundUp bs.length - bs.length) 0 ++ post) a (g + 1)
        (by simpa only [Val.enc,List.append_assoc] using data) room (by omega)
    | @array e n xs =>
      simp only [allocation,need] at room fuel ⊢
      have count : n ≤ lim := by omega
      have range : n < AbiEntry.W := Nat.lt_of_le_of_lt count (by decide)
      have read : load I.data pre.length = n := by
        rw [data]
        simpa only [Val.enc,List.append_assoc] using CanonicalReadback.load_word pre (AbiEntry.assemble (Seq.parts xs) ++ post) n range
      let off := heads (Seq.parts xs)
      let h := (AbiEntry.assemble.go (Seq.parts xs) off).1
      let t := (AbiEntry.assemble.go (Seq.parts xs) off).2
      have enc : Val.enc (.array xs) = AbiEntry.wordBytes n ++ h ++ t := by
        simp only [Val.enc,assembled,off,h,t,List.append_assoc]
      have hlen : h.length = n * e.headSize := by rw [go_head_length,sequence_heads]
      have header : pre.length + 31 < I.size := by simp only [Input.size,data,enc,List.length_append,MixedPacket.word_length]; omega
      have region : pre.length + 32 + n * e.headSize ≤ I.size := by
        simp only [Input.size,data,enc,List.length_append,MixedPacket.word_length,hlen]; omega
      have outer : I.free + (a + (n * 32 + 32)) ≤ lim := by omega
      have dec := sequence g xs I (pre ++ AbiEntry.wordBytes n) (t ++ post) (pre ++ AbiEntry.wordBytes n ++ h) post
        (pre.length + 32) 0 off (a + (n * 32 + 32))
        (by simpa only [enc,List.append_assoc,h] using data)
        (by simpa only [enc,List.append_assoc,t] using data)
        (by simp only [List.length_append,MixedPacket.word_length,Nat.zero_mul,Nat.add_zero])
        (by simp only [List.length_append,MixedPacket.word_length,hlen,off,sequence_heads,Nat.add_assoc])
        (by simp only [List.length_append]; omega) padding size (by omega) (by omega)
      have done := array_step I e g pre.length a n (a + (n * 32 + 32) + sequenceAllocation xs) xs
        read header count outer region dec
      simpa only [Nat.add_assoc] using done
    | @fixed e n xs =>
      simp only [allocation,need] at room fuel ⊢
      let off := heads (Seq.parts xs)
      let h := (AbiEntry.assemble.go (Seq.parts xs) off).1
      let t := (AbiEntry.assemble.go (Seq.parts xs) off).2
      have enc : Val.enc (.fixed xs) = h ++ t := assembled _
      have hlen : h.length = n * e.headSize := by rw [go_head_length,sequence_heads]
      have header : pre.length + 31 < I.size := by simp only [Input.size,data,List.length_append] at *; omega
      have region : pre.length + n * e.headSize ≤ I.size := by simp only [Input.size,data,enc,List.length_append,hlen]; omega
      have count : n ≤ lim := by omega
      have outer : I.free + (a + n * 32) ≤ lim := by omega
      have dec := sequence g xs I pre (t ++ post) (pre ++ h) post pre.length 0 off (a + n * 32)
        (by simpa only [enc,List.append_assoc,h] using data)
        (by simpa only [enc,List.append_assoc,t] using data)
        (by simp only [Nat.zero_mul,Nat.add_zero])
        (by simp only [List.length_append,hlen,off,sequence_heads])
        (by simp only [List.length_append]; omega) padding size (by omega) (by omega)
      simp only [mdec,if_pos header,if_neg (Nat.not_lt.mpr count),alloc,StaticAggregateReadback.aligned,
        if_pos outer,if_neg (Nat.not_lt.mpr region),dec,Nat.add_assoc]
    | @tuple ms vs =>
      simp only [allocation,need] at room fuel ⊢
      let off := heads (Vals.parts vs)
      let h := (AbiEntry.assemble.go (Vals.parts vs) off).1
      let t := (AbiEntry.assemble.go (Vals.parts vs) off).2
      have enc : Val.enc (.tuple vs) = h ++ t := assembled _
      have hlen : h.length = Shape.headsSize ms := by rw [go_head_length,member_heads]
      have region : pre.length + Shape.headsSize ms ≤ I.size := by simp only [Input.size,data,enc,List.length_append,hlen]; omega
      have outer : I.free + (a + ms.length * 32) ≤ lim := by omega
      have dec := members g vs I pre (t ++ post) (pre ++ h) post pre.length 0 off (a + ms.length * 32)
        (by simpa only [enc,List.append_assoc,h] using data)
        (by simpa only [enc,List.append_assoc,t] using data)
        (by omega) (by simp only [List.length_append,hlen,off,member_heads])
        (by simp only [List.length_append]; omega) padding size (by omega) (by omega)
      simp only [mdec,if_neg (Nat.not_lt.mpr region),alloc,StaticAggregateReadback.aligned,if_pos outer,dec,Nat.add_assoc]
termination_by f

/-- Actual melem from real canonical head/payload windows, retaining original
unsigned dynamic-offset validation and static in-place decoding. -/
theorem element (f : Nat) {s : AbiEntry.Shape} (v : AbiEntry.Val s) (I : Input)
    (hp hs tp ts : List UInt8) (base src off a : Nat)
    (headData : I.data = hp ++ (if s.dynamic then AbiEntry.wordBytes off else Val.enc v) ++ hs)
    (tailData : s.dynamic = true → I.data = tp ++ Val.enc v ++ ts)
    (headPos : hp.length = src) (tailPos : s.dynamic = true → tp.length = base + off)
    (headPad : 32 ≤ hs.length) (tailPad : 32 ≤ ts.length) (size : I.size ≤ lim)
    (room : I.free + (a + allocation v) ≤ lim) (fuel : need v + 1 ≤ f) :
    melem I f s base src a = .ok (v,a + allocation v) := by
  cases hf : f with
  | zero => omega
  | succ g =>
    cases hd : s.dynamic
    case false =>
      have dec := value g v I hp hs a (by simpa only [hd,Bool.false_eq_true,ite_false] using headData) headPad size room (by omega)
      rw [headPos] at dec
      simp only [melem,hd,Bool.false_eq_true,ite_false,dec]
    case true =>
      have d := tailData hd
      have p := tailPos hd
      have bound : off ≤ lim := by
        have h : tp.length ≤ I.size := by simp only [Input.size,d,List.length_append]; omega
        omega
      have read : load I.data src = off := by
        rw [← headPos,headData]
        simpa only [hd,ite_true] using CanonicalReadback.load_word hp hs off (Nat.lt_of_le_of_lt bound (by decide))
      have dec := value g v I tp ts a d tailPad size room (by omega)
      rw [p] at dec
      simp only [melem,hd,ite_true,read,if_neg (Nat.not_lt.mpr bound),dec]
termination_by f

theorem sequence (f : Nat) {e : AbiEntry.Shape} {n : Nat} (xs : Seq e n) (I : Input)
    (hp hs tp ts : List UInt8) (base i off a : Nat)
    (headData : I.data = hp ++ (AbiEntry.assemble.go (Seq.parts xs) off).1 ++ hs)
    (tailData : I.data = tp ++ (AbiEntry.assemble.go (Seq.parts xs) off).2 ++ ts)
    (headPos : hp.length = base + i * e.headSize) (tailPos : tp.length = base + off)
    (headPad : 32 ≤ hs.length) (tailPad : 32 ≤ ts.length) (size : I.size ≤ lim)
    (room : I.free + (a + sequenceAllocation xs) ≤ lim) (fuel : sequenceNeed xs ≤ f) :
    mseq I f e base i n a = .ok (xs,a + sequenceAllocation xs) := by
  cases xs with
  | nil => cases f <;> rfl
  | @cons _ n v xs =>
    simp only [sequenceAllocation,sequenceNeed] at room fuel ⊢
    cases hf : f with
    | zero => omega
    | succ g =>
      let off' := if e.dynamic then off + (Val.enc v).length else off
      let b := if e.dynamic then AbiEntry.wordBytes off else Val.enc v
      let t := if e.dynamic then Val.enc v else []
      have dec := element g v I hp ((AbiEntry.assemble.go (Seq.parts xs) off').1 ++ hs) tp
        ((AbiEntry.assemble.go (Seq.parts xs) off').2 ++ ts) base (base + i * e.headSize) off a
        (by simpa only [Seq.parts,go_head_cons,List.append_assoc,b,off'] using headData)
        (by intro hd; simpa only [Seq.parts,go_tail_cons,hd,ite_true,List.append_assoc,off',t] using tailData)
        headPos (by intro _; exact tailPos)
        (by simp only [List.length_append]; omega) (by simp only [List.length_append]; omega)
        size (by omega) (by have h := Nat.le_max_left (need v + 1) (sequenceNeed xs); omega)
      have rest := sequence g xs I (hp ++ b) hs (tp ++ t) ts base (i + 1) off' (a + allocation v)
        (by simpa only [Seq.parts,go_head_cons,List.append_assoc,b,off'] using headData)
        (by simpa only [Seq.parts,go_tail_cons,List.append_assoc,t,off'] using tailData)
        (by simp only [List.length_append,b,piece_length,headPos,Nat.add_mul,Nat.one_mul]; omega)
        (by cases hd : e.dynamic <;> simp only [List.length_append,t,off',hd,Bool.false_eq_true,ite_false,ite_true,List.length_nil,tailPos,Nat.add_zero] <;> omega)
        headPad tailPad size (by omega) (by have h := Nat.le_max_right (need v + 1) (sequenceNeed xs); omega)
      simp only [mseq,dec,rest,Nat.add_assoc]
termination_by f

theorem members (f : Nat) {ms : List AbiEntry.Shape} (vs : Vals ms) (I : Input)
    (hp hs tp ts : List UInt8) (base pos off a : Nat)
    (headData : I.data = hp ++ (AbiEntry.assemble.go (Vals.parts vs) off).1 ++ hs)
    (tailData : I.data = tp ++ (AbiEntry.assemble.go (Vals.parts vs) off).2 ++ ts)
    (headPos : hp.length = base + pos) (tailPos : tp.length = base + off)
    (headPad : 32 ≤ hs.length) (tailPad : 32 ≤ ts.length) (size : I.size ≤ lim)
    (room : I.free + (a + memberAllocation vs) ≤ lim) (fuel : memberNeed vs ≤ f) :
    mmembers I f ms base pos a = .ok (vs,a + memberAllocation vs) := by
  cases vs with
  | nil => cases f <;> rfl
  | @cons s ss v vs =>
    simp only [memberAllocation,memberNeed] at room fuel ⊢
    cases hf : f with
    | zero => omega
    | succ g =>
      let off' := if s.dynamic then off + (Val.enc v).length else off
      let b := if s.dynamic then AbiEntry.wordBytes off else Val.enc v
      let t := if s.dynamic then Val.enc v else []
      have dec := element g v I hp ((AbiEntry.assemble.go (Vals.parts vs) off').1 ++ hs) tp
        ((AbiEntry.assemble.go (Vals.parts vs) off').2 ++ ts) base (base + pos) off a
        (by simpa only [Vals.parts,go_head_cons,List.append_assoc,b,off'] using headData)
        (by intro hd; simpa only [Vals.parts,go_tail_cons,hd,ite_true,List.append_assoc,off',t] using tailData)
        headPos (by intro _; exact tailPos)
        (by simp only [List.length_append]; omega) (by simp only [List.length_append]; omega)
        size (by omega) (by have h := Nat.le_max_left (need v + 1) (memberNeed vs); omega)
      have rest := members g vs I (hp ++ b) hs (tp ++ t) ts base (pos + s.headSize) off' (a + allocation v)
        (by simpa only [Vals.parts,go_head_cons,List.append_assoc,b,off'] using headData)
        (by simpa only [Vals.parts,go_tail_cons,List.append_assoc,t,off'] using tailData)
        (by simp only [List.length_append,b,piece_length,headPos,Nat.add_assoc])
        (by cases hd : s.dynamic <;> simp only [List.length_append,t,off',hd,Bool.false_eq_true,ite_false,ite_true,List.length_nil,tailPos,Nat.add_zero] <;> omega)
        headPad tailPad size (by omega) (by have h := Nat.le_max_right (need v + 1) (memberNeed vs); omega)
      simp only [mmembers,dec,rest,Nat.add_assoc]
termination_by f
end

end Solidity.Backend.AbiWorld.RecursiveReadback
