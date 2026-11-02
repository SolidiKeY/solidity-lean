import Solidity.Backend.AbiWorld.RawEntryTransport

/-! Typed internal Seq composition through the ACTUAL existing mseq.
No evaluator, untyped sequence or default fuel increase. -/
namespace Solidity.Backend.AbiWorld.SeqPrefix
open AbiEntry RecursiveLayout

def append {e : AbiEntry.Shape} : {n m : Nat} → Seq e n → Seq e m → Seq e (n+m)
  | _, _, .nil, ys => (Nat.zero_add _).symm ▸ ys
  | _, _, .cons v xs, ys => (Nat.succ_add _ _).symm ▸ Seq.cons v (append xs ys)

theorem parts_cast {e : AbiEntry.Shape} {n m : Nat} (h : n = m) (xs : Seq e n) :
    Seq.parts (h ▸ xs) = Seq.parts xs := by cases h; rfl

theorem parts_append {e : AbiEntry.Shape} {n m : Nat} (xs : Seq e n) (ys : Seq e m) :
    Seq.parts (append xs ys) = Seq.parts xs ++ Seq.parts ys := by
  induction n with
  | zero => cases xs; simp only [append,parts_cast,Seq.parts,List.nil_append]
  | succ n ih =>
    cases xs with
    | cons v xs => simp only [append,parts_cast,Seq.parts,List.cons_append,ih]

theorem allocation_cast {e : AbiEntry.Shape} {n m : Nat} (h : n = m) (xs : Seq e n) :
    sequenceAllocation (h ▸ xs) = sequenceAllocation xs := by cases h; rfl

theorem allocation_append {e : AbiEntry.Shape} {n m : Nat} (xs : Seq e n) (ys : Seq e m) :
    sequenceAllocation (append xs ys) = sequenceAllocation xs + sequenceAllocation ys := by
  induction n with
  | zero => cases xs; simp only [append,allocation_cast,sequenceAllocation,Nat.zero_add]
  | succ n ih =>
    cases xs with
    | cons v xs => simp only [append,allocation_cast,sequenceAllocation,ih,Nat.add_assoc]

/-- Actual singleton ABI array encoding, with the element-head base AFTER
its length word and the real total count, not a second encoder. -/
theorem array_data {e : AbiEntry.Shape} {n m : Nat} (xs : Seq e n) (ys : Seq e m)
    (selector post : List UInt8) (free : Nat) :
    let I : Input := ⟨selector ++ encodeArgs (.cons (.array (append xs ys)) .nil) ++ post,free⟩
    I.data = (selector ++ AbiEntry.wordBytes 32 ++ AbiEntry.wordBytes (n+m)) ++
      (AbiEntry.assemble.go (Seq.parts (append xs ys)) ((n+m)*e.headSize)).1 ++
      (AbiEntry.assemble.go (Seq.parts (append xs ys)) ((n+m)*e.headSize)).2 ++ post := by
  simp only [encodeArgs,Vals.parts,Shape.dynamic,AbiEntry.assemble,List.foldl_cons,List.foldl_nil,ite_true,Nat.zero_add,
    AbiEntry.assemble.go,List.append_nil,Val.enc]
  simp only [fold_heads,sequence_heads,Nat.zero_add,List.append_assoc]

/-- A selected prefix of a real assembled sequence. The full n+m head extent
and preceding index i determine off; later values have no execution premise. -/
theorem window {e : AbiEntry.Shape} {n m : Nat} (xs : Seq e n) (ys : Seq e m)
    (I : Input) (hp lead post : List UInt8) (base i off a f : Nat)
    (headPos : hp.length = base + i * e.headSize)
    (offset : off = i * e.headSize + (n+m)*e.headSize + lead.length)
    (data : I.data = hp ++ (AbiEntry.assemble.go (Seq.parts (append xs ys)) off).1 ++ lead ++
      (AbiEntry.assemble.go (Seq.parts (append xs ys)) off).2 ++ post)
    (padding : 32 ≤ post.length) (size : I.size ≤ lim)
    (room : I.free + (a + sequenceAllocation xs) ≤ lim) (fuel : sequenceNeed xs ≤ f) :
    mseq I f e base i n a = .ok (xs,a + sequenceAllocation xs) := by
  let next := off + (AbiEntry.assemble.go (Seq.parts xs) off).2.length
  let sh := (AbiEntry.assemble.go (Seq.parts ys) next).1
  let st := (AbiEntry.assemble.go (Seq.parts ys) next).2
  apply RecursiveReadback.sequence f xs I hp (sh ++ lead ++ (AbiEntry.assemble.go (Seq.parts xs) off).2 ++ st ++ post)
    (hp ++ (AbiEntry.assemble.go (Seq.parts xs) off).1 ++ sh ++ lead) (st ++ post) base i off a
  · simpa only [parts_append,DynamicListReadback.go_append,List.append_assoc,next,sh,st] using data
  · simpa only [parts_append,DynamicListReadback.go_append,List.append_assoc,next,sh,st] using data
  · exact headPos
  · simp only [List.length_append,sh,go_head_length,sequence_heads,headPos]
    simp only [Nat.add_mul] at offset
    omega
  · simp only [List.length_append]; omega
  · simp only [List.length_append]; omega
  · exact size
  · exact room
  · exact fuel

/-- Actual typed mseq prefix identity at the original index/base/cursor. -/
theorem noninterference {e : AbiEntry.Shape} {n m : Nat} (xs : Seq e n) (ys zs : Seq e m)
    (I J : Input) (hp lead post : List UInt8) (base i off a f : Nat)
    (headPos : hp.length = base + i*e.headSize)
    (offset : off = i*e.headSize + (n+m)*e.headSize + lead.length)
    (dataI : I.data = hp ++ (AbiEntry.assemble.go (Seq.parts (append xs ys)) off).1 ++ lead ++
      (AbiEntry.assemble.go (Seq.parts (append xs ys)) off).2 ++ post)
    (dataJ : J.data = hp ++ (AbiEntry.assemble.go (Seq.parts (append xs zs)) off).1 ++ lead ++
      (AbiEntry.assemble.go (Seq.parts (append xs zs)) off).2 ++ post)
    (padding : 32 ≤ post.length) (sizeI : I.size ≤ lim) (sizeJ : J.size ≤ lim)
    (roomI : I.free+(a+sequenceAllocation xs) ≤ lim) (roomJ : J.free+(a+sequenceAllocation xs) ≤ lim)
    (fuel : sequenceNeed xs ≤ f) :
    mseq I f e base i n a = mseq J f e base i n a := by
  rw [window xs ys I hp lead post base i off a f headPos offset dataI padding sizeI roomI fuel,
    window xs zs J hp lead post base i off a f headPos offset dataJ padding sizeJ roomJ fuel]

/-- Recover the actual first melem from successful singleton execution;
this is an execution elimination law, not an assumed element decoder. -/
theorem singleton_element (I : Input) (f : Nat) (e : AbiEntry.Shape) (base i a c : Nat) (v : AbiEntry.Val e)
    (h : mseq I (f+1) e base i 1 a = .ok (.cons v .nil,c)) :
    melem I f e base (base+i*e.headSize) a = .ok (v,c) := by
  cases hm : melem I f e base (base+i*e.headSize) a with
  | error err => simp only [mseq,hm] at h; cases h
  | ok pair =>
    obtain ⟨w,b⟩ := pair
    simp only [mseq,hm] at h
    cases h
    rfl
end Solidity.Backend.AbiWorld.SeqPrefix
