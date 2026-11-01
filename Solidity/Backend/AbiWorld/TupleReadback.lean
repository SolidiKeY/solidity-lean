import Solidity.Backend.AbiWorld.BytesReadback
import Solidity.Backend.AbiWorld.ArrayPairPacket

/-! Canonical heterogeneous and multi-dynamic readback through the actual
indexed codec and decoder. These sufficient input/allocation/fuel lemmas do
not restrict the admitted profile and do not describe runtime byte emission. -/
namespace Solidity.Backend.AbiWorld.TupleReadback
open AbiEntry CanonicalReadback

abbrev UInt := PrimTy.uint.Denote
def cost (xs : List UInt) : Nat := xs.length * 32 + 32

/-- A real tuple head and tail suffice to invoke the existing array decoder
at an arbitrary cursor. No desired decoder outcome is a premise. -/
theorem array_window (xs : List UInt) (I : Input) (pos off a f : Nat)
    (post : List UInt8) (head : load I.data (4 + pos) = off)
    (offset : off ≤ lim)
    (tail : I.data.drop (4 + off) = AbiEntry.wordBytes xs.length ++
      xs.flatMap (fun v => AbiEntry.wordBytes v.val.toNat) ++ post)
    (position : 4 + off ≤ I.size)
    (allocation : I.free + (a + cost xs) ≤ lim) (fuel : xs.length + 4 ≤ f) :
    melem I f WordArrayPacket.Shape 4 (4 + pos) a =
      .ok (.array (WordArrayPacket.sequence xs),a + cost xs) := by
  obtain ⟨g,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : f ≠ 0)
  have decoded := mdec_tail xs I (4 + off) a g post tail position allocation (by omega)
  simp only [WordArrayPacket.Shape,melem,Shape.dynamic,head,
    if_neg (Nat.not_lt.mpr offset)]
  exact decoded

/-- A real scalar head uses the same original fuel and allocates nothing. -/
theorem scalar_window (v : UInt) (I : Input) (pos a f : Nat)
    (head : load I.data (4 + pos) = (WordArrayPacket.uintWord v).val) (fuel : 2 ≤ f) :
    melem I f MixedPacket.ScalarShape 4 (4 + pos) a =
      .ok (.word (WordArrayPacket.uintWord v),a) := by
  obtain ⟨g,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : f ≠ 0)
  obtain ⟨h,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : g ≠ 0)
  simp only [MixedPacket.ScalarShape,melem,Shape.dynamic,Bool.false_eq_true,ite_false,
    mdec_uint I v (4 + pos) a h head]

def mixedInput (xs : List UInt) (v : UInt) (selector post : List UInt8) (free : Nat) : Input :=
  ⟨selector ++ encodeArgs (MixedPacket.values xs v) ++ post,free⟩

def mixedParams : List Param :=
  [{shape := WordArrayPacket.Shape,loc := .memory},
   {shape := MixedPacket.ScalarShape,loc := .value}]

theorem mixed_size (xs : List UInt) (v : UInt) (selector post : List UInt8) (free : Nat) :
    (mixedInput xs v selector post free).size = selector.length + 96 + xs.length * 32 + post.length := by
  simp only [mixedInput,Input.size,List.length_append,MixedPacket.encoded_length]
  omega

theorem mixed_reads (xs : List UInt) (v : UInt) (selector post : List UInt8) (free : Nat)
    (sel : selector.length = 4) :
    load (mixedInput xs v selector post free).data 4 = 64 ∧
    load (mixedInput xs v selector post free).data 36 = (WordArrayPacket.uintWord v).val ∧
    (mixedInput xs v selector post free).data.drop 68 =
      AbiEntry.wordBytes xs.length ++ xs.flatMap (fun w => AbiEntry.wordBytes w.val.toNat) ++ post := by
  have r : v.val.toNat < AbiEntry.W := by
    rw [← WordArrayPacket.uintWord_value]; exact (WordArrayPacket.uintWord v).lt
  refine ⟨?_,?_,?_⟩
  · simpa only [mixedInput,MixedPacket.encoded_values,List.append_assoc,sel] using
      load_word selector (AbiEntry.wordBytes v.val.toNat ++ AbiEntry.wordBytes xs.length ++
        xs.flatMap (fun w => AbiEntry.wordBytes w.val.toNat) ++ post) 64 (by decide)
  · simpa only [mixedInput,MixedPacket.encoded_values,List.append_assoc,sel,
      List.length_append,MixedPacket.word_length,WordArrayPacket.uintWord_value] using
      load_word (selector ++ AbiEntry.wordBytes 64)
        (AbiEntry.wordBytes xs.length ++ xs.flatMap (fun w => AbiEntry.wordBytes w.val.toNat) ++ post)
        v.val.toNat r
  · have h : (selector ++ AbiEntry.wordBytes 64 ++ AbiEntry.wordBytes v.val.toNat).length = 68 := by
      simp only [List.length_append,MixedPacket.word_length,sel]
    simpa only [mixedInput,MixedPacket.encoded_values,List.append_assoc] using
      List.drop_left' h (l₂ := AbiEntry.wordBytes xs.length ++
        xs.flatMap (fun w => AbiEntry.wordBytes w.val.toNat) ++ post)

theorem mixed_decoders (xs : List UInt) (v : UInt) (selector post : List UInt8) (free f : Nat)
    (sel : selector.length = 4) (allocation : free + cost xs ≤ lim) (fuel : xs.length + 4 ≤ f) :
    melem (mixedInput xs v selector post free) f WordArrayPacket.Shape 4 4 0 =
      .ok (.array (WordArrayPacket.sequence xs),cost xs) ∧
    melem (mixedInput xs v selector post free) f MixedPacket.ScalarShape 4 36 (cost xs) =
      .ok (.word (WordArrayPacket.uintWord v),cost xs) := by
  have reads := mixed_reads xs v selector post free sel
  constructor
  · simpa only [Nat.add_zero,Nat.zero_add] using
      array_window xs (mixedInput xs v selector post free) 0 64 0 f post reads.1
        (by decide) reads.2.2 (by rw [mixed_size,sel]; omega)
        (by simpa only [mixedInput,Nat.zero_add] using allocation) fuel
  · exact scalar_window v (mixedInput xs v selector post free) 32 (cost xs) f reads.2.1 (by omega)

/-- Actual two-argument entry, exact allocation, indexed body identity. The
same fuel is reused by enter, rather than increased for the second argument. -/
theorem mixed_entry (xs : List UInt) (v : UInt) (selector post : List UInt8) (free f : Nat)
    (sel : selector.length = 4) (allocation : free + cost xs ≤ lim) (fuel : xs.length + 4 ≤ f) :
    enter (mixedInput xs v selector post free) f mixedParams 0 0 =
      .ok (.cons (.val (.array (WordArrayPacket.sequence xs)))
        (.cons (.val (.word (WordArrayPacket.uintWord v))) .nil),cost xs) ∧
    verdict (mixedInput xs v selector post free) f mixedParams = .run (MixedPacket.values xs v) := by
  have d := mixed_decoders xs v selector post free f sel allocation fuel
  have entered : enter (mixedInput xs v selector post free) f mixedParams 0 0 =
      .ok (.cons (.val (.array (WordArrayPacket.sequence xs)))
        (.cons (.val (.word (WordArrayPacket.uintWord v))) .nil),cost xs) := by
    simp only [mixedParams,enter,Nat.add_zero,WordArrayPacket.Shape,MixedPacket.ScalarShape,
      Shape.headSize,d.1,d.2,bind,Except.bind,pure,Except.pure]
  refine ⟨entered,?_⟩
  have heads : ¬ (mixedInput xs v selector post free).size < 4 + headsOf mixedParams := by
    simp only [headsOf,mixedParams,List.map_cons,List.map_nil,Shape.headsSize,
      WordArrayPacket.Shape,MixedPacket.ScalarShape,Shape.headSize,Nat.add_zero,mixed_size,sel]
    omega
  rw [verdict,entry,if_neg heads,entered]
  simp only [mixedParams,bodyValues,
    bind,Except.bind,pure,Except.pure,MixedPacket.values,MixedPacket.snocWord,WordArrayPacket.values]



/-- Canonical array references are validated against the actual input extent,
independently of the memory allocation cursor. -/
theorem reference_window (xs : List UInt) (I : Input) (pos off : Nat) (post : List UInt8)
    (head : load I.data (4 + pos) = off) (offset : off ≤ lim)
    (tail : I.data.drop (4 + off) = AbiEntry.wordBytes xs.length ++
      xs.flatMap (fun v => AbiEntry.wordBytes v.val.toNat) ++ post)
    (position : 4 + off ≤ I.size) (size : I.size ≤ lim) :
    cref I WordArrayPacket.Shape 4 pos = .ok (4 + off + 32,xs.length) := by
  have extent : 4 + off + 32 + xs.length * 32 ≤ I.size := by
    have lengths := congrArg List.length tail
    simp only [List.length_drop,List.length_append,MixedPacket.word_length,words_length,Input.size] at *
    omega
  have lenlim : xs.length ≤ lim := by omega
  have range : xs.length < AbiEntry.W := by
    have h : lim < AbiEntry.W := by decide
    omega
  have slice : (I.data.drop (4 + off)).take 32 = AbiEntry.wordBytes xs.length := by
    rw [tail]
    simpa only [MixedPacket.word_length,List.append_assoc] using
      (List.take_left (l₁ := AbiEntry.wordBytes xs.length)
        (l₂ := xs.flatMap (fun v => AbiEntry.wordBytes v.val.toNat) ++ post))
  have read := load_slice I.data (4 + off) xs.length slice range
  simp only [cref,WordArrayPacket.Shape,Shape.dynamic,head,
    if_neg (Nat.not_lt.mpr offset),if_pos (by omega : 4 + off + 31 < I.size),read,
    if_neg (Nat.not_lt.mpr lenlim),Shape.stride,Shape.headSize,
    if_neg (Nat.not_lt.mpr extent),ite_true]

def pairInput (xs ys : List UInt) (selector post : List UInt8) (free : Nat) : Input :=
  ⟨selector ++ encodeArgs (ArrayPairPacket.values xs ys) ++ post,free⟩

def arrayParam (lazy : Bool) : Param :=
  {shape := WordArrayPacket.Shape,loc := if lazy then .calldata else .memory}
def spent (lazy : Bool) (xs : List UInt) : Nat := if lazy then 0 else cost xs

def pairParams (left right : Bool) : List Param := [arrayParam left,arrayParam right]

def arrayEntry (lazy : Bool) (xs : List UInt) (off : Nat) : Entered WordArrayPacket.Shape :=
  if lazy then .ref (4 + off + 32) xs.length else .val (.array (WordArrayPacket.sequence xs))

def pairEntries (left right : Bool) (xs ys : List UInt) : Entries (pairParams left right) :=
  .cons (arrayEntry left xs 64) (.cons (arrayEntry right ys (ArrayPairPacket.secondOffset xs)) .nil)

theorem pair_size (xs ys : List UInt) (selector post : List UInt8) (free : Nat) :
    (pairInput xs ys selector post free).size = selector.length + 128 +
      (xs.length + ys.length) * 32 + post.length := by
  simp only [pairInput,Input.size,List.length_append,ArrayPairPacket.encoded_length]
  omega

/-- Both offsets and both full tails are derived from the existing codec. -/
theorem pair_reads (xs ys : List UInt) (selector post : List UInt8) (free : Nat)
    (sel : selector.length = 4) (size : (pairInput xs ys selector post free).size ≤ lim) :
    load (pairInput xs ys selector post free).data 4 = 64 ∧
    load (pairInput xs ys selector post free).data 36 = ArrayPairPacket.secondOffset xs ∧
    (pairInput xs ys selector post free).data.drop 68 =
      AbiEntry.wordBytes xs.length ++ xs.flatMap (fun v => AbiEntry.wordBytes v.val.toNat) ++
        (ArrayPairPacket.payload ys ++ post) ∧
    (pairInput xs ys selector post free).data.drop (4 + ArrayPairPacket.secondOffset xs) =
      AbiEntry.wordBytes ys.length ++ ys.flatMap (fun v => AbiEntry.wordBytes v.val.toNat) ++ post := by
  have range : ArrayPairPacket.secondOffset xs < AbiEntry.W := by
    have h : lim < AbiEntry.W := by decide
    rw [pair_size,sel] at size
    rw [ArrayPairPacket.second_offset]
    omega
  refine ⟨?_,?_,?_,?_⟩
  · simpa only [pairInput,ArrayPairPacket.encoded_values,List.append_assoc,sel] using
      load_word selector (AbiEntry.wordBytes (ArrayPairPacket.secondOffset xs) ++
        ArrayPairPacket.payload xs ++ ArrayPairPacket.payload ys ++ post) 64 (by decide)
  · simpa only [pairInput,ArrayPairPacket.encoded_values,List.append_assoc,sel,
      List.length_append,MixedPacket.word_length] using
      load_word (selector ++ AbiEntry.wordBytes 64)
        (ArrayPairPacket.payload xs ++ ArrayPairPacket.payload ys ++ post)
        (ArrayPairPacket.secondOffset xs) range
  · have h : (selector ++ AbiEntry.wordBytes 64 ++ AbiEntry.wordBytes (ArrayPairPacket.secondOffset xs)).length = 68 := by
      simp only [List.length_append,MixedPacket.word_length,sel]
    simpa only [pairInput,ArrayPairPacket.encoded_values,ArrayPairPacket.payload,MixedPacket.array_encoding,
      List.append_assoc] using List.drop_left' h (l₂ := ArrayPairPacket.payload xs ++ ArrayPairPacket.payload ys ++ post)
  · have h : (selector ++ AbiEntry.wordBytes 64 ++ AbiEntry.wordBytes (ArrayPairPacket.secondOffset xs) ++
        ArrayPairPacket.payload xs).length = 4 + ArrayPairPacket.secondOffset xs := by
      simp only [List.length_append,MixedPacket.word_length,sel,ArrayPairPacket.payload_length,
        ArrayPairPacket.second_offset]
      omega
    simpa only [pairInput,ArrayPairPacket.encoded_values,ArrayPairPacket.payload,MixedPacket.array_encoding,
      List.append_assoc] using List.drop_left' h (l₂ := ArrayPairPacket.payload ys ++ post)

/-- Uniform actual pair entry for all four memory/calldata combinations.
The input-size bound also bounds the SECOND offset; length<W is not used as
an offset bound. Allocation is a sufficient bound, not an admission rule. -/
theorem pair_entry (xs ys : List UInt) (selector post : List UInt8) (free f : Nat)
    (left right : Bool) (sel : selector.length = 4)
    (size : (pairInput xs ys selector post free).size ≤ lim)
    (allocation : free + (cost xs + cost ys) ≤ lim)
    (fuel : max xs.length ys.length + 4 ≤ f) :
    enter (pairInput xs ys selector post free) f (pairParams left right) 0 0 =
      .ok (pairEntries left right xs ys,spent left xs + spent right ys) ∧
    verdict (pairInput xs ys selector post free) f (pairParams left right) =
      .run (ArrayPairPacket.values xs ys) := by
  let I := pairInput xs ys selector post free
  have reads := pair_reads xs ys selector post free sel size
  have xpos : 4 + 64 ≤ I.size := by dsimp only [I]; rw [pair_size,sel]; omega
  have ypos : 4 + ArrayPairPacket.secondOffset xs ≤ I.size := by
    dsimp only [I]; rw [pair_size,sel,ArrayPairPacket.second_offset]; omega
  have off : ArrayPairPacket.secondOffset xs ≤ lim := by
    change I.size ≤ lim at size
    omega
  have fx : xs.length + 4 ≤ f := by have := Nat.le_max_left xs.length ys.length; omega
  have fy : ys.length + 4 ≤ f := by have := Nat.le_max_right xs.length ys.length; omega
  have ax : free + cost xs ≤ lim := by omega
  have ay : free + cost ys ≤ lim := by omega
  have d1 := array_window xs I 0 64 0 f (ArrayPairPacket.payload ys ++ post)
    reads.1 (by decide) reads.2.2.1 xpos (by simpa only [I,pairInput,Nat.zero_add] using ax) fx
  have d2 (a : Nat) (ha : a ≤ cost xs) := array_window ys I 32
    (ArrayPairPacket.secondOffset xs) a f post reads.2.1 off reads.2.2.2 ypos
    (by simp only [I,pairInput]; omega) fy
  have c1 := reference_window xs I 0 64 (ArrayPairPacket.payload ys ++ post)
    reads.1 (by decide) reads.2.2.1 xpos size
  have c2 := reference_window ys I 32 (ArrayPairPacket.secondOffset xs) post
    reads.2.1 off reads.2.2.2 ypos size
  have e1 : eager I f WordArrayPacket.Shape 0 = .ok (.array (WordArrayPacket.sequence xs)) := by
    simp only [eager,Nat.add_zero,d1,Nat.zero_add]
  have e2 : eager I f WordArrayPacket.Shape 32 = .ok (.array (WordArrayPacket.sequence ys)) := by
    simp only [eager,d2 0 (by omega),Nat.zero_add]
  have entered : enter I f (pairParams left right) 0 0 =
      .ok (pairEntries left right xs ys,spent left xs + spent right ys) := by
    cases left <;> cases right <;>
      simp only [pairParams,arrayParam,pairEntries,arrayEntry,spent,Bool.false_eq_true,ite_false,ite_true,
        enter,Nat.add_zero,Nat.zero_add,WordArrayPacket.Shape,Shape.headSize,
        d1,d2 0 (by omega),d2 (cost xs) (by omega),c1,c2,
        bind,Except.bind,pure,Except.pure]
  refine ⟨entered,?_⟩
  have heads : ¬ I.size < 4 + headsOf (pairParams left right) := by
    simp only [headsOf,pairParams,arrayParam,List.map_cons,List.map_nil,Shape.headsSize,
      WordArrayPacket.Shape,Shape.headSize,Nat.add_zero]
    omega
  dsimp only [I] at e1 e2
  rw [verdict,entry,if_neg heads,entered]
  cases left <;> cases right <;>
    simp only [pairEntries,arrayEntry,pairParams,arrayParam,Bool.false_eq_true,ite_false,ite_true,
      bodyValues,Nat.add_zero,Nat.zero_add,WordArrayPacket.Shape,Shape.headSize,e1,e2,
      bind,Except.bind,pure,Except.pure,ArrayPairPacket.values,WordArrayPacket.values,ArrayPairPacket.append]



def scalarParam : Param := {shape := MixedPacket.ScalarShape,loc := .value}
def mixedLocations (lazy : Bool) : List Param := [arrayParam lazy,scalarParam]
def mixedEntries (lazy : Bool) (xs : List UInt) (v : UInt) : Entries (mixedLocations lazy) :=
  .cons (arrayEntry lazy xs 64) (.cons (.val (.word (WordArrayPacket.uintWord v))) .nil)

theorem mixed_locations (xs : List UInt) (v : UInt) (selector post : List UInt8) (free f : Nat)
    (lazy : Bool) (sel : selector.length = 4)
    (size : (mixedInput xs v selector post free).size ≤ lim)
    (allocation : free + cost xs ≤ lim) (fuel : xs.length + 4 ≤ f) :
    enter (mixedInput xs v selector post free) f (mixedLocations lazy) 0 0 =
      .ok (mixedEntries lazy xs v,spent lazy xs) ∧
    verdict (mixedInput xs v selector post free) f (mixedLocations lazy) = .run (MixedPacket.values xs v) := by
  have reads := mixed_reads xs v selector post free sel
  have d := mixed_decoders xs v selector post free f sel allocation fuel
  have c := reference_window xs (mixedInput xs v selector post free) 0 64 post
    reads.1 (by decide) reads.2.2 (by rw [mixed_size,sel]; omega) size
  have scalar (a : Nat) := scalar_window v (mixedInput xs v selector post free) 32 a f reads.2.1 (by omega)
  have eagerArray : eager (mixedInput xs v selector post free) f WordArrayPacket.Shape 0 =
      .ok (.array (WordArrayPacket.sequence xs)) := by simp only [eager,Nat.add_zero,d.1]
  have entered : enter (mixedInput xs v selector post free) f (mixedLocations lazy) 0 0 =
      .ok (mixedEntries lazy xs v,spent lazy xs) := by
    cases lazy <;> simp only [mixedLocations,mixedEntries,arrayParam,arrayEntry,scalarParam,spent,
      Bool.false_eq_true,ite_false,ite_true,enter,Nat.add_zero,Nat.zero_add,WordArrayPacket.Shape,
      MixedPacket.ScalarShape,Shape.headSize,d.1,scalar,c,bind,Except.bind,pure,Except.pure]
  refine ⟨entered,?_⟩
  have heads : ¬ (mixedInput xs v selector post free).size < 4 + headsOf (mixedLocations lazy) := by
    simp only [headsOf,mixedLocations,arrayParam,scalarParam,List.map_cons,List.map_nil,
      Shape.headsSize,WordArrayPacket.Shape,MixedPacket.ScalarShape,Shape.headSize,Nat.add_zero,mixed_size,sel]
    omega
  rw [verdict,entry,if_neg heads,entered]
  cases lazy <;> simp only [mixedLocations,mixedEntries,arrayParam,arrayEntry,scalarParam,
    Bool.false_eq_true,ite_false,ite_true,bodyValues,Nat.add_zero,WordArrayPacket.Shape,
    MixedPacket.ScalarShape,Shape.headSize,eagerArray,bind,Except.bind,pure,Except.pure,
    MixedPacket.values,MixedPacket.snocWord,WordArrayPacket.values]

def reverseValues (xs : List UInt) (v : UInt) : Vals [MixedPacket.ScalarShape,WordArrayPacket.Shape] :=
  .cons (.word (WordArrayPacket.uintWord v)) (.cons (.array (WordArrayPacket.sequence xs)) .nil)

theorem reverse_encoded (xs : List UInt) (v : UInt) : encodeArgs (reverseValues xs v) =
    AbiEntry.wordBytes v.val.toNat ++ AbiEntry.wordBytes 64 ++ AbiEntry.wordBytes xs.length ++
      xs.flatMap (fun w => AbiEntry.wordBytes w.val.toNat) := by
  simp only [reverseValues,encodeArgs,Vals.parts,MixedPacket.ScalarShape,WordArrayPacket.Shape,
    Shape.dynamic,Val.enc,WordArrayPacket.uintWord_value]
  change AbiEntry.assemble [(false,AbiEntry.wordBytes v.val.toNat),
    (true,Val.enc (.array (WordArrayPacket.sequence xs)))] = _
  rw [MixedPacket.array_encoding]
  simp only [AbiEntry.assemble,List.foldl_cons,List.foldl_nil,Bool.false_eq_true,ite_false,ite_true,
    MixedPacket.word_length,Nat.zero_add,AbiEntry.assemble.go,List.append_nil,List.append_assoc]

def reverseInput (xs : List UInt) (v : UInt) (selector post : List UInt8) (free : Nat) : Input :=
  ⟨selector ++ encodeArgs (reverseValues xs v) ++ post,free⟩
def reverseParams (lazy : Bool) : List Param := [scalarParam,arrayParam lazy]
def reverseEntries (lazy : Bool) (xs : List UInt) (v : UInt) : Entries (reverseParams lazy) :=
  .cons (.val (.word (WordArrayPacket.uintWord v))) (.cons (arrayEntry lazy xs 64) .nil)

theorem reverse_size (xs : List UInt) (v : UInt) (selector post : List UInt8) (free : Nat) :
    (reverseInput xs v selector post free).size = selector.length + 96 + xs.length * 32 + post.length := by
  simp only [reverseInput,Input.size,reverse_encoded,List.length_append,MixedPacket.word_length,words_length]
  omega

theorem reverse_entry (xs : List UInt) (v : UInt) (selector post : List UInt8) (free f : Nat)
    (lazy : Bool) (sel : selector.length = 4)
    (size : (reverseInput xs v selector post free).size ≤ lim)
    (allocation : free + cost xs ≤ lim) (fuel : xs.length + 4 ≤ f) :
    enter (reverseInput xs v selector post free) f (reverseParams lazy) 0 0 =
      .ok (reverseEntries lazy xs v,spent lazy xs) ∧
    verdict (reverseInput xs v selector post free) f (reverseParams lazy) = .run (reverseValues xs v) := by
  let I := reverseInput xs v selector post free
  have range : v.val.toNat < AbiEntry.W := by
    rw [← WordArrayPacket.uintWord_value]; exact (WordArrayPacket.uintWord v).lt
  have scalarRead : load I.data 4 = (WordArrayPacket.uintWord v).val := by
    simpa only [I,reverseInput,reverse_encoded,WordArrayPacket.uintWord_value,List.append_assoc,sel] using
      load_word selector (AbiEntry.wordBytes 64 ++ AbiEntry.wordBytes xs.length ++
        xs.flatMap (fun w => AbiEntry.wordBytes w.val.toNat) ++ post) v.val.toNat range
  have arrayRead : load I.data 36 = 64 := by
    simpa only [I,reverseInput,reverse_encoded,List.append_assoc,sel,List.length_append,MixedPacket.word_length] using
      load_word (selector ++ AbiEntry.wordBytes v.val.toNat)
        (AbiEntry.wordBytes xs.length ++ xs.flatMap (fun w => AbiEntry.wordBytes w.val.toNat) ++ post) 64 (by decide)
  have tail : I.data.drop 68 = AbiEntry.wordBytes xs.length ++
      xs.flatMap (fun w => AbiEntry.wordBytes w.val.toNat) ++ post := by
    have h : (selector ++ AbiEntry.wordBytes v.val.toNat ++ AbiEntry.wordBytes 64).length = 68 := by
      simp only [List.length_append,MixedPacket.word_length,sel]
    simpa only [I,reverseInput,reverse_encoded,List.append_assoc] using List.drop_left' h
      (l₂ := AbiEntry.wordBytes xs.length ++ xs.flatMap (fun w => AbiEntry.wordBytes w.val.toNat) ++ post)
  have position : 4 + 64 ≤ I.size := by dsimp only [I]; rw [reverse_size,sel]; omega
  have d1 := scalar_window v I 0 0 f scalarRead (by omega)
  have d2 := array_window xs I 32 64 0 f post arrayRead (by decide) tail position
    (by simpa only [I,reverseInput,Nat.zero_add] using allocation) fuel
  have c := reference_window xs I 32 64 post arrayRead (by decide) tail position size
  have e : eager I f WordArrayPacket.Shape 32 = .ok (.array (WordArrayPacket.sequence xs)) := by
    simp only [eager,d2]
  have entered : enter I f (reverseParams lazy) 0 0 = .ok (reverseEntries lazy xs v,spent lazy xs) := by
    cases lazy <;> simp only [reverseParams,reverseEntries,arrayParam,arrayEntry,scalarParam,spent,
      Bool.false_eq_true,ite_false,ite_true,enter,Nat.add_zero,Nat.zero_add,WordArrayPacket.Shape,
      MixedPacket.ScalarShape,Shape.headSize,d1,d2,c,bind,Except.bind,pure,Except.pure]
  refine ⟨entered,?_⟩
  have heads : ¬ I.size < 4 + headsOf (reverseParams lazy) := by
    simp only [headsOf,reverseParams,scalarParam,arrayParam,List.map_cons,List.map_nil,Shape.headsSize,
      MixedPacket.ScalarShape,WordArrayPacket.Shape,Shape.headSize,Nat.add_zero]
    dsimp only [I]; rw [reverse_size,sel]; omega
  dsimp only [I] at e
  rw [verdict,entry,if_neg heads,entered]
  cases lazy <;> simp only [reverseParams,reverseEntries,arrayParam,arrayEntry,scalarParam,
    Bool.false_eq_true,ite_false,ite_true,bodyValues,Nat.add_zero,Nat.zero_add,MixedPacket.ScalarShape,
    WordArrayPacket.Shape,Shape.headSize,e,bind,Except.bind,pure,Except.pure,reverseValues]


/-- info: 'Solidity.Backend.AbiWorld.TupleReadback.array_window' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms array_window
/-- info: 'Solidity.Backend.AbiWorld.TupleReadback.scalar_window' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms scalar_window
/-- info: 'Solidity.Backend.AbiWorld.TupleReadback.mixed_reads' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms mixed_reads
/-- info: 'Solidity.Backend.AbiWorld.TupleReadback.mixed_decoders' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms mixed_decoders
/-- info: 'Solidity.Backend.AbiWorld.TupleReadback.mixed_entry' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms mixed_entry
/-- info: 'Solidity.Backend.AbiWorld.TupleReadback.reference_window' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms reference_window
/-- info: 'Solidity.Backend.AbiWorld.TupleReadback.pair_reads' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms pair_reads
/-- info: 'Solidity.Backend.AbiWorld.TupleReadback.pair_entry' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms pair_entry
/-- info: 'Solidity.Backend.AbiWorld.TupleReadback.mixed_locations' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms mixed_locations
/-- info: 'Solidity.Backend.AbiWorld.TupleReadback.reverse_encoded' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms reverse_encoded
/-- info: 'Solidity.Backend.AbiWorld.TupleReadback.reverse_entry' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms reverse_entry
end Solidity.Backend.AbiWorld.TupleReadback
