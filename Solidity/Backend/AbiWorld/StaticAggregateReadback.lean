import Solidity.Backend.AbiWorld.WordListReadback

/-! Actual static aggregate decoder consumers. These prove existing mdec /
mmembers equations, not an alternate evaluator or source-profile expansion. -/
namespace Solidity.Backend.AbiWorld.StaticAggregateReadback
open AbiEntry WordListReadback

theorem word_at (I : Input) (k : Kind) (w : Word k) (base src a f : Nat)
    (read : load I.data src = w.val) (fuel : 2 ≤ f) :
    melem I f (.word k) base src a = .ok (.word w,a) := by
  obtain ⟨g,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : f ≠ 0)
  obtain ⟨h,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : g ≠ 0)
  simp only [melem,Shape.dynamic,Bool.false_eq_true,ite_false,mdec,read,w.valid,dite_true]

/-- Unlike enter/body parameter recursion, mmembers consumes the ORIGINAL
member recursion fuel. Actual head position/cursor and ordered values retained. -/
theorem members (ss : List AbiEntry.Shape) (vs : Vals ss) (I : Input) (pre post : List UInt8)
    (base pos a f : Nat) (words : WordShapes ss) (data : I.data = pre ++ encodeArgs vs ++ post)
    (position : pre.length = base + pos) (fuel : ss.length + 2 ≤ f) :
    mmembers I f ss base pos a = .ok (vs,a) := by
  induction ss generalizing pre pos f with
  | nil => cases vs; cases f <;> rfl
  | cons s ss ih =>
    obtain ⟨k,rfl⟩ := words s List.mem_cons_self
    cases vs with
    | cons v vs =>
      cases v with
      | word w =>
        have wt : WordShapes ss := fun s hs => words s (List.mem_cons_of_mem _ hs)
        obtain ⟨g,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by simp only [List.length_cons] at fuel; omega : f ≠ 0)
        have read : load I.data (base + pos) = w.val := by
          rw [← position,data,encoded_cons w vs wt]
          simpa only [List.append_assoc] using CanonicalReadback.load_word pre (encodeArgs vs ++ post) w.val w.lt
        have decoded := word_at I k w base (base + pos) a g read (by simp only [List.length_cons] at fuel; omega)
        have tail := ih vs (pre ++ AbiEntry.wordBytes w.val) (pos + 32) g wt
          (by simpa only [encoded_cons w vs wt,List.append_assoc] using data)
          (by simp only [List.length_append,MixedPacket.word_length,position]; omega)
          (by simp only [List.length_cons] at fuel; omega)
        simp only [mmembers,decoded,Shape.headSize,tail]

theorem aligned (n : Nat) : roundUp (n * 32) = n * 32 := by simp only [roundUp]; omega

/-- Actual Shape.tuple mdec, including its outer allocation and original
member fuel; no successful member decoding or desired tuple is assumed. -/
theorem mdec_tuple (ss : List AbiEntry.Shape) (vs : Vals ss) (I : Input) (pre post : List UInt8)
    (a f : Nat) (words : WordShapes ss) (data : I.data = pre ++ encodeArgs vs ++ post)
    (allocation : I.free + (a + ss.length * 32) ≤ lim) (fuel : ss.length + 3 ≤ f) :
    mdec I f (.tuple ss) pre.length a = .ok (.tuple vs,a + ss.length * 32) := by
  have region : pre.length + Shape.headsSize ss ≤ I.size := by
    simp only [Input.size,data,List.length_append,encoded_length vs words,heads_words ss words]
    omega
  obtain ⟨g,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : f ≠ 0)
  have decoded := members ss vs I pre post pre.length 0 (a + ss.length * 32) g words data
    (by omega) (by omega)
  simp only [mdec,if_neg (Nat.not_lt.mpr region),alloc,aligned,if_pos allocation,decoded]

theorem anyDynamic_words (ss : List AbiEntry.Shape) (words : WordShapes ss) : Shape.anyDynamic ss = false := by
  induction ss with
  | nil => rfl
  | cons s ss ih =>
    obtain ⟨k,rfl⟩ := words s List.mem_cons_self
    have wt : WordShapes ss := fun s hs => words s (List.mem_cons_of_mem _ hs)
    simp only [Shape.anyDynamic,Shape.dynamic,ih wt,Bool.or_self]

def tupleValues {ss : List AbiEntry.Shape} (vs : Vals ss) : Vals [.tuple ss] := .cons (.tuple vs) .nil

theorem tuple_encoded (ss : List AbiEntry.Shape) (vs : Vals ss) (words : WordShapes ss) :
    encodeArgs (tupleValues vs) = encodeArgs vs := by
  have hd := anyDynamic_words ss words
  simp only [tupleValues,encodeArgs,Vals.parts,Shape.dynamic,hd,Val.enc]
  have h := assemble_static [(false,AbiEntry.assemble (Vals.parts vs))] (by
    intro p hp
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hp
    subst p
    rfl)
  simpa only [List.flatMap_cons,List.flatMap_nil,List.append_nil] using h

def tupleParams (ss : List AbiEntry.Shape) (lazy : Bool) : List Param :=
  [{shape := .tuple ss,loc := if lazy then .calldata else .memory}]

/-- Single real static tuple parameter, uniformly over arbitrary validated
word-member lists, with memory/calldata entry and typed body identity. -/
theorem tuple_roundtrip (ss : List AbiEntry.Shape) (vs : Vals ss) (selector post : List UInt8) (free f : Nat)
    (lazy : Bool) (words : WordShapes ss) (sel : selector.length = 4)
    (size : (selector ++ encodeArgs (tupleValues vs) ++ post).length ≤ lim)
    (allocation : free + ss.length * 32 ≤ lim) (fuel : ss.length + 4 ≤ f) :
    ∃ es : Entries (tupleParams ss lazy),
      enter ⟨selector ++ encodeArgs (tupleValues vs) ++ post,free⟩ f (tupleParams ss lazy) 0 0 =
        .ok (es,if lazy then 0 else ss.length * 32) ∧
      entry ⟨selector ++ encodeArgs (tupleValues vs) ++ post,free⟩ f (tupleParams ss lazy) = .ok es ∧
      bodyValues ⟨selector ++ encodeArgs (tupleValues vs) ++ post,free⟩ f (tupleParams ss lazy) es 0 = .ok (tupleValues vs) ∧
      verdict ⟨selector ++ encodeArgs (tupleValues vs) ++ post,free⟩ f (tupleParams ss lazy) = .run (tupleValues vs) ∧
      cval ⟨selector ++ encodeArgs (tupleValues vs) ++ post,free⟩ (f - 1) (.tuple ss) 4 0 = .ok (.tuple vs) := by
  let I : Input := ⟨selector ++ encodeArgs (tupleValues vs) ++ post,free⟩
  have data : I.data = selector ++ encodeArgs vs ++ post := by dsimp only [I]; rw [tuple_encoded ss vs words]
  have hd := anyDynamic_words ss words
  obtain ⟨g,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : f ≠ 0)
  have dec := mdec_tuple ss vs I selector post 0 g words data (by simpa only [I,Nat.zero_add] using allocation) (by omega)
  rw [sel] at dec
  have dm : melem I (g + 1) (.tuple ss) 4 4 0 = .ok (.tuple vs,ss.length * 32) := by
    simp only [melem,Shape.dynamic,hd,Bool.false_eq_true,ite_false,dec,Nat.zero_add]
  have ew : eager I (g + 1) (.tuple ss) 0 = .ok (.tuple vs) := by simp only [eager,Nat.add_zero,dm]
  have cr : cref I (.tuple ss) 4 0 = .ok (4,0) := by simp only [cref,Shape.dynamic,hd,Bool.false_eq_true,ite_false,Nat.add_zero]
  have heads : ¬ I.size < 4 + headsOf (tupleParams ss lazy) := by
    simp only [Input.size,data,List.length_append,encoded_length vs words,sel,headsOf,tupleParams,
      List.map_cons,List.map_nil,Shape.headsSize,Shape.headSize,hd,Bool.false_eq_true,ite_false,heads_words ss words,Nat.add_zero]
    omega
  have lv : cval I g (.tuple ss) 4 0 = .ok (.tuple vs) := by
    obtain ⟨addr,len,ref,read⟩ := eager_cref (I := I) size ew
    rw [cr] at ref
    cases ref
    exact read
  cases lazy
  case false =>
    let es : Entries (tupleParams ss false) := .cons (.val (.tuple vs)) .nil
    have en : enter I (g + 1) (tupleParams ss false) 0 0 = .ok (es,ss.length * 32) := by
      simp only [es,tupleParams,Bool.false_eq_true,ite_false,enter,Nat.add_zero,dm,Shape.headSize,hd,bind,Except.bind,pure,Except.pure]
    have ep : entry I (g + 1) (tupleParams ss false) = .ok es := by rw [entry,if_neg heads,en]
    have body : bodyValues I (g + 1) (tupleParams ss false) es 0 = .ok (tupleValues vs) := by
      simp only [es,tupleParams,bodyValues,tupleValues,bind,Except.bind,pure,Except.pure]
    refine ⟨es,en,ep,body,?_,lv⟩
    rw [verdict,ep]
    dsimp only [I] at body
    simp only [body]
  case true =>
    let es : Entries (tupleParams ss true) := .cons (.ref 4 0) .nil
    have en : enter I (g + 1) (tupleParams ss true) 0 0 = .ok (es,0) := by
      simp only [es,tupleParams,ite_true,enter,Nat.add_zero,cr,Shape.headSize,hd,bind,Except.bind,pure,Except.pure]
    have ep : entry I (g + 1) (tupleParams ss true) = .ok es := by rw [entry,if_neg heads,en]
    have body : bodyValues I (g + 1) (tupleParams ss true) es 0 = .ok (tupleValues vs) := by
      simp only [es,tupleParams,bodyValues,Nat.add_zero,ew,tupleValues,bind,Except.bind,pure,Except.pure]
    refine ⟨es,en,ep,body,?_,lv⟩
    rw [verdict,ep]
    dsimp only [I] at body
    simp only [body]



theorem seq_static {k : Kind} {n : Nat} (xs : Seq (.word k) n) :
    ∀ p ∈ Seq.parts xs, p.1 = false := by
  induction n with
  | zero => cases xs; simp only [Seq.parts,List.not_mem_nil,false_implies,forall_const]
  | succ n ih =>
    cases xs with
    | cons v xs =>
      cases v with
      | word w =>
        intro p hp
        simp only [Seq.parts,Shape.dynamic,List.mem_cons] at hp
        rcases hp with rfl | hp
        · rfl
        · exact ih xs p hp

theorem fixed_cons {k : Kind} {n : Nat} (w : Word k) (xs : Seq (.word k) n) :
    Val.enc (.fixed (.cons (.word w) xs)) = AbiEntry.wordBytes w.val ++ Val.enc (.fixed xs) := by
  have all := seq_static (Seq.cons (.word w) xs)
  have tail := seq_static xs
  rw [Val.enc,assemble_static _ all,Val.enc,assemble_static _ tail]
  rfl

theorem fixed_length {k : Kind} {n : Nat} (xs : Seq (.word k) n) : (Val.enc (.fixed xs)).length = n * 32 := by
  induction n with
  | zero => cases xs; rfl
  | succ n ih =>
    cases xs with
    | cons v xs =>
      cases v with
      | word w =>
        rw [fixed_cons]
        simp only [List.length_append,MixedPacket.word_length,ih xs]
        omega

/-- Arbitrary-length existing indexed word sequence through ACTUAL mseq,
with its original element-fuel decrements and unchanged inner cursor. -/
theorem sequence {k : Kind} {n : Nat} (xs : Seq (.word k) n) (I : Input) (pre post : List UInt8)
    (base i a f : Nat) (data : I.data = pre ++ Val.enc (.fixed xs) ++ post)
    (position : pre.length = base + i * 32) (fuel : n + 2 ≤ f) :
    mseq I f (.word k) base i n a = .ok (xs,a) := by
  induction n generalizing pre i f with
  | zero => cases xs; cases f <;> rfl
  | succ n ih =>
    cases xs with
    | cons v xs =>
      cases v with
      | word w =>
        obtain ⟨g,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : f ≠ 0)
        have read : load I.data (base + i * 32) = w.val := by
          rw [← position,data,fixed_cons]
          simpa only [List.append_assoc] using CanonicalReadback.load_word pre (Val.enc (.fixed xs) ++ post) w.val w.lt
        have dm := word_at I k w base (base + i * 32) a g read (by omega)
        have tail := ih xs (pre ++ AbiEntry.wordBytes w.val) (i + 1) g
          (by simpa only [fixed_cons,List.append_assoc] using data)
          (by simp only [List.length_append,MixedPacket.word_length,position]; omega) (by omega)
        simp only [mseq,Shape.headSize,dm,tail]

/-- The published fixed decoder retains its real header guard even for n=0.
This explicit sufficient condition is not a new source admission restriction. -/
theorem mdec_fixed {k : Kind} {n : Nat} (xs : Seq (.word k) n) (I : Input) (pre post : List UInt8)
    (a f : Nat) (data : I.data = pre ++ Val.enc (.fixed xs) ++ post)
    (header : pre.length + 31 < I.size) (allocation : I.free + (a + n * 32) ≤ lim)
    (fuel : n + 3 ≤ f) :
    mdec I f (.fixed (.word k) n) pre.length a = .ok (.fixed xs,a + n * 32) := by
  have count : n ≤ lim := by omega
  have region : pre.length + n * 32 ≤ I.size := by
    simp only [Input.size,data,List.length_append,fixed_length]
    omega
  obtain ⟨g,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : f ≠ 0)
  have decoded := sequence xs I pre post pre.length 0 (a + n * 32) g data (by omega) (by omega)
  simp only [mdec,if_pos header,if_neg (Nat.not_lt.mpr count),alloc,aligned,if_pos allocation,
    Shape.headSize,if_neg (Nat.not_lt.mpr region),decoded]


/-- General validated-word dynamic array, over the ACTUAL indexed Seq.
The count header, original allocation and element fuel are all derived. -/
theorem mdec_word_array {k : Kind} {n : Nat} (xs : Seq (.word k) n) (I : Input) (pre post : List UInt8)
    (a f : Nat) (data : I.data = pre ++ Val.enc (.array xs) ++ post)
    (allocation : I.free + (a + (n * 32 + 32)) ≤ lim) (fuel : n + 3 ≤ f) :
    mdec I f (.array (.word k)) pre.length a = .ok (.array xs,a + (n * 32 + 32)) := by
  have count : n ≤ lim := by omega
  have range : n < AbiEntry.W := by
    have h : lim < AbiEntry.W := by decide
    omega
  have layout : Val.enc (.array xs) = AbiEntry.wordBytes n ++ Val.enc (.fixed xs) := rfl
  have read : load I.data pre.length = n := by
    rw [data,layout]
    simpa only [List.append_assoc] using CanonicalReadback.load_word pre (Val.enc (.fixed xs) ++ post) n range
  have region : pre.length + 32 + n * 32 ≤ I.size := by
    simp only [Input.size,data,layout,List.length_append,MixedPacket.word_length,fixed_length]
    omega
  obtain ⟨g,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : f ≠ 0)
  have decoded := sequence xs I (pre ++ AbiEntry.wordBytes n) post (pre.length + 32) 0 (a + (n * 32 + 32)) g
    (by simpa only [layout,List.append_assoc] using data)
    (by simp only [List.length_append,MixedPacket.word_length]) (by omega)
  simp only [mdec,read,if_pos (by omega : pre.length + 31 < I.size),if_neg (Nat.not_lt.mpr count),
    alloc,CanonicalReadback.roundUp_words,if_pos allocation,Shape.headSize,if_neg (Nat.not_lt.mpr region)]
  unfold mdec.match_3
  rw [read,decoded]

/-- info: 'Solidity.Backend.AbiWorld.StaticAggregateReadback.mdec_word_array' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms mdec_word_array

/-- info: 'Solidity.Backend.AbiWorld.StaticAggregateReadback.word_at' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms word_at
/-- info: 'Solidity.Backend.AbiWorld.StaticAggregateReadback.members' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms members
/-- info: 'Solidity.Backend.AbiWorld.StaticAggregateReadback.aligned' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms aligned
/-- info: 'Solidity.Backend.AbiWorld.StaticAggregateReadback.mdec_tuple' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms mdec_tuple
/-- info: 'Solidity.Backend.AbiWorld.StaticAggregateReadback.anyDynamic_words' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms anyDynamic_words
/-- info: 'Solidity.Backend.AbiWorld.StaticAggregateReadback.tuple_encoded' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms tuple_encoded
/-- info: 'Solidity.Backend.AbiWorld.StaticAggregateReadback.tuple_roundtrip' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms tuple_roundtrip
/-- info: 'Solidity.Backend.AbiWorld.StaticAggregateReadback.seq_static' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms seq_static
/-- info: 'Solidity.Backend.AbiWorld.StaticAggregateReadback.fixed_cons' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms fixed_cons
/-- info: 'Solidity.Backend.AbiWorld.StaticAggregateReadback.fixed_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms fixed_length
/-- info: 'Solidity.Backend.AbiWorld.StaticAggregateReadback.sequence' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms sequence
/-- info: 'Solidity.Backend.AbiWorld.StaticAggregateReadback.mdec_fixed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms mdec_fixed
end Solidity.Backend.AbiWorld.StaticAggregateReadback
