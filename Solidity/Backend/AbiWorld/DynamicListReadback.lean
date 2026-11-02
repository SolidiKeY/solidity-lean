import Solidity.Backend.AbiWorld.StaticAggregateReadback
import Solidity.Backend.AbiWorld.BytesArrayReadback

/-! Canonical heterogeneous word/bytes lists, using the actual assemble.go
head/tail recursion and actual indexed decoder. Auxiliary sufficient cases do
not restrict source admission or supply an unknown-memory runtime encoder. -/
namespace Solidity.Backend.AbiWorld.DynamicListReadback
open AbiEntry

def LeafShapes (ss : List AbiEntry.Shape) : Prop := ∀ s ∈ ss, (∃ k, s = .word k) ∨ s = .bytes

/-- Actual dynamic-tail byte extent; offsets never stand for modular words. -/
def tailSize {ss : List AbiEntry.Shape} (vs : Vals ss) : Nat :=
  (AbiEntry.assemble.go (Vals.parts vs) 0).2.length

theorem tails_independent (parts : List (Bool × List UInt8)) (a b : Nat) :
    (AbiEntry.assemble.go parts a).2 = (AbiEntry.assemble.go parts b).2 := by
  induction parts generalizing a b with
  | nil => rfl
  | cons p ps ih =>
    rcases p with ⟨d,bytes⟩
    cases d <;> simp only [AbiEntry.assemble.go,Bool.false_eq_true,ite_false,ite_true]
    · exact ih _ _
    · rw [ih _ _]

theorem go_word {ss : List AbiEntry.Shape} {k : Kind} (w : Word k) (vs : Vals ss) (off : Nat) :
    AbiEntry.assemble.go (Vals.parts (.cons (.word w) vs)) off =
      (AbiEntry.wordBytes w.val ++ (AbiEntry.assemble.go (Vals.parts vs) off).1,
       (AbiEntry.assemble.go (Vals.parts vs) off).2) := rfl

theorem go_bytes {ss : List AbiEntry.Shape} (bs : List UInt8) (vs : Vals ss) (off : Nat) :
    AbiEntry.assemble.go (Vals.parts (.cons (.bytes bs) vs)) off =
      (AbiEntry.wordBytes off ++ (AbiEntry.assemble.go (Vals.parts vs) (off + (Val.enc (.bytes bs)).length)).1,
       Val.enc (.bytes bs) ++ (AbiEntry.assemble.go (Vals.parts vs) (off + (Val.enc (.bytes bs)).length)).2) := rfl

theorem tail_word {ss : List AbiEntry.Shape} {k : Kind} (w : Word k) (vs : Vals ss) :
    tailSize (.cons (.word w) vs) = tailSize vs := rfl

theorem tail_bytes {ss : List AbiEntry.Shape} (bs : List UInt8) (vs : Vals ss) :
    tailSize (.cons (.bytes bs) vs) = BytesReadback.allocationBytes bs + tailSize vs := by
  simp only [tailSize,go_bytes,List.length_append]
  rw [tails_independent _ _ 0]
  have h := BytesArrayReadback.byte_payload_length bs
  exact congrArg (fun n => n + (AbiEntry.assemble.go (Vals.parts vs) 0).2.length) h

/-- Auxiliary location-dependent measurement. It agrees with actual entry
allocation only under LeafShapes (words/bytes), not for arbitrary aggregates.
No new allocator or general cost model is defined. -/
def spent : (ps : List Param) → Vals (ps.map Param.shape) → Nat
  | [], .nil => 0
  | p :: ps, .cons v vs =>
      (if p.loc == .calldata then 0 else if p.shape.dynamic then (Val.enc v).length else 0) + spent ps vs

 theorem spent_nil : spent [] .nil = 0 := rfl
 theorem spent_cons (p : Param) (ps : List Param) (v : AbiEntry.Val p.shape) (vs : Vals (ps.map Param.shape)) :
    spent (p :: ps) (.cons v vs) =
      (if p.loc == .calldata then 0 else if p.shape.dynamic then (Val.enc v).length else 0) + spent ps vs := rfl

theorem head_length (ss : List AbiEntry.Shape) (vs : Vals ss) (off : Nat) (leaves : LeafShapes ss) :
    (AbiEntry.assemble.go (Vals.parts vs) off).1.length = ss.length * 32 := by
  induction ss generalizing off with
  | nil => cases vs; rfl
  | cons s ss ih =>
    have rest : LeafShapes ss := fun s hs => leaves s (List.mem_cons_of_mem _ hs)
    rcases leaves s List.mem_cons_self with ⟨k,rfl⟩ | rfl
    · cases vs with
      | cons v vs => cases v with
        | word w => simp only [go_word,List.length_append,MixedPacket.word_length,ih vs off rest,List.length_cons]; omega
    · cases vs with
      | cons v vs => cases v with
        | bytes bs => simp only [go_bytes,List.length_append,MixedPacket.word_length,ih vs _ rest,List.length_cons]; omega

theorem heads_leaves (ss : List AbiEntry.Shape) (leaves : LeafShapes ss) : Shape.headsSize ss = ss.length * 32 := by
  induction ss with
  | nil => rfl
  | cons s ss ih =>
    have rest : LeafShapes ss := fun s hs => leaves s (List.mem_cons_of_mem _ hs)
    rcases leaves s List.mem_cons_self with ⟨k,rfl⟩ | rfl
    all_goals simp only [Shape.headsSize,Shape.headSize,ih rest,List.length_cons]; omega

theorem head_fold (ss : List AbiEntry.Shape) (vs : Vals ss) (a : Nat) (leaves : LeafShapes ss) :
    (Vals.parts vs).foldl (fun acc (d,b) => acc + if d then 32 else b.length) a = a + ss.length * 32 := by
  induction ss generalizing a with
  | nil => cases vs; simp only [Vals.parts,List.foldl_nil,List.length_nil,Nat.zero_mul,Nat.add_zero]
  | cons s ss ih =>
    have rest : LeafShapes ss := fun s hs => leaves s (List.mem_cons_of_mem _ hs)
    rcases leaves s List.mem_cons_self with ⟨k,rfl⟩ | rfl
    · cases vs with
      | cons v vs => cases v with
        | word w =>
          simp only [Vals.parts,Shape.dynamic,List.foldl_cons,Bool.false_eq_true,ite_false,Val.enc,
            MixedPacket.word_length,ih vs _ rest,List.length_cons]
          omega
    · cases vs with
      | cons v vs => cases v with
        | bytes bs =>
          simp only [Vals.parts,Shape.dynamic,List.foldl_cons,ite_true,ih vs _ rest,List.length_cons]
          omega

theorem encoded (ss : List AbiEntry.Shape) (vs : Vals ss) (leaves : LeafShapes ss) :
    encodeArgs vs = (AbiEntry.assemble.go (Vals.parts vs) (ss.length * 32)).1 ++
      (AbiEntry.assemble.go (Vals.parts vs) (ss.length * 32)).2 := by
  simp only [encodeArgs,AbiEntry.assemble,head_fold ss vs 0 leaves,Nat.zero_add]

theorem encoded_length (ss : List AbiEntry.Shape) (vs : Vals ss) (leaves : LeafShapes ss) :
    (encodeArgs vs).length = ss.length * 32 + tailSize vs := by
  rw [encoded ss vs leaves,List.length_append,head_length ss vs _ leaves,tails_independent _ _ 0]
  rfl

/-- A reusable one-parameter consequence; all its decoder/reference premises
are discharged from actual codec windows in window below. -/
theorem one_success (p : Param) (v : AbiEntry.Val p.shape) (I : Input) (pos a f cost addr len : Nat)
    (dm : melem I f p.shape 4 (4 + pos) a = .ok (v,a + cost))
    (ew : eager I f p.shape pos = .ok v) (cr : cref I p.shape 4 pos = .ok (addr,len)) :
    ∃ hs : Entries [p], enter I f [p] pos a = .ok (hs,a + if p.loc == .calldata then 0 else cost) ∧
      bodyValues I f [p] hs pos = .ok (.cons v .nil) := by
  cases h : p.loc
  case value | memory =>
    refine ⟨.cons (.val v) .nil,?_,?_⟩ <;>
      simp only [enter,h,dm,bodyValues,bind,Except.bind,pure,Except.pure,BEq.beq,reduceCtorEq,decide_false,Bool.false_eq_true,ite_false]
  case calldata =>
    refine ⟨.cons (.ref addr len) .nil,?_,?_⟩ <;>
      simp only [enter,h,cr,bodyValues,ew,bind,Except.bind,pure,Except.pure,BEq.beq,decide_true,ite_true,Nat.add_zero]

/-- Actual typed induction through mixed static heads and dynamic tails.
Both byte windows are equations from assemble.go, not decoder-success
assumptions. Allocation bound covers eager body copies even for calldata. -/
theorem window (ps : List Param) (vs : Vals (ps.map Param.shape)) (I : Input)
    (hp hs tp ts : List UInt8) (pos off a f : Nat) (leaves : LeafShapes (ps.map Param.shape))
    (headData : I.data = hp ++ (AbiEntry.assemble.go (Vals.parts vs) off).1 ++ hs)
    (tailData : I.data = tp ++ (AbiEntry.assemble.go (Vals.parts vs) off).2 ++ ts)
    (headPos : hp.length = 4 + pos) (tailPos : tp.length = 4 + off)
    (size : I.size ≤ lim) (allocation : I.free + (a + tailSize vs) ≤ lim) (fuel : 2 ≤ f) :
    ∃ es : Entries ps, enter I f ps pos a = .ok (es,a + spent ps vs) ∧
      bodyValues I f ps es pos = .ok vs := by
  induction ps generalizing hp tp pos off a with
  | nil => cases vs; exact ⟨.nil,rfl,rfl⟩
  | cons p ps ih =>
    rcases p with ⟨s,loc,ro⟩
    have rest : LeafShapes (ps.map Param.shape) := fun s hs => leaves s (List.mem_cons_of_mem _ hs)
    rcases leaves s List.mem_cons_self with ⟨k,rfl⟩ | rfl
    · cases vs with
      | cons v vs => cases v with
        | word w =>
          have read : load I.data (4 + pos) = w.val := by
            rw [← headPos,headData,go_word]
            simpa only [List.append_assoc] using CanonicalReadback.load_word hp
              ((AbiEntry.assemble.go (Vals.parts vs) off).1 ++ hs) w.val w.lt
          have dm := WordListReadback.word_melem I k w pos a f read fuel
          have ew : eager I f (.word k) pos = .ok (.word w) := by
            simp only [eager,WordListReadback.word_melem I k w pos 0 f read fuel]
          have single := one_success {shape := .word k,loc,readsOnly := ro} (.word w) I pos a f 0 (4 + pos) 0
            (by simpa only [Nat.add_zero] using dm) ew rfl
          obtain ⟨es,he,hb⟩ := single
          obtain ⟨fs,te,tb⟩ := ih vs (hp ++ AbiEntry.wordBytes w.val) tp (pos + 32) off a rest
            (by simpa only [go_word,List.append_assoc] using headData)
            (by simpa only [go_word] using tailData)
            (by simp only [List.length_append,MixedPacket.word_length,headPos]; omega) tailPos
            (by simpa only [tail_word] using allocation)
          refine ⟨EntryComposition.appendEntries es fs,?_,?_⟩
          · change enter I f ([{shape := .word k,loc,readsOnly := ro}] ++ ps) pos a = _
            rw [EntryComposition.enter_append,he]
            simp only [spent_cons,Shape.dynamic,Bool.false_eq_true,ite_false,ite_self,Nat.add_zero,Nat.zero_add,
              headsOf,List.map_cons,List.map_nil,Shape.headsSize,Shape.headSize,te,bind,Except.bind,pure,Except.pure]
          · have h := BodyComposition.body_success I f es fs (.cons (.word w) .nil) vs pos hb
              (by simpa only [headsOf,List.map_cons,List.map_nil,Shape.headsSize,Shape.headSize,Nat.add_zero] using tb)
            simpa only [BodyComposition.appendValues_cons,BodyComposition.appendValues_nil] using h
    · cases vs with
      | cons v vs => cases v with
        | bytes bs =>
          let b := BytesReadback.allocationBytes bs
          let a' := a + if loc == .calldata then 0 else b
          have plen : (Val.enc (.bytes bs)).length = b := BytesArrayReadback.byte_payload_length bs
          have point : 4 + off ≤ I.size := by
            have h : tp.length ≤ I.size := by simp only [Input.size,tailData,List.length_append]; omega
            omega
          have offlim : off ≤ lim := by omega
          have offword : off < AbiEntry.W := Nat.lt_of_le_of_lt offlim (by decide)
          have read : load I.data (4 + pos) = off := by
            rw [← headPos,headData,go_bytes]
            simpa only [List.append_assoc] using CanonicalReadback.load_word hp
              ((AbiEntry.assemble.go (Vals.parts vs) (off + (Val.enc (.bytes bs)).length)).1 ++ hs) off offword
          have tail : I.data.drop (4 + off) = AbiEntry.wordBytes bs.length ++ bs ++
              (List.replicate (roundUp bs.length - bs.length) 0 ++
                (AbiEntry.assemble.go (Vals.parts vs) (off + (Val.enc (.bytes bs)).length)).2 ++ ts) := by
            rw [tailData,go_bytes]
            simp only [List.append_assoc]
            rw [List.drop_left' tailPos]
            simp only [Val.enc,List.append_assoc]
          have bnd : I.free + (a + b) ≤ lim := by rw [tail_bytes] at allocation; omega
          have dm := BytesArrayReadback.bytes_window bs I pos off a f _ read offlim tail point bnd fuel
          have dm0 := BytesArrayReadback.bytes_window bs I pos off 0 f _ read offlim tail point
            (by omega) fuel
          have ew : eager I f .bytes pos = .ok (.bytes bs) := by simp only [eager,dm0,Nat.zero_add]
          have cr := BytesArrayReadback.bytes_reference bs I pos off _ read offlim tail point size
          obtain ⟨es,he,hb⟩ := one_success {shape := .bytes,loc,readsOnly := ro} (.bytes bs) I pos a f b
            (4 + off + 32) bs.length dm ew cr
          have ale : a' ≤ a + b := by dsimp only [a']; split <;> omega
          obtain ⟨fs,te,tb⟩ := ih vs (hp ++ AbiEntry.wordBytes off) (tp ++ Val.enc (.bytes bs))
            (pos + 32) (off + (Val.enc (.bytes bs)).length) a' rest
            (by simpa only [go_bytes,List.append_assoc] using headData)
            (by simpa only [go_bytes,List.append_assoc] using tailData)
            (by simp only [List.length_append,MixedPacket.word_length,headPos]; omega)
            (by simp only [List.length_append,tailPos]; omega)
            (by rw [tail_bytes] at allocation; omega)
          refine ⟨EntryComposition.appendEntries es fs,?_,?_⟩
          · change enter I f ([{shape := .bytes,loc,readsOnly := ro}] ++ ps) pos a = _
            rw [EntryComposition.enter_append,he]
            simp only [spent_cons,Shape.dynamic,ite_true,plen,headsOf,List.map_cons,List.map_nil,
              Shape.headsSize,Shape.headSize,Nat.add_zero,bind,Except.bind,pure,Except.pure,a',Nat.add_assoc,te]
          · have h := BodyComposition.body_success I f es fs (.cons (.bytes bs) .nil) vs pos hb
              (by simpa only [headsOf,List.map_cons,List.map_nil,Shape.headsSize,Shape.headSize,Nat.add_zero] using tb)
            simpa only [BodyComposition.appendValues_cons,BodyComposition.appendValues_nil] using h

def input (ps : List Param) (vs : Vals (ps.map Param.shape)) (selector post : List UInt8) (free : Nat) : Input :=
  ⟨selector ++ encodeArgs vs ++ post,free⟩

/-- Uniform canonical typed admission beyond WordShapes, with actual dynamic
layout-derived head extent, exact reached cursor, and unchanged original fuel.
This is a sufficient word/bytes family, not a new source admission predicate. -/
theorem roundtrip (ps : List Param) (vs : Vals (ps.map Param.shape)) (selector post : List UInt8) (free f : Nat)
    (leaves : LeafShapes (ps.map Param.shape)) (sel : selector.length = 4)
    (size : (input ps vs selector post free).size ≤ lim) (allocation : free + tailSize vs ≤ lim) (fuel : 2 ≤ f) :
    ∃ es : Entries ps,
      enter (input ps vs selector post free) f ps 0 0 = .ok (es,spent ps vs) ∧
      entry (input ps vs selector post free) f ps = .ok es ∧
      bodyValues (input ps vs selector post free) f ps es 0 = .ok vs ∧
      verdict (input ps vs selector post free) f ps = .run vs ∧ 4 + headsOf ps ≤ lim := by
  let off := (ps.map Param.shape).length * 32
  let h := (AbiEntry.assemble.go (Vals.parts vs) off).1
  let t := (AbiEntry.assemble.go (Vals.parts vs) off).2
  have layout : encodeArgs vs = h ++ t := encoded _ vs leaves
  have hlen : h.length = off := head_length _ vs off leaves
  obtain ⟨es,en,body⟩ := window ps vs (input ps vs selector post free) selector (t ++ post)
    (selector ++ h) post 0 off 0 f leaves
    (by simp only [input,layout,List.append_assoc,h])
    (by simp only [input,layout,List.append_assoc,t])
    (by omega) (by simp only [List.length_append,sel,hlen])
    size (by simpa only [input,Nat.zero_add] using allocation) fuel
  have fit : 4 + headsOf ps ≤ (input ps vs selector post free).size := by
    simp only [input,Input.size,List.length_append,sel,encoded_length _ vs leaves,
      headsOf,heads_leaves _ leaves]
    omega
  have ep : entry (input ps vs selector post free) f ps = .ok es := by
    rw [entry,if_neg (Nat.not_lt.mpr fit),en]
  refine ⟨es,by simpa only [Nat.zero_add] using en,ep,body,?_,Nat.le_trans fit size⟩
  rw [verdict,ep]
  simp only [body]

/-- Real assemble concatenation: a suffix starts after the prefix's actual
ordered dynamic tails, with no dependence on later payload contents. -/
theorem go_append (ps qs : List (Bool × List UInt8)) (off : Nat) :
    AbiEntry.assemble.go (ps ++ qs) off =
      ((AbiEntry.assemble.go ps off).1 ++ (AbiEntry.assemble.go qs (off + (AbiEntry.assemble.go ps off).2.length)).1,
       (AbiEntry.assemble.go ps off).2 ++ (AbiEntry.assemble.go qs (off + (AbiEntry.assemble.go ps off).2.length)).2) := by
  induction ps generalizing off with
  | nil => simp only [List.nil_append,AbiEntry.assemble.go,List.length_nil,Nat.add_zero,List.nil_append]
  | cons p ps ih =>
    rcases p with ⟨d,b⟩
    cases d <;> simp only [List.cons_append,AbiEntry.assemble.go,Bool.false_eq_true,ite_false,ite_true,
      ih,List.length_append,Nat.add_assoc,List.append_assoc]

/-- Exact alignment of the actual canonical dynamic-tail byte extent. -/
theorem tail_aligned (ss : List AbiEntry.Shape) (vs : Vals ss) (leaves : LeafShapes ss) :
    tailSize vs % 32 = 0 := by
  induction ss with
  | nil => cases vs; rfl
  | cons s ss ih =>
    have rest : LeafShapes ss := fun s hs => leaves s (List.mem_cons_of_mem _ hs)
    rcases leaves s List.mem_cons_self with ⟨k,rfl⟩ | rfl
    · cases vs with
      | cons v vs => cases v with
        | word w => exact ih vs rest
    · cases vs with
      | cons v vs => cases v with
        | bytes bs =>
          rw [tail_bytes,Nat.add_mod,ih vs rest]
          simp only [BytesReadback.allocationBytes,roundUp,Nat.add_mod,Nat.mul_mod,Nat.mod_self,
            Nat.mul_zero,Nat.zero_mod,Nat.add_zero]

/-- At the same actual starting offset, later parts cannot change any byte
of the earlier head or tail prefix. Canonical application also retains total
head extent; changing the number of later heads is not covered by this law. -/
theorem prefix_noninterference (ps qs rs : List (Bool × List UInt8)) (off : Nat) :
    ((AbiEntry.assemble.go (ps ++ qs) off).1.take (AbiEntry.assemble.go ps off).1.length =
      (AbiEntry.assemble.go (ps ++ rs) off).1.take (AbiEntry.assemble.go ps off).1.length) ∧
    ((AbiEntry.assemble.go (ps ++ qs) off).2.take (AbiEntry.assemble.go ps off).2.length =
      (AbiEntry.assemble.go (ps ++ rs) off).2.take (AbiEntry.assemble.go ps off).2.length) := by
  rw [go_append,go_append]
  constructor <;> simp only [List.take_left]


/-- info: 'Solidity.Backend.AbiWorld.DynamicListReadback.tails_independent' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms tails_independent
/-- info: 'Solidity.Backend.AbiWorld.DynamicListReadback.tail_bytes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms tail_bytes
/-- info: 'Solidity.Backend.AbiWorld.DynamicListReadback.head_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms head_length
/-- info: 'Solidity.Backend.AbiWorld.DynamicListReadback.heads_leaves' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms heads_leaves
/-- info: 'Solidity.Backend.AbiWorld.DynamicListReadback.head_fold' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms head_fold
/-- info: 'Solidity.Backend.AbiWorld.DynamicListReadback.encoded' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms encoded
/-- info: 'Solidity.Backend.AbiWorld.DynamicListReadback.encoded_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms encoded_length
/-- info: 'Solidity.Backend.AbiWorld.DynamicListReadback.one_success' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms one_success
/-- info: 'Solidity.Backend.AbiWorld.DynamicListReadback.window' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms window
/-- info: 'Solidity.Backend.AbiWorld.DynamicListReadback.roundtrip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms roundtrip
/-- info: 'Solidity.Backend.AbiWorld.DynamicListReadback.go_append' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms go_append
/-- info: 'Solidity.Backend.AbiWorld.DynamicListReadback.tail_aligned' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms tail_aligned
/-- info: 'Solidity.Backend.AbiWorld.DynamicListReadback.prefix_noninterference' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms prefix_noninterference
/-- info: 'Solidity.Backend.AbiWorld.DynamicListReadback.go_word' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms go_word
/-- info: 'Solidity.Backend.AbiWorld.DynamicListReadback.go_bytes' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms go_bytes
/-- info: 'Solidity.Backend.AbiWorld.DynamicListReadback.tail_word' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms tail_word

end Solidity.Backend.AbiWorld.DynamicListReadback
