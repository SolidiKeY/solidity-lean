import Solidity.Backend.AbiWorld.BodyComposition

/-! Uniform canonical readback for arbitrary lists of existing validated word
shapes/values. WordShapes is an auxiliary sufficient constructor condition,
not a new admitted source profile. No new value/decoder/evaluator is defined. -/
namespace Solidity.Backend.AbiWorld.WordListReadback
open AbiEntry

def WordShapes (ss : List AbiEntry.Shape) : Prop := ∀ s ∈ ss, ∃ k, s = .word k

theorem go_static (parts : List (Bool × List UInt8)) (off : Nat)
    (static : ∀ p ∈ parts, p.1 = false) :
    AbiEntry.assemble.go parts off = (parts.flatMap Prod.snd,[]) := by
  induction parts generalizing off with
  | nil => rfl
  | cons p ps ih =>
    rcases p with ⟨d,b⟩
    have hd : d = false := static (d,b) List.mem_cons_self
    subst d
    have tail : ∀ p ∈ ps, p.1 = false := fun p hp => static p (List.mem_cons_of_mem _ hp)
    simp only [AbiEntry.assemble.go,Bool.false_eq_true,ite_false,ih _ tail,List.flatMap_cons]

theorem assemble_static (parts : List (Bool × List UInt8))
    (static : ∀ p ∈ parts, p.1 = false) : AbiEntry.assemble parts = parts.flatMap Prod.snd := by
  simp only [AbiEntry.assemble,go_static parts _ static,List.append_nil]

theorem parts_static {ss : List AbiEntry.Shape} (vs : Vals ss) (words : WordShapes ss) :
    ∀ p ∈ Vals.parts vs, p.1 = false := by
  induction ss with
  | nil => cases vs; simp only [Vals.parts,List.not_mem_nil,false_implies,forall_const]
  | cons s ss ih =>
    obtain ⟨k,rfl⟩ := words s (List.mem_cons_self)
    cases vs with
    | cons v vs =>
      cases v with
      | word w =>
        have tail : WordShapes ss := fun s hs => words s (List.mem_cons_of_mem _ hs)
        intro p hp
        simp only [Vals.parts,Shape.dynamic,List.mem_cons] at hp
        rcases hp with rfl | hp
        · rfl
        · exact ih vs tail p hp

theorem encoded_cons {k : Kind} {ss : List AbiEntry.Shape} (w : Word k) (vs : Vals ss) (words : WordShapes ss) :
    encodeArgs (.cons (.word w) vs) = AbiEntry.wordBytes w.val ++ encodeArgs vs := by
  have tail := parts_static vs words
  have whole : WordShapes (.word k :: ss) := by
    intro s hs
    simp only [List.mem_cons] at hs
    rcases hs with rfl | hs
    · exact ⟨k,rfl⟩
    · exact words s hs
  have all := parts_static (Vals.cons (.word w) vs) whole
  rw [encodeArgs,assemble_static _ all]
  rw [encodeArgs,assemble_static _ tail]
  rfl

theorem encoded_length {ss : List AbiEntry.Shape} (vs : Vals ss) (words : WordShapes ss) :
    (encodeArgs vs).length = ss.length * 32 := by
  induction ss with
  | nil => cases vs; rfl
  | cons s ss ih =>
    obtain ⟨k,rfl⟩ := words s (List.mem_cons_self)
    cases vs with
    | cons v vs =>
      cases v with
      | word w =>
        have tail : WordShapes ss := fun s hs => words s (List.mem_cons_of_mem _ hs)
        rw [encoded_cons w vs tail]
        simp only [List.length_append,MixedPacket.word_length,ih vs tail,List.length_cons]
        omega

theorem heads_words (ss : List AbiEntry.Shape) (words : WordShapes ss) : Shape.headsSize ss = ss.length * 32 := by
  induction ss with
  | nil => rfl
  | cons s ss ih =>
    obtain ⟨k,rfl⟩ := words s (List.mem_cons_self)
    have tail : WordShapes ss := fun s hs => words s (List.mem_cons_of_mem _ hs)
    simp only [Shape.headsSize,Shape.headSize,ih tail,List.length_cons]
    omega

/-- All existing word kinds use their ACTUAL validation proof, not uint8 as
an enum-cardinality proxy or low-byte cleanup. No allocation occurs. -/
theorem word_melem (I : Input) (k : Kind) (w : Word k) (pos a f : Nat)
    (read : load I.data (4 + pos) = w.val) (fuel : 2 ≤ f) :
    melem I f (.word k) 4 (4 + pos) a = .ok (.word w,a) := by
  obtain ⟨g,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : f ≠ 0)
  obtain ⟨h,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : g ≠ 0)
  simp only [melem,Shape.dynamic,Bool.false_eq_true,ite_false,mdec,read,w.valid,dite_true]



/-- Typed induction over arbitrary parameter/value lists. Canonical words are
read from their REAL assembled bytes; both actual composition laws are used.
The original enter/body recursions reuse f, and no parameter allocates. -/
theorem window (ps : List Param) (vs : Vals (ps.map Param.shape)) (I : Input)
    (pre post : List UInt8) (pos a f : Nat) (words : WordShapes (ps.map Param.shape))
    (data : I.data = pre ++ encodeArgs vs ++ post) (position : pre.length = 4 + pos) (fuel : 2 ≤ f) :
    ∃ es : Entries ps, enter I f ps pos a = .ok (es,a) ∧ bodyValues I f ps es pos = .ok vs := by
  induction ps generalizing pre pos with
  | nil =>
    cases vs
    exact ⟨.nil,rfl,rfl⟩
  | cons p ps ih =>
    rcases p with ⟨s,loc,ro⟩
    obtain ⟨k,rfl⟩ := words s List.mem_cons_self
    cases vs with
    | cons v vs =>
      cases v with
      | word w =>
        have wt : WordShapes (ps.map Param.shape) := fun s hs => words s (List.mem_cons_of_mem _ hs)
        have nextData : I.data = (pre ++ AbiEntry.wordBytes w.val) ++ encodeArgs vs ++ post := by
          simpa only [encoded_cons w vs wt,List.append_assoc] using data
        have nextPos : (pre ++ AbiEntry.wordBytes w.val).length = 4 + (pos + 32) := by
          simp only [List.length_append,MixedPacket.word_length,position]
          omega
        obtain ⟨es,tailEnter,tailBody⟩ := ih vs (pre ++ AbiEntry.wordBytes w.val) (pos + 32) wt nextData nextPos
        have read : load I.data (4 + pos) = w.val := by
          rw [← position,data,encoded_cons w vs wt]
          simpa only [List.append_assoc] using CanonicalReadback.load_word pre (encodeArgs vs ++ post) w.val w.lt
        have dm := word_melem I k w pos a f read fuel
        have ew : eager I f (.word k) pos = .ok (.word w) := by
          simp only [eager,word_melem I k w pos 0 f read fuel]
        have cr : cref I (.word k) 4 pos = .ok (4 + pos,0) := rfl
        have single : ∃ hs : Entries [{shape := .word k,loc := loc,readsOnly := ro}],
            enter I f [{shape := .word k,loc := loc,readsOnly := ro}] pos a = .ok (hs,a) ∧
            bodyValues I f [{shape := .word k,loc := loc,readsOnly := ro}] hs pos =
              .ok (.cons (.word w) .nil) := by
          cases loc
          case value | memory =>
            refine ⟨.cons (.val (.word w)) .nil,?_,?_⟩ <;>
              simp only [enter,bodyValues,Shape.headSize,dm,bind,Except.bind,pure,Except.pure]
          case calldata =>
            refine ⟨.cons (.ref (4 + pos) 0) .nil,?_,?_⟩ <;>
              simp only [enter,bodyValues,Shape.headSize,cr,ew,bind,Except.bind,pure,Except.pure]
        obtain ⟨hs,headEnter,headBody⟩ := single
        refine ⟨EntryComposition.appendEntries hs es,?_,?_⟩
        · change enter I f ([{shape := .word k,loc := loc,readsOnly := ro}] ++ ps) pos a = _
          rw [EntryComposition.enter_append,headEnter]
          simp only [headsOf,List.map_cons,List.map_nil,Shape.headsSize,Shape.headSize,Nat.add_zero,
            bind,Except.bind,pure,Except.pure,tailEnter]
        · have h := BodyComposition.body_success I f hs es (.cons (.word w) .nil) vs pos headBody
            (by simpa only [headsOf,List.map_cons,List.map_nil,Shape.headsSize,Shape.headSize,Nat.add_zero] using tailBody)
          simpa only [BodyComposition.appendValues_cons,BodyComposition.appendValues_nil] using h

def input (ps : List Param) (vs : Vals (ps.map Param.shape)) (selector post : List UInt8) (free : Nat) : Input :=
  ⟨selector ++ encodeArgs vs ++ post,free⟩

/-- Uniform actual canonical entry/body admission for arbitrary-length word
parameter lists. Sufficient constructor/fuel/size conditions are NOT a new
profile; all other shapes, noncanonical/lazy behavior and defaults remain. -/
theorem roundtrip (ps : List Param) (vs : Vals (ps.map Param.shape)) (selector post : List UInt8)
    (free f : Nat) (words : WordShapes (ps.map Param.shape)) (sel : selector.length = 4)
    (size : (input ps vs selector post free).size ≤ lim) (fuel : 2 ≤ f) :
    ∃ es : Entries ps,
      enter (input ps vs selector post free) f ps 0 0 = .ok (es,0) ∧
      entry (input ps vs selector post free) f ps = .ok es ∧
      bodyValues (input ps vs selector post free) f ps es 0 = .ok vs ∧
      verdict (input ps vs selector post free) f ps = .run vs ∧ 4 + headsOf ps ≤ lim := by
  obtain ⟨es,entered,body⟩ := window ps vs (input ps vs selector post free) selector post 0 0 f words rfl
    (by simpa only [Nat.add_zero] using sel) fuel
  have fit : 4 + headsOf ps ≤ (input ps vs selector post free).size := by
    simp only [input,Input.size,List.length_append,encoded_length vs words,headsOf,
      heads_words _ words,sel]
    omega
  have heads : ¬ (input ps vs selector post free).size < 4 + headsOf ps := Nat.not_lt.mpr fit
  have e : entry (input ps vs selector post free) f ps = .ok es := by rw [entry,if_neg heads,entered]
  refine ⟨es,entered,e,body,?_,Nat.le_trans fit size⟩
  rw [verdict,e]
  simp only [body]


/-- info: 'Solidity.Backend.AbiWorld.WordListReadback.go_static' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms go_static
/-- info: 'Solidity.Backend.AbiWorld.WordListReadback.assemble_static' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms assemble_static
/-- info: 'Solidity.Backend.AbiWorld.WordListReadback.parts_static' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms parts_static
/-- info: 'Solidity.Backend.AbiWorld.WordListReadback.encoded_cons' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms encoded_cons
/-- info: 'Solidity.Backend.AbiWorld.WordListReadback.encoded_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms encoded_length
/-- info: 'Solidity.Backend.AbiWorld.WordListReadback.heads_words' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms heads_words
/-- info: 'Solidity.Backend.AbiWorld.WordListReadback.word_melem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms word_melem
/-- info: 'Solidity.Backend.AbiWorld.WordListReadback.window' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms window
/-- info: 'Solidity.Backend.AbiWorld.WordListReadback.roundtrip' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms roundtrip
end Solidity.Backend.AbiWorld.WordListReadback
