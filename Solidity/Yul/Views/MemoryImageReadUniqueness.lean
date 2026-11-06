import Solidity.Yul.Views.MemoryImages

namespace Solidity.Yul.Views

theorem MemoryFields.words_unique {D : Source.Layout} {h : Source.Heap D} {p : Placement h}
    {τs : List Source.STy} {fs : Source.DataList D τs} {ws vs : List Roadmap.Word}
    (one : MemoryFields p fs ws) (two : MemoryFields p fs vs) : ws=vs := by
  induction one generalizing vs with
  | nil => cases two; rfl
  | cons v w encoded fs ws rest ih =>
    cases two with
    | cons _ v other _ vs tail =>
      have head := elementWord_unique encoded.read other.read
      rw [head,ih tail]

theorem MemoryFields.word_source {D : Source.Layout} {h : Source.Heap D} {p : Placement h}
    {τs : List Source.STy} {fs : Source.DataList D τs} {ws : List Roadmap.Word}
    (fields : MemoryFields p fs ws) (i : Nat) (w : Roadmap.Word) (found : ws[i]?=some w) :
    ∃ τ, ∃ v : Source.Val D τ, fs.nth i τ=.ok (.val v) ∧ MemoryElement p v w := by
  induction fields generalizing i with
  | nil => cases found
  | @cons τ τs v word encoded fs ws rest ih =>
    cases i with
    | zero =>
      cases found
      exact ⟨τ,v,by simp only [Source.DataList.nth,dite_true]; rfl,encoded⟩
    | succ i => exact ih i found

/-- Converse to the existing logical-read theorem: every serialized word has
an ACTUAL typed ObjectWord witness. No separate word-list adequacy is assumed. -/
theorem MemoryObjectWords.word_source {D : Source.Layout} {h : Source.Heap D} {p : Placement h}
    {τ : Source.STy} {d : Source.Data D τ} {ws : List Roadmap.Word}
    (encoded : MemoryObjectWords p d ws) (i : Nat) (w : Roadmap.Word) (found : ws[i]?=some w) :
    ObjectWord p.address d (i*32) w := by
  cases encoded with
  | value v word e =>
    cases i with
    | zero => cases found; exact .value v _ e.read
    | succ i => cases found
  | @array l τ k n hl bound values words elements =>
    have element (i : Nat) (read : (List.ofFn words)[i]?=some w) :
        ObjectWord p.address (.array (l := l) n hl (fun j => .val (values j)))
          ((if k.isNone then 32 else 0)+i*32) w := by
      obtain ⟨inside,value⟩ := List.getElem?_eq_some_iff.mp read
      have small : i<n := by simpa only [List.length_ofFn] using inside
      have same : words ⟨i,small⟩=w := by simpa only [List.getElem_ofFn] using value
      rw [← same]
      exact .arrayElement n hl _ ⟨i,small⟩ (values ⟨i,small⟩) _ rfl (elements ⟨i,small⟩).read
    cases k with
    | none =>
      cases i with
      | zero => cases found; exact .arrayLength n bound hl _
      | succ i =>
        have read : (List.ofFn words)[i]?=some w := found
        have e := element i read
        have offset : (if (none : Option Nat).isNone then 32 else 0)+i*32=(i+1)*32 := by simp only [Option.isNone_none,if_true]; omega
        rw [offset] at e
        exact e
    | some k =>
      have e := element i found
      simpa only [Option.isNone_some,Bool.false_eq_true,if_false,Nat.zero_add] using e
  | strct fs words fields =>
    obtain ⟨τ,v,source,encoded⟩ := fields.word_source i w found
    exact .structMember fs i v w source encoded.read

theorem MemoryObjectWords.words_unique {D : Source.Layout} {h : Source.Heap D} {p : Placement h}
    {τ : Source.STy} {d : Source.Data D τ} {ws vs : List Roadmap.Word}
    (one : MemoryObjectWords p d ws) (two : MemoryObjectWords p d vs) : ws=vs := by
  have transfer {xs ys : List Roadmap.Word} (a : MemoryObjectWords p d xs) (b : MemoryObjectWords p d ys)
      (i : Nat) (w : Roadmap.Word) (found : xs[i]?=some w) : ys[i]?=some w := by
    obtain ⟨j,read,offset⟩ := b.read (i*32) w (a.word_source i w found)
    have same : j=i := by omega
    rwa [same] at read
  apply List.ext_getElem?
  intro i
  cases left : ws[i]? with
  | none =>
    cases right : vs[i]? with
    | none => rfl
    | some w => have bad := transfer two one i w right; rw [left] at bad; cases bad
  | some w => exact (transfer one two i w left).symm

/-- Any actual constructor-derived image of the SAME intrinsic data has the
same read relation. This is not arbitrary cross-heap pointer agreement. -/
theorem MemoryImage.reads_unique {D : Source.Layout} {h : Source.Heap D} {p : Placement h}
    {τ : Source.STy} {d : Source.Data D τ} (one two : MemoryImage p d) (m : ByteView) (base : Nat) :
    one.Reads m base ↔ two.Reads m base := by
  cases one with
  | bytes bs bound =>
    cases two with
    | bytes _ _ => rfl
    | words _ _ encoded => cases encoded
  | string bs bound =>
    cases two with
    | string _ _ => rfl
    | words _ _ encoded => cases encoded
  | words d ws encoded =>
    cases two with
    | bytes _ _ => cases encoded
    | string _ _ => cases encoded
    | words _ vs other =>
      have same := encoded.words_unique other
      subst vs
      rfl

end Solidity.Yul.Views
