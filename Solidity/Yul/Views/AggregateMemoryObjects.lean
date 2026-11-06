import Solidity.Yul.Views.AggregateMemoryWords

namespace Solidity.Yul.Views

/-- Intrinsic serialization evidence for actual source constructors. All arrays
and structs contain value/pointer WORDS; child contents remain separate objects. -/
inductive MemoryObjectWords {D : Source.Layout} {h : Source.Heap D} (p : Placement h) :
    {τ : Source.STy} → Source.Data D τ → List Roadmap.Word → Prop where
  | value {τ : Source.STy} (v : Source.Val D τ) (w : Roadmap.Word) (encoded : MemoryElement p v w) :
      MemoryObjectWords p (.val v) [w]
  | array {l : Source.DataLoc} {τ : Source.STy} {n : Option Nat} (len : Nat)
      (hl : ∀ k, n = some k → k = len) (bound : len < 2 ^ 256)
      (values : Fin len → Source.Val D τ) (words : Fin len → Roadmap.Word)
      (encoded : ∀ i, MemoryElement p (values i) (words i)) :
      MemoryObjectWords p (.array (l := l) len hl (fun i => .val (values i)))
        ((if n.isNone then [⟨len, bound⟩] else []) ++ List.ofFn words)
  | strct {l : Source.DataLoc} {name : Source.DeclName}
      (fs : Source.DataList D (D.fields name)) (ws : List Roadmap.Word) (encoded : MemoryFields p fs ws) :
      MemoryObjectWords p (.struct (l := l) fs) ws

theorem MemoryObjectWords.read {D : Source.Layout} {h : Source.Heap D} {p : Placement h}
    {τ : Source.STy} {d : Source.Data D τ} {ws : List Roadmap.Word} (encoded : MemoryObjectWords p d ws)
    (off : Nat) (w : Roadmap.Word) (read : ObjectWord p.address d off w) :
    ∃ i, ws[i]? = some w ∧ off = i * 32 := by
  cases encoded with
  | value v word elem =>
    cases read with
    | value _ _ e => exact ⟨0, congrArg some (elementWord_unique elem.read e), rfl⟩
  | @array l σ n len hl bound values words elements =>
    cases read with
    | arrayLength _ _ _ _ => exact ⟨0, rfl, rfl⟩
    | arrayElement _ _ _ i v word found e =>
      have same : values i = v := Source.Data.val.inj found
      have weq : words i = w := elementWord_unique (same ▸ (elements i).read) e
      have nth : (List.ofFn words)[i.val]? = some (words i) := by
        rw [List.getElem?_eq_getElem (by simp only [List.length_ofFn]; exact i.isLt)]
        simp only [List.getElem_ofFn]
      rw [weq] at nth
      cases n with
      | none => exact ⟨i.val + 1, nth, by simp only [Option.isNone_none, if_true]; omega⟩
      | some k => exact ⟨i.val, nth, by simp only [Option.isNone_some, Bool.false_eq_true, if_false, Nat.zero_add]⟩
  | strct fs words fields =>
    cases read with
    | structMember _ i v word found e => exact ⟨i, fields.nth i _ v w found e, rfl⟩

theorem MemoryObjectWords.fits {D : Source.Layout} {h : Source.Heap D} (p : Placement h)
    (a : Nat) {τ : Source.STy} {d : Source.Data D τ} {ws : List Roadmap.Word}
    (found : h.get a = some ⟨τ, d⟩) (encoded : MemoryObjectWords p d ws) :
    ws.length * 32 ≤ (p.shape a).size := by
  have shape := p.typed a τ d found
  generalize he : p.shape a = sh at shape
  cases encoded with
  | value _ _ _ => cases shape
  | @array l σ n len hl bound values words elements =>
    cases shape
    cases n <;> simp only [List.length_append, List.length_ofFn, Option.isNone_none,
      Option.isNone_some, Bool.false_eq_true, if_true, if_false, List.length_singleton,
      List.length_nil, MemoryShape.size] <;> omega
  | strct fs words fields =>
    cases shape
    rw [fields.length]
    exact Nat.le_refl _

/-- A whole ordinary scalar/pointer root has no current owner shape. This
control preserves that interface instead of inventing a false Placement. -/
theorem no_value_memory_shape {D : Source.Layout} {τ : Source.STy} (v : Source.Val D τ) (shape : MemoryShape) :
    ¬ HasMemoryShape (.val v) shape := by intro e; cases e

theorem array_length_from_placement {D : Source.Layout} {h : Source.Heap D} (p : Placement h)
    (a : Nat) {l : Source.DataLoc} {τ : Source.STy} {n : Option Nat} (len : Nat)
    (hl : ∀ k, n = some k → k = len) (xs : Fin len → Source.Data D τ)
    (found : h.get a = some ⟨.array l τ n, .array len hl xs⟩) : len < 2 ^ 256 := by
  have present : (h.cells a).isSome := by change (h.get a).isSome = true; rw [found]; rfl
  have ends := p.ends a present
  have shape := p.typed a _ _ found
  generalize he : p.shape a = sh at shape
  cases shape
  rw [he] at ends
  have size : len ≤ (MemoryShape.array n.isNone len).size := by
    cases n <;> simp only [MemoryShape.size, Option.isNone_none, Option.isNone_some,
      Bool.false_eq_true, if_true, if_false] <;> omega
  have free := p.free.isLt
  omega

end Solidity.Yul.Views
