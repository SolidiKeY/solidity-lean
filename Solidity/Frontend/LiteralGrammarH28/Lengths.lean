import Solidity.Frontend.LiteralGrammarH28.Fragments

/-! # Suffix and byte-length properties

Backfill for the literal grammar lane. The scanner leaves a unique, strictly
shorter suffix of its input. Each literal class bounds its decoded length by
its source length (plain and unicode only from above: an escaped line end
decodes to nothing, so the source has no upper bound in the value); hex
literals are bounded on both sides, tightly. Fragment sequences add the
lower bounds up. All statements are over the independent
relations of `Scanner`, `Quoted`, `Classification` and `Fragments`; none adds
a premise to an accepted input.
-/
namespace Solidity.Frontend.LiteralGrammarH28
open Solidity.Source Solidity.Frontend.Checked

/-- The scanner's split is unique for a literal delimiter. -/
theorem Scan.deterministic {q : UInt8} (quote : IsQuote q) {raw pre pre' suffix suffix' : Bytes}
    (h : Scan q raw pre suffix) (h' : Scan q raw pre' suffix') :
    pre = pre' ∧ suffix = suffix' := by
  have e : some (pre, suffix) = some (pre', suffix') :=
    (untilQuote_complete quote h).symm.trans (untilQuote_complete quote h')
  simp only [Option.some.injEq, Prod.mk.injEq] at e
  exact e

/-- The unconsumed bytes are a list suffix of the input. -/
theorem Scan.isSuffix {q : UInt8} {raw pre suffix : Bytes} (h : Scan q raw pre suffix) :
    suffix <:+ raw :=
  ⟨pre, h.partition.symm⟩

/-- Scanning consumes at least the closer, so the suffix is strictly shorter. -/
theorem Scan.length_lt {q : UInt8} {raw pre suffix : Bytes} (h : Scan q raw pre suffix) :
    1 ≤ pre.length ∧ suffix.length < raw.length := by
  have hp : raw = pre ++ suffix := h.partition
  obtain ⟨body, hb⟩ := h.closer
  subst hp
  subst hb
  simp only [List.length_append, List.length_cons, List.length_nil]
  omega

/-- Consumed bytes plus the suffix account for the whole input. -/
theorem Scan.length_eq {q : UInt8} {raw pre suffix : Bytes} (h : Scan q raw pre suffix) :
    raw.length = pre.length + suffix.length := by
  rw [h.partition, List.length_append]

/-- A plain string decodes to at most its body: two delimiter bytes are dropped. -/
theorem Plain.length_le {raw out : Bytes} (h : Plain raw out) :
    out.length + 2 ≤ raw.length := by
  obtain ⟨q, body, ⟨_, rfl⟩, value⟩ := h
  have b : out.length ≤ body.length := value.length_le
  simp only [List.length_cons, List.length_append, List.length_nil]
  omega

/-- A nonempty hex body has one separator fewer than pairs at most: a separator
needs a following pair. -/
theorem HexBody.length_tight {raw out : Bytes} (h : HexBody raw out) :
    out = [] ∨ raw.length + 1 ≤ 3 * out.length := by
  induction h with
  | nil => exact Or.inl rfl
  | @pair a b raw out _ _ _ rest ih =>
    have bd : 2 * out.length ≤ raw.length ∧ raw.length ≤ 3 * out.length := rest.length_bounds
    refine Or.inr ?_
    simp only [List.length_cons]
    rcases ih with rfl | ih
    · simp only [List.length_nil] at bd ⊢
      omega
    · omega
  | @sep a b raw out _ _ ne rest ih =>
    have bd : 2 * out.length ≤ raw.length ∧ raw.length ≤ 3 * out.length := rest.length_bounds
    have pos : raw.length ≠ 0 := fun e => ne (List.eq_nil_of_length_eq_zero e)
    refine Or.inr ?_
    simp only [List.length_cons]
    rcases ih with rfl | ih
    · simp only [List.length_nil] at bd
      omega
    · omega

/-- Hex literals: two digits per byte, at most one separator per byte, five
framing bytes. The upper bound is reached only by the empty literal;
`HexLiteral.length_le_tight` gives the tight one for nonempty values. -/
theorem HexLiteral.length_bounds {raw out : Bytes} (h : HexLiteral raw out) :
    2 * out.length + 5 ≤ raw.length ∧ raw.length ≤ 3 * out.length + 5 := by
  obtain ⟨q, body, _, rfl, value⟩ := h
  have b : 2 * out.length ≤ body.length ∧ body.length ≤ 3 * out.length := value.length_bounds
  simp only [hexPrefix, quoteBytes, List.length_append, List.length_cons, List.length_nil]
  omega

/-- Tight upper bound: a nonempty hex literal of `n` bytes spells at most
`3n + 4` source bytes (`hex"00_00"` reaches it for `n = 2`). -/
theorem HexLiteral.length_le_tight {raw out : Bytes} (h : HexLiteral raw out) (ne : out ≠ []) :
    raw.length ≤ 3 * out.length + 4 := by
  obtain ⟨q, body, _, rfl, value⟩ := h
  have t : out = [] ∨ body.length + 1 ≤ 3 * out.length := value.length_tight
  rcases t with e | t
  · exact absurd e ne
  · simp only [hexPrefix, quoteBytes, List.length_append, List.length_cons, List.length_nil]
    omega

/-- Unicode literals: the decoded value never exceeds the body; nine framing bytes. -/
theorem UnicodeLiteral.length_le {raw out : Bytes} (h : UnicodeLiteral raw out) :
    out.length + 9 ≤ raw.length := by
  obtain ⟨q, body, _, rfl, _, _, value⟩ := h
  have b : out.length ≤ body.length := value.length_le
  simp only [unicodePrefix, quoteBytes, List.length_append, List.length_cons, List.length_nil]
  omega

/-- Each source fragment yields exactly one decoded value. -/
theorem Fragments.length_eq {literal : Bytes → Bytes → Prop} {raws values : List Bytes}
    (h : Fragments literal raws values) : raws.length = values.length := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp only [List.length_cons, ih]

/-- A per-fragment linear bound adds up over a fragment sequence. -/
theorem Fragments.flatten_length_le {literal : Bytes → Bytes → Prop} (a k : Nat)
    (bound : ∀ {raw out : Bytes}, literal raw out → a * out.length + k ≤ raw.length)
    {raws values : List Bytes} (h : Fragments literal raws values) :
    a * values.flatten.length + k * raws.length ≤ raws.flatten.length := by
  induction h with
  | nil => simp only [List.flatten_nil, List.length_nil, Nat.mul_zero]; omega
  | @cons raw out raws values first _ ih =>
    have b : a * out.length + k ≤ raw.length := bound first
    simp only [List.flatten_cons, List.length_append, List.length_cons, Nat.mul_add, Nat.mul_one]
    omega

/-- Concatenated plain fragments: two delimiters per fragment are dropped. -/
theorem FragmentValue.plain_length_le {raws : List Bytes} {out : Bytes}
    (h : FragmentValue Plain raws out) : out.length + 2 * raws.length ≤ raws.flatten.length := by
  obtain ⟨values, frags, rfl⟩ := h
  have e := Fragments.flatten_length_le 1 2 (fun p => by
    have := Plain.length_le p; omega) frags
  omega

/-- Concatenated hex fragments: two digits per byte, five framing bytes per fragment. -/
theorem FragmentValue.hex_length_le {raws : List Bytes} {out : Bytes}
    (h : FragmentValue HexLiteral raws out) :
    2 * out.length + 5 * raws.length ≤ raws.flatten.length := by
  obtain ⟨values, frags, rfl⟩ := h
  exact Fragments.flatten_length_le 2 5 (fun p => (HexLiteral.length_bounds p).1) frags

/-- Concatenated unicode fragments: nine framing bytes per fragment. -/
theorem FragmentValue.unicode_length_le {raws : List Bytes} {out : Bytes}
    (h : FragmentValue UnicodeLiteral raws out) :
    out.length + 9 * raws.length ≤ raws.flatten.length := by
  obtain ⟨values, frags, rfl⟩ := h
  have e := Fragments.flatten_length_le 1 9 (fun p => by
    have := UnicodeLiteral.length_le p; omega) frags
  omega

/-- Inhabited control: `hex"00_00"` reaches the tight bound. -/
example : HexLiteral [104, 101, 120, 34, 48, 48, 95, 48, 48, 34] [0, 0] :=
  ⟨34, [48, 48, 95, 48, 48], Or.inl rfl, rfl,
    .sep rfl rfl (by decide) (.pair rfl rfl (by decide) .nil)⟩

end Solidity.Frontend.LiteralGrammarH28
