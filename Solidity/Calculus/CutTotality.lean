import Solidity.Calculus.FlattenTotality

/-!
# The cut leaves no operator outside the compilers' fragment

`LFml.cutAll` (`Calculus/QuotientCut.lean`) maps the source fragment with
its cut operators (`LTm.Src false true`) into the fragment without them
(`LTm.Src false false`), every defining equation of a fresh atom in the
shapes the compiler encodes (`LFml.Src.defDiv` …); so the flattener and the
compilers never refuse a cut leaf within the size bounds
(`flattenedArithmetic?_isSome`).
-/

namespace Solidity.Decide

open Semantics ReadRealization

variable {C : Contract}


theorem defs_append {P : LFml C → Prop} {ds es : List (LFml C)} (h1 : ∀ d ∈ ds, P d)
    (h2 : ∀ d ∈ es, P d) : ∀ d ∈ ds ++ es, P d :=
  fun d hd => (List.mem_append.mp hd).elim (h1 d) (h2 d)

theorem defs_single {P : LFml C → Prop} {d : LFml C} (h : P d) : ∀ e ∈ [d], P e :=
  fun e he => List.mem_singleton.mp he ▸ h

theorem LFml.defn_src {p r : PrimTy} (hp : p.isNumeric = true) {g : LTm C (.val p)}
    {e : LTm C (.val r)} {m : Nat} (hg : g.Src false false .num)
    (he : (LFml.eq e (.var m)).Src false false) : (LFml.defn g e m).Src false false :=
  .imp (.eqN hp hg hg) he

theorem quotAtom_mem {p r : PrimTy} {prev ds : List (LFml C)} {g : LTm C (.val p)}
    {e : LTm C (.val r)} {m : Nat} {d : LFml C} (h : d ∈ (quotAtom prev ds g e m).2.1) :
    d ∈ ds ∨ d = LFml.defn g e m := by
  unfold quotAtom at h
  split at h
  · exact .inl h
  · rcases List.mem_append.mp h with h | h
    · exact .inl h
    · exact .inr (List.mem_singleton.mp h)

theorem quotAtom_src {p r : PrimTy} {prev ds : List (LFml C)} {g : LTm C (.val p)}
    {e : LTm C (.val r)} {m : Nat} (hds : ∀ d ∈ ds, d.Src false false)
    (hd : (LFml.defn g e m).Src false false) : ∀ d ∈ (quotAtom prev ds g e m).2.1, d.Src false false :=
  fun d h => (quotAtom_mem h).elim (hds d) (fun h => h ▸ hd)

theorem maskCut_src {prev ds : List (LFml C)} {a : LTm C (.val .uint)} {k m : Nat}
    (ha : a.Src false false .num) (hds : ∀ d ∈ ds, d.Src false false) :
    (maskCut prev a k ds m).term.Src false false .num ∧
      ∀ d ∈ (maskCut prev a k ds m).defs, d.Src false false := by
  unfold maskCut
  split
  · rename_i hk
    have hpos : (uintPow k hk).val ≠ 0 := by
      show ((2 ^ k : Nat) : Int) ≠ 0
      have := Nat.two_pow_pos k; omega
    exact ⟨.sub rfl ha (.mulR rfl _ (.var _)),
      quotAtom_src hds (LFml.defn_src rfl ha (.defDiv rfl rfl _ hpos _ ha))⟩
  · exact ⟨ha, hds⟩

/-- **The cut of a source term is in the fragment without cut operators**, and so
is every definition it makes. -/
theorem LTm.cut_src : ∀ {k : SrcKind} {s : Srt} {t : LTm C s}, t.Src false true k → ∀ prev n,
    (t.cut prev n).term.Src false false k ∧ ∀ d ∈ (t.cut prev n).defs, d.Src false false := by
  intro k s t h
  induction h with
  | kite hc => cases hc
  | ite hc => cases hc
  | var i => intro _ _; exact ⟨.var i, fun _ h => nomatch h⟩
  | lit v => intro _ _; exact ⟨.lit v, fun _ h => nomatch h⟩
  | env e => intro _ _; exact ⟨.env e, fun _ h => nomatch h⟩
  | err => intro _ _; exact ⟨.err, fun _ h => nomatch h⟩
  | root r h => intro _ _; exact ⟨.root r h, fun _ h => nomatch h⟩
  | ofNum _ ih => intro prev n; obtain ⟨h1, h2⟩ := ih prev n; exact ⟨.ofNum h1, h2⟩
  | @word p q _ ih => intro prev n; obtain ⟨h1, h2⟩ := ih prev n; exact ⟨.word h1, h2⟩
  | @field sn f T h q _ ih => intro prev n; obtain ⟨h1, h2⟩ := ih prev n; exact ⟨.field h h1, h2⟩
  | @key K V q i _ _ ihq ihi =>
    intro prev n
    obtain ⟨h1, h2⟩ := ihq prev n
    obtain ⟨h3, h4⟩ := ihi (prev ++ (q.cut prev n).defs) (q.cut prev n).next
    exact ⟨.key h1 h3, defs_append h2 h4⟩
  | @seq q p d a _ _ ihd iha =>
    intro prev n
    obtain ⟨h1, h2⟩ := ihd prev n
    obtain ⟨h3, h4⟩ := iha (prev ++ (d.cut prev n).defs) (d.cut prev n).next
    exact ⟨.seq h1 h3, defs_append h2 h4⟩
  | @seqB d a _ _ ihd iha =>
    intro prev n
    obtain ⟨h1, h2⟩ := ihd prev n
    obtain ⟨h3, h4⟩ := iha (prev ++ (d.cut prev n).defs) (d.cut prev n).next
    exact ⟨.seqB h1 h3, defs_append h2 h4⟩
  | @seqN q hq d a _ _ ihd iha =>
    intro prev n
    obtain ⟨h1, h2⟩ := ihd prev n
    obtain ⟨h3, h4⟩ := iha (prev ++ (d.cut prev n).defs) (d.cut prev n).next
    exact ⟨.seqN hq h1 h3, defs_append h2 h4⟩
  | @neg h a _ ih =>
    intro prev n
    obtain ⟨h1, h2⟩ := ih prev n
    show (cut1 (.unop .neg h) prev (a.cut prev n)).term.Src false false .num ∧
      ∀ d ∈ (cut1 (.unop .neg h) prev (a.cut prev n)).defs, d.Src false false
    rw [cut1_default h (by decide) prev]
    exact ⟨.neg h h1, h2⟩
  | @bnot h a _ ih =>
    intro prev n
    obtain ⟨h1, h2⟩ := ih prev n
    show (cut1 (.unop .bnot h) prev (a.cut prev n)).term.Src false false .num ∧
      ∀ d ∈ (cut1 (.unop .bnot h) prev (a.cut prev n)).defs, d.Src false false
    rw [cut1_default h (by decide) prev]
    exact ⟨.bnot h h1, h2⟩
  | @not a _ ih =>
    intro prev n
    obtain ⟨h1, h2⟩ := ih prev n
    show (cut1 (.unop .not rfl) prev (a.cut prev n)).term.Src false false .bool ∧
      ∀ d ∈ (cut1 (.unop .not rfl) prev (a.cut prev n)).defs, d.Src false false
    rw [cut1_default rfl (by decide) prev]
    exact ⟨.not h1, h2⟩
  | @toInt _ h a _ ih =>
    intro prev n
    obtain ⟨h1, h2⟩ := ih prev n
    exact ⟨.seq h1 (.var _), quotAtom_src h2 (LFml.defn_src rfl h1 (.defToInt rfl h _ h1))⟩
  | @toUint _ h a _ ih =>
    intro prev n
    obtain ⟨h1, h2⟩ := ih prev n
    exact ⟨.seq h1 (.var _), quotAtom_src h2 (LFml.defn_src rfl h1 (.defToUint rfl h _ h1))⟩
  | @divL _ h a v hv _ ih =>
    intro prev n
    obtain ⟨h1, h2⟩ := ih prev n
    show (cut2 (.binop .div h) prev (a.cut prev n) ⟨.app0 (.lit v), [], (a.cut prev n).next⟩).term.Src false false .num ∧
      ∀ d ∈ (cut2 (.binop .div h) prev (a.cut prev n) ⟨.app0 (.lit v), [], (a.cut prev n).next⟩).defs, d.Src false false
    simp only [cut2, if_neg hv]
    exact ⟨.seq h1 (.var _), quotAtom_src (defs_append h2 (fun _ h => nomatch h))
      (LFml.defn_src rfl h1 (.defDiv rfl h v hv _ h1))⟩
  | @modL _ h a v hv _ ih =>
    intro prev n
    obtain ⟨h1, h2⟩ := ih prev n
    show (cut2 (.binop .mod h) prev (a.cut prev n) ⟨.app0 (.lit v), [], (a.cut prev n).next⟩).term.Src false false .num ∧
      ∀ d ∈ (cut2 (.binop .mod h) prev (a.cut prev n) ⟨.app0 (.lit v), [], (a.cut prev n).next⟩).defs, d.Src false false
    simp only [cut2, if_neg hv]
    exact ⟨.sub rfl h1 (.mulR rfl v (.var _)), quotAtom_src (defs_append h2 (fun _ h => nomatch h))
      (LFml.defn_src rfl h1 (.defDiv rfl rfl v hv _ h1))⟩
  | @shrL _ p h a v _ ih =>
    intro prev n
    obtain ⟨h1, h2⟩ := ih prev n
    have hp : p.isNumeric = true := by cases p <;> first | rfl | cases h
    show (cut2 (.binop .shr h) prev (a.cut prev n) ⟨.app0 (.lit v), [], (a.cut prev n).next⟩).term.Src false false .num ∧
      ∀ d ∈ (cut2 (.binop .shr h) prev (a.cut prev n) ⟨.app0 (.lit v), [], (a.cut prev n).next⟩).defs, d.Src false false
    simp only [cut2]
    exact ⟨.seq h1 (.var _), quotAtom_src (defs_append h2 (fun _ h => nomatch h))
      (LFml.defn_src hp h1 (.defShr rfl h v _ h1))⟩
  | @shlL _ h a v _ ih =>
    intro prev n
    obtain ⟨h1, h2⟩ := ih prev n
    show (cut2 (.binop .shl h) prev (a.cut prev n) ⟨.app0 (.lit v), [], (a.cut prev n).next⟩).term.Src false false .num ∧
      ∀ d ∈ (cut2 (.binop .shl h) prev (a.cut prev n) ⟨.app0 (.lit v), [], (a.cut prev n).next⟩).defs, d.Src false false
    simp only [cut2, cutShl]
    have h2' := defs_append h2 (fun _ (h : _ ∈ ([] : List (LFml C))) => nomatch h)
    split
    · exact ⟨h1, h2'⟩
    · split
      · rename_i h0 hk
        have hpos : (uintPow (256 - v.val.toNat) (by have := uint_val_nonneg v; omega)).val ≠ 0 := by
          show ((2 ^ (256 - v.val.toNat) : Nat) : Int) ≠ 0
          have := Nat.two_pow_pos (256 - v.val.toNat); omega
        exact ⟨.mulR rfl _ (.sub rfl h1 (.mulR rfl _ (.var _))),
          quotAtom_src h2' (LFml.defn_src rfl h1 (.defDiv rfl rfl _ hpos _ h1))⟩
      · exact ⟨.seq h1 (.lit _), h2'⟩
  | @bandR _ h a v hm _ ih =>
    intro prev n
    obtain ⟨h1, h2⟩ := ih prev n
    obtain ⟨k, hk⟩ := Option.isSome_iff_exists.mp hm
    show (cut2 (.binop .band h) prev (a.cut prev n) ⟨.app0 (.lit v), [], (a.cut prev n).next⟩).term.Src false false .num ∧
      ∀ d ∈ (cut2 (.binop .band h) prev (a.cut prev n) ⟨.app0 (.lit v), [], (a.cut prev n).next⟩).defs, d.Src false false
    have hmk : (LTm.app0 (C := C) (.lit v)).maskOf? = some k := hk
    show (cutBand prev h (a.cut prev n) ⟨.app0 (.lit v), [], (a.cut prev n).next⟩).term.Src false false .num ∧
      ∀ d ∈ (cutBand prev h (a.cut prev n) ⟨.app0 (.lit v), [], (a.cut prev n).next⟩).defs, d.Src false false
    rw [cutBand_right (B := ⟨.app0 (.lit v), [], (a.cut prev n).next⟩) hmk]
    exact maskCut_src h1 (defs_append h2 (fun _ h => nomatch h))
  | @bandL _ h v hm b _ ih =>
    intro prev n
    obtain ⟨h3, h4⟩ := ih (prev ++ []) n
    obtain ⟨k, hk⟩ := Option.isSome_iff_exists.mp hm
    show (cut2 (.binop .band h) prev ⟨.app0 (.lit v), [], n⟩ (b.cut (prev ++ []) n)).term.Src false false .num ∧
      ∀ d ∈ (cut2 (.binop .band h) prev ⟨.app0 (.lit v), [], n⟩ (b.cut (prev ++ []) n)).defs, d.Src false false
    have hmk : (LTm.app0 (C := C) (.lit v)).maskOf? = some k := hk
    show (cutBand prev h ⟨.app0 (.lit v), [], n⟩ (b.cut (prev ++ []) n)).term.Src false false .num ∧
      ∀ d ∈ (cutBand prev h ⟨.app0 (.lit v), [], n⟩ (b.cut (prev ++ []) n)).defs, d.Src false false
    cases hbk : (b.cut (prev ++ []) n).term.maskOf? with
    | some j =>
      rw [cutBand_right (A := ⟨.app0 (.lit v), [], n⟩) hbk]
      exact maskCut_src (.lit v) (defs_append (fun _ h => nomatch h) h4)
    | none =>
      rw [cutBand_left (A := ⟨.app0 (.lit v), [], n⟩) hbk hmk]
      exact maskCut_src h3 (defs_append (fun _ h => nomatch h) h4)
  | @addW _ h a b _ _ iha ihb =>
    intro prev n
    obtain ⟨h1, h2⟩ := iha prev n
    obtain ⟨h3, h4⟩ := ihb (prev ++ (a.cut prev n).defs) (a.cut prev n).next
    exact ⟨.seq (.seq h1 h3) (.var _), quotAtom_src (defs_append h2 h4)
      (LFml.defn_src rfl (.seq h1 h3) (.defAddW rfl h _ h1 h3))⟩
  | @subW _ h a b _ _ iha ihb =>
    intro prev n
    obtain ⟨h1, h2⟩ := iha prev n
    obtain ⟨h3, h4⟩ := ihb (prev ++ (a.cut prev n).defs) (a.cut prev n).next
    exact ⟨.seq (.seq h1 h3) (.var _), quotAtom_src (defs_append h2 h4)
      (LFml.defn_src rfl (.seq h1 h3) (.defSubW rfl h _ h1 h3))⟩
  | @add p h a b _ _ iha ihb =>
    intro prev n
    obtain ⟨h1, h2⟩ := iha prev n
    obtain ⟨h3, h4⟩ := ihb (prev ++ (a.cut prev n).defs) (a.cut prev n).next
    show (cut2 (.binop _ h) prev (a.cut prev n) (b.cut (prev ++ (a.cut prev n).defs) (a.cut prev n).next)).term.Src false false .num ∧
      ∀ d ∈ (cut2 (.binop _ h) prev (a.cut prev n) (b.cut (prev ++ (a.cut prev n).defs) (a.cut prev n).next)).defs, d.Src false false
    rw [cut2_default h (by decide) prev]
    exact ⟨.add h h1 h3, defs_append h2 h4⟩
  | @sub p h a b _ _ iha ihb =>
    intro prev n
    obtain ⟨h1, h2⟩ := iha prev n
    obtain ⟨h3, h4⟩ := ihb (prev ++ (a.cut prev n).defs) (a.cut prev n).next
    show (cut2 (.binop _ h) prev (a.cut prev n) (b.cut (prev ++ (a.cut prev n).defs) (a.cut prev n).next)).term.Src false false .num ∧
      ∀ d ∈ (cut2 (.binop _ h) prev (a.cut prev n) (b.cut (prev ++ (a.cut prev n).defs) (a.cut prev n).next)).defs, d.Src false false
    rw [cut2_default h (by decide) prev]
    exact ⟨.sub h h1 h3, defs_append h2 h4⟩
  | @mulL p h v b _ ihb =>
    intro prev n
    obtain ⟨h3, h4⟩ := ihb (prev ++ []) n
    show (cut2 (.binop .mul h) prev ⟨.app0 (.lit v), [], n⟩ (b.cut (prev ++ []) n)).term.Src false false .num ∧
      ∀ d ∈ (cut2 (.binop .mul h) prev ⟨.app0 (.lit v), [], n⟩ (b.cut (prev ++ []) n)).defs, d.Src false false
    rw [cut2_default h (by decide) prev]
    exact ⟨.mulL h v h3, defs_append (fun _ h => nomatch h) h4⟩
  | @mulR p h a v _ iha =>
    intro prev n
    obtain ⟨h1, h2⟩ := iha prev n
    show (cut2 (.binop .mul h) prev (a.cut prev n) ⟨.app0 (.lit v), [], (a.cut prev n).next⟩).term.Src false false .num ∧
      ∀ d ∈ (cut2 (.binop .mul h) prev (a.cut prev n) ⟨.app0 (.lit v), [], (a.cut prev n).next⟩).defs, d.Src false false
    rw [cut2_default h (by decide) prev]
    exact ⟨.mulR h v h1, defs_append h2 (fun _ h => nomatch h)⟩
  | @and a b _ _ iha ihb =>
    intro prev n
    obtain ⟨h1, h2⟩ := iha prev n
    obtain ⟨h3, h4⟩ := ihb (prev ++ (a.cut prev n).defs) (a.cut prev n).next
    show (cut2 (.binop _ rfl) prev (a.cut prev n) (b.cut (prev ++ (a.cut prev n).defs) (a.cut prev n).next)).term.Src false false .bool ∧
      ∀ d ∈ (cut2 (.binop _ rfl) prev (a.cut prev n) (b.cut (prev ++ (a.cut prev n).defs) (a.cut prev n).next)).defs, d.Src false false
    rw [cut2_default rfl (by decide) prev]
    exact ⟨.and h1 h3, defs_append h2 h4⟩
  | @or a b _ _ iha ihb =>
    intro prev n
    obtain ⟨h1, h2⟩ := iha prev n
    obtain ⟨h3, h4⟩ := ihb (prev ++ (a.cut prev n).defs) (a.cut prev n).next
    show (cut2 (.binop _ rfl) prev (a.cut prev n) (b.cut (prev ++ (a.cut prev n).defs) (a.cut prev n).next)).term.Src false false .bool ∧
      ∀ d ∈ (cut2 (.binop _ rfl) prev (a.cut prev n) (b.cut (prev ++ (a.cut prev n).defs) (a.cut prev n).next)).defs, d.Src false false
    rw [cut2_default rfl (by decide) prev]
    exact ⟨.or h1 h3, defs_append h2 h4⟩
  | @eqB a b _ _ iha ihb =>
    intro prev n
    obtain ⟨h1, h2⟩ := iha prev n
    obtain ⟨h3, h4⟩ := ihb (prev ++ (a.cut prev n).defs) (a.cut prev n).next
    show (cut2 (.binop _ rfl) prev (a.cut prev n) (b.cut (prev ++ (a.cut prev n).defs) (a.cut prev n).next)).term.Src false false .bool ∧
      ∀ d ∈ (cut2 (.binop _ rfl) prev (a.cut prev n) (b.cut (prev ++ (a.cut prev n).defs) (a.cut prev n).next)).defs, d.Src false false
    rw [cut2_default rfl (by decide) prev]
    exact ⟨.eqB h1 h3, defs_append h2 h4⟩
  | @neB a b _ _ iha ihb =>
    intro prev n
    obtain ⟨h1, h2⟩ := iha prev n
    obtain ⟨h3, h4⟩ := ihb (prev ++ (a.cut prev n).defs) (a.cut prev n).next
    show (cut2 (.binop _ rfl) prev (a.cut prev n) (b.cut (prev ++ (a.cut prev n).defs) (a.cut prev n).next)).term.Src false false .bool ∧
      ∀ d ∈ (cut2 (.binop _ rfl) prev (a.cut prev n) (b.cut (prev ++ (a.cut prev n).defs) (a.cut prev n).next)).defs, d.Src false false
    rw [cut2_default rfl (by decide) prev]
    exact ⟨.neB h1 h3, defs_append h2 h4⟩
  | @eqN p hp a b _ _ iha ihb =>
    intro prev n
    obtain ⟨h1, h2⟩ := iha prev n
    obtain ⟨h3, h4⟩ := ihb (prev ++ (a.cut prev n).defs) (a.cut prev n).next
    show (cut2 (.binop _ rfl) prev (a.cut prev n) (b.cut (prev ++ (a.cut prev n).defs) (a.cut prev n).next)).term.Src false false .bool ∧
      ∀ d ∈ (cut2 (.binop _ rfl) prev (a.cut prev n) (b.cut (prev ++ (a.cut prev n).defs) (a.cut prev n).next)).defs, d.Src false false
    rw [cut2_default rfl (by decide) prev]
    exact ⟨.eqN hp h1 h3, defs_append h2 h4⟩
  | @neN p hp a b _ _ iha ihb =>
    intro prev n
    obtain ⟨h1, h2⟩ := iha prev n
    obtain ⟨h3, h4⟩ := ihb (prev ++ (a.cut prev n).defs) (a.cut prev n).next
    show (cut2 (.binop _ rfl) prev (a.cut prev n) (b.cut (prev ++ (a.cut prev n).defs) (a.cut prev n).next)).term.Src false false .bool ∧
      ∀ d ∈ (cut2 (.binop _ rfl) prev (a.cut prev n) (b.cut (prev ++ (a.cut prev n).defs) (a.cut prev n).next)).defs, d.Src false false
    rw [cut2_default rfl (by decide) prev]
    exact ⟨.neN hp h1 h3, defs_append h2 h4⟩
  | @lt p h a b _ _ iha ihb =>
    intro prev n
    obtain ⟨h1, h2⟩ := iha prev n
    obtain ⟨h3, h4⟩ := ihb (prev ++ (a.cut prev n).defs) (a.cut prev n).next
    show (cut2 (.binop _ h) prev (a.cut prev n) (b.cut (prev ++ (a.cut prev n).defs) (a.cut prev n).next)).term.Src false false .bool ∧
      ∀ d ∈ (cut2 (.binop _ h) prev (a.cut prev n) (b.cut (prev ++ (a.cut prev n).defs) (a.cut prev n).next)).defs, d.Src false false
    rw [cut2_default h (by decide) prev]
    exact ⟨.lt h h1 h3, defs_append h2 h4⟩
  | @gt p h a b _ _ iha ihb =>
    intro prev n
    obtain ⟨h1, h2⟩ := iha prev n
    obtain ⟨h3, h4⟩ := ihb (prev ++ (a.cut prev n).defs) (a.cut prev n).next
    show (cut2 (.binop _ h) prev (a.cut prev n) (b.cut (prev ++ (a.cut prev n).defs) (a.cut prev n).next)).term.Src false false .bool ∧
      ∀ d ∈ (cut2 (.binop _ h) prev (a.cut prev n) (b.cut (prev ++ (a.cut prev n).defs) (a.cut prev n).next)).defs, d.Src false false
    rw [cut2_default h (by decide) prev]
    exact ⟨.gt h h1 h3, defs_append h2 h4⟩
  | @le p h a b _ _ iha ihb =>
    intro prev n
    obtain ⟨h1, h2⟩ := iha prev n
    obtain ⟨h3, h4⟩ := ihb (prev ++ (a.cut prev n).defs) (a.cut prev n).next
    show (cut2 (.binop _ h) prev (a.cut prev n) (b.cut (prev ++ (a.cut prev n).defs) (a.cut prev n).next)).term.Src false false .bool ∧
      ∀ d ∈ (cut2 (.binop _ h) prev (a.cut prev n) (b.cut (prev ++ (a.cut prev n).defs) (a.cut prev n).next)).defs, d.Src false false
    rw [cut2_default h (by decide) prev]
    exact ⟨.le h h1 h3, defs_append h2 h4⟩
  | @ge p h a b _ _ iha ihb =>
    intro prev n
    obtain ⟨h1, h2⟩ := iha prev n
    obtain ⟨h3, h4⟩ := ihb (prev ++ (a.cut prev n).defs) (a.cut prev n).next
    show (cut2 (.binop _ h) prev (a.cut prev n) (b.cut (prev ++ (a.cut prev n).defs) (a.cut prev n).next)).term.Src false false .bool ∧
      ∀ d ∈ (cut2 (.binop _ h) prev (a.cut prev n) (b.cut (prev ++ (a.cut prev n).defs) (a.cut prev n).next)).defs, d.Src false false
    rw [cut2_default h (by decide) prev]
    exact ⟨.ge h h1 h3, defs_append h2 h4⟩

/-- **The cut of a source formula is in the fragment without cut operators.** -/
theorem LFml.cut_src : ∀ {φ : LFml C}, φ.Src false true → ∀ prev n,
    (φ.cut prev n).formula.Src false false ∧ ∀ d ∈ (φ.cut prev n).defs, d.Src false false := by
  intro φ h
  induction h with
  | tt => intro _ _; exact ⟨.tt, fun _ h => nomatch h⟩
  | @eqB a b ha hb =>
    intro prev n
    obtain ⟨h1, h2⟩ := LTm.cut_src ha prev n
    obtain ⟨h3, h4⟩ := LTm.cut_src hb (prev ++ (a.cut prev n).defs) (a.cut prev n).next
    exact ⟨.eqB h1 h3, defs_append h2 h4⟩
  | @eqN p hp a b ha hb =>
    intro prev n
    obtain ⟨h1, h2⟩ := LTm.cut_src ha prev n
    obtain ⟨h3, h4⟩ := LTm.cut_src hb (prev ++ (a.cut prev n).defs) (a.cut prev n).next
    exact ⟨.eqN hp h1 h3, defs_append h2 h4⟩
  | @not φ _ ih => intro prev n; obtain ⟨h1, h2⟩ := ih prev n; exact ⟨.not h1, h2⟩
  | @and φ ψ _ _ ihφ ihψ =>
    intro prev n
    obtain ⟨h1, h2⟩ := ihφ prev n
    obtain ⟨h3, h4⟩ := ihψ (prev ++ (φ.cut prev n).defs) (φ.cut prev n).next
    exact ⟨.and h1 h3, defs_append h2 h4⟩
  | @imp φ ψ _ _ ihφ ihψ =>
    intro prev n
    obtain ⟨h1, h2⟩ := ihφ prev n
    obtain ⟨h3, h4⟩ := ihψ (prev ++ (φ.cut prev n).defs) (φ.cut prev n).next
    exact ⟨.imp h1 h3, defs_append h2 h4⟩
  | defDiv hw => cases hw
  | defShr hw => cases hw
  | defAddW hw => cases hw
  | defSubW hw => cases hw
  | defToInt hw => cases hw
  | defToUint hw => cases hw

theorem LFml.conj_src {ds : List (LFml C)} (h : ∀ d ∈ ds, d.Src false false) :
    (LFml.conj ds).Src false false := by
  induction ds with
  | nil => exact .tt
  | cons d ds ih =>
    cases ds with
    | nil => exact h d List.mem_cons_self
    | cons e es =>
      exact .and (h d List.mem_cons_self) (ih (fun x hx => h x (List.mem_cons_of_mem _ hx)))

/-- **The cut leaf is in the fragment the flattener and compilers take.** -/
theorem LFml.cutAll_src {φ : LFml C} (h : φ.Src false true) : φ.cutAll.Src false false := by
  obtain ⟨h1, h2⟩ := LFml.cut_src h [] φ.atomBound
  unfold LFml.cutAll
  split
  · exact h1
  · exact .imp (LFml.conj_src h2) h1

/-- **The leaf decision never refuses its fragment** (`flattenedArithmetic?`):
a source leaf whose cut has at most 511 nodes and 45 storage reads. -/
theorem flattenedArithmetic?_isSome (φ : LFml C) (h : φ.Src false true)
    (hn : φ.cutAll.nodes ≤ 511) (hw : φ.cutAll.words * φ.cutAll.words ≤ 2048) :
    (flattenedArithmetic? 2048 φ).isSome = true := by
  obtain ⟨src, hsrc⟩ := h.readFormula
  obtain ⟨r, hr, hsq, hE⟩ := readFlatten?_arith φ.cutAll (LFml.cutAll_src h) hn hw
  obtain ⟨E, hE'⟩ := Option.isSome_iff_exists.mp hE
  simp only [flattenedArithmetic?, hsrc, hr, Option.bind_eq_bind, Option.bind_some, hsq, if_true, hE']
  rfl

end Solidity.Decide
