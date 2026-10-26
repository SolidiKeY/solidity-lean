import Solidity.Calculus.AutoComplete
import Solidity.Calculus.LedgerArithmetic

/-!
# The ledger cut maps the source fragment into the cut one

On the lifted source fragment with ledger reads (`LTm.SrcL false w .pre`:
`net(a)`, its address a scalar), the ledger cut (`LFml.ledgerCut`,
`Calculus/LedgerCut.lean`) leaves a formula of the fragment with reads at
constants only (`.post`), every address reads no ledger (`LFml.netOK`), and
the reads are no more than the nodes (`LFml.ledgerCut_src`).  A scalar or
a path of the fragment reads no ledger at all (`LTm.SrcL.remode`): only a
KeY `int` does, and a Boolean through a comparison.
-/

namespace Solidity.Decide

open Semantics ReadRealization Linear ScalarCode

variable {C : Contract}

/-- **A scalar or a path reads no ledger**, and is in every ledger mode. -/
theorem LTm.SrcL.remode {w : Bool} {l l' : LedgerMode} :
    ∀ {k : SrcKind} {s : Srt} {t : LTm C s}, t.SrcL false w l k → (k = .num ∨ k = .path) →
      t.SrcL false w l' k ∧ t.netFree = true := by
  intro k s t h
  induction h with
  | kite hc => cases hc
  | ite hc => cases hc
  | var i => intro _; exact ⟨.var i, rfl⟩
  | lit v => intro _; exact ⟨.lit v, rfl⟩
  | env e => intro _; exact ⟨.env e, rfl⟩
  | err => intro _; exact ⟨.err, rfl⟩
  | root r h => intro _; exact ⟨.root r h, rfl⟩
  | add h _ _ iha ihb =>
    intro _; obtain ⟨a1, a2⟩ := iha (.inl rfl); obtain ⟨b1, b2⟩ := ihb (.inl rfl)
    exact ⟨.add h a1 b1, by simp only [LTm.netFree, a2, b2, Bool.and_self]⟩
  | sub h _ _ iha ihb =>
    intro _; obtain ⟨a1, a2⟩ := iha (.inl rfl); obtain ⟨b1, b2⟩ := ihb (.inl rfl)
    exact ⟨.sub h a1 b1, by simp only [LTm.netFree, a2, b2, Bool.and_self]⟩
  | mulL h v _ ih =>
    intro _; obtain ⟨b1, b2⟩ := ih (.inl rfl)
    exact ⟨.mulL h v b1, by simp only [LTm.netFree, b2, Bool.and_self]⟩
  | mulR h v _ ih =>
    intro _; obtain ⟨a1, a2⟩ := ih (.inl rfl)
    exact ⟨.mulR h v a1, by simp only [LTm.netFree, a2, Bool.and_self]⟩
  | neg h _ ih =>
    intro _; obtain ⟨a1, a2⟩ := ih (.inl rfl)
    exact ⟨.neg h a1, by simp only [LTm.netFree, Op1.isNetB, a2, Bool.not_false, Bool.and_self]⟩
  | bnot h _ ih =>
    intro _; obtain ⟨a1, a2⟩ := ih (.inl rfl)
    exact ⟨.bnot h a1, by simp only [LTm.netFree, Op1.isNetB, a2, Bool.not_false, Bool.and_self]⟩
  | toInt hw h _ ih =>
    intro _; obtain ⟨a1, a2⟩ := ih (.inl rfl)
    exact ⟨.toInt hw h a1, by simp only [LTm.netFree, Op1.isNetB, a2, Bool.not_false, Bool.and_self]⟩
  | toUint hw h _ ih =>
    intro _; obtain ⟨a1, a2⟩ := ih (.inl rfl)
    exact ⟨.toUint hw h a1, by simp only [LTm.netFree, Op1.isNetB, a2, Bool.not_false, Bool.and_self]⟩
  | divL hw h v hv _ ih =>
    intro _; obtain ⟨a1, a2⟩ := ih (.inl rfl)
    exact ⟨.divL hw h v hv a1, by simp only [LTm.netFree, a2, Bool.and_self]⟩
  | modL hw h v hv _ ih =>
    intro _; obtain ⟨a1, a2⟩ := ih (.inl rfl)
    exact ⟨.modL hw h v hv a1, by simp only [LTm.netFree, a2, Bool.and_self]⟩
  | shrL hw h v _ ih =>
    intro _; obtain ⟨a1, a2⟩ := ih (.inl rfl)
    exact ⟨.shrL hw h v a1, by simp only [LTm.netFree, a2, Bool.and_self]⟩
  | shlL hw h v _ ih =>
    intro _; obtain ⟨a1, a2⟩ := ih (.inl rfl)
    exact ⟨.shlL hw h v a1, by simp only [LTm.netFree, a2, Bool.and_self]⟩
  | bandR hw h v hv _ ih =>
    intro _; obtain ⟨a1, a2⟩ := ih (.inl rfl)
    exact ⟨.bandR hw h v hv a1, by simp only [LTm.netFree, a2, Bool.and_self]⟩
  | bandL hw h v hv _ ih =>
    intro _; obtain ⟨b1, b2⟩ := ih (.inl rfl)
    exact ⟨.bandL hw h v hv b1, by simp only [LTm.netFree, b2, Bool.and_self]⟩
  | litR hw op h v hv _ ih =>
    intro _; obtain ⟨a1, a2⟩ := ih (.inl rfl)
    exact ⟨.litR hw op h v hv a1, by simp only [LTm.netFree, a2, Bool.and_self]⟩
  | litL hw op h v hv _ ih =>
    intro _; obtain ⟨b1, b2⟩ := ih (.inl rfl)
    exact ⟨.litL hw op h v hv b1, by simp only [LTm.netFree, b2, Bool.and_self]⟩
  | addW hw h _ _ iha ihb =>
    intro _; obtain ⟨a1, a2⟩ := iha (.inl rfl); obtain ⟨b1, b2⟩ := ihb (.inl rfl)
    exact ⟨.addW hw h a1 b1, by simp only [LTm.netFree, a2, b2, Bool.and_self]⟩
  | subW hw h _ _ iha ihb =>
    intro _; obtain ⟨a1, a2⟩ := iha (.inl rfl); obtain ⟨b1, b2⟩ := ihb (.inl rfl)
    exact ⟨.subW hw h a1 b1, by simp only [LTm.netFree, a2, b2, Bool.and_self]⟩
  | seq _ _ ihd iha =>
    intro _; obtain ⟨d1, d2⟩ := ihd (.inl rfl); obtain ⟨a1, a2⟩ := iha (.inl rfl)
    exact ⟨.seq d1 a1, by simp only [LTm.netFree, d2, a2, Bool.and_self]⟩
  | word _ ih =>
    intro _; obtain ⟨q1, q2⟩ := ih (.inr rfl)
    exact ⟨.word q1, by simp only [LTm.netFree, q2]⟩
  | field h _ ih =>
    intro _; obtain ⟨q1, q2⟩ := ih (.inr rfl)
    exact ⟨.field h q1, by simp only [LTm.netFree, Op1.isNetB, q2, Bool.not_false, Bool.and_self]⟩
  | key _ _ ihq ihk =>
    intro _; obtain ⟨q1, q2⟩ := ihq (.inr rfl); obtain ⟨k1, k2⟩ := ihk (.inl rfl)
    exact ⟨.key q1 k1, by simp only [LTm.netFree, q2, k2, Bool.and_self]⟩
  | _ => intro hk; rcases hk with hk | hk <;> cases hk

/-- A scalar term of the fragment is cut as itself, reading no ledger. -/
theorem LTm.SrcL.netCut_num {w : Bool} {k : SrcKind} {s : Srt} {t : LTm C s}
    (h : t.SrcL false w .pre k) (hk : k = .num ∨ k = .path) (n : Nat) :
    (t.netCut n).1.SrcL false w .post k ∧ (∀ a ∈ t.netReads, a.SrcL false w .post .num) ∧
      t.netOK = true := by
  obtain ⟨h', hf⟩ := h.remode (l' := .post) hk
  have hok : t.netOK = true := by
    have key : ∀ {s : Srt} (u : LTm C s), u.netFree = true → u.netOK = true := by
      intro s u hu
      induction u with
      | var | app0 | err => rfl
      | app1 o a ih =>
        simp only [LTm.netFree, Bool.and_eq_true, Bool.not_eq_true'] at hu
        simp only [LTm.netOK, ih hu.2, hu.1, Bool.not_false, Bool.true_or, Bool.and_self]
      | app2 o a b iha ihb | index it a b iha ihb | seq a b iha ihb | orElse a b iha ihb =>
        simp only [LTm.netFree, Bool.and_eq_true] at hu
        simp only [LTm.netOK, iha hu.1, ihb hu.2, Bool.and_self]
      | app3 o a b c iha ihb ihc =>
        simp only [LTm.netFree, Bool.and_eq_true] at hu
        simp only [LTm.netOK, iha hu.1.1, ihb hu.1.2, ihc hu.2, Bool.and_self]
      | obsW a ih | obsL a ih | obsH a ih => exact ih hu
      | kite a b t e iha ihb iht ihe =>
        simp only [LTm.netFree, Bool.and_eq_true] at hu
        simp only [LTm.netOK, iha hu.1.1.1, ihb hu.1.1.2, iht hu.1.2, ihe hu.2, Bool.and_self]
    exact key t hf
  rw [LTm.netCut_of_netFree t hf, LTm.netReads_of_netFree t hf]
  exact ⟨h', (fun _ h => nomatch h), hok⟩

/-- **The cut of a term of the fragment with ledger reads is in the
fragment with reads at constants**, and so is every address it reads. -/
theorem LTm.SrcL.netCut {w : Bool} : ∀ {k : SrcKind} {s : Srt} {t : LTm C s},
    t.SrcL false w .pre k → ∀ n, (t.netCut n).1.SrcL false w .post k ∧
      (∀ a ∈ t.netReads, a.SrcL false w .post .num) ∧ t.netOK = true := by
  intro k s t h
  induction h with
  | kite hc => cases hc
  | ite hc => cases hc
  | znetLit hl => cases hl
  | zseq hl => cases hl
  | var i => exact LTm.SrcL.netCut_num (.var i) (.inl rfl)
  | lit v => exact LTm.SrcL.netCut_num (.lit v) (.inl rfl)
  | env e => exact LTm.SrcL.netCut_num (.env e) (.inl rfl)
  | err => exact LTm.SrcL.netCut_num .err (.inl rfl)
  | root r h => exact LTm.SrcL.netCut_num (.root r h) (.inr rfl)
  | add h ha hb => exact LTm.SrcL.netCut_num (.add h ha hb) (.inl rfl)
  | sub h ha hb => exact LTm.SrcL.netCut_num (.sub h ha hb) (.inl rfl)
  | mulL h v hb => exact LTm.SrcL.netCut_num (.mulL h v hb) (.inl rfl)
  | mulR h v ha => exact LTm.SrcL.netCut_num (.mulR h v ha) (.inl rfl)
  | neg h ha => exact LTm.SrcL.netCut_num (.neg h ha) (.inl rfl)
  | bnot h ha => exact LTm.SrcL.netCut_num (.bnot h ha) (.inl rfl)
  | toInt hw h ha => exact LTm.SrcL.netCut_num (.toInt hw h ha) (.inl rfl)
  | toUint hw h ha => exact LTm.SrcL.netCut_num (.toUint hw h ha) (.inl rfl)
  | divL hw h v hv ha => exact LTm.SrcL.netCut_num (.divL hw h v hv ha) (.inl rfl)
  | modL hw h v hv ha => exact LTm.SrcL.netCut_num (.modL hw h v hv ha) (.inl rfl)
  | shrL hw h v ha => exact LTm.SrcL.netCut_num (.shrL hw h v ha) (.inl rfl)
  | shlL hw h v ha => exact LTm.SrcL.netCut_num (.shlL hw h v ha) (.inl rfl)
  | bandR hw h v hv ha => exact LTm.SrcL.netCut_num (.bandR hw h v hv ha) (.inl rfl)
  | bandL hw h v hv hb => exact LTm.SrcL.netCut_num (.bandL hw h v hv hb) (.inl rfl)
  | litR hw op h v hv ha => exact LTm.SrcL.netCut_num (.litR hw op h v hv ha) (.inl rfl)
  | litL hw op h v hv hb => exact LTm.SrcL.netCut_num (.litL hw op h v hv hb) (.inl rfl)
  | addW hw h ha hb => exact LTm.SrcL.netCut_num (.addW hw h ha hb) (.inl rfl)
  | subW hw h ha hb => exact LTm.SrcL.netCut_num (.subW hw h ha hb) (.inl rfl)
  | seq hd ha => exact LTm.SrcL.netCut_num (.seq hd ha) (.inl rfl)
  | word hq => exact LTm.SrcL.netCut_num (.word hq) (.inl rfl)
  | field h hq => exact LTm.SrcL.netCut_num (.field h hq) (.inr rfl)
  | key hq hk => exact LTm.SrcL.netCut_num (.key hq hk) (.inr rfl)
  | ofNum ht =>
    intro n
    obtain ⟨h1, h2, h3⟩ := LTm.SrcL.netCut_num ht (.inl rfl) n
    exact ⟨.ofNum h1, h2, h3⟩
  | @not a _ ih =>
    intro n
    obtain ⟨h1, h2, h3⟩ := ih n
    refine ⟨.not h1, fun x hx => h2 x ?_, ?_⟩
    · simpa only [LTm.netReads, read1, List.append_nil] using hx
    · simp only [LTm.netOK, h3, Op1.isNetB, Bool.not_false, Bool.true_or, Bool.and_self]
  | @and a b _ _ iha ihb | @or a b _ _ iha ihb | @eqB a b _ _ iha ihb | @neB a b _ _ iha ihb =>
    intro n
    obtain ⟨a1, a2, a3⟩ := iha n
    obtain ⟨b1, b2, b3⟩ := ihb (a.netCut n).2
    first
    | exact ⟨.and a1 b1, fun x hx => (List.mem_append.1 hx).elim (a2 x) (b2 x),
        by simp only [LTm.netOK, a3, b3, Bool.and_self]⟩
    | exact ⟨.or a1 b1, fun x hx => (List.mem_append.1 hx).elim (a2 x) (b2 x),
        by simp only [LTm.netOK, a3, b3, Bool.and_self]⟩
    | exact ⟨.eqB a1 b1, fun x hx => (List.mem_append.1 hx).elim (a2 x) (b2 x),
        by simp only [LTm.netOK, a3, b3, Bool.and_self]⟩
    | exact ⟨.neB a1 b1, fun x hx => (List.mem_append.1 hx).elim (a2 x) (b2 x),
        by simp only [LTm.netOK, a3, b3, Bool.and_self]⟩
  | @eqN p hp a b ha hb _ _ =>
    intro n
    obtain ⟨a1, a2, a3⟩ := LTm.SrcL.netCut_num ha (.inl rfl) n
    obtain ⟨b1, b2, b3⟩ := LTm.SrcL.netCut_num hb (.inl rfl) (a.netCut n).2
    exact ⟨.eqN hp a1 b1, fun x hx => (List.mem_append.1 hx).elim (a2 x) (b2 x),
      by simp only [LTm.netOK, a3, b3, Bool.and_self]⟩
  | @neN p hp a b ha hb _ _ =>
    intro n
    obtain ⟨a1, a2, a3⟩ := LTm.SrcL.netCut_num ha (.inl rfl) n
    obtain ⟨b1, b2, b3⟩ := LTm.SrcL.netCut_num hb (.inl rfl) (a.netCut n).2
    exact ⟨.neN hp a1 b1, fun x hx => (List.mem_append.1 hx).elim (a2 x) (b2 x),
      by simp only [LTm.netOK, a3, b3, Bool.and_self]⟩
  | @lt p h a b ha hb _ _ | @gt p h a b ha hb _ _ | @le p h a b ha hb _ _ | @ge p h a b ha hb _ _ =>
    intro n
    obtain ⟨a1, a2, a3⟩ := LTm.SrcL.netCut_num ha (.inl rfl) n
    obtain ⟨b1, b2, b3⟩ := LTm.SrcL.netCut_num hb (.inl rfl) (a.netCut n).2
    first
    | exact ⟨.lt h a1 b1, fun x hx => (List.mem_append.1 hx).elim (a2 x) (b2 x),
        by simp only [LTm.netOK, a3, b3, Bool.and_self]⟩
    | exact ⟨.gt h a1 b1, fun x hx => (List.mem_append.1 hx).elim (a2 x) (b2 x),
        by simp only [LTm.netOK, a3, b3, Bool.and_self]⟩
    | exact ⟨.le h a1 b1, fun x hx => (List.mem_append.1 hx).elim (a2 x) (b2 x),
        by simp only [LTm.netOK, a3, b3, Bool.and_self]⟩
    | exact ⟨.ge h a1 b1, fun x hx => (List.mem_append.1 hx).elim (a2 x) (b2 x),
        by simp only [LTm.netOK, a3, b3, Bool.and_self]⟩
  | @seqB d a _ _ ihd iha =>
    intro n
    obtain ⟨d1, d2, d3⟩ := ihd n
    obtain ⟨a1, a2, a3⟩ := iha (d.netCut n).2
    exact ⟨.seqB d1 a1, fun x hx => (List.mem_append.1 hx).elim (d2 x) (a2 x),
      by simp only [LTm.netOK, d3, a3, Bool.and_self]⟩
  | @seqN q hq d a hd _ _ iha =>
    intro n
    obtain ⟨d1, d2, d3⟩ := LTm.SrcL.netCut_num hd (.inl rfl) n
    obtain ⟨a1, a2, a3⟩ := iha (d.netCut n).2
    exact ⟨.seqN hq d1 a1, fun x hx => (List.mem_append.1 hx).elim (d2 x) (a2 x),
      by simp only [LTm.netOK, d3, a3, Bool.and_self]⟩
  | zlit c => intro n; exact ⟨.zlit c, (fun _ h => nomatch h), rfl⟩
  | @zint a ha =>
    intro n
    obtain ⟨a1, a2, a3⟩ := LTm.SrcL.netCut_num ha (.inl rfl) n
    refine ⟨.zint a1, fun x hx => a2 x ?_, ?_⟩
    · simpa only [LTm.netReads, read1, List.append_nil] using hx
    · simp only [LTm.netOK, a3, Op1.isNetB, Bool.not_false, Bool.true_or, Bool.and_self]
  | @zadd h a b _ _ iha ihb | @zsub h a b _ _ iha ihb =>
    intro n
    obtain ⟨a1, a2, a3⟩ := iha n
    obtain ⟨b1, b2, b3⟩ := ihb (a.netCut n).2
    first
    | exact ⟨.zadd h a1 b1, fun x hx => (List.mem_append.1 hx).elim (a2 x) (b2 x),
        by simp only [LTm.netOK, a3, b3, Bool.and_self]⟩
    | exact ⟨.zsub h a1 b1, fun x hx => (List.mem_append.1 hx).elim (a2 x) (b2 x),
        by simp only [LTm.netOK, a3, b3, Bool.and_self]⟩
  | @zcmp op h a b _ _ iha ihb =>
    intro n
    obtain ⟨a1, a2, a3⟩ := iha n
    obtain ⟨b1, b2, b3⟩ := ihb (a.netCut n).2
    exact ⟨.zcmp op h a1 b1, fun x hx => (List.mem_append.1 hx).elim (a2 x) (b2 x),
      by simp only [LTm.netOK, a3, b3, Bool.and_self]⟩
  | @zmulL h c b _ ih =>
    intro n
    obtain ⟨b1, b2, b3⟩ := ih n
    exact ⟨.zmulL h c b1, fun x hx => b2 x (by simpa only [LTm.netReads, List.nil_append] using hx),
      by simp only [LTm.netOK, b3, Bool.and_self]⟩
  | @zmulR h a c _ ih =>
    intro n
    obtain ⟨a1, a2, a3⟩ := ih n
    exact ⟨.zmulR h c a1, fun x hx => a2 x (by simpa only [LTm.netReads, List.append_nil] using hx),
      by simp only [LTm.netOK, a3, Bool.and_self]⟩
  | @znet hl a ha _ =>
    intro n
    obtain ⟨a1, af⟩ := ha.remode (l' := .post) (.inl rfl)
    have hc : a.netCut n = (a, n) := LTm.netCut_of_netFree a af n
    have hr : a.netReads = [] := LTm.netReads_of_netFree a af
    refine ⟨?_, fun x hx => ?_, ?_⟩
    · show (cutNet1 .net (a.netCut n).1 (a.netCut n).2).1.SrcL false w .post .znum
      rw [hc]
      exact .zseq rfl a1 (.znetLit rfl _)
    · simp only [LTm.netReads, hr, read1, List.nil_append, List.mem_singleton] at hx
      subst hx
      exact a1
    · obtain ⟨-, -, hok⟩ := LTm.SrcL.netCut_num ha (.inl rfl) n
      simp only [LTm.netOK, hok, af, Bool.or_true, Bool.and_self]

theorem LFml.netCut_of_netFree (φ : LFml C) (h : φ.netFree = true) (n : Nat) :
    φ.netCut n = (φ, n) := by
  induction φ generalizing n with
  | tt | all => rfl
  | eq a b =>
    simp only [LFml.netFree, Bool.and_eq_true] at h
    simp only [LFml.netCut, LTm.netCut_of_netFree a h.1, LTm.netCut_of_netFree b h.2]
  | not φ ih => simp only [LFml.netCut, ih h]
  | and φ ψ ihφ ihψ | imp φ ψ ihφ ihψ =>
    simp only [LFml.netFree, Bool.and_eq_true] at h
    simp only [LFml.netCut, ihφ h.1, ihψ h.2]

/-- **The cut of a formula of the fragment with ledger reads**, and its reads. -/
theorem LFml.SrcL.netCut : ∀ {φ : LFml C}, φ.SrcL false true .pre →
    ∀ n, (φ.netCut n).1.SrcL false true .post ∧
      (∀ a ∈ φ.netReads, a.SrcL false true .post .num) ∧ φ.netOK = true := by
  intro φ h
  induction h with
  | tt => intro n; exact ⟨.tt, (fun _ h => nomatch h), rfl⟩
  | @eqB a b ha hb =>
    intro n
    obtain ⟨a1, a2, a3⟩ := LTm.SrcL.netCut ha n
    obtain ⟨b1, b2, b3⟩ := LTm.SrcL.netCut hb (a.netCut n).2
    exact ⟨.eqB a1 b1, fun x hx => (List.mem_append.1 hx).elim (a2 x) (b2 x),
      by simp only [LFml.netOK, a3, b3, Bool.and_self]⟩
  | @eqN p hp a b ha hb =>
    intro n
    obtain ⟨a1, a2, a3⟩ := LTm.SrcL.netCut ha n
    obtain ⟨b1, b2, b3⟩ := LTm.SrcL.netCut hb (a.netCut n).2
    exact ⟨.eqN hp a1 b1, fun x hx => (List.mem_append.1 hx).elim (a2 x) (b2 x),
      by simp only [LFml.netOK, a3, b3, Bool.and_self]⟩
  | not _ ih =>
    intro n
    obtain ⟨h1, h2, h3⟩ := ih n
    exact ⟨.not h1, h2, h3⟩
  | @and φ ψ _ _ ihφ ihψ =>
    intro n
    obtain ⟨a1, a2, a3⟩ := ihφ n
    obtain ⟨b1, b2, b3⟩ := ihψ (φ.netCut n).2
    exact ⟨.and a1 b1, fun x hx => (List.mem_append.1 hx).elim (a2 x) (b2 x),
      by simp only [LFml.netOK, a3, b3, Bool.and_self]⟩
  | @imp φ ψ _ _ ihφ ihψ =>
    intro n
    obtain ⟨a1, a2, a3⟩ := ihφ n
    obtain ⟨b1, b2, b3⟩ := ihψ (φ.netCut n).2
    exact ⟨.imp a1 b1, fun x hx => (List.mem_append.1 hx).elim (a2 x) (b2 x),
      by simp only [LFml.netOK, a3, b3, Bool.and_self]⟩
  | defDiv hw => cases hw
  | defDivI hw => cases hw
  | defShr hw => cases hw
  | defAddW hw => cases hw
  | defSubW hw => cases hw
  | defToInt hw => cases hw
  | defToUint hw => cases hw

theorem LFml.conj_srcL {c w : Bool} {l : LedgerMode} {ds : List (LFml C)}
    (h : ∀ d ∈ ds, d.SrcL c w l) : (LFml.conj ds).SrcL c w l := by
  induction ds with
  | nil => exact .tt
  | cons d ds ih =>
    cases ds with
    | nil => exact h d List.mem_cons_self
    | cons e es =>
      exact .and (h d List.mem_cons_self) (ih (fun x hx => h x (List.mem_cons_of_mem _ hx)))

/-- The consistency of the reads is in the fragment with reads at constants. -/
theorem netCons_src {w : Bool} {rs : List (LTm C (.val .uint))}
    (h : ∀ a ∈ rs, a.SrcL false w .post .num) : (netCons rs).SrcL false w .post := by
  have hg : ∀ i, (rs.getD i .err).SrcL false w .post .num := by
    intro i
    rw [List.getD_eq_getElem?_getD]
    cases hi : rs[i]? with
    | none => exact .err
    | some x => exact h x (List.mem_of_getElem? hi)
  apply LFml.conj_srcL
  intro d hd
  simp only [netPairs, List.mem_flatMap, List.mem_map] at hd
  obtain ⟨j, -, i, -, rfl⟩ := hd
  exact .imp (.eqN rfl (hg i) (hg j))
    (.eqB (.zcmp .eqB rfl (.znetLit rfl _) (.znetLit rfl _)) (.ofNum (.lit (p := .bool) true)))

/-- **The ledger cut of a leaf of the fragment is in the fragment with reads
at constants**, and its reads' addresses read no ledger. -/
theorem LFml.ledgerCut_src {φ : LFml C} (h : φ.SrcL false true .pre) :
    φ.ledgerCut.SrcL false true .post ∧ φ.netOK = true := by
  obtain ⟨h1, h2, h3⟩ := LFml.SrcL.netCut h 0
  refine ⟨?_, h3⟩
  unfold LFml.ledgerCut
  split
  · rename_i he
    have hf := LFml.netFree_of_reads φ h3 (List.isEmpty_iff.1 he)
    rw [LFml.netCut_of_netFree φ hf] at h1
    exact h1
  · exact .imp (netCons_src h2) h1

end Solidity.Decide
