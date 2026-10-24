import Solidity.Calculus.Closer.Facts

/-!
# The closer's normal forms

Normal forms of the reduction's terms.

A piece of `Calculus/Closer.lean`, whose docstring describes the whole.
-/

namespace Solidity

namespace Decide

variable {C : Contract}

/-! ## Normal forms -/

section Normal

variable {g : State C []} {ν : AEnv}

/-- The two terms are a pair the facts hold apart. -/
def Facts.apart (F : Facts C) {p : PrimTy} (a b : LTm C (.val p)) : Bool :=
  F.nes.any fun e => (a.beqR e.l && b.beqR e.r) || (a.beqR e.r && b.beqR e.l)

theorem Facts.apart_sound {F : Facts C} (hF : F.Ok g ν) {p : PrimTy} {a b : LTm C (.val p)}
    (h : F.apart a b = true) : ∃ x y, (a.eval g ν : Option p.Denote) = some x ∧
      (b.eval g ν : Option p.Denote) = some y ∧ x ≠ y := by
  obtain ⟨e, he, h⟩ := List.any_eq_true.1 h
  obtain ⟨x, y, hx, hy, hne⟩ := hF.nes e he
  obtain ⟨q, l, r⟩ := e
  simp only [Bool.or_eq_true, Bool.and_eq_true] at h
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · cases LTm.sigma_eq_of_beqR h1
    cases LTm.eq_of_beqR h2
    exact ⟨x, y, hx, hy, hne⟩
  · cases LTm.sigma_eq_of_beqR h1
    cases LTm.eq_of_beqR h2
    exact ⟨y, x, hy, hx, fun e => hne e.symm⟩

/-- Two keys compared: `some true` where they are one, `some false` where
they are apart, `none` where the facts do not tell. -/
def Facts.keyCmp (F : Facts C) {p : PrimTy} (a b : LTm C (.val p)) : Option Bool :=
  match a.litV?, b.litV? with
  | some x, some y => some (decide (x = y))
  | _, _ =>
    if a.beqR b && F.returns a then some true
    else if F.apart a b then some false
    else none

theorem Facts.keyCmp_sound {F : Facts C} (hF : F.Ok g ν) {p : PrimTy} {a b : LTm C (.val p)}
    {c : Bool} (h : F.keyCmp a b = some c) : ∃ x y, (a.eval g ν : Option p.Denote) = some x ∧
      (b.eval g ν : Option p.Denote) = some y ∧ decide (x = y) = c := by
  unfold Facts.keyCmp at h
  split at h
  · rename_i x y hx hy
    cases h
    exact ⟨x, y, LTm.eval_litV? g ν hx, LTm.eval_litV? g ν hy, rfl⟩
  · split at h
    · rename_i hb
      cases h
      simp only [Bool.and_eq_true] at hb
      cases LTm.eq_of_beqR hb.1
      obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 (F.returns_sound hF a hb.2)
      exact ⟨x, x, hx, hx, decide_eq_true rfl⟩
    · split at h
      · cases h
        obtain ⟨x, y, hx, hy, hne⟩ := F.apart_sound hF ‹_›
        exact ⟨x, y, hx, hy, decide_eq_false hne⟩
      · cases h

/-- `a = true ? true : false` at `bool`, as `a`. -/
def kiteBool? {p : PrimTy} {s : Srt} (a b : LTm C (.val p)) (t e : LTm C s) : Option (LTm C s) :=
  match p, s, a, b, t, e with
  | .bool, .val .bool, a, b, t, e => if b.isTT && t.isTT && e.isFF then some a else none
  | _, _, _, _, _, _ => none

theorem kiteBool?_eval {p : PrimTy} {s : Srt} {a b : LTm C (.val p)} {t e : LTm C s}
    {r : LTm C s} (h : kiteBool? a b t e = some r) :
    r.eval g ν = (LTm.kite a b t e).eval g ν := by
  unfold kiteBool? at h
  split at h
  · rename_i a b t e
    split at h
    · rename_i hb
      cases h
      simp only [Bool.and_eq_true] at hb
      obtain ⟨⟨hb, ht⟩, he⟩ := hb
      rw [LTm.eval_kite, LTm.isTT_eval hb, LTm.isTT_eval ht, LTm.isFF_eval he]
      cases ha : (a.eval g ν : Option Bool) with
      | none => rfl
      | some x => cases x <;> rfl
    · cases h
  · cases h

/-- A conditional on keys, its keys compared. -/
def Facts.kiteN (F : Facts C) {p : PrimTy} {s : Srt} (a b : LTm C (.val p)) (t e : LTm C s) :
    LTm C s :=
  match F.keyCmp a b with
  | some true => t
  | some false => e
  | none =>
    if t.beqR e && F.returns a && F.returns b then t
    else match kiteBool? a b t e with
      | some r => r
      | none => .kite a b t e

theorem Facts.kiteN_eval {F : Facts C} (hF : F.Ok g ν) {p : PrimTy} {s : Srt}
    (a b : LTm C (.val p)) (t e : LTm C s) :
    (F.kiteN a b t e).eval g ν = (LTm.kite a b t e).eval g ν := by
  unfold Facts.kiteN
  split
  · rename_i h
    obtain ⟨x, y, hx, hy, hc⟩ := F.keyCmp_sound hF h
    rw [LTm.eval_kite, hx, hy]
    simp only [Option.bind_some, of_decide_eq_true hc, if_true]
  · rename_i h
    obtain ⟨x, y, hx, hy, hc⟩ := F.keyCmp_sound hF h
    rw [LTm.eval_kite, hx, hy]
    simp only [Option.bind_some, of_decide_eq_false hc, if_false]
  · split
    · rename_i hb
      simp only [Bool.and_eq_true] at hb
      cases LTm.eq_of_beqR hb.1.1
      obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 (F.returns_sound hF a hb.1.2)
      obtain ⟨y, hy⟩ := Option.isSome_iff_exists.1 (F.returns_sound hF b hb.2)
      rw [LTm.eval_kite, hx, hy]
      simp only [Option.bind_some, ite_self]
    · split
      · rename_i r hr
        exact kiteBool?_eval hr
      · rfl

/-- `d; a`, the guard dropped where it returns. -/
def Facts.seqN (F : Facts C) {s' s : Srt} (d : LTm C s') (a : LTm C s) : LTm C s :=
  if F.returns d then a else if d.isErr then .err else .seq d a

theorem Facts.seqN_eval {F : Facts C} (hF : F.Ok g ν) {s' s : Srt} (d : LTm C s') (a : LTm C s) :
    (F.seqN d a).eval g ν = (LTm.seq d a).eval g ν := by
  unfold Facts.seqN
  split
  · rename_i h
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 (F.returns_sound hF d h)
    rw [LTm.eval_seq, hx]; rfl
  · split
    · rename_i h
      rw [LTm.eval_seq, LTm.eval_of_isErr g ν h]; rfl
    · rfl

/-- `a`, or `b` where it halts: `a` where it returns, `b` where it is `err`. -/
def Facts.orElseN (F : Facts C) {s : Srt} (a b : LTm C s) : LTm C s :=
  if F.returns a then a else if a.isErr then b else .orElse a b

theorem Facts.orElseN_eval {F : Facts C} (hF : F.Ok g ν) {s : Srt} (a b : LTm C s) :
    (F.orElseN a b).eval g ν = (LTm.orElse a b).eval g ν := by
  unfold Facts.orElseN
  split
  · rename_i h
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 (F.returns_sound hF a h)
    rw [LTm.eval_orElse, hx]; rfl
  · split
    · rename_i h
      rw [LTm.eval_orElse, LTm.eval_of_isErr g ν h]; rfl
    · rfl

/-- A unary symbol folded: on a literal, and `delete`'s value of a term
that returns. -/
def Facts.fold1 (F : Facts C) {a s : Srt} (o : Op1 C a s) (x : LTm C a) : LTm C s :=
  match o, x with
  | @Op1.delValue _ p, x => if F.returns x then .lit (PrimTy.dflt p) else .app1 .delValue x
  | o, x => Decide.fold1 o x

theorem Facts.fold1_eval {F : Facts C} (hF : F.Ok g ν) {a s : Srt} (o : Op1 C a s)
    (x : LTm C a) : (F.fold1 o x).eval g ν = (LTm.app1 o x).eval g ν := by
  cases o
  case delValue p =>
    simp only [Facts.fold1]
    split
    · rename_i h
      obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 (F.returns_sound hF x h)
      rw [LTm.eval_app1, hv]; rfl
    · rfl
  all_goals simp only [Facts.fold1]; exact Decide.fold1_eval g ν _ x

/-- `a < b` by ranges: `true` where the first lies below the second,
`false` where it lies at or above it. -/
def ltDec (rx ry : Int × Int) : Option Bool :=
  if rx.2 < ry.1 then some true else if ry.2 ≤ rx.1 then some false else none

/-- `a <= b` by ranges. -/
def leDec (rx ry : Int × Int) : Option Bool :=
  if rx.2 ≤ ry.1 then some true else if ry.2 < rx.1 then some false else none

theorem ltDec_sound {rx ry : Int × Int} {a b : Int} (ha : InR rx a) (hb : InR ry b) {c : Bool}
    (h : ltDec rx ry = some c) : decide (a < b) = c := by
  unfold ltDec at h
  unfold InR at ha hb
  split at h
  · cases h; exact decide_eq_true (by omega)
  · split at h
    · cases h; exact decide_eq_false (by omega)
    · cases h

theorem leDec_sound {rx ry : Int × Int} {a b : Int} (ha : InR rx a) (hb : InR ry b) {c : Bool}
    (h : leDec rx ry = some c) : decide (a ≤ b) = c := by
  unfold leDec at h
  unfold InR at ha hb
  split at h
  · cases h; exact decide_eq_true (by omega)
  · split at h
    · cases h; exact decide_eq_false (by omega)
    · cases h

/-- The operands of an addition. -/
def Op2.addArgs {a b s : Srt} (o : Op2 C a b s) (x : LTm C a) (y : LTm C b) : Option (EqF C) :=
  match o, x, y with
  | @Op2.binop _ .add p _, x, y => some ⟨p, x, y⟩
  | _, _, _ => none

/-- The operands of an addition. -/
def LTm.addArgs? {s : Srt} (t : LTm C s) : Option (EqF C) :=
  match t with
  | .app2 o x y => Op2.addArgs o x y
  | _ => none

theorem LTm.addArgs?_eq {s : Srt} {t : LTm C s} {e : EqF C} (h : t.addArgs? = some e) :
    ∃ hp : BinOp.add.accepts e.p = true,
      (⟨s, t⟩ : (s : Srt) × LTm C s) = ⟨.val e.p, .app2 (.binop .add hp) e.l e.r⟩ := by
  cases t with
  | app2 o x y =>
    cases o with
    | @binop op p hp =>
      cases op <;> simp only [LTm.addArgs?, Op2.addArgs, reduceCtorEq, Option.some.injEq] at h
      subst h
      exact ⟨hp, rfl⟩
    | _ => simp only [LTm.addArgs?, Op2.addArgs, reduceCtorEq] at h
  | _ => simp only [LTm.addArgs?, reduceCtorEq] at h

/-- A difference's operands. -/
def Op2.subArgs {a b s : Srt} (o : Op2 C a b s) (x : LTm C a) (y : LTm C b) : Option (EqF C) :=
  match o, x, y with
  | @Op2.binop _ .sub p _, x, y => some ⟨p, x, y⟩
  | _, _, _ => none

/-- The operands of a subtraction. -/
def LTm.subArgs? {s : Srt} (t : LTm C s) : Option (EqF C) :=
  match t with
  | .app2 o x y => Op2.subArgs o x y
  | _ => none

theorem LTm.subArgs?_eq {s : Srt} {t : LTm C s} {e : EqF C} (h : t.subArgs? = some e) :
    ∃ hp : BinOp.sub.accepts e.p = true,
      (⟨s, t⟩ : (s : Srt) × LTm C s) = ⟨.val e.p, .app2 (.binop .sub hp) e.l e.r⟩ := by
  cases t with
  | app2 o x y =>
    cases o with
    | @binop op p hp =>
      cases op <;> simp only [LTm.subArgs?, Op2.subArgs, reduceCtorEq, Option.some.injEq] at h
      subst h
      exact ⟨hp, rfl⟩
    | _ => simp only [LTm.subArgs?, Op2.subArgs, reduceCtorEq] at h
  | _ => simp only [LTm.subArgs?, reduceCtorEq] at h

/-- `t` at the sort `s'`, where it is that sort. -/
def LTm.castTo? {s s' : Srt} (t : LTm C s) : Option (LTm C s') :=
  if h : s = s' then some (h ▸ t) else none

theorem LTm.castTo?_eq {s s' : Srt} {t : LTm C s} {t' : LTm C s'} (h : t.castTo? = some t') :
    (⟨s, t⟩ : (s : Srt) × LTm C s) = ⟨s', t'⟩ := by
  unfold LTm.castTo? at h
  split at h
  · rename_i e
    subst e
    cases h; rfl
  · cases h

/-- The operands of a product. -/
def Op2.mulArgs {a b s : Srt} (o : Op2 C a b s) (x : LTm C a) (y : LTm C b) : Option (EqF C) :=
  match o, x, y with
  | @Op2.binop _ .mul p _, x, y => some ⟨p, x, y⟩
  | _, _, _ => none

/-- The operands of a product. -/
def LTm.mulArgs? {s : Srt} (t : LTm C s) : Option (EqF C) :=
  match t with
  | .app2 o x y => Op2.mulArgs o x y
  | _ => none

theorem LTm.mulArgs?_eq {s : Srt} {t : LTm C s} {e : EqF C} (h : t.mulArgs? = some e) :
    ∃ hp : BinOp.mul.accepts e.p = true,
      (⟨s, t⟩ : (s : Srt) × LTm C s) = ⟨.val e.p, .app2 (.binop .mul hp) e.l e.r⟩ := by
  cases t with
  | app2 o x y =>
    cases o with
    | @binop op p hp =>
      cases op <;> simp only [LTm.mulArgs?, Op2.mulArgs, reduceCtorEq, Option.some.injEq] at h
      subst h
      exact ⟨hp, rfl⟩
    | _ => simp only [LTm.mulArgs?, Op2.mulArgs, reduceCtorEq] at h
  | _ => simp only [LTm.mulArgs?, reduceCtorEq] at h

/-- `(a + b) - b`, cancelled to `a` where the sum returns. -/
def Facts.cancel (F : Facts C) {p : PrimTy} (x y : LTm C (.val p)) : Option (LTm C (.val p)) :=
  match x.addArgs? with
  | some e => if e.r.beqR y && F.returns x then e.l.castTo? else none
  | none => none

theorem ofInt?_ival_self {p : PrimTy} (hp : p.isNumeric = true) (v : p.Denote) :
    p.ofInt? (PrimTy.ival v) = some v := by
  cases p with
  | bool => cases hp
  | uint | int =>
    simp only [PrimTy.ofInt?, PrimTy.ival]
    rw [dif_pos v.2]
    rfl

theorem Facts.cancel_eval {F : Facts C} (hF : F.Ok g ν) {p : PrimTy} (hs : BinOp.sub.accepts p = true)
    {x y a : LTm C (.val p)} (h : F.cancel x y = some a) :
    (a.eval g ν : Option p.Denote) = (LTm.app2 (.binop .sub hs) x y).eval g ν := by
  unfold Facts.cancel at h
  split at h
  · rename_i e he
    split at h
    · rename_i hb
      simp only [Bool.and_eq_true] at hb
      obtain ⟨hp, hx⟩ := LTm.addArgs?_eq he
      obtain ⟨q, l, r⟩ := e
      cases hx
      cases LTm.castTo?_eq h
      cases LTm.eq_of_beqR hb.1
      obtain ⟨vx, hvx⟩ := Option.isSome_iff_exists.1 (F.returns_sound hF _ hb.2)
      have hnum : q.isNumeric = true := by
        cases q <;> first | rfl | cases hp
      rw [LTm.eval_app2] at hvx
      cases hl : (l.eval g ν : Option q.Denote) with
      | none => rw [hl] at hvx; cases hvx
      | some va =>
        rw [hl] at hvx
        have h1 : binopT .add _ va (r.eval g ν) = some vx := hvx
        unfold binopT at h1
        simp only [BinOp.shortT] at h1
        cases hr : (r.eval g ν : Option q.Denote) with
        | none => rw [hr] at h1; cases h1
        | some vb =>
          rw [hr, Option.bind_some] at h1
          have hsum := evalT_add h1
          rw [LTm.eval_app2, LTm.eval_app2, hl, hr]
          show some va = (binopT .add _ va (some vb)).bind fun z => binopT .sub _ z (some vb)
          unfold binopT
          simp only [BinOp.shortT, Option.bind_some]
          rw [h1, Option.bind_some]
          have hd : PrimTy.ival vx - PrimTy.ival vb = PrimTy.ival va := by omega
          cases q with
          | bool => cases hnum
          | uint =>
            show some va = PrimTy.uint.ofInt? (PrimTy.ival vx - PrimTy.ival vb)
            rw [hd]; exact (ofInt?_ival_self rfl va).symm
          | int =>
            show some va = PrimTy.int.ofInt? (PrimTy.ival vx - PrimTy.ival vb)
            rw [hd]; exact (ofInt?_ival_self rfl va).symm
    · cases h
  · cases h

/-- `(a - b) + b`, cancelled to `a` where the difference returns. -/
def Facts.cancelAdd (F : Facts C) {p : PrimTy} (x y : LTm C (.val p)) : Option (LTm C (.val p)) :=
  match x.subArgs? with
  | some e => if e.r.beqR y && F.returns x then e.l.castTo? else none
  | none => none

theorem Facts.cancelAdd_eval {F : Facts C} (hF : F.Ok g ν) {p : PrimTy}
    (hs : BinOp.add.accepts p = true) {x y a : LTm C (.val p)} (h : F.cancelAdd x y = some a) :
    (a.eval g ν : Option p.Denote) = (LTm.app2 (.binop .add hs) x y).eval g ν := by
  unfold Facts.cancelAdd at h
  split at h
  · rename_i e he
    split at h
    · rename_i hb
      simp only [Bool.and_eq_true] at hb
      obtain ⟨hp, hx⟩ := LTm.subArgs?_eq he
      obtain ⟨q, l, r⟩ := e
      cases hx
      cases LTm.castTo?_eq h
      cases LTm.eq_of_beqR hb.1
      obtain ⟨vx, hvx⟩ := Option.isSome_iff_exists.1 (F.returns_sound hF _ hb.2)
      have hnum : q.isNumeric = true := by
        cases q <;> first | rfl | cases hp
      rw [LTm.eval_app2] at hvx
      cases hl : (l.eval g ν : Option q.Denote) with
      | none => rw [hl] at hvx; cases hvx
      | some va =>
        rw [hl] at hvx
        have h1 : binopT .sub _ va (r.eval g ν) = some vx := hvx
        unfold binopT at h1
        simp only [BinOp.shortT] at h1
        cases hr : (r.eval g ν : Option q.Denote) with
        | none => rw [hr] at h1; cases h1
        | some vb =>
          rw [hr, Option.bind_some] at h1
          have hdiff := evalT_sub h1
          rw [LTm.eval_app2, LTm.eval_app2, hl, hr]
          show some va = (binopT .sub _ va (some vb)).bind fun z => binopT .add _ z (some vb)
          unfold binopT
          simp only [BinOp.shortT, Option.bind_some]
          rw [h1, Option.bind_some]
          have hd : PrimTy.ival vx + PrimTy.ival vb = PrimTy.ival va := by omega
          cases q with
          | bool => cases hnum
          | uint =>
            show some va = PrimTy.uint.ofInt? (PrimTy.ival vx + PrimTy.ival vb)
            rw [hd]; exact (ofInt?_ival_self rfl va).symm
          | int =>
            show some va = PrimTy.int.ofInt? (PrimTy.ival vx + PrimTy.ival vb)
            rw [hd]; exact (ofInt?_ival_self rfl va).symm
    · cases h
  · cases h

/-- `(a * k + c) / k`, cancelled to `a` at `uint` where the sum returns,
`k` and `c` literals with `c < k` (Lean only): an external function value,
packed as `address * 2^32 + selector`, read back to its address
(`docs/semantic-gaps.md`, "Function types"). -/
def Facts.cancelDiv (F : Facts C) {p : PrimTy} (x y : LTm C (.val p)) : Option (LTm C (.val p)) :=
  match x.addArgs?, y.litV? with
  | some e, some k =>
    match e.l.mulArgs?, e.r.litV? with
    | some m, some c =>
      match m.r.litV? with
      | some k' =>
        if p == .uint && PrimTy.ival k' == PrimTy.ival k && decide (0 ≤ PrimTy.ival c) &&
            decide (PrimTy.ival c < PrimTy.ival k) && F.returns x then m.l.castTo? else none
      | none => none
    | _, _ => none
  | _, _ => none

theorem Facts.cancelDiv_eval {F : Facts C} (hF : F.Ok g ν) {p : PrimTy}
    (hs : BinOp.div.accepts p = true) {x y a : LTm C (.val p)} (h : F.cancelDiv x y = some a) :
    (a.eval g ν : Option p.Denote) = (LTm.app2 (.binop .div hs) x y).eval g ν := by
  unfold Facts.cancelDiv at h
  split at h
  · rename_i e k he hk
    split at h
    · rename_i m c hm hc
      split at h
      · rename_i k' hk'
        split at h
        · rename_i hb
          simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hb
          obtain ⟨⟨⟨⟨hpu, hkk⟩, hc0⟩, hck⟩, hret⟩ := hb
          subst hpu
          obtain ⟨hp, hx⟩ := LTm.addArgs?_eq he
          obtain ⟨q, l, r⟩ := e
          cases hx
          obtain ⟨hpm, hl⟩ := LTm.mulArgs?_eq hm
          obtain ⟨q2, ml, mr⟩ := m
          cases hl
          cases LTm.castTo?_eq h
          obtain rfl := LTm.eq_of_litV? hk
          dsimp only at hk' hc hret ⊢
          have hr := LTm.eq_of_litV? hc
          have hmr := LTm.eq_of_litV? hk'
          rw [hr, hmr] at hret ⊢
          obtain ⟨vx, hvx⟩ := Option.isSome_iff_exists.1 (F.returns_sound hF _ hret)
          cases hl : (ml.eval g ν : Option PrimTy.uint.Denote) with
          | none =>
            rw [LTm.eval_app2, LTm.eval_app2, hl, Op2.eval_none_left, Op2.eval_none_left] at hvx
            cases hvx
          | some va =>
            have e1 : (LTm.app2 (Op2.binop BinOp.mul hpm) ml (LTm.lit k')).eval g ν =
                BinOp.evalT .mul hpm va k' := by
              rw [LTm.eval_app2, hl, Op2.eval_eq_evalM]; rfl
            cases hm' : (BinOp.evalT .mul hpm va k' : Option PrimTy.uint.Denote) with
            | none =>
              rw [LTm.eval_app2, e1.trans hm', Op2.eval_none_left] at hvx; cases hvx
            | some vm =>
              have e2 : (LTm.app2 (Op2.binop BinOp.add hp)
                  (LTm.app2 (Op2.binop BinOp.mul hpm) ml (LTm.lit k')) (LTm.lit c)).eval g ν =
                  BinOp.evalT .add hp vm c := by
                rw [LTm.eval_app2, e1, hm', Op2.eval_eq_evalM]; rfl
              rw [e2] at hvx
              have hmul := evalT_mul hm'
              have hadd := evalT_add hvx
              rw [LTm.eval_app2, e2, hvx, Op2.eval_eq_evalM]
              show some va = BinOp.evalT .div hs vx k
              have hva : 0 ≤ PrimTy.ival va := by
                have h2 := va.2
                simp only [PrimTy.inRange, decide_eq_true_eq] at h2
                exact h2.1
              have hk0 : PrimTy.ival k ≠ 0 := by omega
              have hq : Int.tdiv (PrimTy.ival vx) (PrimTy.ival k) = PrimTy.ival va := by
                rw [hadd, hmul, hkk, Int.tdiv_eq_ediv_of_nonneg (by
                  have : 0 ≤ PrimTy.ival va * PrimTy.ival k := Int.mul_nonneg hva (by omega)
                  omega), Int.add_comm, Int.add_mul_ediv_right _ _ hk0,
                  Int.ediv_eq_zero_of_lt hc0 hck, Int.zero_add]
              simp only [BinOp.evalT, BinOp.evalNum, BinOp.arithInt]
              show some va = (if PrimTy.ival k = 0 then none
                else some (Int.tdiv (PrimTy.ival vx) (PrimTy.ival k))).bind PrimTy.uint.ofInt?
              rw [if_neg hk0, hq, Option.bind_some]
              exact (ofInt?_ival_self rfl va).symm
        · cases h
      · cases h
    · cases h
  · cases h

/-- `x == true` as `x`, `x == false` as `!x`, at `bool`. -/
def eqBoolLit {p : PrimTy} (x y : LTm C (.val p)) : Option (LTm C (.val .bool)) :=
  match p, x, y with
  | .bool, x, y =>
    match y.litV? with
    | some v => some (if (show Bool from v) then x else .app1 (.unop .not rfl) x)
    | none => none
  | _, _, _ => none

theorem eqBoolLit_eval {p : PrimTy} {x y : LTm C (.val p)} {t : LTm C (.val .bool)}
    (h : eqBoolLit x y = some t) (hacc : BinOp.eqB.accepts p = true) :
    (t.eval g ν : Option Bool) = (LTm.app2 (.binop .eqB hacc) x y).eval g ν := by
  cases p with
  | bool =>
    simp only [eqBoolLit] at h
    split at h
    · rename_i v hv
      cases h
      obtain rfl := LTm.eq_of_litV? hv
      rw [LTm.eval_app2]
      cases hx : (x.eval g ν : Option Bool) with
      | none => cases hb : (show Bool from v) <;> simp only [hb, if_true, if_false,
          Bool.false_eq_true, LTm.eval_app1, hx] <;> rfl
      | some u =>
        have hl : ((LTm.lit (p := .bool) v).eval g ν : Option Bool) = some v := rfl
        rw [hl, Op2.eval_eq_evalM]
        simp only [Op2.evalM, Option.bind_some]
        unfold binopT
        simp only [BinOp.shortT, Option.bind_some, BinOp.evalT, BinOp.evalBool]
        cases hb : (show Bool from v) <;> cases u <;>
          simp only [hb, if_true, if_false, Bool.false_eq_true, LTm.eval_app1, hx] <;> rfl
    · cases h
  | uint | int => simp only [eqBoolLit, reduceCtorEq] at h

/-- `x < x + c`, `c` a positive literal, where the sum returns. -/
def Facts.ltSucc (F : Facts C) {p : PrimTy} (x y : LTm C (.val p)) : Bool :=
  match y.addArgs? with
  | some e => e.l.beqR x && ((e.r.litV?).map fun v => decide (0 < PrimTy.ival v)).getD false &&
      F.returns y
  | none => false

theorem Facts.ltSucc_sound {F : Facts C} (hF : F.Ok g ν) {p : PrimTy} {x y : LTm C (.val p)}
    (h : F.ltSucc x y = true) : ∃ u w, (x.eval g ν : Option p.Denote) = some u ∧
      (y.eval g ν : Option p.Denote) = some w ∧ PrimTy.ival u < PrimTy.ival w := by
  unfold Facts.ltSucc at h
  split at h
  · rename_i e he
    simp only [Bool.and_eq_true] at h
    obtain ⟨⟨hl, hc⟩, hr⟩ := h
    obtain ⟨vy, hvy⟩ := Option.isSome_iff_exists.1 (F.returns_sound hF _ hr)
    obtain ⟨hp, hy⟩ := LTm.addArgs?_eq he
    obtain ⟨q, l, r⟩ := e
    cases hy
    cases LTm.sigma_eq_of_beqR hl
    cases hlv : r.litV? with
    | none => rw [hlv] at hc; cases hc
    | some c =>
      rw [hlv] at hc
      simp only [Option.map_some, Option.getD_some, decide_eq_true_eq] at hc
      obtain rfl := LTm.eq_of_litV? hlv
      rw [LTm.eval_app2] at hvy
      cases hxv : (l.eval g ν : Option q.Denote) with
      | none => rw [hxv] at hvy; cases hvy
      | some vx =>
        rw [hxv] at hvy
        have h1 : binopT .add _ vx (some c) = some vy := hvy
        unfold binopT at h1
        simp only [BinOp.shortT, Option.bind_some] at h1
        have hs := evalT_add h1
        refine ⟨vx, vy, rfl, ?_, by omega⟩
        rw [LTm.eval_app2, hxv]
        exact hvy
  · cases h

/-- A comparison folded by its operands' ranges, where both return. -/
def Facts.cmpFold (F : Facts C) {p : PrimTy} (dec : Int × Int → Int × Int → Option Bool)
    (x y : LTm C (.val p)) : Option Bool :=
  if F.returns x && F.returns y then dec (F.range x) (F.range y) else none

/-- The literal `2`. -/
def isTwo {p : PrimTy} (x : LTm C (.val p)) : Bool :=
  match x.litV? with
  | some v => PrimTy.ival v == 2
  | none => false

/-- `2 * y` is `y + y`: both check the one integer `2·y` against the
range. -/
theorem evalT_two_mul {p : PrimTy} {x : LTm C (.val p)} (hx : isTwo x = true)
    (hm : BinOp.mul.accepts p = true) (y : LTm C (.val p)) :
    (LTm.app2 (.binop .add hm) y y).eval g ν = (LTm.app2 (.binop .mul hm) x y).eval g ν := by
  unfold isTwo at hx
  split at hx
  · rename_i v hv
    obtain rfl := LTm.eq_of_litV? hv
    rw [LTm.eval_app2, LTm.eval_app2]
    have hl : ((LTm.lit v : LTm C (.val p)).eval g ν : Option p.Denote) = some v := rfl
    rw [hl, Op2.eval_eq_evalM, Op2.eval_eq_evalM]
    simp only [Op2.evalM, Option.bind_some]
    cases hy : (y.eval g ν : Option p.Denote) with
    | none =>
      unfold binopT
      cases p <;> simp only [BinOp.shortT, Option.bind_none] <;> rfl
    | some w =>
      simp only [Option.bind_some]
      unfold binopT
      cases p with
      | bool => cases hm
      | uint | int =>
        have h2 : v.1 = 2 := by simpa only [PrimTy.ival, beq_iff_eq] using hx
        simp only [BinOp.shortT, Option.bind_some, BinOp.evalT, BinOp.evalNum, BinOp.arithInt, h2]
        rw [show w.1 + w.1 = 2 * w.1 by omega]
  · cases hx

end Normal

end Decide

end Solidity
