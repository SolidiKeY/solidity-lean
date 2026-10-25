import Solidity.Calculus.LiftTotality
import Solidity.Calculus.CutTotality

/-!
# Completeness of the automatic decision on a stated fragment

`dependentReduction?` (`Calculus/DependentReduction.lean`) decides a formula
exactly once it returns a certificate.  This module states when it does:
`Fml.inExact` is the fragment, `dependentReduction?_isSome` the totality and
`auto_complete` the end-to-end statement, with `auto_countermodel` for a
`false` verdict.

The fragment is checked on the eliminated leaf (`leafOf?`: the source leaf
after exact program normalization, update pushing, read elimination and
the folding of trivial conditionals).  Its universal prefix binds every
atom of its body, its body is in `LFml.Src true` (`LFml.src?` recognizes
it), the elimination's conditionals allowed, of lifting weight below the
fuel; lifting then removes them (`LFml.liftedExact_lift`).  Two size bounds
hold on the lifted body (`Fml.exactBounded`): at most 511 nodes and 45
storage reads (the flattener's node budget, the compilers' depth fuel and
the alias-pair budget, `Calculus/FlattenTotality.lean`).  From the leaf on
every stage is proved total; the stages above it
(`ProgramNormalization.ofFormula?`, `sourceReduction?`, `LTm.elim`) are run
by `leafOf?`, not characterized syntactically (`docs/automation.md`, M4,
says what blocks it).

The recognizer is `match`-based, as are the recognizers it mirrors
(`ReadExpr.ofTerm?`, `flattenFuel?`); the term sizes and weights
(`LTm.nodes`, `LTm.words`, `LTm.conds`) too.
-/

namespace Solidity.Decide

open Semantics ReadRealization Linear ScalarCode

variable {C : Contract}

/-! ## Recognizing the source fragment -/

/-- A product with a literal factor, recognized with its evidence from the
factors' (`sa`, `sb`). -/
def LTm.mulSrc? {c w : Bool} {p : PrimTy} (h : BinOp.mul.accepts p = true) (a b : LTm C (.val p))
    (sa : Option (PLift (a.Src c w .num))) (sb : Option (PLift (b.Src c w .num))) :
    Option (PLift ((LTm.app2 (.binop .mul h) a b).Src c w .num)) :=
  match a.lit?, b.lit? with
  | some ⟨v, hv⟩, _ => sb.map fun ⟨hb⟩ => ⟨by subst hv; exact .mulL h v hb⟩
  | none, some ⟨v, hv⟩ => sa.map fun ⟨ha⟩ => ⟨by subst hv; exact .mulR h v ha⟩
  | none, none => none

theorem LTm.mulSrc?_left {c w : Bool} {p : PrimTy} (h : BinOp.mul.accepts p = true) (v : p.Denote)
    (b : LTm C (.val p)) (sa : Option (PLift ((LTm.app0 (C := C) (.lit v)).Src c w .num)))
    (sb : Option (PLift (b.Src c w .num))) (hb : sb.isSome = true) :
    (LTm.mulSrc? h (.app0 (.lit v)) b sa sb).isSome = true := by
  obtain ⟨x, rfl⟩ := Option.isSome_iff_exists.mp hb
  rfl

theorem LTm.mulSrc?_right {c w : Bool} {p : PrimTy} (h : BinOp.mul.accepts p = true)
    (a : LTm C (.val p)) (v : p.Denote) (sa : Option (PLift (a.Src c w .num)))
    (sb : Option (PLift ((LTm.app0 (C := C) (.lit v)).Src c w .num))) (ha : sa.isSome = true)
    (hb : sb.isSome = true) :
    (LTm.mulSrc? h a (.app0 (.lit v)) sa sb).isSome = true := by
  obtain ⟨x, rfl⟩ := Option.isSome_iff_exists.mp ha
  obtain ⟨y, rfl⟩ := Option.isSome_iff_exists.mp hb
  unfold LTm.mulSrc?
  cases hl : a.lit? with
  | some r => obtain ⟨w, hw⟩ := r; rfl
  | none => rfl

/-- A literal low mask on the left of `&`. -/
def LTm.bandLSrc? {c : Bool} (h : BinOp.band.accepts .uint = true) (a b : LTm C (.val .uint))
    (sb : Option (PLift (b.Src c true .num))) :
    Option (PLift ((LTm.app2 (.binop .band h) a b).Src c true .num)) :=
  match a.lit? with
  | some ⟨v, hv⟩ =>
    if hm : (lowMask? v).isSome = true then sb.map fun ⟨hb⟩ => ⟨by subst hv; exact .bandL rfl h v hm hb⟩
    else none
  | none => none

/-- A literal low mask on either side of `&`, recognized with its evidence. -/
def LTm.bandSrc? {c : Bool} (h : BinOp.band.accepts .uint = true) (a b : LTm C (.val .uint))
    (sa : Option (PLift (a.Src c true .num))) (sb : Option (PLift (b.Src c true .num))) :
    Option (PLift ((LTm.app2 (.binop .band h) a b).Src c true .num)) :=
  match b.lit? with
  | some ⟨v, hv⟩ =>
    if hm : (lowMask? v).isSome = true then sa.map fun ⟨ha⟩ => ⟨by subst hv; exact .bandR rfl h v hm ha⟩
    else LTm.bandLSrc? h a b sb
  | none => LTm.bandLSrc? h a b sb

theorem LTm.bandLSrc?_isSome {c : Bool} (h : BinOp.band.accepts .uint = true) (v : PrimTy.uint.Denote)
    (hm : (lowMask? v).isSome = true) (b : LTm C (.val .uint)) (sb : Option (PLift (b.Src c true .num)))
    (hb : sb.isSome = true) : (LTm.bandLSrc? h (.app0 (.lit v)) b sb).isSome = true := by
  obtain ⟨x, rfl⟩ := Option.isSome_iff_exists.mp hb
  unfold LTm.bandLSrc?
  dsimp only [LTm.lit?]
  rw [dif_pos hm]
  rfl

/-- The source fragment, recognized with its evidence. -/
def LTm.src? : (c : Bool) → (k : SrcKind) → {s : Srt} → (t : LTm C s) → Option (PLift (t.Src c true k))
  | _, k, _, .var (p := p) i =>
    match k, p with
    | .num, _ => some ⟨.var i⟩
    | .bool, .bool => some ⟨.ofNum (.var i)⟩
    | _, _ => none
  | _, k, _, .app0 o =>
    match k, o with
    | .num, .lit v => some ⟨.lit v⟩
    | .bool, .lit (p := .bool) v => some ⟨.ofNum (.lit v)⟩
    | .num, .env e => some ⟨.env e⟩
    | .path, .root r h => some ⟨.root r h⟩
    | _, _ => none
  | _, k, s, .err =>
    match k, s with
    | .num, .val _ => some ⟨.err⟩
    | .bool, .val .bool => some ⟨.ofNum .err⟩
    | _, _ => none
  | c, k, _, .obsW (p := p) q =>
    match k, p with
    | .num, _ => (q.src? c .path).map fun ⟨h⟩ => ⟨.word h⟩
    | .bool, .bool => (q.src? c .path).map fun ⟨h⟩ => ⟨.ofNum (.word h)⟩
    | _, _ => none
  | c, k, _, .app1 (.unop op (p := p) hop) a =>
    match k, op, p with
    | .bool, .not, .bool => (a.src? c .bool).map fun ⟨h⟩ => ⟨.not h⟩
    | .num, .neg, .int => (a.src? c .num).map fun ⟨h⟩ => ⟨.neg hop h⟩
    | .num, .bnot, .uint => (a.src? c .num).map fun ⟨h⟩ => ⟨.bnot hop h⟩
    | .num, .toInt, .uint => (a.src? c .num).map fun ⟨h⟩ => ⟨.toInt rfl hop h⟩
    | .num, .toUint, .int => (a.src? c .num).map fun ⟨h⟩ => ⟨.toUint rfl hop h⟩
    | _, _, _ => none
  | c, k, _, .app1 (.field h) q =>
    match k with
    | .path => (q.src? c .path).map fun ⟨hq⟩ => ⟨.field h hq⟩
    | _ => none
  | c, .path, _, .index .map q i => do
    let ⟨hq⟩ ← q.src? c .path
    let ⟨hk⟩ ← i.src? c .num
    return ⟨.key hq hk⟩
  | c, k, _, .app2 (.binop op (p := p) h) a b =>
    match k, op, p with
    | .num, .add, _ => do
      let ⟨ha⟩ ← a.src? c .num
      let ⟨hb⟩ ← b.src? c .num
      return ⟨.add h ha hb⟩
    | .num, .sub, _ => do
      let ⟨ha⟩ ← a.src? c .num
      let ⟨hb⟩ ← b.src? c .num
      return ⟨.sub h ha hb⟩
    | .num, .mul, _ => LTm.mulSrc? h a b (a.src? c .num) (b.src? c .num)
    | .num, .div, .uint =>
      match b with
      | .app0 (.lit v) =>
        if hv : v.val = 0 then none else (a.src? c .num).map fun ⟨ha⟩ => ⟨.divL rfl h v hv ha⟩
      | _ => none
    | .num, .mod, .uint =>
      match b with
      | .app0 (.lit v) =>
        if hv : v.val = 0 then none else (a.src? c .num).map fun ⟨ha⟩ => ⟨.modL rfl h v hv ha⟩
      | _ => none
    | .num, .shr, _ =>
      match b with
      | .app0 (.lit v) => (a.src? c .num).map fun ⟨ha⟩ => ⟨.shrL rfl h v ha⟩
      | _ => none
    | .num, .shl, .uint =>
      match b with
      | .app0 (.lit v) => (a.src? c .num).map fun ⟨ha⟩ => ⟨.shlL rfl h v ha⟩
      | _ => none
    | .num, .band, .uint => LTm.bandSrc? h a b (a.src? c .num) (b.src? c .num)
    | .num, .addW, .uint => do
      let ⟨ha⟩ ← a.src? c .num
      let ⟨hb⟩ ← b.src? c .num
      return ⟨.addW rfl h ha hb⟩
    | .num, .subW, .uint => do
      let ⟨ha⟩ ← a.src? c .num
      let ⟨hb⟩ ← b.src? c .num
      return ⟨.subW rfl h ha hb⟩
    | .bool, .and, .bool => do
      let ⟨ha⟩ ← a.src? c .bool
      let ⟨hb⟩ ← b.src? c .bool
      return ⟨.and ha hb⟩
    | .bool, .or, .bool => do
      let ⟨ha⟩ ← a.src? c .bool
      let ⟨hb⟩ ← b.src? c .bool
      return ⟨.or ha hb⟩
    | .bool, .eqB, .bool => do
      let ⟨ha⟩ ← a.src? c .bool
      let ⟨hb⟩ ← b.src? c .bool
      return ⟨.eqB ha hb⟩
    | .bool, .neB, .bool => do
      let ⟨ha⟩ ← a.src? c .bool
      let ⟨hb⟩ ← b.src? c .bool
      return ⟨.neB ha hb⟩
    | .bool, .eqB, .uint => do
      let ⟨ha⟩ ← a.src? c .num
      let ⟨hb⟩ ← b.src? c .num
      return ⟨.eqN rfl ha hb⟩
    | .bool, .eqB, .int => do
      let ⟨ha⟩ ← a.src? c .num
      let ⟨hb⟩ ← b.src? c .num
      return ⟨.eqN rfl ha hb⟩
    | .bool, .neB, .uint => do
      let ⟨ha⟩ ← a.src? c .num
      let ⟨hb⟩ ← b.src? c .num
      return ⟨.neN rfl ha hb⟩
    | .bool, .neB, .int => do
      let ⟨ha⟩ ← a.src? c .num
      let ⟨hb⟩ ← b.src? c .num
      return ⟨.neN rfl ha hb⟩
    | .bool, .lt, _ => do
      let ⟨ha⟩ ← a.src? c .num
      let ⟨hb⟩ ← b.src? c .num
      return ⟨.lt h ha hb⟩
    | .bool, .gt, _ => do
      let ⟨ha⟩ ← a.src? c .num
      let ⟨hb⟩ ← b.src? c .num
      return ⟨.gt h ha hb⟩
    | .bool, .le, _ => do
      let ⟨ha⟩ ← a.src? c .num
      let ⟨hb⟩ ← b.src? c .num
      return ⟨.le h ha hb⟩
    | .bool, .ge, _ => do
      let ⟨ha⟩ ← a.src? c .num
      let ⟨hb⟩ ← b.src? c .num
      return ⟨.ge h ha hb⟩
    | _, _, _ => none
  | c, k, s, .seq (s' := s') d a =>
    match k, s', s with
    | .num, .val _, .val _ => do
      let ⟨hd⟩ ← d.src? c .num
      let ⟨ha⟩ ← a.src? c .num
      return ⟨.seq hd ha⟩
    | .bool, .val .bool, .val .bool => do
      let ⟨hd⟩ ← d.src? c .bool
      let ⟨ha⟩ ← a.src? c .bool
      return ⟨.seqB hd ha⟩
    | .bool, .val .uint, .val .bool => do
      let ⟨hd⟩ ← d.src? c .num
      let ⟨ha⟩ ← a.src? c .bool
      return ⟨.seqN rfl hd ha⟩
    | .bool, .val .int, .val .bool => do
      let ⟨hd⟩ ← d.src? c .num
      let ⟨ha⟩ ← a.src? c .bool
      return ⟨.seqN rfl hd ha⟩
    | _, _, _ => none
  | c, k, _, .kite (s := .val _) x y t e =>
    match c, k with
    | true, .num => do
      let ⟨hx⟩ ← x.src? true .num
      let ⟨hy⟩ ← y.src? true .num
      let ⟨ht⟩ ← t.src? true .num
      let ⟨he⟩ ← e.src? true .num
      return ⟨.kite (k := .num) rfl (fun h => nomatch h) hx hy ht he⟩
    | true, .bool => do
      let ⟨hx⟩ ← x.src? true .num
      let ⟨hy⟩ ← y.src? true .num
      let ⟨ht⟩ ← t.src? true .bool
      let ⟨he⟩ ← e.src? true .bool
      return ⟨.kite (k := .bool) rfl (fun h => nomatch h) hx hy ht he⟩
    | _, _ => none
  | c, k, _, .app3 .ite d t e =>
    match c, k with
    | true, .num => do
      let ⟨hd⟩ ← d.src? true .bool
      let ⟨ht⟩ ← t.src? true .num
      let ⟨he⟩ ← e.src? true .num
      return ⟨.ite (k := .num) rfl (fun h => nomatch h) hd ht he⟩
    | true, .bool => do
      let ⟨hd⟩ ← d.src? true .bool
      let ⟨ht⟩ ← t.src? true .bool
      let ⟨he⟩ ← e.src? true .bool
      return ⟨.ite (k := .bool) rfl (fun h => nomatch h) hd ht he⟩
    | _, _ => none
  | _, _, _, _ => none

/-- The source leaf, recognized with its evidence. -/
def LFml.src? (c : Bool) : (φ : LFml C) → Option (PLift (φ.Src c true))
  | .tt => some ⟨.tt⟩
  | @LFml.eq _ .bool a b => do
    let ⟨ha⟩ ← a.src? c .bool
    let ⟨hb⟩ ← b.src? c .bool
    return ⟨.eqB ha hb⟩
  | @LFml.eq _ .uint a b => do
    let ⟨ha⟩ ← a.src? c .num
    let ⟨hb⟩ ← b.src? c .num
    return ⟨.eqN rfl ha hb⟩
  | @LFml.eq _ .int a b => do
    let ⟨ha⟩ ← a.src? c .num
    let ⟨hb⟩ ← b.src? c .num
    return ⟨.eqN rfl ha hb⟩
  | .not φ => (φ.src? c).map fun ⟨h⟩ => ⟨.not h⟩
  | .and φ ψ => do
    let ⟨h1⟩ ← φ.src? c
    let ⟨h2⟩ ← ψ.src? c
    return ⟨.and h1 h2⟩
  | .imp φ ψ => do
    let ⟨h1⟩ ← φ.src? c
    let ⟨h2⟩ ← ψ.src? c
    return ⟨.imp h1 h2⟩
  | .all .. => none

/-- **The recognizer is complete**: it accepts every term of the fragment,
and a scalar at `bool` as a Boolean. -/
theorem LTm.src?_complete : ∀ {k : SrcKind} {s : Srt} {t : LTm C s}, t.Src false true k →
    (t.src? false k).isSome = true ∧
      (k = .num → (hs : s = .val .bool) → ((hs ▸ t : LTm C (.val .bool)).src? false .bool).isSome = true) := by
  intro k s t h
  induction h with
  | var i => exact ⟨rfl, fun _ hs => by cases hs; rfl⟩
  | @lit p v => exact ⟨by cases p <;> rfl, fun _ hs => by cases hs; rfl⟩
  | env e => exact ⟨rfl, fun _ hs => by cases hs⟩
  | err => exact ⟨rfl, fun _ hs => by cases hs; rfl⟩
  | @add p h a b _ _ iha ihb =>
    refine ⟨?_, ?_⟩
    · obtain ⟨⟨xa⟩, hxa⟩ := Option.isSome_iff_exists.mp iha.1
      obtain ⟨⟨xb⟩, hxb⟩ := Option.isSome_iff_exists.mp ihb.1
      show (Option.bind (LTm.src? false .num a) _).isSome = true
      rw [hxa]
      show (Option.bind (LTm.src? false .num b) _).isSome = true
      rw [hxb]
      rfl
    · intro _ hs
      have hb : p = .bool := by
        have := congrArg (fun | Srt.val q => q | _ => PrimTy.bool) hs
        simpa only [BinOp.ret, BinOp.isArith, if_true] using this
      subst hb
      cases h
  | @sub p h a b _ _ iha ihb =>
    refine ⟨?_, ?_⟩
    · obtain ⟨⟨xa⟩, hxa⟩ := Option.isSome_iff_exists.mp iha.1
      obtain ⟨⟨xb⟩, hxb⟩ := Option.isSome_iff_exists.mp ihb.1
      show (Option.bind (LTm.src? false .num a) _).isSome = true
      rw [hxa]
      show (Option.bind (LTm.src? false .num b) _).isSome = true
      rw [hxb]
      rfl
    · intro _ hs
      have hb : p = .bool := by
        have := congrArg (fun | Srt.val q => q | _ => PrimTy.bool) hs
        simpa only [BinOp.ret, BinOp.isArith, if_true] using this
      subst hb
      cases h
  | @mulL p h v b _ ihb =>
    refine ⟨LTm.mulSrc?_left h v b _ _ ihb.1, ?_⟩
    intro _ hs
    have hb : p = .bool := by
      have := congrArg (fun | Srt.val q => q | _ => PrimTy.bool) hs
      simpa only [BinOp.ret, BinOp.isArith, if_true] using this
    subst hb
    cases h
  | @mulR p h a v _ iha =>
    refine ⟨LTm.mulSrc?_right h a v _ _ iha.1 (by cases p <;> rfl), ?_⟩
    intro _ hs
    have hb : p = .bool := by
      have := congrArg (fun | Srt.val q => q | _ => PrimTy.bool) hs
      simpa only [BinOp.ret, BinOp.isArith, if_true] using this
    subst hb
    cases h
  | @seq q p d a hd ha ihd iha =>
    refine ⟨?_, ?_⟩
    · obtain ⟨⟨xa⟩, hxa⟩ := Option.isSome_iff_exists.mp ihd.1
      obtain ⟨⟨xb⟩, hxb⟩ := Option.isSome_iff_exists.mp iha.1
      show (Option.bind (LTm.src? false .num d) _).isSome = true
      rw [hxa]
      show (Option.bind (LTm.src? false .num a) _).isSome = true
      rw [hxb]
      rfl
    · intro _ hs
      cases hs
      cases q with
      | bool =>
        obtain ⟨⟨xa⟩, hxa⟩ := Option.isSome_iff_exists.mp (ihd.2 rfl rfl)
        obtain ⟨⟨xb⟩, hxb⟩ := Option.isSome_iff_exists.mp (iha.2 rfl rfl)
        show (Option.bind (LTm.src? false .bool d) _).isSome = true
        rw [hxa]
        show (Option.bind (LTm.src? false .bool a) _).isSome = true
        rw [hxb]
        rfl
      | uint | int =>
        obtain ⟨⟨xa⟩, hxa⟩ := Option.isSome_iff_exists.mp ihd.1
        obtain ⟨⟨xb⟩, hxb⟩ := Option.isSome_iff_exists.mp (iha.2 rfl rfl)
        show (Option.bind (LTm.src? false .num d) _).isSome = true
        rw [hxa]
        show (Option.bind (LTm.src? false .bool a) _).isSome = true
        rw [hxb]
        rfl
  | @word p q _ ih =>
    refine ⟨?_, ?_⟩
    · obtain ⟨⟨x⟩, hx⟩ := Option.isSome_iff_exists.mp ih.1
      show ((LTm.src? false .path q).map _).isSome = true
      rw [hx]
      rfl
    · intro _ hs
      cases hs
      obtain ⟨⟨x⟩, hx⟩ := Option.isSome_iff_exists.mp ih.1
      show ((LTm.src? false .path q).map _).isSome = true
      rw [hx]
      rfl
  | ofNum _ ih => exact ⟨ih.2 rfl rfl, fun hk => by cases hk⟩
  | @not a _ ih =>
    refine ⟨?_, fun hk => by cases hk⟩
    obtain ⟨⟨x⟩, hx⟩ := Option.isSome_iff_exists.mp ih.1
    show ((LTm.src? false .bool a).map _).isSome = true
    rw [hx]
    rfl
  | @neg h a _ ih | @bnot h a _ ih | @toInt _ h a _ ih | @toUint _ h a _ ih =>
    refine ⟨?_, fun _ hs => by cases hs⟩
    obtain ⟨⟨x⟩, hx⟩ := Option.isSome_iff_exists.mp ih.1
    show ((LTm.src? false .num a).map _).isSome = true
    rw [hx]
    rfl
  | @divL _ h a v hv _ ih | @modL _ h a v hv _ ih =>
    refine ⟨?_, fun _ hs => by cases hs⟩
    obtain ⟨⟨x⟩, hx⟩ := Option.isSome_iff_exists.mp ih.1
    show (if hv' : v.val = 0 then none else (LTm.src? false .num a).map _).isSome = true
    rw [dif_neg hv, hx]
    rfl
  | @shlL _ h a v _ ih =>
    refine ⟨?_, fun _ hs => by cases hs⟩
    obtain ⟨⟨x⟩, hx⟩ := Option.isSome_iff_exists.mp ih.1
    show ((LTm.src? false .num a).map _).isSome = true
    rw [hx]
    rfl
  | @shrL _ p h a v _ ih =>
    refine ⟨?_, ?_⟩
    · obtain ⟨⟨x⟩, hx⟩ := Option.isSome_iff_exists.mp ih.1
      show ((LTm.src? false .num a).map _).isSome = true
      rw [hx]
      rfl
    · intro _ hs
      have hb : p = .bool := by
        have := congrArg (fun | Srt.val q => q | _ => PrimTy.bool) hs
        simpa only [BinOp.ret, BinOp.isArith, if_true] using this
      subst hb
      cases h
  | @bandR _ h a v hm _ iha =>
    refine ⟨?_, fun _ hs => by cases hs⟩
    obtain ⟨⟨xa⟩, hxa⟩ := Option.isSome_iff_exists.mp iha.1
    show (LTm.bandSrc? h a (.app0 (.lit v)) (LTm.src? false .num a) _).isSome = true
    unfold LTm.bandSrc?
    dsimp only [LTm.lit?]
    rw [dif_pos hm, hxa]
    rfl
  | @bandL _ h v hm b _ ihb =>
    refine ⟨?_, fun _ hs => by cases hs⟩
    show (LTm.bandSrc? h (.app0 (.lit v)) b _ (LTm.src? false .num b)).isSome = true
    unfold LTm.bandSrc?
    split
    · rename_i w hw _
      split
      · show (Option.map _ (some _)).isSome = true
        rfl
      · exact LTm.bandLSrc?_isSome h v hm b _ ihb.1
    · exact LTm.bandLSrc?_isSome h v hm b _ ihb.1
  | @addW _ h a b _ _ iha ihb | @subW _ h a b _ _ iha ihb =>
    refine ⟨?_, fun _ hs => by cases hs⟩
    obtain ⟨⟨xa⟩, hxa⟩ := Option.isSome_iff_exists.mp iha.1
    obtain ⟨⟨xb⟩, hxb⟩ := Option.isSome_iff_exists.mp ihb.1
    show (Option.bind (LTm.src? false .num a) _).isSome = true
    rw [hxa]
    show (Option.bind (LTm.src? false .num b) _).isSome = true
    rw [hxb]
    rfl
  | @and a b _ _ iha ihb =>
    refine ⟨?_, fun hk => by cases hk⟩
    obtain ⟨⟨xa⟩, hxa⟩ := Option.isSome_iff_exists.mp iha.1
    obtain ⟨⟨xb⟩, hxb⟩ := Option.isSome_iff_exists.mp ihb.1
    show (Option.bind (LTm.src? false .bool a) _).isSome = true
    rw [hxa]
    show (Option.bind (LTm.src? false .bool b) _).isSome = true
    rw [hxb]
    rfl
  | @or a b _ _ iha ihb =>
    refine ⟨?_, fun hk => by cases hk⟩
    obtain ⟨⟨xa⟩, hxa⟩ := Option.isSome_iff_exists.mp iha.1
    obtain ⟨⟨xb⟩, hxb⟩ := Option.isSome_iff_exists.mp ihb.1
    show (Option.bind (LTm.src? false .bool a) _).isSome = true
    rw [hxa]
    show (Option.bind (LTm.src? false .bool b) _).isSome = true
    rw [hxb]
    rfl
  | @eqB a b _ _ iha ihb =>
    refine ⟨?_, fun hk => by cases hk⟩
    obtain ⟨⟨xa⟩, hxa⟩ := Option.isSome_iff_exists.mp iha.1
    obtain ⟨⟨xb⟩, hxb⟩ := Option.isSome_iff_exists.mp ihb.1
    show (Option.bind (LTm.src? false .bool a) _).isSome = true
    rw [hxa]
    show (Option.bind (LTm.src? false .bool b) _).isSome = true
    rw [hxb]
    rfl
  | @neB a b _ _ iha ihb =>
    refine ⟨?_, fun hk => by cases hk⟩
    obtain ⟨⟨xa⟩, hxa⟩ := Option.isSome_iff_exists.mp iha.1
    obtain ⟨⟨xb⟩, hxb⟩ := Option.isSome_iff_exists.mp ihb.1
    show (Option.bind (LTm.src? false .bool a) _).isSome = true
    rw [hxa]
    show (Option.bind (LTm.src? false .bool b) _).isSome = true
    rw [hxb]
    rfl
  | @eqN p hp a b _ _ iha ihb =>
    refine ⟨?_, fun hk => by cases hk⟩
    obtain ⟨⟨xa⟩, hxa⟩ := Option.isSome_iff_exists.mp iha.1
    obtain ⟨⟨xb⟩, hxb⟩ := Option.isSome_iff_exists.mp ihb.1
    cases p with
    | bool => cases hp
    | uint | int =>
      show (Option.bind (LTm.src? false .num a) _).isSome = true
      rw [hxa]
      show (Option.bind (LTm.src? false .num b) _).isSome = true
      rw [hxb]
      rfl
  | @neN p hp a b _ _ iha ihb =>
    refine ⟨?_, fun hk => by cases hk⟩
    obtain ⟨⟨xa⟩, hxa⟩ := Option.isSome_iff_exists.mp iha.1
    obtain ⟨⟨xb⟩, hxb⟩ := Option.isSome_iff_exists.mp ihb.1
    cases p with
    | bool => cases hp
    | uint | int =>
      show (Option.bind (LTm.src? false .num a) _).isSome = true
      rw [hxa]
      show (Option.bind (LTm.src? false .num b) _).isSome = true
      rw [hxb]
      rfl
  | @lt p h a b _ _ iha ihb =>
    refine ⟨?_, fun hk => by cases hk⟩
    obtain ⟨⟨xa⟩, hxa⟩ := Option.isSome_iff_exists.mp iha.1
    obtain ⟨⟨xb⟩, hxb⟩ := Option.isSome_iff_exists.mp ihb.1
    show (Option.bind (LTm.src? false .num a) _).isSome = true
    rw [hxa]
    show (Option.bind (LTm.src? false .num b) _).isSome = true
    rw [hxb]
    rfl
  | @gt p h a b _ _ iha ihb =>
    refine ⟨?_, fun hk => by cases hk⟩
    obtain ⟨⟨xa⟩, hxa⟩ := Option.isSome_iff_exists.mp iha.1
    obtain ⟨⟨xb⟩, hxb⟩ := Option.isSome_iff_exists.mp ihb.1
    show (Option.bind (LTm.src? false .num a) _).isSome = true
    rw [hxa]
    show (Option.bind (LTm.src? false .num b) _).isSome = true
    rw [hxb]
    rfl
  | @le p h a b _ _ iha ihb =>
    refine ⟨?_, fun hk => by cases hk⟩
    obtain ⟨⟨xa⟩, hxa⟩ := Option.isSome_iff_exists.mp iha.1
    obtain ⟨⟨xb⟩, hxb⟩ := Option.isSome_iff_exists.mp ihb.1
    show (Option.bind (LTm.src? false .num a) _).isSome = true
    rw [hxa]
    show (Option.bind (LTm.src? false .num b) _).isSome = true
    rw [hxb]
    rfl
  | @ge p h a b _ _ iha ihb =>
    refine ⟨?_, fun hk => by cases hk⟩
    obtain ⟨⟨xa⟩, hxa⟩ := Option.isSome_iff_exists.mp iha.1
    obtain ⟨⟨xb⟩, hxb⟩ := Option.isSome_iff_exists.mp ihb.1
    show (Option.bind (LTm.src? false .num a) _).isSome = true
    rw [hxa]
    show (Option.bind (LTm.src? false .num b) _).isSome = true
    rw [hxb]
    rfl
  | @seqB a b _ _ iha ihb =>
    refine ⟨?_, fun hk => by cases hk⟩
    obtain ⟨⟨xa⟩, hxa⟩ := Option.isSome_iff_exists.mp iha.1
    obtain ⟨⟨xb⟩, hxb⟩ := Option.isSome_iff_exists.mp ihb.1
    show (Option.bind (LTm.src? false .bool a) _).isSome = true
    rw [hxa]
    show (Option.bind (LTm.src? false .bool b) _).isSome = true
    rw [hxb]
    rfl
  | @seqN q hq a b _ _ iha ihb =>
    refine ⟨?_, fun hk => by cases hk⟩
    obtain ⟨⟨xa⟩, hxa⟩ := Option.isSome_iff_exists.mp iha.1
    obtain ⟨⟨xb⟩, hxb⟩ := Option.isSome_iff_exists.mp ihb.1
    cases q with
    | bool => cases hq
    | uint | int =>
      show (Option.bind (LTm.src? false .num a) _).isSome = true
      rw [hxa]
      show (Option.bind (LTm.src? false .bool b) _).isSome = true
      rw [hxb]
      rfl
  | root r h => exact ⟨rfl, fun hk => by cases hk⟩
  | @field sn f T h q _ ih =>
    refine ⟨?_, fun hk => by cases hk⟩
    obtain ⟨⟨x⟩, hx⟩ := Option.isSome_iff_exists.mp ih.1
    show ((LTm.src? false .path q).map _).isSome = true
    rw [hx]
    rfl
  | @key K V a b _ _ iha ihb =>
    refine ⟨?_, fun hk => by cases hk⟩
    obtain ⟨⟨xa⟩, hxa⟩ := Option.isSome_iff_exists.mp iha.1
    obtain ⟨⟨xb⟩, hxb⟩ := Option.isSome_iff_exists.mp ihb.1
    show (Option.bind (LTm.src? false .path a) _).isSome = true
    rw [hxa]
    show (Option.bind (LTm.src? false .num b) _).isSome = true
    rw [hxb]
    rfl
  | kite hc => cases hc
  | ite hc => cases hc

theorem LFml.src?_complete : ∀ {φ : LFml C}, φ.Src false true → (φ.src? false).isSome = true := by
  intro φ h
  induction h with
  | tt => rfl
  | defDiv hw | defShr hw | defAddW hw | defSubW hw | defToInt hw | defToUint hw => cases hw
  | @eqB a b ha hb =>
    obtain ⟨⟨xa⟩, hxa⟩ := Option.isSome_iff_exists.mp (LTm.src?_complete ha).1
    obtain ⟨⟨xb⟩, hxb⟩ := Option.isSome_iff_exists.mp (LTm.src?_complete hb).1
    show (Option.bind (LTm.src? false .bool a) _).isSome = true
    rw [hxa]
    show (Option.bind (LTm.src? false .bool b) _).isSome = true
    rw [hxb]
    rfl
  | @eqN p hp a b ha hb =>
    obtain ⟨⟨xa⟩, hxa⟩ := Option.isSome_iff_exists.mp (LTm.src?_complete ha).1
    obtain ⟨⟨xb⟩, hxb⟩ := Option.isSome_iff_exists.mp (LTm.src?_complete hb).1
    cases p with
    | bool => cases hp
    | uint | int =>
      show (Option.bind (LTm.src? false .num a) _).isSome = true
      rw [hxa]
      show (Option.bind (LTm.src? false .num b) _).isSome = true
      rw [hxb]
      rfl
  | @not φ _ ih =>
    obtain ⟨⟨x⟩, hx⟩ := Option.isSome_iff_exists.mp ih
    show ((LFml.src? false φ).map _).isSome = true
    rw [hx]
    rfl
  | @and φ ψ _ _ ih1 ih2 | @imp φ ψ _ _ ih1 ih2 =>
    obtain ⟨⟨xa⟩, hxa⟩ := Option.isSome_iff_exists.mp ih1
    obtain ⟨⟨xb⟩, hxb⟩ := Option.isSome_iff_exists.mp ih2
    show (Option.bind (LFml.src? false φ) _).isSome = true
    rw [hxa]
    show (Option.bind (LFml.src? false ψ) _).isSome = true
    rw [hxb]
    rfl


/-! ## The universal prefix -/

/-- A leaf's universal prefix, its binders in order, and its body. -/
def LFml.stripAll : LFml C → List Parameter × LFml C
  | .all k p φ => (⟨p, k⟩ :: φ.stripAll.1, φ.stripAll.2)
  | .tt => ([], .tt)
  | .eq a b => ([], .eq a b)
  | .not φ => ([], .not φ)
  | .and φ ψ => ([], .and φ ψ)
  | .imp φ ψ => ([], .imp φ ψ)

/-- The length of a leaf's universal prefix. -/
def LFml.allDepth : LFml C → Nat
  | .all _ _ φ => φ.allDepth + 1
  | _ => 0

theorem UniversalPrefix.ofFormula?_strip : ∀ (φ : LFml C) (n : Nat), φ.allDepth < n →
    ∃ u, UniversalPrefix.ofFormula? n φ = some u ∧ u.parameters = φ.stripAll.1 ∧
      u.body = φ.stripAll.2
  | .all k p φ, n, h => by
    obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp only [LFml.allDepth] at h; omega⟩
    simp only [LFml.allDepth] at h
    obtain ⟨u, hu, hp, hb⟩ := UniversalPrefix.ofFormula?_strip φ n (by omega)
    refine ⟨UniversalPrefix.all k p u, ?_, ?_, hb⟩
    · show (UniversalPrefix.ofFormula? n φ).map (UniversalPrefix.all k p) = _
      rw [hu]
      rfl
    · show ⟨p, k⟩ :: u.parameters = _
      rw [hp]
      rfl
  | .tt, n + 1, _ | .eq _ _, n + 1, _ | .not _, n + 1, _ | .and _ _, n + 1, _
  | .imp _ _, n + 1, _ => ⟨_, rfl, rfl, rfl⟩
  | .tt, 0, h | .eq _ _, 0, h | .not _, 0, h | .and _ _, 0, h | .imp _ _, 0, h => by
    simp only [LFml.allDepth] at h; omega

theorem LFml.stripAll_of_allDepth : ∀ (φ : LFml C), φ.allDepth = 0 → φ.stripAll = ([], φ)
  | .tt, _ | .eq _ _, _ | .not _, _ | .and _ _, _ | .imp _ _, _ => rfl
  | .all .., h => by simp only [LFml.allDepth] at h; omega

theorem CondGuard.split_allDepth (G : CondGuard C) (P Q R : LFml C) :
    (G.split P Q R).allDepth = 0 := by
  cases G <;> simp only [CondGuard.split] <;> split <;> rfl

theorem LFml.liftCond_allDepth_zero : ∀ (n : Nat) (φ : LFml C), φ.allDepth = 0 →
    (φ.liftCond n).allDepth = 0
  | 0, _, h => h
  | n + 1, .tt, _ | n + 1, .not _, _ | n + 1, .and _ _, _ | n + 1, .imp _ _, _ => rfl
  | n + 1, .eq a b, _ => by
    show (LFml.liftEq (LFml.liftCond n) a b).allDepth = 0
    unfold LFml.liftEq
    cases a.condSplit with
    | some r => exact LFml.liftCond_allDepth_zero n _ (CondGuard.split_allDepth _ _ _ _)
    | none =>
      cases b.condSplit with
      | some r => exact LFml.liftCond_allDepth_zero n _ (CondGuard.split_allDepth _ _ _ _)
      | none => rfl
  | _ + 1, .all .., h => by simp only [LFml.allDepth] at h; omega

theorem LFml.liftCond_stripAll_body (n : Nat) (ψ : LFml C) (h : ψ.allDepth = 0) :
    (ψ.liftCond n).allDepth = ψ.allDepth ∧ (ψ.liftCond n).stripAll = (ψ.stripAll.1, ψ.stripAll.2.liftCond n) := by
  have h' := LFml.liftCond_allDepth_zero n ψ h
  refine ⟨by rw [h', h], ?_⟩
  rw [LFml.stripAll_of_allDepth _ h', LFml.stripAll_of_allDepth _ h]

/-- Lifting keeps the universal prefix and lifts the body. -/
theorem LFml.liftCond_stripAll (n : Nat) : ∀ (ψ : LFml C),
    (ψ.liftCond (n + 1)).allDepth = ψ.allDepth ∧
      (ψ.liftCond (n + 1)).stripAll = (ψ.stripAll.1, ψ.stripAll.2.liftCond (n + 1))
  | .all k p φ => by
    obtain ⟨h1, h2⟩ := LFml.liftCond_stripAll n φ
    refine ⟨?_, ?_⟩
    · show (LFml.all k p (φ.liftCond (n + 1))).allDepth = (LFml.all k p φ).allDepth
      simp only [LFml.allDepth, h1]
    · show (LFml.all k p (φ.liftCond (n + 1))).stripAll = _
      simp only [LFml.stripAll, h2]
  | .tt => LFml.liftCond_stripAll_body _ _ rfl
  | .eq _ _ => LFml.liftCond_stripAll_body _ _ rfl
  | .not _ => LFml.liftCond_stripAll_body _ _ rfl
  | .and _ _ => LFml.liftCond_stripAll_body _ _ rfl
  | .imp _ _ => LFml.liftCond_stripAll_body _ _ rfl

/-! ## The fragment -/

/-- **The leaf the arithmetic stages receive, before lifting**: the original
formula after exact program normalization, update pushing, read
elimination and the folding of trivial conditionals, as
`dependentReduction?` computes it. -/
def leafOf? (φ : Fml C []) : Option (LFml C) := do
  let d ← ProgramNormalization.ofFormula? 2048 φ
  let r ← sourceReduction? d.formula
  return r.leaf.elim.condSimp.prenex

/-- A lifted leaf the arithmetic stages accept: a universal prefix (shorter
than 1024) binding every atom of a body in `LFml.Src false`. -/
def LFml.liftedExact (ψ : LFml C) : Bool :=
  decide (ψ.allDepth < 1024) && (ψ.stripAll.2.src? false).isSome &&
    ψ.stripAll.2.parameters.all (fun q => decide (q ∈ ψ.stripAll.1))

/-- **The eliminated leaf's fragment**: a universal prefix (shorter than
1024) binding every atom of a body in `LFml.Src true` (the elimination's
conditionals allowed), of lifting weight below `condLiftFuel`. -/
def LFml.inExact (ψ : LFml C) : Bool :=
  decide (ψ.allDepth < 1024) && (ψ.stripAll.2.src? true).isSome &&
    decide (ψ.stripAll.2.condMax < condLiftFuel) &&
    ψ.stripAll.2.parameters.all (fun q => decide (q ∈ ψ.stripAll.1))

/-- The size bounds, on the lifted body and on its cut (`LFml.cutAll`, the
body itself where no operator is cut): at most 511 nodes and 45 storage
reads. -/
def LFml.exactBounded (ψ : LFml C) : Bool :=
  let body := (ψ.liftCond condLiftFuel).stripAll.2
  decide (body.nodes ≤ 511) && decide (body.cutAll.nodes ≤ 511) &&
    decide (body.cutAll.words * body.cutAll.words ≤ 2048)

/-- **The fragment of the automatic decision**: the formula normalizes and
pushes its updates exactly, and its eliminated leaf is in `LFml.inExact`. -/
def _root_.Solidity.Fml.inExact (φ : Fml C []) : Bool :=
  match leafOf? φ with
  | some ψ => ψ.inExact
  | none => false

/-- **The size bounds of the automatic decision**, on its lifted leaf. -/
def _root_.Solidity.Fml.exactBounded (φ : Fml C []) : Bool :=
  match leafOf? φ with
  | some ψ => ψ.exactBounded
  | none => false

/-- **Lifting completes the fragment**: an eliminated leaf whose body is in
the fragment with the elimination's conditionals (`LTm.Src true`), of
weight below the lifting fuel, is accepted once lifted. -/
theorem LFml.liftedExact_lift (ψ : LFml C) (h : ψ.inExact = true) :
    (ψ.liftCond condLiftFuel).liftedExact = true := by
  simp only [LFml.inExact, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨hd, hsrc⟩, hm⟩, hc⟩ := h
  obtain ⟨⟨hs⟩, -⟩ := Option.isSome_iff_exists.mp hsrc
  obtain ⟨h1, h2⟩ := LFml.liftCond_stripAll 63 ψ
  have hsrc' := LFml.src?_complete (LFml.liftCond_src condLiftFuel hs hm)
  simp only [LFml.liftedExact, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · show (ψ.liftCond (63 + 1)).allDepth < 1024
    rw [h1]; exact hd
  · show ((ψ.liftCond (63 + 1)).stripAll.2.src? false).isSome = true
    rw [h2]; exact hsrc'
  · intro q hq
    have hq' : q ∈ (ψ.stripAll.2.liftCond (63 + 1)).parameters := by
      have := hq
      rw [show condLiftFuel = 63 + 1 from rfl, h2] at this
      exact this
    show q ∈ (ψ.liftCond (63 + 1)).stripAll.1
    rw [h2]
    exact hc q (LFml.liftCond_params _ _ q hq')

/-! ## The node budget -/

/-- `n - c` where `c ≤ n`: the fuel `fits` leaves after `c` nodes. -/
def fitsCap (c n : Nat) : Option Nat := if c ≤ n then some (n - c) else none

theorem fitsCap_zero : (some : Nat → Option Nat) = fitsCap 0 := by
  funext m; simp only [fitsCap, Nat.zero_le, if_true, Nat.sub_zero]

theorem fitsNode_fitsCap (c n : Nat) : fitsNode n (fitsCap c) = fitsCap (c + 1) n := by
  cases n with
  | zero => simp only [fitsNode, fitsCap, Nat.le_zero, Nat.add_one_ne_zero, if_false]
  | succ n =>
    simp only [fitsNode, fitsCap, Nat.add_le_add_iff_right, Nat.add_sub_add_right]

theorem fitsCap_bind (a b m : Nat) : (fitsCap a m).bind (fitsCap b) = fitsCap (a + b) m := by
  unfold fitsCap
  by_cases ha : a ≤ m
  · by_cases hb : b ≤ m - a
    · rw [if_pos ha, Option.bind_some, if_pos hb, if_pos (by omega), Nat.sub_sub]
    · rw [if_pos ha, Option.bind_some, if_neg hb, if_neg (by omega)]
  · rw [if_neg ha, if_neg (by omega)]; rfl

/-- **`fits` counts nodes**: `t.fits n` is the fuel left after `t.nodes`,
`none` past it. -/
theorem LTm.fits_eq_fitsCap {s : Srt} (t : LTm C s) : t.fits = fitsCap t.nodes := by
  rw [LTm.fits_eq_fitsM]
  induction t with
  | var | app0 | err => funext n; simp only [LTm.fitsM, LTm.nodes, fitsCap_zero, fitsNode_fitsCap]
  | app1 _ _ ih | obsW _ ih | obsL _ ih | obsH _ ih =>
    funext n; simp only [LTm.fitsM, LTm.nodes, ih, fitsNode_fitsCap]
  | app2 _ _ _ ihx ihy | index _ _ _ ihx ihy | seq _ _ ihx ihy | orElse _ _ ihx ihy =>
    funext n; simp only [LTm.fitsM, LTm.nodes, ihx, ihy, fitsCap_bind, fitsNode_fitsCap]
  | app3 _ _ _ _ ihx ihy ihz =>
    funext n; simp only [LTm.fitsM, LTm.nodes, ihx, ihy, ihz, fitsCap_bind, fitsNode_fitsCap]
  | kite _ _ _ _ iha ihb iht ihe =>
    funext n; simp only [LTm.fitsM, LTm.nodes, iha, ihb, iht, ihe, fitsCap_bind, fitsNode_fitsCap]

theorem LFml.fits_eq_fitsCap (φ : LFml C) : φ.fits = fitsCap φ.nodes := by
  rw [LFml.fits_eq_fitsM]
  induction φ with
  | tt => funext n; simp only [LFml.fitsM, LFml.nodes, fitsCap_zero, fitsNode_fitsCap]
  | eq a b =>
    funext n
    simp only [LFml.fitsM, LFml.nodes, LTm.fits_eq_fitsCap, fitsCap_bind, fitsNode_fitsCap]
  | not _ ih | all _ _ _ ih => funext n; simp only [LFml.fitsM, LFml.nodes, ih, fitsNode_fitsCap]
  | and _ _ ihx ihy | imp _ _ ihx ihy =>
    funext n; simp only [LFml.fitsM, LFml.nodes, ihx, ihy, fitsCap_bind, fitsNode_fitsCap]

theorem LFml.nodes_stripAll : ∀ φ : LFml C, φ.nodes = φ.allDepth + φ.stripAll.2.nodes
  | .all k p φ => by
    have := LFml.nodes_stripAll φ
    simp only [LFml.nodes, LFml.allDepth, LFml.stripAll]
    omega
  | .tt | .eq _ _ | .not _ | .and _ _ | .imp _ _ => by
    simp only [LFml.allDepth, LFml.stripAll, Nat.zero_add]

/-- **The budget refuses nothing in the bounds**: a leaf whose lifted
prefix is shorter than 1024 and whose lifted body has at most 511 nodes
(`Fml.exactBounded`) is lifted within `liftBudget`. -/
theorem LFml.liftCondB_isSome (ψ : LFml C) (hd : (ψ.liftCond condLiftFuel).allDepth < 1024)
    (hn : (ψ.liftCond condLiftFuel).stripAll.2.nodes ≤ 511) :
    (ψ.liftCondB condLiftFuel liftBudget).isSome = true := by
  rw [LFml.liftCondB_eq, LFml.fits_eq_fitsCap, fitsCap,
    if_pos (by rw [LFml.nodes_stripAll]; simp only [liftBudget]; omega)]
  rfl

/-! ## Totality and completeness -/

/-- **The automatic decision never refuses its fragment.** -/
theorem dependentReduction?_isSome (φ : Fml C []) (h : φ.inExact = true)
    (hb : φ.exactBounded = true) : (dependentReduction? φ).isSome = true := by
  unfold Fml.inExact at h
  unfold Fml.exactBounded at hb
  cases hl : leafOf? φ with
  | none => rw [hl] at h; cases h
  | some ψ =>
    rw [hl] at h hb
    simp only [leafOf?, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at hl
    obtain ⟨d, hd, r, hr, rfl⟩ := hl
    have h' := LFml.liftedExact_lift _ h
    simp only [LFml.liftedExact, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h'
    obtain ⟨⟨hdepth, hsrc⟩, hcov⟩ := h'
    simp only [LFml.exactBounded, Bool.and_eq_true, decide_eq_true_eq] at hb
    obtain ⟨⟨hn, hcn⟩, hw⟩ := hb
    obtain ⟨u, hu, hup, hub⟩ := UniversalPrefix.ofFormula?_strip _ 1024 hdepth
    obtain ⟨⟨hs⟩, -⟩ := Option.isSome_iff_exists.mp hsrc
    have hs' : u.body.Src false true := hub ▸ hs
    have hc : ∀ p ∈ u.body.parameters, p ∈ u.parameters := by
      rw [hub, hup]
      exact hcov
    obtain ⟨F, hF⟩ := Option.isSome_iff_exists.mp
      (flattenedArithmetic?_isSome u.body hs' (hub ▸ hcn) (hub ▸ hw))
    have hcap := LFml.liftCondB_isSome _ hdepth hn
    have hnone : (r.leaf.elim.condSimp.prenex.liftCondB condLiftFuel liftBudget).isNone = false := by
      cases hX : r.leaf.elim.condSimp.prenex.liftCondB condLiftFuel liftBudget with
      | none => rw [hX] at hcap; cases hcap
      | some _ => rfl
    simp only [dependentReduction?, hd, hr, hu, Option.bind_eq_bind, Option.bind_some, hnone,
      Bool.false_eq_true, if_false]
    rw [dif_pos hc, hF]
    rfl

/-- **Completeness on the fragment**: the decision returns a certificate,
and the formula is valid exactly when the arithmetic decision says so. -/
theorem auto_complete (φ : Fml C []) (h : φ.inExact = true) (hb : φ.exactBounded = true) :
    ∃ r, dependentReduction? φ = some r ∧ (Fml.Valid φ ↔ r.arithmetic.guarded.decide = true) := by
  obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp (dependentReduction?_isSome φ h hb)
  exact ⟨r, hr, r.valid_iff.trans (r.arithmetic.valid_iff.trans (AFml.decide_iff _).symm)⟩

/-- **A `false` verdict has a countermodel**: an actual starting state
refuting the original formula, reconstructed from the arithmetic one. -/
def DependentReduction.countermodelOfDecide {φ : Fml C []} (r : DependentReduction φ)
    (h : r.arithmetic.guarded.decide = false) : r.Countermodel :=
  r.countermodelOf (r.arithmetic.countermodel h)

theorem auto_countermodel (φ : Fml C []) (h : φ.inExact = true) (hb : φ.exactBounded = true) :
    ∃ r, dependentReduction? φ = some r ∧
      (r.arithmetic.guarded.decide = false → ∃ σ : State C [], ¬ holds σ φ) := by
  obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp (dependentReduction?_isSome φ h hb)
  exact ⟨r, hr, fun hd => ⟨(r.countermodelOfDecide hd).state, (r.countermodelOfDecide hd).refutes⟩⟩

end Solidity.Decide
