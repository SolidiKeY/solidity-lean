import Solidity.Calculus.CutTotality
import Solidity.Calculus.LedgerCut

/-!
# Arithmetic over ledger entries (M7, plan step 3)

A leaf the ledger cut leaves (`Calculus/LedgerCut.lean`) reads the ledger
only at constants (`net(c)`).  Each such entry is a KeY `int`, unbounded:
the arithmetic reads it as the difference of two natural codes past the
typed inputs' (`Inputs.AgreeZ`), with no range constraint.  So the decided
formula is `LeafArithmetic`'s with these codes beside it
(`LeafArithmeticZ`); validity is validity over all natural codes, every
integer being a difference of two, and a false assignment is realized with
the ledger its differences (`ledgerOfCodes`).
-/

namespace Solidity.Decide

open Semantics ReadRealization Linear ScalarCode

variable {C : Contract}

/-! ## The constants a leaf reads the ledger at -/

/-- The constant of a ledger read at a literal. -/
def netConst1 {a s : Srt} (o : Op1 C a s) (x : LTm C a) : List PrimTy.uint.Denote :=
  match a, s, o, x with
  | _, _, .net, .app0 (.lit c) => [c]
  | _, _, _, _ => []

/-- The constants of a term's ledger reads at literals. -/
def LTm.netConsts : {s : Srt} → LTm C s → List PrimTy.uint.Denote
  | _, .var _ | _, .app0 _ | _, .err => []
  | _, .app1 o a => a.netConsts ++ netConst1 o a
  | _, .app2 _ a b | _, .index _ a b | _, .seq a b | _, .orElse a b => a.netConsts ++ b.netConsts
  | _, .app3 _ a b c => a.netConsts ++ b.netConsts ++ c.netConsts
  | _, .obsW a | _, .obsL a | _, .obsH a => a.netConsts
  | _, .kite a b t e => a.netConsts ++ b.netConsts ++ t.netConsts ++ e.netConsts

/-- The constants of a formula's ledger reads at literals. -/
def LFml.netConsts : LFml C → List PrimTy.uint.Denote
  | .tt => []
  | .eq a b => a.netConsts ++ b.netConsts
  | .not φ | .all _ _ φ => φ.netConsts
  | .and φ ψ | .imp φ ψ => φ.netConsts ++ ψ.netConsts

theorem LTm.ZNum.ledger_restrict {P : Parameter → Prop} {E : EnvKey → Prop}
    {L L' : PrimTy.uint.Denote → Prop} :
    ∀ {t : LTm C .kint}, t.ZNum P E L → (∀ v ∈ t.netConsts, L' v) → t.ZNum P E L' := by
  intro t h
  induction h with
  | zlit n => intro _; exact .zlit n
  | toInt ha => intro _; exact .toInt ha
  | add h _ _ iha ihb =>
    intro hL
    exact .add h (iha fun v hv => hL v (List.mem_append_left _ hv))
      (ihb fun v hv => hL v (List.mem_append_right _ hv))
  | sub h _ _ iha ihb =>
    intro hL
    exact .sub h (iha fun v hv => hL v (List.mem_append_left _ hv))
      (ihb fun v hv => hL v (List.mem_append_right _ hv))
  | mulL h n _ ih => intro hL; exact .mulL h n (ih fun v hv => hL v (List.mem_append_right _ hv))
  | mulR h n _ ih => intro hL; exact .mulR h n (ih fun v hv => hL v (List.mem_append_left _ hv))
  | netLit v _ => intro hL; exact .netLit v (hL v (by simp only [LTm.netConsts, netConst1,
      List.nil_append, List.mem_singleton]))
  | zseq hd _ ih => intro hL; exact .zseq hd (ih fun v hv => hL v (List.mem_append_right _ hv))

theorem LTm.BoolV.ledger_restrict {P : Parameter → Prop} {E : EnvKey → Prop}
    {L L' : PrimTy.uint.Denote → Prop} :
    ∀ {t : LTm C (.val .bool)}, t.BoolV P E L → (∀ v ∈ t.netConsts, L' v) → t.BoolV P E L' := by
  intro t h
  induction h with
  | var k hk => intro _; exact .var k hk
  | lit v => intro _; exact .lit v
  | err => intro _; exact .err
  | not _ ih => intro hL; exact .not (ih fun v hv => hL v (List.mem_append_left _ hv))
  | and _ _ iha ihb =>
    intro hL
    exact .and (iha fun v hv => hL v (List.mem_append_left _ hv))
      (ihb fun v hv => hL v (List.mem_append_right _ hv))
  | or _ _ iha ihb =>
    intro hL
    exact .or (iha fun v hv => hL v (List.mem_append_left _ hv))
      (ihb fun v hv => hL v (List.mem_append_right _ hv))
  | eqB _ _ iha ihb =>
    intro hL
    exact .eqB (iha fun v hv => hL v (List.mem_append_left _ hv))
      (ihb fun v hv => hL v (List.mem_append_right _ hv))
  | neB _ _ iha ihb =>
    intro hL
    exact .neB (iha fun v hv => hL v (List.mem_append_left _ hv))
      (ihb fun v hv => hL v (List.mem_append_right _ hv))
  | eqN hp ha hb => intro _; exact .eqN hp ha hb
  | neN hp ha hb => intro _; exact .neN hp ha hb
  | lt h ha hb => intro _; exact .lt h ha hb
  | gt h ha hb => intro _; exact .gt h ha hb
  | le h ha hb => intro _; exact .le h ha hb
  | ge h ha hb => intro _; exact .ge h ha hb
  | seqB _ _ ihd iha =>
    intro hL
    exact .seqB (ihd fun v hv => hL v (List.mem_append_left _ hv))
      (iha fun v hv => hL v (List.mem_append_right _ hv))
  | seqN hq hd _ iha => intro hL; exact .seqN hq hd (iha fun v hv => hL v (List.mem_append_right _ hv))
  | zcmp op h ha hb =>
    intro hL
    exact .zcmp op h (ha.ledger_restrict fun v hv => hL v (List.mem_append_left _ hv))
      (hb.ledger_restrict fun v hv => hL v (List.mem_append_right _ hv))

theorem LFml.Arith.ledger_restrict {P : Parameter → Prop} {E : EnvKey → Prop}
    {L L' : PrimTy.uint.Denote → Prop} :
    ∀ {φ : LFml C}, φ.Arith P E L → (∀ v ∈ φ.netConsts, L' v) → φ.Arith P E L' := by
  intro φ h
  induction h with
  | tt => intro _; exact .tt
  | eqB ha hb hda hdb =>
    intro hL
    exact .eqB (ha.ledger_restrict fun v hv => hL v (List.mem_append_left _ hv))
      (hb.ledger_restrict fun v hv => hL v (List.mem_append_right _ hv)) hda hdb
  | eqN hp ha hb hda hdb => intro _; exact .eqN hp ha hb hda hdb
  | not _ ih => intro hL; exact .not (ih hL)
  | and _ _ ih1 ih2 =>
    intro hL
    exact .and (ih1 fun v hv => hL v (List.mem_append_left _ hv))
      (ih2 fun v hv => hL v (List.mem_append_right _ hv))
  | imp _ _ ih1 ih2 =>
    intro hL
    exact .imp (ih1 fun v hv => hL v (List.mem_append_left _ hv))
      (ih2 fun v hv => hL v (List.mem_append_right _ hv))
  | defDiv h c hc k ha hk hd => intro _; exact .defDiv h c hc k ha hk hd
  | defShr h v k ha hk hd => intro _; exact .defShr h v k ha hk hd
  | defAddW h k ha hb hk hda hdb => intro _; exact .defAddW h k ha hb hk hda hdb
  | defSubW h k ha hb hk hda hdb => intro _; exact .defSubW h k ha hb hk hda hdb
  | defToInt h k ha hk hd => intro _; exact .defToInt h k ha hk hd
  | defToUint h k ha hk hd => intro _; exact .defToUint h k ha hk hd

/-! ## The codes of the ledger entries -/

/-- The ledger whose entry at the `j`-th constant is the difference of the
codes at `w + 2j` and `w + 2j + 1`. -/
def ledgerOfCodes (x : Nat → Nat) (w : Nat) : List PrimTy.uint.Denote → Nat → Ledger
  | [], _ => []
  | c :: cs, j => (c, (x (w + 2 * j) : Int) - x (w + 2 * j + 1)) :: ledgerOfCodes x w cs (j + 1)

theorem ledgerOfCodes_at (x : Nat → Nat) (w : Nat) :
    ∀ (ls : List PrimTy.uint.Denote) (n j : Nat) (c : PrimTy.uint.Denote), ls.Nodup →
      ls[j]? = some c →
      ledgerAt (ledgerOfCodes x w ls n) c = (x (w + 2 * (n + j)) : Int) - x (w + 2 * (n + j) + 1)
  | [], _, _, _, _, h => by cases h
  | d :: ls, n, j, c, hn, h => by
    rw [List.nodup_cons] at hn
    cases j with
    | zero =>
      cases h
      simp only [ledgerOfCodes, ledgerAt, lookupBy, if_true, Option.getD_some, Nat.add_zero]
    | succ j =>
      have hc : c ∈ ls := List.mem_of_getElem? (by simpa using h)
      have hne : c ≠ d := fun he => hn.1 (he ▸ hc)
      simp only [ledgerOfCodes, ledgerAt, lookupBy, hne, if_false]
      have := ledgerOfCodes_at x w ls (n + 1) j c hn.2 (by simpa using h)
      rw [show n + (j + 1) = n + 1 + j by omega]
      exact this

theorem Inputs.observe_withLedger (es : List EnvKey) (ps : List Parameter) (rs : List (Ref C))
    (g : State C []) (l : Ledger) (ν : AEnv) :
    Inputs.observe es ps rs (State.withLedger g l) ν = Inputs.observe es ps rs g ν := by
  induction es with
  | nil => rfl
  | cons e es ih => simp only [Inputs.observe, ih]; rfl

/-- The codes of `g` and `ν`: the typed inputs', then each ledger entry at
`ls` as its positive and negative parts. -/
def codesZ (es : List EnvKey) (ps : List Parameter) (rs : List (Ref C))
    (ls : List PrimTy.uint.Denote) (g : State C []) (ν : AEnv) : Nat → Nat := fun k =>
  if k < Inputs.width es ps rs then (Inputs.observe es ps rs g ν).codes k
  else
    let j := (k - Inputs.width es ps rs) / 2
    let e := ledgerAt g.net (ls.getD j (PrimTy.dflt .uint))
    if (k - Inputs.width es ps rs) % 2 = 0 then e.toNat else (-e).toNat

theorem codesZ_agree (es : List EnvKey) (ps : List Parameter) (rs : List (Ref C))
    (ls : List PrimTy.uint.Denote) (g : State C []) (ν : AEnv) :
    Inputs.AgreeZ es ps rs ls g ν (codesZ es ps rs ls g ν) := by
  refine ⟨fun k hk => by simp only [codesZ, if_pos hk], fun j c hj => ?_⟩
  have hw1 : ¬ Inputs.width es ps rs + 2 * j < Inputs.width es ps rs := by omega
  have hw2 : ¬ Inputs.width es ps rs + 2 * j + 1 < Inputs.width es ps rs := by omega
  have hd1 : (Inputs.width es ps rs + 2 * j - Inputs.width es ps rs) / 2 = j := by omega
  have hd2 : (Inputs.width es ps rs + 2 * j + 1 - Inputs.width es ps rs) / 2 = j := by omega
  have hm1 : (Inputs.width es ps rs + 2 * j - Inputs.width es ps rs) % 2 = 0 := by omega
  have hm2 : ¬ (Inputs.width es ps rs + 2 * j + 1 - Inputs.width es ps rs) % 2 = 0 := by omega
  have hg : ls.getD j (PrimTy.dflt .uint) = c := by rw [List.getD_eq_getElem?_getD, hj]; rfl
  simp only [codesZ, hw1, hw2, if_false, hd1, hd2, hm1, hm2, if_true, hg]
  omega

/-! ## The leaf arithmetic with ledger entries -/

/-- **A leaf decided by arithmetic, its ledger reads at constants**: the
typed inputs as `LeafArithmetic`'s, each ledger entry at `ledger` two codes
past them. -/
structure LeafArithmeticZ (φ : LFml C) where
  environment : List EnvKey
  distinctEnvironment : environment.Nodup
  parameters : List Parameter
  distinctParameters : parameters.Nodup
  refs : List (Ref C)
  distinctRefs : refs.Nodup
  ledger : List PrimTy.uint.Denote
  distinctLedger : ledger.Nodup
  formula : AFml
  width : formula.width ≤ Inputs.width environment parameters refs + 2 * ledger.length
  correct : ∀ (g : State C []) (ν : AEnv) (x : Nat → Nat),
    Inputs.AgreeZ environment parameters refs ledger g ν x → (formula.holds x ↔ φ.holds g ν)

def leafArithmeticZ? (φ : LFml C) : Option (LeafArithmeticZ φ) := do
  let es := Inputs.unique (Inputs.formulaKeys φ)
  let ps := φ.parameters.eraseDups
  let ls := φ.netConsts.eraseDups
  let encoded ← StorageEncoding.ofFormula? (ps := ps) (es := es) φ ls
  let rs := Layout.unique encoded.refs
  if he : es.Nodup then
    if hp : ps.Nodup then
      if hr : rs.Nodup then
        if hl : ls.Nodup then
          if hc : ∀ q ∈ encoded.refs, q ∈ rs then
            if hw : (encoded.lower rs).width ≤ Inputs.width es ps rs + 2 * ls.length then
              return ⟨es, he, ps, hp, rs, hr, ls, hl, encoded.lower rs, hw,
                fun g ν x hx => encoded.correctX rs hc g ν x hx⟩
            else none
          else none
        else none
      else none
    else none
  else none

namespace LeafArithmeticZ

/-- The domain of the typed inputs as the premise. -/
def guarded {φ : LFml C} (r : LeafArithmeticZ φ) : AFml :=
  .imp (domain (Inputs.types r.environment r.parameters r.refs)) r.formula

/-- The state and atoms the codes `x`, in the domain, stand for. -/
def realize {φ : LFml C} (r : LeafArithmeticZ φ) (x : Nat → Nat)
    (hd : (domain (Inputs.types r.environment r.parameters r.refs)).holds x) : State C [] × AEnv :=
  let vs := Values.decode _ x hd
  let model := Inputs.realize r.environment r.parameters r.refs vs
  (State.withLedger model.1 (ledgerOfCodes x (Inputs.width r.environment r.parameters r.refs)
    r.ledger 0), model.2)

theorem realize_agree {φ : LFml C} (r : LeafArithmeticZ φ) (x : Nat → Nat)
    (hd : (domain (Inputs.types r.environment r.parameters r.refs)).holds x) :
    Inputs.AgreeZ r.environment r.parameters r.refs r.ledger (r.realize x hd).1 (r.realize x hd).2 x := by
  refine ⟨fun k hk => ?_, fun j c hj => ?_⟩
  · simp only [realize, Inputs.observe_withLedger]
    rw [Inputs.observe_realize _ _ _ r.distinctEnvironment r.distinctParameters r.distinctRefs]
    exact (Values.codes_decode _ x hd k (by rw [Inputs.length_types]; exact hk)).symm
  · simp only [realize]
    rw [ledgerOfCodes_at x _ r.ledger 0 j c r.distinctLedger hj, Nat.zero_add]

theorem domain_codesZ {φ : LFml C} (r : LeafArithmeticZ φ) (g : State C []) (ν : AEnv) :
    (domain (Inputs.types r.environment r.parameters r.refs)).holds
      (codesZ r.environment r.parameters r.refs r.ledger g ν) := by
  have h := domain_codes (Inputs.observe r.environment r.parameters r.refs g ν)
  rw [domain, domainFrom_iff] at h ⊢
  intro k p hk
  have hlt : k < Inputs.width r.environment r.parameters r.refs := by
    have := (List.getElem?_eq_some_iff.1 hk).1
    rw [Inputs.length_types] at this
    exact this
  simp only [Nat.zero_add, codesZ, if_pos hlt] at h ⊢
  exact h k p hk

theorem valid_iff {φ : LFml C} (r : LeafArithmeticZ φ) : φ.Valid ↔ r.guarded.Valid := by
  constructor
  · intro hv x hd
    exact (r.correct _ _ x (r.realize_agree x hd)).2 (hv _ _)
  · intro hv g ν
    exact (r.correct g ν _ (codesZ_agree _ _ _ _ g ν)).1 (hv _ (r.domain_codesZ g ν))

structure Countermodel {φ : LFml C} (r : LeafArithmeticZ φ) where
  state : State C []
  atoms : AEnv
  refutes : ¬ φ.holds state atoms

def countermodelOf {φ : LFml C} (r : LeafArithmeticZ φ) (x : Nat → Nat) (hx : ¬ r.guarded.holds x) :
    r.Countermodel := by
  have hd : (domain (Inputs.types r.environment r.parameters r.refs)).holds x :=
    Classical.byContradiction fun hn => hx fun h => (hn h).elim
  have hf : ¬ r.formula.holds x := fun h => hx fun _ => h
  exact ⟨(r.realize x hd).1, (r.realize x hd).2,
    fun hφ => hf ((r.correct _ _ x (r.realize_agree x hd)).2 hφ)⟩

end LeafArithmeticZ

/-! ## Flattened, with ledger entries -/

/-- A cut leaf decided by arithmetic: its operators cut, its storage reads
flattened, the result compiled with its ledger entries. -/
structure FlattenedArithmeticZ (φ : LFml C) where
  source : ReadFormula φ
  flattening : ReadFlattening φ.cutAll φ.cutAll.atomBound
  encoding : LeafArithmeticZ flattening.formula

def flattenedArithmeticZ? (budget : Nat) (φ : LFml C) : Option (FlattenedArithmeticZ φ) := do
  let src ← ReadFormula.ofFormula? φ
  let r ← readFlatten? budget φ.cutAll
  if r.flat.reads.length * r.flat.reads.length ≤ budget then
    return ⟨src, r, ← leafArithmeticZ? r.formula⟩
  else none

namespace FlattenedArithmeticZ

theorem valid_iff {φ : LFml C} (r : FlattenedArithmeticZ φ) : φ.Valid ↔ r.encoding.guarded.Valid :=
  (LFml.cutAll_valid_iff φ).symm.trans
    (r.flattening.formula_valid_iff.symm.trans r.encoding.valid_iff)

structure Countermodel {φ : LFml C} (r : FlattenedArithmeticZ φ) where
  state : State C []
  atoms : AEnv
  refutes : ¬ φ.holds state atoms

def countermodelOf {φ : LFml C} (r : FlattenedArithmeticZ φ) (x : Nat → Nat)
    (hx : ¬ r.encoding.guarded.holds x) : r.Countermodel := by
  let raw := r.encoding.countermodelOf x hx
  have hn : ¬ ((ReadOccurrence.constraints r.flattening.flat.reads).holds raw.state raw.atoms →
      r.flattening.flat.formula.holds raw.state raw.atoms) := raw.refutes
  have hc := Classical.byContradiction (fun h => hn (fun hh => (h hh).elim))
  have hf := fun h => hn (fun _ => h)
  let actual := r.flattening.countermodel raw.state raw.atoms
    ((r.flattening.layout.constraints_iff _ _).mp hc) hf
  exact ⟨actual.val, raw.atoms, fun h => actual.property (LFml.holds_cutAll φ _ _ h)⟩

def verify {φ : LFml C} (r : FlattenedArithmeticZ φ) : Sum (PLift φ.Valid) r.Countermodel :=
  match r.encoding.guarded.verify with
  | .inl h => .inl ⟨r.valid_iff.mpr h.down⟩
  | .inr cm => .inr (r.countermodelOf cm.1 cm.2)

end FlattenedArithmeticZ

/-! ## Totality -/

/-- **The leaf arithmetic with ledger entries never refuses its fragment.** -/
theorem leafArithmeticZ?_isSome (φ : LFml C)
    (h : φ.Arith (· ∈ φ.parameters.eraseDups) (· ∈ Inputs.unique (Inputs.formulaKeys φ))
      (· ∈ φ.netConsts.eraseDups)) :
    (leafArithmeticZ? φ).isSome = true := by
  obtain ⟨enc, henc, good⟩ := StorageEncoding.ofFormulaL?_good (ls := φ.netConsts.eraseDups) h
  have he : (Inputs.unique (Inputs.formulaKeys φ)).Nodup := (Inputs.unique_spec _).1
  have hp : φ.parameters.eraseDups.Nodup := List.nodup_eraseDups' _
  have hl : φ.netConsts.eraseDups.Nodup := List.nodup_eraseDups' _
  have hr : (Layout.unique enc.refs).Nodup := (Layout.unique_spec _).1
  have hc : ∀ q ∈ enc.refs, q ∈ Layout.unique enc.refs := fun q hq => ((Layout.unique_spec _).2 q).mpr hq
  have hw := good _ hc
  simp only [leafArithmeticZ?, StorageEncoding.ofFormula?, henc, Option.bind_eq_bind,
    Option.bind_some, he, hp, hr, hl, dif_pos]
  rw [dif_pos hc, dif_pos hw]
  rfl

theorem readFlatten?_arithZ (φ : LFml C) (h : φ.SrcL false false .post) (hn : φ.nodes ≤ 511)
    (hw : φ.words * φ.words ≤ 2048) :
    ∃ r, readFlatten? 2048 φ = some r ∧ r.flat.reads.length * r.flat.reads.length ≤ 2048 ∧
      (leafArithmeticZ? r.formula).isSome = true := by
  have hd := LFml.depth_le_nodes φ
  obtain ⟨a, ha, aok, alen, alaid, aocc⟩ :=
    flattenFormulaFuel?_Src (l := .post) (by decide) h 2048 2048 φ.atomBound (by omega) (by omega)
      (Nat.le_refl _) hn
  obtain ⟨src, hsrc⟩ := h.readFormula
  have hwl : φ.words ≤ 2048 := Nat.le_trans (Nat.le_mul_self _) hw
  obtain ⟨L, hL⟩ := Option.isSome_iff_exists.mp (occurrenceLayout?_isSome 2048 alaid (by omega))
  obtain ⟨rf, hrf, hrf0⟩ := aok.readFree
  have hflat : flattenFormula? 2048 φ = some a := by
    show Option.map Prod.fst (flattenFormulaFuel? 2048 2048 φ φ.atomBound) = _
    rw [ha]
    rfl
  have hRF : readFreeFormula? a.formula = some ⟨rf, hrf0⟩ := by
    simp only [readFreeFormula?, hrf, Option.bind_eq_bind, Option.bind_some, hrf0, dif_pos]
    rfl
  have hR : readFlatten? 2048 φ = some ⟨a, src, Nat.le_refl _, L, ⟨rf, hrf0⟩⟩ := by
    simp only [readFlatten?, hflat, hsrc, hL, hRF, Option.bind_eq_bind, Option.bind_some]
    rfl
  have harith : (ReadFlattening.formula (⟨a, src, Nat.le_refl _, L, ⟨rf, hrf0⟩⟩ :
      ReadFlattening φ φ.atomBound)).Arith (fun _ => True) (fun _ => True)
        (fun _ => LedgerMode.post = .post) :=
    .imp ((ReadOccurrence.constraints_arith aocc).ledger_mono (fun _ h => h.elim)) aok
  have hsq : a.reads.length * a.reads.length ≤ 2048 := by rw [alen]; exact hw
  exact ⟨_, hR, hsq, leafArithmeticZ?_isSome _ ((harith.restrict
    (fun q hq => (List.mem_eraseDups' _ q).mpr hq)
    (fun e he => ((Inputs.unique_spec _).2 e).mpr he)).ledger_restrict
    (fun v hv => (List.mem_eraseDups' _ v).mpr hv))⟩

/-- **The flattened arithmetic with ledger entries never refuses its fragment.** -/
theorem flattenedArithmeticZ?_isSome (φ : LFml C) (h : φ.SrcL false true .post)
    (hn : φ.cutAll.nodes ≤ 511) (hw : φ.cutAll.words * φ.cutAll.words ≤ 2048) :
    (flattenedArithmeticZ? 2048 φ).isSome = true := by
  obtain ⟨src, hsrc⟩ := h.readFormula
  obtain ⟨r, hr, hsq, hE⟩ := readFlatten?_arithZ φ.cutAll (LFml.cutAll_src h) hn hw
  obtain ⟨E, hE'⟩ := Option.isSome_iff_exists.mp hE
  simp only [flattenedArithmeticZ?, hsrc, hr, Option.bind_eq_bind, Option.bind_some, hsq, if_true, hE']
  rfl

end Solidity.Decide
