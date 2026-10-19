import Solidity.Calculus.FlattenTotality

/-!
# Lifting removes every conditional of the fragment

`LFml.liftCond` (`Calculus/CondLift.lean`) lifts the elimination's
conditionals (`kite`, `ite`) out of equations.  On the source fragment with
conditionals (`LTm.Src true`), the lifted formula is in the fragment
without them (`LTm.Src false`), once the fuel exceeds the measure
`LFml.condMax`: each equation `a = b` weighs `2^|a| + 2^|b|`, `|t|` the
conditionals of `t`; a branch equation lowers one side, a guard equation is
over a conditional's operands, so every lifting step lowers the weight.
-/

namespace Solidity.Decide

variable {C : Contract}

/-- `1` at `ite`. -/
def _root_.Solidity.Op3.iteN {a b c s : Srt} : Op3 C a b c s → Nat
  | .ite => 1
  | _ => 0

/-- The conditionals of a term. -/
def LTm.conds : {s : Srt} → LTm C s → Nat
  | _, .var _ | _, .app0 _ | _, .err => 0
  | _, .app1 _ a | _, .obsW a | _, .obsL a | _, .obsH a => a.conds
  | _, .app2 _ a b | _, .index _ a b | _, .seq a b | _, .orElse a b => a.conds + b.conds
  | _, .app3 o a b c => a.conds + b.conds + c.conds + o.iteN
  | _, .kite a b t e => a.conds + b.conds + t.conds + e.conds + 1

theorem LTm.Src.sort_bool {c : Bool} : ∀ {k : SrcKind} {s : Srt} {t : LTm C s}, t.Src c k →
    k = .bool → s = .val .bool := by
  intro k s t h
  induction h with
  | ofNum | not | and | or | eqB | neB | eqN | neN | lt | gt | le | ge | seqB | seqN =>
    intro _; rfl
  | kite _ _ _ _ _ _ _ _ iht => intro hk; exact iht hk
  | ite _ _ _ _ _ _ iht => intro hk; exact iht hk
  | _ => intro hk; cases hk

/-- The operands a guard tests. -/
def CondGuard.Src : CondGuard C → Prop
  | .kite x y => x.Src true .num ∧ y.Src true .num
  | .ite d => d.Src true .bool

/-- The conditionals of a guard's operands. -/
def CondGuard.conds : CondGuard C → Nat
  | .kite x y => x.conds + y.conds
  | .ite d => d.conds

/-- A split of a fragment term: its parts in the fragment, each with fewer
conditionals. -/
def SplitOK {s : Srt} (k : SrcKind) (t : LTm C s) (r : CondSplit C s) : Prop :=
  r.thn.Src true k ∧ r.els.Src true k ∧ r.bad.Src true k ∧ r.guard.Src ∧
    r.thn.conds < t.conds ∧ r.els.conds < t.conds ∧ r.bad.conds < t.conds ∧
    r.guard.conds + 1 ≤ t.conds

theorem CondSplit.first_cases {s a b : Srt} {ix : Option (CondSplit C a)}
    {iy : Option (CondSplit C b)} {fx : LTm C a → LTm C s} {fy : LTm C b → LTm C s}
    {r : CondSplit C s} (h : CondSplit.first ix iy fx fy = some r) :
    (∃ r', ix = some r' ∧ r = r'.map fx) ∨ (ix = none ∧ ∃ r', iy = some r' ∧ r = r'.map fy) := by
  unfold CondSplit.first at h
  cases hx : ix with
  | some r' => rw [hx] at h; cases h; exact .inl ⟨r', rfl, rfl⟩
  | none =>
    rw [hx] at h
    cases hy : iy with
    | none => rw [hy] at h; cases h
    | some r' => rw [hy] at h; cases h; exact .inr ⟨rfl, r', rfl, rfl⟩

theorem CondSplit.first_none {s a b : Srt} {ix : Option (CondSplit C a)}
    {iy : Option (CondSplit C b)} {fx : LTm C a → LTm C s} {fy : LTm C b → LTm C s}
    (h : CondSplit.first ix iy fx fy = none) : ix = none ∧ iy = none := by
  unfold CondSplit.first at h
  cases hx : ix with
  | some r' => rw [hx] at h; cases h
  | none =>
    rw [hx] at h
    cases hy : iy with
    | none => exact ⟨rfl, rfl⟩
    | some r' => rw [hy] at h; cases h

/-- A binary node: its split is one operand's, under the node. -/
theorem SplitOK.bin {s a b : Srt} {k ka kb : SrcKind} {x : LTm C a} {y : LTm C b}
    (mk : LTm C a → LTm C b → LTm C s)
    (hmk : ∀ x' y', x'.Src true ka → y'.Src true kb → (mk x' y').Src true k)
    (hc : ∀ x' y', (mk x' y').conds = x'.conds + y'.conds)
    (hx : x.Src true ka) (hy : y.Src true kb)
    (ihx : ∀ r, x.condSplit = some r → SplitOK ka x r)
    (ihy : ∀ r, y.condSplit = some r → SplitOK kb y r)
    {t : LTm C s} (ht : t.condSplit = CondSplit.first x.condSplit y.condSplit (mk · y) (mk x ·))
    (htc : t.conds = x.conds + y.conds) :
    ∀ r, t.condSplit = some r → SplitOK k t r := by
  intro r hr
  rw [ht] at hr
  rcases CondSplit.first_cases hr with ⟨r', hr', rfl⟩ | ⟨_, r', hr', rfl⟩
  · obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := ihx r' hr'
    refine ⟨hmk _ _ h1 hy, hmk _ _ h2 hy, hmk _ _ h3 hy, h4, ?_, ?_, ?_, ?_⟩ <;>
      simp only [CondSplit.map, hc, htc] <;> omega
  · obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := ihy r' hr'
    refine ⟨hmk _ _ hx h1, hmk _ _ hx h2, hmk _ _ hx h3, h4, ?_, ?_, ?_, ?_⟩ <;>
      simp only [CondSplit.map, hc, htc] <;> omega

/-- A unary node: its split is its operand's, under the node. -/
theorem SplitOK.un {s a : Srt} {k ka : SrcKind} {x : LTm C a} (mk : LTm C a → LTm C s)
    (hmk : ∀ x', x'.Src true ka → (mk x').Src true k) (hc : ∀ x', (mk x').conds = x'.conds)
    (ihx : ∀ r, x.condSplit = some r → SplitOK ka x r)
    {t : LTm C s} (ht : t.condSplit = x.condSplit.map (·.map mk)) (htc : t.conds = x.conds) :
    ∀ r, t.condSplit = some r → SplitOK k t r := by
  intro r hr
  rw [ht] at hr
  cases hx : x.condSplit with
  | none => rw [hx] at hr; cases hr
  | some r' =>
    rw [hx] at hr
    cases hr
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := ihx r' hx
    refine ⟨hmk _ h1, hmk _ h2, hmk _ h3, h4, ?_, ?_, ?_, ?_⟩ <;>
      simp only [CondSplit.map, hc, htc] <;> omega

/-- **A fragment term splits into fragment parts with fewer conditionals.** -/
theorem LTm.Src.split : ∀ {k : SrcKind} {s : Srt} {t : LTm C s}, t.Src true k →
    ∀ r, t.condSplit = some r → SplitOK k t r := by
  intro k s t h
  induction h with
  | var | lit | env | err | root => intro r hr; cases hr
  | @add p h a b hx hy ihx ihy =>
    exact SplitOK.bin (fun x' y' => LTm.app2 (.binop .add h) x' y') (fun _ _ hx' hy' => .add h hx' hy') (fun _ _ => rfl)
      hx hy ihx ihy rfl rfl
  | @sub p h a b hx hy ihx ihy =>
    exact SplitOK.bin (fun x' y' => LTm.app2 (.binop .sub h) x' y') (fun _ _ hx' hy' => .sub h hx' hy') (fun _ _ => rfl)
      hx hy ihx ihy rfl rfl
  | @seq q p a b hx hy ihx ihy =>
    exact SplitOK.bin (fun x' y' => LTm.seq x' y') (fun _ _ hx' hy' => .seq hx' hy') (fun _ _ => rfl)
      hx hy ihx ihy rfl rfl
  | @and a b hx hy ihx ihy =>
    exact SplitOK.bin (fun x' y' => LTm.app2 (.binop .and rfl) x' y') (fun _ _ hx' hy' => .and hx' hy') (fun _ _ => rfl)
      hx hy ihx ihy rfl rfl
  | @or a b hx hy ihx ihy =>
    exact SplitOK.bin (fun x' y' => LTm.app2 (.binop .or rfl) x' y') (fun _ _ hx' hy' => .or hx' hy') (fun _ _ => rfl)
      hx hy ihx ihy rfl rfl
  | @eqB a b hx hy ihx ihy =>
    exact SplitOK.bin (fun x' y' => LTm.app2 (.binop .eqB rfl) x' y') (fun _ _ hx' hy' => .eqB hx' hy') (fun _ _ => rfl)
      hx hy ihx ihy rfl rfl
  | @neB a b hx hy ihx ihy =>
    exact SplitOK.bin (fun x' y' => LTm.app2 (.binop .neB rfl) x' y') (fun _ _ hx' hy' => .neB hx' hy') (fun _ _ => rfl)
      hx hy ihx ihy rfl rfl
  | @eqN p hp a b hx hy ihx ihy =>
    exact SplitOK.bin (fun x' y' => LTm.app2 (.binop .eqB rfl) x' y') (fun _ _ hx' hy' => .eqN hp hx' hy') (fun _ _ => rfl)
      hx hy ihx ihy rfl rfl
  | @neN p hp a b hx hy ihx ihy =>
    exact SplitOK.bin (fun x' y' => LTm.app2 (.binop .neB rfl) x' y') (fun _ _ hx' hy' => .neN hp hx' hy') (fun _ _ => rfl)
      hx hy ihx ihy rfl rfl
  | @lt p h a b hx hy ihx ihy =>
    exact SplitOK.bin (fun x' y' => LTm.app2 (.binop .lt h) x' y') (fun _ _ hx' hy' => .lt h hx' hy') (fun _ _ => rfl)
      hx hy ihx ihy rfl rfl
  | @gt p h a b hx hy ihx ihy =>
    exact SplitOK.bin (fun x' y' => LTm.app2 (.binop .gt h) x' y') (fun _ _ hx' hy' => .gt h hx' hy') (fun _ _ => rfl)
      hx hy ihx ihy rfl rfl
  | @le p h a b hx hy ihx ihy =>
    exact SplitOK.bin (fun x' y' => LTm.app2 (.binop .le h) x' y') (fun _ _ hx' hy' => .le h hx' hy') (fun _ _ => rfl)
      hx hy ihx ihy rfl rfl
  | @ge p h a b hx hy ihx ihy =>
    exact SplitOK.bin (fun x' y' => LTm.app2 (.binop .ge h) x' y') (fun _ _ hx' hy' => .ge h hx' hy') (fun _ _ => rfl)
      hx hy ihx ihy rfl rfl
  | @seqB a b hx hy ihx ihy =>
    exact SplitOK.bin (fun x' y' => LTm.seq x' y') (fun _ _ hx' hy' => .seqB hx' hy') (fun _ _ => rfl)
      hx hy ihx ihy rfl rfl
  | @seqN q hq a b hx hy ihx ihy =>
    exact SplitOK.bin (fun x' y' => LTm.seq x' y') (fun _ _ hx' hy' => .seqN hq hx' hy') (fun _ _ => rfl)
      hx hy ihx ihy rfl rfl
  | @key K V a b hx hy ihx ihy =>
    exact SplitOK.bin (fun x' y' => LTm.index .map x' y') (fun _ _ hx' hy' => .key hx' hy') (fun _ _ => rfl)
      hx hy ihx ihy rfl rfl
  | @word p q _ ih =>
    exact SplitOK.un (fun q' => LTm.obsW q') (fun _ h' => .word h') (fun _ => rfl) ih rfl rfl
  | @field sn f T h q _ ih =>
    exact SplitOK.un (fun q' => LTm.app1 (.field h) q') (fun _ h' => .field h h') (fun _ => rfl) ih rfl rfl
  | @not a _ ih =>
    exact SplitOK.un (fun a' => LTm.app1 (.unop .not rfl) a') (fun _ h' => .not h') (fun _ => rfl) ih rfl rfl
  | @ofNum t _ ih =>
    intro r hr
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := ih r hr
    exact ⟨.ofNum h1, .ofNum h2, .ofNum h3, h4, h5, h6, h7, h8⟩
  | @kite hc p q k hk x y t e hx hy ht he _ _ _ _ =>
    intro r hr
    cases hr
    have hbad : (LTm.err (C := C) (s := .val q)).Src true k := by
      cases k with
      | num => exact .err
      | bool =>
        have hq : (Srt.val q : Srt) = .val .bool := ht.sort_bool rfl
        cases hq
        exact .ofNum .err
      | path => exact absurd rfl hk
    refine ⟨ht, he, hbad, ⟨hx, hy⟩, ?_, ?_, ?_, ?_⟩ <;> simp only [LTm.conds, CondGuard.conds] <;> omega
  | @ite hc p k hk d t e hd ht he _ _ _ =>
    intro r hr
    cases hr
    have hbad : (LTm.err (C := C) (s := .val p)).Src true k := by
      cases k with
      | num => exact .err
      | bool =>
        have hq : (Srt.val p : Srt) = .val .bool := ht.sort_bool rfl
        cases hq
        exact .ofNum .err
      | path => exact absurd rfl hk
    refine ⟨ht, he, hbad, hd, ?_, ?_, ?_, ?_⟩ <;>
      simp only [LTm.conds, CondGuard.conds, Op3.iteN] <;> omega

/-- **A fragment term without a conditional is in the fragment without
them.** -/
theorem LTm.Src.noCond : ∀ {k : SrcKind} {s : Srt} {t : LTm C s}, t.Src true k →
    t.condSplit = none → t.Src false k := by
  intro k s t h
  induction h with
  | var i => intro _; exact .var i
  | lit v => intro _; exact .lit v
  | env e => intro _; exact .env e
  | err => intro _; exact .err
  | root r h => intro _; exact .root r h
  | @add p h a b _ _ ihx ihy =>
    intro hn
    have h2 := CondSplit.first_none (fx := fun x' => LTm.app2 (.binop .add h) x' _) (fy := fun y' => LTm.app2 (.binop .add h) _ y') hn
    exact .add h (ihx h2.1) (ihy h2.2)
  | @sub p h a b _ _ ihx ihy =>
    intro hn
    have h2 := CondSplit.first_none (fx := fun x' => LTm.app2 (.binop .sub h) x' _) (fy := fun y' => LTm.app2 (.binop .sub h) _ y') hn
    exact .sub h (ihx h2.1) (ihy h2.2)
  | @seq q p a b _ _ ihx ihy =>
    intro hn
    have h2 := CondSplit.first_none (fx := fun x' => LTm.seq x' _) (fy := fun y' => LTm.seq _ y') hn
    exact .seq (ihx h2.1) (ihy h2.2)
  | @and a b _ _ ihx ihy =>
    intro hn
    have h2 := CondSplit.first_none (fx := fun x' => LTm.app2 (.binop .and rfl) x' _) (fy := fun y' => LTm.app2 (.binop .and rfl) _ y') hn
    exact .and (ihx h2.1) (ihy h2.2)
  | @or a b _ _ ihx ihy =>
    intro hn
    have h2 := CondSplit.first_none (fx := fun x' => LTm.app2 (.binop .or rfl) x' _) (fy := fun y' => LTm.app2 (.binop .or rfl) _ y') hn
    exact .or (ihx h2.1) (ihy h2.2)
  | @eqB a b _ _ ihx ihy =>
    intro hn
    have h2 := CondSplit.first_none (fx := fun x' => LTm.app2 (.binop .eqB rfl) x' _) (fy := fun y' => LTm.app2 (.binop .eqB rfl) _ y') hn
    exact .eqB (ihx h2.1) (ihy h2.2)
  | @neB a b _ _ ihx ihy =>
    intro hn
    have h2 := CondSplit.first_none (fx := fun x' => LTm.app2 (.binop .neB rfl) x' _) (fy := fun y' => LTm.app2 (.binop .neB rfl) _ y') hn
    exact .neB (ihx h2.1) (ihy h2.2)
  | @eqN p hp a b _ _ ihx ihy =>
    intro hn
    have h2 := CondSplit.first_none (fx := fun x' => LTm.app2 (.binop .eqB rfl) x' _) (fy := fun y' => LTm.app2 (.binop .eqB rfl) _ y') hn
    exact .eqN hp (ihx h2.1) (ihy h2.2)
  | @neN p hp a b _ _ ihx ihy =>
    intro hn
    have h2 := CondSplit.first_none (fx := fun x' => LTm.app2 (.binop .neB rfl) x' _) (fy := fun y' => LTm.app2 (.binop .neB rfl) _ y') hn
    exact .neN hp (ihx h2.1) (ihy h2.2)
  | @lt p h a b _ _ ihx ihy =>
    intro hn
    have h2 := CondSplit.first_none (fx := fun x' => LTm.app2 (.binop .lt h) x' _) (fy := fun y' => LTm.app2 (.binop .lt h) _ y') hn
    exact .lt h (ihx h2.1) (ihy h2.2)
  | @gt p h a b _ _ ihx ihy =>
    intro hn
    have h2 := CondSplit.first_none (fx := fun x' => LTm.app2 (.binop .gt h) x' _) (fy := fun y' => LTm.app2 (.binop .gt h) _ y') hn
    exact .gt h (ihx h2.1) (ihy h2.2)
  | @le p h a b _ _ ihx ihy =>
    intro hn
    have h2 := CondSplit.first_none (fx := fun x' => LTm.app2 (.binop .le h) x' _) (fy := fun y' => LTm.app2 (.binop .le h) _ y') hn
    exact .le h (ihx h2.1) (ihy h2.2)
  | @ge p h a b _ _ ihx ihy =>
    intro hn
    have h2 := CondSplit.first_none (fx := fun x' => LTm.app2 (.binop .ge h) x' _) (fy := fun y' => LTm.app2 (.binop .ge h) _ y') hn
    exact .ge h (ihx h2.1) (ihy h2.2)
  | @seqB a b _ _ ihx ihy =>
    intro hn
    have h2 := CondSplit.first_none (fx := fun x' => LTm.seq x' _) (fy := fun y' => LTm.seq _ y') hn
    exact .seqB (ihx h2.1) (ihy h2.2)
  | @seqN q hq a b _ _ ihx ihy =>
    intro hn
    have h2 := CondSplit.first_none (fx := fun x' => LTm.seq x' _) (fy := fun y' => LTm.seq _ y') hn
    exact .seqN hq (ihx h2.1) (ihy h2.2)
  | @key K V a b _ _ ihx ihy =>
    intro hn
    have h2 := CondSplit.first_none (fx := fun x' => LTm.index .map x' _) (fy := fun y' => LTm.index .map _ y') hn
    exact .key (ihx h2.1) (ihy h2.2)
  | @word p q _ ih =>
    intro hn
    exact .word (ih (Option.map_eq_none_iff.mp hn))
  | @field sn f T h q _ ih =>
    intro hn
    exact .field h (ih (Option.map_eq_none_iff.mp hn))
  | @not a _ ih =>
    intro hn
    exact .not (ih (Option.map_eq_none_iff.mp hn))
  | ofNum _ ih => intro hn; exact .ofNum (ih hn)
  | kite => intro hn; cases hn
  | ite => intro hn; cases hn

/-! ## Formulas -/

/-- The lifting weight of a formula: its heaviest equation's. -/
def LFml.condMax : LFml C → Nat
  | .tt => 0
  | .eq a b => 2 ^ a.conds + 2 ^ b.conds
  | .not φ | .all _ _ φ => φ.condMax
  | .and φ ψ | .imp φ ψ => max φ.condMax ψ.condMax

theorem LFml.Src.ofNums {c : Bool} {p : PrimTy} {x y : LTm C (.val p)} (hx : x.Src c .num)
    (hy : y.Src c .num) : (LFml.eq x y).Src c := by
  cases p with
  | bool => exact .eqB (.ofNum hx) (.ofNum hy)
  | uint => exact .eqN rfl hx hy
  | int => exact .eqN rfl hx hy

theorem CondGuard.split_src {G : CondGuard C} {P Q R : LFml C} (hG : G.Src) (hP : P.Src true)
    (hQ : Q.Src true) (hR : R.Src true) : (G.split P Q R).Src true := by
  cases G with
  | kite x y =>
    obtain ⟨hx, hy⟩ := hG
    have hxy : (LFml.eq x y).Src true := LFml.Src.ofNums hx hy
    have hD : (LFml.and (.eq x x) (.eq y y)).Src true :=
      .and (LFml.Src.ofNums hx hx) (LFml.Src.ofNums hy hy)
    simp only [CondGuard.split]
    split
    · exact .and (.imp hxy hP) (.imp (.not hxy) hQ)
    · exact .and (.imp (.and hD hxy) hP) (.and (.imp (.and hD (.not hxy)) hQ) (.imp (.not hD) hR))
  | ite d =>
    have hd : d.Src true .bool := hG
    have ht : (LFml.eq d (.app0 (.lit true))).Src true := .eqB hd (.ofNum (.lit (p := .bool) true))
    have hf : (LFml.eq d (.app0 (.lit false))).Src true := .eqB hd (.ofNum (.lit (p := .bool) false))
    simp only [CondGuard.split]
    split
    · exact .and (.imp ht hP) (.imp hf hQ)
    · exact .and (.imp ht hP) (.and (.imp hf hQ) (.imp (.not (.eqB hd hd)) hR))

theorem CondGuard.split_condMax (G : CondGuard C) (P Q R : LFml C) :
    (G.split P Q R).condMax ≤ max (2 ^ (G.conds + 1)) (max P.condMax (max Q.condMax R.condMax)) := by
  cases G with
  | kite x y =>
    have hx : 2 ^ x.conds ≤ 2 ^ (x.conds + y.conds) := Nat.pow_le_pow_right (by decide) (by omega)
    have hy : 2 ^ y.conds ≤ 2 ^ (x.conds + y.conds) := Nat.pow_le_pow_right (by decide) (by omega)
    have h2 : 2 ^ (x.conds + y.conds + 1) = 2 * 2 ^ (x.conds + y.conds) := by
      rw [Nat.pow_succ]; omega
    simp only [CondGuard.split]
    split <;> simp only [LFml.condMax, CondGuard.conds, CondGuard.cases] <;> omega
  | ite d =>
    have h1 : 1 ≤ 2 ^ d.conds := Nat.one_le_two_pow
    have h2 : 2 ^ (d.conds + 1) = 2 * 2 ^ d.conds := by rw [Nat.pow_succ]; omega
    have hl : ∀ b : Bool, (LTm.app0 (C := C) (.lit (p := .bool) b)).conds = 0 := fun _ => rfl
    simp only [CondGuard.split]
    split <;> simp only [LFml.condMax, CondGuard.conds, CondGuard.cases, hl, Nat.pow_zero] <;> omega

theorem LTm.Src.split_weight {k : SrcKind} {s : Srt} {t : LTm C s} {r : CondSplit C s}
    (h : SplitOK k t r) (w : Nat) (hw : 1 ≤ w) :
    max (2 ^ (r.guard.conds + 1))
      (max (2 ^ r.thn.conds + w) (max (2 ^ r.els.conds + w) (2 ^ r.bad.conds + w))) <
        2 ^ t.conds + w ∧
    max (2 ^ (r.guard.conds + 1))
      (max (w + 2 ^ r.thn.conds) (max (w + 2 ^ r.els.conds) (w + 2 ^ r.bad.conds))) <
        w + 2 ^ t.conds := by
  obtain ⟨-, -, -, -, h5, h6, h7, h8⟩ := h
  have a1 : 2 ^ (r.guard.conds + 1) ≤ 2 ^ t.conds := Nat.pow_le_pow_right (by decide) h8
  have a2 : 2 ^ r.thn.conds < 2 ^ t.conds := Nat.pow_lt_pow_right (by decide) h5
  have a3 : 2 ^ r.els.conds < 2 ^ t.conds := Nat.pow_lt_pow_right (by decide) h6
  have a4 : 2 ^ r.bad.conds < 2 ^ t.conds := Nat.pow_lt_pow_right (by decide) h7
  constructor <;>
    refine Nat.max_lt.mpr ⟨by omega, Nat.max_lt.mpr ⟨by omega, Nat.max_lt.mpr ⟨by omega, by omega⟩⟩⟩

/-- **Lifting removes every conditional** of the fragment, given fuel above
its weight. -/
theorem LFml.liftCond_src : ∀ (n : Nat) {φ : LFml C}, φ.Src true → φ.condMax < n →
    (φ.liftCond n).Src false := by
  intro n
  induction n with
  | zero => intro φ _ h; omega
  | succ n ih =>
    intro φ hφ hm
    show (φ.mapEq (LFml.liftEq (LFml.liftCond n))).Src false
    induction hφ with
    | tt => exact .tt
    | @eqB a b ha hb =>
      show (LFml.liftEq (LFml.liftCond n) a b).Src false
      unfold LFml.liftEq
      cases hsa : a.condSplit with
      | some r =>
        have hr := ha.split r hsa
        apply ih (CondGuard.split_src hr.2.2.2.1 (.eqB hr.1 hb) (.eqB hr.2.1 hb) (.eqB hr.2.2.1 hb))
        have h1 := CondGuard.split_condMax r.guard (.eq r.thn b) (.eq r.els b) (.eq r.bad b)
        have h2 := (LTm.Src.split_weight hr (2 ^ b.conds) Nat.one_le_two_pow).1
        have hm' : 2 ^ a.conds + 2 ^ b.conds < n + 1 := hm
        exact Nat.lt_of_lt_of_le (Nat.lt_of_le_of_lt h1 h2) (by omega)
      | none =>
        cases hsb : b.condSplit with
        | some r =>
          have hr := hb.split r hsb
          apply ih (CondGuard.split_src hr.2.2.2.1 (.eqB ha hr.1) (.eqB ha hr.2.1) (.eqB ha hr.2.2.1))
          have h1 := CondGuard.split_condMax r.guard (.eq a r.thn) (.eq a r.els) (.eq a r.bad)
          have h2 := (LTm.Src.split_weight hr (2 ^ a.conds) Nat.one_le_two_pow).2
          have hm' : 2 ^ a.conds + 2 ^ b.conds < n + 1 := hm
          exact Nat.lt_of_lt_of_le (Nat.lt_of_le_of_lt h1 h2) (by omega)
        | none => exact .eqB (ha.noCond hsa) (hb.noCond hsb)
    | @eqN p hp a b ha hb =>
      show (LFml.liftEq (LFml.liftCond n) a b).Src false
      unfold LFml.liftEq
      cases hsa : a.condSplit with
      | some r =>
        have hr := ha.split r hsa
        apply ih (CondGuard.split_src hr.2.2.2.1 (.eqN hp hr.1 hb) (.eqN hp hr.2.1 hb)
          (.eqN hp hr.2.2.1 hb))
        have h1 := CondGuard.split_condMax r.guard (.eq r.thn b) (.eq r.els b) (.eq r.bad b)
        have h2 := (LTm.Src.split_weight hr (2 ^ b.conds) Nat.one_le_two_pow).1
        have hm' : 2 ^ a.conds + 2 ^ b.conds < n + 1 := hm
        exact Nat.lt_of_lt_of_le (Nat.lt_of_le_of_lt h1 h2) (by omega)
      | none =>
        cases hsb : b.condSplit with
        | some r =>
          have hr := hb.split r hsb
          apply ih (CondGuard.split_src hr.2.2.2.1 (.eqN hp ha hr.1) (.eqN hp ha hr.2.1)
            (.eqN hp ha hr.2.2.1))
          have h1 := CondGuard.split_condMax r.guard (.eq a r.thn) (.eq a r.els) (.eq a r.bad)
          have h2 := (LTm.Src.split_weight hr (2 ^ a.conds) Nat.one_le_two_pow).2
          have hm' : 2 ^ a.conds + 2 ^ b.conds < n + 1 := hm
          exact Nat.lt_of_lt_of_le (Nat.lt_of_le_of_lt h1 h2) (by omega)
        | none => exact .eqN hp (ha.noCond hsa) (hb.noCond hsb)
    | not _ ihφ =>
      simp only [LFml.condMax] at hm
      exact .not (ihφ hm)
    | and _ _ ihφ ihψ =>
      simp only [LFml.condMax] at hm
      exact .and (ihφ (by omega)) (ihψ (by omega))
    | imp _ _ ihφ ihψ =>
      simp only [LFml.condMax] at hm
      exact .imp (ihφ (by omega)) (ihψ (by omega))

/-! ## Lifting adds no atom -/

/-- The atoms a guard reads. -/
def CondGuard.parameters : CondGuard C → List Parameter
  | .kite x y => x.parameters ++ y.parameters
  | .ite d => d.parameters

/-- Every atom of a split's parts is in `L`. -/
def CondSplit.ParamsIn {s : Srt} (r : CondSplit C s) (L : List Parameter) : Prop :=
  ∀ q, q ∈ r.thn.parameters ∨ q ∈ r.els.parameters ∨ q ∈ r.bad.parameters ∨
    q ∈ r.guard.parameters → q ∈ L

theorem CondSplit.ParamsIn.map {s u : Srt} {r : CondSplit C s} {L L' E : List Parameter}
    (f : LTm C s → LTm C u) (hf : ∀ v q, q ∈ (f v).parameters → q ∈ v.parameters ∨ q ∈ E)
    (h : r.ParamsIn L) (hE : ∀ q ∈ E, q ∈ L') (hL : ∀ q ∈ L, q ∈ L') : (r.map f).ParamsIn L' := by
  intro q hq
  rcases hq with hq | hq | hq | hq
  · rcases hf _ q hq with h1 | h1
    · exact hL q (h q (.inl h1))
    · exact hE q h1
  · rcases hf _ q hq with h1 | h1
    · exact hL q (h q (.inr (.inl h1)))
    · exact hE q h1
  · rcases hf _ q hq with h1 | h1
    · exact hL q (h q (.inr (.inr (.inl h1))))
    · exact hE q h1
  · exact hL q (h q (.inr (.inr (.inr hq))))

theorem CondSplit.ParamsIn.first {s a b : Srt} {x : LTm C a} {y : LTm C b} {L : List Parameter}
    (fx : LTm C a → LTm C s) (fy : LTm C b → LTm C s)
    (hfx : ∀ v q, q ∈ (fx v).parameters → q ∈ v.parameters ∨ q ∈ y.parameters)
    (hfy : ∀ v q, q ∈ (fy v).parameters → q ∈ x.parameters ∨ q ∈ v.parameters)
    (hxL : ∀ q ∈ x.parameters, q ∈ L) (hyL : ∀ q ∈ y.parameters, q ∈ L)
    (ihx : ∀ r, x.condSplit = some r → r.ParamsIn x.parameters)
    (ihy : ∀ r, y.condSplit = some r → r.ParamsIn y.parameters) :
    ∀ r, CondSplit.first x.condSplit y.condSplit fx fy = some r → r.ParamsIn L := by
  intro r hr
  rcases CondSplit.first_cases hr with ⟨r', hr', rfl⟩ | ⟨_, r', hr', rfl⟩
  · exact (ihx r' hr').map fx hfx hyL hxL
  · exact (ihy r' hr').map fy (fun v q hq => (hfy v q hq).symm) hxL hyL

theorem LTm.condSplit_params {s : Srt} (t : LTm C s) :
    ∀ r, t.condSplit = some r → r.ParamsIn t.parameters := by
  have m2 : ∀ {α : Type} {q : α} {A B : List α}, q ∈ A ++ B → q ∈ A ∨ q ∈ B := fun h => List.mem_append.mp h
  have l2 : ∀ {α : Type} {q : α} {A B : List α}, q ∈ A → q ∈ A ++ B := fun h => List.mem_append.mpr (.inl h)
  have r2 : ∀ {α : Type} {q : α} {A B : List α}, q ∈ B → q ∈ A ++ B := fun h => List.mem_append.mpr (.inr h)
  induction t with
  | var | app0 | err => intro r hr; cases hr
  | app1 o x ih =>
    intro r hr
    change x.condSplit.map (·.map (LTm.app1 o)) = some r at hr
    cases hx : x.condSplit with
    | none => rw [hx] at hr; cases hr
    | some r' =>
      rw [hx] at hr; cases hr
      exact (ih r' hx).map (LTm.app1 o) (E := []) (fun _ _ h => .inl h) (fun _ h => by cases h) (fun _ h => h)
  | obsW x ih =>
    intro r hr
    change x.condSplit.map (·.map LTm.obsW) = some r at hr
    cases hx : x.condSplit with
    | none => rw [hx] at hr; cases hr
    | some r' =>
      rw [hx] at hr; cases hr
      exact (ih r' hx).map LTm.obsW (E := []) (fun _ _ h => .inl h) (fun _ h => by cases h) (fun _ h => h)
  | obsL x ih =>
    intro r hr
    change x.condSplit.map (·.map LTm.obsL) = some r at hr
    cases hx : x.condSplit with
    | none => rw [hx] at hr; cases hr
    | some r' =>
      rw [hx] at hr; cases hr
      exact (ih r' hx).map LTm.obsL (E := []) (fun _ _ h => .inl h) (fun _ h => by cases h) (fun _ h => h)
  | obsH x ih =>
    intro r hr
    change x.condSplit.map (·.map LTm.obsH) = some r at hr
    cases hx : x.condSplit with
    | none => rw [hx] at hr; cases hr
    | some r' =>
      rw [hx] at hr; cases hr
      exact (ih r' hx).map LTm.obsH (E := []) (fun _ _ h => .inl h) (fun _ h => by cases h) (fun _ h => h)
  | app2 o x y ihx ihy =>
    exact CondSplit.ParamsIn.first _ _ (fun _ _ h => m2 h) (fun _ _ h => m2 h) (fun _ h => l2 h)
      (fun _ h => r2 h) ihx ihy
  | index it x y ihx ihy =>
    exact CondSplit.ParamsIn.first _ _ (fun _ _ h => m2 h) (fun _ _ h => m2 h) (fun _ h => l2 h)
      (fun _ h => r2 h) ihx ihy
  | seq x y ihx ihy =>
    exact CondSplit.ParamsIn.first _ _ (fun _ _ h => m2 h) (fun _ _ h => m2 h) (fun _ h => l2 h)
      (fun _ h => r2 h) ihx ihy
  | orElse x y ihx ihy =>
    exact CondSplit.ParamsIn.first _ _ (fun _ _ h => m2 h) (fun _ _ h => m2 h) (fun _ h => l2 h)
      (fun _ h => r2 h) ihx ihy
  | kite a b t e =>
    intro r hr
    cases hr
    intro q hq
    simp only [LTm.parameters, CondGuard.parameters, List.mem_append] at hq ⊢
    grind
  | app3 o x y z ihx ihy ihz =>
    intro r hr
    cases o with
    | ite =>
      cases hr
      intro q hq
      simp only [LTm.parameters, CondGuard.parameters, List.mem_append] at hq ⊢
      grind
    | _ =>
      change CondSplit.first3 x.condSplit y.condSplit z.condSplit _ _ _ = some r at hr
      unfold CondSplit.first3 at hr
      cases hx : x.condSplit with
      | some r' =>
        rw [hx] at hr; cases hr
        refine (ihx r' hx).map _ (E := y.parameters ++ z.parameters) ?_ ?_ ?_ <;> intros <;>
          rename_i h <;> simp only [LTm.parameters, List.mem_append] at h ⊢ <;> grind
      | none =>
        rw [hx] at hr
        rcases CondSplit.first_cases hr with ⟨r', hr', rfl⟩ | ⟨_, r', hr', rfl⟩
        · refine (ihy r' hr').map _ (E := x.parameters ++ z.parameters) ?_ ?_ ?_ <;> intros <;>
            rename_i h <;> simp only [LTm.parameters, List.mem_append] at h ⊢ <;> grind
        · refine (ihz r' hr').map _ (E := x.parameters ++ y.parameters) ?_ ?_ ?_ <;> intros <;>
            rename_i h <;> simp only [LTm.parameters, List.mem_append] at h ⊢ <;> grind

theorem CondGuard.split_params (G : CondGuard C) (P Q R : LFml C) (q : Parameter)
    (h : q ∈ (G.split P Q R).parameters) :
    q ∈ G.parameters ∨ q ∈ P.parameters ∨ q ∈ Q.parameters ∨ q ∈ R.parameters := by
  cases G with
  | kite x y =>
    simp only [CondGuard.split] at h
    split at h <;>
      simp only [CondGuard.cases, LFml.parameters, CondGuard.parameters,
        List.mem_append] at h ⊢ <;> grind
  | ite d =>
    simp only [CondGuard.split] at h
    split at h <;>
      simp only [CondGuard.cases, LFml.parameters, LTm.parameters, CondGuard.parameters,
        List.mem_append, List.not_mem_nil] at h ⊢ <;> grind

theorem LFml.mapEq_params (f : {p : PrimTy} → LTm C (.val p) → LTm C (.val p) → LFml C)
    (hf : ∀ {p : PrimTy} (a b : LTm C (.val p)) q, q ∈ (f a b).parameters →
      q ∈ a.parameters ∨ q ∈ b.parameters) :
    ∀ (φ : LFml C) q, q ∈ (φ.mapEq f).parameters → q ∈ φ.parameters
  | .tt, _, h => h
  | .eq a b, q, h => List.mem_append.mpr (hf a b q h)
  | .not φ, q, h => LFml.mapEq_params f hf φ q h
  | .all _ _ φ, q, h => LFml.mapEq_params f hf φ q h
  | .and φ ψ, q, h | .imp φ ψ, q, h => by
    simp only [LFml.mapEq, LFml.parameters, List.mem_append] at h ⊢
    rcases h with h | h
    · exact .inl (LFml.mapEq_params f hf φ q h)
    · exact .inr (LFml.mapEq_params f hf ψ q h)

/-- **Lifting adds no atom.** -/
theorem LFml.liftCond_params : ∀ (n : Nat) (φ : LFml C) q, q ∈ (φ.liftCond n).parameters →
    q ∈ φ.parameters := by
  intro n
  induction n with
  | zero => intro φ q h; exact h
  | succ n ih =>
    intro φ
    apply LFml.mapEq_params
    intro p a b q h
    unfold LFml.liftEq at h
    cases ha : a.condSplit with
    | some r =>
      rw [ha] at h
      have hr := LTm.condSplit_params a r ha
      rcases CondGuard.split_params _ _ _ _ q (ih _ q h) with h | h | h | h <;>
        (try simp only [LFml.parameters, List.mem_append] at h)
      · exact .inl (hr q (.inr (.inr (.inr h))))
      · exact h.elim (fun h => .inl (hr q (.inl h))) .inr
      · exact h.elim (fun h => .inl (hr q (.inr (.inl h)))) .inr
      · exact h.elim (fun h => .inl (hr q (.inr (.inr (.inl h))))) .inr
    | none =>
      rw [ha] at h
      cases hb : b.condSplit with
      | some r =>
        rw [hb] at h
        have hr := LTm.condSplit_params b r hb
        rcases CondGuard.split_params _ _ _ _ q (ih _ q h) with h | h | h | h <;>
          (try simp only [LFml.parameters, List.mem_append] at h)
        · exact .inr (hr q (.inr (.inr (.inr h))))
        · exact h.elim .inl (fun h => .inr (hr q (.inl h)))
        · exact h.elim .inl (fun h => .inr (hr q (.inr (.inl h))))
        · exact h.elim .inl (fun h => .inr (hr q (.inr (.inr (.inl h)))))
      | none =>
        rw [hb] at h
        exact List.mem_append.mp h

end Solidity.Decide
