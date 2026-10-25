import Solidity.Semantics.RunFuel
import Solidity.Semantics.RunFrame

/-!
# Loops run in closed form

`Prog.runF` (`Semantics/RunFuel.lean`) gives up on a loop after `n`
iterations.  A counting loop's outcome after any number of them has a closed
form: here a loop whose body only adds literals to `uint` locals
(`x = x + d;`, `x += d;`, `x++;`, `++x;`, each local once, `Prog.bumps?`)
and whose condition compares one local against a term the body leaves alone
(`i < e`, `i <= e`, `e > i`, `e >= i`: `Val.guard?`, `Val.rigid?`) is run in
O(1): to the iteration where the condition first fails, or to the first one
an addition overflows in (a revert), whichever comes first (`TRun.accel?`).
`TRun.accel?_sound` proves it is the typed run's outcome (`TRun.loop`);
`Prog.runA` is `Prog.runF` with every loop of that shape so accelerated,
approximating the typed run as it does (`Prog.runA_approx`).
Counterexamples evaluate it in the kernel (`Tools/Counterexample.lean`): a
loop bounded by an array of `2^255` elements reverts on its first overflow
without its `2^255` iterations.

The recognizers are `match`-based (a deviation from Gate G0's condition 1,
cheap on the loop bodies they see); the run itself is the recursor
(`Prog.runA`) with its compiled twin (`Prog.runAC`, `Prog.runA_eq`).
-/

namespace Solidity

variable {C : Contract}

/-! ## A loop run along a closed form -/

namespace TLoop

variable {α : Type}

theorem iterN_of_steps {body : α → TRes α} {c : α → TRes Bool} (f : Nat → α) (K : Nat)
    {r : TRes α} (hstep : ∀ k, k < K → step body c (f k) = .inl (f (k + 1)))
    (hlast : step body c (f K) = .inr r) :
    ∀ m j, j + m = K → iterN body c (m + 1) (f j) = .inr r
  | 0, j, h => by
    subst h
    rw [Nat.add_zero] at hlast
    simp only [iterN, hlast]
  | m + 1, j, h => by
    have hj : j < K := by omega
    rw [iterN, hstep j hj]
    exact iterN_of_steps f K hstep hlast m (j + 1) (by omega)

/-- **A loop along a closed form**: `f k` the state at the head of the
`k`-th iteration, which goes on for `k < K` and is done at `K`. -/
theorem run_of_steps {body : α → TRes α} {c : α → TRes Bool} (f : Nat → α) (K : Nat)
    {r : TRes α} (hstep : ∀ k, k < K → step body c (f k) = .inl (f (k + 1)))
    (hlast : step body c (f K) = .inr r) : run body c (f 0) = r :=
  run_of_iterN (iterN_of_steps f K hstep hlast K 0 (Nat.zero_add K))

end TLoop

/-! ## Counters -/

/-- A counter `x = x + d;`: a `uint` local and the literal each iteration
adds to it. -/
abbrev Bump (Γ : Ctx) := Idx Γ (.val .uint) × Nat

/-- The counters run one after the other: a revert on the first that
overflows. -/
def bumpRun {Γ : Ctx} : List (Bump Γ) → State C Γ → TRes (State C Γ)
  | [], τ => .ok τ
  | (i, d) :: bs, τ =>
    match PrimTy.ofInt? .uint ((TEnv.get i τ.env : PrimTy.uint.Denote).1 + (d : Int)) with
    | some v => bumpRun bs (τ.setLocal i v)
    | none => .error .revert

/-- `P` runs as its counters do from `τ`, its scope ends taken. -/
def Prog.BumpsAt {Γ Γ' : Ctx} (P : Prog C Γ Γ') (bs : List (Bump Γ)) (τ : State C Γ) : Prop :=
  match bumpRun bs τ with
  | .ok τ' => ∃ o, Prog.runR P τ = .ok o ∧ o.st.drop P.ext = τ'
  | .error e => Prog.runR P τ = .error e

/-- `s` runs as the counter `(i, d)`: `i` stepped by `d`, a revert past the
bound. -/
def Stmt.Bumps {Γ : Ctx} (s : Stmt C Γ Γ) (i : Idx Γ (.val .uint)) (d : Nat) : Prop :=
  s.ext = .refl ∧ ∀ τ : State C Γ, Stmt.runR s τ =
    match PrimTy.ofInt? .uint ((TEnv.get i τ.env : PrimTy.uint.Denote).1 + (d : Int)) with
    | some v => .ok ⟨τ.setLocal i v, List.prefix_refl _⟩
    | none => .error .revert

theorem Stmt.bumps_assign {Γ : Ctx} (i : Idx Γ (.val .uint)) (n : Int)
    (hn : PrimTy.uint.inRange n = true) (h : BinOp.accepts .add .uint = true)
    (hq : BinOp.ret .add .uint = .uint) :
    (Stmt.assignLocal (C := C) i (.binop .add h hq (.simple (.local i)) (.simple (.lit n hn)))).Bumps
      i n.toNat := by
  have hn' : ((n.toNat : Nat) : Int) = n := by
    simp only [PrimTy.inRange, decide_eq_true_eq] at hn
    omega
  refine ⟨rfl, fun τ => ?_⟩
  show TRun.assignLocal i _ τ = _
  simp only [TRun.assignLocal, Val.evalT, Simple.evalT, BinOp.shortT, BinOp.evalT, BinOp.evalNum,
    BinOp.arithInt, hn']
  have hl : (PrimTy.uint.ofLit n hn).val = n := rfl
  cases h' : PrimTy.uint.ofInt? ((TEnv.get i τ.env).val + n) <;>
    simp only [hl, h', Option.bind, TRes.ofOpt, bind, Except.bind, pure, Except.pure]

theorem Stmt.bumps_opAssign {Γ : Ctx} (i : Idx Γ (.val .uint)) (n : Int)
    (hn : PrimTy.uint.inRange n = true) (hop : BinOp.hasCompoundAssign .add = true)
    (hp : PrimTy.isNumeric .uint = true) :
    (Stmt.opAssign (C := C) .add hop hp (.local i) (.simple (.lit n hn))).Bumps i n.toNat := by
  have hn' : ((n.toNat : Nat) : Int) = n := by
    simp only [PrimTy.inRange, decide_eq_true_eq] at hn
    omega
  refine ⟨rfl, fun τ => ?_⟩
  show TRun.opAssign .add (.local i) _ τ = _
  simp only [TRun.opAssign, Val.evalT, Simple.evalT, OpLoc.storeT, compoundT, BinOp.arithInt,
    PrimTy.key, hn']
  have hl : (PrimTy.uint.ofLit n hn).val = n := rfl
  cases h' : PrimTy.uint.ofInt? ((TEnv.get i τ.env).val + n) <;>
    simp only [hl, h', Option.bind, TRes.ofOpt, bind, Except.bind, pure, Except.pure]

theorem Stmt.bumps_incDec {Γ : Ctx} (i : Idx Γ (.val .uint)) (op : IncDec)
    (hop : op.isIncrement = true) (hp : PrimTy.isNumeric .uint = true) :
    (Stmt.incDec (C := C) op hp (.local i)).Bumps i 1 := by
  refine ⟨rfl, fun τ => ?_⟩
  show TRun.incDec op (.local i) τ = _
  simp only [TRun.incDec, OpLoc.bumpT, bumpT, hop, if_true, PrimTy.key, Int.natCast_one]
  cases PrimTy.uint.ofInt? ((TEnv.get i τ.env).val + 1) <;>
    simp only [TRes.ofOpt, bind, Except.bind, pure, Except.pure]

theorem State.drop_refl_trans {Γ Δ : Ctx} (h : Ext Γ Δ) (σ : State C Δ) :
    σ.drop (Ext.refl.trans h) = σ.drop h := by
  simp only [State.drop, TEnv.drop_trans]
  rfl

theorem Prog.bumpsAt_cons {Γ Γ' : Ctx} (s : Stmt C Γ Γ) (i : Idx Γ (.val .uint)) (d : Nat)
    (hs : s.Bumps i d) (P : Prog C Γ Γ') (bs : List (Bump Γ))
    (hP : ∀ τ, P.BumpsAt bs τ) (τ : State C Γ) : (Prog.cons s P).BumpsAt ((i, d) :: bs) τ := by
  unfold Prog.BumpsAt
  have e1 : (Prog.cons s P).runR τ = TRun.seq (Stmt.runR s) (Prog.runR P) τ := rfl
  have e2 : (Prog.cons s P).ext = Ext.refl.trans P.ext := by
    show s.ext.trans P.ext = _
    rw [hs.1]
  rw [e1, e2]
  simp only [bumpRun, TRun.seq, hs.2 τ, State.drop_refl_trans]
  cases hv : PrimTy.ofInt? .uint ((TEnv.get i τ.env : PrimTy.uint.Denote).1 + (d : Int)) with
  | none => rfl
  | some v =>
    have h1 := hP (τ.setLocal i v)
    unfold Prog.BumpsAt at h1
    simp only
    revert h1
    cases bumpRun bs (τ.setLocal i v) with
    | ok τ' =>
      rintro ⟨o, ho, hd⟩
      exact ⟨_, by rw [ho]; rfl, hd⟩
    | error e => intro h1; rw [h1]; rfl

/-- A statement that counts: `x = x + d;`, `x += d;`, `x++;` or `++x;` at a
`uint` local, with the proof. -/
def Stmt.bump? {Γ : Ctx} : (s : Stmt C Γ Γ) → Option {b : Bump Γ // s.Bumps b.1 b.2}
  | .assignLocal (p := .uint) i
      (.binop (p := .uint) .add h hq (.simple (.local j)) (.simple (.lit n hn))) =>
    if hij : j = i then some ⟨(i, n.toNat), by subst hij; exact Stmt.bumps_assign j n hn h hq⟩
    else none
  | .opAssign (p := .uint) .add hop hp (.local i) (.simple (.lit n hn)) =>
    some ⟨(i, n.toNat), Stmt.bumps_opAssign i n hn hop hp⟩
  | .incDec (p := .uint) .preInc hp (.local i) => some ⟨(i, 1), Stmt.bumps_incDec i _ rfl hp⟩
  | .incDec (p := .uint) .postInc hp (.local i) => some ⟨(i, 1), Stmt.bumps_incDec i _ rfl hp⟩
  | _ => none

/-- A counting statement in front of a counting body. -/
def Prog.consBumps {Γ Γ' : Ctx} (s : Stmt C Γ Γ) (P : Prog C Γ Γ')
    (r : Option {bs : List (Bump Γ) // ∀ τ, P.BumpsAt bs τ}) :
    Option {bs : List (Bump Γ) // ∀ τ, (Prog.cons s P).BumpsAt bs τ} :=
  match Stmt.bump? s, r with
  | some b, some bs => some ⟨b.1 :: bs.1, Prog.bumpsAt_cons s b.1.1 b.1.2 b.2 P bs.1 bs.2⟩
  | _, _ => none

/-- **A loop body that only counts**, `x₁ = x₁ + d₁; …; xₘ = xₘ + dₘ;`, with
the proof that it runs as its counters (`Prog.BumpsAt`). -/
def Prog.bumps? : {Γ Γ' : Ctx} → (P : Prog C Γ Γ') →
    Option {bs : List (Bump Γ) // ∀ τ, P.BumpsAt bs τ}
  | _, _, .nil => some ⟨[], fun τ => ⟨⟨τ, List.prefix_refl _⟩, rfl, rfl⟩⟩
  | _, _, .cons (.assignLocal i r) P => Prog.consBumps (.assignLocal i r) P (Prog.bumps? P)
  | _, _, .cons (.opAssign op hop hp l r) P =>
    Prog.consBumps (.opAssign op hop hp l r) P (Prog.bumps? P)
  | _, _, .cons (.incDec op hp l) P => Prog.consBumps (.incDec op hp l) P (Prog.bumps? P)
  | _, _, .cons _ _ => none

/-! ## The counters after `k` iterations -/

/-- A `uint` of the integer `n`, `0` out of range. -/
def uintD (n : Int) : PrimTy.uint.Denote := (PrimTy.ofInt? .uint n).getD (PrimTy.dflt .uint)

theorem uintD_val {n : Int} (h0 : 0 ≤ n) (h1 : n < 2 ^ 256) : (uintD n).1 = n := by
  have hr : PrimTy.uint.inRange n = true := by
    simp only [PrimTy.inRange, decide_eq_true_eq]; omega
  simp only [uintD, PrimTy.ofInt?, hr, dite_true, Option.getD_some]

theorem uint_bounds (v : PrimTy.uint.Denote) : 0 ≤ v.1 ∧ v.1 < 2 ^ 256 := by
  have h := v.2
  simp only [PrimTy.inRange, decide_eq_true_eq] at h
  omega

/-- The counters' positions. -/
def Bump.pos {Γ : Ctx} (bs : List (Bump Γ)) : List Nat := bs.map (·.1.toNat)

/-- Each counter's local set to its value in `src` and `k` steps. -/
def TEnv.bumpK {H : HTy} {Γ : Ctx} (src : TEnv C H Γ) (k : Nat) :
    List (Bump Γ) → TEnv C H Γ → TEnv C H Γ
  | [], e => e
  | (i, d) :: bs, e => TEnv.bumpK src k bs
      (TEnv.set i (uintD ((TEnv.get i src : PrimTy.uint.Denote).1 + ((k * d : Nat) : Int))) e)

section BumpK

variable {H : HTy} {Γ : Ctx}

theorem TEnv.get_bumpK_out {t : LTy} (p : Idx Γ t) (src : TEnv C H Γ) (k : Nat) :
    (bs : List (Bump Γ)) → (e : TEnv C H Γ) → p.toNat ∉ Bump.pos bs →
    TEnv.get p (TEnv.bumpK src k bs e) = TEnv.get p e
  | [], _, _ => rfl
  | (i, d) :: bs, e, h => by
    simp only [Bump.pos, List.map_cons, List.mem_cons, not_or] at h
    rw [TEnv.bumpK, TEnv.get_bumpK_out p src k bs _ h.2]
    exact TEnv.get_set_ne i p _ e (fun h' => h.1 h'.symm)

theorem TEnv.get_bumpK_in (src : TEnv C H Γ) (k : Nat) :
    (bs : List (Bump Γ)) → (e : TEnv C H Γ) → (Bump.pos bs).Nodup → ∀ i d, (i, d) ∈ bs →
    TEnv.get i (TEnv.bumpK src k bs e) =
      uintD ((TEnv.get i src : PrimTy.uint.Denote).1 + ((k * d : Nat) : Int))
  | [], _, _, _, _, h => nomatch h
  | (i₀, d₀) :: bs, e, hnd, i, d, h => by
    simp only [Bump.pos, List.map_cons, List.nodup_cons] at hnd
    rw [TEnv.bumpK]
    rcases List.mem_cons.mp h with h | h
    · obtain ⟨h1, h2⟩ := Prod.mk.inj h
      subst h1; subst h2
      rw [TEnv.get_bumpK_out i src k bs _ hnd.1]
      exact TEnv.get_set i _ e
    · exact TEnv.get_bumpK_in src k bs _ hnd.2 i d h

theorem TEnv.bumpK_congr (src src' : TEnv C H Γ) (k : Nat) :
    (bs : List (Bump Γ)) → (e : TEnv C H Γ) → (∀ i d, (i, d) ∈ bs → TEnv.get i src = TEnv.get i src') →
    TEnv.bumpK src k bs e = TEnv.bumpK src' k bs e
  | [], _, _ => rfl
  | (i, d) :: bs, e, h => by
    rw [TEnv.bumpK, TEnv.bumpK, h i d (List.mem_cons_self ..)]
    exact TEnv.bumpK_congr src src' k bs _ fun i' d' h' => h i' d' (List.mem_cons_of_mem _ h')

/-- Two positions with the same number are one, at one type. -/
theorem Idx.eq_of_toNat_eq' {t u : LTy} (p : Idx Γ t) (i : Idx Γ u) (h : p.toNat = i.toNat) :
    ∃ ht : t = u, ht ▸ p = i := by
  have h1 := Idx.getElem?_toNat p
  have h2 := Idx.getElem?_toNat i
  rw [h, h2] at h1
  cases Option.some.inj h1
  exact ⟨rfl, Idx.toNat_inj p i h⟩

end BumpK

/-- **The counters run once**: all of them in range, the locals stepped;
otherwise the first that overflows reverts. -/
theorem bumpRun_eq {Γ : Ctx} : (bs : List (Bump Γ)) → (Bump.pos bs).Nodup → (τ : State C Γ) →
    bumpRun bs τ =
      if bs.all (fun b => decide ((TEnv.get b.1 τ.env : PrimTy.uint.Denote).1 + (b.2 : Int) <
          2 ^ 256)) then
        .ok { τ with env := TEnv.bumpK τ.env 1 bs τ.env }
      else .error .revert
  | [], _, τ => rfl
  | (i, d) :: bs, hnd, τ => by
    have hnd' := hnd
    simp only [Bump.pos, List.map_cons, List.nodup_cons] at hnd'
    have hv := uint_bounds (TEnv.get i τ.env)
    by_cases hr : (TEnv.get i τ.env : PrimTy.uint.Denote).1 + (d : Int) < 2 ^ 256
    · have hin : PrimTy.uint.inRange ((TEnv.get i τ.env : PrimTy.uint.Denote).1 + (d : Int)) = true := by
        simp only [PrimTy.inRange, decide_eq_true_eq]; omega
      have hagree : ∀ i' d', (i', d') ∈ bs →
          TEnv.get i' (TEnv.set i (⟨_, hin⟩ : PrimTy.uint.Denote) τ.env) = TEnv.get i' τ.env :=
        fun i' d' h' => TEnv.get_set_ne i i' _ _ fun e => hnd'.1 (by
          rw [e]; exact List.mem_map.mpr ⟨(i', d'), h', rfl⟩)
      have ih := bumpRun_eq bs hnd'.2 (τ.setLocal i ⟨_, hin⟩)
      simp only [bumpRun, PrimTy.ofInt?, hin, dite_true, ih, List.all_cons, hr, decide_true,
        Bool.true_and]
      have hall : (bs.all fun b => decide ((TEnv.get b.1 (τ.setLocal i ⟨_, hin⟩).env :
            PrimTy.uint.Denote).1 + (b.2 : Int) < 2 ^ 256)) =
          (bs.all fun b => decide ((TEnv.get b.1 τ.env : PrimTy.uint.Denote).1 + (b.2 : Int) <
            2 ^ 256)) := by
        refine Bool.eq_iff_iff.mpr ?_
        simp only [List.all_eq_true]
        exact forall_congr' fun b => imp_congr_right fun hb => by
          rw [show (τ.setLocal i ⟨_, hin⟩).env = TEnv.set i ⟨_, hin⟩ τ.env from rfl,
            hagree b.1 b.2 hb]
      rw [hall]
      split
      · congr 2
        show TEnv.bumpK (TEnv.set i _ τ.env) 1 bs (TEnv.set i _ τ.env) =
          TEnv.bumpK τ.env 1 bs (TEnv.set i _ τ.env)
        rw [TEnv.bumpK_congr _ τ.env 1 bs _ hagree]
        congr 2
        apply Subtype.ext
        rw [uintD_val (by omega) (by omega)]
        simp only [Nat.one_mul]
      · rfl
    · have hout : PrimTy.uint.inRange ((TEnv.get i τ.env : PrimTy.uint.Denote).1 + (d : Int)) = false := by
        simp only [PrimTy.inRange, decide_eq_false_iff_not]; omega
      simp only [bumpRun, PrimTy.ofInt?, hout, List.all_cons, hr, decide_false, Bool.false_and]
      rfl

/-- The state at the head of a counting loop's `k`-th iteration from `σ`. -/
def State.bumpK {Γ : Ctx} (σ : State C Γ) (bs : List (Bump Γ)) (k : Nat) : State C Γ :=
  { σ with env := TEnv.bumpK σ.env k bs σ.env }

/-- Every counter in range after `k` steps from `σ`. -/
def Bump.InRange {Γ : Ctx} (σ : State C Γ) (bs : List (Bump Γ)) (k : Nat) : Prop :=
  ∀ b ∈ bs, (TEnv.get b.1 σ.env : PrimTy.uint.Denote).1 + ((k * b.2 : Nat) : Int) < 2 ^ 256

theorem Bump.InRange.zero {Γ : Ctx} (σ : State C Γ) (bs : List (Bump Γ)) : Bump.InRange σ bs 0 :=
  fun b _ => by
    have := uint_bounds (TEnv.get b.1 σ.env)
    simp only [Nat.zero_mul, Int.natCast_zero, Int.add_zero]
    exact this.2

theorem Bump.InRange.mono {Γ : Ctx} {σ : State C Γ} {bs : List (Bump Γ)} {k : Nat}
    (h : Bump.InRange σ bs (k + 1)) : Bump.InRange σ bs k := fun b hb => by
  have h1 := h b hb
  have h2 : k * b.2 ≤ (k + 1) * b.2 := Nat.mul_le_mul_right _ (Nat.le_succ k)
  have h3 : ((k * b.2 : Nat) : Int) ≤ (((k + 1) * b.2 : Nat) : Int) := Int.ofNat_le.mpr h2
  omega

theorem Out.eq_of_st {H : HTy} {Γ : Ctx} {a b : Out C H Γ} (h : a.st = b.st) : a = b := by
  cases a; cases b; cases h; rfl

section Closed

variable {Γ : Ctx} (σ : State C Γ) (bs : List (Bump Γ))

theorem State.get_bumpK_in (hnd : (Bump.pos bs).Nodup) {k : Nat} (hk : Bump.InRange σ bs k)
    (b : Bump Γ) (hb : b ∈ bs) :
    (TEnv.get b.1 (σ.bumpK bs k).env : PrimTy.uint.Denote).1 =
      (TEnv.get b.1 σ.env : PrimTy.uint.Denote).1 + ((k * b.2 : Nat) : Int) := by
  show (TEnv.get b.1 (TEnv.bumpK σ.env k bs σ.env) : PrimTy.uint.Denote).1 = _
  rw [TEnv.get_bumpK_in σ.env k bs σ.env hnd b.1 b.2 hb]
  have := uint_bounds (TEnv.get b.1 σ.env)
  exact uintD_val (by omega) (hk b hb)

theorem State.bumpK_zero (hnd : (Bump.pos bs).Nodup) : σ.bumpK bs 0 = σ := by
  show { σ with env := TEnv.bumpK σ.env 0 bs σ.env } = σ
  have : TEnv.bumpK σ.env 0 bs σ.env = σ.env := by
    apply TEnv.ext
    intro t p
    by_cases hp : p.toNat ∈ Bump.pos bs
    · obtain ⟨b, hb, hbp⟩ := List.mem_map.mp hp
      obtain ⟨ht, hpe⟩ := Idx.eq_of_toNat_eq' p b.1 hbp.symm
      subst ht
      subst hpe
      rw [TEnv.get_bumpK_in σ.env 0 bs σ.env hnd b.1 b.2 hb]
      apply Subtype.ext
      have := uint_bounds (TEnv.get b.1 σ.env)
      rw [uintD_val (by simp only [Nat.zero_mul]; omega) (by simp only [Nat.zero_mul]; omega)]
      simp only [Nat.zero_mul, Int.natCast_zero, Int.add_zero]
    · exact TEnv.get_bumpK_out p σ.env 0 bs σ.env hp
  rw [this]

theorem State.bumpK_succ (hnd : (Bump.pos bs).Nodup) {k : Nat} (hk : Bump.InRange σ bs (k + 1)) :
    bumpRun bs (σ.bumpK bs k) = .ok (σ.bumpK bs (k + 1)) := by
  have hk0 := hk.mono
  rw [bumpRun_eq bs hnd]
  have hall : (bs.all fun b => decide ((TEnv.get b.1 (σ.bumpK bs k).env : PrimTy.uint.Denote).1 +
      (b.2 : Int) < 2 ^ 256)) = true := by
    simp only [List.all_eq_true, decide_eq_true_eq]
    intro b hb
    rw [State.get_bumpK_in σ bs hnd hk0 b hb]
    have := hk b hb
    rw [Nat.succ_mul, Int.natCast_add] at this
    omega
  rw [if_pos hall]
  congr 1
  show { σ with env := TEnv.bumpK (σ.bumpK bs k).env 1 bs (σ.bumpK bs k).env } =
    { σ with env := TEnv.bumpK σ.env (k + 1) bs σ.env }
  have : TEnv.bumpK (σ.bumpK bs k).env 1 bs (σ.bumpK bs k).env = TEnv.bumpK σ.env (k + 1) bs σ.env := by
    apply TEnv.ext
    intro t p
    by_cases hp : p.toNat ∈ Bump.pos bs
    · obtain ⟨b, hb, hbp⟩ := List.mem_map.mp hp
      obtain ⟨ht, hpe⟩ := Idx.eq_of_toNat_eq' p b.1 hbp.symm
      subst ht
      subst hpe
      rw [TEnv.get_bumpK_in _ 1 bs _ hnd b.1 b.2 hb, TEnv.get_bumpK_in _ (k + 1) bs _ hnd b.1 b.2 hb]
      have e1 := State.get_bumpK_in σ bs hnd hk0 b hb
      have e2 : (TEnv.get b.1 (σ.bumpK bs k).env : PrimTy.uint.Denote).1 + ((1 * b.2 : Nat) : Int) =
          (TEnv.get b.1 σ.env : PrimTy.uint.Denote).1 + (((k + 1) * b.2 : Nat) : Int) := by
        rw [e1, Nat.one_mul, Nat.succ_mul, Int.natCast_add, Int.add_assoc]
      rw [e2]
    · rw [TEnv.get_bumpK_out p _ 1 bs _ hp, TEnv.get_bumpK_out p _ (k + 1) bs _ hp]
      exact TEnv.get_bumpK_out p σ.env k bs σ.env hp
  rw [this]

theorem State.bumpK_ovf (hnd : (Bump.pos bs).Nodup) {k : Nat} (hk : Bump.InRange σ bs k)
    (hk' : ¬ Bump.InRange σ bs (k + 1)) : bumpRun bs (σ.bumpK bs k) = .error .revert := by
  rw [bumpRun_eq bs hnd]
  have hall : (bs.all fun b => decide ((TEnv.get b.1 (σ.bumpK bs k).env : PrimTy.uint.Denote).1 +
      (b.2 : Int) < 2 ^ 256)) = false := by
    apply Bool.eq_false_iff.mpr
    intro h
    apply hk'
    simp only [List.all_eq_true, decide_eq_true_eq] at h
    intro b hb
    have := h b hb
    rw [State.get_bumpK_in σ bs hnd hk b hb] at this
    rw [Nat.succ_mul, Int.natCast_add]
    omega
  rw [if_neg (by rw [hall]; exact Bool.false_ne_true)]

end Closed

/-! ## The condition -/

/-- A loop condition `x < e` (`δ = 0`) or `x <= e` (`δ = 1`), either way
round. -/
structure Guard (C : Contract) (Γ : Ctx) where
  x : Idx Γ (.val .uint)
  e : Val C Γ .uint
  δ : Nat

/-- What `c` evaluates to, read as the guard `g`. -/
def Guard.Spec {Γ : Ctx} (c : Val C Γ .bool) (g : Guard C Γ) : Prop :=
  ∀ τ : State C Γ, c.evalT τ = (g.e.evalT τ).map fun y =>
    decide ((TEnv.get g.x τ.env : PrimTy.uint.Denote).1 < y.1 + (g.δ : Int))

section Guards

variable {Γ : Ctx} (x : Idx Γ (.val .uint)) (e : Val C Γ .uint)

theorem Guard.spec_lt (h : BinOp.accepts .lt .uint = true) (hq : BinOp.ret .lt .uint = .bool) :
    Guard.Spec (.binop .lt h hq (.simple (.local x)) e) ⟨x, e, 0⟩ := fun τ => by
  simp only [Val.evalT, Simple.evalT, BinOp.shortT, BinOp.evalT, BinOp.evalNum, Int.natCast_zero,
    Int.add_zero]
  cases e.evalT τ <;> rfl

theorem Guard.spec_le (h : BinOp.accepts .le .uint = true) (hq : BinOp.ret .le .uint = .bool) :
    Guard.Spec (.binop .le h hq (.simple (.local x)) e) ⟨x, e, 1⟩ := fun τ => by
  simp only [Val.evalT, Simple.evalT, BinOp.shortT, BinOp.evalT, BinOp.evalNum]
  cases e.evalT τ with
  | error _ => rfl
  | ok y =>
    show Except.ok (decide (_ ≤ _)) = Except.ok (decide (_ < _))
    congr 1
    exact decide_eq_decide.mpr (by simp only [Int.natCast_one]; omega)

theorem Guard.spec_gt (h : BinOp.accepts .gt .uint = true) (hq : BinOp.ret .gt .uint = .bool) :
    Guard.Spec (.binop .gt h hq e (.simple (.local x))) ⟨x, e, 0⟩ := fun τ => by
  simp only [Val.evalT, Simple.evalT, BinOp.shortT, BinOp.evalT, BinOp.evalNum, Int.natCast_zero,
    Int.add_zero]
  cases e.evalT τ <;> rfl

theorem Guard.spec_ge (h : BinOp.accepts .ge .uint = true) (hq : BinOp.ret .ge .uint = .bool) :
    Guard.Spec (.binop .ge h hq e (.simple (.local x))) ⟨x, e, 1⟩ := fun τ => by
  simp only [Val.evalT, Simple.evalT, BinOp.shortT, BinOp.evalT, BinOp.evalNum]
  cases e.evalT τ with
  | error _ => rfl
  | ok y =>
    show Except.ok (decide (_ ≤ _)) = Except.ok (decide (_ < _))
    congr 1
    exact decide_eq_decide.mpr (by simp only [Int.natCast_one]; omega)

end Guards

/-- A loop condition comparing a `uint` local against a `uint` term, with
the proof that it reads so. -/
def Val.guard? {Γ : Ctx} : (c : Val C Γ .bool) → Option {g : Guard C Γ // g.Spec c}
  | .binop (p := .uint) .lt h hq (.simple (.local x)) e => some ⟨_, Guard.spec_lt x e h hq⟩
  | .binop (p := .uint) .le h hq (.simple (.local x)) e => some ⟨_, Guard.spec_le x e h hq⟩
  | .binop (p := .uint) .gt h hq e (.simple (.local x)) => some ⟨_, Guard.spec_gt x e h hq⟩
  | .binop (p := .uint) .ge h hq e (.simple (.local x)) => some ⟨_, Guard.spec_ge x e h hq⟩
  | _ => none

/-- `e` reads none of the locals at the positions `ps`: it evaluates alike in
every state that differs from `σ` only there. -/
def Val.Rigid {Γ : Ctx} {p : PrimTy} (ps : List Nat) (e : Val C Γ p) : Prop :=
  ∀ (σ : State C Γ) (env' : TEnv C σ.H Γ),
    (∀ q (j : Idx Γ (.val q)), j.toNat ∉ ps → TEnv.get j env' = TEnv.get j σ.env) →
    e.evalT { σ with env := env' } = e.evalT σ

/-- A term the counters leave alone: literals, the transaction, other
locals, a root's value or length, and operators over them; with the proof. -/
def Val.rigid? {Γ : Ctx} (ps : List Nat) : {p : PrimTy} → (e : Val C Γ p) →
    Option (PLift (e.Rigid ps))
  | _, .simple (.lit _ _) => some ⟨fun _ _ _ => rfl⟩
  | _, .simple (.bool _) => some ⟨fun _ _ _ => rfl⟩
  | _, .simple (.env _ _) => some ⟨fun _ _ _ => rfl⟩
  | _, .simple (.local j) =>
    if hj : j.toNat ∈ ps then none else some ⟨fun σ env' h => by
      show Except.ok (TEnv.get j env') = Except.ok (TEnv.get j σ.env)
      rw [h _ j hj]⟩
  | _, .len (.loc (.root _ _)) _ => some ⟨fun _ _ _ => rfl⟩
  | _, .read (.root _ _) => some ⟨fun _ _ _ => rfl⟩
  | _, .binop _ _ _ a b => match Val.rigid? ps a, Val.rigid? ps b with
    | some ha, some hb => some ⟨fun σ env' hσ => by
        simp only [Val.evalT]
        rw [ha.down σ env' hσ, hb.down σ env' hσ]⟩
    | _, _ => none
  | _, .unop _ _ _ a => match Val.rigid? ps a with
    | some ha => some ⟨fun σ env' hσ => by
        simp only [Val.evalT]
        rw [ha.down σ env' hσ]⟩
    | none => none
  | _, _ => none

/-! ## The bounds -/

/-- How many iterations every counter `(v, d)` survives: the first `k` at
which one of them overflows, `none` when none of them moves. -/
def ovfBound : List (Nat × Nat) → Option Nat
  | [] => none
  | (v, d) :: r => if d = 0 then ovfBound r else
      some (match ovfBound r with
        | some t => min ((2 ^ 256 - 1 - v) / d) t
        | none => (2 ^ 256 - 1 - v) / d)

theorem ovf_one {v d k : Nat} (hv : v < 2 ^ 256) (hd : 0 < d) :
    v + (k + 1) * d < 2 ^ 256 ↔ k < (2 ^ 256 - 1 - v) / d := by
  rw [Nat.lt_iff_add_one_le (m := k), Nat.le_div_iff_mul_le hd]
  omega

theorem ovfBound_none : (l : List (Nat × Nat)) → ovfBound l = none → ∀ p ∈ l, p.2 = 0
  | [], _, _, h => nomatch h
  | (v, d) :: r, h, p, hp => by
    unfold ovfBound at h
    by_cases hd : d = 0
    · rw [if_pos hd] at h
      rcases List.mem_cons.mp hp with hp | hp
      · rw [hp]; exact hd
      · exact ovfBound_none r h p hp
    · rw [if_neg hd] at h; exact nomatch h

theorem ovfBound_some : (l : List (Nat × Nat)) → (∀ p ∈ l, p.1 < 2 ^ 256) → ∀ T, ovfBound l = some T →
    ∀ k, (∀ p ∈ l, p.1 + (k + 1) * p.2 < 2 ^ 256) ↔ k < T
  | [], _, _, h, _ => nomatch h
  | (v, d) :: r, hl, T, h, k => by
    have hv : v < 2 ^ 256 := hl (v, d) (List.mem_cons_self ..)
    have hr : ∀ p ∈ r, p.1 < 2 ^ 256 := fun p hp => hl p (List.mem_cons_of_mem _ hp)
    simp only [List.forall_mem_cons]
    unfold ovfBound at h
    by_cases hd : d = 0
    · rw [if_pos hd] at h
      rw [ovfBound_some r hr T h k]
      subst hd
      simp only [Nat.mul_zero, Nat.add_zero, hv, true_and]
    · rw [if_neg hd] at h
      have hd' : 0 < d := Nat.pos_of_ne_zero hd
      rw [ovf_one hv hd']
      cases hb : ovfBound r with
      | none =>
        rw [hb] at h
        cases h
        have h0 := ovfBound_none r hb
        constructor
        · exact fun h => h.1
        · intro hk
          refine ⟨hk, fun p hp => ?_⟩
          rw [h0 p hp, Nat.mul_zero, Nat.add_zero]
          exact hr p hp
      | some t =>
        rw [hb] at h
        cases h
        rw [ovfBound_some r hr t hb k, Nat.lt_min]

/-- The first iteration at which `x₀ + k * dx < L` fails, `none` when it
never does. -/
def guardBound (x0 dx L : Nat) : Option Nat :=
  if L ≤ x0 then some 0 else if dx = 0 then none else some ((L - x0 + dx - 1) / dx)

theorem guardBound_some {x0 dx L K : Nat} (h : guardBound x0 dx L = some K) (k : Nat) :
    x0 + k * dx < L ↔ k < K := by
  unfold guardBound at h
  by_cases hL : L ≤ x0
  · rw [if_pos hL] at h
    cases h
    constructor
    · intro h'; omega
    · intro h'; omega
  · rw [if_neg hL] at h
    by_cases hd : dx = 0
    · rw [if_pos hd] at h; exact nomatch h
    · rw [if_neg hd] at h
      cases h
      have hd' : 0 < dx := Nat.pos_of_ne_zero hd
      rw [Nat.lt_iff_add_one_le (m := k), Nat.le_div_iff_mul_le hd', Nat.succ_mul]
      omega

theorem guardBound_none {x0 dx L : Nat} (h : guardBound x0 dx L = none) (k : Nat) :
    x0 + k * dx < L := by
  unfold guardBound at h
  by_cases hL : L ≤ x0
  · rw [if_pos hL] at h; exact nomatch h
  · rw [if_neg hL] at h
    by_cases hd : dx = 0
    · subst hd
      rw [Nat.mul_zero]
      omega
    · rw [if_neg hd] at h; exact nomatch h

/-! ## The loop accelerated -/

/-- What the counters add to `x` each iteration: `0` where `x` is not one. -/
def Bump.step {Γ : Ctx} (bs : List (Bump Γ)) (x : Idx Γ (.val .uint)) : Nat :=
  match bs.find? (fun b => b.1 = x) with
  | some b => b.2
  | none => 0

theorem State.get_bumpK_x {Γ : Ctx} (σ : State C Γ) (bs : List (Bump Γ))
    (hnd : (Bump.pos bs).Nodup) {k : Nat} (hk : Bump.InRange σ bs k) (x : Idx Γ (.val .uint)) :
    (TEnv.get x (σ.bumpK bs k).env : PrimTy.uint.Denote).1 =
      (TEnv.get x σ.env : PrimTy.uint.Denote).1 + ((k * Bump.step bs x : Nat) : Int) := by
  unfold Bump.step
  cases hf : bs.find? (fun b => b.1 = x) with
  | some b =>
    have hb := List.mem_of_find?_eq_some hf
    have hx := List.find?_some hf
    simp only [decide_eq_true_eq] at hx
    subst hx
    exact State.get_bumpK_in σ bs hnd hk b hb
  | none =>
    have hout : x.toNat ∉ Bump.pos bs := by
      intro hm
      obtain ⟨b, hb, hbx⟩ := List.mem_map.mp hm
      have hx : b.1 = x := Idx.toNat_inj _ _ hbx
      have := List.find?_eq_none.mp hf b hb
      exact this (decide_eq_true hx)
    show (TEnv.get x (TEnv.bumpK σ.env k bs σ.env) : PrimTy.uint.Denote).1 = _
    rw [TEnv.get_bumpK_out x σ.env k bs σ.env hout, Nat.mul_zero, Int.natCast_zero, Int.add_zero]

/-- **A counting loop in closed form**: its outcome from `σ`, or `none` where
the loop is not of that shape or does not move.  `K` is the iteration where
the condition fails, `T` the last every counter survives. -/
def TRun.accel? {Γ Γ₁ : Ctx} (c : Val C Γ .bool) (body : Prog C Γ Γ₁) (σ : State C Γ) :
    Option (TRes (Out C σ.H Γ)) :=
  match body.bumps?, c.guard? with
  | some bs, some g =>
    if (Bump.pos bs.1).Nodup then
      match g.1.e.rigid? (Bump.pos bs.1), g.1.e.evalT σ with
      | some _, .ok E =>
        match ovfBound (bs.1.map fun b => ((TEnv.get b.1 σ.env : PrimTy.uint.Denote).1.toNat, b.2)) with
        | none => none
        | some T =>
          match guardBound (TEnv.get g.1.x σ.env : PrimTy.uint.Denote).1.toNat
              (Bump.step bs.1 g.1.x) (E.1.toNat + g.1.δ) with
          | some K =>
            if K ≤ T then some (.ok ⟨σ.bumpK bs.1 K, List.prefix_refl _⟩) else some (.error .revert)
          | none => some (.error .revert)
      | _, _ => none
    else none
  | _, _ => none

section Sound

variable {Γ Γ₁ : Ctx} (c : Val C Γ .bool) (body : Prog C Γ Γ₁) (σ : State C Γ)
  (bs : List (Bump Γ)) (hbs : ∀ τ, body.BumpsAt bs τ) (hnd : (Bump.pos bs).Nodup)

/-- The loop's head states, `k` iterations in. -/
abbrev TRun.heads (k : Nat) : Out C σ.H Γ := ⟨σ.bumpK bs k, List.prefix_refl _⟩

include hbs hnd in
theorem TRun.heads_step_go (G : Nat → Bool)
    (hcond : ∀ k, Bump.InRange σ bs k → c.evalT (σ.bumpK bs k) = .ok (G k)) {k : Nat}
    (hG : G k = true) (hk : Bump.InRange σ bs (k + 1)) :
    TLoop.step (fun o : Out C σ.H Γ =>
        (Prog.runR body o.st).map fun o' => ⟨o'.st.drop body.ext, o.ext.trans o'.ext⟩)
      (fun o => c.evalT o.st) (TRun.heads σ bs k) = .inl (TRun.heads σ bs (k + 1)) := by
  unfold TLoop.step
  dsimp only [TRun.heads]
  rw [hcond k hk.mono, hG]
  have h := hbs (σ.bumpK bs k)
  unfold Prog.BumpsAt at h
  rw [State.bumpK_succ σ bs hnd hk] at h
  obtain ⟨o', ho', hd⟩ := h
  simp only [ho', Except.map]
  exact congrArg Sum.inl (Out.eq_of_st hd)

include hbs hnd in
theorem TRun.heads_step_ovf (G : Nat → Bool)
    (hcond : ∀ k, Bump.InRange σ bs k → c.evalT (σ.bumpK bs k) = .ok (G k)) {k : Nat}
    (hG : G k = true) (hk : Bump.InRange σ bs k) (hk' : ¬ Bump.InRange σ bs (k + 1)) :
    TLoop.step (fun o : Out C σ.H Γ =>
        (Prog.runR body o.st).map fun o' => ⟨o'.st.drop body.ext, o.ext.trans o'.ext⟩)
      (fun o => c.evalT o.st) (TRun.heads σ bs k) = .inr (.error .revert) := by
  unfold TLoop.step
  dsimp only [TRun.heads]
  rw [hcond k hk, hG]
  have h := hbs (σ.bumpK bs k)
  unfold Prog.BumpsAt at h
  rw [State.bumpK_ovf σ bs hnd hk hk'] at h
  simp only [h, Except.map]

include hnd in
theorem TRun.heads_zero : TRun.heads σ bs 0 = ⟨σ, List.prefix_refl _⟩ :=
  Out.eq_of_st (State.bumpK_zero σ bs hnd)

include hbs hnd in
/-- The loop exits at `K`, every counter in range. -/
theorem TRun.loop_exit (G : Nat → Bool)
    (hcond : ∀ k, Bump.InRange σ bs k → c.evalT (σ.bumpK bs k) = .ok (G k)) (K : Nat)
    (hgo : ∀ k, k < K → G k = true ∧ Bump.InRange σ bs (k + 1)) (hG : G K = false)
    (hK : Bump.InRange σ bs K) :
    TRun.loop c body.ext (Prog.runR body) σ = .ok (TRun.heads σ bs K) := by
  unfold TRun.loop
  rw [← TRun.heads_zero σ bs hnd]
  refine TLoop.run_of_steps (TRun.heads σ bs) K (fun k hk => ?_) ?_
  · exact TRun.heads_step_go c body σ bs hbs hnd G hcond (hgo k hk).1 (hgo k hk).2
  · unfold TLoop.step
    dsimp only [TRun.heads]
    rw [hcond K hK, hG]

include hbs hnd in
/-- The loop reverts at `T`, where a counter overflows. -/
theorem TRun.loop_ovf (G : Nat → Bool)
    (hcond : ∀ k, Bump.InRange σ bs k → c.evalT (σ.bumpK bs k) = .ok (G k)) (T : Nat)
    (hgo : ∀ k, k < T → G k = true ∧ Bump.InRange σ bs (k + 1)) (hG : G T = true)
    (hT : Bump.InRange σ bs T) (hT' : ¬ Bump.InRange σ bs (T + 1)) :
    TRun.loop c body.ext (Prog.runR body) σ = .error .revert := by
  unfold TRun.loop
  rw [← TRun.heads_zero σ bs hnd]
  refine TLoop.run_of_steps (TRun.heads σ bs) T (fun k hk => ?_) ?_
  · exact TRun.heads_step_go c body σ bs hbs hnd G hcond (hgo k hk).1 (hgo k hk).2
  · exact TRun.heads_step_ovf c body σ bs hbs hnd G hcond hG hT hT'

end Sound

theorem Bump.inRange_iff {Γ : Ctx} (σ : State C Γ) (bs : List (Bump Γ)) (k : Nat) :
    Bump.InRange σ bs k ↔ ∀ p ∈ bs.map (fun b => ((TEnv.get b.1 σ.env : PrimTy.uint.Denote).1.toNat, b.2)),
      p.1 + k * p.2 < 2 ^ 256 := by
  simp only [Bump.InRange, List.forall_mem_map]
  refine forall_congr' fun b => imp_congr_right fun _ => ?_
  have h := uint_bounds (TEnv.get b.1 σ.env)
  have e : (((TEnv.get b.1 σ.env : PrimTy.uint.Denote).1.toNat : Nat) : Int) =
      (TEnv.get b.1 σ.env : PrimTy.uint.Denote).1 := Int.toNat_of_nonneg h.1
  omega

/-- **The accelerated loop is the loop.** -/
theorem TRun.accel?_sound {Γ Γ₁ : Ctx} (c : Val C Γ .bool) (body : Prog C Γ Γ₁) (σ : State C Γ)
    {r : TRes (Out C σ.H Γ)} (h : TRun.accel? c body σ = some r) :
    r = TRun.loop c body.ext (Prog.runR body) σ := by
  unfold TRun.accel? at h
  split at h
  · rename_i bs g _ _
    obtain ⟨bs, hbs⟩ := bs
    obtain ⟨g, hg⟩ := g
    split at h
    · rename_i hnd
      split at h
      · rename_i hr E _ _
        have hr := hr.down
        have hE : g.e.evalT σ = .ok E := by assumption
        have hl : ∀ p ∈ bs.map (fun b => ((TEnv.get b.1 σ.env : PrimTy.uint.Denote).1.toNat, b.2)),
            p.1 < 2 ^ 256 := by
          simp only [List.forall_mem_map]
          intro b _
          have := uint_bounds (TEnv.get b.1 σ.env)
          omega
        have hcond : ∀ k, Bump.InRange σ bs k → c.evalT (σ.bumpK bs k) =
            .ok (decide ((TEnv.get g.x σ.env : PrimTy.uint.Denote).1.toNat + k * Bump.step bs g.x <
              E.1.toNat + g.δ)) := by
          intro k hk
          rw [hg (σ.bumpK bs k)]
          have hrig : g.e.evalT (σ.bumpK bs k) = g.e.evalT σ :=
            hr σ _ fun q j hj => TEnv.get_bumpK_out j σ.env k bs σ.env hj
          rw [hrig, hE]
          show Except.ok _ = Except.ok _
          congr 1
          apply decide_eq_decide.mpr
          rw [State.get_bumpK_x σ bs hnd hk g.x]
          have h1 := uint_bounds (TEnv.get g.x σ.env)
          have h2 := uint_bounds E
          have e1 : (((TEnv.get g.x σ.env : PrimTy.uint.Denote).1.toNat : Nat) : Int) =
            (TEnv.get g.x σ.env : PrimTy.uint.Denote).1 := Int.toNat_of_nonneg h1.1
          have e2 : ((E.1.toNat : Nat) : Int) = E.1 := Int.toNat_of_nonneg h2.1
          omega
        split at h
        · exact nomatch h
        · rename_i T hT
          have hinr : ∀ k, Bump.InRange σ bs (k + 1) ↔ k < T := fun k =>
            (Bump.inRange_iff σ bs (k + 1)).trans (ovfBound_some _ hl T hT k)
          have hinT : ∀ k, k ≤ T → Bump.InRange σ bs k := fun k hk => by
            cases k with
            | zero => exact Bump.InRange.zero σ bs
            | succ k => exact (hinr k).mpr (by omega)
          have hT' : ¬ Bump.InRange σ bs (T + 1) := fun h' => Nat.lt_irrefl T ((hinr T).mp h')
          split at h
          · rename_i K hK
            have hgK := guardBound_some hK
            split at h
            · rename_i hKT
              cases h
              exact (TRun.loop_exit c body σ bs hbs hnd _ hcond K
                (fun k hk => ⟨decide_eq_true ((hgK k).mpr hk), (hinr k).mpr (by omega)⟩)
                (decide_eq_false fun h' => Nat.lt_irrefl K ((hgK K).mp h')) (hinT K hKT)).symm
            · rename_i hKT
              cases h
              exact (TRun.loop_ovf c body σ bs hbs hnd _ hcond T
                (fun k hk => ⟨decide_eq_true ((hgK k).mpr (by omega)), (hinr k).mpr hk⟩)
                (decide_eq_true ((hgK T).mpr (by omega))) (hinT T (Nat.le_refl T)) hT').symm
          · rename_i hK
            cases h
            exact (TRun.loop_ovf c body σ bs hbs hnd _ hcond T
              (fun k hk => ⟨decide_eq_true (guardBound_none hK k), (hinr k).mpr hk⟩)
              (decide_eq_true (guardBound_none hK T)) (hinT T (Nat.le_refl T)) hT').symm
      · exact nomatch h
    · exact nomatch h
  · exact nomatch h

/-! ## The loop, accelerated where it counts -/

/-- `while` with at most `n` iterations, unless it is a counting loop, which
runs in closed form (`TRun.accel?`). -/
def TRun.loopA {Γ Γ₁ : Ctx} (n : Nat) (c : Val C Γ .bool) (body : Prog C Γ Γ₁)
    (f : TStep C Γ Γ₁) : TStep C Γ Γ := fun σ =>
  match TRun.accel? c body σ with
  | some r => r
  | none => TRun.loopF n c body.ext f σ

theorem TRun.loopA_approx {Γ Γ₁ : Ctx} (n : Nat) (c : Val C Γ .bool) (body : Prog C Γ Γ₁)
    {f : TStep C Γ Γ₁} (hf : TStep.Approx f (Prog.runR body)) :
    TStep.Approx (TRun.loopA n c body f) (TRun.loop c body.ext (Prog.runR body)) := fun σ => by
  unfold TRun.loopA
  split
  · rename_i r h
    rw [← TRun.accel?_sound c body σ h]
    exact .refl _
  · exact TRun.loopF_approx n c body.ext hf σ

/-! ## Running a program, counting loops accelerated -/

mutual

/-- The compiled accelerated run with fuel of a statement. -/
def Stmt.runAC (n : Nat) : {Γ Γ' : Ctx} → Stmt C Γ Γ' → TStep C Γ Γ'
  | _, _, .assign l r => TRun.assign l r
  | _, _, .rebind i r => TRun.rebind i r
  | _, _, .assignLocal i r => TRun.assignLocal i r
  | _, _, .declLocal p _ init => TRun.declLocal p init
  | _, _, .declStorage R _ init => TRun.declStorage R init
  | _, _, .opAssign op _ _ l r => TRun.opAssign op l r
  | _, _, .incDec op _ l => TRun.incDec op l
  | _, _, .pushOpAssign op _ _ b r => TRun.pushOpAssign op b r
  | _, _, .pushIncDec op _ b => TRun.pushIncDec op b
  | _, _, .assignIncDec i op _ l _ => TRun.assignIncDec i op l
  | _, _, .assignLocalPush i b => TRun.assignLocalPush i b
  | _, _, .push b v _ => TRun.push b v
  | _, _, .pop b => TRun.pop b
  | _, _, .transfer r a => TRun.transfer r a
  | _, _, .send pv r a _ => TRun.send pv r a
  | _, _, .declMem R _ init _ hm => TRun.declMem R init hm
  | _, _, .rebindMem i r => TRun.rebindMem i r
  | _, _, .assignFromMem l p => TRun.assignFromMem l p
  | _, _, .assignMem l r => TRun.assignMem l r
  | _, _, .delete l => TRun.delete l
  | _, _, .deleteMem p _ => TRun.deleteMem p
  | _, _, .assignNew l n' h => TRun.assignNew l n' h
  | _, _, .ite c thn els => TRun.ite c thn.ext (Prog.runAC n thn) els.ext (Prog.runAC n els)
  | _, _, .require c => TRun.require c
  | _, _, .assert c => TRun.assert c
  | _, _, .revert => fun _ => .error .revert
  | _, _, .assumeFalse => fun _ => .error .exhausted
  | _, _, .call _ args ret body => TRun.call args ret body.ext (Prog.runAC n body)
  | _, _, .callReceiver _ args r body op =>
    TRun.callReceiver args r body.ext (Prog.runAC n body) op
  | _, _, .callReceiverPush _ args r body code value =>
    TRun.callReceiverPush args r body.ext (Prog.runAC n body)
      code.ext (Prog.runAC n code) value
  | _, _, .tryCall call rets ok err code pnc other sargs sbody self =>
    TRun.tryCall call rets ok.ext (Prog.runAC n ok) err.ext (Prog.runAC n err) code pnc.ext
      (Prog.runAC n pnc) other.ext (Prog.runAC n other) sargs sbody.ext (Prog.runAC n sbody) self
  | _, _, .loop _ c body => TRun.loopA n c body (Prog.runAC n body)
  | _, _, .block body => TRun.block body.ext (Prog.runAC n body)
  | _, _, .callRec _ _ args ret body =>
    TRun.call args ret (body ()).ext (Prog.runAC n (body ()))
  | _, _, .revertData d => TRun.revertData d
  | _, _, .catchData c rets sargs sbody self kind _ body =>
    TRun.catchData c rets sargs sbody.ext (Prog.runAC n sbody) self kind body.ext (Prog.runAC n body)

/-- The compiled accelerated run with fuel of a sequence. -/
def Prog.runAC (n : Nat) : {Γ Γ' : Ctx} → Prog C Γ Γ' → TStep C Γ Γ'
  | _, _, .nil => TRun.nil
  | _, _, .cons s P => TRun.seq (Stmt.runAC n s) (Prog.runAC n P)

end

/-- The typed run of a statement with each loop entered at most `n`
iterations, by its recursor (`Stmt.runR`'s, the loop `TRun.loopA`). -/
@[implemented_by Stmt.runAC]
def Stmt.runA (n : Nat) {Γ Γ' : Ctx} (s : Stmt C Γ Γ') : TStep C Γ Γ' :=
  Stmt.rec (motive_1 := fun Γ Γ' _ => TStep C Γ Γ') (motive_2 := fun Γ Γ' _ => TStep C Γ Γ')
    (fun l r => TRun.assign l r) (fun i r => TRun.rebind i r) (fun i r => TRun.assignLocal i r)
    (fun p _ init => TRun.declLocal p init) (fun R _ init => TRun.declStorage R init)
    (fun op _ _ l r => TRun.opAssign op l r) (fun op _ l => TRun.incDec op l)
    (fun i op _ l _ => TRun.assignIncDec i op l) (fun i b => TRun.assignLocalPush i b)
    (fun b v _ => TRun.push b v)
    (fun b => TRun.pop b) (fun r a => TRun.transfer r a) (fun pv r a _ => TRun.send pv r a)
    (fun R _ init _ hm => TRun.declMem R init hm) (fun i r => TRun.rebindMem i r)
    (fun l p => TRun.assignFromMem l p) (fun l r => TRun.assignMem l r)
    (fun l => TRun.delete l) (fun p _ => TRun.deleteMem p) (fun l n h => TRun.assignNew l n h)
    (fun c thn els ihThn ihEls => TRun.ite c thn.ext ihThn els.ext ihEls)
    (fun c => TRun.require c) (fun c => TRun.assert c) (fun _ => .error .revert)
    (fun _ => .error .exhausted)
    (fun _ args ret body ih => TRun.call args ret body.ext ih)
    (fun call rets ok err code pnc other sargs sbody self ihOk ihErr ihPnc ihOther ihSelf =>
      TRun.tryCall call rets ok.ext ihOk err.ext ihErr code pnc.ext ihPnc other.ext ihOther
        sargs sbody.ext ihSelf self)
    (fun _ c body ih => TRun.loopA n c body ih) (fun body ih => TRun.block body.ext ih)
    (fun op _ _ b r => TRun.pushOpAssign op b r) (fun op _ b => TRun.pushIncDec op b)
    (fun _ args r body op ih => TRun.callReceiver args r body.ext ih op)
    (fun _ args r body code value ihBody ihCode =>
      TRun.callReceiverPush args r body.ext ihBody code.ext ihCode value)
    (fun _ _ args ret body ih => TRun.call args ret (body ()).ext (ih ()))
    (fun d => TRun.revertData d)
    (fun c rets sargs sbody self kind _ body ihS ihB =>
      TRun.catchData c rets sargs sbody.ext ihS self kind body.ext ihB)
    TRun.nil (fun _ _ ihS ihP => TRun.seq ihS ihP) s

/-- The typed run of a sequence with fuel, by its recursor. -/
@[implemented_by Prog.runAC]
def Prog.runA (n : Nat) {Γ Γ' : Ctx} (P : Prog C Γ Γ') : TStep C Γ Γ' :=
  Prog.rec (motive_1 := fun Γ Γ' _ => TStep C Γ Γ') (motive_2 := fun Γ Γ' _ => TStep C Γ Γ')
    (fun l r => TRun.assign l r) (fun i r => TRun.rebind i r) (fun i r => TRun.assignLocal i r)
    (fun p _ init => TRun.declLocal p init) (fun R _ init => TRun.declStorage R init)
    (fun op _ _ l r => TRun.opAssign op l r) (fun op _ l => TRun.incDec op l)
    (fun i op _ l _ => TRun.assignIncDec i op l) (fun i b => TRun.assignLocalPush i b)
    (fun b v _ => TRun.push b v)
    (fun b => TRun.pop b) (fun r a => TRun.transfer r a) (fun pv r a _ => TRun.send pv r a)
    (fun R _ init _ hm => TRun.declMem R init hm) (fun i r => TRun.rebindMem i r)
    (fun l p => TRun.assignFromMem l p) (fun l r => TRun.assignMem l r)
    (fun l => TRun.delete l) (fun p _ => TRun.deleteMem p) (fun l n h => TRun.assignNew l n h)
    (fun c thn els ihThn ihEls => TRun.ite c thn.ext ihThn els.ext ihEls)
    (fun c => TRun.require c) (fun c => TRun.assert c) (fun _ => .error .revert)
    (fun _ => .error .exhausted)
    (fun _ args ret body ih => TRun.call args ret body.ext ih)
    (fun call rets ok err code pnc other sargs sbody self ihOk ihErr ihPnc ihOther ihSelf =>
      TRun.tryCall call rets ok.ext ihOk err.ext ihErr code pnc.ext ihPnc other.ext ihOther
        sargs sbody.ext ihSelf self)
    (fun _ c body ih => TRun.loopA n c body ih) (fun body ih => TRun.block body.ext ih)
    (fun op _ _ b r => TRun.pushOpAssign op b r) (fun op _ b => TRun.pushIncDec op b)
    (fun _ args r body op ih => TRun.callReceiver args r body.ext ih op)
    (fun _ args r body code value ihBody ihCode =>
      TRun.callReceiverPush args r body.ext ihBody code.ext ihCode value)
    (fun _ _ args ret body ih => TRun.call args ret (body ()).ext (ih ()))
    (fun d => TRun.revertData d)
    (fun c rets sargs sbody self kind _ body ihS ihB =>
      TRun.catchData c rets sargs sbody.ext ihS self kind body.ext ihB)
    TRun.nil (fun _ _ ihS ihP => TRun.seq ihS ihP) P

mutual

theorem Stmt.runA_eq (n : Nat) : {Γ Γ' : Ctx} → (s : Stmt C Γ Γ') →
    Stmt.runA n s = Stmt.runAC n s
  | _, _, .ite c thn els => by
    show TRun.ite c thn.ext (thn.runA n) els.ext (els.runA n) =
      TRun.ite c thn.ext (thn.runAC n) els.ext (els.runAC n)
    rw [Prog.runA_eq n thn, Prog.runA_eq n els]
  | _, _, .call f args ret body => by
    show TRun.call args ret body.ext (body.runA n) = TRun.call args ret body.ext (body.runAC n)
    rw [Prog.runA_eq n body]
  | _, _, .callRec f _ args ret body => by
    show TRun.call args ret (body ()).ext ((body ()).runA n) =
      TRun.call args ret (body ()).ext ((body ()).runAC n)
    rw [Prog.runA_eq n (body ())]
  | _, _, .callReceiver _ args r body op => by
    change TRun.callReceiver args r body.ext (body.runA n) op =
      TRun.callReceiver args r body.ext (body.runAC n) op
    rw [Prog.runA_eq n body]
  | _, _, .callReceiverPush _ args r body code value => by
    change TRun.callReceiverPush args r body.ext (body.runA n) code.ext (code.runA n) value =
      TRun.callReceiverPush args r body.ext (body.runAC n) code.ext (code.runAC n) value
    rw [Prog.runA_eq n body, Prog.runA_eq n code]
  | _, _, .tryCall call rets ok err code pnc other sargs sbody self => by
    show TRun.tryCall call rets ok.ext (ok.runA n) err.ext (err.runA n) code pnc.ext
        (pnc.runA n) other.ext (other.runA n) sargs sbody.ext (sbody.runA n) self =
      TRun.tryCall call rets ok.ext (ok.runAC n) err.ext (err.runAC n) code pnc.ext
        (pnc.runAC n) other.ext (other.runAC n) sargs sbody.ext (sbody.runAC n) self
    rw [Prog.runA_eq n ok, Prog.runA_eq n err, Prog.runA_eq n pnc, Prog.runA_eq n other,
      Prog.runA_eq n sbody]
  | _, _, .loop a c body => by
    show TRun.loopA n c body (body.runA n) = TRun.loopA n c body (body.runAC n)
    rw [Prog.runA_eq n body]
  | _, _, .block body => by
    show TRun.block body.ext (body.runA n) = TRun.block body.ext (body.runAC n)
    rw [Prog.runA_eq n body]
  | _, _, .catchData c rets sargs sbody self kind _ body => by
    show TRun.catchData c rets sargs sbody.ext (sbody.runA n) self kind body.ext (body.runA n) =
      TRun.catchData c rets sargs sbody.ext (sbody.runAC n) self kind body.ext (body.runAC n)
    rw [Prog.runA_eq n sbody, Prog.runA_eq n body]
  | _, _, .assign .. | _, _, .rebind .. | _, _, .assignLocal .. | _, _, .declLocal ..
  | _, _, .declStorage .. | _, _, .opAssign .. | _, _, .incDec .. | _, _, .assignIncDec ..
  | _, _, .pushOpAssign .. | _, _, .pushIncDec ..
  | _, _, .assignLocalPush .. | _, _, .push .. | _, _, .pop .. | _, _, .transfer ..
  | _, _, .send .. | _, _, .declMem ..
  | _, _, .rebindMem .. | _, _, .assignFromMem .. | _, _, .assignMem .. | _, _, .delete ..
  | _, _, .deleteMem .. | _, _, .assignNew .. | _, _, .require .. | _, _, .assert ..
  | _, _, .revert | _, _, .assumeFalse | _, _, .revertData _ => rfl

theorem Prog.runA_eq (n : Nat) : {Γ Γ' : Ctx} → (P : Prog C Γ Γ') →
    Prog.runA n P = Prog.runAC n P
  | _, _, .nil => rfl
  | _, _, .cons s P => by
    show TRun.seq (s.runA n) (P.runA n) = TRun.seq (s.runAC n) (P.runAC n)
    rw [Stmt.runA_eq n s, Prog.runA_eq n P]

end

mutual

/-- **The accelerated run agrees with the typed run.** -/
theorem Stmt.runA_approx (n : Nat) : {Γ Γ' : Ctx} → (s : Stmt C Γ Γ') →
    TStep.Approx (Stmt.runA n s) (Stmt.runR s)
  | _, _, .ite c thn els =>
    TRun.ite_approx c thn.ext els.ext (Prog.runA_approx n thn) (Prog.runA_approx n els)
  | _, _, .call _ args ret body => TRun.call_approx args ret body.ext (Prog.runA_approx n body)
  | _, _, .callRec _ _ args ret body =>
    TRun.call_approx args ret (body ()).ext (Prog.runA_approx n (body ()))
  | _, _, .callReceiver _ args r body op => by
    intro σ
    exact (TRun.call_approx args (.storage _ r) body.ext (Prog.runA_approx n body) σ).bind
      fun _ => .refl _
  | _, _, .callReceiverPush _ args r body code value => by
    intro σ
    change TRes.Approx (TRun.callReceiverPush args r body.ext (body.runA n)
      code.ext (code.runA n) value σ) (TRun.callReceiverPush args r body.ext body.runR
      code.ext code.runR value σ)
    unfold TRun.callReceiverPush
    apply (TRun.call_approx args (.storage _ r) body.ext (Prog.runA_approx n body) σ).bind
    intro a
    apply TRes.Approx.map
    unfold TRun.afterReceiverPrefix TRun.pushAfterPrefix
    exact (TRes.Approx.refl _).bind fun _ => (Prog.runA_approx n code _).bind fun _ => .refl _
  | _, _, .tryCall call rets ok err code pnc other sargs sbody self =>
    TRun.tryCall_approx call rets ok.ext err.ext code pnc.ext other.ext sargs sbody.ext self
      (Prog.runA_approx n ok) (Prog.runA_approx n err) (Prog.runA_approx n pnc)
      (Prog.runA_approx n other) (Prog.runA_approx n sbody)
  | _, _, .loop _ c body => TRun.loopA_approx n c body (Prog.runA_approx n body)
  | _, _, .block body => TRun.block_approx body.ext (Prog.runA_approx n body)
  | _, _, .catchData c rets sargs sbody self kind _ body =>
    TRun.catchData_approx c rets sargs sbody.ext self kind body.ext (Prog.runA_approx n sbody)
      (Prog.runA_approx n body)
  | _, _, .assign .. | _, _, .rebind .. | _, _, .assignLocal .. | _, _, .declLocal ..
  | _, _, .declStorage .. | _, _, .opAssign .. | _, _, .incDec .. | _, _, .assignIncDec ..
  | _, _, .pushOpAssign .. | _, _, .pushIncDec ..
  | _, _, .assignLocalPush .. | _, _, .push .. | _, _, .pop .. | _, _, .transfer ..
  | _, _, .send .. | _, _, .declMem ..
  | _, _, .rebindMem .. | _, _, .assignFromMem .. | _, _, .assignMem .. | _, _, .delete ..
  | _, _, .deleteMem .. | _, _, .assignNew .. | _, _, .require .. | _, _, .assert ..
  | _, _, .revert | _, _, .assumeFalse | _, _, .revertData _ => fun _ => .refl _

theorem Prog.runA_approx (n : Nat) : {Γ Γ' : Ctx} → (P : Prog C Γ Γ') →
    TStep.Approx (Prog.runA n P) (Prog.runR P)
  | _, _, .nil => fun _ => .refl _
  | _, _, .cons s P => TRun.seq_approx (Stmt.runA_approx n s) (Prog.runA_approx n P)

end

/-- The frames after a program, run with fuel (`Frames.run`). -/
def Frames.runA (n : Nat) {Γ₀ : Ctx} : {Γ : Ctx} → (σ : State C Γ) → Frames C Γ Γ₀ →
    TRes (Out C σ.H Γ₀)
  | _, σ, .nil => .ok ⟨σ, List.prefix_refl _⟩
  | _, σ, .seq ω κ => TRun.seq (fun τ => Prog.runA n ω τ) (fun τ => Frames.runA n τ κ) σ
  | _, σ, .pop _ h κ => Frames.runA n (σ.drop h) κ
  | _, σ, .drop h κ => Frames.runA n (σ.thin h) κ

theorem Frames.runA_approx (n : Nat) {Γ₀ : Ctx} : {Γ : Ctx} → (σ : State C Γ) →
    (κ : Frames C Γ Γ₀) → TRes.Approx (Frames.runA n σ κ) (Frames.run σ κ)
  | _, _, .nil => .refl _
  | _, σ, .seq ω κ =>
    TRun.seq_approx (Prog.runA_approx n ω) (fun τ => Frames.runA_approx n τ κ) σ
  | _, σ, .pop _ h κ => Frames.runA_approx n (σ.drop h) κ
  | _, σ, .drop h κ => Frames.runA_approx n (σ.thin h) κ

end Solidity
