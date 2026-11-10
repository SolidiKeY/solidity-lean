import Solidity.Syntax.NumericV2
import Solidity.Semantics.NumericLowering
import Solidity.Source.Observe

namespace Solidity.Val.NumericV2

def validThreshold (t : Threshold) : Bool :=
  decide (0 < t.1.val ∧
    t.2.1.val ^ t.1.val ≤ 2^255-1 ∧ 2^255-1 < (t.2.1.val+1)^t.1.val ∧
    t.2.2.val ^ t.1.val ≤ 2^255 ∧ 2^255 < (t.2.2.val+1)^t.1.val)

theorem thresholds_valid : thresholds.all validThreshold = true := by
  decide +kernel

/-- Integer root intervals characterize the complete magnitude range. -/
theorem root_iff (m r n limit : Nat)
    (lower : r^n ≤ limit) (upper : limit < (r+1)^n) :
    m^n ≤ limit ↔ m ≤ r := by
  constructor
  · intro h
    by_cases good : m ≤ r
    · exact good
    · have order : r+1 ≤ m := by omega
      have power := Nat.pow_le_pow_left order n
      omega
  · intro h
    exact Nat.le_trans (Nat.pow_le_pow_left h n) lower

def lookupResult (negative : Bool) (m b : Int) : List Threshold → Bool
  | [] => false
  | (n,p,q)::rest => if b = (n.val : Int) then
      decide (m ≤ ((if negative then q.val else p.val : Nat) : Int))
    else lookupResult negative m b rest

theorem lookup_eval {C : Contract} {Γ : Ctx} (σ : State C Γ)
    (nv : Val C Γ .bool) (mv bv : Val C Γ .uint)
    (negative : Bool) (m b : PrimTy.uint.Denote)
    (hn : nv.evalT σ = .ok negative) (hm : mv.evalT σ = .ok m)
    (hb : bv.evalT σ = .ok b) (ts : List Threshold) :
    (lookup nv mv bv ts).evalT σ = .ok (lookupResult negative m.val b.val ts) := by
  induction ts with
  | nil => rfl
  | cons t rest ih =>
    rcases t with ⟨n,p,q⟩
    simp only [lookup, lookupResult, Val.evalT, hn, hm, hb, word,
      Simple.evalT, PrimTy.ofLit, BinOp.shortT, BinOp.evalT, BinOp.evalNum,
      BinOp.ret, BinOp.isArith, TRes.ofOpt, boolT,
      Bind.bind, Except.bind]
    cases negative <;> by_cases same : b.val = (n.val : Int) <;>
      simp only [same, decide_true, decide_false, Bool.false_eq_true, if_false, if_true, ih]

theorem thresholds_indices : thresholds.map (fun t => t.1.val) = List.range' 1 255 := by
  decide +kernel

theorem threshold_present (n : Nat) (positive : 0 < n) (small : n < 256) :
    ∃ t, t ∈ thresholds ∧ t.1.val = n := by
  apply List.mem_map.mp
  rw [thresholds_indices]
  apply List.mem_range'.mpr
  exact ⟨n-1, by omega, by omega⟩

def limit (negative : Bool) : Nat := if negative then 2^255 else 2^255-1

theorem lookupResult_correct (negative : Bool) (m n : Nat) (ts : List Threshold)
    (valid : ∀ t, t ∈ ts → validThreshold t = true)
    (present : ∃ t, t ∈ ts ∧ t.1.val = n) :
    lookupResult negative (m : Int) (n : Int) ts = decide (m^n ≤ limit negative) := by
  induction ts with
  | nil => obtain ⟨t,member,_⟩ := present; cases member
  | cons t rest ih =>
    rcases t with ⟨e,p,q⟩
    by_cases same : n = e.val
    · have cert := valid (e,p,q) (by simp)
      have facts : 0 < e.val ∧ p.val^e.val ≤ 2^255-1 ∧
          2^255-1 < (p.val+1)^e.val ∧ q.val^e.val ≤ 2^255 ∧
          2^255 < (q.val+1)^e.val := by
        simpa only [validThreshold, decide_eq_true_eq] using cert
      subst n
      cases negative <;> simp only [lookupResult, limit, if_true]
      · apply decide_eq_decide.mpr
        exact Int.ofNat_le.trans (root_iff m p.val e.val (2^255-1) facts.2.1 facts.2.2.1).symm
      · apply decide_eq_decide.mpr
        exact Int.ofNat_le.trans (root_iff m q.val e.val (2^255) facts.2.2.2.1 facts.2.2.2.2).symm
    · have unequal : (n : Int) ≠ (e.val : Int) := by omega
      simp only [lookupResult, unequal, if_false]
      apply ih
      · intro x hx; exact valid x (by simp [hx])
      · obtain ⟨x,hx,he⟩ := present
        simp only [List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact False.elim (same he.symm)
        · exact ⟨x,hx,he⟩

theorem lookupResult_large (negative : Bool) (m : Int) (n : Nat)
    (large : 256 ≤ n) (ts : List Threshold) :
    lookupResult negative m (n : Int) ts = false := by
  induction ts with
  | nil => rfl
  | cons t rest ih =>
    have small := t.1.isLt
    simp only [lookupResult, show (n : Int) ≠ (t.1.val : Int) by omega, if_false, ih]

def fitsResult (negative : Bool) (m n : Nat) : Bool :=
  if m ≤ 1 then true else if n = 0 then true else
    if n < 256 then decide (m^n ≤ limit negative) else false

theorem fitsResult_correct (negative : Bool) (m n : Nat) :
    fitsResult negative m n = decide (m^n ≤ limit negative) := by
  have low : 1 ≤ limit negative := by cases negative <;> decide
  have high : limit negative < 2^256 := by cases negative <;> decide
  unfold fitsResult
  by_cases unit : m ≤ 1
  · simp only [unit, if_true]
    have small : m^n ≤ 1 := by
      exact Nat.le_trans (Nat.pow_le_pow_left unit n) (by simp)
    exact (decide_eq_true (by omega : m^n ≤ limit negative)).symm
  · simp only [unit, if_false]
    by_cases zero : n = 0
    · subst n
      simp only [if_true, Nat.pow_zero, low, decide_true]
    · simp only [zero, if_false]
      by_cases small : n < 256
      · simp only [small, if_true]
      · simp only [small, if_false]
        have power : 2^256 ≤ m^n := Nat.le_trans
          (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 256 ≤ n))
          (Nat.pow_le_pow_left (by omega : 2 ≤ m) n)
        exact (decide_eq_false (by omega : ¬ m^n ≤ limit negative)).symm

theorem powerFits_eval_model {C : Contract} {Γ : Ctx} (σ : State C Γ)
    (av : Val C Γ .int) (bv : Val C Γ .uint)
    (a : PrimTy.int.Denote) (b : PrimTy.uint.Denote)
    (ha : av.evalT σ = .ok a) (hb : bv.evalT σ = .ok b) :
    (powerFits av bv).evalT σ = .ok
      (fitsResult (decide (a.val < 0 ∧ b.val.toNat % 2 = 1)) a.val.natAbs b.val.toNat) := by
  have hm := NumericLowering.signedMagnitude_eval σ av a ha
  have hn := NumericLowering.powerNegative_eval σ av bv a b ha hb
  have hl := lookup_eval σ (Val.powerNegative av bv) (Val.signedMagnitude av) bv _ _ b hn hm hb thresholds
  have br : 0 ≤ b.val := (of_decide_eq_true b.property).1
  have cast : (b.val.toNat : Int) = b.val := Int.toNat_of_nonneg br
  have bz : b.val = 0 ↔ b.val.toNat = 0 := by omega
  simp only [powerFits, Val.evalT, hm, hb, word, Simple.evalT, PrimTy.ofLit,
    BinOp.shortT, BinOp.evalT, BinOp.evalNum, BinOp.ret, BinOp.isArith,
    TRes.ofOpt, boolT, Bind.bind, Except.bind, Int.ofNat_le]
  change (if decide (a.val.natAbs ≤ 1) then .ok true else
    if decide (b.val = 0) then .ok true else
    (lookup (Val.powerNegative av bv) (Val.signedMagnitude av) bv thresholds).evalT σ) = _
  simp only [bz]
  by_cases unit : a.val.natAbs ≤ 1
  · simp only [unit, decide_true, if_true, fitsResult]
  · simp only [unit, decide_false, Bool.false_eq_true, if_false]
    by_cases zero : b.val.toNat = 0
    · simp only [zero, decide_true, if_true, fitsResult, unit, if_false]
    · simp only [zero, decide_false, Bool.false_eq_true, if_false]
      rw [hl]
      unfold fitsResult
      simp only [unit, zero, if_false]
      by_cases small : b.val.toNat < 256
      · rw [if_pos small, ← cast]
        rw [lookupResult_correct _ _ _ thresholds
          (List.all_eq_true.mp thresholds_valid) (threshold_present _ (by omega) small)]
        simp only [Int.toNat_natCast]
      · rw [if_neg small, ← cast, lookupResult_large _ _ _ (by omega)]

theorem signed_range_iff (a : Int) (n : Nat) :
    a.natAbs^n ≤ limit (decide (a < 0 ∧ n % 2 = 1)) ↔
      -Semantics.intBound ≤ a^n ∧ a^n < Semantics.intBound := by
  rw [NumericLowering.power_sign]
  have pos : (0 : Int) < Semantics.intBound := by decide
  have subBound : ((2^255-1 : Nat) : Int) = Semantics.intBound-1 := by
    rw [Int.natCast_sub (by decide : 1 ≤ 2^255), Int.natCast_one]
    rfl
  have nonneg : 0 ≤ (a.natAbs : Int)^n := Int.pow_nonneg (Int.natCast_nonneg _)
  by_cases negative : a < 0 ∧ n % 2 = 1
  · simp only [negative, and_self, decide_true, limit, if_true]
    rw [← Int.ofNat_le]
    rw [Int.natCast_pow a.natAbs n]
    change (a.natAbs : Int)^n ≤ Semantics.intBound ↔ _
    omega
  · simp only [negative, decide_false, Bool.false_eq_true, limit, if_false]
    rw [← Int.ofNat_le]
    rw [Int.natCast_pow a.natAbs n, subBound]
    omega

/-- The actual guard is total for every successfully evaluated word operand. -/
theorem powerFits_eval {C : Contract} {Γ : Ctx} (σ : State C Γ)
    (av : Val C Γ .int) (bv : Val C Γ .uint)
    (a : PrimTy.int.Denote) (b : PrimTy.uint.Denote)
    (ha : av.evalT σ = .ok a) (hb : bv.evalT σ = .ok b) :
    (powerFits av bv).evalT σ = .ok
      (decide (-Semantics.intBound ≤ a.val^b.val.toNat ∧
        a.val^b.val.toNat < Semantics.intBound)) := by
  rw [powerFits_eval_model σ av bv a b ha hb, fitsResult_correct]
  congr 1
  exact decide_eq_decide.mpr (signed_range_iff a.val b.val.toNat)

/-- Range-success preserves the exact value result, not merely its option. -/
theorem powerValue_eval {C : Contract} {Γ : Ctx} (σ : State C Γ)
    (av : Val C Γ .int) (bv : Val C Γ .uint)
    (a : PrimTy.int.Denote) (b : PrimTy.uint.Denote)
    (ha : av.evalT σ = .ok a) (hb : bv.evalT σ = .ok b)
    (fits : -Semantics.intBound ≤ a.val^b.val.toNat ∧
      a.val^b.val.toNat < Semantics.intBound) :
    (powerValue av bv).evalT σ = .ok
      (⟨a.val^b.val.toNat, by simpa only [PrimTy.inRange, decide_eq_true_eq] using fits⟩ : PrimTy.int.Denote) := by
  have old := NumericLowering.checkedSignedPower_correct σ av bv a b ha hb
  simp only [fits, and_self, if_true] at old
  change ((powerValue av bv).evalT σ).toOption.map (·.val) = _ at old
  cases result : (powerValue av bv).evalT σ with
  | error failure => simp only [result, Except.toOption, Option.map] at old; cases old
  | ok value =>
    simp only [result, Except.toOption, Option.map, Option.some.injEq] at old
    congr 1
    exact Subtype.ext old

/-- Exact 36-byte overflow receipt from the real intrinsic statement runner. -/
theorem guard_run {C : Contract} {Γ : Ctx} (σ : State C Γ)
    (condition : Val C Γ .bool) (answer : Bool)
    (computed : condition.evalT σ = .ok answer) :
    (panicStmt 0x11 condition).run σ =
      if answer then .ok (⟨σ,List.prefix_refl _⟩ : Out C σ.H Γ)
      else .error (THalt.ofData (Semantics.encodePanic 0x11)) := by
  cases answer with
  | true =>
    change TRun.ite condition _ _ _ _ σ = _
    simp only [TRun.ite,computed,boolT,TRun.nil]
    rfl
  | false =>
    have literal : TRun.revertData [.bytes (Semantics.encodePanic 0x11)] σ =
        .error (THalt.ofData (Semantics.encodePanic 0x11)) := by
      change Except.error (THalt.ofData ((Semantics.encodePanic 0x11) ++ [])) = _
      rw [List.append_nil]
    change TRun.ite condition _ _ _ _ σ = _
    simp only [TRun.ite,computed,boolT,ok_bind,Bool.false_eq_true,if_false,TRun.seq,literal]
    rfl

/-- Execute the emitted statement before its value; errors carry no rollback state. -/
theorem checkedSignedPower_run {C : Contract} {Γ : Ctx} (σ : State C Γ)
    (av : Val C Γ .int) (bv : Val C Γ .uint)
    (a : PrimTy.int.Denote) (b : PrimTy.uint.Denote)
    (ha : av.evalT σ = .ok a) (hb : bv.evalT σ = .ok b) :
    ((checkedSignedPower av bv).1.run σ >>= fun out =>
      (checkedSignedPower av bv).2.evalT out.st >>= fun result =>
        pure (out,result)) =
      if fits : -Semantics.intBound ≤ a.val^b.val.toNat ∧
          a.val^b.val.toNat < Semantics.intBound then
        .ok ((⟨σ,List.prefix_refl _⟩ : Out C σ.H Γ),
          (⟨a.val^b.val.toNat, by simpa only [PrimTy.inRange, decide_eq_true_eq] using fits⟩ : PrimTy.int.Denote))
      else .error (THalt.ofData (Semantics.encodePanic 0x11)) := by
  have guard := guard_run σ (powerFits av bv) _ (powerFits_eval σ av bv a b ha hb)
  change ((panicStmt 0x11 (powerFits av bv)).run σ >>= fun out =>
      (powerValue av bv).evalT out.st >>= fun result => pure (out,result)) = _
  rw [guard]
  by_cases fits : -Semantics.intBound ≤ a.val^b.val.toNat ∧
      a.val^b.val.toNat < Semantics.intBound
  · simp only [fits, and_self, decide_true, if_true, Bind.bind, Except.bind]
    rw [powerValue_eval σ av bv a b ha hb fits]
    rfl
  · simp only [fits, decide_false, Bool.false_eq_true, if_false, dite_false, Bind.bind, Except.bind]

/-- Pin the payload length independently of halt-category equality. -/
theorem overflow_payload_length : (Semantics.encodePanic 0x11).length = 36 := by
  decide +kernel

/-- Exact Source arithmetic payload, including selector and all ABI bytes. -/
theorem overflow_payload_source : Semantics.encodePanic 0x11 =
    Source.panicData .arithmetic := by
  decide +kernel

theorem checkedSignedPower_source_run {C : Contract} {Γ : Ctx} (σ : State C Γ)
    (av : Val C Γ .int) (bv : Val C Γ .uint)
    (a : PrimTy.int.Denote) (b : PrimTy.uint.Denote)
    (ha : av.evalT σ = .ok a) (hb : bv.evalT σ = .ok b) :
    (checkedSignedPower av bv).1.run σ =
      if -Semantics.intBound ≤ a.val^b.val.toNat ∧ a.val^b.val.toNat < Semantics.intBound
      then .ok (⟨σ,List.prefix_refl _⟩ : Out C σ.H Γ)
      else .error (THalt.ofData (Source.panicData .arithmetic)) := by
  have h := guard_run σ (powerFits av bv) _ (powerFits_eval σ av bv a b ha hb)
  simpa only [checkedSignedPower, decide_eq_true_eq, overflow_payload_source] using h

/-- info: 'Solidity.Val.NumericV2.thresholds_valid' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Val.NumericV2.thresholds_valid
/-- info: 'Solidity.Val.NumericV2.root_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Val.NumericV2.root_iff
/-- info: 'Solidity.Val.NumericV2.lookup_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Val.NumericV2.lookup_eval
/-- info: 'Solidity.Val.NumericV2.thresholds_indices' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Val.NumericV2.thresholds_indices
/-- info: 'Solidity.Val.NumericV2.threshold_present' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Val.NumericV2.threshold_present
/-- info: 'Solidity.Val.NumericV2.lookupResult_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Val.NumericV2.lookupResult_correct
/-- info: 'Solidity.Val.NumericV2.lookupResult_large' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Val.NumericV2.lookupResult_large
/-- info: 'Solidity.Val.NumericV2.fitsResult_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Val.NumericV2.fitsResult_correct
/-- info: 'Solidity.Val.NumericV2.powerFits_eval_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Val.NumericV2.powerFits_eval_model
/-- info: 'Solidity.Val.NumericV2.signed_range_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Val.NumericV2.signed_range_iff
/-- info: 'Solidity.Val.NumericV2.powerFits_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Val.NumericV2.powerFits_eval
/-- info: 'Solidity.Val.NumericV2.powerValue_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Val.NumericV2.powerValue_eval
/-- info: 'Solidity.Val.NumericV2.guard_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Val.NumericV2.guard_run
/-- info: 'Solidity.Val.NumericV2.checkedSignedPower_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Val.NumericV2.checkedSignedPower_run
/-- info: 'Solidity.Val.NumericV2.overflow_payload_length' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Val.NumericV2.overflow_payload_length
/-- info: 'Solidity.Val.NumericV2.overflow_payload_source' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Val.NumericV2.overflow_payload_source
/-- info: 'Solidity.Val.NumericV2.checkedSignedPower_source_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Val.NumericV2.checkedSignedPower_source_run

end Solidity.Val.NumericV2
