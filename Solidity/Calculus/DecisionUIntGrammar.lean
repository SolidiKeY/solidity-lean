import Solidity.Calculus.Decision

/-!
# A constructive source grammar for literal-linear uint terms

An intrinsic predicate on the existing scoped terms, independent of any
coverage or decision test. This is a term-level bridge increment, not the
final Residue or formula-completeness theorem.
-/
namespace Solidity

/-- UInt locals/literals, addition/subtraction, and a literal multiplication operand. -/
inductive Tm.UIntLinear {C : Contract} {Γ : Ctx} : Tm C Γ (.val .uint) → Prop where
  | local (i : Idx Γ (.val .uint)) : Tm.UIntLinear (.pvV i)
  | lit (v : PrimTy.uint.Denote) : Tm.UIntLinear (.app0 (.lit v))
  | add {a b : Tm C Γ (.val .uint)} : Tm.UIntLinear a → Tm.UIntLinear b →
      Tm.UIntLinear (.app2 (.binop .add rfl) a b)
  | sub {a b : Tm C Γ (.val .uint)} : Tm.UIntLinear a → Tm.UIntLinear b →
      Tm.UIntLinear (.app2 (.binop .sub rfl) a b)
  | mulL (v : PrimTy.uint.Denote) {b : Tm C Γ (.val .uint)} : Tm.UIntLinear b →
      Tm.UIntLinear (.app2 (.binop .mul rfl) (.app0 (.lit v)) b)
  | mulR {a : Tm C Γ (.val .uint)} (v : PrimTy.uint.Denote) : Tm.UIntLinear a →
      Tm.UIntLinear (.app2 (.binop .mul rfl) a (.app0 (.lit v)))

namespace Decide

/-- UInt local bindings are present and independently in the existing numeric source grammar. -/
def UIntSourceLocs {C : Contract} {Γ : Ctx} (ρ : SymS C Γ) : Prop :=
  ∀ i : Idx Γ (.val .uint), ∃ l : LTm C (.val .uint),
    ρ.loc.get i = some l ∧ l.Src false true .num

theorem UIntSourceLocs.init {C : Contract} : UIntSourceLocs (SymS.init (C := C)) := by
  intro i
  cases i

theorem UIntSourceLocs.pushQ {C : Contract} {Γ : Ctx} {ρ : SymS C Γ}
    (hρ : UIntSourceLocs ρ) : UIntSourceLocs (ρ.pushQ .uint) := by
  intro i
  cases i with
  | here => exact ⟨.var ρ.next, rfl, .var _⟩
  | there i => exact hρ i

/-- Every term of this intrinsic grammar is source-admitted for every waiver setting. -/
theorem uintLinear_admitted {C : Contract} {Γ : Ctx} {t : Tm C Γ (.val .uint)}
    (h : t.UIntLinear) (w : Waivers) : t.inTarget w false = true := by
  induction h with
  | «local» i => rfl
  | lit v => rfl
  | @add a b ha hb iha ihb | @sub a b ha hb iha ihb =>
    change Bool.and (Bool.and (a.inTarget w false) (b.inTarget w false)) true = true
    rw [iha, ihb]
    rfl
  | @mulL v b hb ihb =>
    change Bool.and (Bool.and true (b.inTarget w false)) true = true
    rw [ihb]
    rfl
  | @mulR a v ha iha =>
    change Bool.and (Bool.and (a.inTarget w false) true) (Bool.or a.isLitV true) = true
    rw [iha, Bool.or_true]
    rfl

/-- Literal folding preserves an already established numeric source derivation. -/
theorem fold2_preserves_num {C : Contract} {p : PrimTy} {c w : Bool}
    (op : BinOp) (h : op.accepts p = true) {x y : LTm C (.val p)}
    (hxy : (LTm.app2 (.binop op h) x y).Src c w .num) :
    (fold2 (.binop op h) x y).Src c w .num := by
  unfold fold2
  simp only
  split
  · split
    · exact .lit _
    · split
      · split
        · exact hxy
        · split
          · exact .lit _
          · exact .err
      · exact hxy
  · exact hxy

/-- Actual source translation reaches the existing numeric grammar, with no coverage assumption. -/
theorem uintLinear_toL {C : Contract} {Γ : Ctx} {t : Tm C Γ (.val .uint)}
    (h : t.UIntLinear) (ρ : SymS C Γ) (hρ : UIntSourceLocs ρ) :
    ∃ l : LTm C (.val .uint), t.toL ρ = some l ∧ l.Src false true .num := by
  induction h with
  | «local» i => exact hρ i
  | lit v => exact ⟨.app0 (.lit v), rfl, .lit v⟩
  | @add a b ha hb iha ihb =>
    obtain ⟨u, hu, hsu⟩ := iha
    obtain ⟨v, hv, hsv⟩ := ihb
    refine ⟨fold2 (.binop .add rfl) u v, ?_, fold2_preserves_num .add rfl (.add rfl hsu hsv)⟩
    change (a.toL ρ).bind (fun u => (b.toL ρ).bind (fun v => some (fold2 (.binop .add rfl) u v))) = _
    rw [hu, hv]
    rfl
  | @sub a b ha hb iha ihb =>
    obtain ⟨u, hu, hsu⟩ := iha
    obtain ⟨v, hv, hsv⟩ := ihb
    refine ⟨fold2 (.binop .sub rfl) u v, ?_, fold2_preserves_num .sub rfl (.sub rfl hsu hsv)⟩
    change (a.toL ρ).bind (fun u => (b.toL ρ).bind (fun v => some (fold2 (.binop .sub rfl) u v))) = _
    rw [hu, hv]
    rfl
  | @mulL v b hb ihb =>
    obtain ⟨u, hu, hsu⟩ := ihb
    refine ⟨fold2 (.binop .mul rfl) (.app0 (.lit v)) u, ?_,
      fold2_preserves_num .mul rfl (.mulL rfl v hsu)⟩
    change (b.toL ρ).bind (fun u => some (fold2 (.binop .mul rfl) (.app0 (.lit v)) u)) = _
    rw [hu]
    rfl
  | @mulR a v ha iha =>
    obtain ⟨u, hu, hsu⟩ := iha
    refine ⟨fold2 (.binop .mul rfl) u (.app0 (.lit v)), ?_,
      fold2_preserves_num .mul rfl (.mulR rfl v hsu)⟩
    change (a.toL ρ).bind (fun u => some (fold2 (.binop .mul rfl) u (.app0 (.lit v)))) = _
    rw [hu]
    rfl

/-- The Theory and interpreter agree on every source term in this grammar. -/
theorem uintLinear_agrees {C : Contract} {Γ : Ctx} {t : Tm C Γ (.val .uint)}
    (h : t.UIntLinear) : t.agreeB = true := by
  induction h <;> simp_all only [Tm.agreeB, Op0.agreesB, Op2.agreesB,
    Bool.true_and, Bool.true_or]

/-- The grammar contains no hash terms. -/
theorem uintLinear_hashFree {C : Contract} {Γ : Ctx} {t : Tm C Γ (.val .uint)}
    (h : t.UIntLinear) : t.hasHash = false := by
  induction h <;> simp_all only [Tm.hasHash, Op2.isHash, Bool.false_or]

/-- The exact Theory translator agrees with the ordinary source translator here. -/
theorem toLT_eq_toL_of_agree {C : Contract} {Γ : Ctx} {s : Srt}
    (t : Tm C Γ s) (ρ : SymS C Γ) (ha : t.agreeB = true) : t.toLT ρ = t.toL ρ := by
  cases t <;> simp only [Tm.toLT, ha, if_true]

/-- The actual exact Theory translation also yields a numeric-source term. -/
theorem uintLinear_toLT {C : Contract} {Γ : Ctx} {t : Tm C Γ (.val .uint)}
    (h : t.UIntLinear) (ρ : SymS C Γ) (hρ : UIntSourceLocs ρ) :
    ∃ l : LTm C (.val .uint), t.toLT ρ = some l ∧ l.Src false true .num := by
  rw [toLT_eq_toL_of_agree t ρ (uintLinear_agrees h)]
  exact uintLinear_toL h ρ hρ

/-- Source admission of these non-hash operators is independent of the hash-position flag. -/
theorem uintLinear_admitted_at {C : Contract} {Γ : Ctx} {t : Tm C Γ (.val .uint)}
    (h : t.UIntLinear) (w : Waivers) (hashOK : Bool) : t.inTarget w hashOK = true := by
  have he : t.inTarget w hashOK = t.inTarget w false := by
    cases h <;> rfl
  rw [he]
  exact uintLinear_admitted h w

/-- No mapping key occurs in the source grammar. -/
theorem uintLinear_mapKeys {C : Contract} {Γ : Ctx} {t : Tm C Γ (.val .uint)}
    (h : t.UIntLinear) : t.mapKeys = [] := by
  induction h <;> simp_all only [Tm.mapKeys, Op2.isMapAt, Bool.false_eq_true,
    if_false, List.nil_append]

end Decide
end Solidity
