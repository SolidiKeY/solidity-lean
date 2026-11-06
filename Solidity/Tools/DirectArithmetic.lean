import Solidity.Calculus.InputReduction
import Solidity.Calculus.DependentReduction
import Solidity.Calculus.ArrayReduction

/-! Bounded compiled arithmetic over the existing exact source reduction.
A closed derivative walk proves validity; refutation or exhaustion leaves this
helper undecided. Runtime proof fields are erased by Lean's C compiler. -/
namespace Solidity.Linear.AFml

def boundedWalk (F : AFml) (fuel : Nat) : Walk (AFml × Nat) (Reached F) :=
  walk Reached.st stateHash Reached.kids (fun r => r.formula.atZero) fuel
    (HSet.leaf.insert (stateHash (Reached.initial F).st) (Reached.initial F).st)
    [Reached.initial F]

theorem boundedWalk_closed {F : AFml} {fuel : Nat} {V : HSet (AFml × Nat)}
    (h : F.boundedWalk fuel = .closed V) : F.Valid := by
  obtain ⟨hk, hall⟩ := walk_closed _ _ _ _ _ _ _ V h (walkInv_initial _ _ _ _ _)
  refine valid_of_rounds F.roundLen (Nat.lt_of_lt_of_le Nat.zero_lt_one (Nat.le_max_right _ _))
    V.Mem ?_ ?_ ?_ F (hk _ (HSet.mem_insert.2 (.inl rfl)))
  · intro G j hG
    obtain ⟨n, hn, -, -⟩ := hall _ hG
    simp only [Reached.st, Prod.mk.injEq] at hn
    rw [← hn.1]
    exact Nat.le_trans n.width (Nat.le_max_left _ _)
  · intro G j hG
    obtain ⟨n, hn, hz, -⟩ := hall _ hG
    simp only [Reached.st, Prod.mk.injEq] at hn
    rw [← hn.1]; exact hz
  · intro G j hG _ b
    obtain ⟨n, hn, -, hs⟩ := hall _ hG
    simp only [Reached.st, Prod.mk.injEq] at hn
    obtain ⟨rfl, rfl⟩ := hn
    have := hs (n.child b) (by cases b <;> simp only [Reached.kids, List.mem_cons, true_or, or_true])
    exact this

def boundedValid (F : AFml) (fuel : Nat) : Option (PLift F.Valid) :=
  match h : F.norm.boundedWalk fuel with
  | .closed _ => some ⟨fun x => (holds_norm x F).1 (boundedWalk_closed h x)⟩
  | _ => none

end Solidity.Linear.AFml



namespace Solidity.Linear.AFml

/-- A consequence of one true arithmetic hypothesis. -/
structure Upper (f : AFml) where
  coefficients : Lin
  bound : Int
  correct : ∀ x, f.holds x → coefficients.eval x ≤ bound

private def upper : (f : AFml) → Option (Upper f)
  | .le a c => some ⟨a, c, fun _ h => h⟩
  | .eq a c => some ⟨a, c, fun _ h => Int.le_of_eq h⟩
  | .not (.le a c) => some ⟨a.map (- ·), -c - 1, fun x h => by
      rw [Lin.eval_neg]
      change ¬ a.eval x ≤ c at h
      omega⟩
  | _ => none

private def uppers : (f : AFml) → List (Upper f)
  | .eq a c => [⟨a, c, fun _ h => Int.le_of_eq h⟩,
      ⟨a.map (- ·), -c, fun x h =>
        (Lin.eval_neg a x).symm ▸ Int.le_of_eq (congrArg (fun n : Int => -n) h)⟩]
  | f => (upper f).toList

/-- An inequality sufficient for the requested conclusion. -/
structure Target (f : AFml) where
  coefficients : Lin
  bound : Int
  correct : ∀ x, coefficients.eval x ≤ bound → f.holds x

private def target : (f : AFml) → Option (Target f)
  | .le a c => some ⟨a, c, fun _ h => h⟩
  | .not (.le a c) => some ⟨a.map (- ·), -c - 1, fun x h => by
      rw [Lin.eval_neg] at h
      change ¬ a.eval x ≤ c
      omega⟩
  | _ => none

/-- Same affine form, with a stronger bound; or the sum of two assumptions.
This is bounded constraint propagation, before any derivative exploration. -/
private def fromBounds? (hs : List AFml) (f : AFml) :
    Option (PLift (∀ x, (∀ a ∈ hs, a.holds x) → f.holds x)) := do
  let t ← target f
  for ha : a in hs do
    for u in uppers a do
      if h : u.coefficients.trim = t.coefficients.trim then
        if hb : u.bound ≤ t.bound then
          return ⟨fun x hx => t.correct x (by
            have hu := u.correct x (hx a ha)
            have he : u.coefficients.eval x = t.coefficients.eval x := by
              rw [← Lin.eval_trim, h, Lin.eval_trim]
            omega)⟩
      for hbmem : b in hs do
        for v in uppers b do
          if h : (u.coefficients.add v.coefficients).trim = t.coefficients.trim then
            if hb : u.bound + v.bound ≤ t.bound then
              return ⟨fun x hx => t.correct x (by
                have hu := u.correct x (hx a ha)
                have hv := v.correct x (hx b hbmem)
                have he : u.coefficients.eval x + v.coefficients.eval x = t.coefficients.eval x := by
                  rw [← Lin.eval_add, ← Lin.eval_trim, h, Lin.eval_trim]
                omega)⟩
  none

private def linearProof? : (fuel : Nat) → (hs : List AFml) → (f : AFml) →
    Option (PLift (∀ x, (∀ a ∈ hs, a.holds x) → f.holds x))
  | 0, _, _ => none
  | n + 1, hs, f =>
    if hf : f ∈ hs then some ⟨fun _ h => h f hf⟩ else
    match f with
    | .tt => some ⟨fun _ _ => True.intro⟩
    | .and a b => do
      let ha ← linearProof? n hs a
      let hb ← linearProof? n hs b
      pure ⟨fun x h => ⟨ha.down x h, hb.down x h⟩⟩
    | .imp a b => do
      let hb ← linearProof? n (a.hypotheses ++ hs) b
      pure ⟨fun x h ha => hb.down x (fun c hc =>
        (List.mem_append.mp hc).elim
          (fun hc => a.hypotheses_hold x ha c hc) (fun hc => h c hc))⟩
    | .eq a c => do
      let hi ← fromBounds? hs (.le a c)
      let lo ← fromBounds? hs (.le (a.map (- ·)) (-c))
      pure ⟨fun x h => Int.le_antisymm (hi.down x h)
        (Int.le_of_neg_le_neg (Eq.mp (congrArg (fun value => value ≤ -c) (Lin.eval_neg a x)) (lo.down x h)))⟩
    | g => fromBounds? hs g

def propagateValid (f : AFml) : Option (PLift f.Valid) := do
  let h ← linearProof? 128 [] f.norm
  pure ⟨fun x => (holds_norm x f).1 (h.down x (fun _ h => nomatch h))⟩

end Solidity.Linear.AFml

namespace Solidity.Tools

private def arithmeticProof {ps : List PrimTy} (f : Linear.TypedFormula ps) : Option (PLift f.Valid) := do
  let h ← f.guarded.propagateValid.orElse (fun _ => f.guarded.boundedValid 8192)
  return ⟨f.valid_iff.mpr h.down⟩

/-- Positive verification needs sound lowering, rather than an exact reverse
mapping for countermodels. This also admits universal loop locals introduced
below source antecedents. All transport proofs are erased by compilation. -/
private def loweredArithmeticProof {C : Contract} (φ : Fml C []) : Option (PLift (Fml.Valid φ)) :=
  match hl : φ.toLS true Decide.SymS.init with
  | none => none
  | some leaf => do
    let sentence ← Decide.UniversalPrefix.ofFormula? 1024 leaf.elim.condSimp.prenex
    let es := Decide.Inputs.unique (Decide.Inputs.formulaKeys sentence.body)
    let encoded ← Decide.StorageEncoding.ofFormula? (ps := sentence.parameters) (es := es) sentence.body
    let rs := ReadRealization.Layout.unique encoded.refs
    if hc : ∀ q ∈ encoded.refs, q ∈ rs then
      if hw : (encoded.lower rs).width ≤ (Decide.Inputs.types es sentence.parameters rs).length then
        let typed : Linear.TypedFormula (Decide.Inputs.types es sentence.parameters rs) := ⟨encoded.lower rs, hw⟩
        let h ← arithmeticProof typed
        return ⟨Fml.Valid.of_toLS hl (fun g ν =>
          (Decide.LFml.elim_holds g leaf ν).mp
            ((Decide.LFml.condSimp_holds g _ ν).mp
              ((Decide.LFml.prenex_holds g _ ν).mp
                (sentence.close g ν (fun chosen =>
                  (encoded.correct rs hc g chosen).mp
                    (h.down (Decide.Inputs.observe es sentence.parameters rs g chosen)))))))⟩
      else none
    else none

/-- The same positive transport through the existing array-read reduction. -/
private def loweredArrayProof {C : Contract} (φ : Fml C []) : Option (PLift (Fml.Valid φ)) :=
  match hl : φ.toLS true Decide.SymS.init with
  | none => none
  | some leaf => do
    let body ← Decide.arrayBody? leaf.elim.condSimp.prenex
    if (body.cut.gx.liftCondB Decide.condLiftFuel Decide.liftBudget).isNone then none else do
      let flat ← Decide.flattenedArithmetic? (Decide.readBudget body.leaf.cutAll) body.leaf
      let h ← arithmeticProof flat.encoding.arithmetic
      return ⟨Fml.Valid.of_toLS hl (fun g ν =>
        (Decide.LFml.elim_holds g leaf ν).mp
          ((Decide.LFml.condSimp_holds g _ ν).mp
            ((Decide.LFml.prenex_holds g _ ν).mp
              (body.pre.close g ν (fun chosen => by
                have hv := body.valid_iff.mpr (flat.valid_iff.mpr h.down)
                exact body.holds_body g chosen (hv g))))))⟩

def directArithmeticProof {C : Contract} (φ : Fml C []) : Option (PLift (Fml.Valid φ)) :=
  let simple : Option (PLift (Fml.Valid φ)) := do
    let r ← Decide.inputReduction? φ
    let h ← arithmeticProof r.arithmetic
    return ⟨r.valid_iff.mpr h.down⟩
  simple.orElse fun _ => (loweredArithmeticProof φ).orElse fun _ => (loweredArrayProof φ).orElse fun _ => do
    -- Loop frames introduce universal locals below antecedents. The existing
    -- dependent reduction hoists that prefix and flattens dependent reads.
    let r ← Decide.dependentReduction? φ
    let h ← arithmeticProof r.arithmetic
    return ⟨r.valid_iff.mpr h.down⟩

def directArithmetic {C : Contract} (φ : Fml C []) : Bool :=
  (directArithmeticProof φ).isSome

end Solidity.Tools
