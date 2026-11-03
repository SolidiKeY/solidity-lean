import Solidity.Yul.RawLiteralScope

/-! In-range integer literal initialization beside authoritative raw locals.
The range premise is the actual Source integer type invariant. -/
namespace Solidity.Yul.RawIntegerInitialization
open RawLocalDeclaration RawDefaultDeclaration

def run {env types} (ty : Solidity.Source.IntTy) (value : Int)
    (inRange : ty.lo ≤ value ∧ value ≤ ty.hi)
    (fuel : Nat) (state : Snapshot env types) : Result env types (.int ty) :=
  match fuel with
  | 0 => .halted .timeout state
  | n+1 => match n with
    | 0 => .halted .timeout state
    | _+1 => .normal ⟨.cons (.int value inRange) state.clean,
        (.clean (.int value inRange),state.values),state.world⟩

def Preserves {env types} (ty : Solidity.Source.IntTy) (value : Int)
    (inRange : ty.lo ≤ value ∧ value ≤ ty.hi) (before : Snapshot env types)
    (result : Result env types (.int ty)) : Prop :=
  Result.casesOn (motive := fun _ => Prop) result
    (fun next =>
      next.clean = .cons (.int value inRange) before.clean ∧
      next.values = (.clean (.int value inRange),before.values) ∧
      next.world = before.world)
    (fun _ next => next = before)


theorem fits : ∀ (ty : Solidity.Source.IntTy) (value : Int),
 (Solidity.Source.Q.ofInt value).FitsInt ty ↔ (ty.lo ≤ value ∧ value ≤ ty.hi) := by
  intro ty value; simp only [Solidity.Source.Q.FitsInt, Solidity.Source.Q.ofInt, Solidity.Source.Q.isInt, Solidity.Source.Q.toInt, Int.natCast_one, Int.emod_one, Int.ediv_one, beq_self_eq_true, true_and]



theorem conversion : ∀ (layout : Solidity.Source.Layout) (ty : Solidity.Source.IntTy) (value : Int)
 (inRange : ty.lo ≤ value ∧ value ≤ ty.hi),
 Solidity.Source.constVal (D := layout) (Solidity.Source.Q.ofInt value) (.int ty) =
 .ok (Solidity.Source.Val.int value inRange) := by
  intro layout ty value inRange; simp only [Solidity.Source.constVal, Solidity.Source.Q.ofInt, Solidity.Source.Q.isInt, Solidity.Source.Q.toInt, Int.natCast_one, Int.emod_one, Int.ediv_one, beq_self_eq_true, ite_true, Solidity.Source.mkInt, dif_pos inRange]; rfl

theorem admissible : ∀ (env : Solidity.Source.Env) (ty : Solidity.Source.IntTy) (value : Int)
 (_inRange : ty.lo ≤ value ∧ value ≤ ty.hi),
 Solidity.Source.STy.implicit env.isBase (.rational (Solidity.Source.Q.ofInt value)) (.int ty) = true := by
  intro env ty value inRange; rw [Solidity.Source.STy.implicit_rational_int]; exact decide_eq_true ((Solidity.Yul.RawIntegerInitialization.fits ty value).2 inRange)



theorem correct :  ∀ (env : Solidity.Source.Env) (types : Solidity.Source.RCtx) (ty : Solidity.Source.IntTy) (value : Int)
 (inRange : ty.lo ≤ value ∧ value ≤ ty.hi)
 (returns : List Solidity.Source.STy) (modifier : Bool) (control : Solidity.Source.SCtx)
 (glob : Solidity.Source.Glob env) (frame : Solidity.Source.Fr) (fuel nps : Nat)
 (ph : Option (Solidity.Source.Ph env)) (state : Solidity.Yul.RawLocalDeclaration.Snapshot env types),
 Solidity.Yul.RawIntegerInitialization.Preserves ty value inRange state
   (Solidity.Yul.RawIntegerInitialization.run ty value inRange fuel state) ∧
 (Solidity.Source.execS glob frame fuel nps ph
   (Solidity.Source.RStmt.declInit (E := env) (R := returns) (M := modifier)
     (k := control) (Γ := types) (τ := .int ty) (.const (Solidity.Source.Q.ofInt value))
       (Solidity.Yul.RawIntegerInitialization.admissible env ty value inRange)) state.clean).run
  (Solidity.Source.L0 env,state.world) =
  Solidity.Yul.RawDefaultDeclaration.project (Solidity.Yul.RawIntegerInitialization.run ty value inRange fuel state) := by
  intro env types ty value inRange returns modifier control glob frame fuel nps ph state
  cases fuel with
  | zero => exact ⟨rfl,rfl⟩
  | succ fuel =>
    cases fuel with
    | zero => exact ⟨rfl,rfl⟩
    | succ fuel =>
      constructor
      · exact ⟨rfl,rfl,rfl⟩
      · simp only [Solidity.Source.execS,Solidity.Source.evalE,Solidity.Source.convRV,
          Solidity.Yul.RawIntegerInitialization.conversion env.layout ty value inRange]
        rfl


end Solidity.Yul.RawIntegerInitialization
