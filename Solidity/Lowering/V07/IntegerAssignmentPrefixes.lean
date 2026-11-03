import Solidity.Lowering.V07.IntegerLocalFamily

/-! Natural prefixes of actual local assignments. These are sequences of the
existing locals/environments, not an operation AST, state layer or Source
execution semantics. Each recurrence is identified with actual published runs.
No length/depth cutoff is a source admission rule. -/
namespace Solidity.Lowering.V07

def sourceIntegerPrefixes {D : Source.Layout} {Γ : Source.RCtx} {ι : Type}
    {t : Source.IntTy} (si : ι → Source.Idx Γ (.int t)) (written rhs : Nat → ι)
    (source : Source.Locals D Γ) : Nat → Source.Locals D Γ
  | 0 => source
  | n+1 => let previous := sourceIntegerPrefixes si written rhs source n
           previous.set (si (written n)) (previous.get (si (rhs n)))

def targetIntegerPrefixes {C : Contract} {H : HTy} {Γ : Ctx} {ι : Type}
    {p : PrimTy} (ti : ι → Idx Γ (.val p)) (written rhs : Nat → ι)
    (target : TEnv C H Γ) : Nat → TEnv C H Γ
  | 0 => target
  | n+1 => let previous := targetIntegerPrefixes ti written rhs target n
           TEnv.set (ti (written n)) (TEnv.get (ti (rhs n)) previous) previous

theorem integer_assignment_prefix_family {D : Source.Layout} {srcΓ : Source.RCtx}
    {C : Contract} {H : HTy} {Γ : Ctx} {ι : Type} {t : Source.IntTy}
    {si : ι → Source.Idx srcΓ (.int t)} {ti : ι → Idx Γ (.val (integerPrim t))}
    {source : Source.Locals D srcΓ} {target : TEnv C H Γ}
    (initial : IntegerLocalFamily t si ti source target) (written rhs : Nat → ι) (n : Nat) :
    IntegerLocalFamily t si ti (sourceIntegerPrefixes si written rhs source n)
      (targetIntegerPrefixes ti written rhs target n) := by
  induction n with
  | zero => exact initial
  | succ n ih => exact ih.write (written n) (rhs n)

theorem integer_assignment_prefix_step {E : Source.Env} {srcΓ : Source.RCtx}
    {C : Contract} {Γ : Ctx} {ι : Type} (t : Source.IntTy)
    (si : ι → Source.Idx srcΓ (.int t)) (ti : ι → Idx Γ (.val (integerPrim t)))
    (G : Source.Glob E) (F : Source.Fr) (fuel n : Nat)
    (source : Source.EMState E srcΓ) (target : State C Γ)
    (initial : IntegerLocalFamily t si ti source.1 target.env) (written rhs : Nat → ι) :
    (Source.evalE G F (fuel+2)
      (.assign (.local (si (written n))) (.local (si (rhs n))))).run
      (sourceIntegerPrefixes si written rhs source.1 n,source.2) =
      (.ok (.val ((sourceIntegerPrefixes si written rhs source.1 n).get (si (rhs n)))),
        (sourceIntegerPrefixes si written rhs source.1 (n+1),source.2)) ∧
    (assignLocalOperand (ti (written n)) (ti (rhs n))).run
      (target.withEnv (targetIntegerPrefixes ti written rhs target.env n)) =
      .ok (⟨target.withEnv (targetIntegerPrefixes ti written rhs target.env (n+1)),List.prefix_refl _⟩,
        .prim (TEnv.get (ti (rhs n)) (targetIntegerPrefixes ti written rhs target.env n))) ∧
    IntegerLocalFamily t si ti (sourceIntegerPrefixes si written rhs source.1 (n+1))
      (targetIntegerPrefixes ti written rhs target.env (n+1)) := by
  have reached := integer_assignment_prefix_family initial written rhs n
  simpa only [sourceIntegerPrefixes,targetIntegerPrefixes,State.withEnv,State.setLocal] using
    assignment_family_transport t si ti G F fuel
      (sourceIntegerPrefixes si written rhs source.1 n,source.2)
      (target.withEnv (targetIntegerPrefixes ti written rhs target.env n)) reached (written n) (rhs n)

end Solidity.Lowering.V07
