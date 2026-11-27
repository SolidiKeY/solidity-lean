import Solidity.Backend.CompilerOptimizerDomain.ConstFold
import Solidity.Optimizer.Propagate

/-! Facts produced by constant propagation contain accepted simple values. -/
namespace Solidity.Backend.CompilerOptimizerDomain
open Solidity Solidity.Optimizer.ConstFold
open Solidity.Backend.AbiWorld.PublicCompilerTotal
variable {C : Contract}

def FactsOk {Γ : Ctx} (F : Facts C Γ) : Prop :=
  ∀ p (i : Idx Γ (.val p)) s, F.get p i = some s → ValOk (.simple s)

theorem facts_empty_ok {Γ : Ctx} : FactsOk (Facts.empty : Facts C Γ) :=
  fun _ _ _ h => nomatch h

theorem asSimple_ok {Γ : Ctx} {p : PrimTy} (v : Val C Γ p) {s : Simple C Γ p}
    (h : v.asSimple? = some s) : ValOk (.simple s) := by
  cases v <;> simp only [Val.asSimple?, reduceCtorEq] at h
  next t =>
    cases t <;> simp only [Simple.asPure?, Option.some.injEq, reduceCtorEq] at h
    all_goals subst s; constructor

theorem shiftS_ok {Γ : Ctx} {p : PrimTy} {s : Simple C Γ p} (h : ValOk (.simple s))
    (t : LTy) : ValOk (.simple (shiftS (t := t) s)) := by
  cases h <;> constructor <;> assumption

theorem facts_set_ok {Γ : Ctx} {p : PrimTy} {F : Facts C Γ} (hF : FactsOk F)
    (i : Idx Γ (.val p)) (v : Val C Γ p) : FactsOk (F.set i v.asSimple?) := by
  intro q j s hs
  simp only [Facts.set] at hs
  split at hs
  · cases hv : v.asSimple? with
    | none => simp only [hv, reduceCtorEq] at hs
    | some t =>
        simp only [hv] at hs
        split at hs
        · next hq =>
            subst q
            simp only [Option.some.injEq] at hs
            subst s
            exact asSimple_ok v hv
        · contradiction
  · cases hf : F.get q j with
    | none => simp only [hf, reduceCtorEq] at hs
    | some t =>
        simp only [hf] at hs
        split at hs
        · contradiction
        · cases hs; exact hF _ _ _ hf

theorem facts_push_ok {Γ : Ctx} {p : PrimTy} {F : Facts C Γ} (hF : FactsOk F)
    (v : Option (Val C Γ p)) : FactsOk (F.push (v.bind Val.asSimple?)) := by
  intro q j s hs
  cases j with
  | here =>
      cases hv : v with
      | none => simp only [Facts.push, hv, Option.bind_none, Option.map_none, reduceCtorEq] at hs
      | some e =>
          cases he : e.asSimple? with
          | none => simp only [Facts.push, hv, Option.bind_some, he, Option.map_none, reduceCtorEq] at hs
          | some t =>
              simp only [Facts.push, hv, Option.bind_some, he, Option.map_some, Option.some.injEq] at hs
              subst s
              exact shiftS_ok (asSimple_ok e he) _
  | there j =>
      cases hf : F.get q j with
      | none => simp only [Facts.push, hf, Option.map_none, reduceCtorEq] at hs
      | some t =>
          simp only [Facts.push, hf, Option.map_some, Option.some.injEq] at hs
          subst s
          exact shiftS_ok (hF _ _ _ hf) _

theorem val_subst_ok {Γ : Ctx} {F : Facts C Γ} (hF : FactsOk F) :
    {p : PrimTy} → {v : Val C Γ p} → ValOk v → ValOk (v.subst F)
  | _, _, h@(.lit ..) => by simpa only [Val.subst] using h
  | _, _, h@(.bool ..) => h
  | _, _, .local i => by
      simp only [Val.subst]
      split
      · next hs => exact hF _ _ _ hs
      · exact .local i
  | _, _, h@(.env ..) => by simpa only [Val.subst] using h
  | _, _, h@(.read ..) => h
  | _, _, h@(.len ..) => h
  | _, _, .binop op h hq ha hb => .binop op h hq (val_subst_ok hF ha) (val_subst_ok hF hb)
  | _, _, .unop op h hq ha => .unop op h hq (val_subst_ok hF ha)
  | _, _, .ternary hc ha hb => .ternary (val_subst_ok hF hc) (val_subst_ok hF ha) (val_subst_ok hF hb)

theorem val_opt_ok {Γ : Ctx} {F : Facts C Γ} (hF : FactsOk F) {p : PrimTy}
    {v : Val C Γ p} (hv : ValOk v) : ValOk (v.opt F) := val_cfold_ok (val_subst_ok hF hv)

mutual
theorem stmt_cprop_ok : {Γ Γ' : Ctx} → {K K' : Kinds} → {s : Solidity.Stmt C Γ Γ'} →
    StmtOk K s K' → {F : Facts C Γ} → FactsOk F →
    StmtOk K (Stmt.cprop F s).1 K' ∧ FactsOk (Stmt.cprop F s).2
  | _, _, _, _, _, .assign hl hv, _, hF => ⟨.assign hl (val_opt_ok hF hv), hF⟩
  | _, _, _, _, _, .assignLocal i hv, _, hF =>
      ⟨.assignLocal i (val_opt_ok hF hv), facts_set_ok hF i _⟩
  | _, _, _, _, _, .declNone p x, _, hF => ⟨.declNone p x, facts_push_ok hF none⟩
  | _, _, _, _, _, .declSome p x hv, _, hF =>
      ⟨.declSome p x (val_opt_ok hF hv), facts_push_ok hF (some _)⟩
  | _, _, _, _, _, h@(.declStorage ..), _, _ => ⟨h, facts_empty_ok⟩
  | _, _, _, _, _, h@(.declIndexed ..), _, _ => ⟨h, facts_empty_ok⟩
  | _, _, _, _, _, h@(.rebind ..), _, _ => ⟨h, facts_empty_ok⟩
  | _, _, _, _, _, h@(.rebindIndexed ..), _, _ => ⟨h, facts_empty_ok⟩
  | _, _, _, _, _, h@(.opAssign ..), _, _ => ⟨h, facts_empty_ok⟩
  | _, _, _, _, _, h@(.incDec ..), _, _ => ⟨h, facts_empty_ok⟩
  | _, _, _, _, _, .require hc, _, hF => ⟨.require (val_opt_ok hF hc), hF⟩
  | _, _, _, _, _, .assert hc, _, hF => ⟨.assert (val_opt_ok hF hc), hF⟩
  | _, _, _, _, _, h@(.revert), _, _ => ⟨h, facts_empty_ok⟩
  | _, _, _, _, _, h@(.callNone ..), _, _ => ⟨h, facts_empty_ok⟩
  | _, _, _, _, _, h@(.callVal ..), _, _ => ⟨h, facts_empty_ok⟩
  | _, _, _, _, _, .ite hc ht he, _, hF =>
      ⟨.ite (val_opt_ok hF hc) (prog_cprop_ok ht hF) (prog_cprop_ok he hF), facts_empty_ok⟩
  | _, _, _, _, _, .block hb, _, hF => ⟨.block (prog_cprop_ok hb hF), facts_empty_ok⟩
  | _, _, _, _, _, .loop a hc hb, _, _ =>
      ⟨.loop a (val_cfold_ok hc) (prog_cprop_ok hb facts_empty_ok), facts_empty_ok⟩

theorem prog_cprop_ok : {Γ Δ : Ctx} → {K : Kinds} → {P : Solidity.Prog C Γ Δ} →
    ProgOk K P → {F : Facts C Γ} → FactsOk F → ProgOk K (Prog.cprop F P)
  | _, _, _, _, .nil, _, _ => .nil
  | _, _, _, _, .cons hs hp, _, hF =>
      .cons (stmt_cprop_ok hs hF).1 (prog_cprop_ok hp (stmt_cprop_ok hs hF).2)
end

end Solidity.Backend.CompilerOptimizerDomain
