import Solidity.Source.Progress.BuiltinAdmission

/-! A builtin call used as an expression statement makes progress. This is a
statement-level lemma: the callee-body catalogue checker does not admit
bodies containing builtin statements, so no checked body reaches it yet. -/

namespace Solidity.Source.Progress
open EM

/-- Lift expression non-stuckness through the actual statement sub frame. -/
theorem execS_expression_ns {E : Env} (G : Glob E) (F : Fr) (n nps : Nat)
    (ph : Option (Ph E)) {R : List STy} {M : Bool} {k : SCtx} {Γ : RCtx} {t : STy}
    (e : RExpr E Γ t) (l : Locals E.layout Γ) (h : NS (evalE G F n e)) :
    NS (execS G F (n+1) nps ph (.expr (R := R) (M := M) (k := k) e) l) := by
  simp only [execS]
  exact NS.bind (NSP.ns (NSP.sub' (Q := fun _ => True)
    (NSP.weaken (NSP.of_ns h) fun _ _ _ => trivial))) fun _ => NS.pure' _

theorem checked_builtin_statement (res : Resolution) (G : Glob res.env) (c : String)
    (ha : (Source.elaborate res).isSome = true) (hg : G.prog = Source.progOf res.env)
    (hc : Solidity.Lowering.P9.WholeProgram.checkFunctions res G c = true)
    (F : Fr) (hF : F.contract = c) (n nps : Nat) (ph : Option (Ph res.env))
    {R : List STy} {M : Bool} {k : SCtx} {Γ : RCtx} {ts : List STy}
    (b : Builtin) (args : RArgs res.env Γ ts) (t : STy)
    (ht : b.callTy res.env.isBase ts = some t)
    (hf : BuiltinFragment (fun d => d ∈ Solidity.Lowering.P9.WholeProgram.functions res) b args t)
    (l : Locals res.env.layout Γ) :
    NS (execS G F (n+1) nps ph
      (.expr (R := R) (M := M) (k := k) (.builtin b args ht)) l) :=
  execS_expression_ns G F n nps ph _ l (checked_builtin res G c ha hg hc F hF n b args t ht hf)

#print axioms checked_builtin_statement
end Solidity.Source.Progress
