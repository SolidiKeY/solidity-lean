import Solidity.Source.Progress.BuiltinStatements

/-! Callee-body sequences containing the proved builtin and emit statements.
This additive syntactic admission keeps the old value statement fragment,
including its loops, intact. New effects are admitted at sequence positions;
effects nested inside an old conditional/loop remain outside this admission. -/
namespace Solidity.Source.Progress
open EM
variable {E : Env}

inductive EffectItems (A : Decl → Prop) {R : List STy} {M : Bool} :
    {Γ Δ : RCtx} → RItems E R M .body Γ Δ → Prop
  | value {Γ Δ} {items : RItems E R M .body Γ Δ} :
      items.ValFragC A → items.OpsOK → EffectItems A items
  | stmt {Γ Ξ Δ} {s : RStmt E R M .body Γ Ξ} {rest : RItems E R M .body Ξ Δ} :
      s.ValFragC A → s.OpsOK → EffectItems A rest → EffectItems A (.stmt s rest)
  | builtin {Γ Δ ts t} {b : Builtin} {args : RArgs E Γ ts}
      {ht : b.callTy E.isBase ts = some t} {rest : RItems E R M .body Γ Δ} :
      BuiltinFragment A b args t → EffectItems A rest →
      EffectItems A (.stmt (.expr (.builtin b args ht)) rest)
  | emit {Γ Δ ps} {ev : Decl} {he : ev.paramTys E = some ps}
      {args : RConvArgs E Γ ps} {rest : RItems E R M .body Γ Δ} :
      ps.all STy.keyable = true → args.ValFragC A → args.OpsOK → EffectItems A rest →
      EffectItems A (.stmt (.emit ev he args) rest)

/-- A builtin expression statement either halts non-stuck or returns normal;
this is the flow fact needed to continue the containing body. -/
theorem builtin_statement_normal {A : Decl → Prop} (G : Glob E) (F : Fr)
    (he : ∀ n, ExprNSAt A G F n) (n nps : Nat) (ph : Option (Ph E))
    {R : List STy} {M : Bool} {Γ : RCtx} {ts : List STy} {t : STy}
    (b : Builtin) (args : RArgs E Γ ts) (ht : b.callTy E.isBase ts = some t)
    (hf : BuiltinFragment A b args t) (l : Locals E.layout Γ) :
    NSP (execS G F n nps ph (.expr (R := R) (M := M) (k := .body) (.builtin b args ht)) l)
      (fun o => ∃ l', o = .normal l') := by
  cases n with
  | zero => rw [execS.eq_1]; exact NSP.halt' trivial
  | succ n =>
    have expression : NS (evalE G F n (.builtin b args ht)) := by
      cases n with
      | zero => exact NS.halt' (fun _ h => by cases h)
      | succ k => exact builtinFragment_ns G F he hf k
    rw [execS]
    refine NSP.bind (NSP.sub' (Q := fun _ => True)
      (NSP.weaken (NSP.of_ns expression) (fun _ _ _ => trivial))) (fun p _ => ?_)
    exact NSP.pure' ⟨p.2,rfl⟩

/-- Elementary emits keep their actual static revert and event encoding, and
on success return a normal statement outcome. -/
theorem emit_statement_normal {A : Decl → Prop} (G : Glob E) (F : Fr)
    (he : ∀ n, ExprNSAt A G F n) (n nps : Nat) (ph : Option (Ph E))
    {R : List STy} {M : Bool} {Γ : RCtx} {ps : List STy}
    (ev : Decl) (hs : ev.paramTys E = some ps) (args : RConvArgs E Γ ps)
    (hp : ps.all STy.keyable = true) (hf : args.ValFragC A) (ho : args.OpsOK)
    (l : Locals E.layout Γ) :
    NSP (execS G F n nps ph (.emit (R := R) (M := M) (k := .body) ev hs args) l)
      (fun o => ∃ l', o = .normal l') := by
  cases n with
  | zero => rw [execS.eq_1]; exact NSP.halt' trivial
  | succ n =>
    rw [execS]
    refine NSP.bind (NSP.sub' (Q := fun _ => True)
      (NSP.weaken (NSP.of_ns ((he n).convArgs args hf ho)) (fun _ _ _ => trivial))) (fun p _ => ?_)
    refine NSP.bind (NSP.of_ns (encodeVals_key_ns F n false hp p.1)) (fun data _ => ?_)
    split
    · exact NSP.halt' trivial
    · refine NSP.bind (NSP.of_ns (NS.modSt' (fun s =>
        {s with logs := (F.this,G.selector (sigOf E.layout ev.name ps) ++ data) :: s.logs}))) (fun _ _ => ?_)
      exact NSP.pure' ⟨p.2,rfl⟩

/-- The complete sequence progresses, rather than just its direct effect
nodes. Every old statement retains its body-frame and operations premises. -/
theorem effect_items_ns {A : Decl → Prop} {G : Glob E} {c : String}
    (he : ∀ n F, F.contract = c → ExprNSAt A G F n)
    (hs : ∀ n, StmtNSAt G A (· = c) n) (F : Fr) (hc : F.contract = c)
    (nps : Nat) (ph : Option (Ph E)) {R : List STy} {M : Bool} :
    ∀ n {Γ Δ : RCtx} (items : RItems E R M .body Γ Δ), EffectItems A items →
      ∀ (l : Locals E.layout Γ), BodyFrame nps R Γ →
      NSP (execItems G F n nps ph items l) (fun o => o.esc = false)
  | 0, _, _, _, _, _, _ => by rw [execItems.eq_1]; exact NSP.halt' trivial
  | n+1, _, _, items, admitted, l, frame => by
    cases admitted with
    | value hf ho =>
      exact NSP.weaken ((hs (n+1)).execItems F hc nps ph items l hf ho frame)
        (fun _ h => h rfl)
    | @stmt Γ Ξ Δ s rest hf ho tail =>
      rw [execItems]
      obtain ⟨ys,rfl⟩ := RStmt.ext s
      refine NSP.bind ((hs n).execS F hc nps ph s l hf ho frame) (fun o h => ?_)
      cases o with
      | normal l' =>
        refine NSP.bind (effect_items_ns he hs F hc nps ph n rest tail l' (frame.ext ys)) (fun o' h' => ?_)
        exact NSP.weaken (Out.up_esc ys o') (fun _ h'' => h''.trans h')
      | brk _ => exact NSP.pure' (h.2 rfl)
      | cont _ => exact NSP.pure' (h.2 rfl)
      | ret _ => exact NSP.pure' rfl
    | @builtin Γ Δ ts t b args ht rest hf tail =>
      rw [execItems]
      refine NSP.bind (builtin_statement_normal G F (fun k => he k F hc) n nps ph b args ht hf l)
        (fun o h => ?_)
      rcases h with ⟨l',rfl⟩
      refine NSP.bind (effect_items_ns he hs F hc nps ph n rest tail l' frame) (fun o' h' => ?_)
      exact NSP.weaken (Out.up_esc [] o') (fun _ h'' => h''.trans h')
    | @emit Γ Δ ps ev ht args rest hp hf ho tail =>
      rw [execItems]
      refine NSP.bind (emit_statement_normal G F (fun k => he k F hc) n nps ph ev ht args hp hf ho l)
        (fun o h => ?_)
      rcases h with ⟨l',rfl⟩
      refine NSP.bind (effect_items_ns he hs F hc nps ph n rest tail l' frame) (fun o' h' => ?_)
      exact NSP.weaken (Out.up_esc [] o') (fun _ h'' => h''.trans h')

#print axioms builtin_statement_normal
#print axioms emit_statement_normal
#print axioms effect_items_ns
end Solidity.Source.Progress
