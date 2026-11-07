import Solidity.Source.Progress.ReadyReturns

/-! Progress through syntactically ready memory statements and sequences.
The admission refines the preservation certificate with readiness, plain-value
extraction and default witnesses. Existing value loops keep their old checks;
new memory loops and modifiers are not admitted. -/
namespace Solidity.Source.Progress
open EM
variable {E : Env}

mutual
inductive ReadyStmt (A : Decl → Prop) (R : List STy) (M : Bool) :
    {k : SCtx} → {Γ Δ : RCtx} → RStmt E R M k Γ Δ → Prop
  | value {k Γ Δ} {s : RStmt E R M k Γ Δ} :
      s.ValFragC A → s.OpsOK → ReadyStmt A R M s
  | expr {k Γ τ} {e : RExpr E Γ τ} :
      ReadyExpr A e → ReadyStmt A R M (.expr (k := k) e)
  | declVar {k Γ} (τ : STy) : ZeroReady E τ →
      ReadyStmt A R M (.declVar (k := k) (Γ := Γ) τ)
  | declInit {k Γ τ} {e : RExpr E Γ τ} (same : τ.implicit E.isBase E.mapFree τ = true) :
      PlainResultType τ → ReadyExpr A e → ReadyStmt A R M (.declInit (k := k) e same)
  | returnValue {k Γ τ} {e : RExpr E Γ τ} (returns : R = [τ])
      (same : τ.implicit E.isBase E.mapFree τ = true) :
      PlainResultType τ → ReadyExpr A e → ReadyStmt A R M (.retVal (k := k) returns e same)
  | returns {k Γ} {args : RConvArgs E Γ R} :
      ReadyArgs A args → ReadyStmt A R M (.retTuple (k := k) args)
  | ifThen {k Γ Δ} {cond : RExpr E Γ .bool} {t : RStmt E R M k Γ Δ} :
      ReadyExpr A cond → ReadyStmt A R M t → ReadyStmt A R M (.ifThen cond t)
  | ifElse {k Γ Δ Ξ} {cond : RExpr E Γ .bool}
      {t : RStmt E R M k Γ Δ} {f : RStmt E R M k Γ Ξ} :
      ReadyExpr A cond → ReadyStmt A R M t → ReadyStmt A R M f →
      ReadyStmt A R M (.ifElse cond t f)
  | block {k Γ Δ} {b : RItems E R M k Γ Δ} :
      ReadyItems A R M b → ReadyStmt A R M (.block b)
inductive ReadyItems (A : Decl → Prop) (R : List STy) (M : Bool) :
    {k : SCtx} → {Γ Δ : RCtx} → RItems E R M k Γ Δ → Prop
  | nil {k Γ} : ReadyItems A R M (.nil (k := k) (Γ := Γ))
  | stmt {k Γ Ξ Δ} {s : RStmt E R M k Γ Ξ} {rest : RItems E R M k Ξ Δ} :
      ReadyStmt A R M s → ReadyItems A R M rest → ReadyItems A R M (.stmt s rest)
  | unchecked {l Γ Ξ Δ} {b : RItems E R M ⟨l,true⟩ Γ Ξ}
      {rest : RItems E R M ⟨l,false⟩ Γ Δ} :
      ReadyItems A R M b → ReadyItems A R M rest → ReadyItems A R M (.unchecked b rest)
end

theorem ReadyStmt.memory {A : Decl → Prop} {R : List STy} {M : Bool} {k : SCtx} {Γ Δ : RCtx}
    {s : RStmt E R M k Γ Δ} (ready : ReadyStmt A R M s) : Preservation.MemoryStmt A R M s := by
  induction ready using ReadyStmt.rec
    (motive_2 := fun {k Γ Δ} b _ => Preservation.MemoryItems A R M b) with
  | value fragment operations => exact .value fragment operations
  | expr expression => exact .expr (.base expression.allocating)
  | declVar τ _ => exact .declVar τ
  | declInit same _ expression => exact .declInit same (.base expression.allocating)
  | returnValue returns same _ expression => exact .returnValue returns same (.base expression.allocating)
  | returns args => exact .returns args.exact
  | ifThen condition yes ih => exact .ifThen (.base condition.allocating) ih
  | ifElse condition yes no ihy ihn => exact .ifElse (.base condition.allocating) ihy ihn
  | block items ih => exact .block ih
  | nil => exact .nil
  | stmt head tail ihh iht => exact .stmt ihh iht
  | unchecked inner tail ihi iht => exact .unchecked ihi iht

theorem ReadyItems.memory {A : Decl → Prop} {R : List STy} {M : Bool} {k : SCtx} {Γ Δ : RCtx}
    {items : RItems E R M k Γ Δ} (ready : ReadyItems A R M items) : Preservation.MemoryItems A R M items := by
  induction ready using ReadyItems.rec
    (motive_1 := fun {k Γ Δ} s _ => Preservation.MemoryStmt A R M s) with
  | value fragment operations => exact .value fragment operations
  | expr expression => exact .expr (.base expression.allocating)
  | declVar τ _ => exact .declVar τ
  | declInit same _ expression => exact .declInit same (.base expression.allocating)
  | returnValue returns same _ expression => exact .returnValue returns same (.base expression.allocating)
  | returns args => exact .returns args.exact
  | ifThen condition yes ih => exact .ifThen (.base condition.allocating) ih
  | ifElse condition yes no ihy ihn => exact .ifElse (.base condition.allocating) ihy ihn
  | block items ih => exact .block ih
  | nil => exact .nil
  | stmt head tail ihh iht => exact .stmt ihh iht
  | unchecked inner tail ihi iht => exact .unchecked ihi iht

structure ReadyBodyAt (A : Decl → Prop) (G : Glob E) (c : String) (n : Nat) : Prop where
  stmt : ∀ F, F.contract = c → ∀ nps ph {R : List STy} {M : Bool} {k : SCtx} {Γ Δ : RCtx}
    (s : RStmt E R M k Γ Δ), ReadyStmt A R M s → ∀ l, BodyFrame nps R Γ →
    NSP (execS G F n nps ph s l) (fun o => k.loop = false → o.esc = false)
  items : ∀ F, F.contract = c → ∀ nps ph {R : List STy} {M : Bool} {k : SCtx} {Γ Δ : RCtx}
    (b : RItems E R M k Γ Δ), ReadyItems A R M b → ∀ l, BodyFrame nps R Γ →
    NSP (execItems G F n nps ph b l) (fun o => k.loop = false → o.esc = false)

theorem ready_stmt_step {A : Decl → Prop} {G : Glob E} {c : String} {n : Nat}
    (calls : CallsOK A G c) (ih : ReadyBodyAt A G c n)
    (F : Fr) (contract : F.contract = c) (nps : Nat) (ph : Option (Ph E))
    {R : List STy} {M : Bool} {k : SCtx} {Γ Δ : RCtx} (s : RStmt E R M k Γ Δ)
    (ready : ReadyStmt A R M s) (l : Locals E.layout Γ) (frame : BodyFrame nps R Γ) :
    NSP (execS G F (n+1) nps ph s l) (fun o => k.loop = false → o.esc = false) := by
  have plain : ∀ {τ} (e : RExpr E Γ τ), PlainResultType τ → ReadyExpr A e →
      NS (do getV (← convRV F n τ (← evalE G F n e))) := by
    intro τ e extraction expression
    refine NS.bind (eval_ready_expr_ns calls F contract n e expression) (fun v => ?_)
    simp only [convRV,↓reduceDIte,pure_bind]
    exact getV_plain_ns extraction v
  cases ready with
  | value fragment operations =>
    exact NSP.weaken ((fragAt calls (n+1)).stmt.execS F contract nps ph s l fragment operations frame)
      (fun _ h => h.2)
  | expr expression =>
    rw [execS]
    exact NSP.bind (NSP.sub' (Q := fun _ => True) (NSP.weaken
      (NSP.of_ns (eval_ready_expr_ns calls F contract n _ expression)) (fun _ _ _ => trivial)))
      (fun _ _ => NSP.pure' (fun _ => rfl))
  | declVar τ defaults =>
    rw [execS]
    exact NSP.bind (NSP.sub' (Q := fun _ => True) (NSP.weaken
      (NSP.of_ns (zero_ready_ns defaults n)) (fun _ _ _ => trivial)))
      (fun _ _ => NSP.pure' (fun _ => rfl))
  | declInit same extraction expression =>
    rw [execS]
    exact NSP.bind (NSP.sub' (Q := fun _ => True) (NSP.weaken
      (NSP.of_ns (plain _ extraction expression)) (fun _ _ _ => trivial)))
      (fun _ _ => NSP.pure' (fun _ => rfl))
  | returnValue returns same extraction expression =>
    subst R
    exact NSP.weaken (return_ready_nsp calls F contract n nps ph _ same extraction expression l frame)
      (fun _ h _ => by rcases h with ⟨last,rfl⟩; rfl)
  | returns args =>
    rw [execS]
    obtain ⟨ys,ps,rfl,length⟩ := frame
    refine NSP.bind (NSP.sub' (Q := fun _ => True) (NSP.weaken
      (NSP.of_ns (eval_ready_args_ns calls F contract n _ args)) (fun _ _ _ => trivial)))
      (fun p _ => ?_)
    have offset : (ys ++ (R.reverse ++ ps)).length - (nps + R.length) = ys.length := by
      simp only [List.length_append,List.length_reverse]
      omega
    rw [offset]
    exact NSP.bind (NSP.lift_ok (setRets_ok ys R p.2 rfl p.1))
      (fun _ _ => NSP.pure' (fun _ => rfl))
  | @block k Γ Δ b items =>
    rw [execS]
    obtain ⟨ys,rfl⟩ := RItems.ext b
    exact NSP.bind (ih.items F contract nps ph _ items l frame) (fun o h =>
      NSP.weaken (Out.close_esc ys o) (fun _ same loop => same.trans (h loop)))
  | @ifThen k Γ Δ cond t condition yes =>
    rw [execS]
    refine NSP.bind (NSP.sub' (Q := fun _ => True) (NSP.weaken
      (NSP.of_ns (eval_ready_expr_ns calls F contract n _ condition)) (fun _ _ _ => trivial)))
      (fun p _ => NSP.bind (NSP.of_ns (getV_ns rfl p.1)) (fun x _ => ?_))
    split
    · obtain ⟨ys,rfl⟩ := RStmt.ext t
      exact NSP.bind (ih.stmt F contract nps ph _ yes p.2 frame) (fun o h =>
        NSP.weaken (Out.close_esc ys o) (fun _ same loop => same.trans (h loop)))
    · exact NSP.pure' (fun _ => rfl)
  | @ifElse k Γ Δ Ξ cond t f condition yes no =>
    rw [execS]
    refine NSP.bind (NSP.sub' (Q := fun _ => True) (NSP.weaken
      (NSP.of_ns (eval_ready_expr_ns calls F contract n _ condition)) (fun _ _ _ => trivial)))
      (fun p _ => NSP.bind (NSP.of_ns (getV_ns rfl p.1)) (fun x _ => ?_))
    split
    · obtain ⟨ys,rfl⟩ := RStmt.ext t
      exact NSP.bind (ih.stmt F contract nps ph _ yes p.2 frame) (fun o h =>
        NSP.weaken (Out.close_esc ys o) (fun _ same loop => same.trans (h loop)))
    · obtain ⟨ys,rfl⟩ := RStmt.ext f
      exact NSP.bind (ih.stmt F contract nps ph _ no p.2 frame) (fun o h =>
        NSP.weaken (Out.close_esc ys o) (fun _ same loop => same.trans (h loop)))

theorem ready_items_step {A : Decl → Prop} {G : Glob E} {c : String} {n : Nat}
    (ih : ReadyBodyAt A G c n) (F : Fr) (contract : F.contract = c) (nps : Nat) (ph : Option (Ph E))
    {R : List STy} {M : Bool} {k : SCtx} {Γ Δ : RCtx} (b : RItems E R M k Γ Δ)
    (ready : ReadyItems A R M b) (l : Locals E.layout Γ) (frame : BodyFrame nps R Γ) :
    NSP (execItems G F (n+1) nps ph b l) (fun o => k.loop = false → o.esc = false) := by
  cases ready with
  | nil => exact NSP.pure' (fun _ => rfl)
  | @stmt k Γ Ξ Δ s rest head tail =>
    rw [execItems]
    obtain ⟨ys,rfl⟩ := RStmt.ext s
    refine NSP.bind (ih.stmt F contract nps ph _ head l frame) (fun o h => ?_)
    cases o with
    | normal l' =>
      exact NSP.bind (ih.items F contract nps ph _ tail l' (frame.ext ys)) (fun out result =>
        NSP.weaken (Out.up_esc ys out) (fun _ same loop => same.trans (result loop)))
    | brk _ | cont _ => exact NSP.pure' h
    | ret _ => exact NSP.pure' (fun _ => rfl)
  | @unchecked loop Γ Ξ Δ b rest inner tail =>
    rw [execItems]
    obtain ⟨ys,rfl⟩ := RItems.ext b
    refine NSP.bind (ih.items {F with checked := false} contract nps ph _ inner l frame) (fun o h => ?_)
    cases o with
    | normal l' =>
      exact NSP.bind (NSP.lift_ok (Locals.restore_ok ys l')) (fun l'' _ =>
        ih.items F contract nps ph _ tail l'' frame)
    | brk _ | cont _ => exact NSP.pure' h
    | ret _ => exact NSP.pure' (fun _ => rfl)

theorem ready_body_at {A : Decl → Prop} {G : Glob E} {c : String}
    (calls : CallsOK A G c) : ∀ n, ReadyBodyAt A G c n
  | 0 => {
      stmt := by intros; rw [execS.eq_1]; exact NSP.halt' trivial
      items := by intros; rw [execItems.eq_1]; exact NSP.halt' trivial }
  | n+1 => {
      stmt := ready_stmt_step calls (ready_body_at calls n)
      items := ready_items_step (ready_body_at calls n) }

#print axioms ready_body_at
#print axioms ReadyItems.memory
end Solidity.Source.Progress
