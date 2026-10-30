import Solidity.Source.ExprProgress

/-!
# Progress of the interpreter on value statements (lane V04b)

`NSP m Q`: from every state, `m` returns a result satisfying `Q` or halts
other than `stuck`. For the **statement value fragment**
(`RStmt.ValFrag`: expression statements, declarations of types with a
default, blocks, `unchecked`, `if`, loops, `break`, `continue`, `return;`,
`return e;` and `return (a, b);` of value types, over expressions of the
value fragment)
execution is never `stuck`, at any horizon, in any modifier context,
provided its expressions are in the operations' domains (`RStmt.OpsOK`,
which every elaborated statement satisfies, `StmtD.toR_opsOK`) and its
locals are a function's frame (`BodyFrame`: they end in the return slots,
then the parameters): `stmtNS`, `itemsNS`. Outside loops no `break` or
`continue` escapes a block (`itemsNSP`), so a body without modifiers runs
to completion (`runMods_nil_ns`), and an internal call to such a body is
never `stuck` when dispatch finds it and its frame is the one the call
builds (`callInternal_ns`). For elaborated programs that frame is derived
(`Elaborated.body_locals`), and dispatch keeps the parameter types
(`Glob.dispatchFn_params`), so a call needs only the dispatched override's
return types to agree (`Elaborated.callInternal_call_ns`).

The scope facts it needs are structural: a statement's output context
extends its input (`RStmt.ext`, `RItems.ext`), so ending a scope
(`Locals.restore`, `Out.close`, `Out.up`) is never `stuck`; and a `for`
loop's iterations end normally or by `return` (`forIter`'s
postcondition).
-/

namespace Solidity.Source

open EM

variable {E : Env}

/-! ## Scopes -/

/-- **A statement only adds locals**, innermost first. -/
theorem RStmt.ext {R : List STy} {M : Bool} : {k : SCtx} → {Γ Γ' : RCtx} → RStmt E R M k Γ Γ' →
    ∃ ys, Γ' = ys ++ Γ
  | _, _, _, .declVar τ => ⟨[τ], rfl⟩
  | _, _, _, .declInit (τ := τ) _ _ => ⟨[τ], rfl⟩
  | _, _, _, .expr _ | _, _, _, .placeholder _ | _, _, _, .block _ | _, _, _, .ifThen _ _
  | _, _, _, .ifElse _ _ _ | _, _, _, .whileLoop _ _ | _, _, _, .doWhile _ _ | _, _, _, .forLoop _ _ _ _
  | _, _, _, .skip | _, _, _, .brk | _, _, _, .cont | _, _, _, .ret _ | _, _, _, .retVal _ _ _
  | _, _, _, .retTuple _ | _, _, _, .emit _ _ _ | _, _, _, .revertError _ _ _ | _, _, _, .rethrow _ => ⟨[], rfl⟩

/-- **A block only adds locals.** -/
theorem RItems.ext {R : List STy} {M : Bool} : {k : SCtx} → {Γ Γ' : RCtx} → RItems E R M k Γ Γ' →
    ∃ ys, Γ' = ys ++ Γ
  | _, _, _, .nil => ⟨[], rfl⟩
  | _, _, _, .stmt s rest =>
    match RStmt.ext s, RItems.ext rest with
    | ⟨ys, h1⟩, ⟨zs, h2⟩ => ⟨zs ++ ys, by rw [h2, h1, List.append_assoc]⟩
  | _, _, _, .unchecked _ rest => RItems.ext rest

/-- **Ending a scope is never `stuck`** when the inner context extends the
outer one. -/
theorem Locals.restore_ok {D : Layout} {Γ : RCtx} (ys : RCtx) (l : Locals D (ys ++ Γ)) :
    NotStuckR (l.restore Γ) := by
  intro w h
  unfold Locals.restore at h
  have e : (ys ++ Γ).drop ((ys ++ Γ).length - Γ.length) = Γ := by
    rw [List.length_append, Nat.add_sub_cancel, List.drop_left]
  rw [dif_pos e] at h
  cases h

theorem Out.close_ok {D : Layout} {Γ : RCtx} (ys : RCtx) (o : Out D Γ (ys ++ Γ)) : NotStuckR o.close := by
  cases o with
  | normal l => exact NotStuckR.bind (Locals.restore_ok ys l) fun _ => NotStuckR.pure _
  | brk _ => exact NotStuckR.pure _
  | cont _ => exact NotStuckR.pure _
  | ret _ => exact NotStuckR.pure _

theorem Out.up_ok {D : Layout} {Γ₀ Γ₂ : RCtx} (ys : RCtx) (o : Out D (ys ++ Γ₀) Γ₂) : NotStuckR (o.up Γ₀) := by
  cases o with
  | normal _ => exact NotStuckR.pure _
  | brk l => exact NotStuckR.bind (Locals.restore_ok ys l) fun _ => NotStuckR.pure _
  | cont l => exact NotStuckR.bind (Locals.restore_ok ys l) fun _ => NotStuckR.pure _
  | ret l => exact NotStuckR.bind (Locals.restore_ok ys l) fun _ => NotStuckR.pure _

/-- Whether an outcome is a `break` or a `continue`. -/
def Out.esc {D : Layout} {Γ Γ' : RCtx} : Out D Γ Γ' → Bool
  | .brk _ | .cont _ => true
  | _ => false

/-- Ending a scope keeps whether an outcome is a `break`/`continue`. -/
theorem Out.close_esc {Γ₀ Γ : RCtx} (ys : RCtx) (o : Out E.layout Γ (ys ++ Γ)) :
    NSP (lift o.close : EM E Γ₀ (Out E.layout Γ Γ)) (fun o' => o'.esc = o.esc) := by
  apply NSP.lift'
  cases o with
  | normal l =>
    have h := Locals.restore_ok ys l
    simp only [Out.close]
    cases e : l.restore Γ with
    | ok l' => rfl
    | error w =>
      show NotStuck w
      cases w with
      | stuck w' => exact absurd e (h w')
      | _ => trivial
  | brk _ => rfl
  | cont _ => rfl
  | ret _ => rfl

/-- Leaving a block keeps whether an outcome is a `break`/`continue`. -/
theorem Out.up_esc {Γ₀ Γ₁ Γ₂ : RCtx} (ys : RCtx) (o : Out E.layout (ys ++ Γ₀) Γ₂) :
    NSP (lift (o.up Γ₀) : EM E Γ₁ (Out E.layout Γ₀ Γ₂)) (fun o' => o'.esc = o.esc) := by
  apply NSP.lift'
  cases o with
  | normal _ => rfl
  | brk l =>
    have h := Locals.restore_ok ys l
    simp only [Out.up]
    cases e : l.restore Γ₀ with
    | ok l' => rfl
    | error w =>
      show NotStuck w
      cases w with
      | stuck w' => exact absurd e (h w')
      | _ => trivial
  | cont l =>
    have h := Locals.restore_ok ys l
    simp only [Out.up]
    cases e : l.restore Γ₀ with
    | ok l' => rfl
    | error w =>
      show NotStuck w
      cases w with
      | stuck w' => exact absurd e (h w')
      | _ => trivial
  | ret l =>
    have h := Locals.restore_ok ys l
    simp only [Out.up]
    cases e : l.restore Γ₀ with
    | ok l' => rfl
    | error w =>
      show NotStuck w
      cases w with
      | stuck w' => exact absurd e (h w')
      | _ => trivial

theorem NSP.lift_ok {Γ : RCtx} {α : Type} {r : R α} (h : NotStuckR r) : NSP (lift r : EM E Γ α) (fun _ => True) :=
  NSP.of_ns (NS.lift' h)

/-! ## The statement value fragment -/

/-- The fragment's conversions' source types. -/
def STy.FragSrc (σ : STy) : Prop := σ.isValue = true ∨ (∃ q, σ = .rational q) ∨ (∃ q k, σ = .hexConst q k)

def ROptBool.ValFrag {Γ : RCtx} : ROptBool E Γ → Prop
  | .none => True
  | .some c => c.ValFrag

def ROptExpr.ValFrag {Γ : RCtx} : ROptExpr E Γ → Prop
  | .none => True
  | .some (τ := τ) e => e.ValFrag ∧ τ.isValue = true

/-- A `for` initializer that completes normally when it completes. -/
def RStmt.Simple {R : List STy} {M : Bool} {k : SCtx} {Γ Γ' : RCtx} : RStmt E R M k Γ Γ' → Prop
  | .expr _ | .declVar _ | .declInit _ _ | .skip => True
  | _ => False

/-- Converted arguments of the fragment: each of the value fragment, at a
value type, converted from a value type or a constant. -/
def RConvArgs.ValFrag {Γ : RCtx} : {τs : List STy} → RConvArgs E Γ τs → Prop
  | _, .nil => True
  | _, .cons (σ := σ) (τ := τ) e _ es => e.ValFrag ∧ τ.isValue = true ∧ σ.FragSrc ∧ RConvArgs.ValFrag es

mutual

/-- **The statement value fragment.** -/
def RStmt.ValFrag {R : List STy} {M : Bool} : {k : SCtx} → {Γ Γ' : RCtx} → RStmt E R M k Γ Γ' → Prop
  | _, _, _, .expr e => e.ValFrag
  | _, _, _, .declVar τ => (Val.default E.layout τ).isSome = true
  | _, _, _, .declInit (σ := σ) (τ := τ) e _ => e.ValFrag ∧ τ.isValue = true ∧ σ.FragSrc
  | _, _, _, .block b => RItems.ValFrag b
  | _, _, _, .ifThen c s => c.ValFrag ∧ RStmt.ValFrag s
  | _, _, _, .ifElse c s t => c.ValFrag ∧ RStmt.ValFrag s ∧ RStmt.ValFrag t
  | _, _, _, .whileLoop c s => c.ValFrag ∧ RStmt.ValFrag s
  | _, _, _, .doWhile s c => RStmt.ValFrag s ∧ c.ValFrag
  | _, _, _, .forLoop i c p s => i.Simple ∧ RStmt.ValFrag i ∧ c.ValFrag ∧ p.ValFrag ∧ RStmt.ValFrag s
  | _, _, _, .skip | _, _, _, .brk | _, _, _, .cont | _, _, _, .ret _ => True
  | _, _, _, .retVal (σ := σ) (τ := τ) _ e _ => e.ValFrag ∧ τ.isValue = true ∧ σ.FragSrc
  | _, _, _, .retTuple es => RConvArgs.ValFrag es
  | _, _, _, _ => False

def RItems.ValFrag {R : List STy} {M : Bool} : {k : SCtx} → {Γ Γ' : RCtx} → RItems E R M k Γ Γ' → Prop
  | _, _, _, .nil => True
  | _, _, _, .stmt s rest => RStmt.ValFrag s ∧ RItems.ValFrag rest
  | _, _, _, .unchecked b rest => RItems.ValFrag b ∧ RItems.ValFrag rest

end

theorem zeroVal_ns {Γ : RCtx} (n : Nat) {τ : STy} (h : (Val.default E.layout τ).isSome = true) :
    NS (zeroVal (E := E) (Γ := Γ) n τ) := by
  cases n with
  | zero => exact NS.halt' fun _ e => by cases e
  | succ n =>
    unfold zeroVal
    rcases hd : Val.default E.layout τ with _ | v
    · rw [hd] at h; cases h
    · exact NS.pure' _

/-- **The frame of a body**: its locals end in the return slots (last
return innermost), then the `nps` parameters, as `callInternal` builds
them; declarations push on top. -/
def BodyFrame (nps : Nat) (R : List STy) (Γ : RCtx) : Prop := ∃ ys ps, Γ = ys ++ (R.reverse ++ ps) ∧ ps.length = nps

theorem BodyFrame.ext {nps : Nat} {R : List STy} {Γ : RCtx} (h : BodyFrame nps R Γ) (zs : RCtx) : BodyFrame nps R (zs ++ Γ) := by
  obtain ⟨ys, ps, rfl, hn⟩ := h
  exact ⟨zs ++ ys, ps, by simp only [List.append_assoc], hn⟩

/-- Writing the local below `ys` at its type is never `stuck`. -/
theorem Locals.setAt_ok {D : Layout} {τ : STy} {rest : RCtx} : (ys : RCtx) → (l : Locals D (ys ++ τ :: rest)) →
    (v : Val D τ) → NotStuckR (l.setAt ys.length v)
  | [], .cons _ _, v => by
    intro w h
    simp only [List.length_nil, Locals.setAt, dif_pos rfl] at h
    cases h
  | _ :: ys, .cons _ r, v => NotStuckR.bind (Locals.setAt_ok ys r v) fun _ => NotStuckR.pure _

theorem Locals.setAt_ok' {D : Layout} {τ : STy} {rest Γ : RCtx} (ys : RCtx) (hΓ : Γ = ys ++ τ :: rest)
    (l : Locals D Γ) (v : Val D τ) : NotStuckR (l.setAt ys.length v) := by
  subst hΓ
  exact Locals.setAt_ok ys l v

section
variable (G : Glob E)

/-- **The induction hypothesis**: at horizon `n`, statements, blocks and
`for` iterations of the fragment are never `stuck`; a simple statement
completes normally, `for` iterations normally or by `return`. -/
structure StmtNSAt (n : Nat) : Prop where
  execS : ∀ (F : Fr) (nps : Nat) (ph : Option (Ph E)) {R : List STy} {M : Bool} {k : SCtx} {Γ Γ' : RCtx}
    (s : RStmt E R M k Γ Γ') (l : Locals E.layout Γ), s.ValFrag → s.OpsOK → BodyFrame nps R Γ →
    NSP (execS G F n nps ph s l) (fun o => (s.Simple → ∃ l', o = .normal l') ∧ (k.loop = false → o.esc = false))
  execItems : ∀ (F : Fr) (nps : Nat) (ph : Option (Ph E)) {R : List STy} {M : Bool} {k : SCtx} {Γ Γ' : RCtx}
    (b : RItems E R M k Γ Γ') (l : Locals E.layout Γ), b.ValFrag → b.OpsOK → BodyFrame nps R Γ →
    NSP (execItems G F n nps ph b l) (fun o => k.loop = false → o.esc = false)
  forIter : ∀ (F : Fr) (nps : Nat) (ph : Option (Ph E)) {R : List STy} {M u : Bool} {Γ₁ Γ₂ : RCtx}
    (c : ROptBool E Γ₁) (post : ROptExpr E Γ₁) (body : RStmt E R M ⟨true, u⟩ Γ₁ Γ₂) (l : Locals E.layout Γ₁),
    c.ValFrag → c.OpsOK → post.ValFrag → post.OpsOK → body.ValFrag → body.OpsOK → BodyFrame nps R Γ₁ →
    NSP (forIter G F n nps ph c post body l) (fun o => (∃ l', o = .normal l') ∨ (∃ l', o = .ret l'))

theorem stmtNSAt_zero : StmtNSAt G 0 where
  execS _ _ _ _ _ _ _ _ _ _ _ _ _ := by rw [execS.eq_1]; exact NSP.halt' trivial
  execItems _ _ _ _ _ _ _ _ _ _ _ _ _ := by rw [execItems.eq_1]; exact NSP.halt' trivial
  forIter _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ := by rw [forIter.eq_1]; exact NSP.halt' trivial

end

section
variable {G : Glob E} {n : Nat}

/-- **Converted arguments of the fragment** are never `stuck`. -/
theorem evalConvArgs_ns (G : Glob E) (F : Fr) {Γ : RCtx} : {τs : List STy} → (es : RConvArgs E Γ τs) →
    ∀ n, es.ValFrag → es.OpsOK → NS (evalConvArgs G F n es)
  | _, es, 0, _, _ => by rw [evalConvArgs.eq_1]; exact NS.halt' fun _ e => by cases e
  | _, .nil, n + 1, _, _ => by simp only [evalConvArgs]; exact NS.pure' _
  | _, .cons e h es, n + 1, hf, ho => by
    simp only [evalConvArgs]
    exact NS.bind (evalE_valFrag_ns G F n e hf.1 ho.1) fun v => NS.bind (convRV_ns F n (.inl h) hf.2.2.1 v)
      fun w => NS.bind (getV_ns hf.2.1 w) fun _ => NS.bind (evalConvArgs_ns G F es n hf.2.2.2 ho.2) fun _ =>
        NS.pure' _

/-- **Writing the return slots** of a body frame is never `stuck`. -/
theorem setRets_ok {D : Layout} {Γ : RCtx} (ys : RCtx) : (rs : List STy) → {ps : RCtx} → (l : Locals D Γ) →
    Γ = ys ++ (rs.reverse ++ ps) → (vs : Vals D rs) → NotStuckR (setRets l ys.length vs)
  | [], _, _, _, .nil => NotStuckR.pure _
  | τ :: τs, ps, l, hΓ, .cons v vs => by
    have hΓ' : Γ = (ys ++ τs.reverse) ++ τ :: ps := by
      rw [hΓ, List.reverse_cons, List.append_assoc, List.append_assoc, List.singleton_append]
    have h1 := Locals.setAt_ok' (ys ++ τs.reverse) hΓ' l v
    rw [List.length_append, List.length_reverse] at h1
    have hΓ'' : Γ = ys ++ (τs.reverse ++ τ :: ps) := by rw [hΓ', List.append_assoc]
    simp only [setRets]
    exact NotStuckR.bind h1 fun l' => setRets_ok ys τs l' hΓ'' vs

theorem execS_nsStep (ih : StmtNSAt G n) (F : Fr) (nps : Nat) (ph : Option (Ph E)) {R : List STy} {M : Bool}
    {k : SCtx} {Γ Γ' : RCtx} (s : RStmt E R M k Γ Γ') (l : Locals E.layout Γ) (hf : s.ValFrag) (ho : s.OpsOK)
    (hfr : BodyFrame nps R Γ) :
    NSP (execS G F (n + 1) nps ph s l) (fun o => (s.Simple → ∃ l', o = .normal l') ∧ (k.loop = false → o.esc = false)) := by
  have hE : ∀ {Γ τ} (e : RExpr E Γ τ), e.ValFrag → e.OpsOK → NSP (evalE G F n e) (fun _ => True) :=
    fun e hf ho => NSP.of_ns (evalE_valFrag_ns G F n e hf ho)
  have hsub : ∀ {Γ₀ τ} {l₀ : Locals E.layout Γ₀} (e : RExpr E Γ₀ τ), e.ValFrag → e.OpsOK →
      NSP (sub (Γ := []) l₀ (evalE G F n e)) (fun _ => True) :=
    fun e hf ho => NSP.sub' (NSP.weaken (hE e hf ho) fun _ _ _ => trivial)
  have hclose : ∀ {Γ₁} {t : RStmt E R M k Γ Γ₁} (l₁ : Locals E.layout Γ), t.ValFrag → t.OpsOK →
      NSP (do lift (← execS G F n nps ph t l₁).close)
        (fun (o : Out E.layout Γ Γ) => k.loop = false → o.esc = false) := by
    intro Γ₁ t l₁ ht ho'
    obtain ⟨ys, rfl⟩ := RStmt.ext t
    exact NSP.bind (ih.execS F nps ph t l₁ ht ho' hfr) fun o h =>
      NSP.weaken (Out.close_esc ys o) fun _ h' hk => h'.trans (h.2 hk)
  cases s with
  | expr e =>
    simp only [execS]
    exact NSP.bind (hsub e hf ho) fun _ _ => NSP.pure' ⟨fun _ => ⟨_, rfl⟩, fun _ => rfl⟩
  | declVar τ =>
    simp only [execS]
    exact NSP.bind (NSP.sub' (Q := fun _ => True) (NSP.weaken (NSP.of_ns (zeroVal_ns n hf))
      fun _ _ _ => trivial)) fun _ _ =>
      NSP.pure' ⟨fun _ => ⟨_, rfl⟩, fun _ => rfl⟩
  | declInit e h =>
    simp only [execS]
    refine NSP.bind (NSP.sub' (Q := fun _ => True) (NSP.weaken (NSP.of_ns ?_) fun _ _ _ => trivial)) fun _ _ =>
      NSP.pure' ⟨fun _ => ⟨_, rfl⟩, fun _ => rfl⟩
    exact NS.bind (evalE_valFrag_ns G F n e hf.1 ho) fun v =>
      NS.bind (convRV_ns F n (.inl h) hf.2.2 v) fun w => getV_ns hf.2.1 w
  | block b =>
    simp only [execS]
    obtain ⟨ys, rfl⟩ := RItems.ext b
    exact NSP.bind (ih.execItems F nps ph b l hf ho hfr) fun o h =>
      NSP.weaken (Out.close_esc ys o) fun _ h' => ⟨fun h0 => h0.elim, fun hk => h'.trans (h hk)⟩
  | ifThen c t =>
    simp only [execS]
    refine NSP.bind (hsub c hf.1 ho.1) fun p _ => NSP.bind (NSP.of_ns (getV_ns rfl p.1)) fun x _ => ?_
    split
    · exact NSP.weaken (hclose p.2 hf.2 ho.2) fun _ h => ⟨fun h0 => h0.elim, h⟩
    · exact NSP.pure' ⟨fun h => h.elim, fun _ => rfl⟩
  | ifElse c t f =>
    simp only [execS]
    refine NSP.bind (hsub c hf.1 ho.1) fun p _ => NSP.bind (NSP.of_ns (getV_ns rfl p.1)) fun x _ => ?_
    split
    · exact NSP.weaken (hclose p.2 hf.2.1 ho.2.1) fun _ h => ⟨fun h0 => h0.elim, h⟩
    · exact NSP.weaken (hclose p.2 hf.2.2 ho.2.2) fun _ h => ⟨fun h0 => h0.elim, h⟩
  | whileLoop c body =>
    simp only [execS]
    obtain ⟨ys, rfl⟩ := RStmt.ext body
    refine NSP.bind (hsub c hf.1 ho.1) fun p _ => NSP.bind (NSP.of_ns (getV_ns rfl p.1)) fun x _ => ?_
    split
    · refine NSP.bind (ih.execS F nps ph body p.2 hf.2 ho.2 hfr) fun o _ => ?_
      cases o with
      | normal l2 =>
        exact NSP.bind (NSP.lift_ok (Locals.restore_ok ys l2)) fun l3 _ =>
          NSP.weaken (ih.execS F nps ph _ l3 hf ho hfr) fun _ h => ⟨fun h0 => h0.elim, h.2⟩
      | cont l2 => exact NSP.weaken (ih.execS F nps ph _ l2 hf ho hfr) fun _ h => ⟨fun h0 => h0.elim, h.2⟩
      | brk _ => exact NSP.pure' ⟨fun h => h.elim, fun _ => rfl⟩
      | ret _ => exact NSP.pure' ⟨fun h => h.elim, fun _ => rfl⟩
    · exact NSP.pure' ⟨fun h => h.elim, fun _ => rfl⟩
  | @doWhile lp u0 _ _ body c =>
    simp only [execS]
    obtain ⟨ys, rfl⟩ := RStmt.ext body
    have tail : ∀ l₂ : Locals E.layout Γ, NSP (do
        let __discr ← sub l₂ (evalE G F n c)
        let __do_lift ← getV __discr.fst
        match __do_lift with
          | Val.bool true => execS G F n nps ph (body.doWhile c) __discr.snd
          | _ => pure (Out.normal __discr.snd))
        (fun o => lp = false → o.esc = false) := fun l₂ =>
      NSP.bind (hsub c hf.2 ho.2) fun p _ => NSP.bind (NSP.of_ns (getV_ns rfl p.1)) fun x _ => by
        split
        · exact NSP.weaken (ih.execS F nps ph _ p.2 hf ho hfr) fun _ h => h.2
        · exact NSP.pure' fun _ => rfl
    refine NSP.bind (ih.execS F nps ph body l hf.1 ho.1 hfr) fun o _ => ?_
    cases o with
    | normal l2 =>
      refine NSP.bind (NSP.lift_ok (Locals.restore_ok ys l2)) fun l3 _ => ?_
      exact NSP.weaken (tail l3) fun _ h => ⟨fun h0 => h0.elim, h⟩
    | cont l2 =>
      refine NSP.bind (NSP.pure' (Q := fun _ => True) trivial) fun l3 _ => ?_
      exact NSP.weaken (tail l3) fun _ h => ⟨fun h0 => h0.elim, h⟩
    | brk _ => exact NSP.pure' ⟨fun h => h.elim, fun _ => rfl⟩
    | ret _ => exact NSP.pure' ⟨fun h => h.elim, fun _ => rfl⟩
  | forLoop init c post body =>
    simp only [execS]
    obtain ⟨ys, rfl⟩ := RStmt.ext init
    refine NSP.bind (ih.execS F nps ph init l hf.2.1 ho.1 hfr) fun o ho1 => ?_
    obtain ⟨l1, rfl⟩ := ho1.1 hf.1
    refine NSP.bind (ih.forIter F nps ph c post body l1 hf.2.2.1 ho.2.1 hf.2.2.2.1 ho.2.2.1 hf.2.2.2.2 ho.2.2.2 (hfr.ext ys))
      fun o2 h2 => ?_
    rcases h2 with ⟨l2, rfl⟩ | ⟨l2, rfl⟩
    · exact NSP.bind (NSP.lift_ok (Locals.restore_ok ys l2)) fun _ _ => NSP.pure' ⟨fun h => h.elim, fun _ => rfl⟩
    · exact NSP.bind (NSP.lift_ok (Locals.restore_ok ys l2)) fun _ _ => NSP.pure' ⟨fun h => h.elim, fun _ => rfl⟩
  | skip => exact NSP.pure' ⟨fun _ => ⟨_, rfl⟩, fun _ => rfl⟩
  | brk => exact NSP.pure' ⟨fun h => h.elim, fun h => nomatch h⟩
  | cont => exact NSP.pure' ⟨fun h => h.elim, fun h => nomatch h⟩
  | ret _ => exact NSP.pure' ⟨fun h => h.elim, fun _ => rfl⟩
  | @retVal _ _ σ τ hR e h =>
    simp only [execS]
    obtain ⟨ys, ps, rfl, hn⟩ := hfr
    refine NSP.bind (NSP.sub' (Q := fun _ => True) (NSP.weaken (NSP.of_ns (NS.bind
      (evalE_valFrag_ns G F n e hf.1 ho) fun v => NS.bind (convRV_ns F n (.inl h) hf.2.2 v) fun w =>
        getV_ns hf.2.1 w)) fun _ _ _ => trivial)) fun p _ => ?_
    have hb : (ys ++ (R.reverse ++ ps)).length - (nps + R.length) = ys.length := by
      rw [hR, ← hn]
      simp only [List.length_append, List.length_reverse, List.length_singleton]
      omega
    have hΓ : ys ++ (R.reverse ++ ps) = ys ++ τ :: ps := by rw [hR]; rfl
    rw [hb]
    exact NSP.bind (NSP.lift_ok (Locals.setAt_ok' ys hΓ p.2 p.1)) fun _ _ =>
      NSP.pure' ⟨fun h => h.elim, fun _ => rfl⟩
  | retTuple es =>
    simp only [execS]
    obtain ⟨ys, ps, rfl, hn⟩ := hfr
    refine NSP.bind (NSP.sub' (Q := fun _ => True) (NSP.weaken (NSP.of_ns (evalConvArgs_ns G F es n hf ho))
      fun _ _ _ => trivial)) fun p _ => ?_
    have hb : (ys ++ (R.reverse ++ ps)).length - (nps + R.length) = ys.length := by
      simp only [List.length_append, List.length_reverse]
      omega
    rw [hb]
    exact NSP.bind (NSP.lift_ok (setRets_ok ys R p.2 rfl p.1)) fun _ _ =>
      NSP.pure' ⟨fun h => h.elim, fun _ => rfl⟩
  | _ => exact hf.elim

theorem execItems_nsStep (ih : StmtNSAt G n) (F : Fr) (nps : Nat) (ph : Option (Ph E)) {R : List STy} {M : Bool}
    {k : SCtx} {Γ Γ' : RCtx} (b : RItems E R M k Γ Γ') (l : Locals E.layout Γ) (hf : b.ValFrag) (ho : b.OpsOK)
    (hfr : BodyFrame nps R Γ) : NSP (execItems G F (n + 1) nps ph b l) (fun o => k.loop = false → o.esc = false) := by
  cases b with
  | nil => exact NSP.pure' fun _ => rfl
  | stmt s rest =>
    simp only [execItems]
    obtain ⟨ys, rfl⟩ := RStmt.ext s
    refine NSP.bind (ih.execS F nps ph s l hf.1 ho.1 hfr) fun o h => ?_
    cases o with
    | normal l1 =>
      exact NSP.bind (ih.execItems F nps ph rest l1 hf.2 ho.2 (hfr.ext ys)) fun o' h' =>
        NSP.weaken (Out.up_esc ys o') fun _ h'' hk => h''.trans (h' hk)
    | brk _ => exact NSP.pure' fun hk => h.2 hk
    | cont _ => exact NSP.pure' fun hk => h.2 hk
    | ret _ => exact NSP.pure' fun _ => rfl
  | unchecked inner rest =>
    simp only [execItems]
    obtain ⟨ys, rfl⟩ := RItems.ext inner
    refine NSP.bind (ih.execItems _ nps ph inner l hf.1 ho.1 hfr) fun o h => ?_
    cases o with
    | normal l1 =>
      exact NSP.bind (NSP.lift_ok (Locals.restore_ok ys l1)) fun l2 _ => ih.execItems F nps ph rest l2 hf.2 ho.2 hfr
    | brk _ => exact NSP.pure' fun hk => h hk
    | cont _ => exact NSP.pure' fun hk => h hk
    | ret _ => exact NSP.pure' fun _ => rfl

theorem forIter_nsStep (ih : StmtNSAt G n) (F : Fr) (nps : Nat) (ph : Option (Ph E)) {R : List STy} {M u : Bool}
    {Γ₁ Γ₂ : RCtx} (c : ROptBool E Γ₁) (post : ROptExpr E Γ₁) (body : RStmt E R M ⟨true, u⟩ Γ₁ Γ₂)
    (l : Locals E.layout Γ₁) (hc : c.ValFrag) (hc' : c.OpsOK) (hp : post.ValFrag) (hp' : post.OpsOK)
    (hb : body.ValFrag) (hb' : body.OpsOK) (hfr : BodyFrame nps R Γ₁) :
    NSP (forIter G F (n + 1) nps ph c post body l) (fun o => (∃ l', o = .normal l') ∨ (∃ l', o = .ret l')) := by
  simp only [forIter]
  obtain ⟨ys, rfl⟩ := RStmt.ext body
  cases c with
  | none =>
    refine NSP.bind (NSP.pure' (Q := fun _ => True) trivial) fun y _ => ?_
    split
    · exact NSP.pure' (.inl ⟨_, rfl⟩)
    · refine NSP.bind (NSP.pure' (Q := fun _ => True) trivial) fun _ _ => ?_
      refine NSP.bind (ih.execS F nps ph body y.2 hb hb' hfr) fun o _ => ?_
      cases o with
      | normal l2 =>
        refine NSP.bind (NSP.lift_ok (Locals.restore_ok ys l2)) fun l3 _ => ?_
        cases post with
        | none =>
          exact NSP.bind (NSP.pure' (Q := fun _ => True) trivial) fun l4 _ =>
            ih.forIter F nps ph _ _ body l4 hc hc' hp hp' hb hb' hfr
        | some pe =>
          exact NSP.bind (NSP.sub' (Q := fun _ => True) (NSP.weaken
            (NSP.of_ns (evalE_valFrag_ns G F n pe hp.1 hp')) fun _ _ _ => trivial)) fun q _ =>
            NSP.bind (NSP.pure' (Q := fun _ => True) trivial) fun l4 _ =>
              ih.forIter F nps ph _ _ body l4 hc hc' hp hp' hb hb' hfr
      | cont l2 =>
        refine NSP.bind (NSP.pure' (Q := fun _ => True) trivial) fun l3 _ => ?_
        cases post with
        | none =>
          exact NSP.bind (NSP.pure' (Q := fun _ => True) trivial) fun l4 _ =>
            ih.forIter F nps ph _ _ body l4 hc hc' hp hp' hb hb' hfr
        | some pe =>
          exact NSP.bind (NSP.sub' (Q := fun _ => True) (NSP.weaken
            (NSP.of_ns (evalE_valFrag_ns G F n pe hp.1 hp')) fun _ _ _ => trivial)) fun q _ =>
            NSP.bind (NSP.pure' (Q := fun _ => True) trivial) fun l4 _ =>
              ih.forIter F nps ph _ _ body l4 hc hc' hp hp' hb hb' hfr
      | brk _ => exact NSP.pure' (.inl ⟨_, rfl⟩)
      | ret _ => exact NSP.pure' (.inr ⟨_, rfl⟩)
  | some ce =>
    refine NSP.bind (NSP.sub' (Q := fun _ => True) (NSP.weaken
      (NSP.of_ns (evalE_valFrag_ns G F n ce hc hc')) fun _ _ _ => trivial)) fun p _ =>
      NSP.bind (NSP.of_ns (getV_ns rfl p.1)) fun x _ => ?_
    obtain ⟨b, rfl⟩ := Val.eq_bool x
    refine NSP.bind (NSP.pure' (Q := fun _ => True) trivial) fun y _ => ?_
    split
    · exact NSP.pure' (.inl ⟨_, rfl⟩)
    · refine NSP.bind (NSP.pure' (Q := fun _ => True) trivial) fun _ _ => ?_
      refine NSP.bind (ih.execS F nps ph body y.2 hb hb' hfr) fun o _ => ?_
      cases o with
      | normal l2 =>
        refine NSP.bind (NSP.lift_ok (Locals.restore_ok ys l2)) fun l3 _ => ?_
        cases post with
        | none =>
          exact NSP.bind (NSP.pure' (Q := fun _ => True) trivial) fun l4 _ =>
            ih.forIter F nps ph _ _ body l4 hc hc' hp hp' hb hb' hfr
        | some pe =>
          exact NSP.bind (NSP.sub' (Q := fun _ => True) (NSP.weaken
            (NSP.of_ns (evalE_valFrag_ns G F n pe hp.1 hp')) fun _ _ _ => trivial)) fun q _ =>
            NSP.bind (NSP.pure' (Q := fun _ => True) trivial) fun l4 _ =>
              ih.forIter F nps ph _ _ body l4 hc hc' hp hp' hb hb' hfr
      | cont l2 =>
        refine NSP.bind (NSP.pure' (Q := fun _ => True) trivial) fun l3 _ => ?_
        cases post with
        | none =>
          exact NSP.bind (NSP.pure' (Q := fun _ => True) trivial) fun l4 _ =>
            ih.forIter F nps ph _ _ body l4 hc hc' hp hp' hb hb' hfr
        | some pe =>
          exact NSP.bind (NSP.sub' (Q := fun _ => True) (NSP.weaken
            (NSP.of_ns (evalE_valFrag_ns G F n pe hp.1 hp')) fun _ _ _ => trivial)) fun q _ =>
            NSP.bind (NSP.pure' (Q := fun _ => True) trivial) fun l4 _ =>
              ih.forIter F nps ph _ _ body l4 hc hc' hp hp' hb hb' hfr
      | brk _ => exact NSP.pure' (.inl ⟨_, rfl⟩)
      | ret _ => exact NSP.pure' (.inr ⟨_, rfl⟩)

end

/-- **Progress on the statement value fragment**, at every horizon. -/
theorem stmtNSAt (G : Glob E) : ∀ n, StmtNSAt G n
  | 0 => stmtNSAt_zero G
  | n + 1 =>
    have ih := stmtNSAt G n
    { execS := fun F nps ph _ _ _ _ _ s l hf ho hfr => execS_nsStep ih F nps ph s l hf ho hfr
      execItems := fun F nps ph _ _ _ _ _ b l hf ho hfr => execItems_nsStep ih F nps ph b l hf ho hfr
      forIter := fun F nps ph _ _ _ _ _ c post body l hc hc' hp hp' hb hb' hfr =>
        forIter_nsStep ih F nps ph c post body l hc hc' hp hp' hb hb' hfr }

/-- **A statement of the value fragment in the operations' domains is
never `stuck`**: at every horizon, in every state, in any modifier
context. -/
theorem stmtNS (G : Glob E) (F : Fr) (n nps : Nat) (ph : Option (Ph E)) {R : List STy} {M : Bool} {k : SCtx}
    {Γ Γ' : RCtx} (s : RStmt E R M k Γ Γ') (l : Locals E.layout Γ) (hf : s.ValFrag) (ho : s.OpsOK)
    (hfr : BodyFrame nps R Γ) : NS (execS G F n nps ph s l) :=
  ((stmtNSAt G n).execS F nps ph s l hf ho hfr).ns

/-- **A block of the value fragment in the operations' domains is never
`stuck`.** -/
theorem itemsNS (G : Glob E) (F : Fr) (n nps : Nat) (ph : Option (Ph E)) {R : List STy} {M : Bool} {k : SCtx}
    {Γ Γ' : RCtx} (b : RItems E R M k Γ Γ') (l : Locals E.layout Γ) (hf : b.ValFrag) (ho : b.OpsOK)
    (hfr : BodyFrame nps R Γ) : NS (execItems G F n nps ph b l) :=
  ((stmtNSAt G n).execItems F nps ph b l hf ho hfr).ns

/-- **A block outside loops ends normally or by `return`**: no `break` or
`continue` escapes it (`Out.esc`), and it is never `stuck`. -/
theorem itemsNSP (G : Glob E) (F : Fr) (n nps : Nat) (ph : Option (Ph E)) {R : List STy} {M u : Bool}
    {Γ Γ' : RCtx} (b : RItems E R M ⟨false, u⟩ Γ Γ') (l : Locals E.layout Γ) (hf : b.ValFrag) (ho : b.OpsOK)
    (hfr : BodyFrame nps R Γ) : NSP (execItems G F n nps ph b l) (fun o => o.esc = false) :=
  NSP.weaken ((stmtNSAt G n).execItems F nps ph b l hf ho hfr) fun _ h => h rfl

/-- **Elaborated blocks**: a typing derivation whose elaboration is in the
value fragment is never `stuck` when run (the operations' domains come
from the derivation, `ItemsD.toR_opsOK`). -/
theorem ItemsD.toR_ns {C : Ctx} (G : Glob C.env) (F : Fr) (n nps : Nat) (ph : Option (Ph C.env))
    {k : SCtx} {L L' : List (String × STy)} {b : Syn (.list (.item k))} (d : ItemsD C L b L')
    (l : Locals C.env.layout (tysOf L)) (hf : d.toR.ValFrag) (hfr : BodyFrame nps C.rets (tysOf L)) :
    NS (execItems G F n nps ph d.toR l) :=
  itemsNS G F n nps ph d.toR l hf (ItemsD.toR_opsOK d) hfr


/-! ## The function level: internal calls without modifiers -/

/-- Reading the local below `ys` at its type is never `stuck`. -/
theorem Locals.getAt_ok {D : Layout} {τ : STy} {rest : RCtx} : (ys : RCtx) → (l : Locals D (ys ++ τ :: rest)) →
    NotStuckR (l.getAt ys.length τ)
  | [], .cons _ _ => by
    intro w h
    simp only [List.length_nil, Locals.getAt, dif_pos rfl] at h
    cases h
  | _ :: ys, .cons _ r => Locals.getAt_ok ys r

theorem Locals.getAt_ok' {D : Layout} {τ : STy} {rest Γ : RCtx} (ys : RCtx) (hΓ : Γ = ys ++ τ :: rest)
    (l : Locals D Γ) : NotStuckR (l.getAt ys.length τ) := by
  subst hΓ
  exact Locals.getAt_ok ys l

theorem Locals.restore_ok' {D : Layout} {Γ Γ' : RCtx} (ys : RCtx) (hΓ : Γ' = ys ++ Γ) (l : Locals D Γ') :
    NotStuckR (l.restore Γ) := by
  subst hΓ
  exact Locals.restore_ok ys l

/-- **Reading the return slots** of a frame is never `stuck`. -/
theorem retVals_ok {D : Layout} {Γ : RCtx} (l : Locals D Γ) :
    (rs : List STy) → {ps : RCtx} → Γ = rs.reverse ++ ps → NotStuckR (retVals l 0 rs)
  | [], _, _ => NotStuckR.pure _
  | r :: rs, ps, hΓ => by
    have hΓ' : Γ = rs.reverse ++ r :: ps := by
      rw [hΓ, List.reverse_cons, List.append_assoc, List.singleton_append]
    have h1 := Locals.getAt_ok' rs.reverse hΓ' l
    rw [List.length_reverse] at h1
    simp only [retVals, Nat.zero_add]
    exact NotStuckR.bind h1 fun _ => NotStuckR.bind (retVals_ok l rs hΓ') fun _ => NotStuckR.pure _

/-- **Zeroing return slots** of types with a default is never `stuck`. -/
theorem zeroVals_ns {Γ : RCtx} (n : Nat) : (τs : List STy) → (∀ τ ∈ τs, (Val.default E.layout τ).isSome = true) →
    NS (zeroVals (E := E) (Γ := Γ) n τs)
  | [], _ => NS.pure' _
  | τ :: τs, h => by
    simp only [zeroVals]
    exact NS.bind (zeroVal_ns n (h τ (by simp only [List.mem_cons, true_or]))) fun _ =>
      NS.bind (zeroVals_ns n τs fun σ hσ => h σ (by simp only [List.mem_cons, hσ, or_true])) fun _ => NS.pure' _

/-- **A body without modifiers** of the statement fragment, run in its
frame, is never `stuck`: no `break` or `continue` escapes it
(`itemsNSP`), and its scope closes. -/
theorem runMods_nil_ns (G : Glob E) (F : Fr) (n : Nat) (b : RBody E) (l : Locals E.layout b.locals)
    (hf : b.items.ValFrag) (ho : b.items.OpsOK) (hfr : BodyFrame b.ps.length b.rs b.locals) :
    NS (runMods G F n b [] l) := by
  cases n with
  | zero => rw [runMods.eq_1]; exact NS.halt' fun _ e => by cases e
  | succ n =>
    simp only [runMods]
    obtain ⟨ys, hys⟩ := RItems.ext b.items
    refine NSP.ns (NSP.bind (R := fun _ => True) (itemsNSP G F n b.ps.length none b.items l hf ho hfr) fun o ho' => ?_)
    cases o with
    | normal l' => exact NSP.of_ns (NS.lift' (Locals.restore_ok' ys hys l'))
    | ret l' => exact NSP.pure' trivial
    | brk _ => exact nomatch ho'
    | cont _ => exact nomatch ho'

/-- **An internal call** to a function whose body (found by virtual
dispatch) has no modifiers, is in the statement fragment and has the
frame the call builds (its parameters and returns are the call's, return
types with defaults), is never `stuck`. -/
theorem callInternal_ns (G : Glob E) (F : Fr) (n : Nat) (d : Decl) {ps : List STy} (vs : Vals E.layout ps)
    (rs : List STy) (b : RBody E) (hb : G.prog.body (G.dispatchFn F.contract d) = some b)
    (hloc : rs.reverseAux (ps.reverseAux []) = b.locals) (hrs : b.rs = rs) (hps : b.ps.length = ps.length)
    (hmods : b.mods = []) (hz : ∀ τ ∈ rs, (Val.default E.layout τ).isSome = true)
    (hf : b.items.ValFrag) (ho : b.items.OpsOK) :
    NS (callInternal G F n d vs rs) := by
  have hl : b.locals = rs.reverse ++ ps.reverse := by
    rw [← hloc, List.reverseAux_eq, List.reverseAux_eq, List.append_nil]
  cases n with
  | zero => rw [callInternal.eq_1]; exact NS.halt' fun _ e => by cases e
  | succ n =>
    simp only [callInternal, hb]
    refine NS.bind (zeroVals_ns n rs hz) fun rv => ?_
    rw [dif_pos hloc, hmods]
    refine NS.bind (runMods_nil_ns G _ n b _ hf ho ⟨[], ps.reverse, ?_, ?_⟩) fun l' =>
      NS.bind (NS.lift' (retVals_ok l' rs (hl.trans rfl))) fun _ => NS.pure' _
    · rw [hl, hrs, List.nil_append]
    · rw [List.length_reverse, hps]


/-! ## Elaborated bodies are in their frame -/

/-- A type name has one type. -/
theorem Syn.tys_typeName_length {E : Env} {scope : Option String} {loc : DataLoc} (t : Syn .typeName)
    (a : List STy) (h : t.tys E scope loc = Option.some a) : a.length = 1 := by
  cases t with
  | elem e => simp only [Syn.tys, Option.some.injEq] at h; subst h; rfl
  | userType p =>
    simp only [Syn.tys, Option.map_eq_some_iff] at h
    obtain ⟨_, _, rfl⟩ := h; rfl
  | array t len =>
    simp only [Syn.tys] at h
    split at h
    · simp only [Option.some.injEq] at h; subst h; rfl
    · cases h
  | mapping k kn v vn =>
    simp only [Syn.tys] at h
    split at h
    · split at h
      · simp only [Option.some.injEq] at h; subst h; rfl
      · cases h
    · cases h
  | fnType ps vis m rs =>
    simp only [Syn.tys] at h
    split at h
    · simp only [Option.some.injEq] at h; subst h; rfl
    · cases h


/-- A parameter list has one type per name. -/
theorem Syn.tys_params_length {E : Env} {scope : Option String} {loc : DataLoc} :
    (ps : Syn (.list .param)) → (a : List STy) → ps.tys E scope loc = Option.some a →
      a.length = ps.paramNames.length
  | .nil, a, h => by simp only [Syn.tys, Option.some.injEq] at h; subst h; rfl
  | .cons (.param t l n) xs, a, h => by
    simp only [Syn.tys] at h
    split at h
    · rename_i a1 b1 h1 h2
      simp only [Option.some.injEq] at h
      subst h
      rw [List.length_append, Syn.tys_typeName_length t a1 h1, Syn.tys_params_length xs b1 h2]
      simp only [Syn.paramNames, List.length_append, List.length_singleton]
    · cases h


/-- A frame has one type per parameter and return name. -/
theorem Frame.mk?_lengths {E : Env} {scope : Option String} {ps rs : Syn (.list .param)}
    {body : Syn (.list (.item .body))} {mv im : Bool} {f : Frame} (h : Frame.mk? E scope ps rs body mv im = some f) :
    f.names.length = f.ps.length ∧ f.rnames.length = f.rs.length := by
  unfold Frame.mk? at h
  split at h
  · rename_i a r ha hr
    simp only [Option.some.injEq] at h
    subst h
    exact ⟨(Syn.tys_params_length ps a ha).symm, (Syn.tys_params_length rs r hr).symm⟩
  · cases h

/-- **A body's frame**: one type per parameter and return name. -/
theorem Decl.frame?_lengths {E : Env} {d : Decl} {f : Frame} (h : d.frame? E = some f) :
    f.names.length = f.ps.length ∧ f.rnames.length = f.rs.length := by
  obtain ⟨k, name, scope, top, node⟩ := d
  cases k <;> cases node
  case modifier.modifier _ ps0 _ _ b0 =>
    (cases b0 <;> try (rename_i blk; cases blk)) <;> (try cases ps0) <;>
      first | exact Frame.mk?_lengths h | (cases h <;> exact ⟨rfl, rfl⟩)
  case fallback.fallback sig _ _ _ _ _ b0 =>
    (cases b0 <;> try (rename_i blk; cases blk)) <;> (try cases sig) <;>
      first | exact Frame.mk?_lengths h | (cases h <;> exact ⟨rfl, rfl⟩)
  all_goals (try (first | exact Frame.mk?_lengths h | cases h))
  all_goals (rename_i b0; cases b0 <;> (try (first | exact Frame.mk?_lengths h | cases h)))
  all_goals (rename_i b1; cases b1 <;> (try (first | exact Frame.mk?_lengths h | cases h)))
  all_goals exact ⟨rfl, rfl⟩

/-- **A frame's locals are its returns over its parameters**, last
innermost, as `callInternal` builds them. -/
theorem Frame.tysOf_locals {f : Frame} (hp : f.names.length = f.ps.length) (hr : f.rnames.length = f.rs.length) :
    tysOf f.locals = f.rs.reverse ++ f.ps.reverse := by
  have hl : (f.names ++ f.rnames).length = (f.ps ++ f.rs).length := by
    simp only [List.length_append, hp, hr]
  simp only [tysOf, Frame.locals, List.map_reverse, List.map_map]
  have : List.map (Prod.snd ∘ fun (x : Option String × STy) => (x.1.getD "", x.2)) ((f.names ++ f.rnames).zip (f.ps ++ f.rs))
      = f.ps ++ f.rs := by
    rw [show (Prod.snd ∘ fun (x : Option String × STy) => (x.1.getD "", x.2)) = Prod.snd from rfl]
    exact List.map_snd_zip (Nat.le_of_eq hl.symm)
  rw [this, List.reverse_append]


/-- **A function's frame has its signature's types.** -/
theorem Decl.frame?_fnSig {E : Env} {d : Decl} {ps rs : List STy} {f : Frame} (hs : d.fnSig E = some (ps, rs))
    (hf : d.frame? E = some f) : f.ps = ps ∧ f.rs = rs := by
  obtain ⟨k, name, scope, top, node⟩ := d
  cases k <;> cases node <;> (try cases hs)
  case function.function _ ps0 _ _ _ _ _ rs0 b0 =>
    cases b0 with
    | none => cases hf
    | some blk =>
      cases blk with
      | block b =>
        change (match ps0.tys E scope .memory, rs0.tys E scope .memory with
          | Option.some a, Option.some r => Option.some (a, r)
          | _, _ => Option.none) = some (ps, rs) at hs
        change Frame.mk? E scope ps0 rs0 b _ false = some f at hf
        unfold Frame.mk? at hf
        cases ha : ps0.tys E scope .memory <;> cases hr : rs0.tys E scope .memory <;>
          simp only [ha, hr, reduceCtorEq, Option.some.injEq, Prod.mk.injEq] at hs hf
        subst hf
        exact ⟨hs.1, hs.2⟩

/-- **An elaborated body is in its frame**: its locals are its returns over
its parameters, last innermost, exactly the frame `callInternal` builds. -/
theorem Elaborated.body_locals (el : Elaborated) {d : Decl} {b : RBody el.res.env}
    (hd : d ∈ el.res.unit.decls) (hb : el.prog.body d = some b) : b.locals = b.rs.reverse ++ b.ps.reverse := by
  obtain ⟨f, L', hf, D, hps, hrs, _, hl, _, _⟩ := el.bodies_typed d hd b hb
  obtain ⟨h1, h2⟩ := Decl.frame?_lengths hf
  rw [hl, Frame.tysOf_locals h1 h2, hps, hrs]

/-- **Internal calls in elaborated programs**: the frame hypotheses of
`callInternal_ns` (`hloc`, `hps` as a length) reduce to the body dispatch
finds having the call's parameter and return types (`hps`, `hrs`: dispatch
coherence), given that the program is the elaborated one (`hG`) and the
dispatched declaration is one of the unit's (`hdec`); `hmods`, `hz`, `hf`
and `ho` are `callInternal_ns`'s, kept. -/
theorem Elaborated.callInternal_ns (el : Elaborated) (G : Glob el.res.env) (hG : G.prog = el.prog) (F : Fr)
    (n : Nat) (d : Decl) {ps : List STy} (vs : Vals el.res.env.layout ps) (rs : List STy) (b : RBody el.res.env)
    (hdec : G.dispatchFn F.contract d ∈ el.res.unit.decls) (hb : G.prog.body (G.dispatchFn F.contract d) = some b)
    (hps : b.ps = ps) (hrs : b.rs = rs) (hmods : b.mods = [])
    (hz : ∀ τ ∈ rs, (Val.default el.res.env.layout τ).isSome = true)
    (hf : b.items.ValFrag) (ho : b.items.OpsOK) : NS (callInternal G F n d vs rs) := by
  have hb' : el.prog.body (G.dispatchFn F.contract d) = some b := by rw [← hG]; exact hb
  have hloc : rs.reverseAux (ps.reverseAux []) = b.locals := by
    rw [Elaborated.body_locals el hdec hb', hps, hrs, List.reverseAux_eq, List.reverseAux_eq, List.append_nil]
  exact Solidity.Source.callInternal_ns G F n d vs rs b hb hloc hrs (by rw [hps]) hmods hz hf ho


/-- **An elaborated body has its declaration's signature.** -/
theorem Elaborated.body_sig (el : Elaborated) {d : Decl} {b : RBody el.res.env} {ps rs : List STy}
    (hd : d ∈ el.res.unit.decls) (hb : el.prog.body d = some b) (hs : d.fnSig el.res.env = some (ps, rs)) :
    b.ps = ps ∧ b.rs = rs := by
  obtain ⟨f, L', hf, D, hps, hrs, _⟩ := el.bodies_typed d hd b hb
  obtain ⟨h1, h2⟩ := Decl.frame?_fnSig hs hf
  exact ⟨hps.trans h1, hrs.trans h2⟩

/-- **Dispatch keeps the parameter types**: the declaration virtual
dispatch finds for `d` has `d`'s parameter types (`Env.fnIn` selects
overrides by them; every fallback is `d` itself). -/
theorem Glob.dispatchFn_params (G : Glob E) (c : String) (d : Decl) {ps rs ps' rs' : List STy}
    (hd : d.fnSig E = some (ps, rs)) (h' : (G.dispatchFn c d).fnSig E = some (ps', rs')) : ps' = ps := by
  unfold Glob.dispatchFn at h'
  rw [hd] at h'
  simp only at h'
  split at h'
  · cases hf : ((E.linearize c).getD [c]).findSome? (fun s => (E.fnIn s d.name ps).find?
        fun d' => (G.prog.body d').isSome) with
    | none =>
      rw [hf, Option.getD_none, hd] at h'
      simp only [Option.some.injEq, Prod.mk.injEq] at h'
      exact h'.1.symm
    | some d' =>
      rw [hf, Option.getD_some] at h'
      obtain ⟨s, _, hs⟩ := List.exists_of_findSome?_eq_some hf
      have hm := List.mem_of_find?_eq_some hs
      simp only [Env.fnIn, List.mem_filter, Bool.and_eq_true, beq_iff_eq, h'] at hm
      exact (STy.eq_of_sameList ps ps' hm.2.2).symm
  · rw [hd] at h'
    simp only [Option.some.injEq, Prod.mk.injEq] at h'
    exact h'.1.symm

/-- **Internal calls in elaborated programs, by signature**: an internal
call is never `stuck` when the declaration virtual dispatch finds is one
of the unit's with the call's signature and a body without modifiers in
the statement fragment (return types with defaults). For a call whose
dispatch is the called declaration itself, the signature is the call
node's own (`RExpr.call`'s premise). -/
theorem Elaborated.callInternal_sig_ns (el : Elaborated) (G : Glob el.res.env) (hG : G.prog = el.prog) (F : Fr)
    (n : Nat) (d : Decl) {ps : List STy} (vs : Vals el.res.env.layout ps) (rs : List STy) (b : RBody el.res.env)
    (hdec : G.dispatchFn F.contract d ∈ el.res.unit.decls) (hb : G.prog.body (G.dispatchFn F.contract d) = some b)
    (hsig : (G.dispatchFn F.contract d).fnSig el.res.env = some (ps, rs)) (hmods : b.mods = [])
    (hz : ∀ τ ∈ rs, (Val.default el.res.env.layout τ).isSome = true)
    (hf : b.items.ValFrag) (ho : b.items.OpsOK) : NS (callInternal G F n d vs rs) := by
  have hb' : el.prog.body (G.dispatchFn F.contract d) = some b := by rw [← hG]; exact hb
  obtain ⟨hps, hrs⟩ := Elaborated.body_sig el hdec hb' hsig
  exact Elaborated.callInternal_ns el G hG F n d vs rs b hdec hb hps hrs hmods hz hf ho


/-- **Internal calls in elaborated programs, by the call node**: for a call
`d(args)` with `d`'s signature `(ps, rs)` (`RExpr.call`'s premise), only the
return types of the declaration virtual dispatch finds remain to agree;
its parameter types agree by construction (`Glob.dispatchFn_params`). -/
theorem Elaborated.callInternal_call_ns (el : Elaborated) (G : Glob el.res.env) (hG : G.prog = el.prog) (F : Fr)
    (n : Nat) (d : Decl) {ps : List STy} (vs : Vals el.res.env.layout ps) (rs : List STy) (b : RBody el.res.env)
    (hd : d.fnSig el.res.env = some (ps, rs))
    (hdec : G.dispatchFn F.contract d ∈ el.res.unit.decls) (hb : G.prog.body (G.dispatchFn F.contract d) = some b)
    (hret : ∃ ps', (G.dispatchFn F.contract d).fnSig el.res.env = some (ps', rs)) (hmods : b.mods = [])
    (hz : ∀ τ ∈ rs, (Val.default el.res.env.layout τ).isSome = true)
    (hf : b.items.ValFrag) (ho : b.items.OpsOK) : NS (callInternal G F n d vs rs) := by
  obtain ⟨ps', h'⟩ := hret
  have e := Glob.dispatchFn_params G F.contract d hd h'
  subst e
  exact Elaborated.callInternal_sig_ns el G hG F n d vs rs b hdec hb h' hmods hz hf ho

end Solidity.Source
