import Solidity.Source.ExprProgress

/-!
# Progress of the interpreter on value statements (lane V04b)

`NSP m Q`: from every state, `m` returns a result satisfying `Q` or halts
other than `stuck`. For the **statement value fragment**
(`RStmt.ValFrag`: expression statements, declarations of types with a
default, blocks, `if`, loops, `break`, `continue`, over expressions of the
value fragment) execution is never `stuck`, at any horizon, in any
modifier context, provided its expressions are in the operations' domains
(`RStmt.OpsOK`, which every elaborated statement satisfies,
`StmtD.toR_opsOK`): `stmtNS`.

The scope facts it needs are structural: a statement's output context
extends its input (`RStmt.ext`, `RItems.ext`), so ending a scope
(`Locals.restore`, `Out.close`, `Out.up`) is never `stuck`; and a `for`
loop's iterations end normally or by `return` (`forIter`'s
postcondition).
-/

namespace Solidity.Source

open EM

variable {E : Env}

/-! ## Never `stuck`, with a postcondition -/

/-- From every state, `m` returns a result satisfying `Q` or halts other
than `stuck`. -/
def NSP {Γ : RCtx} {α : Type} (m : EM E Γ α) (Q : α → Prop) : Prop :=
  ∀ x, match (m.run x).1 with
    | .ok a => Q a
    | .error h => NotStuck h

namespace NSP

variable {Γ : RCtx} {α β : Type}

theorem pure' {a : α} {Q : α → Prop} (h : Q a) : NSP (pure a : EM E Γ α) Q := fun _ => h

theorem halt' {h : Halt} {Q : α → Prop} (hh : NotStuck h) : NSP (halt h : EM E Γ α) Q := fun _ => hh

theorem bind {m : EM E Γ α} {k : α → EM E Γ β} {Q : α → Prop} {R : β → Prop} (hm : NSP m Q)
    (hk : ∀ a, Q a → NSP (k a) R) : NSP (m >>= k) R := by
  intro x
  rw [Hoare.run_bind]
  have h1 := hm x
  rcases hr : m.run x with ⟨r, y⟩
  rw [hr] at h1
  cases r with
  | ok a => exact hk a h1 y
  | error e => exact h1

theorem lift' {r : R α} {Q : α → Prop}
    (h : match r with | .ok a => Q a | .error e => NotStuck e) : NSP (lift r : EM E Γ α) Q := by
  intro x
  cases r with
  | ok a => exact h
  | error e => exact h

theorem of_ns {m : EM E Γ α} (h : NS m) : NSP m (fun _ => True) := by
  intro x
  rcases hr : (m.run x).1 with e | a
  · cases e with
    | stuck w => exact (h x w hr).elim
    | _ => trivial
  · trivial

theorem ns {m : EM E Γ α} {Q : α → Prop} (h : NSP m Q) : NS m := by
  intro x w e
  have := h x
  rw [e] at this
  exact this

theorem weaken {m : EM E Γ α} {Q Q' : α → Prop} (h : NSP m Q) (hq : ∀ a, Q a → Q' a) : NSP m Q' := by
  intro x
  have := h x
  rcases hr : (m.run x).1 with e | a
  · rw [hr] at this; exact this
  · rw [hr] at this; exact hq a this

/-- A computation over other locals. -/
theorem sub' {Γ' : RCtx} {l' : Locals E.layout Γ'} {m : EM E Γ' α} {Q : α × Locals E.layout Γ' → Prop}
    (h : NSP m fun a => ∀ l'', Q (a, l'')) : NSP (sub (Γ := Γ) l' m) Q := by
  intro ⟨l, s⟩
  have h1 := h (l', s)
  unfold EM.sub
  rcases hr : m.run (l', s) with ⟨r, ⟨l'', s'⟩⟩
  have hr' : m (l', s) = (r, (l'', s')) := hr
  rw [hr] at h1
  cases r with
  | ok a => simp only [ExceptT.run, ExceptT.mk, hr']; exact h1 l''
  | error e => simp only [ExceptT.run, ExceptT.mk, hr']; exact h1

end NSP

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
  | _, _, _, .skip | _, _, _, .brk | _, _, _, .cont => True
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

section
variable (G : Glob E)

/-- **The induction hypothesis**: at horizon `n`, statements, blocks and
`for` iterations of the fragment are never `stuck`; a simple statement
completes normally, `for` iterations normally or by `return`. -/
structure StmtNSAt (n : Nat) : Prop where
  execS : ∀ (F : Fr) (nps : Nat) (ph : Option (Ph E)) {R : List STy} {M : Bool} {k : SCtx} {Γ Γ' : RCtx}
    (s : RStmt E R M k Γ Γ') (l : Locals E.layout Γ), s.ValFrag → s.OpsOK →
    NSP (execS G F n nps ph s l) (fun o => s.Simple → ∃ l', o = .normal l')
  execItems : ∀ (F : Fr) (nps : Nat) (ph : Option (Ph E)) {R : List STy} {M : Bool} {k : SCtx} {Γ Γ' : RCtx}
    (b : RItems E R M k Γ Γ') (l : Locals E.layout Γ), b.ValFrag → b.OpsOK →
    NSP (execItems G F n nps ph b l) (fun _ => True)
  forIter : ∀ (F : Fr) (nps : Nat) (ph : Option (Ph E)) {R : List STy} {M u : Bool} {Γ₁ Γ₂ : RCtx}
    (c : ROptBool E Γ₁) (post : ROptExpr E Γ₁) (body : RStmt E R M ⟨true, u⟩ Γ₁ Γ₂) (l : Locals E.layout Γ₁),
    c.ValFrag → c.OpsOK → post.ValFrag → post.OpsOK → body.ValFrag → body.OpsOK →
    NSP (forIter G F n nps ph c post body l) (fun o => (∃ l', o = .normal l') ∨ (∃ l', o = .ret l'))

theorem stmtNSAt_zero : StmtNSAt G 0 where
  execS _ _ _ _ _ _ _ _ _ _ _ _ := by rw [execS.eq_1]; exact NSP.halt' trivial
  execItems _ _ _ _ _ _ _ _ _ _ _ _ := by rw [execItems.eq_1]; exact NSP.halt' trivial
  forIter _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ := by rw [forIter.eq_1]; exact NSP.halt' trivial

end

section
variable {G : Glob E} {n : Nat}

theorem execS_step (ih : StmtNSAt G n) (F : Fr) (nps : Nat) (ph : Option (Ph E)) {R : List STy} {M : Bool}
    {k : SCtx} {Γ Γ' : RCtx} (s : RStmt E R M k Γ Γ') (l : Locals E.layout Γ) (hf : s.ValFrag) (ho : s.OpsOK) :
    NSP (execS G F (n + 1) nps ph s l) (fun o => s.Simple → ∃ l', o = .normal l') := by
  have hE : ∀ {Γ τ} (e : RExpr E Γ τ), e.ValFrag → e.OpsOK → NSP (evalE G F n e) (fun _ => True) :=
    fun e hf ho => NSP.of_ns (evalE_valFrag_ns G F n e hf ho)
  have hsub : ∀ {Γ₀ τ} {l₀ : Locals E.layout Γ₀} (e : RExpr E Γ₀ τ), e.ValFrag → e.OpsOK →
      NSP (sub (Γ := []) l₀ (evalE G F n e)) (fun _ => True) :=
    fun e hf ho => NSP.sub' (NSP.weaken (hE e hf ho) fun _ _ _ => trivial)
  have hclose : ∀ {Γ₁} {t : RStmt E R M k Γ Γ₁} (l₁ : Locals E.layout Γ), t.ValFrag → t.OpsOK →
      NSP (do lift (← execS G F n nps ph t l₁).close) (fun (_ : Out E.layout Γ Γ) => True) := by
    intro Γ₁ t l₁ ht ho'
    obtain ⟨ys, rfl⟩ := RStmt.ext t
    exact NSP.bind (ih.execS F nps ph t l₁ ht ho') fun o _ => NSP.lift_ok (Out.close_ok ys o)
  cases s with
  | expr e =>
    simp only [execS]
    exact NSP.bind (hsub e hf ho) fun _ _ => NSP.pure' fun _ => ⟨_, rfl⟩
  | declVar τ =>
    simp only [execS]
    exact NSP.bind (NSP.sub' (Q := fun _ => True) (NSP.weaken (NSP.of_ns (zeroVal_ns n hf))
      fun _ _ _ => trivial)) fun _ _ =>
      NSP.pure' fun _ => ⟨_, rfl⟩
  | declInit e h =>
    simp only [execS]
    refine NSP.bind (NSP.sub' (Q := fun _ => True) (NSP.weaken (NSP.of_ns ?_) fun _ _ _ => trivial)) fun _ _ =>
      NSP.pure' fun _ => ⟨_, rfl⟩
    exact NS.bind (evalE_valFrag_ns G F n e hf.1 ho) fun v =>
      NS.bind (convRV_ns F n (.inl h) hf.2.2 v) fun w => getV_ns hf.2.1 w
  | block b =>
    simp only [execS]
    obtain ⟨ys, rfl⟩ := RItems.ext b
    exact NSP.bind (ih.execItems F nps ph b l hf ho) fun o _ =>
      NSP.weaken (NSP.lift_ok (Out.close_ok ys o)) fun _ _ h => h.elim
  | ifThen c t =>
    simp only [execS]
    refine NSP.bind (hsub c hf.1 ho.1) fun p _ => NSP.bind (NSP.of_ns (getV_ns rfl p.1)) fun x _ => ?_
    split
    · exact NSP.weaken (hclose p.2 hf.2 ho.2) fun _ _ h => h.elim
    · exact NSP.pure' fun h => h.elim
  | ifElse c t f =>
    simp only [execS]
    refine NSP.bind (hsub c hf.1 ho.1) fun p _ => NSP.bind (NSP.of_ns (getV_ns rfl p.1)) fun x _ => ?_
    split
    · exact NSP.weaken (hclose p.2 hf.2.1 ho.2.1) fun _ _ h => h.elim
    · exact NSP.weaken (hclose p.2 hf.2.2 ho.2.2) fun _ _ h => h.elim
  | whileLoop c body =>
    simp only [execS]
    obtain ⟨ys, rfl⟩ := RStmt.ext body
    refine NSP.bind (hsub c hf.1 ho.1) fun p _ => NSP.bind (NSP.of_ns (getV_ns rfl p.1)) fun x _ => ?_
    split
    · refine NSP.bind (ih.execS F nps ph body p.2 hf.2 ho.2) fun o _ => ?_
      cases o with
      | normal l2 =>
        exact NSP.bind (NSP.lift_ok (Locals.restore_ok ys l2)) fun l3 _ =>
          NSP.weaken (ih.execS F nps ph _ l3 hf ho) fun _ _ h => h.elim
      | cont l2 => exact NSP.weaken (ih.execS F nps ph _ l2 hf ho) fun _ _ h => h.elim
      | brk _ => exact NSP.pure' fun h => h.elim
      | ret _ => exact NSP.pure' fun h => h.elim
    · exact NSP.pure' fun h => h.elim
  | doWhile body c =>
    simp only [execS]
    obtain ⟨ys, rfl⟩ := RStmt.ext body
    have tail : ∀ l₂ : Locals E.layout Γ, NSP (do
        let __discr ← sub l₂ (evalE G F n c)
        let __do_lift ← getV __discr.fst
        match __do_lift with
          | Val.bool true => execS G F n nps ph (body.doWhile c) __discr.snd
          | _ => pure (Out.normal __discr.snd))
        (fun _ => True) := fun l₂ =>
      NSP.bind (hsub c hf.2 ho.2) fun p _ => NSP.bind (NSP.of_ns (getV_ns rfl p.1)) fun x _ => by
        split
        · exact NSP.weaken (ih.execS F nps ph _ p.2 hf ho) fun _ _ => trivial
        · exact NSP.pure' trivial
    refine NSP.bind (ih.execS F nps ph body l hf.1 ho.1) fun o _ => ?_
    cases o with
    | normal l2 =>
      refine NSP.bind (NSP.lift_ok (Locals.restore_ok ys l2)) fun l3 _ => ?_
      exact NSP.weaken (tail l3) fun _ _ h => h.elim
    | cont l2 =>
      refine NSP.bind (NSP.pure' (Q := fun _ => True) trivial) fun l3 _ => ?_
      exact NSP.weaken (tail l3) fun _ _ h => h.elim
    | brk _ => exact NSP.pure' fun h => h.elim
    | ret _ => exact NSP.pure' fun h => h.elim
  | forLoop init c post body =>
    simp only [execS]
    obtain ⟨ys, rfl⟩ := RStmt.ext init
    refine NSP.bind (ih.execS F nps ph init l hf.2.1 ho.1) fun o ho1 => ?_
    obtain ⟨l1, rfl⟩ := ho1 hf.1
    refine NSP.bind (ih.forIter F nps ph c post body l1 hf.2.2.1 ho.2.1 hf.2.2.2.1 ho.2.2.1 hf.2.2.2.2 ho.2.2.2)
      fun o2 h2 => ?_
    rcases h2 with ⟨l2, rfl⟩ | ⟨l2, rfl⟩
    · exact NSP.bind (NSP.lift_ok (Locals.restore_ok ys l2)) fun _ _ => NSP.pure' fun h => h.elim
    · exact NSP.bind (NSP.lift_ok (Locals.restore_ok ys l2)) fun _ _ => NSP.pure' fun h => h.elim
  | skip => exact NSP.pure' fun _ => ⟨_, rfl⟩
  | brk => exact NSP.pure' fun h => h.elim
  | cont => exact NSP.pure' fun h => h.elim
  | _ => exact hf.elim

end

end Solidity.Source
