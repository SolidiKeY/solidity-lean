import Solidity.Source.Eval
import Solidity.Source.ValueProgress
import Solidity.Source.Hoare

/-!
# Progress of the interpreter on value expressions (lane V04b)

`NS m`: the computation `m` never halts `stuck`, from any state. For the
**value fragment** of resolved expressions (`RExpr.ValFrag`: constants,
locals of value type, `this`, unary and binary operators, comparisons,
shifts and powers, conditionals, and implicit conversions between value
types or from constants) evaluation is never `stuck` at any horizon,
provided the expression is in the operations' domains (`RExpr.OpsOK`),
which every elaborated expression is (`Typed.toR_opsOK`):
`evalE_valFrag_ns`.

This is the expression core of gap-relative progress: the value-layer
lemmas of `Solidity/Source/ValueProgress.lean` lifted through the
interpreter's binds, pipelines (`evalPair`) and conversions (`convRV`).
-/

namespace Solidity.Source

open EM

variable {E : Env}

/-- **Never `stuck`**: from every state, `m` succeeds or halts otherwise. -/
def NS {Γ : RCtx} {α : Type} (m : EM E Γ α) : Prop := ∀ x w, (m.run x).1 ≠ .error (.stuck w)

namespace NS

variable {Γ : RCtx} {α β : Type}

theorem pure' (a : α) : NS (pure a : EM E Γ α) := fun _ _ h => by cases h

theorem halt' {h : Halt} (hh : ∀ w, h ≠ .stuck w) : NS (halt h : EM E Γ α) := fun _ w e => by
  cases e; exact hh w rfl

theorem bind {m : EM E Γ α} {k : α → EM E Γ β} (hm : NS m) (hk : ∀ a, NS (k a)) : NS (m >>= k) := by
  intro x w h
  rw [Hoare.run_bind] at h
  rcases hr : m.run x with ⟨r, y⟩
  rw [hr] at h
  cases r with
  | ok a => exact hk a y w h
  | error e =>
    have he : e = .stuck w := by cases h; rfl
    have := hm x w
    rw [hr, he] at this
    exact this rfl

theorem lift' {r : R α} (h : NotStuckR r) : NS (lift r : EM E Γ α) := by
  intro x w e
  cases r with
  | ok a => cases e
  | error e' => exact h w (by cases e; rfl)

theorem locals' : NS (locals : EM E Γ (Locals E.layout Γ)) := fun _ _ h => by cases h

end NS

/-- A run-time value of a value type is plain: `getV` is never `stuck`. -/
theorem getV_ns {Γ : RCtx} {τ : STy} (hτ : τ.isValue = true) (v : RVal E.layout τ) :
    NS (getV (Γ := Γ) v) := by
  refine NS.lift' ?_
  cases v with
  | val x => exact NotStuckR.pure _
  | const _ => cases hτ
  | strLit _ => cases hτ
  | hex _ _ => cases hτ
  | tuple _ => cases hτ

/-! ## Conversions -/

/-- An implicit conversion of a hexadecimal constant to anything but
`bytesN` is never `stuck` (as a rational constant's). -/
theorem constVal_hex_ok (B : DeclName → DeclName → Bool) {q : Q} {k : Nat} {τ : STy}
    (h : (STy.hexConst q k).implicit B τ = true) (hτ : ∀ m hm, τ ≠ .fixedBytes m hm) :
    NotStuckR (constVal (D := E.layout) q τ) := by
  cases τ <;> (try (cases h <;> done))
  · rename_i t
    exact constVal_ok B (τ := .int t) (by
      rw [show STy.implicit B (.hexConst q k) (.int t) = decide (q.FitsInt t) from rfl] at h
      exact h)
  · rename_i m hm
    exact absurd rfl (hτ m hm)
  · rename_i f
    exact constVal_ok B (τ := .fixed f) (by
      rw [show STy.implicit B (.hexConst q k) (.fixed f) = (q.toFixed? f).isSome from rfl] at h
      exact h)

/-- A type of the fragment's conversions has no location. -/
theorem loc_of_frag {σ : STy} (hσ : σ.isValue = true ∨ (∃ q, σ = .rational q) ∨ (∃ q k, σ = .hexConst q k)) :
    σ.loc? = none := by
  rcases hσ with hσ | ⟨q, rfl⟩ | ⟨q, k, rfl⟩
  · cases σ <;> first | rfl | cases hσ
  · rfl
  · rfl

/-- **`convRV` is never `stuck` on the conversions of the value fragment**:
an implicit conversion (or the identity) from a value type or a constant
to a value type. -/
theorem convRV_ns {Γ : RCtx} (F : Fr) (n : Nat) {σ τ : STy} (hc : Conv E.isBase σ τ)
    (hσ : σ.isValue = true ∨ (∃ q, σ = .rational q) ∨ (∃ q k, σ = .hexConst q k)) (v : RVal E.layout σ) :
    NS (convRV (Γ := Γ) F n τ v) := by
  have hl := loc_of_frag hσ
  unfold convRV
  split
  · -- a constant
    dsimp only
    split
    · exact NS.pure' _
    · rename_i he
      exact NS.bind (NS.pure' _) fun _ => NS.bind (NS.lift' (constVal_ok E.isBase (hc.resolve_right he)))
        fun _ => NS.pure' _
  · -- a hexadecimal constant to `bytesN`
    dsimp only
    split
    · exact NS.pure' _
    · exact NS.bind (NS.pure' _) fun _ => NS.pure' _
  · -- a hexadecimal constant to another type
    rename_i hτ
    dsimp only
    split
    · exact NS.pure' _
    · rename_i he
      exact NS.bind (NS.pure' _) fun _ => NS.bind (NS.lift' (constVal_hex_ok E.isBase (hc.resolve_right he)
        (fun m hm e => hτ m hm e))) fun _ => NS.pure' _
  all_goals first
    | (exfalso; rcases hσ with h | ⟨_, h⟩ | ⟨_, _, h⟩ <;> cases h)
    | (rename_i h; rw [hl] at h; cases h)
    | skip
  · -- a plain value
    rename_i x hr hh _ _ _ _ _ _
    dsimp only
    split
    · exact NS.pure' _
    · rename_i he
      have hv : σ.isValue = true := by
        rcases hσ with hσ | ⟨q, rfl⟩ | ⟨q, k, rfl⟩
        · exact hσ
        · exact (hr q _ rfl HEq.rfl).elim
        · exact (hh q k _ rfl HEq.rfl).elim
      exact NS.bind (NS.pure' _) fun _ =>
        NS.bind (NS.lift' (convVal_ok E.isBase hv (.inl (hc.resolve_right he)) x)) fun _ => NS.pure' _
  · -- not a plain value: impossible for the fragment's types
    rename_i hr hh _ _ hval _ _ _ _
    exfalso
    rcases hσ with hσ | ⟨q, rfl⟩ | ⟨q, k, rfl⟩
    · cases v with
      | val x => exact hval x rfl
      | const _ => cases hσ
      | strLit _ => cases hσ
      | hex _ _ => cases hσ
      | tuple _ => cases hσ
    · exact hr q v rfl HEq.rfl
    · exact hh q k v rfl HEq.rfl

/-! ## The value fragment -/

/-- **The value fragment** of resolved expressions: no state, memory,
calls or references; every intermediate value of a value type, every
conversion from a value type or a constant. -/
def RExpr.ValFrag {Γ : RCtx} : {τ : STy} → RExpr E Γ τ → Prop
  | _, .const _ | _, .bytesLit _ _ | _, .addressLit _ | _, .bool _ | _, .this _ | _, .compareConst _ _ _ => True
  | τ, .local _ => τ.isValue = true
  | τ, .unary _ a => a.ValFrag ∧ τ.isValue = true
  | τ, .binary _ a b => a.ValFrag ∧ b.ValFrag ∧ τ.isValue = true
  | _, .compare (τ := τ) _ a b => a.ValFrag ∧ b.ValFrag ∧ τ.isValue = true
  | τ, .shiftLike _ a b _ => a.ValFrag ∧ b.ValFrag ∧ τ.isValue = true
  | _, .cond c a b => c.ValFrag ∧ a.ValFrag ∧ b.ValFrag
  | τ, .conv (σ := σ) a _ => a.ValFrag ∧ τ.isValue = true ∧
      (σ.isValue = true ∨ (∃ q, σ = .rational q) ∨ (∃ q k, σ = .hexConst q k))
  | _, _ => False

theorem cmpConst_ok {op : BinOp} (hop : (BinKind.order.admits op || BinKind.eq.admits op) = true) (a b : Q) :
    NotStuckR (cmpConst op a b) := by
  intro w h
  cases op <;> (try exact absurd hop (by decide)) <;> cases h

/-- A logical operator's domain is `bool`. -/
theorem fitsAt_logic {op : BinOp} {τ : STy} (h : op.FitsAt τ) (hl : (op = .and || op = .or) = true) :
    τ = .bool := by
  rcases h with ⟨hop, _⟩ | ⟨hop, _⟩ | ⟨_, hτ⟩
  · cases op <;> first | exact absurd hop (by decide) | exact absurd hl (by decide)
  · cases op <;> first | exact absurd hop (by decide) | exact absurd hl (by decide)
  · exact hτ

section
variable (G : Glob E) (F : Fr)

/-- **Progress on the value fragment**: evaluating an expression of the
value fragment that is in the operations' domains is never `stuck`, at any
horizon (it may time out). -/
theorem evalE_valFrag_ns : ∀ (n : Nat) {Γ : RCtx} {τ : STy} (e : RExpr E Γ τ), e.ValFrag → e.OpsOK →
    NS (evalE G F n e)
  | 0, _, _, _, _, _ => by
    rw [evalE.eq_1]; exact NS.halt' fun _ h => by cases h
  | n + 1, Γ, τ, e, hf, ho => by
    have ihP : ∀ {σ ρ : STy} (a : RExpr E Γ σ) (b : RExpr E Γ ρ), a.ValFrag → a.OpsOK → b.ValFrag → b.OpsOK →
        NS (evalPair G F n a b) := by
      intro σ ρ a b ha ha' hb hb'
      cases n with
      | zero => rw [evalPair.eq_1]; exact NS.halt' fun _ h => by cases h
      | succ m =>
        simp only [evalPair]
        split
        · exact NS.bind (evalE_valFrag_ns m b hb hb') fun _ =>
            NS.bind (evalE_valFrag_ns m a ha ha') fun _ => NS.pure' _
        · exact NS.bind (evalE_valFrag_ns m a ha ha') fun _ =>
            NS.bind (evalE_valFrag_ns m b hb hb') fun _ => NS.pure' _
    cases e with
    | const _ => exact NS.pure' _
    | bytesLit _ _ => exact NS.pure' _
    | addressLit _ => exact NS.pure' _
    | bool _ => exact NS.pure' _
    | this _ => exact NS.pure' _
    | «local» i =>
      simp only [evalE]
      exact NS.bind NS.locals' fun _ => NS.pure' _
    | unary op a =>
      simp only [evalE]
      exact NS.bind (evalE_valFrag_ns n a hf.1 ho.2) fun v => NS.bind (getV_ns hf.2 v) fun x =>
        NS.bind (NS.lift' (unaryVal_ok _ ho.1 x)) fun _ => NS.pure' _
    | binary op a b =>
      simp only [evalE]
      split
      · rename_i hl
        have hb : τ = .bool := fitsAt_logic ho.1 hl
        subst hb
        refine NS.bind (evalE_valFrag_ns n a hf.1 ho.2.1) fun v => NS.bind (getV_ns rfl v) fun x => ?_
        obtain ⟨c, rfl⟩ := Val.eq_bool x
        show NS (match some (if c then (1 : Int) else 0) with
          | some kx =>
            if (decide (op = BinOp.and) && decide (kx = 0) || decide (op = BinOp.or) && decide (kx = 1)) = true then
              pure (RVal.val (Val.bool c))
            else do
              let __do_lift ← evalE G F n b
              let __do_lift ← getV __do_lift
              pure (RVal.val __do_lift)
          | none => halt (Halt.stuck "logical operand"))
        dsimp only
        split <;> split <;> first
          | exact NS.pure' _
          | exact NS.bind (evalE_valFrag_ns n b hf.2.1 ho.2.2) fun w => NS.bind (getV_ns rfl w) fun _ =>
              NS.pure' _
      · exact NS.bind (ihP a b hf.1 ho.2.1 hf.2.1 ho.2.2) fun p =>
          NS.bind (getV_ns hf.2.2 p.1) fun x => NS.bind (getV_ns hf.2.2 p.2) fun y =>
            NS.bind (NS.lift' (binVal_ok _ ho.1 x y)) fun _ => NS.pure' _
    | compare op a b =>
      simp only [evalE]
      exact NS.bind (ihP a b hf.1 ho.2.2.1 hf.2.1 ho.2.2.2) fun p =>
        NS.bind (getV_ns hf.2.2 p.1) fun x => NS.bind (getV_ns hf.2.2 p.2) fun y =>
          NS.bind (NS.lift' (cmpVal_ok ho.1 ho.2.1 x y)) fun _ => NS.pure' _
    | compareConst op qa qb =>
      simp only [evalE]
      exact NS.bind (NS.lift' (cmpConst_ok ho qa qb)) fun _ => NS.pure' _
    | shiftLike op a b h =>
      simp only [evalE]
      exact NS.bind (ihP a b hf.1 ho.2.1 hf.2.1 ho.2.2) fun p =>
        NS.bind (NS.lift' (amount_ok h p.2)) fun k => NS.bind (getV_ns hf.2.2 p.1) fun x =>
          NS.bind (NS.lift' (shiftVal_ok _ k ho.1 x)) fun _ => NS.pure' _
    | cond c a b =>
      simp only [evalE]
      refine NS.bind (evalE_valFrag_ns n c hf.1 ho.1) fun v => NS.bind (getV_ns rfl v) fun x => ?_
      split
      · exact evalE_valFrag_ns n a hf.2.1 ho.2.1
      · exact evalE_valFrag_ns n b hf.2.2 ho.2.2
    | conv a h =>
      simp only [evalE]
      exact NS.bind (evalE_valFrag_ns n a hf.1 ho) fun v => convRV_ns F n h hf.2.2 v
    | _ => exact hf.elim

end

end Solidity.Source
