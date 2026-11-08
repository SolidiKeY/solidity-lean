import Solidity.Lowering.Readonly.SourceKnownExpressionEffects
import Solidity.Lowering.Readonly.SourceKnownTryEffects

/-! Guard-parametric body and statement journal histories. Regression purpose:
the typed library try success and Error(string) catch continuations preserve
histories in both calldata modes. All original statements remain unchanged. -/
namespace Solidity.Lowering.Readonly.SourceHistory
open Solidity.Source
variable {E : Env}

theorem execItems_succ_known : ∀ {E : Solidity.Source.Env} (G : Solidity.Source.Glob E) (F : Solidity.Source.Fr) (n : Nat) (known : Bool) (_h : KnownAt G n) (nps : Nat) (ph : Option (Solidity.Source.Ph E)) {R : List Solidity.Source.STy} {M : Bool} {k : Solidity.Source.SCtx} {Γ Γ' : Solidity.Source.RCtx} (b : Solidity.Source.RItems E R M k Γ Γ') (l : Solidity.Source.Locals E.layout Γ), Solidity.Lowering.Readonly.SourceHistory.Effect F.static (Solidity.Source.execItems (calldataKnown := known) G F (n+1) nps ph b l) := by
  intro E G F n known h nps ph R M k Γ Γ' b l
  cases b
  case nil => exact Solidity.Lowering.Readonly.SourceHistory.Effect.pure F.static _
  case stmt =>
    unfold Solidity.Source.execItems
    apply Solidity.Lowering.Readonly.SourceHistory.Effect.bind
    · exact h.execS known F _ _ _ _
    · intro out
      cases out
      case normal =>
        exact Solidity.Lowering.Readonly.SourceHistory.Effect.bind _ _ _ (h.execItems known F _ _ _ _) (fun result => Solidity.Lowering.Readonly.SourceHistory.Effect.lift F.static _)
      all_goals exact Solidity.Lowering.Readonly.SourceHistory.Effect.pure F.static _
  case unchecked =>
    unfold Solidity.Source.execItems
    apply Solidity.Lowering.Readonly.SourceHistory.Effect.bind
    · exact h.execItems known {F with checked := false} _ _ _ _
    · intro out
      cases out
      case normal =>
        exact Solidity.Lowering.Readonly.SourceHistory.Effect.bind _ _ _ (Solidity.Lowering.Readonly.SourceHistory.Effect.lift F.static _) (fun restored => h.execItems known F _ _ _ restored)
      all_goals exact Solidity.Lowering.Readonly.SourceHistory.Effect.pure F.static _


theorem runMods_succ_known : ∀ {E : Solidity.Source.Env} (G : Solidity.Source.Glob E) (F : Solidity.Source.Fr) (n : Nat) (known : Bool) (_h : KnownAt G n) (b : Solidity.Source.RBody E) (mods : List (Solidity.Source.RModInv E b.locals)) (l : Solidity.Source.Locals E.layout b.locals), Solidity.Lowering.Readonly.SourceHistory.Effect F.static (Solidity.Source.runMods (calldataKnown := known) G F (n+1) b mods l) := by
  intro E G F n known h b mods l
  cases mods with
  | nil =>
    unfold Solidity.Source.runMods
    apply Solidity.Lowering.Readonly.SourceHistory.Effect.bind
    · exact h.execItems known F _ _ _ _
    · intro out
      cases out
      case normal => exact Solidity.Lowering.Readonly.SourceHistory.Effect.lift F.static _
      case ret => exact Solidity.Lowering.Readonly.SourceHistory.Effect.pure F.static _
      all_goals exact Solidity.Lowering.Readonly.SourceHistory.Effect.halt F.static _
  | cons modifier rest =>
    unfold Solidity.Source.runMods
    apply Solidity.Lowering.Readonly.SourceHistory.Effect.bind
    · apply Solidity.Lowering.Readonly.SourceHistory.Effect.sub
      exact h.evalConvArgs known F _
    · intro pair
      rcases pair with ⟨vs, updated⟩
      cases chosen : G.prog.body (G.dispatchMod F.contract modifier.modifier) with
      | none => exact Solidity.Lowering.Readonly.SourceHistory.Effect.halt F.static _
      | some body =>
        dsimp only
        split
        · apply Solidity.Lowering.Readonly.SourceHistory.Effect.bind
          · exact Solidity.Lowering.Readonly.SourceHistory.Effect.st F.static
          · intro saved
            apply Solidity.Lowering.Readonly.SourceHistory.Effect.bind
            · exact Solidity.Lowering.Readonly.SourceHistory.Effect.modSt F.static _ (fun _ => rfl)
            · intro done
              apply Solidity.Lowering.Readonly.SourceHistory.Effect.bind
              · apply Solidity.Lowering.Readonly.SourceHistory.Effect.attempt
                exact h.execItems known F _ _ _ _
              · intro caught
                apply Solidity.Lowering.Readonly.SourceHistory.Effect.bind
                · exact Solidity.Lowering.Readonly.SourceHistory.Effect.st F.static
                · intro reached
                  cases current : reached.fnLocals with
                  | mk context values =>
                    apply Solidity.Lowering.Readonly.SourceHistory.Effect.bind
                    · exact Solidity.Lowering.Readonly.SourceHistory.Effect.modSt F.static _ (fun _ => rfl)
                    · intro restored
                      cases caught
                      all_goals repeat' first
                       | exact Solidity.Lowering.Readonly.SourceHistory.Effect.pure F.static _
                       | exact Solidity.Lowering.Readonly.SourceHistory.Effect.halt F.static _
                       | refine Solidity.Lowering.Readonly.SourceHistory.Effect.bind _ _ _ ?_ (fun value => ?_)
                       | split
                       | dsimp only
        · exact Solidity.Lowering.Readonly.SourceHistory.Effect.halt F.static _


theorem callInternal_succ_known : ∀ {E : Solidity.Source.Env} (G : Solidity.Source.Glob E) (F : Solidity.Source.Fr) (n : Nat) (known : Bool) (_h : KnownAt G n) (d : Solidity.Source.Decl) {ps : List Solidity.Source.STy} (vs : Solidity.Source.Vals E.layout ps) (rs : List Solidity.Source.STy), Solidity.Lowering.Readonly.SourceHistory.Effect F.static (Solidity.Source.callInternal (calldataKnown := known) G F (n+1) d vs rs) := by
  intro E G F n known h d ps vs rs
  simp only [Solidity.Source.callInternal]
  split
  · exact Solidity.Lowering.Readonly.SourceHistory.Effect.halt F.static _
  · apply Solidity.Lowering.Readonly.SourceHistory.Effect.bind
    · exact Solidity.Lowering.Readonly.SourceHistory.zeroVals_effect F.static n rs
    · intro defaults
      dsimp only
      split
      · apply Solidity.Lowering.Readonly.SourceHistory.Effect.bind
        · exact h.runMods known {F with checked := true} _ _ _
        · intro locals
          exact Solidity.Lowering.Readonly.SourceHistory.Effect.bind _ _ _ (Solidity.Lowering.Readonly.SourceHistory.Effect.lift F.static _) (fun returns => Solidity.Lowering.Readonly.SourceHistory.Effect.pure F.static _)
      · exact Solidity.Lowering.Readonly.SourceHistory.Effect.halt F.static _

theorem forIter_succ_known : ∀ {E : Solidity.Source.Env} (G : Solidity.Source.Glob E) (F : Solidity.Source.Fr) (n : Nat) (known : Bool) (_h : KnownAt G n) (nps : Nat) (ph : Option (Solidity.Source.Ph E)) {R : List Solidity.Source.STy} {M u : Bool} {Γ₁ Γ₂ : Solidity.Source.RCtx} (c : Solidity.Source.ROptBool E Γ₁) (post : Solidity.Source.ROptExpr E Γ₁) (body : Solidity.Source.RStmt E R M ⟨true,u⟩ Γ₁ Γ₂) (l : Solidity.Source.Locals E.layout Γ₁), Solidity.Lowering.Readonly.SourceHistory.Effect F.static (Solidity.Source.forIter (calldataKnown := known) G F (n+1) nps ph c post body l) := by
  intro E G F n known h nps ph R M u Γ₁ Γ₂ c post body l
  cases c <;> unfold Solidity.Source.forIter <;> dsimp only
  all_goals repeat' first
   | (with_reducible exact h.forIter known F _ _ _ _ _ _)
   | (with_reducible exact h.execS known F _ _ _ _)
   | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.getV_effect F.static _)
   | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.Effect.lift F.static _)
   | (with_reducible exact Solidity.Lowering.Readonly.SourceHistory.Effect.pure F.static _)
   | (with_reducible apply Solidity.Lowering.Readonly.SourceHistory.Effect.sub; exact h.evalE known F _)
   | (refine Solidity.Lowering.Readonly.SourceHistory.Effect.bind _ _ _ ?_ (fun value => ?_))
   | (cases post <;> dsimp only)
   | split
   | dsimp only

syntax "known_statement_case" ident "[" term,* "]" : tactic
macro_rules
  | `(tactic| known_statement_case $F:ident [$ls,*]) => `(tactic| repeat' first
      | (first $[| with_reducible exact $ls:term]*)
      | refine Effect.bind _ _ _ ?_ (fun value => ?_)
      | (with_reducible apply Effect.sub ($F).static)
      | split
      | dsimp only)

private theorem tryCall_succ_known {E : Env} (G : Glob E) (F : Fr) (fuel : Nat) (known : Bool) (_history : KnownAt G fuel) (nps : Nat) (ph : Option (Ph E)) {R : List STy} {M : Bool} {k : SCtx} {Γ Γ₁ Γ₂ : RCtx} {dn : DeclName} {ps rs : List STy} (target : RExpr E Γ (.contract dn)) (d : Decl) (h : d.fnSig E = some (ps, rs)) (args : RConvArgs E Γ ps) (ok : RItems E R M k (rs.reverseAux Γ) Γ₁) (cbind : Bool) (cat : RItems E R M k (catchCtx cbind Γ) Γ₂) (locals : Locals E.layout Γ) :
    Effect F.static (execS (calldataKnown := known) G F (fuel+1) nps ph ((RStmt.tryCall (E := E) (R := R) (M := M) target d h args ok cbind cat) : RStmt E R M k Γ Γ) locals) := by
  rw [TryKnown.equation]
  apply Effect.bind
  · exact Effect.sub _ _ _ (TryKnown.payload_effect G F fuel known _history target d h args)
  · intro pair
    exact TryKnown.finish_effect G F fuel nps known _history ph ok cbind cat pair.1 pair.2

private theorem statement_case_0 {E : Env} (G : Glob E) (F : Fr) (n : Nat) (known : Bool)
    (h : KnownAt G n) (nps : Nat) (ph : Option (Ph E))
    {R : List STy} {M : Bool} {k : SCtx} {Γ Γ' : RCtx}
    (s : RStmt E R M k Γ Γ') (locals : Locals E.layout Γ)
    (selected : s.ctorIdx = 0) :
    Effect F.static (execS (calldataKnown := known) G F (n+1) nps ph s locals) := by
  cases s <;> first
  | (exfalso; simp only [RStmt.ctorIdx] at selected; omega)
  | (simp only [execS]; known_statement_case F [Effect.pure F.static _, Effect.halt F.static _, Effect.lift F.static _, Effect.st F.static, Effect.modSt F.static _ (fun _ => rfl), h.evalE known F _])

private theorem statement_case_1 {E : Env} (G : Glob E) (F : Fr) (n : Nat) (known : Bool)
    (h : KnownAt G n) (nps : Nat) (ph : Option (Ph E))
    {R : List STy} {M : Bool} {k : SCtx} {Γ Γ' : RCtx}
    (s : RStmt E R M k Γ Γ') (locals : Locals E.layout Γ)
    (selected : s.ctorIdx = 1) :
    Effect F.static (execS (calldataKnown := known) G F (n+1) nps ph s locals) := by
  cases s <;> first
  | (exfalso; simp only [RStmt.ctorIdx] at selected; omega)
  | (simp only [execS]; known_statement_case F [Effect.pure F.static _, Effect.halt F.static _, Effect.lift F.static _, Effect.st F.static, Effect.modSt F.static _ (fun _ => rfl), h.runMods known F _ _ _, zeroInner_effect F.static n _ _])

private theorem statement_case_2 {E : Env} (G : Glob E) (F : Fr) (n : Nat) (known : Bool)
    (_h : KnownAt G n) (nps : Nat) (ph : Option (Ph E))
    {R : List STy} {M : Bool} {k : SCtx} {Γ Γ' : RCtx}
    (s : RStmt E R M k Γ Γ') (locals : Locals E.layout Γ)
    (selected : s.ctorIdx = 2) :
    Effect F.static (execS (calldataKnown := known) G F (n+1) nps ph s locals) := by
  cases s <;> first
  | (exfalso; simp only [RStmt.ctorIdx] at selected; omega)
  | (simp only [execS]; known_statement_case F [Effect.pure F.static _, Effect.halt F.static _, Effect.lift F.static _, Effect.st F.static, Effect.modSt F.static _ (fun _ => rfl), (zero_histories F.static n).2.1 _])

private theorem statement_case_3 {E : Env} (G : Glob E) (F : Fr) (n : Nat) (known : Bool)
    (h : KnownAt G n) (nps : Nat) (ph : Option (Ph E))
    {R : List STy} {M : Bool} {k : SCtx} {Γ Γ' : RCtx}
    (s : RStmt E R M k Γ Γ') (locals : Locals E.layout Γ)
    (selected : s.ctorIdx = 3) :
    Effect F.static (execS (calldataKnown := known) G F (n+1) nps ph s locals) := by
  cases s <;> first
  | (exfalso; simp only [RStmt.ctorIdx] at selected; omega)
  | (simp only [execS]; known_statement_case F [Effect.pure F.static _, Effect.halt F.static _, Effect.lift F.static _, Effect.st F.static, Effect.modSt F.static _ (fun _ => rfl), h.evalE known F _, getV_effect F.static _, convRV_effect F.static F n _ _])

private theorem statement_case_4 {E : Env} (G : Glob E) (F : Fr) (n : Nat) (known : Bool)
    (h : KnownAt G n) (nps : Nat) (ph : Option (Ph E))
    {R : List STy} {M : Bool} {k : SCtx} {Γ Γ' : RCtx}
    (s : RStmt E R M k Γ Γ') (locals : Locals E.layout Γ)
    (selected : s.ctorIdx = 4) :
    Effect F.static (execS (calldataKnown := known) G F (n+1) nps ph s locals) := by
  cases s <;> first
  | (exfalso; simp only [RStmt.ctorIdx] at selected; omega)
  | (simp only [execS]; known_statement_case F [Effect.pure F.static _, Effect.halt F.static _, Effect.lift F.static _, Effect.st F.static, Effect.modSt F.static _ (fun _ => rfl), h.execItems known F _ _ _ _])

private theorem statement_case_5 {E : Env} (G : Glob E) (F : Fr) (n : Nat) (known : Bool)
    (h : KnownAt G n) (nps : Nat) (ph : Option (Ph E))
    {R : List STy} {M : Bool} {k : SCtx} {Γ Γ' : RCtx}
    (s : RStmt E R M k Γ Γ') (locals : Locals E.layout Γ)
    (selected : s.ctorIdx = 5) :
    Effect F.static (execS (calldataKnown := known) G F (n+1) nps ph s locals) := by
  cases s <;> first
  | (exfalso; simp only [RStmt.ctorIdx] at selected; omega)
  | (simp only [execS]; known_statement_case F [Effect.pure F.static _, Effect.halt F.static _, Effect.lift F.static _, Effect.st F.static, Effect.modSt F.static _ (fun _ => rfl), h.evalE known F _, h.execS known F _ _ _ _, getV_effect F.static _])

private theorem statement_case_6 {E : Env} (G : Glob E) (F : Fr) (n : Nat) (known : Bool)
    (h : KnownAt G n) (nps : Nat) (ph : Option (Ph E))
    {R : List STy} {M : Bool} {k : SCtx} {Γ Γ' : RCtx}
    (s : RStmt E R M k Γ Γ') (locals : Locals E.layout Γ)
    (selected : s.ctorIdx = 6) :
    Effect F.static (execS (calldataKnown := known) G F (n+1) nps ph s locals) := by
  cases s <;> first
  | (exfalso; simp only [RStmt.ctorIdx] at selected; omega)
  | (simp only [execS]; known_statement_case F [Effect.pure F.static _, Effect.halt F.static _, Effect.lift F.static _, Effect.st F.static, Effect.modSt F.static _ (fun _ => rfl), h.evalE known F _, h.execS known F _ _ _ _, getV_effect F.static _])

private theorem statement_case_7 {E : Env} (G : Glob E) (F : Fr) (n : Nat) (known : Bool)
    (h : KnownAt G n) (nps : Nat) (ph : Option (Ph E))
    {R : List STy} {M : Bool} {k : SCtx} {Γ Γ' : RCtx}
    (s : RStmt E R M k Γ Γ') (locals : Locals E.layout Γ)
    (selected : s.ctorIdx = 7) :
    Effect F.static (execS (calldataKnown := known) G F (n+1) nps ph s locals) := by
  cases s <;> first
  | (exfalso; simp only [RStmt.ctorIdx] at selected; omega)
  | (simp only [execS]; known_statement_case F [Effect.pure F.static _, Effect.halt F.static _, Effect.lift F.static _, Effect.st F.static, Effect.modSt F.static _ (fun _ => rfl), h.evalE known F _, h.execS known F _ _ _ _, getV_effect F.static _])

private theorem statement_case_8 {E : Env} (G : Glob E) (F : Fr) (n : Nat) (known : Bool)
    (h : KnownAt G n) (nps : Nat) (ph : Option (Ph E))
    {R : List STy} {M : Bool} {k : SCtx} {Γ Γ' : RCtx}
    (s : RStmt E R M k Γ Γ') (locals : Locals E.layout Γ)
    (selected : s.ctorIdx = 8) :
    Effect F.static (execS (calldataKnown := known) G F (n+1) nps ph s locals) := by
  cases s <;> first
  | (exfalso; simp only [RStmt.ctorIdx] at selected; omega)
  | (simp only [execS]; known_statement_case F [Effect.pure F.static _, Effect.halt F.static _, Effect.lift F.static _, Effect.st F.static, Effect.modSt F.static _ (fun _ => rfl), h.evalE known F _, h.execS known F _ _ _ _, getV_effect F.static _])

private theorem statement_case_9 {E : Env} (G : Glob E) (F : Fr) (n : Nat) (known : Bool)
    (h : KnownAt G n) (nps : Nat) (ph : Option (Ph E))
    {R : List STy} {M : Bool} {k : SCtx} {Γ Γ' : RCtx}
    (s : RStmt E R M k Γ Γ') (locals : Locals E.layout Γ)
    (selected : s.ctorIdx = 9) :
    Effect F.static (execS (calldataKnown := known) G F (n+1) nps ph s locals) := by
  cases s <;> first
  | (exfalso; simp only [RStmt.ctorIdx] at selected; omega)
  | (simp only [execS]; known_statement_case F [Effect.pure F.static _, Effect.halt F.static _, Effect.lift F.static _, Effect.st F.static, Effect.modSt F.static _ (fun _ => rfl), h.execS known F _ _ _ _, h.forIter known F _ _ _ _ _ _])

private theorem statement_case_10 {E : Env} (G : Glob E) (F : Fr) (n : Nat) (known : Bool)
    (_h : KnownAt G n) (nps : Nat) (ph : Option (Ph E))
    {R : List STy} {M : Bool} {k : SCtx} {Γ Γ' : RCtx}
    (s : RStmt E R M k Γ Γ') (locals : Locals E.layout Γ)
    (selected : s.ctorIdx = 10) :
    Effect F.static (execS (calldataKnown := known) G F (n+1) nps ph s locals) := by
  cases s <;> first
  | (exfalso; simp only [RStmt.ctorIdx] at selected; omega)
  | (simp only [execS]; known_statement_case F [Effect.pure F.static _, Effect.halt F.static _, Effect.lift F.static _, Effect.st F.static, Effect.modSt F.static _ (fun _ => rfl)])

private theorem statement_case_11 {E : Env} (G : Glob E) (F : Fr) (n : Nat) (known : Bool)
    (_h : KnownAt G n) (nps : Nat) (ph : Option (Ph E))
    {R : List STy} {M : Bool} {k : SCtx} {Γ Γ' : RCtx}
    (s : RStmt E R M k Γ Γ') (locals : Locals E.layout Γ)
    (selected : s.ctorIdx = 11) :
    Effect F.static (execS (calldataKnown := known) G F (n+1) nps ph s locals) := by
  cases s <;> first
  | (exfalso; simp only [RStmt.ctorIdx] at selected; omega)
  | (simp only [execS]; known_statement_case F [Effect.pure F.static _, Effect.halt F.static _, Effect.lift F.static _, Effect.st F.static, Effect.modSt F.static _ (fun _ => rfl)])

private theorem statement_case_12 {E : Env} (G : Glob E) (F : Fr) (n : Nat) (known : Bool)
    (_h : KnownAt G n) (nps : Nat) (ph : Option (Ph E))
    {R : List STy} {M : Bool} {k : SCtx} {Γ Γ' : RCtx}
    (s : RStmt E R M k Γ Γ') (locals : Locals E.layout Γ)
    (selected : s.ctorIdx = 12) :
    Effect F.static (execS (calldataKnown := known) G F (n+1) nps ph s locals) := by
  cases s <;> first
  | (exfalso; simp only [RStmt.ctorIdx] at selected; omega)
  | (simp only [execS]; known_statement_case F [Effect.pure F.static _, Effect.halt F.static _, Effect.lift F.static _, Effect.st F.static, Effect.modSt F.static _ (fun _ => rfl)])

private theorem statement_case_13 {E : Env} (G : Glob E) (F : Fr) (n : Nat) (known : Bool)
    (_h : KnownAt G n) (nps : Nat) (ph : Option (Ph E))
    {R : List STy} {M : Bool} {k : SCtx} {Γ Γ' : RCtx}
    (s : RStmt E R M k Γ Γ') (locals : Locals E.layout Γ)
    (selected : s.ctorIdx = 13) :
    Effect F.static (execS (calldataKnown := known) G F (n+1) nps ph s locals) := by
  cases s <;> first
  | (exfalso; simp only [RStmt.ctorIdx] at selected; omega)
  | (simp only [execS]; known_statement_case F [Effect.pure F.static _, Effect.halt F.static _, Effect.lift F.static _, Effect.st F.static, Effect.modSt F.static _ (fun _ => rfl)])

private theorem statement_case_14 {E : Env} (G : Glob E) (F : Fr) (n : Nat) (known : Bool)
    (h : KnownAt G n) (nps : Nat) (ph : Option (Ph E))
    {R : List STy} {M : Bool} {k : SCtx} {Γ Γ' : RCtx}
    (s : RStmt E R M k Γ Γ') (locals : Locals E.layout Γ)
    (selected : s.ctorIdx = 14) :
    Effect F.static (execS (calldataKnown := known) G F (n+1) nps ph s locals) := by
  cases s <;> first
  | (exfalso; simp only [RStmt.ctorIdx] at selected; omega)
  | (simp only [execS]; known_statement_case F [Effect.pure F.static _, Effect.halt F.static _, Effect.lift F.static _, Effect.st F.static, Effect.modSt F.static _ (fun _ => rfl), h.evalE known F _, getV_effect F.static _, convRV_effect F.static F n _ _])

private theorem statement_case_15 {E : Env} (G : Glob E) (F : Fr) (n : Nat) (known : Bool)
    (h : KnownAt G n) (nps : Nat) (ph : Option (Ph E))
    {R : List STy} {M : Bool} {k : SCtx} {Γ Γ' : RCtx}
    (s : RStmt E R M k Γ Γ') (locals : Locals E.layout Γ)
    (selected : s.ctorIdx = 15) :
    Effect F.static (execS (calldataKnown := known) G F (n+1) nps ph s locals) := by
  cases s <;> first
  | (exfalso; simp only [RStmt.ctorIdx] at selected; omega)
  | (simp only [execS]; known_statement_case F [Effect.pure F.static _, Effect.halt F.static _, Effect.lift F.static _, Effect.st F.static, Effect.modSt F.static _ (fun _ => rfl), h.evalConvArgs known F _])

private theorem statement_case_16 {E : Env} (G : Glob E) (F : Fr) (n : Nat) (known : Bool)
    (h : KnownAt G n) (nps : Nat) (ph : Option (Ph E))
    {R : List STy} {M : Bool} {k : SCtx} {Γ Γ' : RCtx}
    (s : RStmt E R M k Γ Γ') (locals : Locals E.layout Γ)
    (selected : s.ctorIdx = 16) :
    Effect F.static (execS (calldataKnown := known) G F (n+1) nps ph s locals) := by
  cases s <;> first
  | (exfalso; simp only [RStmt.ctorIdx] at selected; omega)
  | (simp only [execS]; known_statement_case F [Effect.pure F.static _, Effect.halt F.static _, Effect.lift F.static _, Effect.st F.static, Effect.modSt F.static _ (fun _ => rfl), h.evalConvArgs known F _, encodeVals_effect F.static F n _ _])

private theorem statement_case_17 {E : Env} (G : Glob E) (F : Fr) (n : Nat) (known : Bool)
    (h : KnownAt G n) (nps : Nat) (ph : Option (Ph E))
    {R : List STy} {M : Bool} {k : SCtx} {Γ Γ' : RCtx}
    (s : RStmt E R M k Γ Γ') (locals : Locals E.layout Γ)
    (selected : s.ctorIdx = 17) :
    Effect F.static (execS (calldataKnown := known) G F (n+1) nps ph s locals) := by
  cases s <;> first
  | (exfalso; simp only [RStmt.ctorIdx] at selected; omega)
  | (simp only [execS]; known_statement_case F [Effect.pure F.static _, Effect.halt F.static _, Effect.lift F.static _, Effect.st F.static, Effect.modSt F.static _ (fun _ => rfl), h.evalConvArgs known F _, encodeVals_effect F.static F n _ _])

private theorem statement_case_18 {E : Env} (G : Glob E) (F : Fr) (n : Nat) (known : Bool)
    (_h : KnownAt G n) (nps : Nat) (ph : Option (Ph E))
    {R : List STy} {M : Bool} {k : SCtx} {Γ Γ' : RCtx}
    (s : RStmt E R M k Γ Γ') (locals : Locals E.layout Γ)
    (selected : s.ctorIdx = 18) :
    Effect F.static (execS (calldataKnown := known) G F (n+1) nps ph s locals) := by
  cases s <;> first
  | (exfalso; simp only [RStmt.ctorIdx] at selected; omega)
  | (simp only [execS]; known_statement_case F [Effect.pure F.static _, Effect.halt F.static _, Effect.lift F.static _, Effect.st F.static, Effect.modSt F.static _ (fun _ => rfl), heapBytes_effect F.static _])

private theorem statement_case_19 {E : Env} (G : Glob E) (F : Fr) (n : Nat) (known : Bool)
    (h : KnownAt G n) (nps : Nat) (ph : Option (Ph E))
    {R : List STy} {M : Bool} {k : SCtx} {Γ Γ' : RCtx}
    (s : RStmt E R M k Γ Γ') (locals : Locals E.layout Γ)
    (selected : s.ctorIdx = 19) :
    Effect F.static (execS (calldataKnown := known) G F (n+1) nps ph s locals) := by
  cases s <;> first
  | (exfalso; simp only [RStmt.ctorIdx] at selected; omega)
  | (simp only [execS]; known_statement_case F [Effect.pure F.static _, Effect.halt F.static _, Effect.lift F.static _, Effect.st F.static, Effect.modSt F.static _ (fun _ => rfl), h.evalE known F _, pushVals_effect F.static F n _ _ _])

private theorem statement_case_20 {E : Env} (G : Glob E) (F : Fr) (n : Nat) (known : Bool)
    (h : KnownAt G n) (nps : Nat) (ph : Option (Ph E))
    {R : List STy} {M : Bool} {k : SCtx} {Γ Γ' : RCtx}
    (s : RStmt E R M k Γ Γ') (locals : Locals E.layout Γ)
    (selected : s.ctorIdx = 20) :
    Effect F.static (execS (calldataKnown := known) G F (n+1) nps ph s locals) := by
  cases s <;> first
  | (exfalso; simp only [RStmt.ctorIdx] at selected; omega)
  | (with_reducible exact tryCall_succ_known G F n known h nps ph _ _ _ _ _ _ _ _)

private theorem statement_case_21 {E : Env} (G : Glob E) (F : Fr) (n : Nat) (known : Bool)
    (h : KnownAt G n) (nps : Nat) (ph : Option (Ph E))
    {R : List STy} {M : Bool} {k : SCtx} {Γ Γ' : RCtx}
    (s : RStmt E R M k Γ Γ') (locals : Locals E.layout Γ)
    (selected : s.ctorIdx = 21) :
    Effect F.static (execS (calldataKnown := known) G F (n+1) nps ph s locals) := by
  cases s <;> first
  | (exfalso; simp only [RStmt.ctorIdx] at selected; omega)
  | (simp only [execS]; known_statement_case F [Effect.pure F.static _, Effect.halt F.static _, Effect.lift F.static _, Effect.st F.static, Effect.modSt F.static _ (fun _ => rfl), h.evalConvArgs known F _, h.execItems known F _ _ _ _, allocRef_effect F.static _, h.callLibrary F _ _ _])

/-- Every typed statement constructor, including delegated try, with
only its actual direct operations in proof search. -/
theorem execS_succ_known {E : Env} (G : Glob E) (F : Fr) (n : Nat) (known : Bool)
    (h : KnownAt G n) (nps : Nat) (ph : Option (Ph E))
    {R : List STy} {M : Bool} {k : SCtx} {Γ Γ' : RCtx}
    (s : RStmt E R M k Γ Γ') (locals : Locals E.layout Γ) :
    Effect F.static (execS (calldataKnown := known) G F (n+1) nps ph s locals) := by
  by_cases cut0 : s.ctorIdx = 0
  · exact statement_case_0 G F n known h nps ph s locals cut0
  by_cases cut1 : s.ctorIdx = 1
  · exact statement_case_1 G F n known h nps ph s locals cut1
  by_cases cut2 : s.ctorIdx = 2
  · exact statement_case_2 G F n known h nps ph s locals cut2
  by_cases cut3 : s.ctorIdx = 3
  · exact statement_case_3 G F n known h nps ph s locals cut3
  by_cases cut4 : s.ctorIdx = 4
  · exact statement_case_4 G F n known h nps ph s locals cut4
  by_cases cut5 : s.ctorIdx = 5
  · exact statement_case_5 G F n known h nps ph s locals cut5
  by_cases cut6 : s.ctorIdx = 6
  · exact statement_case_6 G F n known h nps ph s locals cut6
  by_cases cut7 : s.ctorIdx = 7
  · exact statement_case_7 G F n known h nps ph s locals cut7
  by_cases cut8 : s.ctorIdx = 8
  · exact statement_case_8 G F n known h nps ph s locals cut8
  by_cases cut9 : s.ctorIdx = 9
  · exact statement_case_9 G F n known h nps ph s locals cut9
  by_cases cut10 : s.ctorIdx = 10
  · exact statement_case_10 G F n known h nps ph s locals cut10
  by_cases cut11 : s.ctorIdx = 11
  · exact statement_case_11 G F n known h nps ph s locals cut11
  by_cases cut12 : s.ctorIdx = 12
  · exact statement_case_12 G F n known h nps ph s locals cut12
  by_cases cut13 : s.ctorIdx = 13
  · exact statement_case_13 G F n known h nps ph s locals cut13
  by_cases cut14 : s.ctorIdx = 14
  · exact statement_case_14 G F n known h nps ph s locals cut14
  by_cases cut15 : s.ctorIdx = 15
  · exact statement_case_15 G F n known h nps ph s locals cut15
  by_cases cut16 : s.ctorIdx = 16
  · exact statement_case_16 G F n known h nps ph s locals cut16
  by_cases cut17 : s.ctorIdx = 17
  · exact statement_case_17 G F n known h nps ph s locals cut17
  by_cases cut18 : s.ctorIdx = 18
  · exact statement_case_18 G F n known h nps ph s locals cut18
  by_cases cut19 : s.ctorIdx = 19
  · exact statement_case_19 G F n known h nps ph s locals cut19
  by_cases cut20 : s.ctorIdx = 20
  · exact statement_case_20 G F n known h nps ph s locals cut20
  have bound : s.ctorIdx < 22 := by cases s <;> simp only [RStmt.ctorIdx] <;> decide
  exact statement_case_21 G F n known h nps ph s locals (by omega)

end Solidity.Lowering.Readonly.SourceHistory

/-- info: 'Solidity.Lowering.Readonly.SourceHistory.execItems_succ_known' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Lowering.Readonly.SourceHistory.execItems_succ_known

/-- info: 'Solidity.Lowering.Readonly.SourceHistory.runMods_succ_known' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Lowering.Readonly.SourceHistory.runMods_succ_known

/-- info: 'Solidity.Lowering.Readonly.SourceHistory.callInternal_succ_known' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Lowering.Readonly.SourceHistory.callInternal_succ_known

/-- info: 'Solidity.Lowering.Readonly.SourceHistory.forIter_succ_known' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Lowering.Readonly.SourceHistory.forIter_succ_known

/-- info: 'Solidity.Lowering.Readonly.SourceHistory.execS_succ_known' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Lowering.Readonly.SourceHistory.execS_succ_known
