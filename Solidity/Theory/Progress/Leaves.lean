import Solidity.Theory.Progress.Fragment
import Solidity.Source.Progress.BuiltinStatements
import Solidity.Source.Progress.EmitBuiltins


namespace Solidity.Theory.Progress

open Solidity.Source Solidity.Source.Progress EM

variable {E : Env}

inductive EmitNode (A : Decl → Prop) {R : List STy} {M : Bool} :
    {k : SCtx} → {Γ Γ' : RCtx} → RStmt E R M k Γ Γ' → Prop where
  | mk {k : SCtx} {Γ : RCtx} {ps : List STy} (ev : Decl) (he : ev.paramTys E = some ps) (args : RConvArgs E Γ ps) :
      ps.all STy.keyable = true → RConvArgs.ValFragC A args →
      EmitNode A (RStmt.emit (R := R) (M := M) (k := k) ev he args)

inductive RevertErrorNode (A : Decl → Prop) {R : List STy} {M : Bool} :
    {k : SCtx} → {Γ Γ' : RCtx} → RStmt E R M k Γ Γ' → Prop where
  | mk {k : SCtx} {Γ : RCtx} {ps : List STy} (er : Decl) (he : er.paramTys E = some ps) (args : RConvArgs E Γ ps) :
      ps.all STy.keyable = true → RConvArgs.ValFragC A args →
      RevertErrorNode A (RStmt.revertError (R := R) (M := M) (k := k) er he args)

inductive BuiltinNode (A : Decl → Prop) {R : List STy} {M : Bool} :
    {k : SCtx} → {Γ Γ' : RCtx} → RStmt E R M k Γ Γ' → Prop where
  | mk {k : SCtx} {Γ : RCtx} {ts : List STy} {t : STy} (b : Builtin) (args : RArgs E Γ ts)
      (ht : b.callTy E.isBase E.mapFree ts = some t) :
      BuiltinFragment A b args t → BuiltinNode A (RStmt.expr (R := R) (M := M) (k := k) (.builtin b args ht))

def emitExt (A : Decl → Prop) : StmtExt E := ⟨fun s _ => EmitNode A s⟩
def revertErrorExt (A : Decl → Prop) : StmtExt E := ⟨fun s _ => RevertErrorNode A s⟩
def builtinExt (A : Decl → Prop) : StmtExt E := ⟨fun s _ => BuiltinNode A s⟩

def leafExt (A : Decl → Prop) : StmtExt E := (emitExt A).or ((revertErrorExt A).or (builtinExt A))

theorem emitExt_sound (G : Glob E) (A : Decl → Prop) (Q : String → Prop) : (emitExt A).Sound G A Q := by
  intro _ _ n _ hX F hP nps ph R M k Γ Γ' s _ l hs _ ho _
  cases hs with
  | mk ev he args hp hf =>
    rename_i ps
    simp only [execS]
    refine NSP.bind (NSP.sub' (Q := fun _ => True) (NSP.weaken
      (NSP.of_ns ((hX n (Nat.le_refl n) F hP).convArgs args hf ho)) fun _ _ _ => trivial)) fun p _ => ?_
    refine NSP.bind (NSP.of_ns (encodeVals_key_ns F n false hp p.1)) fun data _ => ?_
    split
    · exact NSP.halt' trivial
    · exact NSP.bind (NSP.of_ns (NS.modSt' (fun s => { s with logs :=
        (F.this, G.selector (sigOf E.layout ev.name ps) ++ data) :: s.logs }))) fun _ _ =>
        NSP.pure' ⟨fun h => h.elim, fun _ => rfl⟩

theorem revertErrorExt_sound (G : Glob E) (A : Decl → Prop) (Q : String → Prop) :
    (revertErrorExt A).Sound G A Q := by
  intro _ _ n _ hX F hP nps ph R M k Γ Γ' s _ l hs _ ho _
  cases hs with
  | mk er he args hp hf =>
    simp only [execS]
    refine NSP.bind (NSP.sub' (Q := fun _ => True) (NSP.weaken
      (NSP.of_ns ((hX n (Nat.le_refl n) F hP).convArgs args hf ho)) fun _ _ _ => trivial)) fun p _ => ?_
    exact NSP.bind (NSP.of_ns (encodeVals_key_ns F n false hp p.1)) fun _ _ => NSP.halt' trivial

theorem builtinExt_sound {G : Glob E} {A : Decl → Prop} {Q : String → Prop}
    (hAll : ∀ n F, Q F.contract → ExprNSAt A G F n) : (builtinExt A).Sound G A Q := by
  intro _ _ n _ _ F hP nps ph R M k Γ Γ' s _ l hs _ _ _
  cases hs with
  | mk b args ht hf =>
    have hb : NS (evalE G F n (.builtin b args ht)) := by
      cases n with
      | zero => exact NS.halt' fun _ h => by cases h
      | succ m => exact builtinFragment_ns G F (fun j => hAll j F hP) hf m
    simp only [execS]
    exact NSP.bind (NSP.sub' (Q := fun _ => True) (NSP.weaken (NSP.of_ns hb) fun _ _ _ => trivial)) fun _ _ =>
      NSP.pure' ⟨fun _ => ⟨_, rfl⟩, fun _ => rfl⟩

theorem leafExt_sound {G : Glob E} {A : Decl → Prop} {Q : String → Prop}
    (hAll : ∀ n F, Q F.contract → ExprNSAt A G F n) : (leafExt A).Sound G A Q :=
  (emitExt_sound G A Q).or ((revertErrorExt_sound G A Q).or (builtinExt_sound hAll))

def effectExt (A : Decl → Prop) : StmtExt E := (emitExt A).or (revertErrorExt A)

theorem effectExt_sound (G : Glob E) (A : Decl → Prop) (Q : String → Prop) : (effectExt A).Sound G A Q :=
  (emitExt_sound G A Q).or (revertErrorExt_sound G A Q)

theorem leafExt_sound_callFree (G : Glob E) (Q : String → Prop) : (leafExt (fun _ => False)).Sound G (fun _ => False) Q :=
  leafExt_sound fun n F _ => exprNSAt G F n

end Solidity.Theory.Progress
