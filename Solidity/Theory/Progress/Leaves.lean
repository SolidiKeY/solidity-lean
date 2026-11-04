import Solidity.Theory.Progress.Fragment
import Solidity.Source.Progress.BuiltinStatements
import Solidity.Source.Progress.EmitBuiltins

/-!
# Leaf statements as extensions (S4.2)

Three statement kinds the source interpreter runs, each an instance of the
extension lemma shape `StmtExt.Sound` (`Theory/Progress/Fragment.lean`), so
they are admitted inside every block, loop and body of the closure:

* `emit E(args);` with arguments of the call fragment and event parameters
  of elementary keyable types (`emitExt`, sound for every program,
  `emitExt_sound`; the static-frame revert is kept);
* `revert E(args);` of a custom error, under the same conditions
  (`revertErrorExt`, `revertErrorExt_sound`): it always reverts;
* a builtin statement (`require`, `assert`, `revert`, the hashes,
  `addmod`/`mulmod`, `ecrecover`) of `Source/Progress/BuiltinAdmission.lean`'s
  `BuiltinFragment` (`builtinExt`). Its soundness (`builtinExt_sound`) asks
  expression progress at **every** horizon, which the call-free fragment
  (`exprNSAt`) and checked elaborated programs (`checked_fragments`) give,
  but the joint induction of `Theory/Progress/Calls.lean` does not (it has
  only the horizons up to the current one): a builtin statement is
  admitted at a call site, and inside a called body only of a call-free
  program. The step lemmas the existing direct-node adapters prove
  (`execS_emit_ns`, `checked_builtin_statement`) give `NS` only; the ones
  here add the postcondition the closure needs (a simple statement ends
  normally; nothing escapes).

`leafExt` combines the three (`leafExt_sound`, by `StmtExt.Sound.or`).
-/

namespace Solidity.Theory.Progress

open Solidity.Source Solidity.Source.Progress EM

variable {E : Env}

/-- `emit ev(args);` with fragment arguments and keyable parameters. -/
inductive EmitNode (A : Decl → Prop) {R : List STy} {M : Bool} :
    {k : SCtx} → {Γ Γ' : RCtx} → RStmt E R M k Γ Γ' → Prop where
  | mk {k : SCtx} {Γ : RCtx} {ps : List STy} (ev : Decl) (he : ev.paramTys E = some ps) (args : RConvArgs E Γ ps) :
      ps.all STy.keyable = true → RConvArgs.ValFragC A args →
      EmitNode A (RStmt.emit (R := R) (M := M) (k := k) ev he args)

/-- `revert er(args);` with fragment arguments and keyable parameters. -/
inductive RevertErrorNode (A : Decl → Prop) {R : List STy} {M : Bool} :
    {k : SCtx} → {Γ Γ' : RCtx} → RStmt E R M k Γ Γ' → Prop where
  | mk {k : SCtx} {Γ : RCtx} {ps : List STy} (er : Decl) (he : er.paramTys E = some ps) (args : RConvArgs E Γ ps) :
      ps.all STy.keyable = true → RConvArgs.ValFragC A args →
      RevertErrorNode A (RStmt.revertError (R := R) (M := M) (k := k) er he args)

/-- A builtin statement of the builtins' fragment. -/
inductive BuiltinNode (A : Decl → Prop) {R : List STy} {M : Bool} :
    {k : SCtx} → {Γ Γ' : RCtx} → RStmt E R M k Γ Γ' → Prop where
  | mk {k : SCtx} {Γ : RCtx} {ts : List STy} {t : STy} (b : Builtin) (args : RArgs E Γ ts)
      (ht : b.callTy E.isBase ts = some t) :
      BuiltinFragment A b args t → BuiltinNode A (RStmt.expr (R := R) (M := M) (k := k) (.builtin b args ht))

def emitExt (A : Decl → Prop) : StmtExt E := ⟨EmitNode A⟩
def revertErrorExt (A : Decl → Prop) : StmtExt E := ⟨RevertErrorNode A⟩
def builtinExt (A : Decl → Prop) : StmtExt E := ⟨BuiltinNode A⟩

/-- The three leaf extensions. -/
def leafExt (A : Decl → Prop) : StmtExt E := (emitExt A).or ((revertErrorExt A).or (builtinExt A))

/-- **`emit` is sound**: never `stuck`; it completes normally or reverts
(static frame). -/
theorem emitExt_sound (G : Glob E) (A : Decl → Prop) (Q : String → Prop) : (emitExt A).Sound G A Q := by
  intro n _ hX F hP nps ph R M k Γ Γ' s l hs ho _
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

/-- **A custom-error revert is sound**: it is never `stuck`; it reverts. -/
theorem revertErrorExt_sound (G : Glob E) (A : Decl → Prop) (Q : String → Prop) :
    (revertErrorExt A).Sound G A Q := by
  intro n _ hX F hP nps ph R M k Γ Γ' s l hs ho _
  cases hs with
  | mk er he args hp hf =>
    simp only [execS]
    refine NSP.bind (NSP.sub' (Q := fun _ => True) (NSP.weaken
      (NSP.of_ns ((hX n (Nat.le_refl n) F hP).convArgs args hf ho)) fun _ _ _ => trivial)) fun p _ => ?_
    exact NSP.bind (NSP.of_ns (encodeVals_key_ns F n false hp p.1)) fun _ _ => NSP.halt' trivial

/-- **A builtin statement is sound** where expression progress holds at
every horizon; it completes normally, reverts or panics. -/
theorem builtinExt_sound {G : Glob E} {A : Decl → Prop} {Q : String → Prop}
    (hAll : ∀ n F, Q F.contract → ExprNSAt A G F n) : (builtinExt A).Sound G A Q := by
  intro n _ _ F hP nps ph R M k Γ Γ' s l hs _ _
  cases hs with
  | mk b args ht hf =>
    have hb : NS (evalE G F n (.builtin b args ht)) := by
      cases n with
      | zero => exact NS.halt' fun _ h => by cases h
      | succ m => exact builtinFragment_ns G F (fun j => hAll j F hP) hf m
    simp only [execS]
    exact NSP.bind (NSP.sub' (Q := fun _ => True) (NSP.weaken (NSP.of_ns hb) fun _ _ _ => trivial)) fun _ _ =>
      NSP.pure' ⟨fun _ => ⟨_, rfl⟩, fun _ => rfl⟩

/-- **The leaf extensions together are sound**, given expression progress
at every horizon. -/
theorem leafExt_sound {G : Glob E} {A : Decl → Prop} {Q : String → Prop}
    (hAll : ∀ n F, Q F.contract → ExprNSAt A G F n) : (leafExt A).Sound G A Q :=
  (emitExt_sound G A Q).or ((revertErrorExt_sound G A Q).or (builtinExt_sound hAll))

/-- Call-free programs have expression progress at every horizon. -/
theorem leafExt_sound_callFree (G : Glob E) (Q : String → Prop) : (leafExt (fun _ => False)).Sound G (fun _ => False) Q :=
  leafExt_sound fun n F _ => exprNSAt G F n

end Solidity.Theory.Progress
