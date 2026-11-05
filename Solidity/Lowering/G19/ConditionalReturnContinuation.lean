import Solidity.Lowering.G19.ConditionalReturn

/-! Continuations after a mapped unconditional return are unreachable.
The target consumes the existing captured flag; arbitrary tails are not certified on a normal path. -/
namespace Solidity.Lowering.G19.ConditionalReturnContinuation
open Solidity.Lowering.V07

def statement {E : Source.Env} {Γ outΓ : Source.RCtx} {τ : Source.STy} {M : Bool} {k : Source.SCtx}
    (ci ca : Source.Idx Γ .bool) (i a j b : Source.Idx Γ τ)
    (tail : Source.RItems E [] M k Γ outΓ) : Source.RStmt E [] M k Γ Γ :=
  .block (.stmt (ConditionalReturn.statement ci ca i a j b) tail)

def suffix {C : Contract} {Γ : Ctx}
    (tail : Prog C (.val .bool :: Γ) (.val .bool :: Γ)) : Prog C (.val .bool :: Γ) (.val .bool :: Γ) :=
  .cons (.ite (.simple (.local .here)) .nil tail) .nil

def code {C : Contract} {Γ : Ctx} {p : PrimTy} (ci ca : Idx Γ (.val .bool))
    (i a j b : Idx Γ (.val p)) (tail : Prog C (.val .bool :: Γ) (.val .bool :: Γ)) : Prog C Γ (.val .bool :: Γ) :=
  (ConditionalReturn.code ci ca i a j b).join (suffix tail)

theorem source_run {E : Source.Env} {Γ outΓ : Source.RCtx} {τ : Source.STy}
    (G : Source.Glob E) (F : Source.Fr) (fuel nps : Nat) (ph : Option (Source.Ph E))
    {M : Bool} {k : Source.SCtx} (s : Source.EMState E Γ)
    (ci ca : Source.Idx Γ .bool) (choice : Bool) (i a j b : Source.Idx Γ τ)
    (tail : Source.RItems E [] M k Γ outΓ) (read : s.1.get ca = .bool choice) :
    (Source.execS G F (fuel+8) nps ph (M := M) (statement (k := k) ci ca i a j b tail) s.1).run
      (.nil,s.2) =
      (.ok (Source.Out.ret (ConditionalAssignments.sourceAfter s ci choice i a j b).1),(.nil,s.2)) := by
  have beforeRun : (Source.execS G F (fuel+6) nps ph (M := M)
      (ConditionalReturn.statement (k := k) ci ca i a j b) s.1).run (.nil,s.2) =
      (.ok (Source.Out.ret (ConditionalAssignments.sourceAfter s ci choice i a j b).1),(.nil,s.2)) :=
    ConditionalReturn.source_run G F fuel nps ph s ci ca choice i a j b read
  have itemsRun : (Source.execItems G F (fuel+7) nps ph (M := M) (k := k)
      (.stmt (ConditionalReturn.statement ci ca i a j b) tail) s.1).run (.nil,s.2) =
      (.ok (Source.Out.ret (ConditionalAssignments.sourceAfter s ci choice i a j b).1),(.nil,s.2)) := by
    rw [Source.execItems,Source.Hoare.run_bind,beforeRun]
    rfl
  rw [statement,Source.execS,Source.Hoare.run_bind,itemsRun]
  rfl

theorem target_run {C : Contract} {Γ : Ctx} {p : PrimTy} (s : State C Γ)
    (ci ca : Idx Γ (.val .bool)) (choice : Bool) (i a j b : Idx Γ (.val p))
    (tail : Prog C (.val .bool :: Γ) (.val .bool :: Γ)) (read : TEnv.get ca s.env = choice) :
    (code ci ca i a j b tail).run s = .ok ⟨ConditionalReturn.reached s ci choice i a j b,List.prefix_refl _⟩ := by
  have beforeRun : (ConditionalReturn.code ci ca i a j b).run s =
      .ok ⟨ConditionalReturn.reached s ci choice i a j b,List.prefix_refl _⟩ :=
    ConditionalReturn.target_run s ci ca choice i a j b read
  unfold Prog.run at beforeRun
  rw [code,DeferredSource.join_run]
  unfold TRun.seq
  rw [beforeRun]
  rfl

theorem correct {E : Source.Env} {srcΓ outΓ : Source.RCtx} {τ : Source.STy}
    {C : Contract} {Γ : Ctx} {p : PrimTy}
    (G : Source.Glob E) (F : Source.Fr) (fuel nps : Nat) (ph : Option (Source.Ph E))
    {M : Bool} {k : Source.SCtx}
    (source : Source.EMState E srcΓ) (target : State C Γ) (m : ContextMap srcΓ Γ)
    (R : (σ : Source.STy) → (u : LTy) → Source.Val E.layout σ → u.TDenote C target.H → Prop)
    (aligned : m.Related R source.1 target.env)
    (boolReflect : ∀ (v : Source.Val E.layout .bool) (c : Bool), R .bool (.val .bool) v c → v = .bool c)
    (ci ca : Source.Idx srcΓ .bool) (i a j b : Source.Idx srcΓ τ)
    (tci tca : Idx Γ (.val .bool)) (ti ta tj tb : Idx Γ (.val p))
    (mapCI : m.slot ci = ⟨.val .bool,tci⟩) (mapCA : m.slot ca = ⟨.val .bool,tca⟩)
    (mapI : m.slot i = ⟨.val p,ti⟩) (mapA : m.slot a = ⟨.val p,ta⟩)
    (mapJ : m.slot j = ⟨.val p,tj⟩) (mapB : m.slot b = ⟨.val p,tb⟩)
    (sourceTail : Source.RItems E [] M k srcΓ outΓ)
    (targetTail : Prog C (.val .bool :: Γ) (.val .bool :: Γ)) :
    let choice : Bool := TEnv.get tca target.env
    (Source.execS G F (fuel+8) nps ph (M := M)
      (statement (k := k) ci ca i a j b sourceTail) source.1).run (.nil,source.2) =
      (.ok (Source.Out.ret (ConditionalAssignments.sourceAfter source ci choice i a j b).1),(.nil,source.2)) ∧
    (code tci tca ti ta tj tb targetTail).run target =
      .ok ⟨ConditionalReturn.reached target tci choice ti ta tj tb,List.prefix_refl _⟩ ∧
    (m.wk (Thin.drop (t := .val .bool) .refl)).Related R (ConditionalAssignments.sourceAfter source ci choice i a j b).1
      (ConditionalReturn.reached target tci choice ti ta tj tb).env ∧
    TEnv.get .here (ConditionalReturn.reached target tci choice ti ta tj tb).env = true ∧
    (ConditionalReturn.reached target tci choice ti ta tj tb).glob = target.glob := by
  rcases ConditionalReturn.correct G F fuel nps ph (M := M) (k := k)
    source target m R aligned boolReflect ci ca i a j b tci tca ti ta tj tb
    mapCI mapCA mapI mapA mapJ mapB with ⟨_,_,related,flag,globals⟩
  have read : source.1.get ca = .bool (TEnv.get tca target.env) :=
    boolReflect _ _ (ContextMap.value_at m R source.1 target.env aligned ca tca mapCA)
  exact ⟨source_run G F fuel nps ph source ci ca _ i a j b sourceTail read,
    target_run target tci tca _ ti ta tj tb targetTail rfl,related,flag,globals⟩

end Solidity.Lowering.G19.ConditionalReturnContinuation
