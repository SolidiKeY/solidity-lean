import Solidity.Lowering.G19.ConditionalStatement
import Solidity.Lowering.G19.ReturnTail

/-! A mapped if/else assignment followed by bare return. Reuses V07 branch
transport and G19 statement execution; no second lowering relation. -/
namespace Solidity.Lowering.G19.ConditionalReturn
open Solidity.Lowering.V07

def statement {E : Source.Env} {Γ : Source.RCtx} {τ : Source.STy} {M : Bool} {k : Source.SCtx}
    (ci ca : Source.Idx Γ .bool) (i a j b : Source.Idx Γ τ) : Source.RStmt E [] M k Γ Γ :=
  .block (.stmt (ConditionalStatement.statement ci ca i a j b) (.stmt (.ret rfl) .nil))

def code {C : Contract} {Γ : Ctx} {p : PrimTy} (ci ca : Idx Γ (.val .bool))
    (i a j b : Idx Γ (.val p)) : Prog C Γ (.val .bool :: Γ) :=
  (ConditionalStatement.code ci ca i a j b).join
    (.cons (.declLocal .bool (.user "g19_return") (some (.simple (.bool true)))) .nil)

def reached {C : Contract} {Γ : Ctx} {p : PrimTy} (s : State C Γ)
    (ci : Idx Γ (.val .bool)) (choice : Bool) (i a j b : Idx Γ (.val p)) : State C (.val .bool :: Γ) :=
  (ConditionalAssignments.targetAfter s ci choice i a j b).push (t := .val .bool) true

theorem source_run {E : Source.Env} {Γ : Source.RCtx} {τ : Source.STy}
    (G : Source.Glob E) (F : Source.Fr) (fuel nps : Nat) (ph : Option (Source.Ph E))
    {M : Bool} {k : Source.SCtx} (s : Source.EMState E Γ)
    (ci ca : Source.Idx Γ .bool) (choice : Bool) (i a j b : Source.Idx Γ τ)
    (read : s.1.get ca = .bool choice) :
    (Source.execS G F (fuel+6) nps ph (M := M) (statement (k := k) ci ca i a j b) s.1).run
      (.nil,s.2) =
      (.ok (Source.Out.ret (ConditionalAssignments.sourceAfter s ci choice i a j b).1),(.nil,s.2)) := by
  have prefixRun : (Source.execS G F (fuel+4) nps ph (R := []) (M := M)
      (ConditionalStatement.statement (k := k) ci ca i a j b) s.1).run (.nil,s.2) =
      (.ok (Source.Out.normal (ConditionalAssignments.sourceAfter s ci choice i a j b).1),(.nil,s.2)) :=
    ConditionalStatement.source_run G F fuel nps ph s ci ca choice i a j b read
  have restRun : (Source.execItems G F (fuel+4) nps ph (R := []) (M := M) (k := k)
      (.stmt (.ret rfl) .nil) (ConditionalAssignments.sourceAfter s ci choice i a j b).1).run
      (.nil,s.2) = (.ok (Source.Out.ret (ConditionalAssignments.sourceAfter s ci choice i a j b).1),(.nil,s.2)) := by rfl
  have itemsRun : (Source.execItems G F (fuel+5) nps ph (R := []) (M := M) (k := k)
      (.stmt (ConditionalStatement.statement ci ca i a j b) (.stmt (.ret rfl) .nil)) s.1).run
      (.nil,s.2) = (.ok (Source.Out.ret (ConditionalAssignments.sourceAfter s ci choice i a j b).1),(.nil,s.2)) := by
    rw [Source.execItems,Source.Hoare.run_bind,prefixRun]
    dsimp only
    rw [Source.Hoare.run_bind,restRun]
    simp only [Source.Out.up,ReturnTail.source_locals_restore_self]
    rfl
  rw [statement,Source.execS,Source.Hoare.run_bind,itemsRun]
  simp only [Source.Out.close]
  rfl

theorem target_run {C : Contract} {Γ : Ctx} {p : PrimTy} (s : State C Γ)
    (ci ca : Idx Γ (.val .bool)) (choice : Bool) (i a j b : Idx Γ (.val p))
    (read : TEnv.get ca s.env = choice) :
    (code ci ca i a j b).run s = .ok ⟨reached s ci choice i a j b,List.prefix_refl _⟩ := by
  have prefixRun : (ConditionalStatement.code ci ca i a j b).run s =
      .ok ⟨ConditionalAssignments.targetAfter s ci choice i a j b,List.prefix_refl _⟩ :=
    ConditionalStatement.target_run s ci ca choice i a j b read
  unfold Prog.run at prefixRun
  rw [code,DeferredSource.join_run]
  unfold TRun.seq
  rw [prefixRun]
  rfl


theorem correct {E : Source.Env} {srcΓ : Source.RCtx} {τ : Source.STy}
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
    (mapJ : m.slot j = ⟨.val p,tj⟩) (mapB : m.slot b = ⟨.val p,tb⟩) :
    let choice : Bool := TEnv.get tca target.env
    (Source.execS G F (fuel+6) nps ph (M := M)
      (statement (k := k) ci ca i a j b) source.1).run (.nil,source.2) =
      (.ok (Source.Out.ret (ConditionalAssignments.sourceAfter source ci choice i a j b).1),(.nil,source.2)) ∧
    (code tci tca ti ta tj tb).run target =
      .ok ⟨reached target tci choice ti ta tj tb,List.prefix_refl _⟩ ∧
    (m.wk (Thin.drop (t := .val .bool) .refl)).Related R (ConditionalAssignments.sourceAfter source ci choice i a j b).1
      (reached target tci choice ti ta tj tb).env ∧
    TEnv.get .here (reached target tci choice ti ta tj tb).env = true ∧
    (reached target tci choice ti ta tj tb).glob = target.glob := by
  dsimp only
  have read : source.1.get ca = .bool (TEnv.get tca target.env) :=
    boolReflect _ _ (ContextMap.value_at m R source.1 target.env aligned ca tca mapCA)
  rcases ConditionalStatement.correct G F fuel nps ph (returns := []) (M := M) (k := k)
    source target m R aligned boolReflect ci ca i a j b tci tca ti ta tj tb
    mapCI mapCA mapI mapA mapJ mapB with ⟨_,_,related,globals⟩
  have post : (m.wk (Thin.drop (t := .val .bool) .refl)).Related R
      (ConditionalAssignments.sourceAfter source ci (TEnv.get tca target.env) i a j b).1
      (reached target tci (TEnv.get tca target.env) ti ta tj tb).env := by
    intro σ index
    exact related index
  exact ⟨source_run G F fuel nps ph source ci ca _ i a j b read,
    target_run target tci tca _ ti ta tj tb rfl,post,rfl,globals⟩

theorem source_zero {E : Source.Env} {Γ : Source.RCtx} {τ : Source.STy}
    (G : Source.Glob E) (F : Source.Fr) (nps : Nat) (ph : Option (Source.Ph E))
    {M : Bool} {k : Source.SCtx} (s : Source.EMState E Γ)
    (ci ca : Source.Idx Γ .bool) (i a j b : Source.Idx Γ τ) :
    Source.execS G F 0 nps ph (M := M) (statement (k := k) ci ca i a j b) s.1 =
      Source.EM.halt .timeout := by rfl

end Solidity.Lowering.G19.ConditionalReturn
