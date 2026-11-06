import Solidity.Source.Agreement.BoolSlotReadWrite
import Solidity.Source.Agreement.BoolSlotToggleControls

/-! Concrete two-update executions at an arbitrary existing boolean slot.
Intermediate locals are derived from actual checked interpreter runs. -/
namespace Solidity.Source.Agreement
variable {E : Env} {C : Contract} {R : List STy} {M : Bool} {k : SCtx}

/-- Forward normal sequencing of actual Source runs, allowing a declaration
between contexts. It observes execution; concrete clients supply both runs. -/
theorem source_cons_normal_run {Γ₀ Γ₁ Γ₂ : RCtx} (G : Glob E) (F : Fr)
    (n nps : Nat) (ph : Option (Ph E)) (s : RStmt E R M k Γ₀ Γ₁)
    (rest : RItems E R M k Γ₁ Γ₂) (ls : Locals E.layout Γ₀)
    (mid : Locals E.layout Γ₁) (last : Locals E.layout Γ₂)
    (st midSt lastSt : St E)
    (headRun : (execS G F n nps ph s ls).run (.nil, st) = (.ok (.normal mid), (.nil, midSt)))
    (tailRun : (execItems G F n nps ph rest mid).run (.nil, midSt) =
      (.ok (.normal last), (.nil, lastSt))) :
    (execItems G F (n+1) nps ph (.stmt s rest) ls).run (.nil, st) =
      (.ok (.normal last), (.nil, lastSt)) := by
  exact source_run_bind_ok (execS G F n nps ph s ls) _
    (.nil, st) (.nil, midSt) (.normal mid) _ headRun
    (source_run_bind_ok (execItems G F n nps ph rest mid) _
      (.nil, midSt) (.nil, lastSt) (.normal last) _ tailRun (by rfl))

/-- Both Source statements read the same actual slot; the second read observes
its first update. Their final locals and nonlocal state are derived, not assumed. -/
theorem bool_double_toggle_source (pre tail : List PrimTy) (b : Bool)
    (G : Glob E) (F : Fr) (n nps : Nat) (ph : Option (Ph E))
    (ls : Locals E.layout (sourceContext (pre ++ .bool::tail))) (st : St E)
    (read : ls.get (sourceBoolSlot tail pre) = .bool b) :
    (execItems G F (n+6) nps ph
      (.stmt (.expr (.assign (.local (sourceBoolSlot tail pre))
        (.unary .not (.local (sourceBoolSlot tail pre)))))
        (.stmt (.expr (.assign (.local (sourceBoolSlot tail pre))
          (.unary .not (.local (sourceBoolSlot tail pre))))) .nil) :
        RItems E R M k (sourceContext (pre ++ .bool::tail))
          (sourceContext (pre ++ .bool::tail))) ls).run (.nil, st) =
      (.ok (.normal ls), (.nil, st)) := by
  let s : RStmt E R M k (sourceContext (pre ++ .bool::tail))
      (sourceContext (pre ++ .bool::tail)) :=
    .expr (.assign (.local (sourceBoolSlot tail pre))
      (.unary .not (.local (sourceBoolSlot tail pre))))
  let mid := ls.set (sourceBoolSlot tail pre) (.bool (!b))
  let last := mid.set (sourceBoolSlot tail pre) (.bool (!(!b)))
  have firstRun : (execS G F (n+5) nps ph s ls).run (.nil, st) =
      (.ok (.normal mid), (.nil, st)) :=
    bool_toggle_source pre tail b G F (n+1) nps ph ls st read
  have nextRead : mid.get (sourceBoolSlot tail pre) = .bool (!b) :=
    bool_slot_source_get_set E.layout pre tail ls (!b)
  have secondRun : (execS G F (n+4) nps ph s mid).run (.nil, st) =
      (.ok (.normal last), (.nil, st)) :=
    bool_toggle_source pre tail (!b) G F n nps ph mid st nextRead
  have nilRun : (execItems G F (n+4) nps ph (.nil : RItems E R M k _ _) last).run
      (.nil, st) = (.ok (.normal last), (.nil, st)) := by rfl
  have tailRun : (execItems G F (n+5) nps ph (.stmt s .nil) mid).run (.nil, st) =
      (.ok (.normal last), (.nil, st)) :=
    source_cons_normal_run G F (n+4) nps ph s .nil mid last last st st st secondRun nilRun
  have fullRun : (execItems G F (n+6) nps ph (.stmt s (.stmt s .nil)) ls).run
      (.nil, st) = (.ok (.normal last), (.nil, st)) :=
    source_cons_normal_run G F (n+5) nps ph s (.stmt s .nil) ls mid last st st st firstRun tailRun
  have restored : last = ls := bool_slot_source_double_not E.layout pre tail ls b read
  simpa only [restored] using fullRun

/-- The actual model program also reads the intervening write and restores its
original state. This concerns local writes, not transaction rollback. -/
theorem bool_double_toggle_model (pre tail : List PrimTy)
    (model : Solidity.State C (modelContext (pre ++ .bool::tail))) :
    Prog.runC
      (.cons (.assignLocal (modelBoolSlot tail pre)
        (.unop .not rfl rfl (.simple (.local (modelBoolSlot tail pre)))) )
        (.cons (.assignLocal (modelBoolSlot tail pre)
          (.unop .not rfl rfl (.simple (.local (modelBoolSlot tail pre))))) .nil)) model =
      .ok ⟨model, List.prefix_refl _⟩ := by
  let after := model.setLocal (modelBoolSlot tail pre)
    (!(TEnv.get (modelBoolSlot tail pre) model.env))
  have restored : after.setLocal (modelBoolSlot tail pre)
      (!(TEnv.get (modelBoolSlot tail pre) after.env)) = model := by
    dsimp only [after]
    cases model
    simp only [Solidity.State.setLocal, bool_slot_model_double_not]
  have ran : Prog.runC
      (.cons (.assignLocal (modelBoolSlot tail pre)
        (.unop .not rfl rfl (.simple (.local (modelBoolSlot tail pre)))) )
        (.cons (.assignLocal (modelBoolSlot tail pre)
          (.unop .not rfl rfl (.simple (.local (modelBoolSlot tail pre))))) .nil)) model =
      .ok ⟨after.setLocal (modelBoolSlot tail pre)
        (!(TEnv.get (modelBoolSlot tail pre) after.env)), List.prefix_refl _⟩ := by rfl
  simpa only [restored] using ran

/-- Both normal-step premises of the old sequence consumer are concrete producers. -/
theorem bool_double_toggle_agree (pre tail : List PrimTy)
    (G : Glob E) (F : Fr) (nps : Nat) (ph : Option (Ph E)) :
    NormalLocalsObligation (C := C) (R := R) (M := M) (k := k)
      (pre ++ .bool::tail) (pre ++ .bool::tail) G F nps ph
      (.stmt (.expr (.assign (.local (sourceBoolSlot tail pre))
        (.unary .not (.local (sourceBoolSlot tail pre)))))
        (.stmt (.expr (.assign (.local (sourceBoolSlot tail pre))
          (.unary .not (.local (sourceBoolSlot tail pre))))) .nil))
      (.cons (.assignLocal (modelBoolSlot tail pre)
        (.unop .not rfl rfl (.simple (.local (modelBoolSlot tail pre)))))
        (.cons (.assignLocal (modelBoolSlot tail pre)
          (.unop .not rfl rfl (.simple (.local (modelBoolSlot tail pre))))) .nil)) := by
  exact normal_two G F nps ph _ _ _ _
    (bool_toggle_step pre tail G F nps ph) (bool_toggle_step pre tail G F nps ph)

end Solidity.Source.Agreement
