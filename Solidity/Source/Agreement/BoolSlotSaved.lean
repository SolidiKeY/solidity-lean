import Solidity.Source.Agreement.BoolSlotRepeated

/-! A saved primitive copy and a subsequent computed update of its original
slot, using fixed existing Source/model code rather than a chosen new literal. -/
namespace Solidity.Source.Agreement
variable {E : Env} {C : Contract} {R : List STy} {M : Bool} {k : SCtx}

/-- Actual Source execution retains the old copy while the original slot takes
its newly computed inverse. The operational lookup is derived by the client. -/
theorem bool_saved_toggle_source (pre tail : List PrimTy) (b : Bool)
    (G : Glob E) (F : Fr) (n nps : Nat) (ph : Option (Ph E))
    (ls : Locals E.layout (sourceContext (pre ++ .bool::tail))) (st : St E)
    (read : ls.get (sourceBoolSlot tail pre) = .bool b) :
    (execItems G F (n+6) nps ph
      (.stmt (.declInit (.local (sourceBoolSlot tail pre)) rfl)
        (.stmt (.expr (.assign (.local (sourceBoolSlot tail (.bool::pre)))
          (.unary .not (.local (sourceBoolSlot tail (.bool::pre)))))) .nil) : RItems E R M k
        (sourceContext (pre ++ .bool::tail)) (sourceContext (.bool::pre ++ .bool::tail)))
      ls).run (.nil, st) =
      (.ok (.normal (.cons (.bool b) (ls.set (sourceBoolSlot tail pre) (.bool (!b))))), (.nil, st)) := by
  let d : RStmt E R M k (sourceContext (pre ++ .bool::tail))
      (sourceContext (.bool::pre ++ .bool::tail)) :=
    .declInit (.local (sourceBoolSlot tail pre)) rfl
  let s : RStmt E R M k (sourceContext (.bool::pre ++ .bool::tail))
      (sourceContext (.bool::pre ++ .bool::tail)) :=
    .expr (.assign (.local (sourceBoolSlot tail (.bool::pre)))
      (.unary .not (.local (sourceBoolSlot tail (.bool::pre)))))
  let mid := Locals.cons (.bool b) ls
  let last := Locals.cons (.bool b) (ls.set (sourceBoolSlot tail pre) (.bool (!b)))
  have firstRun : (execS G F (n+5) nps ph d ls).run (.nil, st) =
      (.ok (.normal mid), (.nil, st)) := by
    simpa only [read] using (bool_read_init_source (R := R) (M := M) (k := k)
      pre tail G F (n+3) nps ph ls st)
  have nextRead : mid.get (sourceBoolSlot tail (.bool::pre)) = .bool b := read
  have secondRun : (execS G F (n+4) nps ph s mid).run (.nil, st) =
      (.ok (.normal last), (.nil, st)) :=
    bool_toggle_source (.bool::pre) tail b G F n nps ph mid st nextRead
  have nilRun : (execItems G F (n+4) nps ph (.nil : RItems E R M k _ _) last).run
      (.nil, st) = (.ok (.normal last), (.nil, st)) := by rfl
  have tailRun : (execItems G F (n+5) nps ph (.stmt s .nil) mid).run (.nil, st) =
      (.ok (.normal last), (.nil, st)) :=
    source_cons_normal_run G F (n+4) nps ph s .nil mid last last st st st secondRun nilRun
  exact source_cons_normal_run G F (n+5) nps ph d (.stmt s .nil)
    ls mid last st st st firstRun tailRun

/-- The actual model RHS reads the original slot under the saved binding;
that saved head retains its old value, independently of the new write. -/
theorem bool_saved_toggle_model (pre tail : List PrimTy) (name : Var)
    (model : Solidity.State C (modelContext (pre ++ .bool::tail))) :
    Prog.runC
      (.cons (.declLocal .bool name (some (.simple (.local (modelBoolSlot tail pre)))))
        (.cons (.assignLocal (modelBoolSlot tail (.bool::pre))
          (.unop .not rfl rfl (.simple (.local (modelBoolSlot tail (.bool::pre)))))) .nil)) model =
      .ok ⟨(model.setLocal (modelBoolSlot tail pre)
        (!(TEnv.get (modelBoolSlot tail pre) model.env))).push
        (TEnv.get (modelBoolSlot tail pre) model.env), List.prefix_refl _⟩ := by
  rfl

/-- Both sequence premises are supplied by concrete producers on the actual
intermediate context; no desired operand or reached state is a premise. -/
theorem bool_saved_toggle_agree (pre tail : List PrimTy) (name : Var)
    (G : Glob E) (F : Fr) (nps : Nat) (ph : Option (Ph E)) :
    NormalLocalsObligation (C := C) (R := R) (M := M) (k := k)
      (pre ++ .bool::tail) (.bool::pre ++ .bool::tail) G F nps ph
      (.stmt (.declInit (.local (sourceBoolSlot tail pre)) rfl)
        (.stmt (.expr (.assign (.local (sourceBoolSlot tail (.bool::pre)))
          (.unary .not (.local (sourceBoolSlot tail (.bool::pre)))))) .nil))
      (.cons (.declLocal .bool name (some (.simple (.local (modelBoolSlot tail pre)))))
        (.cons (.assignLocal (modelBoolSlot tail (.bool::pre))
          (.unop .not rfl rfl (.simple (.local (modelBoolSlot tail (.bool::pre)))))) .nil)) := by
  exact normal_two G F nps ph _ _ _ _
    (bool_read_init_step pre tail name G F nps ph)
    (bool_toggle_step (.bool::pre) tail G F nps ph)

end Solidity.Source.Agreement
