import Solidity.Frontend.Testing

/-!
# A primitive push through a complex receiver

The source fixture checks declaration and assignment forms, nested array lengths,
and a false postcondition. These execution theorems use the typed interpreter
at the initial state. General-state derivation coverage is tracked separately
by the migration runner; an open proof-search leaf is not a counterexample.
-/

solc_import "../../../tests/solc/PushReceiver.ast.json" hash 0x22918c5980ba66a2
  as Solkey.Migration.PushReceiver testing

namespace Solidity.Examples.Tactics.PushReceiver

/-- `y = matrix[0 + 0].push()` retains its complex receiver as one statement. -/
private def complexBinding : Stmt Solkey.Migration.PushReceiver [.val .uint] [.val .uint] :=
  .assignLocalPush .here (.loc (.index (.arr .dyn) (.loc (.root "matrix" rfl))
    (.binop .add rfl rfl (.simple (.lit 0 rfl)) (.simple (.lit 0 rfl)))))

/-- Even `matrix[0]` is a path captured into a simple storage alias. -/
private def literalBinding : Stmt Solkey.Migration.PushReceiver [.val .uint] [.val .uint] :=
  .assignLocalPush .here (.loc (.index (.arr .dyn) (.loc (.root "matrix" rfl))
    (.simple (.lit 0 rfl))))

/-- `y = row.push()` through a storage alias updates directly. -/
private def simpleBinding : Stmt Solkey.Migration.PushReceiver
    [.alias (.array (.prim .uint)), .val .uint]
    [.alias (.array (.prim .uint)), .val .uint] :=
  .assignLocalPush (.there .here) (.alias .here)

/-- info: Solidity.Taclet.localValuePush_unfold_leftFstReceiver -/
#guard_msgs in #rule_of .box complexBinding

/-- info: Solidity.Taclet.localValuePush_unfold_leftFstReceiver -/
#guard_msgs in #rule_of .diamond complexBinding

/-- info: Solidity.Taclet.localValuePush_unfold_leftFstReceiver -/
#guard_msgs in #rule_of .box literalBinding

/-- info: Solidity.Taclet.storageLocalPrimitivePushBind -/
#guard_msgs in #rule_of .box simpleBinding

private def failingBinding : Rhs Solkey.Migration.PushReceiver [] (.val .uint) :=
  .val (.app2 (.binop .div rfl) (.app0 (.lit ⟨1, rfl⟩)) (.app0 (.lit ⟨0, rfl⟩)))

/-- A failing parallel binding cannot be hidden by a push's exhaustion
shortcut, regardless of the original array's length. -/
theorem exhaustion_keeps_binding_failure (σ : State Solkey.Migration.PushReceiver []) :
    ((Decide.pushLocalExhL Decide.SymS.init
      (.app2 .pushSlot (.app0 .storage)
        (Loc.root (Γ := []) "matrix" rfl).lower) failingBinding).bind
      fun x => x.eval σ Decide.AEnv.dflt) = none := by
  rfl

/-- The nested receiver is captured before both forms of primitive push. -/
theorem nested_initial :
    (Prog.run (State.init Solkey.Migration.PushReceiver) Solkey.Migration.PushReceiver.nested).isOk = true := by
  decide +kernel

/-- The false claim about the appended zero fails in the typed run. -/
theorem falsePost_initial :
    (Prog.run (State.init Solkey.Migration.PushReceiver) Solkey.Migration.PushReceiver.falsePost).isOk = false := by
  decide +kernel

/-- Each incremented index is evaluated once, in both binding forms. -/
theorem effectfulReceiver_initial :
    (Prog.run (State.init Solkey.Migration.PushReceiver)
      Solkey.Migration.PushReceiver.effectfulReceiver).isOk = true := by
  decide +kernel

/-- `y = matrix[y + 0].push()` reads the old target before assigning zero. -/
theorem oldTargetIndex_initial :
    (Prog.run (State.init Solkey.Migration.PushReceiver)
      Solkey.Migration.PushReceiver.oldTargetIndex).isOk = true := by
  decide +kernel

/-- Reading the newly assigned zero as the receiver's index would be wrong. -/
theorem falseTargetIndex_initial :
    (Prog.run (State.init Solkey.Migration.PushReceiver)
      Solkey.Migration.PushReceiver.falseTargetIndex).isOk = false := by
  decide +kernel

/-- A well-formed entry state may contain old data in a reference shadow slot. -/
def dirtyStorage : Storage Solkey.Migration.PushReceiver :=
  .cons (.array .nil
    (.cons (.array (.cons (.prim ⟨9, rfl⟩) .nil) .nil (by decide)) .nil)
    (by decide)) .nil

theorem dirtyStorage_wellformed : dirtyStorage.wtB = true := by decide +kernel

/-- A zero-argument reference push exposes that reused slot as it is: the
old row's element stays, and `nested`'s length assertion fails from this
well-formed entry (solkey: an empty inner array needs a precondition). -/
theorem nested_dirty :
    (Prog.run ((State.init Solkey.Migration.PushReceiver).withStorage dirtyStorage)
      Solkey.Migration.PushReceiver.nested).isOk = false := by
  decide +kernel

/-- The appended mapping slot keeps every stored entry. -/
theorem mappingSlot_kept {K : PrimTy} {V : Ty} (entries : SMap K V) (d : SVal V) :
    (pushSlot (.ref (.mapping K V)) [SVal.map entries d]).1 = SVal.map entries d := rfl

private def matrixPath : SRef Solkey.Migration.PushReceiver
    (.ref (.array (.ref (.array (.prim .uint))))) := .ofRoot "matrix" rfl

private def firstRow : SRef Solkey.Migration.PushReceiver (.ref (.array (.prim .uint))) :=
  matrixPath.index (.arr .dyn) ⟨0, rfl⟩

/-- A written length-only save exposes the old row without resetting it. -/
theorem lengthOnly_keepsRow :
    (((Op2.eval (State.init Solkey.Migration.PushReceiver) .extend (some dirtyStorage)
      (some matrixPath)).bind fun st => st.len firstRow).map Subtype.val) = some 1 := by
  decide +kernel

/-- `pushSlot` is the same length-only save: the old row is kept. -/
theorem pushSlot_keepsRow :
    (((Op2.eval (State.init Solkey.Migration.PushReceiver) .pushSlot (some dirtyStorage)
      (some matrixPath)).bind fun st => st.len firstRow).map Subtype.val) = some 1 := by
  decide +kernel

/-- A fixed array keeps its arity and the entries of its mapping element. -/
theorem fixedMappingSlot_kept {K : PrimTy} {V : Ty} (entries : SMap K V) (d : SVal V) :
    (pushSlot (.ref (.fixed (.ref (.mapping K V)) 1))
      [.fixed (.cons (.map entries d) .nil)]).1 =
      .fixed (.cons (.map entries d) .nil) := rfl

end Solidity.Examples.Tactics.PushReceiver
