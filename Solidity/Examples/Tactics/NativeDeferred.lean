import Solidity.Semantics.NativeDeferred
import Solidity.Syntax.Splice

/-! Native deferred-receiver execution checks. Source elaboration and canonical
source-printer checks are in `Examples/Tactics/NativeDeferredSource.lean`. -/

namespace Solidity.Examples.Tactics.NativeDeferred

def C : Contract := contract!{ uint calls; uint[] values; uint[][] matrix; }

def getter : Prog C [.alias (.array .uint)] [.alias (.array .uint)] :=
  .cons (.incDec .postInc rfl (.root "calls" rfl))
    (.cons (.rebind .here (.path (.loc (.root "values" rfl)))) .nil)

def increment : Prog C [] [.val .uint] :=
  .cons (.declLocal .uint (.fresh "se" 1) none)
    (.cons (.assignIncDec .here .postInc rfl (.root "calls" rfl) rfl) .nil)

def nativeIncrement : Stmt C [] [] :=
  .callReceiverPush "valuesRef" .nil (.user "r") getter increment (.val (.simple (.local .here)))

def observe {Γ : Ctx} (o : TRes (Out C [] Γ)) : Option (Int × Int × Nat) :=
  (do
    let a ← o
    let calls ← Val.evalT a.st (.read (.root "calls" rfl))
    let first ← Val.evalT a.st
      (.read (.index (.arr .dyn) (.loc (.root "values" rfl)) (.simple (.lit 0 rfl))))
    pure (calls.1, first.1, a.st.H.length)).toOption

example : observe (nativeIncrement.run (State.init C)) = some (2, 1, 0) := by decide +kernel

def nativeUnset : Stmt C [] [] :=
  .callReceiverPush "unset" .nil (.user "r") .nil
    (.cons (.assert (.simple (.bool false))) .nil)
    (.val (p := .uint) (.binop .div rfl rfl (.simple (.lit 1 rfl)) (.simple (.lit 0 rfl))))

example : (nativeUnset.run (State.init C)).halt? = some .revert := by decide +kernel

def allocate : Prog C [] [.mem (.array .uint)] :=
  .cons (.declMem (.array .uint) (.fresh "mv" 2) (some (.newArr (.lit 1 rfl) rfl)) rfl rfl) .nil

def nativeAllocate : Stmt C [] [] :=
  .callReceiverPush "valuesRef" .nil (.user "r") getter allocate
    (.val (.read (.root "calls" rfl)))

example : observe (nativeAllocate.run (State.init C)) = some (1, 1, 1) := by decide +kernel

def growingGetter : Prog C [.alias (.array .uint)]
    [.mem (.array .uint), .alias (.array .uint)] :=
  .cons (.declMem (.array .uint) (.fresh "mv" 0) (some (.newArr (.lit 1 rfl) rfl)) rfl rfl)
    (.cons (.incDec .postInc rfl (.root "calls" rfl))
      (.cons (.rebind (.there .here) (.path (.loc (.root "values" rfl)))) .nil))

def nativeBothAllocate : Stmt C [] [] :=
  .callReceiverPush "growingRef" .nil (.user "r") growingGetter allocate
    (.val (.read (.root "calls" rfl)))

example : observe (nativeBothAllocate.run (State.init C)) = some (1, 1, 2) := by decide +kernel

def localIncrement : Prog C [.val .uint] [.val .uint, .val .uint] :=
  .cons (.declLocal .uint (.fresh "se" 1) none)
    (.cons (.assignIncDec .here .postInc rfl (.local (.there .here)) rfl) .nil)

def nativeCallerLocal : Stmt C [.val .uint] [.val .uint] :=
  .callReceiverPush "valuesRef" .nil (.user "r") getter localIncrement
    (.val (.simple (.local .here)))

example : ((nativeCallerLocal.run ((State.init C).push (t := .val .uint) ⟨7, rfl⟩)).map
    (fun a => (a.st.env.1.1, observe (.ok a)))).toOption = some (8, some (1, 7, 0)) := by
  decide +kernel

def matrixGetter : Prog C [.alias (.array (.array .uint))] [.alias (.array (.array .uint))] :=
  .cons (.incDec .postInc rfl (.root "calls" rfl))
    (.cons (.rebind .here (.path (.loc (.root "matrix" rfl)))) .nil)

def memoryCopy : Prog C [] [.mem (.array .uint)] :=
  .cons (.declMem (.array .uint) (.fresh "mv" 2) (some (.newArr (.lit 1 rfl) rfl)) rfl rfl)
    (.cons (.assignMem (.index .dyn (.var .here rfl) (.simple (.lit 0 rfl)))
      (.val (.simple (.lit 47 rfl)))) .nil)

def nativeReference : Stmt C [] [] :=
  .callReceiverPush "matrixRef" .nil (.user "r") matrixGetter memoryCopy
    (.copyMem (.var .here rfl))

def observeReference (o : TRes (Out C [] [])) : Option (Int × Int × Nat) :=
  (do
    let a ← o
    let calls ← Val.evalT a.st (.read (.root "calls" rfl))
    let first ← Val.evalT a.st
      (.read (.index (.arr .dyn)
        (.loc (.index (.arr .dyn) (.loc (.root "matrix" rfl)) (.simple (.lit 0 rfl))))
        (.simple (.lit 0 rfl))))
    pure (calls.1, first.1, a.st.H.length)).toOption

example : observeReference (nativeReference.run (State.init C)) = some (1, 47, 1) := by
  decide +kernel

end Solidity.Examples.Tactics.NativeDeferred
