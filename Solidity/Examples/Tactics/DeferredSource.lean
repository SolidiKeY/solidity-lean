import Solidity.Semantics.DeferredSource
import Solidity.Syntax.Splice

/-! Kernel execution checks for the deferred-operand foundation. These use an
explicit getter-and-capture program; native `f().push(i++)` source support is
still pending. Prefix effects, copy snapshots, caller locals, allocation and
failure order are checked independently of the general agreement theorem. -/

namespace Solidity.Examples.Tactics.DeferredSource

open Solidity.DeferredSource

def ExampleContract : Contract := contract!{
  uint calls; uint[] values; uint[][] matrix;
  function valuesRef() returns (uint[] storage r) { calls++; r = values; }
  function nextValue() returns (uint r) { r = calls; calls++; }
}

def getter := sol[ExampleContract]{ valuesRef(); }

def postIncrement : Operand ExampleContract [] .uint :=
  ⟨[.val .uint], sol[ExampleContract]{ uint captured; captured = calls++; },
    .val (.simple (.local .here))⟩

def preIncrement : Operand ExampleContract [] .uint :=
  ⟨[.val .uint], sol[ExampleContract]{ uint captured; captured = ++calls; },
    .val (.simple (.local .here))⟩

def valueCall : Operand ExampleContract [] .uint :=
  ⟨[.val .uint], sol[ExampleContract]{ uint captured; captured = nextValue(); },
    .val (.simple (.local .here))⟩

def allocating : Operand ExampleContract [] .uint :=
  ⟨[.val .uint, .mem (.array .uint)],
    sol[ExampleContract]{ uint[] memory tmp = new uint[](1); tmp[0] = 41; uint captured = tmp[0]; },
    .val (.simple (.local .here))⟩

def memoryCopy : Operand ExampleContract [] (.ref (.array .uint)) :=
  ⟨[.mem (.array .uint)],
    sol[ExampleContract]{ uint[] memory tmp = new uint[](1); tmp[0] = 47; },
    .copyMem (.var .here rfl)⟩

def storageCopy : Operand ExampleContract [] (.ref (.array .uint)) :=
  ⟨[.val .uint], sol[ExampleContract]{ values.push(calls++); },
    .copy (.loc (.root "values" rfl)) rfl⟩

def trappedValue : Src ExampleContract [] .uint :=
  .val (.binop .div rfl rfl (.simple (.lit 1 rfl)) (.simple (.lit 0 rfl)))

def reverting : Operand ExampleContract [] .uint :=
  ⟨[], sol[ExampleContract]{ require(false); }, trappedValue⟩

def panicking : Operand ExampleContract [] .uint :=
  ⟨[], sol[ExampleContract]{ assert(false); }, trappedValue⟩

def localIncrement : Operand ExampleContract [.val .uint] .uint :=
  ⟨[.val .uint, .val .uint],
    .cons (.declLocal .uint (.user "captured") none)
      (.cons (.assignIncDec .here .postInc rfl (.local (.there .here)) rfl) .nil),
    .val (.simple (.local .here))⟩

def uintOf : SVal .uint → Int
  | .prim n => n.1

def afterGetter (e : Operand ExampleContract [] .uint) : TRes (Int × Int × Nat × Bool) := do
  let a ← getter.run (State.init ExampleContract)
  let x ← (e.wk (.drop .refl)).run a.st
  let n ← Val.evalT x.1.st (.read (.root "calls" rfl))
  pure (uintOf x.2, n.1, x.1.st.H.length, x.1.st.env.1.isSome)

example : (afterGetter postIncrement).toOption = some (1, 2, 0, true) := by decide +kernel
example : (afterGetter preIncrement).toOption = some (2, 2, 0, true) := by decide +kernel
example : (afterGetter valueCall).toOption = some (1, 2, 0, true) := by decide +kernel
example : (afterGetter allocating).toOption = some (41, 1, 1, true) := by decide +kernel
example : (afterGetter reverting).halt? = some .revert := by decide +kernel
example : (afterGetter panicking).halt? = some .panic := by decide +kernel
example : (trappedValue.valueT (State.init ExampleContract)).halt? = some .revert := by decide +kernel

example : ((localIncrement.run
    ((State.init ExampleContract).push (t := .val .uint) ⟨7, rfl⟩)).map
      (fun x => (x.1.st.env.1.1, uintOf x.2))).toOption = some (8, 7) := by
  decide +kernel

example : (((localIncrement.wk (.drop (t := .alias (.array .uint)) .refl)).run
    (((State.init ExampleContract).push (t := .val .uint) ⟨7, rfl⟩).push none)).map
      (fun x => (x.1.st.env.1.isNone, x.1.st.env.2.1.1, uintOf x.2))).toOption =
        some (true, 8, 7) := by
  decide +kernel

def memoryCaller := sol[ExampleContract]{
  uint[] memory beforeCall = new uint[](1); beforeCall[0] = 19;
}

def allocatePastMemory : TRes (Int × Int × Nat) := do
  let a ← memoryCaller.run (State.init ExampleContract)
  let x ← (allocating.wk (.drop .refl)).run a.st
  let n ← Val.evalT x.1.st
    (.readMem (.index .dyn (.var .here rfl) (.simple (.lit 0 rfl))))
  pure (uintOf x.2, n.1, x.1.st.H.length)

example : allocatePastMemory.toOption = some (41, 19, 2) := by decide +kernel

def getterBody : Prog ExampleContract [.alias (.array .uint)] [.alias (.array .uint)] :=
  .cons (.incDec .postInc rfl (.root "calls" rfl))
    (.cons (.rebind .here (.path (.loc (.root "values" rfl)))) .nil)

def observeCapture (e : Operand ExampleContract [] .uint) : TRes (Int × Int × Int × Nat) := do
  let a ← (callProgram "valuesRef" .nil (.user "r") getterBody e).run (State.init ExampleContract)
  let σ := a.st.drop (.push (.push .refl))
  let calls ← Val.evalT σ (.read (.root "calls" rfl))
  let len ← Val.evalT σ (.len (.loc (.root "values" rfl)) rfl)
  let first ← Val.evalT σ
    (.read (.index (.arr .dyn) (.loc (.root "values" rfl)) (.simple (.lit 0 rfl))))
  pure (calls.1, len.1, first.1, σ.H.length)

example : (observeCapture postIncrement).toOption = some (2, 1, 1, 0) := by decide +kernel
example : (observeCapture preIncrement).toOption = some (2, 1, 2, 0) := by decide +kernel
example : (observeCapture valueCall).toOption = some (2, 1, 1, 0) := by decide +kernel
example : (observeCapture allocating).toOption = some (1, 1, 41, 1) := by decide +kernel
example : (observeCapture reverting).halt? = some .revert := by decide +kernel
example : (observeCapture panicking).halt? = some .panic := by decide +kernel

def matrixGetterBody : Prog ExampleContract [.alias (.array (.ref (.array .uint)))]
    [.alias (.array (.ref (.array .uint)))] :=
  .cons (.incDec .postInc rfl (.root "calls" rfl))
    (.cons (.rebind .here (.path (.loc (.root "matrix" rfl)))) .nil)

def observeReferenceCapture (e : Operand ExampleContract [] (.ref (.array .uint))) :
    TRes (Int × Int × Int × Nat) := do
  let a ← (callProgram "matrixRef" .nil (.user "r") matrixGetterBody e).run (State.init ExampleContract)
  let σ := a.st.drop (.push (.push .refl))
  let calls ← Val.evalT σ (.read (.root "calls" rfl))
  let len ← Val.evalT σ (.len (.loc (.root "matrix" rfl)) rfl)
  let first ← Val.evalT σ (.read (.index (.arr .dyn)
    (.loc (.index (.arr .dyn) (.loc (.root "matrix" rfl)) (.simple (.lit 0 rfl))))
    (.simple (.lit 0 rfl))))
  pure (calls.1, len.1, first.1, σ.H.length)

example : (observeReferenceCapture memoryCopy).toOption = some (1, 1, 47, 1) := by decide +kernel
example : (observeReferenceCapture storageCopy).toOption = some (2, 1, 1, 0) := by decide +kernel

example : ((callProgram "unset" .nil (.user "r") .nil panicking).run
    (State.init ExampleContract)).halt? = some .revert := by decide +kernel

example : ((callProgram "reject" .nil (.user "r") (.cons .revert .nil) panicking).run
    (State.init ExampleContract)).halt? = some .revert := by decide +kernel

def growingGetterBody : Prog ExampleContract [.alias (.array .uint)]
    [.mem (.array .uint), .alias (.array .uint)] :=
  .cons (.declMem (.array .uint) (.user "tmp") (some (.newArr (.lit 1 rfl) rfl)) rfl rfl)
    (getterBody.wk (.drop (t := .mem (.array .uint)) .refl)).2.2

def observeGrowing : TRes (Int × Nat) := do
  let a ← (callProgram "growingRef" .nil (.user "r") growingGetterBody allocating).run
    (State.init ExampleContract)
  let first ← Val.evalT a.st
    (.read (.index (.arr .dyn) (.loc (.root "values" rfl)) (.simple (.lit 0 rfl))))
  pure (first.1, a.st.H.length)

example : observeGrowing.toOption = some (41, 2) := by decide +kernel

end Solidity.Examples.Tactics.DeferredSource
