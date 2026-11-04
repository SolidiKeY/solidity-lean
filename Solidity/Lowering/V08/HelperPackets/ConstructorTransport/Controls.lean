import Solidity.Lowering.V08.HelperPackets.ConstructorTransport.Producer

/-! Same-case negative order and uint256 boundary controls. -/
namespace Solidity.Lowering.V08.HelperPackets.ConstructorTransport
open Solidity Source

def wrongBody : Source.RBody E :=
  ⟨[uint],[],false,[uint],[uint,uint],
    .stmt (.expr (.assign (.state savedDecl rfl rfl) (.local .here)))
    (.stmt (.declInit (.state savedDecl rfl) rfl)
    (.stmt (.expr (.assign (.state capturedDecl rfl rfl) (.local .here))) .nil)),[]⟩
def wrongGlobal (p : Roadmap.Pipeline) : Source.Glob E :=
  {global p with prog:={program with ctor:=fun c => if c="Cell" then some wrongBody else none}}
def wrongReached (bytes : Roadmap.Bytes) (n : Int) (h : range n) :=
  write (write (initialized bytes) savedDecl n h) capturedDecl n h

theorem wrong_order_actual (p : Roadmap.Pipeline) (bytes : Roadmap.Bytes) (n : Int) (h : range n) :
    (Source.construct (wrongGlobal p) frame 16 "Cell" (locals n h)).run
      (Source.L0 E,initial bytes) = (.ok (),(Source.L0 E,wrongReached bytes n h)) := by
  cases p <;> rfl

theorem wrong_order_counterexample (bytes : Roadmap.Bytes) (n : Int) (h : range n) (different : n ≠ 7) :
    wrongReached bytes n h ≠ reached bytes n h := by
  intro same
  have scalar := congrArg (fun s : Source.St E =>
    ((s.ex.world.accounts frame.this).storage.read capturedDecl.path).bind (fun v => v.key)) same
  change (some n : Option Int) = some 7 at scalar
  exact different (Option.some.inj scalar)

abbrev maxUint : Int := 2^256-1

theorem boundary_zero (p : Roadmap.Pipeline) :
    (Source.construct (global p) frame 16 "Cell" (locals 0 (by decide +kernel))).run
      (Source.L0 E,initial []) = (.ok (),(Source.L0 E,reached [] 0 (by decide +kernel))) :=
  source_actual p [] 0 (by decide +kernel)

theorem boundary_max (p : Roadmap.Pipeline) :
    (Source.construct (global p) frame 16 "Cell" (locals maxUint (by decide +kernel))).run
      (Source.L0 E,initial [0,255,128]) =
      (.ok (),(Source.L0 E,reached [0,255,128] maxUint (by decide +kernel))) :=
  source_actual p [0,255,128] maxUint (by decide +kernel)

theorem boundary_seven :
    wrongReached [] 7 (by decide +kernel) = reached [] 7 (by decide +kernel) := rfl
def nondefaultInitial (bytes : Roadmap.Bytes) :=
  write (write (initial bytes) savedDecl 17 (by decide +kernel)) capturedDecl 88 (by decide +kernel)
def nondefaultReached (bytes : Roadmap.Bytes) (n : Int) (h : range n) :=
  write (write (write (nondefaultInitial bytes) savedDecl 7 (by decide +kernel)) savedDecl n h)
    capturedDecl 7 (by decide +kernel)

theorem nondefault_actual (p : Roadmap.Pipeline) (bytes : Roadmap.Bytes) (n : Int) (h : range n) :
    (Source.construct (global p) frame 16 "Cell" (locals n h)).run
      (Source.L0 E,nondefaultInitial bytes) = (.ok (),(Source.L0 E,nondefaultReached bytes n h)) := by
  cases p <;> rfl

theorem nondefault_capture (bytes : Roadmap.Bytes) (n : Int) (h : range n) :
    ((nondefaultReached bytes n h).ex.world.accounts frame.this).storage.read capturedDecl.path =
      some (.int 7 (by decide +kernel)) := rfl
end Solidity.Lowering.V08.HelperPackets.ConstructorTransport
