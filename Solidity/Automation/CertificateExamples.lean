import Solidity.Automation.Certificate

namespace Solidity.Automation
open Decide
variable {C : Contract}

example : Leaf.spine (C := C) (.eq .tt .tt) = true := rfl
example : Leaf.spine (C := C) (.eq (.lit (p := .bool) false) .tt) = false := rfl
example : Leaf.spine (C := C) (.eq (p := .uint) (.var 0) (.var 0)) = false := rfl
example : Leaf.spine (C := C) (.not .tt) = false := rfl
example : Leaf.spine (C := C) (.and .tt (.not .tt)) = false := rfl
example : Leaf.spine (C := C) (.imp (.not .tt) (.not .tt)) = false := rfl
example : Leaf.prefer (some false) (fun _ => some true) = some true := rfl
example : Leaf.prefer none (fun _ => some true) = some true := rfl
example : Leaf.prefer (some true) (fun _ => none) = some true := rfl

/-- A real conditional-join step, followed by a structural local leaf witness.
No walk search, general closer, or `verified` certificate constructor is used. -/
def joinedBranch : Certificate C .all .nil
    (.all "b" .bool
      (.modal .box (.cons (.ite (.simple (.local .here)) .nil .nil) .nil) .nil .tt)) :=
  .allIntro (.update rfl rfl (.leaf _ rfl (.spine rfl) rfl))

theorem joinedBranch_proved : Proves C .all [] .nil
    (.all "b" .bool
      (.modal .box (.cons (.ite (.simple (.local .here)) .nil .nil) .nil) .nil .tt)) :=
  joinedBranch.proves

def trueLeaf : Certificate C .all .nil (.tt : Fml C []) :=
  .leaf .tt rfl (.spine rfl) rfl

example : Proves C .all [] .nil (.tt : Fml C []) :=
  Certificate.useOr (some trueLeaf) (fun _ => trueLeaf.proves)

example : Proves C .all [] .nil (.tt : Fml C []) :=
  Certificate.useOr none (fun _ => trueLeaf.proves)

end Solidity.Automation
