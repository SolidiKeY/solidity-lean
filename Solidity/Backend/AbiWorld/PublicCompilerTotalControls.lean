import Solidity.Backend.AbiWorld.PublicCompilerTotal

/-! Controls for `PublicCompilerTotal`: an inhabited domain program using a
storage read, a mapping write, a loop, a branch, a revert and a single-value
internal call is accepted through the theorem and, independently, by kernel
evaluation of the public entry. Negative controls show each recorded side
condition names a real refusal of that entry, so the domain is not the
compiler's own acceptance test widened by hand. -/
namespace Solidity.Backend.AbiWorld.PublicCompilerTotalControls
open Solidity.Evm Solidity.Backend.AbiWorld.PublicCompilerTotal

def C : Contract :=
  { vars := [("total", .prim .uint), ("balances", .ref (.mapping .uint (.prim .uint)))] }

abbrev Γ₀ : Ctx := []
abbrev Γ₁ : Ctx := [.val .uint]

def total : Solidity.Loc C Γ₁ (.prim .uint) := .root "total" rfl

def x : Solidity.Val C Γ₁ .uint := .simple (.local .here)

def lit (n : Nat) (h : PrimTy.uint.inRange n = true := by decide) : Solidity.Val C Γ₁ .uint :=
  .simple (.lit n h)

/-- `function f(uint p) returns (uint r) { r = p + 1; }`, frame `[r, p]`. -/
def fBody : Solidity.Prog C ([.val .uint] ++ [.val .uint]) ([.val .uint] ++ [.val .uint]) :=
  .cons (.assignLocal .here
    (.binop .add rfl rfl (.simple (.local (.there .here))) (.simple (.lit 1 (by decide))))) .nil

def fArgs : Solidity.Args C Γ₁ [.val .uint] := .snoc .nil .uint (.user "p") x

/-- `uint x = total; while (x < 3) { x += 1; }
if (x == 3) { balances[x] = x; } else { revert(); } x = f(x);` -/
def program : Solidity.Prog C Γ₀ Γ₁ :=
  .cons (.declLocal .uint (.user "x") (some (.read (.root "total" rfl)))) <|
  .cons (.loop .auto (.binop .lt rfl rfl x (lit 3))
    (.cons (.opAssign .add rfl rfl (.local .here) (lit 1)) .nil)) <|
  .cons (.ite (.binop .eqB rfl rfl x (lit 3))
    (.cons (.assign (.index .map (.loc (.root "balances" rfl)) x) (.val x)) .nil)
    (.cons .revert .nil)) <|
  .cons (.call "f" fArgs (.val .uint (.user "r") (some .here)) fBody) .nil

theorem program_ok : ProgOk program :=
  .cons (.declSome _ _ (.read (.root _ _))) <|
  .cons (.loop _ (.binop _ _ _ (by decide) (.local _) (.lit _ _))
    (.cons (.opAssign _ _ _ _ (.lit _ _)) .nil)) <|
  .cons (.ite (.binop _ _ _ (by decide) (.local _) (.lit _ _))
    (.cons (.assign (.map (.loc (.root _ _)) (.local _)) (.local _)) .nil)
    (.cons .revert .nil)) <|
  .cons (.callVal _ _ _ _ (.snoc _ _ .nil (.local _))
    (.cons (.assignLocal _ (.binop _ _ _ (by decide) (.local _) (.lit _ _))) .nil)) .nil

/-- Acceptance through the totality theorem, at an arbitrary base. -/
theorem program_accepted (b : Nat) : (Compiler.compile b (Frag.init Γ₀) program).isSome = true :=
  compile_isSome b _ program_ok

/-- Independent kernel evaluation of the same public entry agrees. -/
theorem program_kernel : (Compiler.compile 0 (Frag.init Γ₀) program).isSome = true := by
  decide +kernel

/-- The accepted code is not empty. -/
theorem program_code_nonempty :
    0 < ((Compiler.compile 0 (Frag.init Γ₀) program).map (·.code.length)).getD 0 := by
  decide +kernel

/-- The `Sim` premise of `compile_agrees` is met by the published fresh
contract (`Sim.init`), so the observation is reached, not vacuous. -/
theorem program_agrees_fresh : ∃ result, Compiler.compile 0 (Frag.init Γ₀) program = some result ∧
    ∀ (frame : Nat) (base : Nat → Fin W), result.Agrees 1 frame base
      (freshT C 0 W_pos ⟨0, W_pos⟩) (Machine.init (fun _ => 0) ⟨0, W_pos⟩) := by
  obtain ⟨result, accepted, agrees⟩ := compile_agrees 0 (Frag.init Γ₀) program_ok
  exact ⟨result, accepted, fun frame base =>
    agrees 1 frame base _ _ (Sim.init C 0 W_pos (fun _ => 0) ⟨0, W_pos⟩ rfl) (by unfold Lmax; decide)⟩

/-! ## Negative controls: each side condition is a real refusal -/

/-- `x & 1` at `int` is typed but refused. -/
def signedAnd : Solidity.Prog C Γ₀ Γ₀ :=
  .cons (.require (.binop .eqB rfl rfl
    (.binop .band rfl rfl (.simple (.lit 1 (by decide)) : Solidity.Val C Γ₀ .int)
      (.simple (.lit 1 (by decide)))) (.simple (.lit 1 (by decide))))) .nil

theorem signedAnd_refused : (Compiler.compile 0 (Frag.init Γ₀) signedAnd).isNone = true := by
  decide +kernel

/-- `address(this).balance` is refused. -/
def selfBalance : Solidity.Prog C Γ₀ Γ₀ :=
  .cons (.require (.binop .eqB rfl rfl
    (.simple (.env .selfBalance rfl) : Solidity.Val C Γ₀ .uint) (.simple (.lit 0 (by decide))))) .nil

theorem selfBalance_refused :
    (Compiler.compile 0 (Frag.init Γ₀) selfBalance).isNone = true := by
  decide +kernel

/-- The domain is not every program: the refusals stay outside it. -/
theorem signedAnd_outside : ¬ ProgOk signedAnd := fun h =>
  absurd (compile_isSome 0 (Frag.init Γ₀) h) (by rw [Option.isSome_iff_ne_none,
    ← Option.isNone_iff_eq_none.mp signedAnd_refused]; exact fun e => e rfl)

/-- info: 'Solidity.Backend.AbiWorld.PublicCompilerTotal.compile_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms compile_core

/-- info: 'Solidity.Backend.AbiWorld.PublicCompilerTotal.compile_agrees' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms compile_agrees

end Solidity.Backend.AbiWorld.PublicCompilerTotalControls
