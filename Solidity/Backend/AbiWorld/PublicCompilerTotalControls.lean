import Solidity.Backend.AbiWorld.PublicCompilerTotal

/-! Controls for `PublicCompilerTotal`: an inhabited domain program using a
storage read, a storage alias with a rebind, a mapping write through it,
root and indexed storage `+=`, `++`, signed `&`, `|`, `^`, a loop, a branch, a revert and a
single-value internal call is accepted through the theorem and,
independently, by kernel evaluation of the public entry. A signed `&`
formerly refused is now accepted. Negative controls kernel-observe refusals
for two remaining side conditions (self balance, a non-`uint` mapping key);
the word-fit conditions are refusals of `locIn` by its code without a kernel
control. H96: an alias bound through an array index (`row = rows[x]`, rebound
inside a loop) is accepted by the theorem and by kernel evaluation, with a
fresh-machine `Agrees` witness; a kind-changing rebind in a loop and a read of
an unset alias are kernel-observed refusals. -/
namespace Solidity.Backend.AbiWorld.PublicCompilerTotalControls
open Solidity.Evm Solidity.Backend.AbiWorld.PublicCompilerTotal

def C : Contract :=
  { vars := [("total", .prim .uint), ("balances", .ref (.mapping .uint (.prim .uint))),
    ("signed", .ref (.mapping .int (.prim .uint))),
    ("rows", .ref (.array (.ref (.array (.prim .uint))))), ("list", .ref (.array (.prim .uint))),
    ("mrows", .ref (.array (.ref (.mapping .uint (.ref (.array (.prim .uint))))))),
    ("frows", .ref (.fixed (.ref (.array (.prim .uint))) 3))] }

abbrev Γ₀ : Ctx := []
abbrev Γ₁ : Ctx := [.val .uint]
abbrev M : RefTy := .mapping .uint (.prim .uint)
abbrev Γ₂ : Ctx := [.alias M, .val .uint]

def x : Solidity.Val C Γ₂ .uint := .simple (.local (.there .here))

def bs : Solidity.SPath C Γ₂ (.ref M) := .alias .here

def lit (n : Nat) (h : PrimTy.uint.inRange n = true := by decide) : Solidity.Val C Γ₂ .uint :=
  .simple (.lit n h)

/-- `int(x)`. -/
def sx : Solidity.Val C Γ₂ .int := .unop .toInt rfl rfl x

/-- `function f(uint p) returns (uint r) { r = p + 1; }`, frame `[r, p]`. -/
def fBody : Solidity.Prog C ([.val .uint] ++ [.val .uint]) ([.val .uint] ++ [.val .uint]) :=
  .cons (.assignLocal .here
    (.binop .add rfl rfl (.simple (.local (.there .here))) (.simple (.lit 1 (by decide))))) .nil

def fArgs : Solidity.Args C Γ₂ [.val .uint] := .snoc .nil .uint (.user "p") x

/-- `uint x = total; mapping(uint => uint) storage bs = balances;
while (x < 3) { x += 1; }
if (x == 3) { bs[x] = x; total += x; bs = balances; bs[x] += 1; } else { revert(); }
++total; require((int(x) & int(x)) == int(x));
require((int(x) | (int(x) ^ int(x))) == int(x)); x = f(x);` -/
def program : Solidity.Prog C Γ₀ Γ₂ :=
  .cons (.declLocal .uint (.user "x") (some (.read (.root "total" rfl)))) <|
  .cons (.declStorage M (.user "bs") (some (.path (.loc (.root "balances" rfl))))) <|
  .cons (.loop .auto (.binop .lt rfl rfl x (lit 3))
    (.cons (.opAssign .add rfl rfl (.local (.there .here)) (lit 1)) .nil)) <|
  .cons (.ite (.binop .eqB rfl rfl x (lit 3))
    (.cons (.assign (.index .map bs x) (.val x)) <|
     .cons (.opAssign .add rfl rfl (.root "total" rfl) x) <|
     .cons (.rebind .here (.path (.loc (.root "balances" rfl)))) <|
     .cons (.opAssign .add rfl rfl (.index .map bs (.local (.there .here))) (lit 1)) .nil)
    (.cons .revert .nil)) <|
  .cons (.incDec .preInc rfl (.root "total" rfl)) <|
  .cons (.require (.binop .eqB rfl rfl (.binop .band rfl rfl sx sx) sx)) <|
  .cons (.require (.binop .eqB rfl rfl (.binop .bor rfl rfl sx (.binop .bxor rfl rfl sx sx)) sx)) <|
  .cons (.call "f" fArgs (.val .uint (.user "r") (some (.there .here))) fBody) .nil

theorem program_ok : ProgOk [] program :=
  .cons (.declSome _ _ (.read (.root _ _))) <|
  .cons (.declStorage _ _ (.root _ _)) <|
  .cons (.loop _ (.binop _ _ _ (.local _) (.lit _ _))
    (.cons (.opAssign _ _ _ (.local _) (.lit _ _)) .nil)) <|
  .cons (.ite (.binop _ _ _ (.local _) (.lit _ _))
    (.cons (.assign (.map (.alias _) (.local _)) (.local _)) <|
     .cons (.opAssign _ _ _ (.root _ _) (.local _)) <|
     .cons (.rebind _ rfl (.root _ _)) <|
     .cons (.opAssign _ _ _ (.index (.map (.alias _) (.local _))) (.lit _ _)) .nil)
    (.cons .revert .nil)) <|
  .cons (.incDec _ _ (.root _ _)) <|
  .cons (.require (.binop _ _ _ (.binop _ _ _ (.unop _ _ _ (.local _)) (.unop _ _ _ (.local _)))
    (.unop _ _ _ (.local _)))) <|
  .cons (.require (.binop _ _ _ (.binop _ _ _ (.unop _ _ _ (.local _))
    (.binop _ _ _ (.unop _ _ _ (.local _)) (.unop _ _ _ (.local _)))) (.unop _ _ _ (.local _)))) <|
  .cons (.callVal _ _ _ _ (.snoc _ _ .nil (.local _))
    (.cons (.assignLocal _ (.binop _ _ _ (.local _) (.lit _ _))) .nil)) .nil

/-- Acceptance through the totality theorem, at an arbitrary base. -/
theorem program_accepted (b : Nat) : (Compiler.compile b (Frag.init Γ₀) program).isSome = true :=
  compile_init b program_ok

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
  obtain ⟨result, accepted, agrees⟩ := compile_agrees 0 (Matches.init Γ₀) program_ok
  exact ⟨result, accepted, fun frame base =>
    agrees 1 frame base _ _ (Sim.init C 0 W_pos (fun _ => 0) ⟨0, W_pos⟩ rfl) (by unfold Lmax; decide)⟩

/-! ## Aliases bound through an array index (H96) -/

abbrev A : RefTy := .array (.prim .uint)
abbrev Γa : Ctx := [.alias A, .val .uint]

def xa : Solidity.Val C Γa .uint := .simple (.local (.there .here))

def row : Solidity.SPath C Γa (.ref A) := .alias .here

def litA (n : Nat) (h : PrimTy.uint.inRange n = true := by decide) : Solidity.Val C Γa .uint :=
  .simple (.lit n h)

/-- `rows[i]`, an indexed path. -/
def rowsAt {Γ : Ctx} (i : Solidity.Val C Γ .uint) : Solidity.SPath C Γ (.ref A) :=
  .loc (.index (.arr .dyn) (.loc (.root "rows" rfl)) i)

/-- `uint x = 2; uint[] storage row = rows[x];
while (x < 3) { row[0] += x; row = rows[x]; x += 1; }
if (x == 3) { row = rows[0]; } else { revert(); }
row[1] = x; require(row[0] == row[0]);` -/
def indexed : Solidity.Prog C Γ₀ Γa :=
  .cons (.declLocal .uint (.user "x") (some (.simple (.lit 2 (by decide))))) <|
  .cons (.declStorage A (.user "row") (some (.path (rowsAt (.simple (.local .here)))))) <|
  .cons (.loop .auto (.binop .lt rfl rfl xa (litA 3))
    (.cons (.opAssign .add rfl rfl (.index (.arr .dyn) row (.lit 0 (by decide))) xa) <|
     .cons (.rebind .here (.path (rowsAt xa))) <|
     .cons (.opAssign .add rfl rfl (.local (.there .here)) (litA 1)) .nil)) <|
  .cons (.ite (.binop .eqB rfl rfl xa (litA 3))
    (.cons (.rebind .here (.path (rowsAt (litA 0)))) .nil)
    (.cons .revert .nil)) <|
  .cons (.assign (.index (.arr .dyn) row (litA 1)) (.val xa)) <|
  .cons (.require (.binop .eqB rfl rfl (.read (.index (.arr .dyn) row (litA 0)))
    (.read (.index (.arr .dyn) row (litA 0))))) .nil

theorem indexed_ok : ProgOk [] indexed :=
  .cons (.declSome _ _ (.lit _ _)) <|
  .cons (.declIndexed _ _ (.loc (.dyn (.loc (.root _ _)) (.local _))) .dyn) <|
  .cons (.loop _ (.binop _ _ _ (.local _) (.lit _ _))
    (.cons (.opAssign _ _ _ (.index (.dyn (.alias _) (.lit _ _))) (.local _)) <|
     .cons (.rebindIndexed _ rfl (.loc (.dyn (.loc (.root _ _)) (.local _))) .dyn) <|
     .cons (.opAssign _ _ _ (.local _) (.lit _ _)) .nil)) <|
  .cons (.ite (.binop _ _ _ (.local _) (.lit _ _))
    (.cons (.rebindIndexed _ rfl (.loc (.dyn (.loc (.root _ _)) (.lit _ _))) .dyn) .nil)
    (.cons .revert .nil)) <|
  .cons (.assign (.dyn (.alias _) (.lit _ _)) (.local _)) <|
  .cons (.require (.binop _ _ _ (.read (.dyn (.alias _) (.lit _ _)))
    (.read (.dyn (.alias _) (.lit _ _))))) .nil

theorem indexed_accepted (b : Nat) : (Compiler.compile b (Frag.init Γ₀) indexed).isSome = true :=
  compile_init b indexed_ok

theorem indexed_kernel : (Compiler.compile 0 (Frag.init Γ₀) indexed).isSome = true := by
  decide +kernel

/-- Joint satisfiability: the fresh contract meets every premise of
`compile_agrees` for the indexed-alias program. -/
theorem indexed_agrees_fresh : ∃ result, Compiler.compile 0 (Frag.init Γ₀) indexed = some result ∧
    ∀ (frame : Nat) (base : Nat → Fin W), result.Agrees 1 frame base
      (freshT C 0 W_pos ⟨0, W_pos⟩) (Machine.init (fun _ => 0) ⟨0, W_pos⟩) := by
  obtain ⟨result, accepted, agrees⟩ := compile_agrees 0 (Matches.init Γ₀) indexed_ok
  exact ⟨result, accepted, fun frame base =>
    agrees 1 frame base _ _ (Sim.init C 0 W_pos (fun _ => 0) ⟨0, W_pos⟩ rfl) (by unfold Lmax; decide)⟩

/-- `uint x = 1; uint[] storage row = rows[x]; uint[] storage r2 = row;
uint[] storage m = mrows[x][x]; uint[] storage f = frows[x];
require(r2[0] == m[0]); f[0] = x;`: an alias of an indexed alias, a mapping
inside an array element, and a fixed array element. -/
def nested : Solidity.Prog C Γ₀ [.alias A, .alias A, .alias A, .alias A, .val .uint] :=
  .cons (.declLocal .uint (.user "x") (some (.simple (.lit 1 (by decide))))) <|
  .cons (.declStorage A (.user "row") (some (.path (rowsAt (.simple (.local .here)))))) <|
  .cons (.declStorage A (.user "r2") (some (.path (.alias .here)))) <|
  .cons (.declStorage A (.user "m") (some (.path (.loc (.index .map
    (.loc (.index (.arr .dyn) (.loc (.root "mrows" rfl)) (.simple (.local (.there (.there .here))))))
    (.simple (.local (.there (.there .here))))))))) <|
  .cons (.declStorage A (.user "f") (some (.path (.loc (.index (.arr .fixed)
    (.loc (.root "frows" rfl)) (.simple (.local (.there (.there (.there .here)))))))))) <|
  .cons (.require (.binop .eqB rfl rfl
    (.read (.index (.arr .dyn) (.alias (.there (.there .here))) (.simple (.lit 0 (by decide)))))
    (.read (.index (.arr .dyn) (.alias (.there .here)) (.simple (.lit 0 (by decide))))))) <|
  .cons (.assign (.index (.arr .dyn) (.alias .here) (.simple (.lit 0 (by decide))))
    (.val (.simple (.local (.there (.there (.there (.there .here)))))))) .nil

theorem nested_ok : ProgOk [] nested :=
  .cons (.declSome _ _ (.lit _ _)) <|
  .cons (.declIndexed _ _ (.loc (.dyn (.loc (.root _ _)) (.local _))) .dyn) <|
  .cons (.declIndexed _ _ (.alias _) (.alias _ rfl)) <|
  .cons (.declIndexed _ _ (.loc (.map (.loc (.dyn (.loc (.root _ _)) (.local _))) (.local _)))
    (.map .dyn)) <|
  .cons (.declIndexed _ _ (.loc (.fixed (by decide) (.loc (.root _ _)) (.local _))) .fixed) <|
  .cons (.require (.binop _ _ _ (.read (.dyn (.alias _) (.lit _ _)))
    (.read (.dyn (.alias _) (.lit _ _))))) <|
  .cons (.assign (.dyn (.alias _) (.lit _ _)) (.local _)) .nil

theorem nested_accepted : (Compiler.compile 0 (Frag.init Γ₀) nested).isSome = true :=
  compile_init 0 nested_ok

theorem nested_kernel : (Compiler.compile 0 (Frag.init Γ₀) nested).isSome = true := by
  decide +kernel

/-- Rebinding an indexed alias to a plain path inside a loop changes its kind:
the loop fixed-point check refuses it, and the judgement excludes it. -/
def kindChange : Solidity.Prog C Γ₀ Γa :=
  .cons (.declLocal .uint (.user "x") (some (.simple (.lit 2 (by decide))))) <|
  .cons (.declStorage A (.user "row") (some (.path (rowsAt (.simple (.local .here)))))) <|
  .cons (.loop .auto (.binop .lt rfl rfl xa (litA 3))
    (.cons (.rebind .here (.path (.loc (.root "list" rfl)))) .nil)) .nil

theorem kindChange_refused : (Compiler.compile 0 (Frag.init Γ₀) kindChange).isNone = true := by
  decide +kernel

theorem kindChange_outside : ¬ ProgOk [] kindChange := fun h => by
  have accepted := compile_init 0 h
  rw [Option.isSome_iff_ne_none] at accepted
  exact accepted (Option.isNone_iff_eq_none.mp kindChange_refused)

/-- Reading an unset alias is refused (and solc rejects it). -/
def unsetRead : Solidity.Prog C Γ₀ [.alias A] :=
  .cons (.declStorage A (.user "u") none) <|
  .cons (.require (.binop .eqB rfl rfl
    (.read (.index (.arr .dyn) (.alias .here) (.simple (.lit 0 (by decide)))))
    (.simple (.lit 0 (by decide))))) .nil

theorem unsetRead_refused : (Compiler.compile 0 (Frag.init Γ₀) unsetRead).isNone = true := by
  decide +kernel

/-! ## Former and remaining refusals -/

/-- Signed `x & 1` is accepted since H87 (it was refused before). -/
def signedAnd : Solidity.Prog C Γ₀ Γ₀ :=
  .cons (.require (.binop .eqB rfl rfl
    (.binop .band rfl rfl (.simple (.lit (-1) (by decide)) : Solidity.Val C Γ₀ .int)
      (.simple (.lit 1 (by decide)))) (.simple (.lit 1 (by decide))))) .nil

theorem signedAnd_accepted : (Compiler.compile 0 (Frag.init Γ₀) signedAnd).isSome = true := by
  decide +kernel

/-- `address(this).balance` is refused. -/
def selfBalance : Solidity.Prog C Γ₀ Γ₀ :=
  .cons (.require (.binop .eqB rfl rfl
    (.simple (.env .selfBalance rfl) : Solidity.Val C Γ₀ .uint) (.simple (.lit 0 (by decide))))) .nil

theorem selfBalance_refused :
    (Compiler.compile 0 (Frag.init Γ₀) selfBalance).isNone = true := by
  decide +kernel

/-- A read of an `int`-keyed mapping is typed but refused. -/
def intKey : Solidity.Prog C Γ₀ Γ₀ :=
  .cons (.require (.binop .eqB rfl rfl
    (.read (.index .map (.loc (.root "signed" rfl)) (.simple (.lit 0 (by decide))))
      : Solidity.Val C Γ₀ .uint) (.simple (.lit 0 (by decide))))) .nil

theorem intKey_refused : (Compiler.compile 0 (Frag.init Γ₀) intKey).isNone = true := by
  decide +kernel

/-- Contrapositive of totality: the refused program is outside the domain. -/
theorem intKey_outside : ¬ ProgOk [] intKey := fun h => by
  have accepted := compile_init 0 h
  rw [Option.isSome_iff_ne_none] at accepted
  exact accepted (Option.isNone_iff_eq_none.mp intKey_refused)

/-- info: 'Solidity.Backend.AbiWorld.PublicCompilerTotal.compile_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms compile_core

/-- info: 'Solidity.Backend.AbiWorld.PublicCompilerTotal.compile_agrees' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms compile_agrees

end Solidity.Backend.AbiWorld.PublicCompilerTotalControls
