import Solidity.Source.Progress.BuiltinControls

/-! Controls for `addmod`, `mulmod` and `ecrecover`: exact results, the
zero-modulus panic, and the legacy/via-IR argument-order difference.
`recovery_failure` uses a precompile that halts (`none`), a branch the pinned
Osaka precompiles never take; an invalid signature there returns `some []`. -/

namespace Solidity.Source.Progress.ScalarBuiltinControls
open EM Preservation.AllocationControls

def modCtx : Ctx := {ctx with locals :=
  [("x", .int IntTy.u256), ("y", .int IntTy.u256), ("k", .int IntTy.u256)]}
def modSyn (name : String) : Syn .expr := .call (.ident name) (.positional
  (.cons (.ident "x") (.cons (.ident "y") (.cons (.ident "k") .nil))))
def addTyped : Typed modCtx (modSyn "addmod") (.int IntTy.u256) :=
  .builtinCall rfl rfl (.cons (.loc rfl rfl) (.cons (.loc rfl rfl) (.cons (.loc rfl rfl) .nil))) rfl
def mulTyped : Typed modCtx (modSyn "mulmod") (.int IntTy.u256) :=
  .builtinCall rfl rfl (.cons (.loc rfl rfl) (.cons (.loc rfl rfl) (.cons (.loc rfl rfl) .nil))) rfl

def modArgs : RArgs E [.int IntTy.u256, .int IntTy.u256, .int IntTy.u256]
    [.int IntTy.u256, .int IntTy.u256, .int IntTy.u256] :=
  .cons (.local .here) (.cons (.local (.there .here)) (.cons (.local (.there (.there .here))) .nil))
def modLocals : Locals E.layout [.int IntTy.u256, .int IntTy.u256, .int IntTy.u256] :=
  .cons (.int 2 (by decide)) (.cons (.int 3 (by decide)) (.cons (.int 4 (by decide)) .nil))
def zeroLocals : Locals E.layout [.int IntTy.u256, .int IntTy.u256, .int IntTy.u256] :=
  .cons (.int 2 (by decide)) (.cons (.int 3 (by decide)) (.cons (.int 0 (by decide)) .nil))

theorem mod_admitted (C : Decl → Prop) (b : Builtin) (hb : b = .addmod ∨ b = .mulmod) :
    BuiltinFragment C b modArgs (.int IntTy.u256) :=
  .mod _ _ hb (.inl rfl) (.inl rfl) (.inl rfl) rfl rfl rfl
    (.cons (.checked _ rfl trivial) (.cons (.checked _ rfl trivial) (.cons (.checked _ rfl trivial) .nil)))

theorem mod_progress (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) (b : Builtin)
    (hb : b = .addmod ∨ b = .mulmod) (n : Nat) :
    NS (evalBuiltin (glob p fixed) frame n b modArgs (.int IntTy.u256)) :=
  builtinFragment_ns _ _ (Source.exprNSAt _ _) (mod_admitted _ b hb) n

theorem add_run (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    (evalE (glob p fixed) frame 15 addTyped.toR).run (modLocals, BuiltinControls.initial) =
      (.ok (.val (.int 1 (by decide))), (modLocals, BuiltinControls.initial)) := by cases p <;> rfl

theorem mul_run (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    (evalE (glob p fixed) frame 15 mulTyped.toR).run (modLocals, BuiltinControls.initial) =
      (.ok (.val (.int 2 (by decide))), (modLocals, BuiltinControls.initial)) := by cases p <;> rfl

theorem zero_modulus (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    (evalE (glob p fixed) frame 15 addTyped.toR).run (zeroLocals, BuiltinControls.initial) =
      (.error (.revert (panicData .divZero)), (zeroLocals, BuiltinControls.initial)) := by cases p <;> rfl

def orderCtx : Ctx := {ctx with locals := [("x", .int IntTy.u256)]}
def orderSyn : Syn .expr := .call (.ident "addmod") (.positional
  (.cons (.assign .assign (.ident "x") (.lit (.num (.dec 2 0 0))))
  (.cons (.assign .assign (.ident "x") (.lit (.num (.dec 3 0 0)))) (.cons (.ident "x") .nil))))
def orderTyped : Typed orderCtx orderSyn (.int IntTy.u256) :=
  .builtinCall rfl rfl (.cons (.assign (.loc rfl rfl) (.const rfl rfl rfl) rfl rfl)
    (.cons (.assign (.loc rfl rfl) (.const rfl rfl rfl) rfl rfl) (.cons (.loc rfl rfl) .nil))) rfl

theorem legacy_argument_order (fixed : Roadmap.Fixed) :
    (evalE (glob .legacy fixed) frame 20 orderTyped.toR).run
      (.cons (.int 4 (by decide)) .nil, BuiltinControls.initial) =
      (.ok (.val (.int 1 (by decide))), (.cons (.int 2 (by decide)) .nil, BuiltinControls.initial)) := rfl
theorem viaIR_argument_order (fixed : Roadmap.Fixed) :
    (evalE (glob .viaIR fixed) frame 20 orderTyped.toR).run
      (.cons (.int 4 (by decide)) .nil, BuiltinControls.initial) =
      (.ok (.val (.int 2 (by decide))), (.cons (.int 3 (by decide)) .nil, BuiltinControls.initial)) := rfl

def recoveryCtx : Ctx := {ctx with locals :=
  [("h", .bytes32), ("v", .int IntTy.u8), ("r", .bytes32), ("s", .bytes32)]}
def recoverySyn : Syn .expr := .call (.ident "ecrecover") (.positional
  (.cons (.ident "h") (.cons (.ident "v") (.cons (.ident "r") (.cons (.ident "s") .nil)))))
def recoveryTyped : Typed recoveryCtx recoverySyn (.address false) :=
  .builtinCall rfl rfl (.cons (.loc rfl rfl) (.cons (.loc rfl rfl)
    (.cons (.loc rfl rfl) (.cons (.loc rfl rfl) .nil)))) rfl
def recoveryArgs : RArgs E [.bytes32, .int IntTy.u8, .bytes32, .bytes32]
    [.bytes32, .int IntTy.u8, .bytes32, .bytes32] :=
  .cons (.local .here) (.cons (.local (.there .here)) (.cons (.local (.there (.there .here)))
    (.cons (.local (.there (.there (.there .here)))) .nil)))
def recoveryLocals : Locals E.layout [.bytes32, .int IntTy.u8, .bytes32, .bytes32] :=
  .cons (mkBytes (n := 32) (h := by decide) []) (.cons (.int 0 (by decide))
    (.cons (mkBytes (n := 32) (h := by decide) []) (.cons (mkBytes (n := 32) (h := by decide) []) .nil)))
def failingRecovery (fixed : Roadmap.Fixed) : Roadmap.Fixed :=
  {fixed with evm := {fixed.evm with precompile := fun _ _ => none}}

theorem recovery_admitted (C : Decl → Prop) :
    BuiltinFragment C .ecrecover recoveryArgs (.address false) :=
  .recovery _ (.inl (.inl rfl)) (.inl (.inl rfl)) (.inl (.inl rfl)) (.inl (.inl rfl))
    rfl rfl rfl rfl (.cons (.checked _ rfl trivial) (.cons (.checked _ rfl trivial)
      (.cons (.checked _ rfl trivial) (.cons (.checked _ rfl trivial) .nil))))

theorem recovery_progress (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) (n : Nat) :
    NS (evalBuiltin (glob p fixed) frame n .ecrecover recoveryArgs (.address false)) :=
  builtinFragment_ns _ _ (Source.exprNSAt _ _) (recovery_admitted _) n

theorem recovery_failure (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    (evalE (glob p (failingRecovery fixed)) frame 15 recoveryTyped.toR).run
      (recoveryLocals, BuiltinControls.initial) =
      (.ok (.val (.address ⟨0, by decide⟩)), (recoveryLocals, BuiltinControls.initial)) := by cases p <;> rfl

#print axioms mod_progress
#print axioms legacy_argument_order
#print axioms viaIR_argument_order
#print axioms recovery_progress
#print axioms recovery_failure
end Solidity.Source.Progress.ScalarBuiltinControls
