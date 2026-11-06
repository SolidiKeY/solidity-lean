import Solidity.Backend.Scalar.Slice

/-!
Draft simultaneous-premise witnesses for all 15 public named theorems in the
frozen Slice interface. Each existential binds every input of its statement;
all premises share that single assignment, followed by its instantiated result.

VALIDATION BLOCKED: the unchanged import fails its ternary axiom guard under
the required Lean 4.35.0 pin. These declarations are not counted as verified.
No producer statement, proof, or guard is edited by this audit.
-/
namespace Solidity.Backend.Scalar.H62Audit

-- AUDIT-WITNESS: Solidity.Backend.Scalar.run_append
theorem witness_run_append : ∃ (p q : Program) (s : Stack),
    run (p ++ q) s = (run p s).bind (run q) :=
  ⟨[.op .POP], [.op .POP], [7, 3, 99], run_append _ _ _⟩

-- AUDIT-WITNESS: Solidity.Backend.Scalar.run_comp
theorem witness_run_comp : ∃ (p q : Program) (s t u : Stack),
    run p s = some t ∧ run q t = some u ∧ run (p ++ q) s = some u :=
  ⟨[.op .POP], [.op .POP], [7, 3, 99], [3, 99], [99], rfl, rfl,
    run_comp (p := [.op .POP]) (q := [.op .POP])
      (s := [7, 3, 99]) (t := [3, 99]) (u := [99]) rfl rfl⟩

-- AUDIT-WITNESS: Solidity.Backend.Scalar.step_pushByte
theorem witness_step_pushByte : ∃ (b : UInt8) (s : Stack),
    step (pushByte b) s = some (BitVec.ofNat 256 b.toNat :: s) :=
  ⟨7, [99], step_pushByte 7 [99]⟩

-- AUDIT-WITNESS: Solidity.Backend.Scalar.applyUnary_frame
theorem witness_applyUnary_frame : ∃ (f : Word → Word) (s t tail : Stack),
    applyUnary f s = some t ∧ applyUnary f (s ++ tail) = some (t ++ tail) :=
  ⟨id, [7], [7], [99], rfl, applyUnary_frame id (s := [7]) (t := [7]) rfl [99]⟩

-- AUDIT-WITNESS: Solidity.Backend.Scalar.applyBinary_frame
theorem witness_applyBinary_frame : ∃ (f : Word → Word → Word) (s t tail : Stack),
    applyBinary f s = some t ∧ applyBinary f (s ++ tail) = some (t ++ tail) :=
  ⟨(fun a _ => a), [7, 3], [7], [99], rfl,
    applyBinary_frame (fun a _ => a) (s := [7, 3]) (t := [7]) rfl [99]⟩

-- AUDIT-WITNESS: Solidity.Backend.Scalar.applyTernary_frame
theorem witness_applyTernary_frame :
    ∃ (f : Word → Word → Word → Word) (s t tail : Stack),
    applyTernary f s = some t ∧ applyTernary f (s ++ tail) = some (t ++ tail) :=
  ⟨(fun a _ _ => a), [7, 3, 2], [7], [99], rfl,
    applyTernary_frame (fun a _ _ => a) (s := [7, 3, 2]) (t := [7]) rfl [99]⟩

-- AUDIT-WITNESS: Solidity.Backend.Scalar.duplicate_frame
theorem witness_duplicate_frame : ∃ (n : Nat) (s t tail : Stack),
    duplicate n s = some t ∧ duplicate n (s ++ tail) = some (t ++ tail) :=
  ⟨0, [7], [7, 7], [99], rfl, duplicate_frame 0 (s := [7]) (t := [7, 7]) rfl [99]⟩

-- AUDIT-WITNESS: Solidity.Backend.Scalar.exchange_frame
theorem witness_exchange_frame : ∃ (a : Word) (n : Nat) (s t : Stack) (b : Word) (tail : Stack),
    exchange a n s = some (b, t) ∧ exchange a n (s ++ tail) = some (b, t ++ tail) :=
  ⟨3, 0, [7], [3], 7, [99], rfl, exchange_frame 3 0 (s := [7]) (t := [3]) (b := 7) rfl [99]⟩

-- AUDIT-WITNESS: Solidity.Backend.Scalar.swap_frame
theorem witness_swap_frame : ∃ (n : Nat) (s t tail : Stack),
    swap n s = some t ∧ swap n (s ++ tail) = some (t ++ tail) :=
  ⟨0, [7, 3], [3, 7], [99], rfl, swap_frame 0 (s := [7, 3]) (t := [3, 7]) rfl [99]⟩

-- AUDIT-WITNESS: Solidity.Backend.Scalar.pop_frame
theorem witness_pop_frame : ∃ s t tail : Stack,
    pop s = some t ∧ pop (s ++ tail) = some (t ++ tail) :=
  ⟨[7], [], [99], rfl, pop_frame (s := [7]) (t := []) rfl [99]⟩

-- AUDIT-WITNESS: Solidity.Backend.Scalar.numericStep_frame
theorem witness_numericStep_frame : ∃ (o : Op) (s t tail : Stack),
    numericStep o s = some t ∧ numericStep o (s ++ tail) = some (t ++ tail) :=
  ⟨.ISZERO, [0], [1], [99], rfl, numericStep_frame (o := .ISZERO) (s := [0]) (t := [1]) rfl [99]⟩

-- AUDIT-WITNESS: Solidity.Backend.Scalar.step_frame
theorem witness_step_frame : ∃ (i : Instr) (s t tail : Stack),
    step i s = some t ∧ step i (s ++ tail) = some (t ++ tail) :=
  ⟨.op .POP, [7], [], [99], rfl, step_frame (i := .op .POP) (s := [7]) (t := []) rfl [99]⟩

-- AUDIT-WITNESS: Solidity.Backend.Scalar.run_frame
theorem witness_run_frame : ∃ (p : Program) (s t tail : Stack),
    run p s = some t ∧ run p (s ++ tail) = some (t ++ tail) :=
  ⟨[.op .POP], [7], [], [99], rfl, run_frame (p := [.op .POP]) (s := [7]) (t := []) rfl [99]⟩

-- AUDIT-WITNESS: Solidity.Backend.Scalar.step_pushWord
theorem witness_step_pushWord : ∃ (w : Word) (s : Stack),
    step (pushWord w) s = some (w :: s) :=
  ⟨7, [99], step_pushWord 7 [99]⟩

-- AUDIT-WITNESS: Solidity.Backend.Scalar.encode_pushWord
theorem witness_encode_pushWord : ∃ w : Word,
    (pushWord w).encode = 0x7f :: (toBytesBE 32 w.toNat).toList :=
  ⟨7, encode_pushWord 7⟩

end Solidity.Backend.Scalar.H62Audit
