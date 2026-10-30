import Solidity.Source.ValueProgress
import Solidity.Source.WellTyped
import Solidity.Source.TypingExamples
import Solidity.Source.StmtProgress
import Solidity.Source.SemanticsExamples

/-!
# Controls of the soundness lane (V04b)

Witnesses and negative controls for `Solidity/Source/ValueProgress.lean`
and `Solidity/Source/WellTyped.lean`: each progress lemma's domain is
inhabited by a value it computes, and each hypothesis is needed (outside
it the operation is `stuck`).

| Theorem | Statement |
|---|---|
| `add_ok`, `add_value` | `1 + 2` at `uint8` is in `binVal`'s domain and is `3` |
| `add_bool_stuck`, `add_bool_outside` | `+` on booleans is `stuck`, and outside `BinOp.FitsAt` |
| `cmp_add_stuck` | `cmpVal` with a non-comparison operator is `stuck` |
| `shift_bool_stuck` | `shiftVal` on a boolean is `stuck` |
| `addSub_opsOK`, `order_opsOK`, `shift_opsOK` | elaborated `a + a`, `a < 1`, `a << 1` (S01's controls) are `OpsOK` |
| `badBinary_not_opsOK` | a resolved `true + false`, which no derivation elaborates to, is not `OpsOK` |
| `refOK_wrong_heap` | a memory reference to an address the heap typing does not give its type does not agree |
| `addSub_ns` | the elaboration of S01's `a + a` is in the value fragment and never `stuck` (`evalE_valFrag_ns`) |
| `badBinary_stuck` | evaluating the out-of-domain `true + false` is `stuck`: `OpsOK` is needed |
| `cond_ns`, `cond_value` | `true ? 1 + 2 : 0` at `uint8` is never `stuck` and evaluates to `3` |
| `loop_ns`, `loop_value` | `uint8 i; while (i < 3) { i += 1; }` is never `stuck` (`itemsNS`) and ends with `i = 3` |
| `cb_ns`, `cb_value` | `x = x + 1;` on a storage variable (S05's callback body) is never `stuck`, and takes `x` from 3 to 4 |
| `ret_unframed_stuck`, `ret_unframed_no_frame` | a `return 1;` run outside a coherent frame (no return slot) is `stuck`, and those locals are not a `BodyFrame`: the frame hypothesis is needed |
| `ret_framed_ns` | the same `return 1;` with a return slot is never `stuck` |
-/

namespace Solidity.Source.SoundnessExamples

open Solidity.Source

variable {D : Layout}

def one8 : Val D (.int IntTy.u8) := .int 1 (by decide)
def two8 : Val D (.int IntTy.u8) := .int 2 (by decide)

/-- **Witness**: `+` at `uint8` is in `binVal`'s domain. -/
theorem add_ok : NotStuckR (binVal (D := D) true .add one8 two8) :=
  binVal_ok true (.inl ⟨rfl, rfl⟩) _ _

/-- ... and computes `3`. -/
theorem add_value : (binVal (D := D) true .add one8 two8) = .ok (.int 3 (by decide)) := rfl

/-- **Negative control**: `+` on booleans is `stuck`. -/
theorem add_bool_stuck :
    binVal (D := D) true .add (.bool true) (.bool false) = .error (.stuck "not a boolean operation") := rfl

/-- ... and it is outside `binVal_ok`'s domain. -/
theorem add_bool_outside : ¬ BinOp.add.FitsAt .bool := by
  intro h
  rcases h with ⟨_, h⟩ | ⟨_, h⟩ | ⟨h, _⟩ <;> cases h

/-- **Negative control**: `cmpVal` with an arithmetic operator is `stuck`. -/
theorem cmp_add_stuck : cmpVal (D := D) .add one8 two8 = .error (.stuck "not a comparison") := rfl

/-- **Negative control**: `shiftVal` on a boolean is `stuck`. -/
theorem shift_bool_stuck : shiftVal (D := D) true .shl 1 (.bool true) = .error (.stuck "shift operand") := rfl

open TypingExamples in
/-- **Witnesses**: S01's own derivations elaborate into the domains. -/
theorem addSub_opsOK : w_addSub.toR.OpsOK := Typed.toR_opsOK _

open TypingExamples in
theorem order_opsOK : w_order.toR.OpsOK := Typed.toR_opsOK _

open TypingExamples in
theorem shift_opsOK : w_shift.toR.OpsOK := Typed.toR_opsOK _

/-- **Negative control**: `OpsOK` is not trivial — a resolved `true + false`
(an `RExpr`, which no derivation elaborates to) is not in the domain. -/
theorem badBinary_not_opsOK {E : Env} :
    ¬ (RExpr.binary (E := E) (Γ := []) .add (.bool true) (.bool false)).OpsOK := by
  intro h
  rcases h.1 with ⟨_, h⟩ | ⟨_, h⟩ | ⟨h, _⟩ <;> cases h

/-- **Negative control**: a memory reference agrees only with a heap typing
that gives its address its type. -/
theorem refOK_wrong_heap {E : Env} :
    ¬ (Val.memRef (D := E.layout) (τ := .bytes .memory) rfl 0).RefOK E (fun _ => some .bool) := by
  intro h
  cases h

/-- **Witness**: the same reference agrees with a heap typing that gives
address `0` the type `bytes memory`. -/
theorem refOK_heap {E : Env} :
    (Val.memRef (D := E.layout) (τ := .bytes .memory) rfl 0).RefOK E (fun _ => some (.bytes .memory)) := rfl


open TypingExamples in
/-- **Witness**: the elaboration of S01's `a + a` is in the value fragment,
so its evaluation is never `stuck` (at any horizon, in any state). -/
theorem addSub_ns (G : Glob Γ.env) (F : Fr) (n : Nat) : NS (evalE G F n w_addSub.toR) :=
  evalE_valFrag_ns G F n _ ⟨⟨rfl, rfl, .inl rfl⟩, ⟨rfl, rfl, .inl rfl⟩, rfl⟩ (Typed.toR_opsOK _)

/-- **Negative control**: `true + false`, resolved by hand (out of the
operations' domain), is `stuck` when evaluated. -/
theorem badBinary_stuck :
    ((evalE (SemanticsExamples.G0 .viaIR) SemanticsExamples.F0 3
      (RExpr.binary (E := SemanticsExamples.E0) (Γ := []) .add (.bool true) (.bool false))).run
      (.nil, SemanticsExamples.s0)).1 = .error (.stuck "not a boolean operation") := by
  rfl

/-- `true ? 1 + 2 : 0` at `uint8`, with its conversions. -/
def condE : RExpr SemanticsExamples.E0 [] (.int IntTy.u8) :=
  .cond (.bool true)
    (.binary .add (.conv (.const (Q.ofInt 1)) (.inl (by decide))) (.conv (.const (Q.ofInt 2)) (.inl (by decide))))
    (.conv (.const (Q.ofInt 0)) (.inl (by decide)))

/-- **Witness**: it is in the fragment and the domains, so never `stuck` ... -/
theorem cond_ns (n : Nat) : NS (evalE (SemanticsExamples.G0 .viaIR) SemanticsExamples.F0 n condE) :=
  evalE_valFrag_ns _ _ n condE
    ⟨trivial, ⟨⟨trivial, rfl, .inr (.inl ⟨_, rfl⟩)⟩, ⟨trivial, rfl, .inr (.inl ⟨_, rfl⟩)⟩, rfl⟩,
      ⟨trivial, rfl, .inr (.inl ⟨_, rfl⟩)⟩, rfl⟩
    ⟨trivial, ⟨.inl ⟨rfl, rfl⟩, trivial, trivial⟩, trivial⟩

/-- ... and evaluates to `3`. -/
theorem cond_value :
    ((evalE (SemanticsExamples.G0 .viaIR) SemanticsExamples.F0 5 condE).run (.nil, SemanticsExamples.s0)).1.toOption.map
      (fun v => match v with | .val x => x.key) = some (some 3) := by
  rfl

/-- `i < 3` over the local `uint8 i`. -/
def loopCond : RExpr SemanticsExamples.E0 [.int IntTy.u8] .bool :=
  .compare .lt (.local .here) (.conv (.const (Q.ofInt 3)) (.inl (by decide)))

/-- `i += 1;` -/
def loopBody : RStmt SemanticsExamples.E0 [] false ⟨true, false⟩ [.int IntTy.u8] [.int IntTy.u8] :=
  .expr (.compound .add (.local .here) (.const (Q.ofInt 1)) (by decide))

/-- `uint8 i; while (i < 3) { i += 1; }` -/
def loopItems : RItems SemanticsExamples.E0 [] false .body [] [.int IntTy.u8] :=
  .stmt (.declVar (.int IntTy.u8)) (.stmt (.whileLoop loopCond loopBody) .nil)

theorem loopItems_frag : loopItems.ValFrag :=
  ⟨rfl, ⟨⟨rfl, ⟨trivial, rfl, .inr (.inl ⟨_, rfl⟩)⟩, rfl⟩, ⟨trivial, trivial, rfl, .inr (.inl ⟨_, rfl⟩)⟩⟩, trivial⟩

theorem loopItems_ops : loopItems.OpsOK :=
  ⟨trivial, ⟨⟨⟨rfl, rfl, trivial, trivial⟩, ⟨trivial, trivial⟩⟩, trivial⟩⟩

/-- **Witness**: the loop is never `stuck`, at any horizon ... -/
theorem loop_ns (n : Nat) :
    NS (execItems (SemanticsExamples.G0 .viaIR) SemanticsExamples.F0 n 0 none loopItems .nil) :=
  itemsNS _ _ n 0 none loopItems .nil loopItems_frag loopItems_ops ⟨[], [], rfl, rfl⟩

/-- ... and ends with `i = 3`. -/
theorem loop_value :
    (match ((execItems (SemanticsExamples.G0 .viaIR) SemanticsExamples.F0 40 0 none loopItems .nil).run
      (.nil, SemanticsExamples.s0)).1 with
    | .ok (.normal (.cons v .nil)) => v.key
    | _ => none) = some 3 := by
  rfl

/-- **Negative control**: `return 1;` in a body whose locals hold no return
slot is `stuck` — `return` is in the fragment, but only under `BodyFrame`
(the locals end in the return slots), which these locals violate. -/
theorem ret_unframed_stuck :
    ((execS (SemanticsExamples.G0 .viaIR) SemanticsExamples.F0 5 0 none
      (RStmt.retVal (E := SemanticsExamples.E0) (R := [.int IntTy.u8]) (M := false) (k := .body) (Γ := [])
        rfl (.const (Q.ofInt 1)) (by decide)) .nil).run (.nil, SemanticsExamples.s0)).1 =
      .error (.stuck "no local") := by
  rfl

open SemanticsExamples in
theorem cbItems_frag : cbBody.items.ValFrag :=
  ⟨⟨⟨rfl, by decide, rfl⟩, ⟨⟨rfl, rfl, by decide, rfl, rfl⟩, ⟨trivial, rfl, .inr (.inl ⟨_, rfl⟩)⟩, rfl⟩, rfl⟩, trivial⟩

open SemanticsExamples in
theorem cbItems_ops : cbBody.items.OpsOK :=
  ⟨⟨trivial, ⟨.inl ⟨rfl, rfl⟩, trivial, trivial⟩⟩, trivial⟩

open SemanticsExamples in
/-- **Witness**: `x = x + 1;` on a storage variable is never `stuck` ... -/
theorem cb_ns (n : Nat) (F : Fr) (s : Option (Ph EB)) :
    NS (execItems (GB answerOnly) F n 0 s cbBody.items .nil) :=
  itemsNS _ F n 0 s _ .nil cbItems_frag cbItems_ops ⟨[], [], rfl, rfl⟩

open SemanticsExamples in
/-- ... and takes `x` from 3 to 4 in S05's deployed state. -/
theorem cb_value :
    (match (execItems (GB answerOnly) FC 10 0 none cbBody.items .nil).run (.nil, sB) with
    | (.ok _, (_, s)) => readX s
    | _ => none) = some 4 := by
  rfl

/-- ... and those locals are no `BodyFrame` for a `uint8` return. -/
theorem ret_unframed_no_frame : ¬ BodyFrame 0 [.int IntTy.u8] [] := by
  intro ⟨ys, ps, h, _⟩
  have := congrArg List.length h
  simp only [List.length_nil, List.length_append, List.length_reverse, List.length_singleton] at this
  omega

/-- **Witness**: with its return slot, `return 1;` is never `stuck`. -/
theorem ret_framed_ns (n : Nat) (l : Locals SemanticsExamples.E0.layout [.int IntTy.u8]) :
    NS (execS (SemanticsExamples.G0 .viaIR) SemanticsExamples.F0 n 0 none
      (RStmt.retVal (E := SemanticsExamples.E0) (R := [.int IntTy.u8]) (M := false) (k := .body)
        rfl (.const (Q.ofInt 1)) (by decide)) l) :=
  stmtNS _ _ n 0 none _ l ⟨trivial, rfl, .inr (.inl ⟨_, rfl⟩)⟩ trivial ⟨[], [], rfl, rfl⟩

end Solidity.Source.SoundnessExamples
