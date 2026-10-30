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
| `indexMapping_ns` | the elaboration of S01's `m[o]` (a mapping value, read through an implicit key conversion) is in the value fragment and never `stuck` |
| `incBody_ns` | the elaboration of the counter's typed body `count++;` (`TypingExamples.incBody`, an `ItemsD` derivation) is in the statement fragment and never `stuck` in its frame (`ItemsD.toR_ns`) |
| `retPair_ns`, `retPair_unframed_stuck` | `return (1, 2);` with two return slots is never `stuck`; over locals without them it is |
| `callF_ns`, `callF_value`, `callF_badFrame_stuck` | the call expression `f()` (a function implemented by `return 1;`) is never `stuck` (`evalE_callFrag_ns`) and evaluates to `1`; with a body outside the call's frame it is `stuck` |
| `recF_ns`, `recF_timeout` | with `f` calling itself (`return f();`), `f()` is never `stuck` and runs out of horizon |
| `callG_ns`, `callG_value` | in a program with distinct bodies for `f` (`return 1;`) and `g` (`return f();`), `g()` is never `stuck` and evaluates to `1` |
| `retLocalPair_ns` | `return (x, x);` with a declared local `x` over the two return slots is never `stuck` |
| `callRetOne_ns` | an internal call of `function f() internal returns (uint8) { return 1; }` (no modifiers, a fragment body in the frame the call builds) is never `stuck` (`callInternal_ns`) |
| `callBadFrame_stuck` | a body whose locals lack the return slot is `stuck` ("call frame"): the frame hypothesis is needed |
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
that gives its address its type (up to `bytes`/`string`). -/
theorem refOK_wrong_heap {E : Env} :
    ¬ (Val.memRef (D := E.layout) (τ := .bytes .memory) rfl 0).RefOK E (fun _ => some .bool) := by
  intro ⟨σ, h1, h2⟩
  cases h1
  cases h2

/-- **Witness**: the same reference agrees with a heap typing that gives
address `0` the type `bytes memory`, and with one that gives it a string
(`bytes(s)` of a `string memory s`). -/
theorem refOK_heap {E : Env} :
    (Val.memRef (D := E.layout) (τ := .bytes .memory) rfl 0).RefOK E (fun _ => some (.bytes .memory)) ∧
    (Val.memRef (D := E.layout) (τ := .bytes .memory) rfl 0).RefOK E (fun _ => some (.string .memory)) :=
  ⟨⟨_, rfl, rfl⟩, ⟨_, rfl, rfl⟩⟩


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

/-- `return (1, 2);` in a function returning `(uint8, uint8)`. -/
def retPair : RStmt SemanticsExamples.E0 [.int IntTy.u8, .int IntTy.u8] false .body Γ Γ :=
  .retTuple (.cons (.const (Q.ofInt 1)) (by decide) (.cons (.const (Q.ofInt 2)) (by decide) .nil))

/-- **Witness**: `return (1, 2);` with its two return slots is never
`stuck` (`retTuple`, through `setRets_ok`). -/
theorem retPair_ns (n : Nat) (l : Locals SemanticsExamples.E0.layout [.int IntTy.u8, .int IntTy.u8]) :
    NS (execS (SemanticsExamples.G0 .viaIR) SemanticsExamples.F0 n 0 none (retPair (Γ := _)) l) :=
  stmtNS _ _ n 0 none _ l ⟨trivial, rfl, .inr (.inl ⟨_, rfl⟩), trivial, rfl, .inr (.inl ⟨_, rfl⟩), trivial⟩
    ⟨trivial, trivial, trivial⟩ ⟨[], [], rfl, rfl⟩

/-- **Negative control**: the same statement over locals without the return
slots is `stuck` ("no local"). -/
theorem retPair_unframed_stuck :
    ((execS (SemanticsExamples.G0 .viaIR) SemanticsExamples.F0 5 0 none (retPair (Γ := [])) .nil).run
      (.nil, SemanticsExamples.s0)).1 = .error (.stuck "no local") := by
  rfl

/-- `uint8 x; …; return (x, x);` in a function returning `(uint8, uint8)`:
the arguments are a local, not constants. -/
def retLocalPair : RStmt SemanticsExamples.E0 [.int IntTy.u8, .int IntTy.u8] false .body
    [.int IntTy.u8, .int IntTy.u8, .int IntTy.u8] [.int IntTy.u8, .int IntTy.u8, .int IntTy.u8] :=
  .retTuple (.cons (.local .here) (by decide) (.cons (.local .here) (by decide) .nil))

/-- **Witness**: `return (x, x);` with a declared local over the two return
slots is never `stuck`. -/
theorem retLocalPair_ns (n : Nat)
    (l : Locals SemanticsExamples.E0.layout [.int IntTy.u8, .int IntTy.u8, .int IntTy.u8]) :
    NS (execS (SemanticsExamples.G0 .viaIR) SemanticsExamples.F0 n 0 none retLocalPair l) :=
  stmtNS _ _ n 0 none _ l ⟨rfl, rfl, .inl rfl, rfl, rfl, .inl rfl, trivial⟩ ⟨trivial, trivial, trivial⟩
    ⟨[.int IntTy.u8], [], rfl, rfl⟩

/-! ## Elaborated witnesses: a statement and a mapping -/

open TypingExamples in
/-- **Witness**: the elaboration of S01's `m[o]` (a mapping value, read)
is in the value fragment, so its evaluation is never `stuck`. -/
theorem indexMapping_ns (G : Glob Γ.env) (F : Fr) (n : Nat) : NS (evalE G F n w_index_mapping.toR) :=
  evalE_valFrag_ns G F n _ (by
    exact ⟨⟨rfl, rfl, _, _, rfl⟩, ⟨rfl, rfl, .inl rfl⟩, rfl, rfl, rfl⟩) (Typed.toR_opsOK _)

open TypingExamples in
/-- **Witness**: the elaboration of the counter's body `count++;` (an
elaborated typing derivation, `incBody`) is in the statement fragment, so
running it in its function's frame is never `stuck` (`ItemsD.toR_ns`). -/
theorem incBody_ns (G : Glob Examples.counter.env) (F : Fr) (n : Nat) :
    NS (execItems G F n 0 none incBody.toR .nil) :=
  ItemsD.toR_ns G F n 0 none incBody .nil (by
    exact ⟨⟨rfl, rfl, rfl⟩, trivial⟩) ⟨[], [], rfl, rfl⟩

/-! ## The function level -/

open SemanticsExamples in
/-- `function f() internal returns (uint8) { return 1; }`, resolved: its
locals are the return slot. -/
def retOneBody : RBody E0 where
  ps := []
  rs := [u8]
  inModifier := false
  locals := [u8]
  out := [u8]
  items := .stmt (.retVal rfl (.const (Q.ofInt 1)) (by decide)) .nil

open SemanticsExamples in
/-- A body with no locals (and no statements) for a call returning
`uint8`: not the frame the call builds. -/
def badFrameBody : RBody E0 where
  ps := []
  rs := [u8]
  inModifier := false
  locals := []
  out := []
  items := .nil

open SemanticsExamples in
/-- A program whose every function has body `b`. -/
def progOf (b : RBody E0) : Glob E0 :=
  ⟨{ P0 with body := fun _ => some b }, .viaIR, toyFixed, fun _ => word 0, fun _ _ => false,
    fun _ => .answer (.success []), word 0⟩

open SemanticsExamples in
/-- **Witness**: an internal call of `f` (no modifiers, a fragment body,
the frame the call builds) is never `stuck` (`callInternal_ns`). -/
theorem callRetOne_ns (d : Decl) (n : Nat) :
    NS (callInternal (progOf retOneBody) F0 n d (ps := []) .nil [u8]) :=
  callInternal_ns _ _ n d .nil [u8] retOneBody rfl rfl rfl rfl rfl
    (fun τ h => by simp only [List.mem_cons, List.not_mem_nil, or_false] at h; subst h; rfl)
    ⟨⟨trivial, rfl, .inr (.inl ⟨_, rfl⟩)⟩, trivial⟩ ⟨trivial, trivial⟩

open SemanticsExamples in
/-- **Negative control**: a body whose locals are not the frame the call
builds is `stuck` ("call frame"): `callInternal_ns`'s frame hypothesis is
needed. -/
theorem callBadFrame_stuck (d : Decl) :
    ((callInternal (progOf badFrameBody) F0 5 d (ps := []) .nil [u8]).run (.nil, s0)).1 =
      .error (.stuck "call frame") := by
  rfl

/-! ## Internal calls inside expressions -/

/-- `function f() internal returns (uint8)`, as a declaration. -/
def fDecl : Decl := ⟨.function, "f", none, false,
  .function (.ident "f") .nil (some .internal) none .nil false none
    (.cons (.param (.elem (.int false 8 (by decide))) none none) .nil) (.some (.block .nil))⟩

theorem fDecl_sig : fDecl.fnSig SemanticsExamples.E0 = some ([], [.int IntTy.u8]) := rfl

/-- The call expression `f()`. -/
def callF : RExpr SemanticsExamples.E0 [] (STy.ret [.int IntTy.u8]) := .call fDecl fDecl_sig .nil

open SemanticsExamples in
/-- The program implements every function by `return 1;` (`retOneBody`):
the functions `fDecl` names are fragment bodies. -/
theorem retOne_callsOK : CallsOK (fun d => d = fDecl) (progOf retOneBody) "C" := by
  intro d ps rs hs hA
  subst hA
  rw [fDecl_sig] at hs
  simp only [Option.some.injEq, Prod.mk.injEq] at hs
  obtain ⟨rfl, rfl⟩ := hs
  exact ⟨retOneBody, rfl, rfl, rfl, rfl, rfl,
    fun τ h => by simp only [List.mem_cons, List.not_mem_nil, or_false] at h; subst h; rfl,
    ⟨⟨trivial, rfl, .inr (.inl ⟨_, rfl⟩)⟩, trivial⟩, ⟨trivial, trivial⟩⟩

open SemanticsExamples in
/-- **Witness**: the call expression `f()` is never `stuck`
(`evalE_callFrag_ns`: the joint induction over expressions, statements,
bodies and internal calls). -/
theorem callF_ns (n : Nat) : NS (evalE (progOf retOneBody) F0 n callF) :=
  evalE_callFrag_ns retOne_callsOK F0 rfl n callF ⟨rfl, trivial⟩ trivial

open SemanticsExamples in
/-- **Value control**: `f()` evaluates to `1`. -/
theorem callF_value : intOf ((evalE (progOf retOneBody) F0 10 callF).run (.nil, s0)) = some 1 := by
  rfl

open SemanticsExamples in
/-- **Negative control**: with a body whose locals are not the call's frame,
`f()` is `stuck` ("call frame"): the frame conjunct of `CallsOK` is
needed. -/
theorem callF_badFrame_stuck :
    ((evalE (progOf badFrameBody) F0 10 callF).run (.nil, s0)).1 = .error (.stuck "call frame") := by
  rfl

open SemanticsExamples in
/-- `function f() internal returns (uint8) { return f(); }`, resolved: a body
that calls, recursively. -/
def recBody : RBody E0 where
  ps := []
  rs := [u8]
  inModifier := false
  locals := [u8]
  out := [u8]
  items := .stmt (.retVal rfl (.call fDecl fDecl_sig .nil) (by decide)) .nil

open SemanticsExamples in
theorem rec_callsOK : CallsOK (fun d => d = fDecl) (progOf recBody) "C" := by
  intro d ps rs hs hA
  subst hA
  rw [fDecl_sig] at hs
  simp only [Option.some.injEq, Prod.mk.injEq] at hs
  obtain ⟨rfl, rfl⟩ := hs
  exact ⟨recBody, rfl, rfl, rfl, rfl, rfl,
    fun τ h => by simp only [List.mem_cons, List.not_mem_nil, or_false] at h; subst h; rfl,
    ⟨⟨⟨rfl, trivial⟩, rfl, .inl rfl⟩, trivial⟩, ⟨trivial, trivial⟩⟩

open SemanticsExamples in
/-- **Witness, recursion**: with `f` calling itself, `f()` is never `stuck`
at any horizon (the joint induction: the callee's body itself calls); it
only times out. -/
theorem recF_ns (n : Nat) : NS (evalE (progOf recBody) F0 n callF) :=
  evalE_callFrag_ns rec_callsOK F0 rfl n callF ⟨rfl, trivial⟩ trivial

open SemanticsExamples in
/-- **Value control**: the recursion runs out of horizon (a timeout, not
`stuck`). -/
theorem recF_timeout : ((evalE (progOf recBody) F0 12 callF).run (.nil, s0)).1 = .error .timeout := by
  rfl

/-- `function g() internal returns (uint8)`, as a declaration. -/
def gDecl : Decl := ⟨.function, "g", none, false,
  .function (.ident "g") .nil (some .internal) none .nil false none
    (.cons (.param (.elem (.int false 8 (by decide))) none none) .nil) (.some (.block .nil))⟩

theorem gDecl_sig : gDecl.fnSig SemanticsExamples.E0 = some ([], [.int IntTy.u8]) := rfl

open SemanticsExamples in
/-- `function g() internal returns (uint8) { return f(); }`, resolved. -/
def gBody : RBody E0 where
  ps := []
  rs := [u8]
  inModifier := false
  locals := [u8]
  out := [u8]
  items := .stmt (.retVal rfl (.call fDecl fDecl_sig .nil) (by decide)) .nil

open SemanticsExamples in
/-- A program with two bodies: `g` returns `f()`, every other function
(`f` among them) returns `1`. -/
def progFG : Glob E0 :=
  ⟨{ P0 with body := fun d => if d.name = "g" then some gBody else some retOneBody }, .viaIR, toyFixed,
    fun _ => word 0, fun _ _ => false, fun _ => .answer (.success []), word 0⟩

open SemanticsExamples in
theorem fg_callsOK : CallsOK (fun d => d = fDecl ∨ d = gDecl) progFG "C" := by
  intro d ps rs hs hA
  rcases hA with rfl | rfl
  · rw [fDecl_sig] at hs
    simp only [Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨rfl, rfl⟩ := hs
    exact ⟨retOneBody, rfl, rfl, rfl, rfl, rfl,
      fun τ h => by simp only [List.mem_cons, List.not_mem_nil, or_false] at h; subst h; rfl,
      ⟨⟨trivial, rfl, .inr (.inl ⟨_, rfl⟩)⟩, trivial⟩, ⟨trivial, trivial⟩⟩
  · rw [gDecl_sig] at hs
    simp only [Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨rfl, rfl⟩ := hs
    exact ⟨gBody, rfl, rfl, rfl, rfl, rfl,
      fun τ h => by simp only [List.mem_cons, List.not_mem_nil, or_false] at h; subst h; rfl,
      ⟨⟨⟨Or.inl rfl, trivial⟩, rfl, .inl rfl⟩, trivial⟩, ⟨trivial, trivial⟩⟩

/-- The call expression `g()`. -/
def callG : RExpr SemanticsExamples.E0 [] (STy.ret [.int IntTy.u8]) := .call gDecl gDecl_sig .nil

open SemanticsExamples in
/-- **Witness, a call through a body that calls**: `g()`, whose body returns
`f()`, is never `stuck` in a program with distinct bodies for `f` and `g`. -/
theorem callG_ns (n : Nat) : NS (evalE progFG F0 n callG) :=
  evalE_callFrag_ns fg_callsOK F0 rfl n callG ⟨Or.inr rfl, trivial⟩ trivial

open SemanticsExamples in
/-- **Value control**: `g()` evaluates to `f()`'s `1` (at horizon 12). -/
theorem callG_value : intOf ((evalE progFG F0 12 callG).run (.nil, s0)) = some 1 := by
  rfl

/-! ## The census's semantic bug, fixed -/

/-- `string memory s = "abc"; bytes(s)[0] = 0x78; bytes1 b = bytes(s)[0];` -/
def strItems : RItems SemanticsExamples.E0 [] false .body []
    [.fixedBytes 1 (by decide), .string .memory] :=
  .stmt (.declInit (.str [97, 98, 99]) (by decide))
    (.stmt (.expr (.assign
      (.indexBytes (.convExplicit (.local .here) (τ := .bytes .memory) (by decide)) (by decide) (.const (Q.ofInt 0)) (by decide))
      (.conv (.bytesLit (.hex [7, 8] false) 1) (.inl (by decide)))))
    (.stmt (.declInit (.indexBytes (.convExplicit (.local .here) (τ := .bytes .memory) (by decide))
        (.const (Q.ofInt 0)) (by decide)) (by decide)) .nil))

/-- **Semantic fix**: writing a byte of `bytes(s)` for a `string memory s`
updates the string (it was `stuck`, "not bytes"): `b` is `0x78`. -/
theorem stringByte_write :
    (match ((execItems (SemanticsExamples.G0 .viaIR) SemanticsExamples.F0 20 0 none strItems .nil).run
      (.nil, SemanticsExamples.s0)).1 with
    | .ok (.normal (.cons b _)) => b.key
    | _ => none) = some 0x78 := by
  rfl

/-! ## Preservation of location writes and the shape gap -/

/-- A heap with a `bytes memory` object at `0` and, at `1`, a `bytes memory`
object stored as a pointer to `0` (a `Data.val`, not a `Data.bytes`). -/
def ptrHeap : Heap SemanticsExamples.E0.layout :=
  (((Heap.empty : Heap SemanticsExamples.E0.layout).alloc ⟨.bytes .memory, .bytes [1]⟩).1.alloc
    ⟨.bytes .memory, .val (Val.memRef rfl 0)⟩).1

/-- `ptrHeap` is well typed: the pointer at `1` names an object of its type. -/
theorem ptrHeap_ok : HeapOK (E := SemanticsExamples.E0) ptrHeap :=
  (HeapOK.empty.alloc (.bytes _)).alloc (.val ⟨_, rfl, rfl⟩)

/-- **Negative control (progress needs object shapes)**: a byte write at
`1` in the well-typed `ptrHeap` is `stuck`, although `writeLoc_memByte_pres`
keeps the state well typed. `HeapOK` constrains where references point, not
the shape of the top-level object, so progress for memory writes needs an
extra invariant (no top-level `Data.val` at a memory reference type). -/
theorem ptrHeap_byte_stuck :
    ((writeLoc (E := SemanticsExamples.E0) (Γ := []) SemanticsExamples.F0 3 (.memByte 1 0)
      (Val.fixedBytes [7] rfl)).run (.nil, { SemanticsExamples.s0 with heap := ptrHeap })).1 =
      .error (.stuck "not bytes") := by
  rfl

/-- **Control**: `ptrHeap` is not shaped (`HeapShaped`), so
`writeLoc_memByte_ok` does not apply to it. -/
theorem ptrHeap_not_shaped : ¬ HeapShaped (E := SemanticsExamples.E0) ptrHeap := fun h => by
  have ht := h 1 _ rfl
  simp only [Data.Top, STy.loc?, reduceCtorEq] at ht

/-- A heap with only the `bytes memory` object `[1]` at `0`. -/
def bytesHeap : Heap SemanticsExamples.E0.layout :=
  ((Heap.empty : Heap SemanticsExamples.E0.layout).alloc ⟨.bytes .memory, .bytes [1]⟩).1

/-- `bytesHeap` is shaped. -/
theorem bytesHeap_shaped : HeapShaped (E := SemanticsExamples.E0) bytesHeap :=
  HeapShaped.empty.alloc trivial

/-- **Witness**: in the shaped `bytesHeap`, the byte write at `0` succeeds
(`writeLoc_memByte_ok`: never `stuck`). -/
theorem bytesHeap_byte_write :
    ((writeLoc (E := SemanticsExamples.E0) (Γ := []) SemanticsExamples.F0 3 (.memByte 0 0)
      (Val.fixedBytes [7] rfl)).run (.nil, { SemanticsExamples.s0 with heap := bytesHeap })).1 = .ok () := by
  rfl

/-- A heap with a `bool[] memory` of one element `false` at `0`. -/
def arrHeap : Heap SemanticsExamples.E0.layout :=
  ((Heap.empty : Heap SemanticsExamples.E0.layout).alloc
    ⟨.array .memory .bool none, .array 1 (fun _ h => nomatch h) fun _ => .val (.bool false)⟩).1

/-- `arrHeap` is shaped. -/
theorem arrHeap_shaped : HeapShaped (E := SemanticsExamples.E0) arrHeap :=
  HeapShaped.empty.alloc trivial

/-- **Witness** (`writeLoc_mem_ok`): writing `true` as element `0` of the
`bool[]` at `0` succeeds. -/
theorem arrHeap_write :
    ((writeLoc (E := SemanticsExamples.E0) (Γ := []) SemanticsExamples.F0 3 (.mem 0 0)
      (Val.bool true)).run (.nil, { SemanticsExamples.s0 with heap := arrHeap })).1 = .ok () := by
  rfl

/-- **Negative control** (the element-type premise of `writeLoc_mem_ok`):
writing an `address` as an element of the `bool[]` is `stuck`. -/
theorem arrHeap_wrong_elem_stuck :
    ((writeLoc (E := SemanticsExamples.E0) (Γ := []) SemanticsExamples.F0 3 (.mem 0 0)
      (Val.address (p := false) (SemanticsExamples.addr 1))).run (.nil, { SemanticsExamples.s0 with heap := arrHeap })).1 =
      .error (.stuck "element type") := by
  rfl

/-- **Witness** (`readLoc_memByte_ok`): reading byte `0` of the shaped
`bytesHeap` gives `0x01`. -/
theorem bytesHeap_byte_read :
    (match ((readLoc (E := SemanticsExamples.E0) (Γ := []) SemanticsExamples.F0 (.memByte 0 0)).run
      (.nil, { SemanticsExamples.s0 with heap := bytesHeap })).1 with
    | .ok (.fixedBytes bs _) => some bs
    | _ => none) = some [1] := by
  rfl

/-- **Negative control** (the shape premise of `readLoc_memByte_ok`):
reading byte `0` at `1` of the unshaped `ptrHeap` is `stuck`. -/
theorem ptrHeap_byte_read_stuck :
    ((readLoc (E := SemanticsExamples.E0) (Γ := []) SemanticsExamples.F0 (.memByte 1 0)).run
      (.nil, { SemanticsExamples.s0 with heap := ptrHeap })).1 = .error (.stuck "not a bytes object") := by
  rfl

/-- `arrHeap` has bare-value elements. -/
theorem arrHeap_inner : HeapInner (E := SemanticsExamples.E0) arrHeap :=
  HeapInner.empty.alloc fun _ => ⟨_, rfl⟩

/-- **Witness** (`readLoc_mem_ok`): element `0` of the `bool[]` at `0` of
`arrHeap` is `false`. -/
theorem arrHeap_read :
    ((readLoc (E := SemanticsExamples.E0) (Γ := []) SemanticsExamples.F0 (τ := .bool) (.mem 0 0)).run
      (.nil, { SemanticsExamples.s0 with heap := arrHeap })).1 = .ok (.bool false) := by
  rfl

/-- A heap with a `bytes[] memory` at `0` whose one element is an inline
`bytes` (not a pointer). -/
def inlineHeap : Heap SemanticsExamples.E0.layout :=
  ((Heap.empty : Heap SemanticsExamples.E0.layout).alloc
    ⟨.array .memory (.bytes .memory) none, .array 1 (fun _ h => nomatch h) fun _ => .bytes [1]⟩).1

/-- **Negative control** (the `HeapInner` premise of `readLoc_mem_ok`):
`inlineHeap` is well typed and shaped but its element is inline, and
reading it is `stuck`. -/
theorem inlineHeap_read_stuck :
    HeapOK (E := SemanticsExamples.E0) inlineHeap ∧ HeapShaped (E := SemanticsExamples.E0) inlineHeap ∧
    ((readLoc (E := SemanticsExamples.E0) (Γ := []) SemanticsExamples.F0 (τ := .bytes .memory) (.mem 0 0)).run
      (.nil, { SemanticsExamples.s0 with heap := inlineHeap })).1 = .error (.stuck "inline aggregate element") :=
  ⟨HeapOK.empty.alloc (.array fun _ => .bytes _), HeapShaped.empty.alloc trivial, rfl⟩

/-- **Witness** (`zeroOK`): zeroing a `bool[2] memory` allocates one object,
at `0`, whose elements are bare values (`false`). -/
theorem zeroArr_alloc :
    (match ((zeroVal (E := SemanticsExamples.E0) (Γ := []) 6 (.array .memory .bool (some 2))).run
      (.nil, SemanticsExamples.s0)) with
    | (.ok (.memRef _ a), y) => some (a, y.2.heap.next)
    | _ => none) = some (0, 1) := by
  rfl

/-! ## Axioms -/

/-- info: 'Solidity.Source.binVal_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.binVal_ok
/-- info: 'Solidity.Source.cmpVal_ok' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Source.cmpVal_ok
/-- info: 'Solidity.Source.shiftVal_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.shiftVal_ok
/-- info: 'Solidity.Source.unaryVal_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.unaryVal_ok
/-- info: 'Solidity.Source.incDecVal_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.incDecVal_ok
/-- info: 'Solidity.Source.amount_ok' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Source.amount_ok
/-- info: 'Solidity.Source.convVal_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.convVal_ok
/-- info: 'Solidity.Source.constVal_ok' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.constVal_ok
/-- info: 'Solidity.Source.Typed.toR_opsOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.Typed.toR_opsOK
/-- info: 'Solidity.Source.StmtD.toR_opsOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.StmtD.toR_opsOK
/-- info: 'Solidity.Source.Elaborated.body_opsOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.Elaborated.body_opsOK
/-- info: 'Solidity.Source.Elaborated.inits_opsOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.Elaborated.inits_opsOK
/-- info: 'Solidity.Source.convRV_ns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.convRV_ns
/-- info: 'Solidity.Source.readAt_ns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.readAt_ns
/-- info: 'Solidity.Source.writeAt_ns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.writeAt_ns
/-- info: 'Solidity.Source.keyStep_nsp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.keyStep_nsp
/-- info: 'Solidity.Source.exprNSAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.exprNSAt
/-- info: 'Solidity.Source.evalE_valFrag_ns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.evalE_valFrag_ns
/-- info: 'Solidity.Source.stmtNSAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.stmtNSAt
/-- info: 'Solidity.Source.stmtNS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.stmtNS
/-- info: 'Solidity.Source.itemsNS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.itemsNS
/-- info: 'Solidity.Source.ItemsD.toR_ns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.ItemsD.toR_ns
/-- info: 'Solidity.Source.alloc_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.alloc_ok
/-- info: 'Solidity.Source.allocRef_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.allocRef_ok
/-- info: 'Solidity.Source.heapPut_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.heapPut_ok
/-- info: 'Solidity.Source.heapObj_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.heapObj_ok
/-- info: 'Solidity.Source.heapAt_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.heapAt_ok
/-- info: 'Solidity.Source.storRef_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.storRef_ok
/-- info: 'Solidity.Source.HeapOK.alloc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.HeapOK.alloc
/-- info: 'Solidity.Source.HeapOK.write' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.HeapOK.write
/-- info: 'Solidity.Source.heapObj_pres' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.heapObj_pres
/-- info: 'Solidity.Source.heapPut_pres' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.heapPut_pres
/-- info: 'Solidity.Source.DataListOK.setNth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.DataListOK.setNth
/-- info: 'Solidity.Source.DataListOK.nth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.DataListOK.nth
/-- info: 'Solidity.Source.asVal_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.asVal_ok
/-- info: 'Solidity.Source.memSet_pres' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.memSet_pres
/-- info: 'Solidity.Source.writeLoc_mem_pres' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.writeLoc_mem_pres
/-- info: 'Solidity.Source.writeLoc_memByte_pres' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.writeLoc_memByte_pres
/-- info: 'Solidity.Source.writeLoc_local_pres' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.writeLoc_local_pres
/-- info: 'Solidity.Source.memElem_pres' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.memElem_pres
/-- info: 'Solidity.Source.readLoc_local_pres' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.readLoc_local_pres
/-- info: 'Solidity.Source.readLoc_mem_pres' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.readLoc_mem_pres
/-- info: 'Solidity.Source.readLoc_memByte_pres' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.readLoc_memByte_pres
/-- info: 'Solidity.Source.SoundnessExamples.ptrHeap_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.SoundnessExamples.ptrHeap_ok
/-- info: 'Solidity.Source.SoundnessExamples.ptrHeap_byte_stuck' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.SoundnessExamples.ptrHeap_byte_stuck
/-- info: 'Solidity.Source.HeapShaped.empty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.HeapShaped.empty
/-- info: 'Solidity.Source.HeapShaped.alloc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.HeapShaped.alloc
/-- info: 'Solidity.Source.HeapShaped.write' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.HeapShaped.write
/-- info: 'Solidity.Source.heapObj_gen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.heapObj_gen
/-- info: 'Solidity.Source.heapObj_top' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.heapObj_top
/-- info: 'Solidity.Source.heapPut_shaped' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.heapPut_shaped
/-- info: 'Solidity.Source.writeLoc_memByte_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.writeLoc_memByte_ok
/-- info: 'Solidity.Source.STy.memShape_bytes' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Source.STy.memShape_bytes
/-- info: 'Solidity.Source.DataList.setNth_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.DataList.setNth_ok
/-- info: 'Solidity.Source.memSet_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.memSet_ok
/-- info: 'Solidity.Source.writeLoc_mem_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.writeLoc_mem_ok
/-- info: 'Solidity.Source.SoundnessExamples.arrHeap_write' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.SoundnessExamples.arrHeap_write
/-- info: 'Solidity.Source.SoundnessExamples.arrHeap_shaped' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.SoundnessExamples.arrHeap_shaped
/-- info: 'Solidity.Source.STy.memShape_array' depends on axioms: [propext] -/
#guard_msgs in #print axioms Solidity.Source.STy.memShape_array
/-- info: 'Solidity.Source.heapBytes_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.heapBytes_ok
/-- info: 'Solidity.Source.readLoc_memByte_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.readLoc_memByte_ok
/-- info: 'Solidity.Source.SoundnessExamples.bytesHeap_byte_read' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.SoundnessExamples.bytesHeap_byte_read
/-- info: 'Solidity.Source.SoundnessExamples.ptrHeap_byte_read_stuck' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.SoundnessExamples.ptrHeap_byte_read_stuck
/-- info: 'Solidity.Source.DataList.nth_val' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.DataList.nth_val
/-- info: 'Solidity.Source.heapObj_get' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.heapObj_get
/-- info: 'Solidity.Source.memElem_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.memElem_ok
/-- info: 'Solidity.Source.HeapInner.empty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.HeapInner.empty
/-- info: 'Solidity.Source.HeapInner.alloc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.HeapInner.alloc
/-- info: 'Solidity.Source.HeapInner.write' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.HeapInner.write
/-- info: 'Solidity.Source.readLoc_mem_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.readLoc_mem_ok
/-- info: 'Solidity.Source.SoundnessExamples.arrHeap_inner' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.SoundnessExamples.arrHeap_inner
/-- info: 'Solidity.Source.SoundnessExamples.arrHeap_read' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.SoundnessExamples.arrHeap_read
/-- info: 'Solidity.Source.SoundnessExamples.inlineHeap_read_stuck' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.SoundnessExamples.inlineHeap_read_stuck
/-- info: 'Solidity.Source.heapPut_inner' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.heapPut_inner
/-- info: 'Solidity.Source.DataList.AllVal.setNth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.DataList.AllVal.setNth
/-- info: 'Solidity.Source.memSet_inner' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.memSet_inner
/-- info: 'Solidity.Source.writeLoc_memByte_inner' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.writeLoc_memByte_inner
/-- info: 'Solidity.Source.MemOK.self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.MemOK.self
/-- info: 'Solidity.Source.Hoare.memGrow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.Hoare.memGrow
/-- info: 'Solidity.Source.Val.default_loc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.Val.default_loc
/-- info: 'Solidity.Source.allocRef_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.allocRef_mem
/-- info: 'Solidity.Source.zeroOK_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.zeroOK_zero
/-- info: 'Solidity.Source.zeroOK_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.zeroOK_step
/-- info: 'Solidity.Source.zeroOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.zeroOK
/-- info: 'Solidity.Source.SoundnessExamples.zeroArr_alloc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.SoundnessExamples.zeroArr_alloc
/-- info: 'Solidity.Source.SoundnessExamples.arrHeap_wrong_elem_stuck' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.SoundnessExamples.arrHeap_wrong_elem_stuck
/-- info: 'Solidity.Source.SoundnessExamples.ptrHeap_not_shaped' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.SoundnessExamples.ptrHeap_not_shaped
/-- info: 'Solidity.Source.SoundnessExamples.bytesHeap_shaped' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.SoundnessExamples.bytesHeap_shaped
/-- info: 'Solidity.Source.SoundnessExamples.bytesHeap_byte_write' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.SoundnessExamples.bytesHeap_byte_write
/-- info: 'Solidity.Source.SoundnessExamples.add_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.SoundnessExamples.add_value
/-- info: 'Solidity.Source.SoundnessExamples.add_bool_stuck' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.SoundnessExamples.add_bool_stuck
/-- info: 'Solidity.Source.SoundnessExamples.badBinary_not_opsOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.SoundnessExamples.badBinary_not_opsOK
/-- info: 'Solidity.Source.SoundnessExamples.badBinary_stuck' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.SoundnessExamples.badBinary_stuck
/-- info: 'Solidity.Source.SoundnessExamples.refOK_wrong_heap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.SoundnessExamples.refOK_wrong_heap
/-- info: 'Solidity.Source.SoundnessExamples.refOK_heap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.SoundnessExamples.refOK_heap
/-- info: 'Solidity.Source.SoundnessExamples.cond_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.SoundnessExamples.cond_value
/-- info: 'Solidity.Source.SoundnessExamples.loop_ns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.SoundnessExamples.loop_ns
/-- info: 'Solidity.Source.SoundnessExamples.loop_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.SoundnessExamples.loop_value
/-- info: 'Solidity.Source.SoundnessExamples.cb_ns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.SoundnessExamples.cb_ns
/-- info: 'Solidity.Source.SoundnessExamples.cb_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.SoundnessExamples.cb_value
/-- info: 'Solidity.Source.SoundnessExamples.ret_unframed_stuck' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.SoundnessExamples.ret_unframed_stuck
/-- info: 'Solidity.Source.SoundnessExamples.ret_unframed_no_frame' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.SoundnessExamples.ret_unframed_no_frame
/-- info: 'Solidity.Source.SoundnessExamples.ret_framed_ns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.SoundnessExamples.ret_framed_ns
/-- info: 'Solidity.Source.SoundnessExamples.stringByte_write' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.SoundnessExamples.stringByte_write
/-- info: 'Solidity.Source.SoundnessExamples.indexMapping_ns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.SoundnessExamples.indexMapping_ns
/-- info: 'Solidity.Source.SoundnessExamples.incBody_ns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.SoundnessExamples.incBody_ns
/-- info: 'Solidity.Source.itemsNSP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.itemsNSP
/-- info: 'Solidity.Source.runMods_nil_ns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.runMods_nil_ns
/-- info: 'Solidity.Source.callInternal_ns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.callInternal_ns
/-- info: 'Solidity.Source.retVals_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.retVals_ok
/-- info: 'Solidity.Source.SoundnessExamples.callRetOne_ns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.SoundnessExamples.callRetOne_ns
/-- info: 'Solidity.Source.SoundnessExamples.callBadFrame_stuck' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.SoundnessExamples.callBadFrame_stuck
/-- info: 'Solidity.Source.Decl.frame?_lengths' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.Decl.frame?_lengths
/-- info: 'Solidity.Source.Elaborated.body_locals' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.Elaborated.body_locals
/-- info: 'Solidity.Source.Elaborated.callInternal_ns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.Elaborated.callInternal_ns
/-- info: 'Solidity.Source.SoundnessExamples.retPair_ns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.SoundnessExamples.retPair_ns
/-- info: 'Solidity.Source.SoundnessExamples.retPair_unframed_stuck' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.SoundnessExamples.retPair_unframed_stuck
/-- info: 'Solidity.Source.Decl.frame?_fnSig' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.Decl.frame?_fnSig
/-- info: 'Solidity.Source.Elaborated.body_sig' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.Elaborated.body_sig
/-- info: 'Solidity.Source.Elaborated.callInternal_sig_ns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.Elaborated.callInternal_sig_ns
/-- info: 'Solidity.Source.Glob.dispatchFn_params' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.Glob.dispatchFn_params
/-- info: 'Solidity.Source.Elaborated.callInternal_call_ns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.Elaborated.callInternal_call_ns
/-- info: 'Solidity.Source.fragAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.fragAt
/-- info: 'Solidity.Source.evalE_callFrag_ns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.evalE_callFrag_ns
/-- info: 'Solidity.Source.stmt_callFrag_ns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.stmt_callFrag_ns
/-- info: 'Solidity.Source.callInternal_callFrag_ns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.callInternal_callFrag_ns
/-- info: 'Solidity.Source.SoundnessExamples.callF_ns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.SoundnessExamples.callF_ns
/-- info: 'Solidity.Source.SoundnessExamples.callF_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.SoundnessExamples.callF_value
/-- info: 'Solidity.Source.SoundnessExamples.callF_badFrame_stuck' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.SoundnessExamples.callF_badFrame_stuck
/-- info: 'Solidity.Source.evalConvArgs_ns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.evalConvArgs_ns
/-- info: 'Solidity.Source.setRets_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.setRets_ok
/-- info: 'Solidity.Source.SoundnessExamples.retLocalPair_ns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.SoundnessExamples.retLocalPair_ns
/-- info: 'Solidity.Source.SoundnessExamples.recF_ns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.SoundnessExamples.recF_ns
/-- info: 'Solidity.Source.SoundnessExamples.recF_timeout' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.SoundnessExamples.recF_timeout
/-- info: 'Solidity.Source.SoundnessExamples.callG_ns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.SoundnessExamples.callG_ns
/-- info: 'Solidity.Source.SoundnessExamples.callG_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.SoundnessExamples.callG_value

end Solidity.Source.SoundnessExamples
