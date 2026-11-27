import Solidity.Source.ValueProgress
import Solidity.Source.WellTyped
import Solidity.Source.TypingExamples
import Solidity.Source.StmtProgress
import Solidity.Source.SemanticsExamples


namespace Solidity.Source.SoundnessExamples

open Solidity.Source

variable {D : Layout}

def one8 : Val D (.int IntTy.u8) := .int 1 (by decide)
def two8 : Val D (.int IntTy.u8) := .int 2 (by decide)

theorem add_ok : NotStuckR (binVal (D := D) true .add one8 two8) :=
  binVal_ok true (.inl ⟨rfl, rfl⟩) _ _

theorem add_value : (binVal (D := D) true .add one8 two8) = .ok (.int 3 (by decide)) := rfl

theorem add_bool_stuck :
    binVal (D := D) true .add (.bool true) (.bool false) = .error (.stuck "not a boolean operation") := rfl

theorem add_bool_outside : ¬ BinOp.add.FitsAt .bool := by
  intro h
  rcases h with ⟨_, h⟩ | ⟨_, h⟩ | ⟨h, _⟩ <;> cases h

theorem cmp_add_stuck : cmpVal (D := D) .add one8 two8 = .error (.stuck "not a comparison") := rfl

theorem shift_bool_stuck : shiftVal (D := D) true .shl 1 (.bool true) = .error (.stuck "shift operand") := rfl

open TypingExamples in
theorem addSub_opsOK : w_addSub.toR.OpsOK := Typed.toR_opsOK _

open TypingExamples in
theorem order_opsOK : w_order.toR.OpsOK := Typed.toR_opsOK _

open TypingExamples in
theorem shift_opsOK : w_shift.toR.OpsOK := Typed.toR_opsOK _

theorem badBinary_not_opsOK {E : Env} :
    ¬ (RExpr.binary (E := E) (Γ := []) .add (.bool true) (.bool false)).OpsOK := by
  intro h
  rcases h.1 with ⟨_, h⟩ | ⟨_, h⟩ | ⟨h, _⟩ <;> cases h

example (C : Ctx) (e : Syn .expr) :
    ¬ ∃ d : Typed C e .bool,
      d.toR = RExpr.binary (E := C.env) (Γ := C.tys)
        .add (.bool true) (.bool false) := by
  rintro ⟨d, same⟩
  have domain := Typed.toR_opsOK d
  rw [same] at domain
  rcases domain.1 with ⟨_, h⟩ | ⟨_, h⟩ | ⟨h, _⟩ <;> cases h

theorem refOK_wrong_heap {E : Env} :
    ¬ (Val.memRef (D := E.layout) (τ := .bytes .memory) rfl 0).RefOK E (fun _ => some .bool) := by
  intro ⟨σ, h1, h2⟩
  cases h1
  cases h2

theorem refOK_heap {E : Env} :
    (Val.memRef (D := E.layout) (τ := .bytes .memory) rfl 0).RefOK E (fun _ => some (.bytes .memory)) ∧
    (Val.memRef (D := E.layout) (τ := .bytes .memory) rfl 0).RefOK E (fun _ => some (.string .memory)) :=
  ⟨⟨_, rfl, rfl⟩, ⟨_, rfl, rfl⟩⟩


open TypingExamples in
theorem addSub_ns (G : Glob Γ.env) (F : Fr) (n : Nat) : NS (evalE G F n w_addSub.toR) :=
  evalE_valFrag_ns G F n _ ⟨⟨rfl, rfl, .inl rfl⟩, ⟨rfl, rfl, .inl rfl⟩, rfl⟩ (Typed.toR_opsOK _)

theorem badBinary_stuck :
    ((evalE (SemanticsExamples.G0 .viaIR) SemanticsExamples.F0 3
      (RExpr.binary (E := SemanticsExamples.E0) (Γ := []) .add (.bool true) (.bool false))).run
      (.nil, SemanticsExamples.s0)).1 = .error (.stuck "not a boolean operation") := by
  rfl

def condE : RExpr SemanticsExamples.E0 [] (.int IntTy.u8) :=
  .cond (.bool true)
    (.binary .add (.conv (.const (Q.ofInt 1)) (.inl (by decide))) (.conv (.const (Q.ofInt 2)) (.inl (by decide))))
    (.conv (.const (Q.ofInt 0)) (.inl (by decide)))

theorem cond_ns (n : Nat) : NS (evalE (SemanticsExamples.G0 .viaIR) SemanticsExamples.F0 n condE) :=
  evalE_valFrag_ns _ _ n condE
    ⟨trivial, ⟨⟨trivial, rfl, .inr (.inl ⟨_, rfl⟩)⟩, ⟨trivial, rfl, .inr (.inl ⟨_, rfl⟩)⟩, rfl⟩,
      ⟨trivial, rfl, .inr (.inl ⟨_, rfl⟩)⟩, rfl⟩
    ⟨trivial, ⟨.inl ⟨rfl, rfl⟩, trivial, trivial⟩, trivial⟩

theorem cond_value :
    ((evalE (SemanticsExamples.G0 .viaIR) SemanticsExamples.F0 5 condE).run (.nil, SemanticsExamples.s0)).1.toOption.map
      (fun v => match v with | .val x => x.key) = some (some 3) := by
  rfl

def loopCond : RExpr SemanticsExamples.E0 [.int IntTy.u8] .bool :=
  .compare .lt (.local .here) (.conv (.const (Q.ofInt 3)) (.inl (by decide)))

def loopBody : RStmt SemanticsExamples.E0 [] false ⟨true, false⟩ [.int IntTy.u8] [.int IntTy.u8] :=
  .expr (.compound .add (.local .here) (.const (Q.ofInt 1)) (by decide))

def loopItems : RItems SemanticsExamples.E0 [] false .body [] [.int IntTy.u8] :=
  .stmt (.declVar (.int IntTy.u8)) (.stmt (.whileLoop loopCond loopBody) .nil)

theorem loopItems_frag : loopItems.ValFrag :=
  ⟨rfl, ⟨⟨rfl, ⟨trivial, rfl, .inr (.inl ⟨_, rfl⟩)⟩, rfl⟩, ⟨trivial, trivial, rfl, .inr (.inl ⟨_, rfl⟩)⟩⟩, trivial⟩

theorem loopItems_ops : loopItems.OpsOK :=
  ⟨trivial, ⟨⟨⟨rfl, rfl, trivial, trivial⟩, ⟨trivial, trivial⟩⟩, trivial⟩⟩

theorem loop_ns (n : Nat) :
    NS (execItems (SemanticsExamples.G0 .viaIR) SemanticsExamples.F0 n 0 none loopItems .nil) :=
  itemsNS _ _ n 0 none loopItems .nil loopItems_frag loopItems_ops ⟨[], [], rfl, rfl⟩

theorem loop_value :
    (match ((execItems (SemanticsExamples.G0 .viaIR) SemanticsExamples.F0 40 0 none loopItems .nil).run
      (.nil, SemanticsExamples.s0)).1 with
    | .ok (.normal (.cons v .nil)) => v.key
    | _ => none) = some 3 := by
  rfl

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
theorem cb_ns (n : Nat) (F : Fr) (s : Option (Ph EB)) :
    NS (execItems (GB answerOnly) F n 0 s cbBody.items .nil) :=
  itemsNS _ F n 0 s _ .nil cbItems_frag cbItems_ops ⟨[], [], rfl, rfl⟩

open SemanticsExamples in
theorem cb_value :
    (match (execItems (GB answerOnly) FC 10 0 none cbBody.items .nil).run (.nil, sB) with
    | (.ok _, (_, s)) => readX s
    | _ => none) = some 4 := by
  rfl

theorem ret_unframed_no_frame : ¬ BodyFrame 0 [.int IntTy.u8] [] := by
  intro ⟨ys, ps, h, _⟩
  have := congrArg List.length h
  simp only [List.length_nil, List.length_append, List.length_reverse, List.length_singleton] at this
  omega

theorem ret_framed_ns (n : Nat) (l : Locals SemanticsExamples.E0.layout [.int IntTy.u8]) :
    NS (execS (SemanticsExamples.G0 .viaIR) SemanticsExamples.F0 n 0 none
      (RStmt.retVal (E := SemanticsExamples.E0) (R := [.int IntTy.u8]) (M := false) (k := .body)
        rfl (.const (Q.ofInt 1)) (by decide)) l) :=
  stmtNS _ _ n 0 none _ l ⟨trivial, rfl, .inr (.inl ⟨_, rfl⟩)⟩ trivial ⟨[], [], rfl, rfl⟩

def retPair : RStmt SemanticsExamples.E0 [.int IntTy.u8, .int IntTy.u8] false .body Γ Γ :=
  .retTuple (.cons (.const (Q.ofInt 1)) (by decide) (.cons (.const (Q.ofInt 2)) (by decide) .nil))

theorem retPair_ns (n : Nat) (l : Locals SemanticsExamples.E0.layout [.int IntTy.u8, .int IntTy.u8]) :
    NS (execS (SemanticsExamples.G0 .viaIR) SemanticsExamples.F0 n 0 none (retPair (Γ := _)) l) :=
  stmtNS _ _ n 0 none _ l ⟨trivial, rfl, .inr (.inl ⟨_, rfl⟩), trivial, rfl, .inr (.inl ⟨_, rfl⟩), trivial⟩
    ⟨trivial, trivial, trivial⟩ ⟨[], [], rfl, rfl⟩

theorem retPair_unframed_stuck :
    ((execS (SemanticsExamples.G0 .viaIR) SemanticsExamples.F0 5 0 none (retPair (Γ := [])) .nil).run
      (.nil, SemanticsExamples.s0)).1 = .error (.stuck "no local") := by
  rfl

def retLocalPair : RStmt SemanticsExamples.E0 [.int IntTy.u8, .int IntTy.u8] false .body
    [.int IntTy.u8, .int IntTy.u8, .int IntTy.u8] [.int IntTy.u8, .int IntTy.u8, .int IntTy.u8] :=
  .retTuple (.cons (.local .here) (by decide) (.cons (.local .here) (by decide) .nil))

theorem retLocalPair_ns (n : Nat)
    (l : Locals SemanticsExamples.E0.layout [.int IntTy.u8, .int IntTy.u8, .int IntTy.u8]) :
    NS (execS (SemanticsExamples.G0 .viaIR) SemanticsExamples.F0 n 0 none retLocalPair l) :=
  stmtNS _ _ n 0 none _ l ⟨rfl, rfl, .inl rfl, rfl, rfl, .inl rfl, trivial⟩ ⟨trivial, trivial, trivial⟩
    ⟨[.int IntTy.u8], [], rfl, rfl⟩


open TypingExamples in
theorem indexMapping_ns (G : Glob Γ.env) (F : Fr) (n : Nat) : NS (evalE G F n w_index_mapping.toR) :=
  evalE_valFrag_ns G F n _ (by
    exact ⟨⟨rfl, rfl, _, _, rfl⟩, ⟨rfl, rfl, .inl rfl⟩, rfl, rfl, rfl⟩) (Typed.toR_opsOK _)

open TypingExamples in
theorem incBody_ns (G : Glob Examples.counter.env) (F : Fr) (n : Nat) :
    NS (execItems G F n 0 none incBody.toR .nil) :=
  ItemsD.toR_ns G F n 0 none incBody .nil (by
    exact ⟨⟨rfl, rfl, rfl⟩, trivial⟩) ⟨[], [], rfl, rfl⟩


open SemanticsExamples in
def retOneBody : RBody E0 where
  ps := []
  rs := [u8]
  inModifier := false
  locals := [u8]
  out := [u8]
  items := .stmt (.retVal rfl (.const (Q.ofInt 1)) (by decide)) .nil

open SemanticsExamples in
def badFrameBody : RBody E0 where
  ps := []
  rs := [u8]
  inModifier := false
  locals := []
  out := []
  items := .nil

open SemanticsExamples in
def progOf (b : RBody E0) : Glob E0 :=
  ⟨{ P0 with body := fun _ => some b }, .viaIR, toyFixed, fun _ => word 0, fun _ _ => false,
    fun _ => .answer (.success []), word 0⟩

open SemanticsExamples in
theorem callRetOne_ns (d : Decl) (n : Nat) :
    NS (callInternal (progOf retOneBody) F0 n d (ps := []) .nil [u8]) :=
  callInternal_ns _ _ n d .nil [u8] retOneBody rfl rfl rfl rfl rfl
    (fun τ h => by simp only [List.mem_cons, List.not_mem_nil, or_false] at h; subst h; rfl)
    ⟨⟨trivial, rfl, .inr (.inl ⟨_, rfl⟩)⟩, trivial⟩ ⟨trivial, trivial⟩

open SemanticsExamples in
theorem callBadFrame_stuck (d : Decl) :
    ((callInternal (progOf badFrameBody) F0 5 d (ps := []) .nil [u8]).run (.nil, s0)).1 =
      .error (.stuck "call frame") := by
  rfl


def fDecl : Decl := ⟨.function, "f", none, false,
  .function (.ident "f") .nil (some .internal) none .nil false none
    (.cons (.param (.elem (.int false 8 (by decide))) none none) .nil) (.some (.block .nil))⟩

theorem fDecl_sig : fDecl.fnSig SemanticsExamples.E0 = some ([], [.int IntTy.u8]) := rfl

def callF : RExpr SemanticsExamples.E0 [] (STy.ret [.int IntTy.u8]) := .call fDecl fDecl_sig .nil

open SemanticsExamples in
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
theorem callF_ns (n : Nat) : NS (evalE (progOf retOneBody) F0 n callF) :=
  evalE_callFrag_ns retOne_callsOK F0 rfl n callF ⟨rfl, trivial⟩ trivial

open SemanticsExamples in
theorem callF_value : intOf ((evalE (progOf retOneBody) F0 10 callF).run (.nil, s0)) = some 1 := by
  rfl

open SemanticsExamples in
theorem callF_badFrame_stuck :
    ((evalE (progOf badFrameBody) F0 10 callF).run (.nil, s0)).1 = .error (.stuck "call frame") := by
  rfl

open SemanticsExamples in
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
theorem recF_ns (n : Nat) : NS (evalE (progOf recBody) F0 n callF) :=
  evalE_callFrag_ns rec_callsOK F0 rfl n callF ⟨rfl, trivial⟩ trivial

open SemanticsExamples in
theorem recF_timeout : ((evalE (progOf recBody) F0 12 callF).run (.nil, s0)).1 = .error .timeout := by
  rfl

def gDecl : Decl := ⟨.function, "g", none, false,
  .function (.ident "g") .nil (some .internal) none .nil false none
    (.cons (.param (.elem (.int false 8 (by decide))) none none) .nil) (.some (.block .nil))⟩

theorem gDecl_sig : gDecl.fnSig SemanticsExamples.E0 = some ([], [.int IntTy.u8]) := rfl

open SemanticsExamples in
def gBody : RBody E0 where
  ps := []
  rs := [u8]
  inModifier := false
  locals := [u8]
  out := [u8]
  items := .stmt (.retVal rfl (.call fDecl fDecl_sig .nil) (by decide)) .nil

open SemanticsExamples in
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

def callG : RExpr SemanticsExamples.E0 [] (STy.ret [.int IntTy.u8]) := .call gDecl gDecl_sig .nil

open SemanticsExamples in
theorem callG_ns (n : Nat) : NS (evalE progFG F0 n callG) :=
  evalE_callFrag_ns fg_callsOK F0 rfl n callG ⟨Or.inr rfl, trivial⟩ trivial

open SemanticsExamples in
theorem callG_value : intOf ((evalE progFG F0 12 callG).run (.nil, s0)) = some 1 := by
  rfl



def strItems : RItems SemanticsExamples.E0 [] false .body []
    [.fixedBytes 1 (by decide), .string .memory] :=
  .stmt (.declInit (.str [97, 98, 99]) (by decide))
    (.stmt (.expr (.assign
      (.indexBytes (.convExplicit (.local .here) (τ := .bytes .memory) (by decide)) (by decide) (.const (Q.ofInt 0)) (by decide))
      (.conv (.bytesLit (.hex [7, 8] false) 1) (.inl (by decide)))))
    (.stmt (.declInit (.indexBytes (.convExplicit (.local .here) (τ := .bytes .memory) (by decide))
        (.const (Q.ofInt 0)) (by decide)) (by decide)) .nil))

theorem stringByte_write :
    (match ((execItems (SemanticsExamples.G0 .viaIR) SemanticsExamples.F0 20 0 none strItems .nil).run
      (.nil, SemanticsExamples.s0)).1 with
    | .ok (.normal (.cons b _)) => b.key
    | _ => none) = some 0x78 := by
  rfl


def ptrHeap : Heap SemanticsExamples.E0.layout :=
  (((Heap.empty : Heap SemanticsExamples.E0.layout).alloc ⟨.bytes .memory, .bytes [1]⟩).1.alloc
    ⟨.bytes .memory, .val (Val.memRef rfl 0)⟩).1

theorem ptrHeap_ok : HeapOK (E := SemanticsExamples.E0) ptrHeap :=
  (HeapOK.empty.alloc (.bytes _)).alloc (.val ⟨_, rfl, rfl⟩)

theorem ptrHeap_byte_stuck :
    ((writeLoc (E := SemanticsExamples.E0) (Γ := []) SemanticsExamples.F0 3 (.memByte 1 0)
      (Val.fixedBytes [7] rfl)).run (.nil, { SemanticsExamples.s0 with heap := ptrHeap })).1 =
      .error (.stuck "not bytes") := by
  rfl

theorem ptrHeap_not_shaped : ¬ HeapShaped (E := SemanticsExamples.E0) ptrHeap := fun h => by
  have ht := h 1 _ rfl
  simp only [Data.Top, STy.loc?, reduceCtorEq] at ht

def bytesHeap : Heap SemanticsExamples.E0.layout :=
  ((Heap.empty : Heap SemanticsExamples.E0.layout).alloc ⟨.bytes .memory, .bytes [1]⟩).1

theorem bytesHeap_shaped : HeapShaped (E := SemanticsExamples.E0) bytesHeap :=
  HeapShaped.empty.alloc trivial

theorem bytesHeap_byte_write :
    ((writeLoc (E := SemanticsExamples.E0) (Γ := []) SemanticsExamples.F0 3 (.memByte 0 0)
      (Val.fixedBytes [7] rfl)).run (.nil, { SemanticsExamples.s0 with heap := bytesHeap })).1 = .ok () := by
  rfl

def arrHeap : Heap SemanticsExamples.E0.layout :=
  ((Heap.empty : Heap SemanticsExamples.E0.layout).alloc
    ⟨.array .memory .bool none, .array 1 (fun _ h => nomatch h) fun _ => .val (.bool false)⟩).1

theorem arrHeap_shaped : HeapShaped (E := SemanticsExamples.E0) arrHeap :=
  HeapShaped.empty.alloc trivial

theorem arrHeap_write :
    ((writeLoc (E := SemanticsExamples.E0) (Γ := []) SemanticsExamples.F0 3 (.mem 0 0)
      (Val.bool true)).run (.nil, { SemanticsExamples.s0 with heap := arrHeap })).1 = .ok () := by
  rfl

theorem arrHeap_wrong_elem_stuck :
    ((writeLoc (E := SemanticsExamples.E0) (Γ := []) SemanticsExamples.F0 3 (.mem 0 0)
      (Val.address (p := false) (SemanticsExamples.addr 1))).run (.nil, { SemanticsExamples.s0 with heap := arrHeap })).1 =
      .error (.stuck "element type") := by
  rfl

theorem bytesHeap_byte_read :
    (match ((readLoc (E := SemanticsExamples.E0) (Γ := []) SemanticsExamples.F0 (.memByte 0 0)).run
      (.nil, { SemanticsExamples.s0 with heap := bytesHeap })).1 with
    | .ok (.fixedBytes bs _) => some bs
    | _ => none) = some [1] := by
  rfl

theorem ptrHeap_byte_read_stuck :
    ((readLoc (E := SemanticsExamples.E0) (Γ := []) SemanticsExamples.F0 (.memByte 1 0)).run
      (.nil, { SemanticsExamples.s0 with heap := ptrHeap })).1 = .error (.stuck "not a bytes object") := by
  rfl

theorem arrHeap_inner : HeapInner (E := SemanticsExamples.E0) arrHeap :=
  HeapInner.empty.alloc fun _ => ⟨_, rfl⟩

theorem arrHeap_read :
    ((readLoc (E := SemanticsExamples.E0) (Γ := []) SemanticsExamples.F0 (τ := .bool) (.mem 0 0)).run
      (.nil, { SemanticsExamples.s0 with heap := arrHeap })).1 = .ok (.bool false) := by
  rfl

def inlineHeap : Heap SemanticsExamples.E0.layout :=
  ((Heap.empty : Heap SemanticsExamples.E0.layout).alloc
    ⟨.array .memory (.bytes .memory) none, .array 1 (fun _ h => nomatch h) fun _ => .bytes [1]⟩).1

theorem inlineHeap_read_stuck :
    HeapOK (E := SemanticsExamples.E0) inlineHeap ∧ HeapShaped (E := SemanticsExamples.E0) inlineHeap ∧
    ((readLoc (E := SemanticsExamples.E0) (Γ := []) SemanticsExamples.F0 (τ := .bytes .memory) (.mem 0 0)).run
      (.nil, { SemanticsExamples.s0 with heap := inlineHeap })).1 = .error (.stuck "inline aggregate element") :=
  ⟨HeapOK.empty.alloc (.array fun _ => .bytes _), HeapShaped.empty.alloc trivial, rfl⟩

theorem zeroArr_alloc :
    (match ((zeroVal (E := SemanticsExamples.E0) (Γ := []) 6 (.array .memory .bool (some 2))).run
      (.nil, SemanticsExamples.s0)) with
    | (.ok (.memRef _ a), y) =>
      match y.2.heap.get 0 with
      | some ⟨_, .array 2 _ xs⟩ =>
        some (a, y.2.heap.next, (List.finRange 2).map fun j => match xs j with
          | .val (.bool b) => some b
          | _ => none)
      | _ => none
    | _ => none) = some (0, 1, [some false, some false]) := by
  rfl

theorem arrHeap_delete :
    (match ((do
        writeLoc SemanticsExamples.F0 3 (.mem 0 0) (Val.bool true)
        deleteLoc (E := SemanticsExamples.E0) (Γ := []) SemanticsExamples.F0 3 (τ := .bool) (.mem 0 0)).run
      (.nil, { SemanticsExamples.s0 with heap := arrHeap })) with
    | (.ok (), y) =>
      match y.2.heap.get 0 with
      | some ⟨_, .array 1 _ xs⟩ =>
        some (y.2.heap.next, match xs 0 with
          | .val (.bool b) => some b
          | _ => none)
      | _ => none
    | _ => none) = some (1, some false) := by
  rfl

def arrPath : SPath := ⟨⟨some "C", "arr"⟩, []⟩

def copyArr : EM TypingExamples.Γ.env [] (Option (List Nat)) := do
  writeLen SemanticsExamples.F0 arrPath 2
  writeAt SemanticsExamples.F0 (arrPath.go (.index 0)) (intWrap (D := TypingExamples.Γ.env.layout) IntTy.u256 7)
  writeAt SemanticsExamples.F0 (arrPath.go (.index 1)) (intWrap (D := TypingExamples.Γ.env.layout) IntTy.u256 9)
  let v ← loadElem SemanticsExamples.F0 6 (.array .memory (.int IntTy.u256) none) arrPath
  match v with
  | .memRef _ a =>
    match (← EM.st).heap.get a with
    | some ⟨_, .array n _ xs⟩ =>
      pure (some ((List.finRange n).map fun j => match xs j with
        | .val (.int i _) => i.toNat
        | _ => 0))
    | _ => pure none
  | _ => pure none

theorem copyArr_value :
    ((copyArr.run (.nil, SemanticsExamples.s0)).1 matches .ok (some [7, 9])) = true := by
  decide

example :
    let before : EMState TypingExamples.Γ.env [] := (.nil, SemanticsExamples.s0)
    let copied := copyArr.run before
    before.2.heap.get before.2.heap.next = none ∧
      copied.2.2.heap.next = before.2.heap.next + 1 ∧
      copied.2.2.heap.ty before.2.heap.next =
        some (.array .memory (.int IntTy.u256) none) ∧
      (match copied.2.2.heap.get before.2.heap.next with
      | some ⟨_, .array 2 _ elements⟩ =>
        some ((List.finRange 2).map fun index => match elements index with
          | .val (.int value _) => some value
          | _ => none)
      | _ => none) = some [some 7, some 9] := by
  constructor
  · rfl
  · decide

def roundTrip : EM TypingExamples.Γ.env [] (Option (List Nat)) := do
  let a ← allocRef (τ := .array .memory (.int IntTy.u256) none)
    (Data.array 2 (fun _ h => nomatch h) fun j =>
      .val (intWrap (D := TypingExamples.Γ.env.layout) IntTy.u256 (7 + 2 * j.val)))
  storeVal SemanticsExamples.F0 6 (.array .storage (.int IntTy.u256) none) arrPath a
  let v ← loadElem SemanticsExamples.F0 6 (.array .memory (.int IntTy.u256) none) arrPath
  match v with
  | .memRef _ b =>
    match (← EM.st).heap.get b with
    | some ⟨_, .array n _ xs⟩ =>
      pure (some ((List.finRange n).map fun j => match xs j with
        | .val (.int i _) => i.toNat
        | _ => 0))
    | _ => pure none
  | _ => pure none

theorem roundTrip_value :
    ((roundTrip.run (.nil, SemanticsExamples.s0)).1 matches .ok (some [7, 9])) = true := by
  decide


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
/-- info: 'Solidity.Source.Hoare.and' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.Hoare.and
/-- info: 'Solidity.Source.heapPut_top' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.heapPut_top
/-- info: 'Solidity.Source.memSet_top' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.memSet_top
/-- info: 'Solidity.Source.writeLoc_memByte_top' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.writeLoc_memByte_top
/-- info: 'Solidity.Source.writeLoc_local_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.writeLoc_local_mem
/-- info: 'Solidity.Source.writeLoc_mem_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.writeLoc_mem_mem
/-- info: 'Solidity.Source.writeLoc_memByte_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.writeLoc_memByte_mem
/-- info: 'Solidity.Source.deleteLoc_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.deleteLoc_mem
/-- info: 'Solidity.Source.SoundnessExamples.arrHeap_delete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.SoundnessExamples.arrHeap_delete
/-- info: 'Solidity.Source.readCell_keep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.readCell_keep
/-- info: 'Solidity.Source.readAt_keep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.readAt_keep
/-- info: 'Solidity.Source.readLen_keep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.readLen_keep
/-- info: 'Solidity.Source.loadBytes_keep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.loadBytes_keep
/-- info: 'Solidity.Source.allocRef_mem'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.allocRef_mem'
/-- info: 'Solidity.Source.STy.loc_of_byRef' does not depend on any axioms -/
#guard_msgs in #print axioms Solidity.Source.STy.loc_of_byRef
/-- info: 'Solidity.Source.loadOK_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.loadOK_zero
/-- info: 'Solidity.Source.loadOK_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.loadOK_step
/-- info: 'Solidity.Source.loadOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.loadOK
/-- info: 'Solidity.Source.SoundnessExamples.copyArr_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.SoundnessExamples.copyArr_value
/-- info: 'Solidity.Source.applyOp_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.applyOp_mem
/-- info: 'Solidity.Source.setCell_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.setCell_mem
/-- info: 'Solidity.Source.writeAt_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.writeAt_mem
/-- info: 'Solidity.Source.writeLen_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.writeLen_mem
/-- info: 'Solidity.Source.deleteOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.deleteOK
/-- info: 'Solidity.Source.storeOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.storeOK
/-- info: 'Solidity.Source.writeLoc_stor_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.writeLoc_stor_mem
/-- info: 'Solidity.Source.deleteLoc_stor_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.deleteLoc_stor_mem
/-- info: 'Solidity.Source.writeLoc_memOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.writeLoc_memOK
/-- info: 'Solidity.Source.deleteLoc_memOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.deleteLoc_memOK
/-- info: 'Solidity.Source.SoundnessExamples.roundTrip_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Source.SoundnessExamples.roundTrip_value
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
