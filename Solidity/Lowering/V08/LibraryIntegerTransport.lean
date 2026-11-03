import Solidity.Lowering.V08.SignedCallableControls
import Solidity.Lowering.V08.LibraryFrameTransport

/-! Actual caller-typed library execution of the proved integer-return Entry.
This uses existing library roles/accounts and ordinary-mode guards, not Source
library dispatch or ABI linkage. The argument is specialized as a typed literal.
The entire target world is retained; no second payment or library storage write.
Static mode refuses this nonempty body even though its final state is unchanged. -/
namespace Solidity.Lowering.V08.LibraryIntegerTransport
open Solidity ContractWorld
open Solidity.Lowering.V07
variable {K : Type} [DecidableEq K] {cs : K → Contract}

def library (caller kind : K) (address : Address) (decl : Source.Decl)
    (t : Source.IntTy) (n : Int) (h : t.lo ≤ n ∧ n ≤ t.hi) : Library cs caller (integerPrim t).Denote :=
  ⟨kind,address,IntegerCallable.entry (cs caller) decl t n h⟩

omit [DecidableEq K] in
theorem finish_local (w : World cs) {caller : K} (self : Handle caller) (ctx : Context)
    (store : Storage (cs caller)) (t : Source.IntTy) (n : Int) (h : t.lo ≤ n ∧ n ≤ t.hi)
    (present : w.accounts self.address = some ⟨caller,store⟩) :
    w.finish self.address ((LibraryFrameTransport.emptyFrame w self ctx store).push
      (t:=.val (integerPrim t)) (integerValue t n h)) = .ok w := by
  change w.finish self.address (LibraryFrameTransport.emptyFrame w self ctx store) = _
  exact LibraryFrameTransport.finish_empty w self ctx store present

theorem library_actual (w : World cs) (caller kind : K) (self : Handle caller)
    (address : Address) (ctx : Context)
    (runtime : LibraryFrameTransport.RuntimeInputs w caller kind self address)
    (ordinary : ctx.isStatic=false) (decl : Source.Decl) (t : Source.IntTy)
    (n : Int) (h : t.lo ≤ n ∧ n ≤ t.hi) :
    w.libraryCall self (library caller kind address decl t n h) ctx = .ok (w,integerValue t n h) := by
  have linked : w.storage? (⟨address⟩ : Handle kind) = some runtime.linked := by
    simp only [World.storage?,runtime.linkedAccount,bind,Option.bind]
    rfl
  have store : w.storage? self = some runtime.store := by
    simp only [World.storage?,runtime.callerAccount,bind,Option.bind]
    rfl
  unfold World.libraryCall library
  simp only [runtime.libraryRole,runtime.callerRole,Bool.not_true,Bool.false_or,
    ordinary,Bool.false_and,linked,store,TRes.ofOpt,bind,Except.bind]
  change (do
    let out ← (IntegerCallable.entry (cs caller) decl t n h).body.run
      (LibraryFrameTransport.emptyFrame w self ctx runtime.store)
    let next ← w.finish self.address out.st
    let value ← (IntegerCallable.entry (cs caller) decl t n h).result out.st
    pure (next,value)) = _
  rw [IntegerCallable.target_body]
  simp only [bind,Except.bind]
  rw [finish_local w self ctx runtime.store t n h runtime.callerAccount,IntegerCallable.target_result]
  rfl

theorem observed {α : Type} (observe : World cs → α) (w : World cs)
    (caller kind : K) (self : Handle caller) (address : Address) (ctx : Context)
    (runtime : LibraryFrameTransport.RuntimeInputs w caller kind self address)
    (ordinary : ctx.isStatic=false) (decl : Source.Decl) (t : Source.IntTy)
    (n : Int) (h : t.lo ≤ n ∧ n ≤ t.hi) :
    (w.libraryCall self (library caller kind address decl t n h) ctx).map
      (fun out => (observe out.1,out.2)) = .ok (observe w,integerValue t n h) := by
  rw [library_actual w caller kind self address ctx runtime ordinary decl t n h]
  rfl

theorem source_transport {E : Source.Env} (g : Source.Glob E) (f : Source.Fr)
    (decl : Source.Decl) (t : Source.IntTy) (selected : IntegerCallable.Inputs g f decl t)
    (source : Source.St E) (extra : Nat) (w : World cs) (caller kind : K)
    (self : Handle caller) (address : Address) (ctx : Context)
    (runtime : LibraryFrameTransport.RuntimeInputs w caller kind self address)
    (frame : LibraryFrameTransport.FrameInputs f self ctx) (ordinary : ctx.isStatic=false)
    (n : Int) (h : t.lo ≤ n ∧ n ≤ t.hi) :
    (Source.callInternal g f (extra+12) decl (.cons (.int n h) .nil) [.int t]).run
      (Source.L0 E,source) = (.ok (.val (.int n h)),(Source.L0 E,source)) ∧
    w.libraryCall self (library caller kind address decl t n h) ctx = .ok (w,integerValue t n h) ∧
    IntValueRel t (.int n h : Source.Val E.layout (.int t)) (integerValue t n h) ∧
    f.static=false :=
  ⟨IntegerCallable.source_call g f decl t selected extra source n h,
    library_actual w caller kind self address ctx runtime ordinary decl t n h,
    integer_related t n h,frame.static.trans ordinary⟩

theorem populated_client (p : Roadmap.Pipeline) (extra : Nat) (bytes : Roadmap.Bytes) :
    (Source.callInternal (SignedCallableControls.global p) SignedCallableControls.frame (extra+12)
      SignedCallableControls.declaration (.cons SignedCallableControls.minimum .nil)
      [.int SignedCallableControls.t]).run
      (Source.L0 SignedCallableControls.E,SignedCallableControls.populated bytes) =
        (.ok (.val SignedCallableControls.minimum),
          (Source.L0 SignedCallableControls.E,SignedCallableControls.populated bytes)) ∧
    LibraryHandlerControls.outer.libraryCall (⟨Controls.self⟩ : Handle false)
      (library false true LibraryHandlerControls.link SignedCallableControls.declaration
        SignedCallableControls.t (-128) (by decide +kernel)) Controls.paidCtx =
      .ok (LibraryHandlerControls.outer,integerValue SignedCallableControls.t (-128) (by decide +kernel)) := by
  obtain ⟨runtime⟩ := LibraryFrameTransport.runtime_of_success
    LibraryHandlerControls.outer LibraryHandlerControls.handled (⟨Controls.self⟩ : Handle false)
    LibraryHandlerControls.library Controls.paidCtx LibraryHandlerControls.expected
    LibraryHandlerControls.delegated_reached
  have combined := source_transport (SignedCallableControls.global p) SignedCallableControls.frame
    SignedCallableControls.declaration SignedCallableControls.t (SignedCallableControls.inputs p)
    (SignedCallableControls.populated bytes) extra LibraryHandlerControls.outer false true
    (⟨Controls.self⟩ : Handle false) LibraryHandlerControls.link Controls.paidCtx runtime
    ⟨rfl,rfl,rfl,rfl⟩ rfl (-128) (by decide +kernel)
  exact ⟨combined.1,combined.2.1⟩

theorem static_refusal (w : World cs) (caller kind : K) (self : Handle caller)
    (address : Address) (ctx : Context) (static : ctx.isStatic=true)
    (decl : Source.Decl) (t : Source.IntTy) (n : Int) (h : t.lo ≤ n ∧ n ≤ t.hi) :
    w.libraryCall self (library caller kind address decl t n h) ctx = .error .revert := by
  simp only [World.libraryCall,library,IntegerCallable.entry,emptyBody,static,Bool.not_false,
    Bool.true_and,Bool.or_true,if_true]

theorem no_second_payment (w : World cs) (caller kind : K) (self : Handle caller)
    (address : Address) (ctx : Context)
    (runtime : LibraryFrameTransport.RuntimeInputs w caller kind self address)
    (ordinary : ctx.isStatic=false) (decl : Source.Decl) (t : Source.IntTy)
    (n : Int) (h : t.lo ≤ n ∧ n ≤ t.hi) :
    (w.libraryCall self (library caller kind address decl t n h) ctx).map
      (fun out => (out.1.funds,out.2)) = .ok (w.funds,integerValue t n h) :=
  observed (fun next => next.funds) w caller kind self address ctx runtime ordinary decl t n h

theorem all_accounts_retained (w : World cs) (caller kind : K) (self : Handle caller)
    (address : Address) (ctx : Context)
    (runtime : LibraryFrameTransport.RuntimeInputs w caller kind self address)
    (ordinary : ctx.isStatic=false) (decl : Source.Decl) (t : Source.IntTy)
    (n : Int) (h : t.lo ≤ n ∧ n ≤ t.hi) :
    (w.libraryCall self (library caller kind address decl t n h) ctx).map
      (fun out => (out.1.accounts,out.2)) = .ok (w.accounts,integerValue t n h) :=
  observed (fun next => next.accounts) w caller kind self address ctx runtime ordinary decl t n h

theorem wrong_signed_value (p : Roadmap.Pipeline) (bytes : Roadmap.Bytes) :
    (LibraryHandlerControls.outer.libraryCall (⟨Controls.self⟩ : Handle false)
      (library false true LibraryHandlerControls.link SignedCallableControls.declaration
        SignedCallableControls.t (-128) (by decide +kernel)) Controls.paidCtx).toOption.map
        (fun out => PrimTy.num? out.2) ≠ some (some 128) := by
  rw [(populated_client p 0 bytes).2]
  simp only [Except.toOption,Option.map,integer_observe]
  intro wrong
  cases wrong

/-- info: 'Solidity.Lowering.V08.LibraryIntegerTransport.finish_local' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.LibraryIntegerTransport.finish_local

/-- info: 'Solidity.Lowering.V08.LibraryIntegerTransport.library_actual' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.LibraryIntegerTransport.library_actual

/-- info: 'Solidity.Lowering.V08.LibraryIntegerTransport.observed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.LibraryIntegerTransport.observed

/-- info: 'Solidity.Lowering.V08.LibraryIntegerTransport.source_transport' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.LibraryIntegerTransport.source_transport

/-- info: 'Solidity.Lowering.V08.LibraryIntegerTransport.populated_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.LibraryIntegerTransport.populated_client

/-- info: 'Solidity.Lowering.V08.LibraryIntegerTransport.static_refusal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.LibraryIntegerTransport.static_refusal

/-- info: 'Solidity.Lowering.V08.LibraryIntegerTransport.no_second_payment' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.LibraryIntegerTransport.no_second_payment

/-- info: 'Solidity.Lowering.V08.LibraryIntegerTransport.all_accounts_retained' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.LibraryIntegerTransport.all_accounts_retained

/-- info: 'Solidity.Lowering.V08.LibraryIntegerTransport.wrong_signed_value' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.LibraryIntegerTransport.wrong_signed_value
end Solidity.Lowering.V08.LibraryIntegerTransport
