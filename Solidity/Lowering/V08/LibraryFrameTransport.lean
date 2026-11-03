import Solidity.Lowering.V07.SourceReads
import Solidity.Lowering.V08.SourceEnvironmentControls
import Solidity.Lowering.V08.LibraryHandlerControls

/-! Actual independent Source context reads and caller-typed library execution.
RuntimeInputs certify code-role/account identity, not execution/preservation.
FrameInputs are the exact P1 input correspondence still required from a real
lowerer. This primitive component does not resolve source library dispatch. -/
namespace Solidity.Lowering.V08.LibraryFrameTransport
open Solidity
open Solidity.ContractWorld
variable {K : Type} [DecidableEq K] {contracts : K → Contract}

abbrev Observation := Int × Int × Int

def entry (C : Contract) : Entry C Observation :=
  {locals:=[],body:=.nil,result:=fun state =>
    .ok (state.tx.msgSender.1,state.tx.msgValue.1,state.tx.selfAddress.1)}
def library (caller kind : K) (address : Address) : Library contracts caller Observation :=
  ⟨kind,address,entry (contracts caller)⟩

structure RuntimeInputs (w : World contracts) (caller kind : K)
    (reference : Handle caller) (address : Address) where
  linked : Storage (contracts kind)
  store : Storage (contracts caller)
  libraryRole : w.isLibrary kind = true
  callerRole : w.isLibrary caller = false
  linkedAccount : w.accounts address = some ⟨kind,linked⟩
  callerAccount : w.accounts reference.address = some ⟨caller,store⟩

structure FrameInputs (f : Source.Fr) {caller : K} (reference : Handle caller) (ctx : Context) : Prop where
  sender : (f.sender.val : Int) = ctx.sender.1.1
  value : (f.value.val : Int) = ctx.value.1
  caller : (f.this.val : Int) = reference.address.1.1
  static : f.static = ctx.isStatic

def emptyFrame (w : World contracts) {caller : K} (self : Handle caller)
    (ctx : Context) (store : Storage (contracts caller)) : State (contracts caller) [] :=
  {storage:=store,H:=[],heap:=Heap.empty,env:=(),net:=[],
    selfBalance:=w.funds self.address,tx:=ctx.tx w self.address}

omit [DecidableEq K] in
theorem finish_empty (w : World contracts) {caller : K} (self : Handle caller)
    (ctx : Context) (store : Storage (contracts caller))
    (present : w.accounts self.address = some ⟨caller,store⟩) :
    w.finish self.address (emptyFrame w self ctx store) = .ok w := by
  have accounts : (fun a => if a=self.address then some ⟨caller,store⟩ else w.accounts a) = w.accounts := by
    funext a
    by_cases eq : a=self.address
    · subst a; rw [if_pos rfl,present]
    · rw [if_neg eq]
  have funds : (fun a => if a=self.address then w.funds self.address else w.funds a) = w.funds := by
    funext a
    by_cases eq : a=self.address
    · subst a; rw [if_pos rfl]
    · rw [if_neg eq]
  change (Except.ok {w with accounts:=_,funds:=_} : TRes (World contracts)) = .ok w
  dsimp only [emptyFrame]
  rw [accounts,funds]

theorem account_of_lookup (w : World contracts) {kind : K} (reference : Handle kind)
    (store : Storage (contracts kind)) (read : w.storage? reference = some store) :
    w.accounts reference.address = some ⟨kind,store⟩ := by
  unfold World.storage? at read
  cases account : w.accounts reference.address with
  | none => simp only [account,bind,Option.bind] at read; cases read
  | some pair =>
    rcases pair with ⟨actual,data⟩
    by_cases same : actual=kind
    · subst actual
      simp only [account,bind,Option.bind] at read
      cases read
      rfl
    · simp only [account,bind,Option.bind,dif_neg same] at read
      cases read

/-- Reconstruct only the independently checked code/account inputs from a real
successful library operation, not a Source preservation premise. -/
theorem runtime_of_success {α : Type} (w next : World contracts) {caller : K}
    (reference : Handle caller) (lib : Library contracts caller α) (ctx : Context) (value : α)
    (run : w.libraryCall reference lib ctx = .ok (next,value)) :
    Nonempty (RuntimeInputs w caller lib.kind reference lib.address) := by
  unfold World.libraryCall at run
  cases libraryRole : w.isLibrary lib.kind with
  | false => simp only [libraryRole,Bool.not_false,Bool.true_or,if_true] at run; cases run
  | true =>
    cases callerRole : w.isLibrary caller with
    | true => simp only [libraryRole,callerRole,Bool.not_true,Bool.false_or,Bool.true_or,if_true] at run; cases run
    | false =>
      simp only [libraryRole,callerRole,Bool.not_true,Bool.false_or] at run
      split at run
      · cases run
      · cases linked : w.storage? (⟨lib.address⟩ : Handle lib.kind) with
        | none => simp only [linked,TRes.ofOpt,bind,Except.bind] at run; cases run
        | some linkedStore =>
          cases callerStore : w.storage? reference with
          | none => simp only [linked,callerStore,TRes.ofOpt,bind,Except.bind] at run; cases run
          | some store => exact ⟨⟨linkedStore,store,libraryRole,callerRole,
              account_of_lookup w _ _ linked,account_of_lookup w _ _ callerStore⟩⟩

theorem library_actual (w : World contracts) (caller kind : K) (self : Handle caller)
    (address : Address) (ctx : Context) (inputs : RuntimeInputs w caller kind self address) :
    w.libraryCall self (library caller kind address) ctx =
      .ok (w,(ctx.sender.1.1,ctx.value.1,self.address.1.1)) := by
  have linked : w.storage? (⟨address⟩ : Handle kind) = some inputs.linked := by
    simp only [World.storage?,inputs.linkedAccount,bind,Option.bind]
    rfl
  have store : w.storage? self = some inputs.store := by
    simp only [World.storage?,inputs.callerAccount,bind,Option.bind]
    rfl
  unfold World.libraryCall library entry
  simp only [inputs.libraryRole,inputs.callerRole,emptyBody,Bool.not_true,
    Bool.and_false,Bool.false_or,linked,store,TRes.ofOpt,bind,Except.bind]
  change (do
    let next ← w.finish self.address (emptyFrame w self ctx inputs.store)
    pure (next,(ctx.sender.1.1,ctx.value.1,self.address.1.1))) = _
  rw [finish_empty w self ctx inputs.store inputs.callerAccount]
  rfl

theorem library_observe {α : Type} (w : World contracts) (caller kind : K) (self : Handle caller)
    (address : Address) (ctx : Context) (inputs : RuntimeInputs w caller kind self address)
    (observe : World contracts → α) :
    (w.libraryCall self (library caller kind address) ctx).map (fun out => (observe out.1,out.2)) =
      .ok (observe w,(ctx.sender.1.1,ctx.value.1,self.address.1.1)) := by
  rw [library_actual w caller kind self address ctx inputs]
  rfl

theorem source_pair {E : Source.Env} {Γ : Source.RCtx} (g : Source.Glob E)
    (f : Source.Fr) (fuel : Nat) (locals : Source.Locals E.layout Γ) (state : Source.St E) :
    (Source.evalPair g f (fuel+2)
      (.magic .msg "sender" rfl : Source.RExpr E Γ (.address false))
      (.magic .msg "value" rfl : Source.RExpr E Γ (.int Source.IntTy.u256))).run (locals,state) =
      (.ok (.val (.address f.sender),.val (SourceEnvironment.sourceWord f.value)),(locals,state)) :=
  V07.source_pure_pair g f (fuel+1) (locals,state) _ _ _ _
    (SourceEnvironment.eval_sender g f fuel locals state)
    (SourceEnvironment.eval_value g f fuel locals state)

theorem context_transport {E : Source.Env} {Γ : Source.RCtx} (g : Source.Glob E)
    (f : Source.Fr) (fuel : Nat) (locals : Source.Locals E.layout Γ) (state : Source.St E)
    (w : World contracts) (caller kind : K) (self : Handle caller) (address : Address) (ctx : Context)
    (runtime : RuntimeInputs w caller kind self address) (frame : FrameInputs f self ctx) :
    (Source.evalPair g f (fuel+2)
      (.magic .msg "sender" rfl : Source.RExpr E Γ (.address false))
      (.magic .msg "value" rfl : Source.RExpr E Γ (.int Source.IntTy.u256))).run (locals,state) =
      (.ok (.val (.address f.sender),.val (SourceEnvironment.sourceWord f.value)),(locals,state)) ∧
    w.libraryCall self (library caller kind address) ctx =
      .ok (w,((f.sender.val : Int),(f.value.val : Int),(f.this.val : Int))) := by
  refine ⟨source_pair g f fuel locals state,?_⟩
  rw [library_actual w caller kind self address ctx runtime,frame.sender,frame.value,frame.caller]

open LibraryHandlerControls in
/-- Actual reachable paid world, installed caller and library. -/
def clientRun : TRes (World LibraryHandlerControls.Catalog × Observation) := outer.libraryCall (⟨Controls.self⟩ : Handle false)
  (library false true LibraryHandlerControls.link) Controls.paidCtx

theorem populated_client : clientRun = .ok (LibraryHandlerControls.outer,(1,7,2)) := by
  obtain ⟨runtime⟩ := runtime_of_success (contracts:=LibraryHandlerControls.Catalog)
    LibraryHandlerControls.outer LibraryHandlerControls.handled (⟨Controls.self⟩ : Handle false)
    LibraryHandlerControls.library Controls.paidCtx LibraryHandlerControls.expected
    LibraryHandlerControls.delegated_reached
  exact library_actual LibraryHandlerControls.outer false true _ _ Controls.paidCtx runtime

/-- Every complete world observer is retained, including the existing ordered
vector. Keeping the observer abstract avoids re-evaluating the large setup. -/
theorem populated_vector {α : Type} (observe : World LibraryHandlerControls.Catalog → α) :
    clientRun.map (fun out => (observe out.1,out.2)) =
      .ok (observe LibraryHandlerControls.outer,(1,7,2)) :=
by
  obtain ⟨runtime⟩ := runtime_of_success (contracts:=LibraryHandlerControls.Catalog)
    LibraryHandlerControls.outer LibraryHandlerControls.handled (⟨Controls.self⟩ : Handle false)
    LibraryHandlerControls.library Controls.paidCtx LibraryHandlerControls.expected
    LibraryHandlerControls.delegated_reached
  exact library_observe LibraryHandlerControls.outer false true _ _ Controls.paidCtx runtime observe

theorem populated_transport (p : Roadmap.Pipeline) (fuel : Nat) :
    (Source.evalPair (SourceEnvironmentControls.global p) SourceEnvironmentControls.frame (fuel+2)
      (.magic .msg "sender" rfl : Source.RExpr SourceEnvironmentControls.E [.bool] (.address false))
      (.magic .msg "value" rfl : Source.RExpr SourceEnvironmentControls.E [.bool] (.int Source.IntTy.u256))).run
        (SourceEnvironmentControls.locals,SourceEnvironmentControls.populated) =
      (.ok (.val (.address SourceEnvironmentControls.sender),
        .val (SourceEnvironment.sourceWord SourceEnvironmentControls.frame.value)),
        (SourceEnvironmentControls.locals,SourceEnvironmentControls.populated)) ∧
    clientRun = .ok (LibraryHandlerControls.outer,(1,7,2)) := by
  obtain ⟨runtime⟩ := runtime_of_success (contracts:=LibraryHandlerControls.Catalog)
    LibraryHandlerControls.outer LibraryHandlerControls.handled (⟨Controls.self⟩ : Handle false)
    LibraryHandlerControls.library Controls.paidCtx LibraryHandlerControls.expected
    LibraryHandlerControls.delegated_reached
  exact context_transport (SourceEnvironmentControls.global p) SourceEnvironmentControls.frame fuel
    SourceEnvironmentControls.locals SourceEnvironmentControls.populated LibraryHandlerControls.outer
    false true (⟨Controls.self⟩ : Handle false) LibraryHandlerControls.link Controls.paidCtx runtime
    ⟨rfl,rfl,rfl,rfl⟩

theorem wrong_context : clientRun.toOption.map Prod.snd ≠ some (4,0,4) := by
  rw [populated_client]
  intro wrong
  cases wrong

theorem static_read_client :
    LibraryHandlerControls.outer.libraryCall (⟨Controls.self⟩ : Handle false)
      (library false true LibraryHandlerControls.link) {Controls.paidCtx with mode:=.readOnly} =
      .ok (LibraryHandlerControls.outer,(1,0,2)) := by
  obtain ⟨runtime⟩ := runtime_of_success (contracts:=LibraryHandlerControls.Catalog)
    LibraryHandlerControls.outer LibraryHandlerControls.handled (⟨Controls.self⟩ : Handle false)
    LibraryHandlerControls.library Controls.paidCtx LibraryHandlerControls.expected
    LibraryHandlerControls.delegated_reached
  exact library_actual LibraryHandlerControls.outer false true _ _ _ runtime

/-- info: 'Solidity.Lowering.V08.LibraryFrameTransport.library_observe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms library_observe
/-- info: 'Solidity.Lowering.V08.LibraryFrameTransport.account_of_lookup' depends on axioms: [propext] -/
#guard_msgs in
#print axioms account_of_lookup
/-- info: 'Solidity.Lowering.V08.LibraryFrameTransport.runtime_of_success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms runtime_of_success
/-- info: 'Solidity.Lowering.V08.LibraryFrameTransport.populated_vector' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms populated_vector
/-- info: 'Solidity.Lowering.V08.LibraryFrameTransport.populated_transport' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms populated_transport
/-- info: 'Solidity.Lowering.V08.LibraryFrameTransport.finish_empty' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms finish_empty
/-- info: 'Solidity.Lowering.V08.LibraryFrameTransport.library_actual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms library_actual
/-- info: 'Solidity.Lowering.V08.LibraryFrameTransport.source_pair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms source_pair
/-- info: 'Solidity.Lowering.V08.LibraryFrameTransport.context_transport' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms context_transport
/-- info: 'Solidity.Lowering.V08.LibraryFrameTransport.populated_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms populated_client
/-- info: 'Solidity.Lowering.V08.LibraryFrameTransport.wrong_context' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms wrong_context
/-- info: 'Solidity.Lowering.V08.LibraryFrameTransport.static_read_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms static_read_client
end Solidity.Lowering.V08.LibraryFrameTransport
