import Solidity.Lowering.V08.ScalarCallableTransport

/-! Environment-polymorphic G20 scalar callable boundary. All existing integer
widths/signs are retained. Inputs contain declaration/signature/body selection,
never an assumed execution or preservation equality. This covers the pure
argument-return body shape, not arbitrary bodies or external-call admission. -/
namespace Solidity.Lowering.V08.IntegerCallable
open Solidity Source
open Solidity.Lowering.V07

theorem implicit_identity (t : Source.IntTy) : t.implicit t = true := by
  rcases t with ⟨signed,bits,valid⟩
  cases signed <;> change (decide (bits ≤ bits) || false) = true
  all_goals rw [decide_eq_true (Nat.le_refl bits)]; rfl

def body (E : Source.Env) (t : Source.IntTy) : Source.RBody E :=
  ⟨[.int t],[.int t],false,[.int t,.int t],[.int t,.int t],
    .stmt (.retVal rfl (.local (.there .here)) (implicit_identity t)) .nil,[]⟩

structure Inputs {E : Source.Env} (g : Source.Glob E) (f : Source.Fr)
    (declaration : Source.Decl) (t : Source.IntTy) : Prop where
  member : declaration ∈ E.decls
  kind : declaration.kind = .function
  signature : declaration.fnSig E = some ([.int t],[.int t])
  selected : g.prog.body (g.dispatchFn f.contract declaration) = some (body E t)

/-- Preserve the existing source declaration's payability bit. -/
def payable (declaration : Source.Decl) : Bool :=
  match declaration.kind,declaration.top,declaration.node with
  | .function,_,.function _ _ _ _ _ pay _ _ _ => pay
  | _,_,_ => false

theorem conversion_identity {E : Source.Env} {Γ : Source.RCtx} (f : Source.Fr)
    (fuel : Nat) (τ : Source.STy) (v : Source.RVal E.layout τ) :
    (Source.convRV f fuel τ v : Source.EM E Γ _) = pure v := by
  unfold Source.convRV
  rw [dif_pos rfl]

theorem slot_write_same {D : Source.Layout} {Γ : Source.RCtx} {τ : Source.STy}
    (old value : Source.Val D τ) (rest : Source.Locals D Γ) :
    (Source.Locals.cons old rest).setAt 0 value = .ok (.cons value rest) := by
  unfold Source.Locals.setAt
  rw [dif_pos rfl]
  rfl

theorem slot_read_same {D : Source.Layout} {Γ : Source.RCtx} {τ : Source.STy}
    (value : Source.Val D τ) (rest : Source.Locals D Γ) :
    (Source.Locals.cons value rest).getAt 0 τ = .ok value := by
  unfold Source.Locals.getAt
  rw [dif_pos rfl]
  rfl

theorem source_call {E : Source.Env} (g : Source.Glob E) (f : Source.Fr)
    (declaration : Source.Decl) (t : Source.IntTy) (inputs : Inputs g f declaration t)
    (extra : Nat) (state : Source.St E) (n : Int) (h : t.lo ≤ n ∧ n ≤ t.hi) :
    (Source.callInternal g f (extra+12) declaration (.cons (.int n h) .nil) [.int t]).run
      (Source.L0 E,state) = (.ok (.val (.int n h)),(Source.L0 E,state)) :=
  SourceCallable.complete g f (extra+11) declaration (.cons (.int n h) .nil)
    (body E t) inputs.selected (.cons (.int 0 t.zero_mem) .nil) rfl
    (.cons (.int n h) (.cons (.int n h) .nil)) (.cons (.val (.int n h)) .nil)
    state state state (by rfl) (by
      simp only [Source.runMods, body, Source.execItems, Source.execS, Source.evalE, Source.withLibraryCalldata, conversion_identity, Source.EM.sub, Source.getV, Source.RVal.get, Source.EM.locals, bind, pure, ExceptT.run, ExceptT.bind, ExceptT.pure, get, getThe, MonadStateOf.get, liftM, monadLift, MonadLift.monadLift, ExceptT.lift, Functor.map, Source.EM.lift]
      dsimp only [ExceptT.mk,StateT.bind,StateT.pure,StateT.get,StateT.map,ExceptT.bindCont,
        Source.Vals.onto,Source.Locals.get,Source.RVal.get]
      simp only [bind, pure, StateT.bind, StateT.pure, Except.pure, ExceptT.bindCont, Source.L0, Source.Locals.get, List.length_cons, List.length_nil, Nat.sub_self, slot_write_same]) (by
      change (do
        let value ← (Source.Locals.cons (.int n h) (.cons (.int n h) .nil)).getAt 0 (.int t)
        pure (Source.RVals.cons (.val value) .nil)) = _
      rw [slot_read_same]
      rfl)

def entry (C : Contract) (declaration : Source.Decl) (t : Source.IntTy)
    (n : Int) (h : t.lo ≤ n ∧ n ≤ t.hi) : ContractWorld.Entry C (integerPrim t).Denote :=
  {locals:=[.val (integerPrim t)],
    body:=.cons (.declLocal (integerPrim t) (.user "argument")
      (some (.simple (.lit n (integer_range t n h))))) .nil,
    result:=fun state => (Solidity.Val.simple (.local .here) : Solidity.Val C [.val (integerPrim t)] (integerPrim t)).evalT state,
    payable:=payable declaration}

theorem target_body (C : Contract) (state : State C []) (declaration : Source.Decl)
    (t : Source.IntTy) (n : Int) (h : t.lo ≤ n ∧ n ≤ t.hi) :
    (entry C declaration t n h).body.run state =
      .ok ⟨state.push (t:=.val (integerPrim t)) (integerValue t n h),List.prefix_refl _⟩ := by
  rcases t with ⟨signed,bits,valid⟩
  cases signed <;> rfl

theorem target_result (C : Contract) (state : State C []) (declaration : Source.Decl)
    (t : Source.IntTy) (n : Int) (h : t.lo ≤ n ∧ n ≤ t.hi) :
    (entry C declaration t n h).result (state.push (t:=.val (integerPrim t)) (integerValue t n h)) =
      .ok (integerValue t n h) := rfl

theorem caller_restored (C : Contract) (state : State C []) (declaration : Source.Decl)
    (t : Source.IntTy) (n : Int) (h : t.lo ≤ n ∧ n ≤ t.hi) :
    (state.push (t:=.val (integerPrim t)) (integerValue t n h)).drop (entry C declaration t n h).body.ext =
      state := rfl

theorem metadata_preserved (C : Contract) (declaration : Source.Decl)
    (t : Source.IntTy) (n : Int) (h : t.lo ≤ n ∧ n ≤ t.hi) :
    (entry C declaration t n h).payable = payable declaration := rfl

theorem transport {E : Source.Env} (g : Source.Glob E) (f : Source.Fr)
    (declaration : Source.Decl) (t : Source.IntTy) (inputs : Inputs g f declaration t)
    (extra : Nat) (source : Source.St E) (C : Contract) (target : State C [])
    (n : Int) (h : t.lo ≤ n ∧ n ≤ t.hi) :
    (Source.callInternal g f (extra+12) declaration (.cons (.int n h) .nil) [.int t]).run
      (Source.L0 E,source) = (.ok (.val (.int n h)),(Source.L0 E,source)) ∧
    (entry C declaration t n h).body.run target =
      .ok ⟨target.push (t:=.val (integerPrim t)) (integerValue t n h),List.prefix_refl _⟩ ∧
    (entry C declaration t n h).result (target.push (t:=.val (integerPrim t)) (integerValue t n h)) =
      .ok (integerValue t n h) ∧
    IntValueRel t (.int n h : Source.Val E.layout (.int t)) (integerValue t n h) ∧
    (target.push (t:=.val (integerPrim t)) (integerValue t n h)).drop (entry C declaration t n h).body.ext = target :=
  ⟨source_call g f declaration t inputs extra source n h,target_body C target declaration t n h,
    target_result C target declaration t n h,integer_related t n h,caller_restored C target declaration t n h⟩

/-- Real metadata and selected source body instantiate the polymorphic input. -/
theorem uint_inputs (p : Roadmap.Pipeline) : Inputs (ScalarCallableTransport.global p)
    ScalarCallableTransport.frame ScalarCallableTransport.declaration Source.IntTy.u256 :=
  ⟨ScalarCallableTransport.declaration_member,rfl,ScalarCallableTransport.signature,rfl⟩

theorem populated_client (p : Roadmap.Pipeline) (extra : Nat) (bytes : Roadmap.Bytes)
    (n : Int) (h : Source.IntTy.u256.lo ≤ n ∧ n ≤ Source.IntTy.u256.hi) :
    (Source.callInternal (ScalarCallableTransport.global p) ScalarCallableTransport.frame (extra+12)
      ScalarCallableTransport.declaration (.cons (.int n h) .nil) [.int Source.IntTy.u256]).run
      (Source.L0 ScalarCallableTransport.E,ScalarCallableTransport.populated bytes) =
      (.ok (.val (.int n h)),(Source.L0 ScalarCallableTransport.E,ScalarCallableTransport.populated bytes)) :=
  source_call _ _ _ _ (uint_inputs p) extra _ n h

/-- info: 'Solidity.Lowering.V08.IntegerCallable.implicit_identity' does not depend on any axioms -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.IntegerCallable.implicit_identity

/-- info: 'Solidity.Lowering.V08.IntegerCallable.conversion_identity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.IntegerCallable.conversion_identity

/-- info: 'Solidity.Lowering.V08.IntegerCallable.slot_write_same' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.IntegerCallable.slot_write_same

/-- info: 'Solidity.Lowering.V08.IntegerCallable.slot_read_same' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.IntegerCallable.slot_read_same

/-- info: 'Solidity.Lowering.V08.IntegerCallable.source_call' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.IntegerCallable.source_call

/-- info: 'Solidity.Lowering.V08.IntegerCallable.target_body' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.IntegerCallable.target_body

/-- info: 'Solidity.Lowering.V08.IntegerCallable.target_result' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.IntegerCallable.target_result

/-- info: 'Solidity.Lowering.V08.IntegerCallable.caller_restored' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.IntegerCallable.caller_restored

/-- info: 'Solidity.Lowering.V08.IntegerCallable.metadata_preserved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.IntegerCallable.metadata_preserved

/-- info: 'Solidity.Lowering.V08.IntegerCallable.transport' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.IntegerCallable.transport

/-- info: 'Solidity.Lowering.V08.IntegerCallable.uint_inputs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.IntegerCallable.uint_inputs

/-- info: 'Solidity.Lowering.V08.IntegerCallable.populated_client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Solidity.Lowering.V08.IntegerCallable.populated_client
end Solidity.Lowering.V08.IntegerCallable
