import Solidity.Backend.InternalFlow.PublishedDirectCalls

/-! Direct tuple calls over the actual primitive-only Binders interface.
The public compiler still refuses CallRet.rets; this owned adapter compiles its
published expansion and compacts exported primitive cells in increasing order.
No alternative syntax, call evaluator or reference-binder semantics is added. -/
namespace Solidity.Backend.InternalFlow.TupleCalls
open Evm Evm.Memory
variable {C : Contract}

def expand {Γ ps rs Γf : Ctx} (args : Args C Γ ps) (bs : Binders rs)
    (body : Prog C (rs ++ ps) Γf) : Prog C Γ (rs ++ (ps ++ Γ)) :=
  args.declsThen (bs.declsThen
    (.cons (.block (body.wk (Thin.keepAll rs (Thin.atop ps Γ))).2.2) .nil))

theorem expand_runSt {Γ ps rs Γf : Ctx} (f : Name) (args : Args C Γ ps)
    (bs : Binders rs) (body : Prog C (rs ++ ps) Γf) (σ : State C Γ) :
    ((expand args bs body).runSt σ).map
      (State.thin (Thin.keepAll rs (Thin.ofExt (Ext.append Γ ps)))) =
      (Stmt.call f args (.rets bs) body).runSt σ :=
  Stmt.runSt_callRets f args bs body σ

/-- Defaults are precisely the primitive values; tuple entry does not allocate. -/
theorem tuple_entry {Γ ps rs : Ctx} (bs : Binders rs) (σ : State C ps) :
    (CallRet.rets (Γ := Γ) bs).enterT σ =
      ⟨σ.withEnv (TEnv.append rs (bs.defaultsT (C := C)) σ.env), List.prefix_refl _⟩ := rfl

def resultFrag {Γ : Ctx} (G : Frag Γ) : {rs : Ctx} → Binders rs → Frag (rs ++ Γ)
  | _, .nil => G
  | _, .snoc bs p _ => (resultFrag G bs).push (.val p) .ok

/-- Copy lower result cells first: with overlapping source/destination regions,
each lower result is read before a later destination can overwrite its source;
earlier destinations lie below subsequent sources. -/
def exportCode (b : Nat) (Γ ps : Ctx) : {rs : Ctx} → Binders rs → List Instr
  | _, .nil => []
  | _, .snoc (ρ := rs) bs _ _ => exportCode b Γ ps bs ++
      [.mload (cell (b + Γ.length + ps.length + rs.length)),
       .mstore (cell (b + Γ.length + rs.length))]

private theorem restrict_tail {Γ ps rs : Ctx} {p : PrimTy}
    (F : Frag (.val p :: (rs ++ (ps ++ Γ)))) :
    (F.restrict (rs ++ (ps ++ Γ))).restrict Γ = F.restrict Γ := by
  cases F
  simp only [Frag.restrict, List.length_cons, List.length_append, List.drop_drop]
  congr 2 <;> omega

/-- Actual checked-in instruction execution, representation, protected cells,
stack and allocator frame for arbitrary binder arity. Contents are not copied. -/
theorem compact {L b frame : Nat} {Γ ps : Ctx} :
    {rs : Ctx} → (bs : Binders rs) → {F : Frag (rs ++ (ps ++ Γ))} →
    (σ : State C (rs ++ (ps ++ Γ))) → {base : Nat → Fin W} → {m : Machine} →
    StateRepr L b frame F σ base m →
    ∃ m', Evm.run (exportCode b Γ ps bs) m = .ok m' 0 ∧
      StateRepr L b frame (resultFrag (F.restrict Γ) bs)
        (σ.thin (Thin.keepAll rs (Thin.ofExt (Ext.append Γ ps)))) base m' ∧
      m'.stack = m.stack ∧
      (∀ l, l < b + Γ.length ∨ b + Γ.length + rs.length ≤ l → m'.mem l = m.mem l) ∧
      (∀ cursor, 0 < b → StructAllocatorRepr σ.heap base frame cursor m →
        StructAllocatorRepr σ.heap base frame cursor m') := by
  intro rs bs
  induction bs with
  | nil =>
    intro F σ base m hm
    refine ⟨m, rfl, ?_, rfl, (fun _ _ => rfl), (fun _ _ h => h)⟩
    have h := hm.drop (Ext.append Γ ps)
    simpa only [resultFrag, Thin.keepAll, State.thin, State.drop, State.withEnv, TEnv.thin_ofExt] using h
  | @snoc rs bs p name ih =>
    intro F σ base m hm
    let tail := σ.drop (Ext.push Ext.refl)
    have htail : StateRepr L b frame (F.restrict (rs ++ (ps ++ Γ))) tail base m :=
      hm.drop (Ext.push Ext.refl)
    obtain ⟨m₁, hc, hr, hk, hf, ha⟩ := ih tail htail
    rw [restrict_tail F] at hr
    let source := cell (b + Γ.length + ps.length + rs.length)
    let destination := cell (b + Γ.length + rs.length)
    let w := m.mem source
    have hs : m₁.mem source = w := hf source (.inr (by dsimp [source, cell]; omega))
    have hw : ReprV p σ.env.1 w := by
      have h := hm.core.vals (Idx.here : Idx (.val p :: (rs ++ (ps ++ Γ))) (.val p))
      simpa only [Look.ofTEnv, see, TEnv.get, w, source, Machine.memAt, cellOf, lvl_here, List.length_append,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
    have hroom : b + ((rs ++ Γ).length + 1) ≤ frame := by
      have h := hm.locals
      simp only [List.length_cons, List.length_append] at h ⊢
      omega
    have hrepr := hr.consVal σ.env.1 w hw hroom
    have hstate : σ.thin (Thin.keepAll (.val p :: rs) (Thin.ofExt (Ext.append Γ ps))) =
        (tail.thin (Thin.keepAll rs (Thin.ofExt (Ext.append Γ ps)))).push (t := .val p) σ.env.1 := rfl
    let m₂ := writeMachine m₁ destination w
    refine ⟨m₂, ?_, ?_, hk, ?_, ?_⟩
    · rw [exportCode, run_append_ok hc]
      change run [.mload source, .mstore destination] m₁ = .ok m₂ 0
      simp only [run, exec_cons_zero, Instr.step, Machine.next, hs, Out.ok_bind,
        exec_nil, m₂, writeMachine]
    · rw [hstate]
      simpa only [resultFrag, List.length_append, destination, m₂, Nat.add_comm, Nat.add_assoc] using hrepr
    · intro l hl
      have hne : l ≠ destination := by dsimp [destination, cell]; simp only [List.length_cons] at hl; omega
      change upd m₁.mem destination w l = m.mem l
      exact (upd_other m₁.mem w hne).trans (hf l (by simp only [List.length_cons] at hl; omega))
    · intro cursor hb hal
      have hlocal : destination < frame := by dsimp [destination, cell]; simp only [List.length_append] at hroom; omega
      exact (ha cursor hb hal).localWrite destination (by dsimp [destination, cell]; omega) hlocal w


private theorem state_result_injective {H : HTy} {Γ : Ctx}
    {a b : TRes (Solidity.Out C H Γ)} (h : a.map (·.st) = b.map (·.st)) : a = b := by
  cases a with
  | error e => cases b with
    | error f => exact congrArg Except.error (Except.error.inj h)
    | ok o => cases h
  | ok o => cases b with
    | error f => cases h
    | ok o' =>
      have hs : o.st = o'.st := Except.ok.inj h
      have ho : o = o' := by cases o; cases o'; cases hs; rfl
      exact congrArg Except.ok ho

/-- Exact runtime outcome, including the original error class and bytes.
The output Ext is the actual expansion's heap extension, not a new premise. -/
theorem expand_runR {Γ ps rs Γf : Ctx} (f : Name) (args : Args C Γ ps)
    (bs : Binders rs) (body : Prog C (rs ++ ps) Γf) (σ : State C Γ) :
    ((expand args bs body).run σ).map (fun o =>
      (⟨o.st.thin (Thin.keepAll rs (Thin.ofExt (Ext.append Γ ps))), o.ext⟩ :
        Solidity.Out C σ.H (rs ++ Γ))) = (Stmt.call f args (.rets bs) body).run σ := by
  apply state_result_injective
  have h := expand_runSt f args bs body σ
  cases hx : (expand args bs body).run σ with
  | error e => simpa only [Prog.runSt, hx, Except.map] using h
  | ok o => simpa only [Prog.runSt, hx, Except.map] using h

private theorem outcome_ok {H : HTy} {Γ : Ctx}
    {res : TRes (Solidity.Out C H Γ)} {τ : State C Γ}
    (h : res.map (·.st) = .ok τ) : ∃ o, res = .ok o ∧ o.st = τ := by
  cases res with
  | error e => cases h
  | ok o => exact ⟨o, rfl, Except.ok.inj h⟩

/-- Actual multi-result target certificate. The expanded program is compiled
by the published producer; the export code is proved above, not assumed. -/
def tupleReturn {b : Nat} {Γ ps rs Γf : Ctx} {F : Frag Γ}
    (f : Name) (args : Args C Γ ps) (bs : Binders rs)
    (body : Prog C (rs ++ ps) Γf)
    (hq : Calls.Program b F (expand args bs body)) :
    Calls.Statement b F (.call f args (.rets bs) body) where
  frag := resultFrag (hq.frag.restrict Γ) bs
  code := hq.code ++ exportCode b Γ ps bs
  need := hq.need
  cost := hq.cost
  allocates := hq.allocates
  zeroCost := hq.zeroCost
  sound := by
    intro L frame σ base m h hcap ha
    rcases hq.sound h hcap ha with ⟨o,m₁,base',ho,hc,hm,hk,he,hal⟩ | ⟨ho,hc⟩
    · obtain ⟨m₂,hrun,hrepr,hstack,hframe,halloc⟩ := compact bs o.st hm
      let τ := o.st.thin (Thin.keepAll rs (Thin.ofExt (Ext.append Γ ps)))
      have hs : ((Stmt.call f args (.rets bs) body).run σ).map (·.st) = .ok τ := by
        change (Stmt.call f args (.rets bs) body).runSt σ = _
        rw [← expand_runSt f args bs body σ]
        show (((expand args bs body).run σ).map (·.st)).map _ = _
        rw [ho]
        rfl
      obtain ⟨o',hs',ht⟩ := outcome_ok hs
      refine .inl ⟨o',m₂,base',hs',?_,?_,hstack.trans hk,he,?_⟩
      · rw [run_append_ok hc]
        exact hrun
      · rw [ht]
        exact hrepr
      · intro cursor hb initial hspace
        rw [ht]
        exact halloc ⟨cursor.val + hq.cost σ, hspace⟩ hb (hal cursor hb initial hspace)
    · have hs : ((Stmt.call f args (.rets bs) body).run σ).map (·.st) = .error .revert := by
        change (Stmt.call f args (.rets bs) body).runSt σ = _
        rw [← expand_runSt f args bs body σ]
        show (((expand args bs body).run σ).map (·.st)).map _ = _
        rw [ho]
        rfl
      have failed : (Stmt.call f args (.rets bs) body).run σ = .error .revert := by
        cases hrun : (Stmt.call f args (.rets bs) body).run σ with
        | error e =>
          rw [hrun] at hs
          exact congrArg Except.error (Except.error.inj hs)
        | ok o => rw [hrun] at hs; cases hs
      exact .inr ⟨failed,run_append_revert hc⟩


/-- Actual Binders has no memory-reference constructor. -/
theorem no_memory_binder {rs : Ctx} (bs : Binders rs) (R : RefTy)
    (i : Idx rs (.mem R)) : False := by
  induction bs with
  | nil => cases i
  | snoc bs p name ih => cases i with
    | there j => exact ih j

/-- Actual Binders has no storage-reference constructor either. -/
theorem no_storage_binder {rs : Ctx} (bs : Binders rs) (R : RefTy)
    (i : Idx rs (.alias R)) : False := by
  induction bs with
  | nil => cases i
  | snoc bs p name ih => cases i with
    | there j => exact ih j


/-- Owned direct-tuple entrypoint. It delegates the entire expanded body to the
published compiler; unsupported statements/expanded bodies still return none.
This does not modify public Compiler.compile or add recursive tuple lowering. -/
def compileTuple (b : Nat) {Γ Δ : Ctx} (F : Frag Γ) (s : Stmt C Γ Δ) :
    Option (Calls.Statement b F s) :=
  match s with
  | .call f args (.rets bs) body => do
    let hq ← Calls.compile b F (expand args bs body)
    pure (tupleReturn f args bs body hq)
  | _ => none

/-- Expose the actual returned certificate from a successful published body
compilation, without normalizing that compiler result again. This is not a
simulation premise and does not change selector admission. -/
theorem compileTuple_success {b : Nat} {Γ ps rs Γf : Ctx} (F : Evm.Frag Γ)
    (f : Name) (args : Args C Γ ps) (bs : Binders rs) (body : Prog C (rs ++ ps) Γf)
    (compiled : Evm.Memory.Calls.Program b F (expand args bs body))
    (built : Evm.Memory.Calls.compile b F (expand args bs body) = some compiled) :
    compileTuple b F (.call f args (.rets bs) body) = some (tupleReturn f args bs body compiled) := by
  simp only [compileTuple,built]
  rfl
/-- info: 'Solidity.Backend.InternalFlow.TupleCalls.compileTuple_success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms compileTuple_success

namespace Scoped

/-- Dropping the result frame after exact tuple expansion also removes the
private parameter frame. This is a typed state equality, not Heap.Keeps. -/
private theorem drop_return_env {H : HTy} (Γ ps rs : Ctx)
    (e : TEnv C H (rs ++ (ps ++ Γ))) :
    TEnv.drop (Ext.append Γ rs)
      (TEnv.thin (Thin.keepAll rs (Thin.ofExt (Ext.append Γ ps))) e) =
    TEnv.drop ((Ext.append Γ ps).trans (Ext.append (ps ++ Γ) rs)) e := by
  induction rs with
  | nil => exact TEnv.thin_ofExt _ _
  | cons t rs ih => exact ih e.2

private theorem drop_return_state {Γ ps rs : Ctx} (σ : State C (rs ++ (ps ++ Γ))) :
    State.drop (Ext.append Γ rs)
      (State.thin (Thin.keepAll rs (Thin.ofExt (Ext.append Γ ps))) σ) =
    State.drop ((Ext.append Γ ps).trans (Ext.append (ps ++ Γ) rs)) σ := by
  change σ.withEnv (TEnv.drop (Ext.append Γ rs)
      (TEnv.thin (Thin.keepAll rs (Thin.ofExt (Ext.append Γ ps))) σ.env)) =
    σ.withEnv (TEnv.drop ((Ext.append Γ ps).trans (Ext.append (ps ++ Γ) rs)) σ.env)
  rw [drop_return_env]

theorem scoped_tuple_expansion {Γ ps rs Γf : Ctx} (f : Name)
    (args : Args C Γ ps) (bs : Binders rs) (body : Prog C (rs ++ ps) Γf)
    (σ : State C Γ) :
    (Stmt.block (.cons (.call f args (.rets bs) body) .nil)).runSt σ =
      (Stmt.block (TupleCalls.expand args bs body)).runSt σ := by
  rw [Stmt.runSt_block,Prog.runSt_single,← TupleCalls.expand_runSt f args bs body σ,
    Stmt.runSt_block]
  cases h : (TupleCalls.expand args bs body).runSt σ with
  | error e => rfl
  | ok τ =>
    change Except.ok (State.drop _ (State.thin _ τ)) = Except.ok (State.drop _ τ)
    apply congrArg Except.ok
    rw [Ext.eq_of_depth (Prog.cons (.call f args (.rets bs) body) .nil).ext (Ext.append Γ rs),
      Ext.eq_of_depth (TupleCalls.expand args bs body).ext
        ((Ext.append Γ ps).trans (Ext.append (ps ++ Γ) rs))]
    exact drop_return_state τ

/-- Compile an unused tuple result through the published block constructor.
No result-copy instructions are needed after its complete local frame drops.
Admission and finite direct-body compilation remain the caller's responsibility. -/
def statement {b : Nat} {Γ ps rs Γf : Ctx} {F : Frag Γ}
    (f : Name) (args : Args C Γ ps) (bs : Binders rs)
    (body : Prog C (rs ++ ps) Γf)
    (compiled : Calls.Program b F (expand args bs body)) :
    Calls.Statement b F (.block (.cons (.call f args (.rets bs) body) .nil)) where
  frag := compiled.frag.restrict Γ
  code := compiled.code
  need := compiled.need
  cost := compiled.cost
  allocates := compiled.allocates
  zeroCost := compiled.zeroCost
  sound := by
    intro L frame σ base m repr room capacity
    have same : (Stmt.block (.cons (.call f args (.rets bs) body) .nil)).run σ =
        (Stmt.block (expand args bs body)).run σ :=
      state_result_injective (scoped_tuple_expansion f args bs body σ)
    rw [same]
    exact (Calls.block compiled).sound repr room capacity

/-- info: 'Solidity.Backend.InternalFlow.TupleCalls.Scoped.scoped_tuple_expansion' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms scoped_tuple_expansion
/-- info: 'Solidity.Backend.InternalFlow.TupleCalls.Scoped.statement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms statement

/-- Actual prefix and scoped-statement execution expose both reached frames.
Capacity comes from the summed reached costs; nextInput derives the midpoint.
This is a finite certificate consumer, not unbounded recursive simulation. -/
theorem program_statement_endpoint {C : Contract} {b L frame : Nat} {Γ Δ Ξ : Ctx}
    {F : Frag Γ} {P : Prog C Γ Δ} {s : Stmt C Δ Ξ}
    (before : Calls.Program b F P) (after : Calls.Statement b before.frag s)
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine}
    (repr : StateRepr L b frame F σ base m)
    (roomBefore : b + before.need ≤ frame) (roomAfter : b + after.need ≤ frame)
    (middle : Solidity.Out C σ.H Δ) (out : Solidity.Out C middle.st.H Ξ)
    (capacity : AllocationInput b frame (before.cost σ + after.cost middle.st) σ base m)
    (hp : P.run σ = .ok middle) (hs : s.run middle.st = .ok out) :
    ∃ m₁ base₁ m₂ base₂,
      Evm.run before.code m = .ok m₁ 0 ∧ Evm.run after.code m₁ = .ok m₂ 0 ∧
      StateRepr L b frame before.frag middle.st base₁ m₁ ∧
      StateRepr L b frame after.frag out.st base₂ m₂ ∧
      m₁.stack = m.stack ∧ m₂.stack = m₁.stack ∧
      BaseExtends middle.st.H base₁ base₂ ∧
      GrowsAllocator b frame (after.cost middle.st) middle.st base₁ m₁ out.st base₂ m₂ := by
  obtain ⟨m₁,base₁,hp',repr₁,stack₁,bases₁,growth₁⟩ := PublishedDirectCalls.program_endpoint before repr roomBefore
    (capacity.of_le (Nat.le_add_right _ _)) middle hp
  obtain ⟨m₂,base₂,hs',repr₂,stack₂,bases₂,growth₂⟩ := PublishedDirectCalls.statement_endpoint after repr₁ roomAfter
    (growth₁.nextInput capacity) out hs
  exact ⟨m₁,base₁,m₂,base₂,hp',hs',repr₁,repr₂,stack₁,stack₂,bases₂,growth₂⟩

/-- info: 'Solidity.Backend.InternalFlow.TupleCalls.Scoped.program_statement_endpoint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms program_statement_endpoint
end Scoped

end Solidity.Backend.InternalFlow.TupleCalls
