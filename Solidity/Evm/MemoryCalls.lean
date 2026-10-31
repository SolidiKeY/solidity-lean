import Solidity.Evm.MemoryCompile
import Solidity.Calculus.SoundCalls

/-!
# Checked internal calls with memory frames

The existing intrinsic call expansion is compiled with the memory backend.
All caller locals remain in the represented context during the inlined body;
no core-only simulation is used as a memory prefix. Certificates retain the
largest expanded frame and the exact reached allocation cost. A returned
reference is copied by pointer after dropping the private parameter frame.
-/
namespace Solidity.Evm.Memory.Calls

variable {C : Contract}

/-- A typed program and its memory simulation, including private call frames. -/
structure Program (b : Nat) {Γ Δ : Ctx} (F : Frag Γ) (P : Prog C Γ Δ) where
  frag : Frag Δ
  code : List Instr
  need : Nat
  cost : State C Γ → Nat
  sound : ∀ {L frame : Nat} {σ : State C Γ} {base : Nat → Fin W} {m : Machine},
    StateRepr L b frame F σ base m → b + need ≤ frame →
    AllocationInput b frame (cost σ) σ base m →
    GrowingResult L b frame (cost σ) frag σ base m (P.run σ) (run code m)
  allocates : Bool
  zeroCost : allocates = false → ∀ σ, cost σ = 0

structure Statement (b : Nat) {Γ Δ : Ctx} (F : Frag Γ) (s : Stmt C Γ Δ) where
  frag : Frag Δ
  code : List Instr
  need : Nat
  cost : State C Γ → Nat
  sound : ∀ {L frame : Nat} {σ : State C Γ} {base : Nat → Fin W} {m : Machine},
    StateRepr L b frame F σ base m → b + need ≤ frame →
    AllocationInput b frame (cost σ) σ base m →
    GrowingResult L b frame (cost σ) frag σ base m (s.run σ) (run code m)
  allocates : Bool
  zeroCost : allocates = false → ∀ σ, cost σ = 0

def plain {b : Nat} {Γ Δ : Ctx} {F : Frag Γ} {P : Prog C Γ Δ}
    (p : CompiledProg b F P) : Program b F P :=
  ⟨p.frag, p.code, frameNeedProg P, allocationCostProg P, p.cert.correct,
    hasAllocation P, allocationCostProg_zero P⟩

def plainStmt {b : Nat} {Γ Δ : Ctx} {F : Frag Γ} {s : Stmt C Γ Δ}
    (p : CompiledStmt b F s) : Statement b F s :=
  ⟨p.frag, p.code, frameNeedStmt s, allocationCostStmt s, p.cert.correct,
    hasAllocationStmt s, by
      intro hz σ
      simp only [allocationCostStmt, hz, Bool.false_eq_true, if_false]⟩

def nil (b : Nat) {Γ : Ctx} (F : Frag Γ) : Program (C := C) b F .nil :=
  plain ⟨F, [], .nil F⟩

/-- Do not force a source outcome merely to learn that its suffix costs zero.
The thunk preserves this short-circuit in native evaluation as well as the kernel. -/
private def reachedCost {α : Type} (allocates : Bool) (cost : α → Nat) (result : Unit → TRes α) : Nat :=
  if allocates then match result () with | .ok x => cost x | .error _ => 0 else 0

/-- The short-circuit is propositionally the exact ordinary reached cost. -/
private theorem reachedCost_eq {α : Type} {allocates : Bool} {cost : α → Nat}
    (hz : allocates = false → ∀ x, cost x = 0) (result : Unit → TRes α) :
    reachedCost allocates cost result = match result () with | .ok x => cost x | .error _ => 0 := by
  cases hb : allocates with
  | false =>
    simp only [reachedCost, Bool.false_eq_true, if_false]
    cases result () with
    | error e => rfl
    | ok x => exact (hz hb x).symm
  | true => rfl

def cons {b : Nat} {Γ Δ Ξ : Ctx} {F : Frag Γ} {s : Stmt C Γ Δ} {P : Prog C Δ Ξ}
    (hs : Statement b F s) (hp : Program b hs.frag P) : Program b F (.cons s P) where
  frag := hp.frag
  code := hs.code ++ hp.code
  need := max hs.need hp.need
  cost σ := hs.cost σ + reachedCost hp.allocates (fun o => hp.cost o.st) (fun _ => s.run σ)
  allocates := hs.allocates || hp.allocates
  zeroCost := by
    intro hz σ
    have hh : hs.allocates = false ∧ hp.allocates = false := Bool.or_eq_false_iff.mp hz
    rw [hs.zeroCost hh.1 σ]
    simp only [reachedCost, hh.2, Bool.false_eq_true, if_false, Nat.zero_add]
  sound := by
    intro L frame σ base m h hcap ha
    rw [reachedCost_eq (fun hz o => hp.zeroCost hz o.st)] at ha ⊢
    have hcs : b + hs.need ≤ frame := by omega
    have hcp : b + hp.need ≤ frame := by omega
    have hi := ha.of_le (Nat.le_add_right (hs.cost σ) _)
    rcases hs.sound h hcs hi with ⟨o, m₁, base₁, ho, hc, hm, hk, he, hal⟩ | ⟨ho, hc⟩
    · rw [Solidity.Prog.run_cons_ok ho, run_append_ok hc]
      have ha' : AllocationInput b frame (hs.cost σ + hp.cost o.st) σ base m := by
        simpa only [ho] using ha
      have hit := hal.nextInput ha'
      rcases hp.sound hm hcp hit with ⟨o', m₂, base₂, ho', hc', hm', hk', he', hal'⟩ | ⟨ho', hc'⟩
      · refine .inl ⟨⟨o'.st, o.ext.trans o'.ext⟩, m₂, base₂,
          by rw [ho']; rfl, hc', hm', hk'.trans hk, he.trans o.ext he', ?_⟩
        simpa only [ho] using hal.comp hal'
      · exact .inr ⟨by rw [ho']; rfl, hc'⟩
    · refine .inr ⟨?_, run_append_revert hc⟩
      show TRun.seq s.runR P.runR σ = _
      simp only [TRun.seq, Solidity.Stmt.run] at ho ⊢
      rw [ho]

def block {b : Nat} {Γ Δ : Ctx} {F : Frag Γ} {P : Prog C Γ Δ}
    (hp : Program b F P) : Statement b F (.block P) where
  frag := hp.frag.restrict Γ
  code := hp.code
  need := hp.need
  cost := hp.cost
  allocates := hp.allocates
  zeroCost := hp.zeroCost
  sound := by
    intro L frame σ base m h hcap ha
    rcases hp.sound h hcap ha with ⟨o, m', base', ho, hc, hm, hk, he, hal⟩ | ⟨ho, hc⟩
    · refine .inl ⟨⟨o.st.drop P.ext, o.ext⟩, m', base', ?_, hc, hm.drop P.ext, hk, he, hal⟩
      change (P.run σ).map (fun o => (⟨o.st.drop P.ext, o.ext⟩ : Solidity.Out C σ.H Γ)) = _
      rw [ho]
      rfl
    · refine .inr ⟨?_, hc⟩
      change (P.run σ).map (fun o => (⟨o.st.drop P.ext, o.ext⟩ : Solidity.Out C σ.H Γ)) = _
      rw [ho]
      rfl

/-- Equality of state observations recovers the actual intrinsic outcome. -/
private theorem run_ok_of_state {Γ Δ : Ctx} {σ : State C Γ}
    {res : TRes (Solidity.Out C σ.H Δ)} {τ : State C Δ}
    (h : res.map (·.st) = .ok τ) : ∃ o, res = .ok o ∧ o.st = τ := by
  cases res with
  | error e => cases h
  | ok o => exact ⟨o, rfl, Except.ok.inj h⟩

private theorem run_error_of_state {Γ Δ : Ctx} {σ : State C Γ}
    {res : TRes (Solidity.Out C σ.H Δ)}
    (h : res.map (·.st) = .error .revert) : res = .error .revert := by
  cases res with
  | error e => cases h; rfl
  | ok o => cases h

/-- Reuse an exact expansion with identical input and output contexts. -/
def equivalent {b : Nat} {Γ Δ : Ctx} {F : Frag Γ} {s : Stmt C Γ Δ} {Q : Prog C Γ Δ}
    (hq : Program b F Q) (heq : ∀ σ, Q.runSt σ = s.runSt σ) : Statement b F s where
  frag := hq.frag
  code := hq.code
  need := hq.need
  cost := hq.cost
  allocates := hq.allocates
  zeroCost := hq.zeroCost
  sound := by
    intro L frame σ base m h hcap ha
    rcases hq.sound h hcap ha with ⟨o, m', base', ho, hc, hm, hk, he, hal⟩ | ⟨ho, hc⟩
    · have hs : (s.run σ).map (·.st) = .ok o.st := by
        change s.runSt σ = _
        rw [← heq σ]
        show (Q.run σ).map (·.st) = _
        rw [ho]
        rfl
      obtain ⟨o', ho', ht⟩ := run_ok_of_state hs
      refine .inl ⟨o', m', base', ho', hc, ?_, hk, he, ?_⟩
      · rw [ht]; exact hm
      · rw [ht]; exact hal
    · have hs : (s.run σ).map (·.st) = .error .revert := by
        change s.runSt σ = _
        rw [← heq σ]
        show (Q.run σ).map (·.st) = _
        rw [ho]
        rfl
      exact .inr ⟨run_error_of_state hs, hc⟩

/-- The compiler uses the same frame expansion as internalCallExpand. -/
def expandNone {Γ ps Γf : Ctx} (args : Args C Γ ps) (body : Prog C ps Γf) : Prog C Γ Γ :=
  .cons (.block (args.declsThen
    (.cons (.block (body.wk (Thin.atop ps Γ)).2.2) .nil))) .nil

theorem expandNone_run {Γ ps Γf : Ctx} (f : Name) (args : Args C Γ ps)
    (body : Prog C ps Γf) (σ : State C Γ) :
    (expandNone args body).runSt σ = (Stmt.call f args .none body).runSt σ := by
  rw [expandNone, Prog.runSt_single, Stmt.runSt_block]
  refine Eq.trans ?_ (Stmt.runSt_callNone f args body σ)
  congr 2 <;> exact Subsingleton.elim _ _

def expandVal {Γ ps Γf : Ctx} (args : Args C Γ ps) (p : PrimTy) (r : Var)
    (res : Option (Idx Γ (.val p))) (body : Prog C (.val p :: ps) Γf) : Prog C Γ Γ :=
  .cons (.block (args.declsThen (.cons (.declLocal p r none)
    (.cons (.block (body.wk (Thin.atop (.val p :: ps) Γ)).2.2) (match res with
      | none => .nil
      | some j => .cons (.assignLocal (j.under ps).there (.simple (.local .here))) .nil))))) .nil

theorem expandVal_run {Γ ps Γf : Ctx} (f : Name) (args : Args C Γ ps) (p : PrimTy) (r : Var)
    (res : Option (Idx Γ (.val p))) (body : Prog C (.val p :: ps) Γf) (σ : State C Γ) :
    (expandVal args p r res body).runSt σ = (Stmt.call f args (.val p r res) body).runSt σ := by
  rw [expandVal.eq_def, Prog.runSt_single, Stmt.runSt_block]
  refine Eq.trans ?_ (Stmt.runSt_callVal f args p r res body σ)
  congr 2 <;> exact Subsingleton.elim _ _



/-- Private parameters below a returned pointer are removed without copying its object. -/
def expandMem {Γ ps Γf : Ctx} (args : Args C Γ ps) (R : RefTy) (r : Var)
    (hd : (Ty.ref R).defaultOkS = true) (hm : (Ty.ref R).mapFree = true)
    (body : Prog C (.mem R :: ps) Γf) : Prog C Γ (.mem R :: (ps ++ Γ)) :=
  args.declsThen (.cons (.declMem R r none hd hm)
    (.cons (.block (body.wk (Thin.atop (.mem R :: ps) Γ)).2.2) .nil))

theorem expandMem_run {Γ ps Γf : Ctx} (f : Name) (args : Args C Γ ps) (R : RefTy) (r : Var)
    (hd : (Ty.ref R).defaultOkS = true) (hm : (Ty.ref R).mapFree = true)
    (body : Prog C (.mem R :: ps) Γf) (σ : State C Γ) :
    ((expandMem args R r hd hm body).runSt σ).map
      (State.thin (.keep (Thin.ofExt (Ext.append Γ ps)))) =
      (Stmt.call f args (.mem R r hd hm) body).runSt σ := by
  rw [expandMem, Args.runSt_declsThen]
  show _ = (TRun.call args (.mem R r hd hm) body.ext body.runR σ).map (·.st)
  rw [TRun.call_eq]
  cases args.evalT σ with
  | error => rfl
  | ok a =>
    let g := (σ.withEnv a).allocDefaultG R hm
    show (Prog.runSt _ _).map _ = (TRun.callFrom (.mem R r hd hm) body.ext body.runR σ
      ⟨g.st.push (t := .mem R) (some g.val), g.ext⟩).map _
    rw [Prog.runSt_cons, Stmt.runSt_declMem_none, TRes.ok_bind, State.withEnv_append_lift,
      State.allocDefaultG_lift, Prog.runSt_single]
    show (Stmt.runSt ((g.st.push (t := .mem R) (some g.val)).lift (Thin.atop (.mem R :: ps) Γ)
      (some g.val, TEnv.wk g.ext _ (TEnv.append ps a σ.env))) _).map _ = _
    rw [Stmt.runSt, Stmt.run_block_wk]
    unfold TRun.callFrom Prog.run
    dsimp only
    cases Prog.runR body (g.st.push (t := .mem R) (some g.val)) with
    | error => rfl
    | ok o =>
      exact congrArg Except.ok (by
        simp only [Out.drop, Out.lift, State.lift, State.drop, State.thin, State.withEnv,
          CallRet.leaveT]
        erw [TEnv.thin_keep_put_atop]
        rfl)

def returnPointerCode (b : Nat) (Γ ps : Ctx) : List Instr :=
  [.mload (cell (b + Γ.length + ps.length)), .mstore (cell (b + Γ.length))]

def memoryReturn {b : Nat} {Γ ps Γf : Ctx} {F : Frag Γ} (f : Name)
    (args : Args C Γ ps) (R : RefTy) (r : Var)
    (hd : (Ty.ref R).defaultOkS = true) (hmf : (Ty.ref R).mapFree = true)
    (body : Prog C (.mem R :: ps) Γf)
    (hq : Program b F (expandMem args R r hd hmf body)) :
    Statement b F (.call f args (.mem R r hd hmf) body) where
  frag := (hq.frag.restrict Γ).push (.mem R) .ok
  code := hq.code ++ returnPointerCode b Γ ps
  need := hq.need
  cost := hq.cost
  allocates := hq.allocates
  zeroCost := hq.zeroCost
  sound := by
    intro L frame σ base m h hcap ha
    rcases hq.sound h hcap ha with ⟨o, m', base', ho, hc, hm, hk, he, hal⟩ | ⟨ho, hc⟩
    · obtain ⟨ref, href, hptr⟩ := hm.pointers (.here : Idx (.mem R :: (ps ++ Γ)) (.mem R))
      let τ := o.st.thin (.keep (Thin.ofExt (Ext.append Γ ps)))
      have hτ : τ = (o.st.drop (Ext.append Γ (.mem R :: ps))).push (t := .mem R) (some ref) := by
        unfold τ State.thin State.drop State.push State.withEnv
        simp only [TEnv.thin, TEnv.thin_ofExt]
        have href' : o.st.env.1 = some ref := href
        rw [href']
        rfl
      have hs : (Stmt.run σ (.call f args (.mem R r hd hmf) body)).map (·.st) = .ok τ := by
        change (Stmt.call f args (.mem R r hd hmf) body).runSt σ = _
        rw [← expandMem_run f args R r hd hmf body σ]
        show ((Prog.run σ _).map (·.st)).map _ = _
        rw [ho]
        rfl
      obtain ⟨o', ho', ht⟩ := run_ok_of_state hs
      have hroom : b + (Γ.length + 1) ≤ frame := by
        have hx := hm.locals
        simp only [List.length_cons, List.length_append] at hx
        omega
      have hrep := (hm.drop (Ext.append Γ (.mem R :: ps))).consMem ref hroom
      have hlocal : b + Γ.length < frame := by omega
      have hz : 0 < b → 0 < b + Γ.length := by omega
      have hcode : run (returnPointerCode b Γ ps) m' =
          .ok (writeMachine m' (cell (b + Γ.length)) (.val (base' ref.id))) 0 := by
        have hp : m'.mem (cell (b + Γ.length + ps.length)) = .val (base' ref.id) := by
          simpa only [cellOf, lvl_here, List.length_append, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hptr
        simp only [returnPointerCode, run, exec_cons_zero, Instr.step, Machine.next,
          hp, Out.ok_bind, exec_nil, writeMachine]
      refine .inl ⟨o', writeMachine m' (cell (b + Γ.length)) (.val (base' ref.id)),
        base', ho', ?_, ?_, hk, he, ?_⟩
      · rw [run_append_ok hc]; exact hcode
      · rw [ht, hτ]; exact hrep
      · intro cursor hb halloc hspace
        rw [ht, hτ]
        exact (hal cursor hb halloc hspace).localWrite _ (hz hb) hlocal _
    · have hs : (Stmt.run σ (.call f args (.mem R r hd hmf) body)).map (·.st) = .error .revert := by
        change (Stmt.call f args (.mem R r hd hmf) body).runSt σ = _
        rw [← expandMem_run f args R r hd hmf body σ]
        show ((Prog.run σ _).map (·.st)).map _ = _
        rw [ho]
        rfl
      exact .inr ⟨run_error_of_state hs, run_append_revert hc⟩

def branch {b : Nat} {Γ Δ Ξ : Ctx} {F : Frag Γ} (c : Val C Γ .bool)
    {thn : Prog C Γ Δ} {els : Prog C Γ Ξ} (cond : CompiledVal b F c)
    (ht : Program b F thn) (he : Program b F els) : Statement b F (.ite c thn els) where
  frag := (ht.frag.restrict Γ).meet (he.frag.restrict Γ)
  code := conditionalCode cond.code ht.code he.code
  need := max ht.need he.need
  cost σ := reachedCost (ht.allocates || he.allocates)
    (fun v => if boolT v then ht.cost σ else he.cost σ) (fun _ => c.evalT σ)
  allocates := ht.allocates || he.allocates
  zeroCost := by
    intro hz σ
    simp only [reachedCost, hz, Bool.false_eq_true, if_false]
  sound := by
    intro L frame σ base m h hcap ha
    have hz : (ht.allocates || he.allocates) = false →
        ∀ v, (if boolT v then ht.cost σ else he.cost σ) = 0 := by
      intro hb v
      have hh : ht.allocates = false ∧ he.allocates = false := Bool.or_eq_false_iff.mp hb
      rw [ht.zeroCost hh.1 σ, he.zeroCost hh.2 σ]
      exact ite_self 0
    rw [reachedCost_eq hz] at ha ⊢
    have hbt : b + ht.need ≤ frame := by omega
    have hbe : b + he.need ≤ frame := by omega
    change GrowingResult _ _ _ _ _ _ _ _ (TRun.ite c thn.ext thn.runR els.ext els.runR σ) _
    simp only [TRun.ite, conditionalCode, List.append_assoc]
    rcases cond.cert.correct h with ⟨vc, wc, hvc, hrc, hrunc⟩ | ⟨hvc, hrunc⟩
    · obtain rfl := hrc.bool_inv
      rw [run_append_ok hrunc, hvc]
      simp only [bind, Except.bind, Solidity.boolT]
      cases vc
      · simp only [hvc, Solidity.boolT, Bool.false_eq_true, if_false] at ha ⊢
        rw [run_append_skip (m' := m) (k := ht.code.length + 1) rfl,
          show ht.code.length + 1 = ht.code.length + 1 from rfl, exec_append, exec_skip]
        simp only [Out.ok_bind]
        rcases (block he).sound h hbe ha with ⟨o, m', base', ho, hc, hm, hk, hex, hal⟩ | ⟨ho, hc⟩
        · exact .inl ⟨o, m', base', ho, hc, hm.meetRight _, hk, hex, hal⟩
        · exact .inr ⟨ho, hc⟩
      · simp only [hvc, Solidity.boolT, if_true] at ha ⊢
        rw [run_append_skip (m' := m) (k := 0) rfl]
        rcases (block ht).sound h hbt ha with ⟨o, m', base', ho, hc, hm, hk, hex, hal⟩ | ⟨ho, hc⟩
        · refine .inl ⟨o, m', base', ho, ?_, hm.meet _, hk, hex, hal⟩
          change run ht.code m = _ at hc
          change run _ m = _
          rw [run_append_ok hc]
          exact exec_length _ _
        · exact .inr ⟨ho, run_append_revert hc⟩
    · exact .inr ⟨by simp only [bind, Except.bind, hvc], run_append_revert hrunc⟩

abbrev Expander (C : Contract) (b : Nat) :=
  {Γ Δ : Ctx} → (F : Frag Γ) → (s : Stmt C Γ Δ) → Option (Statement b F s)

mutual
private def statementUsing (b : Nat) (expand : Expander C b) {Γ Δ : Ctx} (F : Frag Γ) :
    (s : Stmt C Γ Δ) → Option (Statement b F s)
  | .block body => do
    let out ← programUsing b expand F body
    pure (block out)
  | .ite c thn els => do
    let cond ← Memory.compileVal b F c
    let left ← programUsing b expand F thn
    let right ← programUsing b expand F els
    pure (branch c cond left right)
  | s => match Memory.compileStmt b F s with
    | some out => some (plainStmt out)
    | none => expand F s

private def programUsing (b : Nat) (expand : Expander C b) {Γ Δ : Ctx} (F : Frag Γ) :
    (P : Prog C Γ Δ) → Option (Program b F P)
  | .nil => some (nil b F)
  | .cons s P => do
    let head ← statementUsing b expand F s
    let tail ← programUsing b expand head.frag P
    pure (cons head tail)
end

private def expandCall (b : Nat)
    (previous : {Γ Δ : Ctx} → (F : Frag Γ) → (P : Prog C Γ Δ) → Option (Program b F P))
    {Γ Δ : Ctx} (F : Frag Γ) (s : Stmt C Γ Δ) : Option (Statement b F s) :=
  match s with
  | @Solidity.Stmt.call _ _ _ ps _ Γf f args ret body =>
    CallRet.casesOn (motive := fun rs _ ret => (body : Prog C (rs ++ ps) Γf) →
      Option (Statement b F (.call f args ret body))) ret
      (fun body => do
        let out ← previous F (expandNone args body)
        pure (equivalent out (expandNone_run f args body)))
      (fun p r res body => do
        let out ← previous F (expandVal args p r res body)
        pure (equivalent out (expandVal_run f args p r res body)))
      (fun _ _ => none)
      (fun R r hd hm body => do
        let out ← previous F (expandMem args R r hd hm body)
        pure (memoryReturn f args R r hd hm body out))
      (fun _ _ _ => none) body
  | _ => none

/-- Each call expansion removes one level of calls. No public search limit. -/
private def atHeight (b : Nat) : Nat → {Γ Δ : Ctx} →
    (F : Frag Γ) → (P : Prog C Γ Δ) → Option (Program b F P)
  | 0, _, _, F, P => (Memory.compileProg b F P).map plain
  | n + 1, _, _, F, P => programUsing b (expandCall b (atHeight b n)) F P

mutual
private def statementHeight {Γ Δ : Ctx} : Stmt C Γ Δ → Nat
  | .call _ _ _ body => height body + 1
  | .block body => height body
  | .ite _ thn els => max (height thn) (height els)
  | _ => 0

private def height {Γ Δ : Ctx} : Prog C Γ Δ → Nat
  | .nil => 0
  | .cons s P => max (statementHeight s) (height P)
end

/-- Direct internal signatures only; unsupported syntax retains refusal. -/
def compile (b : Nat) {Γ Δ : Ctx} (F : Frag Γ) (P : Prog C Γ Δ) : Option (Program b F P) :=
  atHeight b (height P) F P

end Solidity.Evm.Memory.Calls
