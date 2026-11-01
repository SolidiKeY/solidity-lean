import Solidity.Backend.InternalFlow.CallerFrame
/-! Eliminate a genuinely captured typed caller view into represented old-reference
addresses. These laws carry no execution or compiler oracle and assert no heap
content frame. Concrete clients must produce the captured view and reached repr. -/
namespace Solidity.Backend.InternalFlow
open Evm Evm.Memory
namespace CallerView
variable {C : Contract}
/-- Typed optional-reference identity follows from its observed object ID. -/
theorem by_id {H : HTy} {R : RefTy} (v : Option (HRef H R)) (r : HRef H R)
    (observed : v.map HRef.id = some r.id) : v = some r := by
  cases v with
  | none => cases observed
  | some q =>
    have same : q = r := by
      cases q
      cases r
      have ids := Option.some.inj observed
      cases ids
      rfl
    cases same
    rfl

theorem reference {Γ Ξ : Ctx} {σ : State C Γ} (out : Out C σ.H Γ)
    (h : Thin Ξ Γ)
    (captured : TEnv.thin h out.st.env = TEnv.wk out.ext Ξ (TEnv.thin h σ.env))
    {R : RefTy} (i : Idx Ξ (.mem R)) (r : HRef σ.H R)
    (old : TEnv.get (i.wk h) σ.env = some r) :
    TEnv.get (i.wk h) out.st.env = some (r.wk out.ext) := by
  have observed := congrArg (TEnv.get i) captured
  rw [CallerFrame.read_thin,TEnv.get_wk,CallerFrame.read_thin,old] at observed
  exact observed

theorem represented {L b frame : Nat} {Γ Ξ : Ctx} {F : Frag Γ}
    {σ : State C Γ} (out : Out C σ.H Γ) (h : Thin Ξ Γ)
    (captured : TEnv.thin h out.st.env = TEnv.wk out.ext Ξ (TEnv.thin h σ.env))
    {base base' : Nat → Fin W} {m : Machine}
    (repr : StateRepr L b frame F out.st base' m)
    (addresses : BaseExtends σ.H base base') :
    ∀ (R : RefTy) (i : Idx Ξ (.mem R)) (r : HRef σ.H R),
      TEnv.get (i.wk h) σ.env = some r →
        m.mem (cellOf b (i.wk h)) = .val (base r.id) := by
  intro R i r old
  exact PublishedDirectCalls.old_alias_at_entry_address out repr addresses r (i.wk h)
    (reference out h captured i r old)
/-- Different represented primitive-array objects cannot impersonate a captured
caller alias. The separation comes from the reached heap representation. -/
theorem different_array {L b frame : Nat} {Γ Ξ : Ctx} {F : Frag Γ}
    {σ : State C Γ} (out : Out C σ.H Γ) (h : Thin Ξ Γ)
    (captured : TEnv.thin h out.st.env = TEnv.wk out.ext Ξ (TEnv.thin h σ.env))
    {base : Nat → Fin W} {m : Machine}
    (repr : StateRepr L b frame F out.st base m)
    {p q : PrimTy} (i : Idx Ξ (.mem (.array (.prim p))))
    (r : HRef σ.H (.array (.prim p)))
    (old : TEnv.get (i.wk h) σ.env = some r)
    (other : HRef out.st.H (.array (.prim q))) (different : r.id ≠ other.id) :
    m.mem (cellOf b (i.wk h)) ≠ .val (base other.id) := by
  have preserved := reference out h captured i r old
  obtain ⟨found,found_eq,pointer⟩ := repr.pointers (i.wk h)
  have eq : found = r.wk out.ext := Option.some.inj (found_eq.symm.trans preserved)
  subst found
  have gap := repr.heap.separated (r.wk out.ext) other different
  have addresses : base r.id ≠ base other.id := by
    intro same
    change (base r.id).val + 1 + _ ≤ (base other.id).val ∨
      (base other.id).val + 1 + _ ≤ (base r.id).val at gap
    rw [same] at gap
    rcases gap with first | last <;> omega
  exact fun wrong => addresses (Word.val.inj (pointer.symm.trans wrong))

/-- Read a captured caller alias after actual result/local-prefix removal.
The reached context may extend the caller; no heap-content frame is asserted. -/
theorem reference_drop {Γ Δ Ξ : Ctx} {σ : State C Γ} (out : Out C σ.H Δ)
    (extension : Ext Γ Δ) (h : Thin Ξ Γ)
    (captured : TEnv.thin h (TEnv.drop extension out.st.env) =
      TEnv.wk out.ext Ξ (TEnv.thin h σ.env))
    {R : RefTy} (i : Idx Ξ (.mem R)) (r : HRef σ.H R)
    (old : TEnv.get (i.wk h) σ.env = some r) :
    TEnv.get ((i.wk h).ext extension) out.st.env = some (r.wk out.ext) := by
  rw [TEnv.get_ext_drop]
  have observed := congrArg (TEnv.get i) captured
  rw [CallerFrame.read_thin,TEnv.get_wk,CallerFrame.read_thin,old] at observed
  exact observed

/-- A real reached representation exposes the old target address even when
result/local binders remain in the output context. -/
theorem represented_drop {L b frame : Nat} {Γ Δ Ξ : Ctx} {F : Frag Δ}
    {σ : State C Γ} (out : Out C σ.H Δ) (extension : Ext Γ Δ) (h : Thin Ξ Γ)
    (captured : TEnv.thin h (TEnv.drop extension out.st.env) =
      TEnv.wk out.ext Ξ (TEnv.thin h σ.env))
    {base base' : Nat → Fin W} {m : Machine}
    (repr : StateRepr L b frame F out.st base' m)
    (addresses : BaseExtends σ.H base base') :
    ∀ (R : RefTy) (i : Idx Ξ (.mem R)) (r : HRef σ.H R),
      TEnv.get (i.wk h) σ.env = some r →
        m.mem (cellOf b ((i.wk h).ext extension)) = .val (base r.id) := by
  intro R i r old
  exact PublishedDirectCalls.old_alias_at_entry_address out repr addresses r
    ((i.wk h).ext extension) (reference_drop out extension h captured i r old)

/-- Primitive caller values survive the same actual extended-context drop;
heap mutation by the callee remains unrestricted. -/
theorem value_drop {Γ Δ Ξ : Ctx} {σ : State C Γ} (out : Out C σ.H Δ)
    (extension : Ext Γ Δ) (h : Thin Ξ Γ)
    (captured : TEnv.thin h (TEnv.drop extension out.st.env) =
      TEnv.wk out.ext Ξ (TEnv.thin h σ.env))
    {p : PrimTy} (i : Idx Ξ (.val p)) :
    TEnv.get ((i.wk h).ext extension) out.st.env = TEnv.get (i.wk h) σ.env := by
  rw [TEnv.get_ext_drop]
  have observed := congrArg (TEnv.get i) captured
  rw [CallerFrame.read_thin,TEnv.get_wk,CallerFrame.read_thin] at observed
  exact observed

theorem represented_value_drop {L b frame : Nat} {Γ Δ Ξ : Ctx} {F : Frag Δ}
    {σ : State C Γ} (out : Out C σ.H Δ) (extension : Ext Γ Δ) (h : Thin Ξ Γ)
    (captured : TEnv.thin h (TEnv.drop extension out.st.env) =
      TEnv.wk out.ext Ξ (TEnv.thin h σ.env))
    {base : Nat → Fin W} {m : Machine}
    (repr : StateRepr L b frame F out.st base m)
    {p : PrimTy} (i : Idx Ξ (.val p)) :
    ReprV p (TEnv.get (i.wk h) σ.env)
      (m.mem (cellOf b ((i.wk h).ext extension))) := by
  have encoded := repr.core.vals ((i.wk h).ext extension)
  change ReprV p (TEnv.get ((i.wk h).ext extension) out.st.env)
    (m.mem (cellOf b ((i.wk h).ext extension))) at encoded
  rw [value_drop out extension h captured i] at encoded
  exact encoded

/-- info: 'Solidity.Backend.InternalFlow.CallerView.by_id' does not depend on any axioms -/
#guard_msgs in #print axioms by_id
/-- info: 'Solidity.Backend.InternalFlow.CallerView.reference' depends on axioms: [propext] -/
#guard_msgs in #print axioms reference
/-- info: 'Solidity.Backend.InternalFlow.CallerView.represented' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms represented
/-- info: 'Solidity.Backend.InternalFlow.CallerView.different_array' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms different_array
end CallerView
end Solidity.Backend.InternalFlow
