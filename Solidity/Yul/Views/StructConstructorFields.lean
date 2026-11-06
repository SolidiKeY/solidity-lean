import Solidity.Yul.Views.AllocatedObjectMemory

namespace Solidity.Yul.Views

/-- Member types are derived from the ACTUAL resolved constructor certificate
and owner declaration lookup, not an unrelated supplied layout equation. -/
theorem structConstructor_types (E : Source.Env) (name : Source.DeclName) (ps : List Source.STy)
    (typed : (E.structFields name .memory).map (List.map Prod.snd)=some ps) : E.layout.fields name=ps := by
  change ((E.structFields name .memory).getD []).map Prod.snd=ps
  cases found : E.structFields name .memory with
  | none => rw [found] at typed; cases typed
  | some fields =>
    rw [found] at typed
    exact Option.some.inj typed

/-- Parameter-list recursion over existing intrinsic Vals, not a new argument
AST or intermediate state. Every resulting field remains actual Data.val. -/
def constructorFields {D : Source.Layout} : (ps : List Source.STy) → Source.Vals D ps → Source.DataList D ps
  | [], vs => by cases vs; exact .nil
  | _::ps, vs => by cases vs with | cons value rest => exact .cons (.val value) (constructorFields ps rest)

theorem constructorFields_run {E Γ} (s : Source.EMState E Γ) {ps : List Source.STy} (vs : Source.Vals E.layout ps) :
    (Source.fieldsOf vs ps).run s=(.ok (constructorFields ps vs),s) := by
  induction vs with
  | nil => rfl
  | @cons τ ps value rest ih =>
    rw [Source.fieldsOf,dif_pos rfl,Source.Hoare.run_bind,ih]
    rfl

theorem constructorFields_inner {E : Source.Env} {ps : List Source.STy} (vs : Source.Vals E.layout ps) :
    (constructorFields ps vs).AllVal := by
  induction vs with
  | nil => trivial
  | cons value rest ih => exact ⟨⟨value,rfl⟩,ih⟩

theorem constructorFields_valid {E : Source.Env} (H : Source.HeapTy) {ps : List Source.STy} (vs : Source.Vals E.layout ps)
    (valid : Source.RValsOK E H vs.toR) : Source.DataListOK E H (constructorFields ps vs) := by
  induction vs with
  | nil => exact .nil
  | cons value rest ih => exact .cons (.val valid.1) (ih valid.2)

end Solidity.Yul.Views
