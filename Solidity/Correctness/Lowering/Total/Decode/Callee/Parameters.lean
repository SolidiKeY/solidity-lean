import Solidity.Correctness.Lowering.Total.Versions.Marked

/-!
# Callee parameter and return syntax

The same ordered list translator serves parameters and return slots. It reads
the declaration width/shape table using the existing marked primitive decoder.
References remain unsupported; this is an executable component, not a callee
admission predicate or a proof of universal callee coverage. Reference locations,
function types, declaration identity and complete function translation remain
separate obligations.
-/
namespace Solidity.Correctness.Lowering.Total.Decode.Callee

open Source (Syn STy)

/-- Preserve every primitive binder, including its name and declaration order.
No parameter location is written for a value type. -/
def parameters (widths : List (Name × Nat)) :
    List (Name × Ty) → Option (Syn (.list .param))
  | [] => some .nil
  | (x, .prim p) :: rest => do
      pure (.cons (.param (.elem (← elemB widths x p)) none (some x))
        (← parameters widths rest))
  | (_, .ref _) :: _ => none

/-- The exact width/marker-table result and its corresponding primitive slot.
This is type representation, not value-range or execution agreement. -/
def Slot (widths : List (Name × Nat)) (x : Name × Ty) (τ : STy) : Prop :=
  ∃ p e, x.2 = .prim p ∧ elemB widths x.1 p = some e ∧
    τ = e.ty .memory ∧ Version.Prim p τ

/-- Ordered correspondence of all binders; neither list may have extra slots. -/
inductive Slots (widths : List (Name × Nat)) : List (Name × Ty) → List STy → Prop where
  | nil : Slots widths [] []
  | cons {x xs τ τs} : Slot widths x τ → Slots widths xs τs →
      Slots widths (x :: xs) (τ :: τs)

private theorem elemB_memory {widths : List (Name × Nat)} {x : Name}
    {p : PrimTy} {e : Source.Elem} (h : elemB widths x p = some e) :
    Version.Prim p (e.ty .memory) := by
  have hp := (Version.elemB_prim h).1
  cases e with
  | fixed s dims => cases dims <;> cases hp
  | _ => first | exact hp | cases hp

/-- Successful spelling preserves names/order and elaborates in any Source
scope to pointwise corresponding primitive types. It neither presupposes nor
adds a restriction on which requests the whole decoder must eventually cover. -/
theorem parameters_faithful (widths : List (Name × Nat))
    (E : Source.Env) (scope : Option String) :
    ∀ (xs : List (Name × Ty)) (ps : Syn (.list .param)),
      parameters widths xs = some ps →
      ps.paramNames = xs.map (fun x => some x.1) ∧
      ∃ τs, ps.tys E scope .memory = some τs ∧ Slots widths xs τs := by
  intro xs
  induction xs with
  | nil =>
      intro ps h
      cases h
      exact ⟨rfl, [], rfl, .nil⟩
  | cons x xs ih =>
      obtain ⟨x, t⟩ := x
      cases t with
      | ref R => intro ps h; cases h
      | prim p =>
          intro ps h
          simp only [parameters, Option.bind_eq_bind, Option.pure_def,
            Option.bind_eq_some_iff, Option.some.injEq] at h
          obtain ⟨e, he, rest, hr, rfl⟩ := h
          obtain ⟨names, τs, typed, slots⟩ := ih rest hr
          refine ⟨?_, e.ty .memory :: τs, ?_, .cons ⟨p, e, rfl, he, rfl, elemB_memory he⟩ slots⟩
          · simp [Source.Syn.paramNames, names]
          · simp [Source.Syn.tys, typed]

/-- Translate both binder lists of the original declaration with its own
width table. No renamed output or lowered body is consulted. -/
def signature (d : FunDecl) : Option (Syn (.list .param) × Syn (.list .param)) := do
  pure (← parameters d.widths d.params, ← parameters d.widths d.rets)

/-- The actual Source frame constructor accepts a successful signature,
with exactly the original ordered names and corresponding primitive slots.
Its body and flags are supplied unchanged; this proves no body semantics. -/
theorem signature_frame {d : FunDecl} {ps rs : Syn (.list .param)}
    (h : signature d = some (ps, rs)) (E : Source.Env) (scope : Option String)
    (body : Syn (.list (.item .body))) (msgValue inModifier : Bool) :
    ∃ f, Source.Frame.mk? E scope ps rs body msgValue inModifier = some f ∧
      f.names = d.params.map (fun p => some p.1) ∧
      f.rnames = d.rets.map (fun p => some p.1) ∧
      Slots d.widths d.params f.ps ∧ Slots d.widths d.rets f.rs ∧
      f.body = body ∧ f.msgValue = msgValue ∧ f.inModifier = inModifier := by
  simp only [signature, Option.bind_eq_bind, Option.pure_def,
    Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨ps', hp, rs', hr, rfl, rfl⟩ := h
  obtain ⟨pn, pts, pt, pr⟩ := parameters_faithful d.widths E scope _ _ hp
  obtain ⟨rn, rts, rt, rr⟩ := parameters_faithful d.widths E scope _ _ hr
  refine ⟨⟨ps'.paramNames, pts, rs'.paramNames, rts, body, msgValue, inModifier⟩,
    ?_, pn, rn, pr, rr, rfl, rfl, rfl⟩
  simp [Source.Frame.mk?, pt, rt]

end Solidity.Correctness.Lowering.Total.Decode.Callee
