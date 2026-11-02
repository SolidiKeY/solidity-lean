import Solidity.Semantics.ExternalReturnBytes

/-!
# Declared primitive return validation and typed projection

Validate every declared return before binding or discarding values. Successful
projections retain the actual byte-derived words. These helpers do not change
callback execution or certify source call-site, frame or native provenance.
The operational consumer remains a separate unfinished O1 component.
-/
namespace Solidity.PrimitiveReturnConsumer
open Semantics
variable {C : Contract} {H : HTy}

/-- A checked primitive signature; no enum/nominal erasure or source default. -/
structure Declaration (types : List PrimTy) where
  context : Ctx
  binders : Binders context
  signature : binders.toList.map Prod.fst = types

/-- The supported source fragment binds every result or discards every result.
Names can differ; the retained environment remains intrinsically typed. -/
inductive Projection : {δ : Ctx} → Binders δ → {ρ : Ctx} → Binders ρ → Type where
  | bind {δ : Ctx} (declared caller : Binders δ) : Projection declared caller
  | discard {δ : Ctx} (declared : Binders δ) : Projection declared Binders.nil

def Projection.env {δ ρ : Ctx} {declared : Binders δ} {caller : Binders ρ}
    (selection : Projection declared caller) : TEnv C H δ → TEnv C H ρ :=
  Projection.casesOn
    (motive := fun {ρ} _ _ => TEnv C H δ → TEnv C H ρ)
    selection (fun _ value => value) (fun _ => ())

/-- Decode the entire declared result first, using the existing actual decoder.
Only successful decoded environments can be projected into caller binders. -/
def consume {types : List PrimTy} (declared : Declaration types)
    {ρ : Ctx} {caller : Binders ρ} (selection : Projection declared.binders caller)
    (bytes : List UInt8) : TRes (TEnv C H ρ × List Word) := do
  let (values, rest) ← ExternalReturnBytes.decode declared.binders bytes
  pure (selection.env values, rest)

theorem declared_failure {types : List PrimTy} (declared : Declaration types)
    {ρ : Ctx} {caller : Binders ρ} (selection : Projection declared.binders caller)
    {bytes : List UInt8} {e : THalt}
    (failed : ExternalReturnBytes.decode (C := C) (H := H) declared.binders bytes = .error e) :
    consume (C := C) (H := H) declared selection bytes = .error e := by
  unfold consume
  rw [failed]
  rfl

theorem declared_success {types : List PrimTy} (declared : Declaration types)
    {ρ : Ctx} {caller : Binders ρ} (selection : Projection declared.binders caller)
    {bytes : List UInt8} {values : TEnv C H declared.context} {rest : List Word}
    (decoded : ExternalReturnBytes.decode declared.binders bytes = .ok (values, rest)) :
    consume declared selection bytes = .ok (selection.env values, rest) := by
  unfold consume
  rw [decoded]
  rfl

theorem success_validates_declaration {types : List PrimTy} (declared : Declaration types)
    {ρ : Ctx} {caller : Binders ρ} (selection : Projection declared.binders caller)
    {bytes : List UInt8} {result : TEnv C H ρ × List Word}
    (success : consume declared selection bytes = .ok result) :
    ∃ values rest, ExternalReturnBytes.decode declared.binders bytes = .ok (values, rest) ∧
      result = (selection.env values, rest) := by
  cases decoded : ExternalReturnBytes.decode (C := C) (H := H) declared.binders bytes with
  | error e => rw [declared_failure declared selection decoded] at success; cases success
  | ok pair =>
    obtain ⟨values, rest⟩ := pair
    exact ⟨values, rest, rfl, (Except.ok.inj ((declared_success declared selection decoded).symm.trans success)).symm⟩

/-- Binder labels cannot affect actual primitive word decoding. -/
theorem decode_names {δ : Ctx} (declared caller : Binders δ) (vs : List Word) :
    declared.decodeT (C := C) (H := H) vs = caller.decodeT vs := by
  induction declared with
  | nil => cases caller; rfl
  | @snoc δ bs p x ih =>
    cases caller with
    | snoc cs q y =>
      let next : (TEnv C H δ × List Word) → TRes (TEnv C H (.val p :: δ) × List Word) :=
        fun pair => match pair.2 with
          | v :: rest => match PrimTy.ofWord? p v with
            | some value => .ok ((value, pair.1), rest)
            | none => .error .revert
          | [] => .error .revert
      change (bs.decodeT vs >>= next) = (cs.decodeT vs >>= next)
      rw [ih cs]

/-- A successful consumer supplies the actual bytes' words to the existing
caller decoder. Discarded declared values may remain in its unused word tail;
no detached arbitrary-word witness is chosen. -/
theorem success_reads_actual_words {types : List PrimTy} (declared : Declaration types)
    {ρ : Ctx} {caller : Binders ρ} (selection : Projection declared.binders caller)
    {bytes : List UInt8} {result : TEnv C H ρ × List Word}
    (success : consume declared selection bytes = .ok result) :
    ∃ vs rest, ExternalReturnBytes.words declared.context.length bytes = .ok vs ∧
      caller.decodeT (C := C) (H := H) vs = .ok (result.1, rest) := by
  obtain ⟨values, tail, decoded, resultEq⟩ := success_validates_declaration declared selection success
  obtain ⟨vs, read, decodeWords⟩ := ExternalReturnBytes.decode_ok decoded
  cases selection with
  | bind caller =>
    subst result
    exact ⟨vs, tail, read, (decode_names caller declared.binders vs).trans decodeWords⟩
  | discard =>
    subst result
    exact ⟨vs, vs, read, rfl⟩

/-- Validation cannot skip a demanded declared word merely because the caller
will discard the result. -/
theorem success_complete_word {types : List PrimTy} (declared : Declaration types)
    {ρ : Ctx} {caller : Binders ρ} (selection : Projection declared.binders caller)
    {bytes : List UInt8} {result : TEnv C H ρ × List Word}
    (success : consume declared selection bytes = .ok result)
    {i : Nat} (index : i < declared.context.length) : i * 32 + 32 ≤ bytes.length := by
  obtain ⟨vs, rest, read, decoded⟩ := success_reads_actual_words declared selection success
  exact ExternalReturnBytes.complete_word read index

/-- info: 'Solidity.PrimitiveReturnConsumer.declared_failure' depends on axioms: [propext] -/
#guard_msgs in
#print axioms declared_failure

/-- info: 'Solidity.PrimitiveReturnConsumer.declared_success' depends on axioms: [propext] -/
#guard_msgs in
#print axioms declared_success

/-- info: 'Solidity.PrimitiveReturnConsumer.success_validates_declaration' depends on axioms: [propext] -/
#guard_msgs in
#print axioms success_validates_declaration

/-- info: 'Solidity.PrimitiveReturnConsumer.decode_names' depends on axioms: [propext] -/
#guard_msgs in
#print axioms decode_names

/-- info: 'Solidity.PrimitiveReturnConsumer.success_reads_actual_words' depends on axioms: [propext] -/
#guard_msgs in
#print axioms success_reads_actual_words

/-- info: 'Solidity.PrimitiveReturnConsumer.success_complete_word' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms success_complete_word

end Solidity.PrimitiveReturnConsumer
